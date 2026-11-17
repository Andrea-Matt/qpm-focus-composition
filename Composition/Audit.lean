import Composition.Examples.NonModal
import Composition.Examples.Modal

/-!
# Audit of the readable/auxiliary separation

The modules under `Composition.Lemmas` are auxiliary: they hold lemmas (and possibly definitions)
used only inside proofs, and need not be read.  The other modules of `Composition` are readable.
`#audit`, run at the end of this file and so at every build, fails the build unless:

0. every file under `Composition/` is imported here, and every imported module belongs to
   `Composition`, to Lean, or to Mathlib and its dependencies;
1. no auxiliary declaration occurs in the type of a readable declaration (the statement of a
   theorem, the signature of a definition), nor in the body of a readable definition outside its
   proof subterms; helpers Lean generates for readable declarations are checked the same way;
2. every readable declaration depends on no axioms beyond `propext`, `Classical.choice` and
   `Quot.sound` (so no `sorry`, no `native_decide`, no `axiom` from an auxiliary file);
3. auxiliary files contain no axioms, instances or syntax (notations, macros, elaborators,
   attributes), which could change what readable text means without adding a constant.

Lake reruns this file only when one of its imports changes, so a new file that nothing imports
is reported at the next such rebuild; `lake env lean Composition/Audit.lean` runs the audit at
any time.
-/

open Lean Meta Elab Command

namespace Composition.Audit

/-- What is audited: the library `root` (folder and namespace of the same name), the libraries
it may import besides the trusted packages, and the axioms beyond the standard ones that are
allowed (for `Composition`, none). -/
structure Spec where
  root : Name
  imports : List Name := []
  allowedAxiom : Name → Bool := fun _ => false

/-- An auxiliary module: under `root.Lemmas`. -/
def isAux (root m : Name) : Bool := (root ++ `Lemmas).isPrefixOf m

/-- A readable module: in `root`, and neither auxiliary nor the audit itself. -/
def isReadable (root m : Name) : Bool :=
  root.isPrefixOf m && !isAux root m && m != root ++ `Audit

/-- The packages trusted as they are: Lean, Mathlib, and Mathlib's dependencies. -/
def trustedRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
    `ImportGraph, `LeanSearchClient]

/-- The module that declares `c`. -/
def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- Add to `r` the constants occurring in `e` outside its proof subterms. -/
partial def collectNonProof (r : IO.Ref NameSet) (e : Expr) : MetaM Unit := do
  if ← (try isProof e catch _ => pure false) then return
  match e with
  | .const n _ => r.modify (·.insert n)
  | .app f a => collectNonProof r f; collectNonProof r a
  | .lam n t b bi | .forallE n t b bi =>
    collectNonProof r t
    withLocalDecl n bi t fun x => collectNonProof r (b.instantiate1 x)
  | .letE n t v b _ =>
    collectNonProof r t; collectNonProof r v
    withLetDecl n t v fun x => collectNonProof r (b.instantiate1 x)
  | .mdata _ b | .proj _ _ b => collectNonProof r b
  | _ => pure ()

/-- The constants occurring in `e` outside its proof subterms. -/
def nonProofConsts (e : Expr) : MetaM NameSet := do
  let r ← IO.mkRef ({} : NameSet)
  collectNonProof r e
  r.get

/-- Words that may not start a command in an auxiliary file. -/
def forbidden : List String :=
  ["axiom", "instance", "attribute", "notation", "prefix", "infix", "infixl", "infixr",
    "postfix", "notation3", "macro", "macro_rules", "syntax", "elab", "elab_rules", "deriving",
    "binder_predicate", "export", "scoped", "local", "declare_syntax_cat", "initialize",
    "builtin_initialize", "unsafe"]

/-- The source text of `s` with comments (`--` and nested `/- -/`) replaced by spaces. -/
def stripComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let d := cs.getD (i + 1) ' '
    if depth == 0 && c == '-' && d == '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '/' && d == '-' then
      depth := depth + 1; i := i + 2; out := out.push ' '
    else if depth > 0 && c == '-' && d == '/' then
      depth := depth - 1; i := i + 2; out := out.push ' '
    else
      out := out.push (if depth > 0 && c != '\n' then ' ' else c); i := i + 1
  return String.ofList out.toList

/-- The forbidden command words starting a line of the auxiliary source `src`, with line numbers.
Attribute prefixes `@[…]` and modifiers are skipped. -/
def lintSource (src : String) : List (Nat × String) := Id.run do
  let mut found := []
  let mut n := 0
  for line in (stripComments src).splitOn "\n" do
    n := n + 1
    let mut t := line.trimAsciiStart.toString
    if t.startsWith "@[" then
      t := ((t.dropWhile (· != ']')).drop 1).toString.trimAsciiStart.toString
    let ws := (t.splitOn " ").filter (· ≠ "")
    let ws := ws.dropWhile (· ∈ ["private", "protected", "noncomputable", "nonrec", "partial"])
    if let w :: _ := ws then
      if w ∈ forbidden then found := found ++ [(n, w)]
  return found

/-- The head constant of a type, under its binders. -/
def headConst? (t : Expr) : Option Name := t.getForallBody.getAppFn.constName?

/-- Declarations written in the source, for the counts: not internal, and not equation lemmas or
matchers, which Lean creates on demand in whichever module first needs them. -/
def isWritten (c : Name) : Bool :=
  !c.isInternal && match c with
    | .str _ s =>
      let gen (pre : String) :=
        s.startsWith pre && (s.drop pre.length).all fun c => c.isDigit || c == '_'
      !(s == "eq_def" || gen "eq_" || gen "match_")
    | _ => true

/-- The standard axioms. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Run the checks on the library of `spec`; report each violation as an error. -/
def audit (spec : Spec) : CommandElabM Unit := do
  let root := spec.root
  let isAux := isAux root
  let isReadable := isReadable root
  let allowed (a : Name) : Bool := a ∈ standardAxioms || spec.allowedAxiom a
  let env ← getEnv
  let mut errors : Array String := #[]
  let mut nReadable := 0
  let mut nAux := 0
  let consts := env.constants.toList
  -- 0. Imports: every file under the library's folder, and nothing untrusted.
  for f in ← System.FilePath.walkDir root.toString do
    unless f.extension == some "lean" do continue
    let m := (f.withExtension "").components.foldl Name.str .anonymous
    unless m == root ++ `Audit || env.header.moduleNames.contains m do
      errors := errors.push s!"{f}: not imported by the audit, so not checked"
  for m in env.header.moduleNames do
    unless (root :: spec.imports ++ trustedRoots).any (·.isPrefixOf m) do
      errors := errors.push
        s!"{m}: imported module outside `{root}`, its allowed imports and the trusted packages"
  -- 3. Auxiliary declarations.
  for (c, info) in consts do
    let some m := moduleOf env c | continue
    unless isAux m do continue
    if isWritten c then nAux := nAux + 1
    if info matches .axiomInfo _ then
      unless allowed c do errors := errors.push s!"{m}: axiom {c}"
    if isInstanceCore env c then errors := errors.push s!"{m}: instance {c}"
    if !(info matches .thmInfo _) then
      if let some h := headConst? info.type then
        if (`Lean).isPrefixOf h then errors := errors.push s!"{m}: meta-level declaration {c}"
  for m in env.header.moduleNames do
    unless isAux m do continue
    let path := System.mkFilePath (m.components.map (·.toString)) |>.addExtension "lean"
    let src ← try IO.FS.readFile path catch _ =>
      errors := errors.push s!"{m}: cannot read {path}"; pure ""
    for (n, w) in lintSource src do
      errors := errors.push s!"{path}:{n}: `{w}` is not allowed in an auxiliary file"
  -- 1, 2. Readable declarations, and the helpers their definitions reach.
  let isAuxConst (n : Name) : Bool := (moduleOf env n).any isAux
  let isReadableHelper (n : Name) : Bool := n.isInternal && (moduleOf env n).any isReadable
  let mut todo : Array Name := #[]
  for (c, _) in consts do
    let some m := moduleOf env c | continue
    if isReadable m && !c.isInternal then todo := todo.push c
  nReadable := (todo.filter isWritten).size
  let mut seen : NameSet := {}
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some info := env.find? c | continue
    for n in info.type.getUsedConstants do
      if isAuxConst n then errors := errors.push s!"{c}: its type uses auxiliary {n}"
      else if isReadableHelper n then todo := todo.push n
    let body? := match info with
      | .defnInfo d => some d.value
      | .opaqueInfo d => some d.value
      | _ => none
    if let some body := body? then
      for n in ← liftTermElabM (nonProofConsts body) do
        if isAuxConst n then errors := errors.push s!"{c}: its body uses auxiliary {n}"
        else if isReadableHelper n then todo := todo.push n
    unless c.isInternal do
      let axs ← liftCoreM (collectAxioms c)
      for a in axs do
        unless allowed a do errors := errors.push s!"{c}: depends on axiom {a}"
  if errors.isEmpty then
    logInfo m!"audit: {nReadable} readable, {nAux} auxiliary declarations, no violations"
  else
    for e in errors do logError e

/-- Check the readable/auxiliary separation of `Composition` (see the module docstring). -/
elab "#audit" : command => audit { root := `Composition }

#audit

end Composition.Audit
