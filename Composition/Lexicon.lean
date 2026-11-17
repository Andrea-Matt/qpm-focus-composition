import Mathlib.Data.Finset.Functor
import Composition.Ontology

/-!
# The lexicon

The meanings of the lexical items (*not*, *or*, *and*, *both*, *can*, *must*), and what
composing them with focus gives as alternatives.  Readable.
-/

namespace Composition

variable {World Individual : Type}

/-- *Not*: fuzzy negation. -/
def NL.not (r : FuzzyP) : FuzzyP := Fz.not r

/-- *Or* is union: each disjunct enters as a singleton, outside focus or inside it (see
*Focus on sets*), and *or* joins the sets. -/
def NL.or {α : Type} [DecidableEq α] (X Y : Finset α) : Finset α := X ∪ Y

/-- Homogeneous *and* forms the sum of two pluralities: predicated with `⋆`, the sum is fully true
when every atom is, fully false when none is.  Contrast *both*. -/
def NL.and {α : Type} [DecidableEq α] (x y : Plural α) : Plural α :=
  ⟨x.atoms ∪ y.atoms, x.nonempty.mono Finset.subset_union_left⟩

/-- *Both*, a quantifier: the conjunction (minimum) of `pred` over the atoms of `x`, fully true
exactly when `pred` is fully true of every atom.  It takes the predicate first: `NL.both pred x`
is *pred both x* (*Taro drank both of `x`*).  The predicate is atomic, not `⋆pred`, since *both*
itself distributes it over the atoms. -/
def NL.both {α : Type} (pred : α → FuzzyP) (x : Plural α) : FuzzyP := fun w =>
  x.atoms.fold min 1 (pred · w)

/-- *Can* takes a set of propositions (`{r}` for a plain prejacent, `NL.or {r} {s}` for free
choice): the average, over its members, of their possibility. -/
def NL.can (acc : World → Finset World) (R : Finset FuzzyP) : FuzzyP := fun w =>
  avg R fun r => Fz.diamond acc r w

/-- *Must* takes a set of propositions: the necessity of their disjunction. -/
def NL.must (acc : World → Finset World) (R : Finset FuzzyP) : FuzzyP := Fz.box acc (bigOr R)

/-! ## Alternatives of coordinations -/

/-- A sum of a plurality with itself is that plurality. -/
theorem NL.and_self {α : Type} [DecidableEq α] (x : Plural α) : NL.and x x = x := by
  cases x; simp only [NL.and, Finset.union_self]

section
variable (pred : Individual → FuzzyP) {A : Set (Plural Individual)} {a b : Plural Individual}
  (ha : a ∈ A) (hb : b ∈ A)

/-- The alternatives of *[a]_F and [b]_F* are exactly `A`, the alternatives of each conjunct, when
`A` is closed under sums. -/
theorem NL.and_alts [DecidableEq Individual] (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A) :
    (NL.and <$> Foc A a ha <*> Foc A b hb).alts = A := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, z, hz, rfl⟩
    exact hA y hy z hz
  · exact fun hx => ⟨_, ⟨x, hx, rfl⟩, x, hx, NL.and_self x⟩

open Classical in
/-- The alternatives of *[a]_F or [b]_F*, inside focus: the sets `R.image (⋆pred)`, for `R` a
nonempty finite set of alternatives.  No closure hypothesis is needed. -/
theorem NL.or_finsets_alts :
    ((⋆pred <$> ·) <$>
      (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)).alts =
    Finset.image (⋆pred) '' finSubsets A :=
  congrArg (Set.image _) (Focus.union_finsets_alts rfl)

end

end Composition
