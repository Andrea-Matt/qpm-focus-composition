import Composition.Apparatus
import Composition.Questions

/-!
# The natural-language ontology

Pluralities and distributive predication (`⋆`), independence of the atoms, focus structures, and
focus on sets (`Focus.finsets`).  Readable.
-/

namespace Composition

variable {World : Type}

/-! ## Pluralities -/

/-- A plurality: a nonempty finite set of atoms, kept apart from the sets that *or* forms. -/
structure Plural (α : Type) where
  /-- The atoms of the plurality. -/
  atoms : Finset α
  nonempty : atoms.Nonempty

/-- The plurality whose only atom is `a`: the unit of the plural construction, as `{a}` is for
finite sets.  `Plural` is not given a `Monad` instance. -/
def Plural.pure {α : Type} (a : α) : Plural α := ⟨{a}, Finset.singleton_nonempty a⟩

/-- Pluralization (Link's `*`), graded: the value of `⋆pred x` at a world is the average, over
the atoms of `x`, of the values of `pred` there. -/
def star {α : Type} (pred : α → FuzzyP) (x : Plural α) : FuzzyP := fun w =>
  avg x.atoms (pred · w)

@[inherit_doc] prefix:max "⋆" => star

/-- The atomic propositions `pred m` are independent: for every set `S` of atoms, some world
makes `pred` fully true on `S` and fully false elsewhere. -/
def Independent {α : Type} (pred : α → FuzzyP) : Prop :=
  ∀ S : Set α, ∃ w, ∀ m, (m ∈ S → pred m w = 1) ∧ (m ∉ S → pred m w = 0)

/-! ## Focus -/

/-- A focus structure: a point among its alternatives. -/
@[ext] structure Focus (α : Type) where
  /-- The ordinary value. -/
  point : α
  /-- The alternatives (the focus value). -/
  alts  : Set α
  /-- The ordinary value is among the alternatives. -/
  mem   : point ∈ alts

/-- Functorial map: apply `f` to the point and to every alternative. -/
def Focus.map {α β : Type} (f : α → β) (x : Focus α) : Focus β where
  point := f x.point
  alts  := f '' x.alts
  mem   := Set.mem_image_of_mem f x.mem

/-- Point-wise application: every alternative function to every alternative argument. -/
def Focus.seq {α β : Type} (F : Focus (α → β)) (X : Focus α) : Focus β where
  point := F.point X.point
  alts  := Set.image2 (fun f x => f x) F.alts X.alts
  mem   := Set.mem_image2_of_mem F.mem X.mem

instance : Applicative Focus where
  pure x  := ⟨x, {x}, Set.mem_singleton x⟩
  map     := Focus.map
  seq F X := Focus.seq F (X ())

instance : LawfulApplicative Focus where
  map_const       := rfl
  id_map x        := Focus.ext rfl (Set.image_id x.alts)
  comp_map g h x  := Focus.ext rfl (Set.image_comp h g x.alts)
  seqLeft_eq x y  := rfl
  seqRight_eq x y := rfl
  pure_seq g x    := Focus.ext rfl Set.image2_singleton_left
  map_pure g x    := Focus.ext rfl (Set.image_singleton (f := g) (a := x))
  seq_pure g x    := Focus.ext rfl Set.image2_singleton_right
  seq_assoc x g h := Focus.ext rfl (by
    ext c
    simp only [Seq.seq, Functor.map, Focus.seq, Focus.map, Set.mem_image2, Set.mem_image]
    constructor
    · rintro ⟨k, hk, _, ⟨f, hf, a, ha, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨k, hk, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
    · rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, f, hf, rfl⟩, a, ha, rfl⟩
      exact ⟨k, hk, _, ⟨f, hf, a, ha, rfl⟩, rfl⟩)

/-- Focus marking on `point`, with the alternatives `alts` supplied by the context. -/
def Foc {α : Type} (alts : Set α) (point : α) (mem : point ∈ alts) : Focus α :=
  ⟨point, alts, mem⟩

/-- Matching for a focus structure: the propositions its alternatives assert match `k`. -/
def Focus.Matches (k : Set World) (F : Focus FuzzyP) : Prop :=
  Composition.Matches k ((Assert ·) '' F.alts)

/-- The cell of the alternative `r` of `F` in `k`: the worlds of `k` where `r` is the strongest
fully true alternative of `F` (fully true there, and entailing every alternative of `F` fully true
there). -/
def Focus.cell (k : Set World) (F : Focus FuzzyP) (r : FuzzyP) : Set World :=
  k ∩ exh ((Assert ·) '' F.alts) (Assert r)

/-! ## Focus on sets

*Or* forms finite sets of disjuncts, and each disjunct enters as a singleton, outside focus or
inside it.  Outside focus, `F ↦ {F}` gives a set of focus structures, matched member by member.
Inside focus, `Focus.finsets` gives a focused set, whose value and alternatives are sets a modal
can apply to; the alternatives of `{a}` are then the nonempty finite sets of alternatives of `a`,
the free join-semilattice on them. -/

/-- The nonempty finite subsets of `A`. -/
def finSubsets {α : Type} (A : Set α) : Set (Finset α) := {S | S.Nonempty ∧ ↑S ⊆ A}

/-- Lift a focus structure to finite sets: the point is the singleton of the point of `X`, and the
alternatives are the nonempty finite sets of alternatives of `X`. -/
def Focus.finsets {α : Type} (X : Focus α) : Focus (Finset α) :=
  ⟨{X.point}, finSubsets X.alts, by simp [finSubsets, X.mem]⟩

/-- `Focus.finsets` is natural: lifting `f <$> X` gives `X.finsets` mapped with `Finset.image f`.
A finite subset of `f '' A` is the image of a finite subset of `A`. -/
theorem Focus.finsets_map {α β : Type} [DecidableEq β] (f : α → β) (X : Focus α) :
    (f <$> X).finsets = Finset.image f <$> X.finsets := by
  refine Focus.ext (Finset.image_singleton f X.point).symm (Set.ext fun S => ⟨?_, ?_⟩)
  · rintro ⟨hS, hSX⟩
    obtain ⟨T, hT, rfl⟩ := Finset.subset_set_image_iff.mp hSX
    exact ⟨T, ⟨Finset.image_nonempty.mp hS, hT⟩, rfl⟩
  · rintro ⟨T, ⟨hT, hTX⟩, rfl⟩
    exact ⟨hT.image f, by rw [Finset.coe_image]; exact Set.image_mono hTX⟩

/-- The alternatives of `{a} ∪ {b}`, for `a` and `b` with the same alternatives, are those of
`{a}`: the free semilattice is closed under union. -/
theorem Focus.union_finsets_alts {α : Type} [DecidableEq α] {X Y : Focus α}
    (h : X.alts = Y.alts) : ((· ∪ ·) <$> X.finsets <*> Y.finsets).alts = X.finsets.alts := by
  ext S
  constructor
  · rintro ⟨_, ⟨T, ⟨hT, hTX⟩, rfl⟩, U, ⟨-, hUY⟩, rfl⟩
    exact ⟨hT.mono Finset.subset_union_left,
      by rw [Finset.coe_union]; exact Set.union_subset hTX (h ▸ hUY)⟩
  · exact fun hS => ⟨_, ⟨S, hS, rfl⟩, S, ⟨hS.1, h ▸ hS.2⟩, Finset.union_self S⟩

end Composition
