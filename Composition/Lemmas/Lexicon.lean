import Composition.Lexicon
import Composition.Lemmas.Ontology

/-!
# Lemmas on the lexicon

Auxiliary: optional reading.  Nothing declared here occurs in a statement or in a definition
body of a readable file; `Composition.Audit` checks this at every build.
-/

namespace Composition

variable {World Individual : Type}

/-! ## Values of the lexical items, and when they are fully true -/

section
variable (acc : World → Finset World) {R : Finset FuzzyP} {r : FuzzyP} {w : World}

/-- *Not r* is fully true iff `r` is fully false. -/
theorem NL.not_eq_one : NL.not r w = 1 ↔ r w = 0 := by
  rw [← Truth.not_zero]
  exact (Function.Involutive.injective Truth.not_not).eq_iff

/-- *Not both* is fully true iff `pred` is fully false of some atom. -/
theorem NL.not_both_eq_one {α : Type} {pred : α → FuzzyP} {x : Plural α} :
    NL.not (NL.both pred x) w = 1 ↔ ∃ m ∈ x.atoms, pred m w = 0 :=
  NL.not_eq_one.trans fold_min_eq_zero

/-- A property holds of every member of *x or y* iff it holds of `x` and of `y`. -/
theorem NL.forall_mem_or {α : Type} [DecidableEq α] {Φ : α → Prop} {x y : α} :
    (∀ z ∈ NL.or {x} {y}, Φ z) ↔ Φ x ∧ Φ y := by
  simp [NL.or]

/-- *Can* with a plain prejacent is possibility. -/
theorem NL.can_singleton (r : FuzzyP) : NL.can acc {r} = Fz.diamond acc r := by
  funext w
  apply Subtype.ext
  simp only [NL.can, avg, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, div_one]

/-- *Must* with a plain prejacent is necessity. -/
theorem NL.must_singleton (r : FuzzyP) : NL.must acc {r} = Fz.box acc r := by
  rw [NL.must, bigOr_singleton]

/-- *Can R* is fully true iff each member of `R` is fully true at some accessible world. -/
theorem NL.can_eq_one (hR : R.Nonempty) :
    NL.can acc R w = 1 ↔ ∀ r ∈ R, ∃ v ∈ acc w, r v = 1 :=
  (avg_eq_one hR).trans (forall₂_congr fun _ _ => Fz.diamond_eq_one acc)

/-- *Can R* is fully false (so *not can R* is fully true) iff no member of `R` is true to any
degree at an accessible world. -/
theorem NL.can_eq_zero : NL.can acc R w = 0 ↔ ∀ r ∈ R, ∀ v ∈ acc w, r v = 0 :=
  avg_eq_zero.trans (forall₂_congr fun _ _ => Fz.diamond_eq_zero acc)

/-- **`must` is classical**: *must R* is fully true iff every accessible world makes some member
of `R` fully true. -/
theorem NL.must_eq_one : NL.must acc R w = 1 ↔ ∀ v ∈ acc w, ∃ r ∈ R, r v = 1 :=
  (Fz.box_eq_one acc).trans (forall₂_congr fun _ _ => fold_max_eq_one)

end

/-! ## Entailment between pluralities -/

section
variable {α : Type} {P : Plural α → FuzzyP} (T : World → Set α)
  (hP : ∀ x w, P x w = 1 ↔ ↑x.atoms ⊆ T w) (hT : ∀ S, ∃ w, T w = S)
include hP hT

/-- When `P x` is fully true at `w` iff the atoms of `x` lie in `T w`, and every set of atoms is
some `T w`, `P x` entails `P y` iff the atoms of `y` are among those of `x`. -/
theorem assert_subset_iff (x y : Plural α) :
    Assert (P x) ⊆ Assert (P y) ↔ y.atoms ⊆ x.atoms := by
  refine ⟨fun h => ?_,
    fun h v hv => (hP y v).mpr ((Finset.coe_subset.mpr h).trans ((hP x v).mp hv))⟩
  obtain ⟨v, hv⟩ := hT ↑x.atoms
  exact Finset.coe_subset.mp (hv ▸ (hP y v).mp (h ((hP x v).mpr hv.symm.subset)))

end

/-! ## Sums asserting unions -/

/-- **Sums asserting unions are never the strongest**: when what `P (u ⊕ v)` asserts is the union
of what `P u` and `P v` assert, and `P u` entails `P v` only if the atoms of `u` are among those of
`v`, then for alternatives `x`, `y` neither of whose atoms include the other's, no world is in the
cell of `P (x ⊕ y)`. -/
theorem exh_sum_eq_empty {α : Type} [DecidableEq α] {A : Set (Plural α)} {a b : Plural α}
    (ha : a ∈ A) (hb : b ∈ A) (P : Plural α → FuzzyP)
    (hsum : ∀ u v, Assert (P (NL.and u v)) = Assert (P u) ∪ Assert (P v))
    (hsep : ∀ u v, ¬ u.atoms ⊆ v.atoms → ¬ Assert (P u) ⊆ Assert (P v))
    {x y : Plural α} (hx : x ∈ A) (hy : y ∈ A) (hxy : ¬ x.atoms ⊆ y.atoms)
    (hyx : ¬ y.atoms ⊆ x.atoms) :
    exh ((Assert ·) '' (P <$> (NL.and <$> Foc A a ha <*> Foc A b hb)).alts)
      (Assert (P (NL.and x y))) = ∅ := by
  have single : ∀ u ∈ A,
      Assert (P u) ∈ (Assert ·) '' (P <$> (NL.and <$> Foc A a ha <*> Foc A b hb)).alts :=
    fun u hu => ⟨_, ⟨_, ⟨_, ⟨u, hu, rfl⟩, u, hu, rfl⟩, congrArg P (NL.and_self u)⟩, rfl⟩
  rw [hsum]
  exact exh_union_eq_empty (single x hx) (single y hy) (hsep y x hyx) (hsep x y hxy)

/-! ## Focus, negation and negated *both* under independence -/

section
variable {α : Type} {pred : α → FuzzyP} (hI : Independent pred)

include hI in
/-- Under independence, *Taro drank `x`* entails *Taro drank `y`* iff the atoms of `y` are among
those of `x`. -/
theorem Independent.star_subset_iff (x y : Plural α) :
    Assert (⋆pred x) ⊆ Assert (⋆pred y) ↔ y.atoms ⊆ x.atoms :=
  assert_subset_iff (fun w => {m | pred m w = 1}) (fun x _ => star_eq_one pred x)
    (fun S => (hI.eq_one_iff S).imp fun _ h => Set.ext h) x y

include hI in
/-- **The cells of focus without coordination**: `w` is in the cell of *Taro drank `x`* iff Taro
drank `x` at `w`, and every alternative he drank there is part of `x`. -/
theorem NL.mem_focus_cell {A : Set (Plural α)} {a x : Plural α} (ha : a ∈ A) (hx : x ∈ A)
    {k : Set World} {w : World} :
    w ∈ (⋆pred <$> Foc A a ha).cell k (⋆pred x) ↔
    w ∈ k ∧ ⋆pred x w = 1 ∧ ∀ y ∈ A, ⋆pred y w = 1 → y.atoms ⊆ x.atoms :=
  and_congr_right fun _ => mem_exh_image_iff (P := (⋆pred)) (fun y x => y.atoms ⊆ x.atoms)
    (fun x _ y _ => hI.star_subset_iff x y) hx w

include hI in
/-- Under independence, *Taro didn't drink `x`* entails *Taro didn't drink `y`* iff the atoms of
`y` are among those of `x`. -/
theorem Independent.not_star_subset_iff (x y : Plural α) :
    Assert (NL.not (⋆pred x)) ⊆ Assert (NL.not (⋆pred y)) ↔ y.atoms ⊆ x.atoms :=
  assert_subset_iff (P := fun x => NL.not (⋆pred x)) (fun w => {m | pred m w = 0})
    (fun x _ => NL.not_eq_one.trans (star_eq_zero pred x))
    (fun S => (hI.eq_zero_iff S).imp fun _ h => Set.ext h) x y

include hI in
/-- **The cells of negated focus**: `w` is in the cell of *Taro didn't drink `x`* iff Taro drank
none of `x` at `w`, and every alternative he drank none of there is part of `x`. -/
theorem NL.mem_notFocus_cell {A : Set (Plural α)} {a x : Plural α} (ha : a ∈ A) (hx : x ∈ A)
    {k : Set World} {w : World} :
    w ∈ (NL.not <$> (⋆pred <$> Foc A a ha)).cell k (NL.not (⋆pred x)) ↔
    w ∈ k ∧ ⋆pred x w = 0 ∧ ∀ y ∈ A, ⋆pred y w = 0 → y.atoms ⊆ x.atoms := by
  change w ∈ k ∩ exh ((Assert ·) '' (NL.not '' (⋆pred '' A))) _ ↔ _
  rw [Set.image_image NL.not (⋆pred) A]
  refine and_congr_right fun _ => (mem_exh_image_iff (P := fun x => NL.not (⋆pred x))
    (fun y x => y.atoms ⊆ x.atoms) (fun x _ y _ => hI.not_star_subset_iff x y) hx w).trans ?_
  simp only [NL.not_eq_one]

/-- *Not both x ⊕ y* is the union of *not both x* and *not both y*. -/
theorem NL.assert_notBoth_and [DecidableEq α] (u v : Plural α) :
    Assert (NL.not (NL.both pred (NL.and u v))) =
      Assert (NL.not (NL.both pred u)) ∪ Assert (NL.not (NL.both pred v)) := by
  ext w
  simp [mem_assert, NL.not_both_eq_one, NL.and, or_and_right, exists_or]

include hI in
/-- Under independence, *not both u* entails *not both v* only if the atoms of `u` are among
those of `v`. -/
theorem NL.notBoth_not_subset {u v : Plural α} (huv : ¬ u.atoms ⊆ v.atoms) :
    ¬ Assert (NL.not (NL.both pred u)) ⊆ Assert (NL.not (NL.both pred v)) := fun h => by
  obtain ⟨m, hmu, hmv⟩ := Finset.not_subset.mp huv
  obtain ⟨w, hw⟩ := hI.eq_zero_iff {m}
  obtain ⟨m', hm', h0⟩ :=
    NL.not_both_eq_one.mp (h (NL.not_both_eq_one.mpr ⟨m, hmu, (hw m).mpr rfl⟩))
  exact hmv (Set.mem_singleton_iff.mp ((hw m').mp h0) ▸ hm')

include hI in
/-- **The disjunctive alternative of negated *both* is never the strongest**: for alternatives
`x`, `y` neither of whose atoms include the other's, *not both x ⊕ y* is the union of the
incomparable *not both x* and *not both y*, so no world is in its cell. -/
theorem NL.exh_notBoth_eq_empty [DecidableEq α] {A : Set (Plural α)} {a b : Plural α}
    (ha : a ∈ A) (hb : b ∈ A) {x y : Plural α} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : ¬ x.atoms ⊆ y.atoms) (hyx : ¬ y.atoms ⊆ x.atoms) :
    exh ((Assert ·) ''
      (NL.not <$> (NL.both pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb))).alts)
      (Assert (NL.not (NL.both pred (NL.and x y)))) = ∅ := by
  rw [Functor.map_map]
  exact exh_sum_eq_empty ha hb (fun u => NL.not (NL.both pred u)) NL.assert_notBoth_and
    (fun _ _ huv => NL.notBoth_not_subset hI huv) hx hy hxy hyx

end

/-! ## Modals on focused sets -/

section
variable (acc : World → Finset World) (hU : Unconstrained acc) (pred : Individual → FuzzyP)
  (hI : Independent pred) {A : Set (Plural Individual)} {k : Set World}

open Classical in
/-- *Can* of a set of alternatives is fully true iff each is fully true at an accessible world. -/
theorem NL.can_image_eq_one {R : Finset (Plural Individual)} (hR : R.Nonempty) {w : World} :
    NL.can acc (R.image (⋆pred)) w = 1 ↔ ∀ x ∈ R, ∃ v ∈ acc w, ⋆pred x v = 1 := by
  rw [NL.can_eq_one acc (hR.image _), Finset.forall_mem_image]

open Classical in
/-- A modal `M` applied to a focused set whose alternatives are the images of the nonempty finite
sets of alternatives (as *[a]_F or [b]_F*, `NL.or_finsets_alts`) matches `k` iff its cells cover
`k` and are live, given how its alternatives entail each other and what makes one the strongest
fully true one. -/
theorem NL.set_matches_iff (M : Finset FuzzyP → FuzzyP) (F : Focus (Finset FuzzyP))
    (hF : F.alts = Finset.image (⋆pred) '' finSubsets A)
    (le : Finset (Plural Individual) → Finset (Plural Individual) → Prop)
    (ent : ∀ R ∈ finSubsets A, ∀ R' ∈ finSubsets A,
      Assert (M (R.image (⋆pred))) ⊆ Assert (M (R'.image (⋆pred))) ↔ le R' R)
    (C : Finset (Plural Individual) → Set World)
    (top : ∀ R ∈ finSubsets A, ∀ w ∈ k, (M (R.image (⋆pred)) w = 1 ∧
      ∀ R' ∈ finSubsets A, M (R'.image (⋆pred)) w = 1 → le R' R) ↔ w ∈ C R) :
    (M <$> F).Matches k ↔
    (∀ R ∈ finSubsets A, (k ∩ C R).Nonempty) ∧
    k ⊆ ⋃ R ∈ finSubsets A, C R := by
  change Matches k ((Assert ·) '' (M '' F.alts)) ↔ _
  rw [hF, Set.image_image M (Finset.image (⋆pred)) (finSubsets A)]
  exact matches_image_iff le C ent top

open Classical in
/-- The cell of the alternative indexed by `R` of a modal `M` applied to such a focused set:
`M` of `R` is fully true, and every alternative fully true is below `R`. -/
theorem NL.mem_set_cell (M : Finset FuzzyP → FuzzyP) (F : Focus (Finset FuzzyP))
    (hF : F.alts = Finset.image (⋆pred) '' finSubsets A)
    (le : Finset (Plural Individual) → Finset (Plural Individual) → Prop)
    (ent : ∀ R ∈ finSubsets A, ∀ R' ∈ finSubsets A,
      Assert (M (R.image (⋆pred))) ⊆ Assert (M (R'.image (⋆pred))) ↔ le R' R)
    {R : Finset (Plural Individual)} (hR : R ∈ finSubsets A) {w : World} :
    w ∈ (M <$> F).cell k (M (R.image (⋆pred))) ↔
    w ∈ k ∧ M (R.image (⋆pred)) w = 1 ∧
      ∀ R' ∈ finSubsets A, M (R'.image (⋆pred)) w = 1 → le R' R := by
  change w ∈ k ∩ exh ((Assert ·) '' (M '' F.alts)) _ ↔ _
  rw [hF, Set.image_image M (Finset.image (⋆pred)) (finSubsets A)]
  exact and_congr_right fun _ => mem_exh_image_iff (P := fun R => M (R.image (⋆pred))) le ent hR w

open Classical in
include hU hI in
/-- With unconstrained accessibility and independent atoms, *can R* entails *can R'* iff every
member of `R'` is part of a member of `R`. -/
theorem NL.can_subset_iff :
    ∀ R ∈ finSubsets A, ∀ R' ∈ finSubsets A,
      Assert (NL.can acc (R.image (⋆pred))) ⊆ Assert (NL.can acc (R'.image (⋆pred))) ↔
      ∀ y ∈ R', ∃ x ∈ R, y.atoms ⊆ x.atoms := by
  have can1 := @NL.can_image_eq_one World Individual acc pred
  choose v hv using fun x : Plural Individual => hI.eq_one_iff (↑x.atoms : Set Individual)
  have hsv : ∀ x y, ⋆pred y (v x) = 1 ↔ y.atoms ⊆ x.atoms := fun x y =>
    (star_eq_one pred y).trans (forall₂_congr fun m _ => hv x m)
  rintro R ⟨hR, -⟩ R' ⟨hR', -⟩
  refine ⟨fun h y hy => ?_, fun hle w hw => (can1 hR').mpr fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ := hU (R.image v) (hR.image v)
    have hRw := (can1 hR).mpr fun x hx =>
      ⟨v x, by rw [hw]; exact Finset.mem_image_of_mem v hx, (hsv x x).mpr subset_rfl⟩
    obtain ⟨u, hu, hyu⟩ := (can1 hR').mp (h hRw) y hy
    rw [hw, Finset.mem_image] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, (hsv x y).mp hyu⟩
  · obtain ⟨x, hx, hyx⟩ := hle y hy
    obtain ⟨u, hu, hxu⟩ := (can1 hR).mp hw x hx
    exact ⟨u, hu, star_eq_one_of_subset pred x hyx hxu⟩

open Classical in
/-- *Can R* is the strongest fully true alternative at `w` iff the alternatives allowed at `w` are
exactly those that are part of a member of `R`. -/
theorem NL.can_top_iff : ∀ R ∈ finSubsets A, ∀ w,
    (NL.can acc (R.image (⋆pred)) w = 1 ∧ ∀ R' ∈ finSubsets A,
      NL.can acc (R'.image (⋆pred)) w = 1 → ∀ y ∈ R', ∃ x ∈ R, y.atoms ⊆ x.atoms) ↔
    ∀ y ∈ A, (∃ v ∈ acc w, ⋆pred y v = 1) ↔ ∃ x ∈ R, y.atoms ⊆ x.atoms := by
  have can1 := @NL.can_image_eq_one World Individual acc pred
  rintro R ⟨hR, hRA⟩ w
  refine ⟨fun ⟨h1, hmax⟩ y hy => ⟨fun hya => ?_, fun ⟨x, hx, hyx⟩ => ?_⟩,
    fun h => ⟨?_, ?_⟩⟩
  · exact hmax {y} ⟨Finset.singleton_nonempty y, by simpa using hy⟩
      ((can1 (Finset.singleton_nonempty y)).mpr (by simpa using hya)) y
      (Finset.mem_singleton_self y)
  · obtain ⟨u, hu, hxu⟩ := (can1 hR).mp h1 x hx
    exact ⟨u, hu, star_eq_one_of_subset pred x hyx hxu⟩
  · exact (can1 hR).mpr fun x hx => (h x (hRA hx)).mpr ⟨x, hx, subset_rfl⟩
  · exact fun R' ⟨hR', hR'A⟩ h' y hy => (h y (hR'A hy)).mp ((can1 hR').mp h' y hy)

open Classical in
include hU hI in
/-- **The cells of focused free choice**: `w` is in the cell of *Taro can drink x₁ or … or xₙ*,
for `R = {x₁, …, xₙ}`, iff the alternatives Taro is allowed at `w` are exactly those that are part
of a member of `R`. -/
theorem NL.mem_canOr_cell {a b : Plural Individual} (ha : a ∈ A) (hb : b ∈ A)
    {R : Finset (Plural Individual)} (hR : R ∈ finSubsets A)
    {w : World} :
    w ∈ (NL.can acc <$> ((⋆pred <$> ·) <$>
      (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).cell k
      (NL.can acc (R.image (⋆pred))) ↔
    w ∈ k ∧ ∀ y ∈ A, (∃ v ∈ acc w, ⋆pred y v = 1) ↔ ∃ x ∈ R, y.atoms ⊆ x.atoms :=
  (NL.mem_set_cell pred _ _ (NL.or_finsets_alts pred ha hb) _
    (NL.can_subset_iff acc hU pred hI) hR).trans
    (and_congr_right fun _ => NL.can_top_iff acc pred R hR w)

open Classical in
/-- *Must* of a set of alternatives is fully true iff every accessible world makes one of them
fully true. -/
theorem NL.must_image_eq_one (R : Finset (Plural Individual)) (w : World) :
    NL.must acc (R.image (⋆pred)) w = 1 ↔ ∀ v ∈ acc w, ∃ x ∈ R, ⋆pred x v = 1 := by
  rw [NL.must_eq_one]
  simp

open Classical in
include hU hI in
/-- With unconstrained accessibility and independent atoms, *must R* entails *must R'* iff every
member of `R` has a member of `R'` as part. -/
theorem NL.must_subset_iff :
    ∀ R ∈ finSubsets A, ∀ R' ∈ finSubsets A,
      Assert (NL.must acc (R.image (⋆pred))) ⊆ Assert (NL.must acc (R'.image (⋆pred))) ↔
      ∀ x ∈ R, ∃ y ∈ R', y.atoms ⊆ x.atoms := by
  have must1 := NL.must_image_eq_one acc pred
  choose v hv using fun x : Plural Individual => hI.eq_one_iff (↑x.atoms : Set Individual)
  have hsv : ∀ x y, ⋆pred y (v x) = 1 ↔ y.atoms ⊆ x.atoms := fun x y =>
    (star_eq_one pred y).trans (forall₂_congr fun m _ => hv x m)
  rintro R - R' -
  refine ⟨fun h x hx => ?_, fun hle w hw => (must1 R' w).mpr fun u hu => ?_⟩
  · obtain ⟨w, hw⟩ := hU {v x} (Finset.singleton_nonempty _)
    have hRw : NL.must acc (R.image (⋆pred)) w = 1 := (must1 R w).mpr fun u hu => by
      rw [hw, Finset.mem_singleton] at hu
      exact ⟨x, hx, hu ▸ (hsv x x).mpr subset_rfl⟩
    obtain ⟨y, hy, hyu⟩ :=
      (must1 R' w).mp (h hRw) (v x) (by rw [hw]; exact Finset.mem_singleton_self _)
    exact ⟨y, hy, (hsv x y).mp hyu⟩
  · obtain ⟨x, hx, hxu⟩ := (must1 R w).mp hw u hu
    obtain ⟨y, hy, hyx⟩ := hle x hx
    exact ⟨y, hy, star_eq_one_of_subset pred x hyx hxu⟩

open Classical in
/-- At a world from which some world is accessible, *must R* is the strongest fully true
alternative iff every accessible world makes Taro drink a member of `R`, and for each member `x`
of `R` some accessible world is one where every alternative he drinks is part of `x`. -/
theorem NL.must_top_iff : ∀ R ∈ finSubsets A, ∀ w, (acc w).Nonempty →
    ((NL.must acc (R.image (⋆pred)) w = 1 ∧ ∀ R' ∈ finSubsets A,
      NL.must acc (R'.image (⋆pred)) w = 1 → ∀ x ∈ R, ∃ y ∈ R', y.atoms ⊆ x.atoms) ↔
    (∀ v ∈ acc w, ∃ x ∈ R, ⋆pred x v = 1) ∧
      ∀ x ∈ R, ∃ v ∈ acc w, ∀ y ∈ A, ⋆pred y v = 1 → y.atoms ⊆ x.atoms) := by
  have must1 := NL.must_image_eq_one acc pred
  rintro R ⟨hR, hRA⟩ w hS
  refine ⟨fun ⟨h1, hmax⟩ => ⟨(must1 R w).mp h1, fun x hx => by_contra fun hn => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨(must1 R w).mpr h1, fun R' ⟨_, hR'A⟩ h' x hx => ?_⟩⟩
  · push Not at hn
    have : Nonempty (Plural Individual) := ⟨x⟩
    choose! f hfA hf1 hfx using hn
    obtain ⟨y, hy, hyx⟩ := hmax ((acc w).image f) ⟨hS.image f, by
      rw [Finset.coe_image]; rintro _ ⟨u, hu, rfl⟩; exact hfA u hu⟩
      ((must1 _ w).mpr fun u hu => ⟨f u, Finset.mem_image_of_mem f hu, hf1 u hu⟩) x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    exact hfx u hu hyx
  · obtain ⟨u, hu, hux⟩ := h2 x hx
    obtain ⟨y, hy, hyu⟩ := (must1 R' w).mp h' u hu
    exact ⟨y, hy, hux y (hR'A hy) hyu⟩

open Classical in
include hU hI in
/-- **The cells of *must* with *[a]_F or [b]_F***: at a world of `k` from which some world is
accessible, `w` is in the cell of *Taro must drink a member of `R`* iff every accessible world
makes Taro drink a member of `R`, and for each member `x` of `R` some accessible world is one
where every alternative he drinks is part of `x`. -/
theorem NL.mem_mustOr_cell {a b : Plural Individual} (ha : a ∈ A) (hb : b ∈ A)
    (hS : ∀ w ∈ k, (acc w).Nonempty)
    {R : Finset (Plural Individual)} (hR : R ∈ finSubsets A) {w : World} :
    w ∈ (NL.must acc <$> ((⋆pred <$> ·) <$>
      (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).cell k
      (NL.must acc (R.image (⋆pred))) ↔
    w ∈ k ∧ (∀ v ∈ acc w, ∃ x ∈ R, ⋆pred x v = 1) ∧
      ∀ x ∈ R, ∃ v ∈ acc w, ∀ y ∈ A, ⋆pred y v = 1 → y.atoms ⊆ x.atoms :=
  (NL.mem_set_cell pred _ _ (NL.or_finsets_alts pred ha hb) _
    (NL.must_subset_iff acc hU pred hI) hR).trans
    (and_congr_right fun hw => NL.must_top_iff acc pred R hR w (hS w hw))

end

/-! ## *Both* under a negated modal

Each conjunct is lifted (`Focus.finsets`), *and* sums the lifted sets memberwise
(`Finset.image₂ NL.and`), and `NL.both pred` applies to each member. -/

section
variable {acc : World → Finset World} (hU : Unconstrained acc) {pred : Individual → FuzzyP}
  (hI : Independent pred) {A : Set (Plural Individual)} {a b : Plural Individual} (ha : a ∈ A)
  (hb : b ∈ A)

open Classical in
/-- A property inherited by sums holds of every sum of two members of `R` iff it holds of every
member of `R`. -/
theorem forall_mem_image₂_and_self [DecidableEq Individual] {Φ : Plural Individual → Prop}
    (hΦ : ∀ x y, Φ x → Φ (NL.and x y)) {R : Finset (Plural Individual)} :
    (∀ z ∈ Finset.image₂ NL.and R R, Φ z) ↔ ∀ x ∈ R, Φ x := by
  refine ⟨fun h x hx => NL.and_self x ▸ h _ (Finset.mem_image₂_of_mem hx hx), fun h z hz => ?_⟩
  obtain ⟨x, hx, y, -, rfl⟩ := Finset.mem_image₂.mp hz
  exact hΦ x y (h x hx)

open Classical in
/-- The memberwise sums of two nonempty finite sets of alternatives are again one, when the
alternatives are closed under sums. -/
theorem image₂_and_mem_finSubsets [DecidableEq Individual]
    (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A) {S T : Finset (Plural Individual)}
    (hS : S ∈ finSubsets A) (hT : T ∈ finSubsets A) : Finset.image₂ NL.and S T ∈ finSubsets A := by
  refine ⟨hS.1.image₂ hT.1, fun z hz => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hz
  exact hA x (hS.2 hx) y (hT.2 hy)

open Classical in
/-- *Taro can't drink both of each member of `R`* is fully true iff each member of `R` has, at
every accessible world, an atom left fully undrunk. -/
theorem NL.not_can_both_image_eq_one {R : Finset (Plural Individual)} {w : World} :
    NL.not (NL.can acc (R.image (NL.both pred))) w = 1 ↔
      ∀ x ∈ R, ∀ v ∈ acc w, ∃ m ∈ x.atoms, pred m v = 0 := by
  rw [NL.not_eq_one, NL.can_eq_zero, Finset.forall_mem_image]
  exact forall₂_congr fun _ _ => forall₂_congr fun _ _ => fold_min_eq_zero

open Classical in
/-- *Taro doesn't have to drink both of each member of `R`* is fully true iff some accessible world
leaves an atom of each member of `R` fully undrunk. -/
theorem NL.not_must_both_image_eq_one {R : Finset (Plural Individual)} {w : World} :
    NL.not (NL.must acc (R.image (NL.both pred))) w = 1 ↔
      ∃ v ∈ acc w, ∀ x ∈ R, ∃ m ∈ x.atoms, pred m v = 0 := by
  rw [NL.not_eq_one, NL.must, Fz.box_eq_zero]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  change (R.image (NL.both pred)).fold max 0 (· v) = 0 ↔ _
  rw [fold_max_eq_zero, Finset.forall_mem_image]
  exact forall₂_congr fun _ _ => fold_min_eq_zero

/-- *Taro doesn't have to drink both of `x`* is fully true iff some accessible world leaves some
atom of `x` fully undrunk. -/
theorem NL.not_must_both_eq_one {x : Plural Individual} {w : World} :
    NL.not (NL.must acc {NL.both pred x}) w = 1 ↔ ∃ v ∈ acc w, ∃ m ∈ x.atoms, pred m v = 0 := by
  rw [NL.not_eq_one, NL.must_singleton, Fz.box_eq_zero]
  exact exists_congr fun _ => and_congr_right fun _ => fold_min_eq_zero

open Classical in
/-- The alternatives of `G` applied to *both [a]_F and [b]_F* include `G {both (u ⊕ v)}`, for any
two alternatives `u`, `v`. -/
theorem NL.bothSums_mem_alts [DecidableEq Individual] (G : Finset FuzzyP → FuzzyP)
    {u v : Plural Individual} (hu : u ∈ A) (hv : v ∈ A) :
    G {NL.both pred (NL.and u v)} ∈ (G <$> ((NL.both pred <$> ·) <$>
      (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).alts :=
  ⟨_, ⟨_, ⟨_, ⟨{u}, ⟨Finset.singleton_nonempty u, by
      rw [Finset.coe_singleton]; exact Set.singleton_subset_iff.mpr hu⟩, rfl⟩, {v},
    ⟨Finset.singleton_nonempty v, by
      rw [Finset.coe_singleton]; exact Set.singleton_subset_iff.mpr hv⟩, rfl⟩, rfl⟩,
    by simp [Finset.fmap_def]⟩

open Classical in
/-- The asserted alternatives of `G` applied to *both [a]_F and [b]_F*: when `A` is closed under
sums and `G` asserts the same of the sums of `R` with itself as of `R`, they are those of the
nonempty finite sets of alternatives. -/
theorem NL.assert_bothSums_alts [DecidableEq Individual] (G : Finset FuzzyP → FuzzyP)
    (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A)
    (hG : ∀ R : Finset (Plural Individual),
      Assert (G ((Finset.image₂ NL.and R R).image (NL.both pred))) =
        Assert (G (R.image (NL.both pred)))) :
    (Assert ·) '' (G <$> ((NL.both pred <$> ·) <$>
      (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).alts =
    (Assert ·) '' ((fun R => G (R.image (NL.both pred))) '' finSubsets A) := by
  change (Assert ·) '' (G '' ((fun S => NL.both pred <$> S) ''
    Set.image2 (fun f x => f x) (Finset.image₂ NL.and '' finSubsets A) (finSubsets A))) = _
  rw [Set.image2_image_left]
  ext p
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨S, hS, T, hT, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, image₂_and_mem_finSubsets hA hS hT, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨R, hR, R, hR, rfl⟩, rfl⟩, rfl⟩, hG R⟩

open Classical in
/-- *Can't* with *both* asserts the same of the sums of `R` with itself as of `R`. -/
theorem NL.notCanBoth_sums [DecidableEq Individual] (R : Finset (Plural Individual)) :
    Assert (NL.not (NL.can acc ((Finset.image₂ NL.and R R).image (NL.both pred)))) =
      Assert (NL.not (NL.can acc (R.image (NL.both pred)))) := by
  ext w
  simp only [mem_assert, NL.not_can_both_image_eq_one]
  exact forall_mem_image₂_and_self fun x y h v hv =>
    (h v hv).imp fun m ⟨hm, h0⟩ => ⟨Finset.mem_union_left _ hm, h0⟩

include hU hI in
open Classical in
/-- With unconstrained accessibility and independent atoms, *can't* with *both* of `R` entails it
of `R'` iff every member of `R'` includes a member of `R`. -/
theorem NL.notCanBoth_subset_iff :
    ∀ R ∈ finSubsets A, ∀ R' ∈ finSubsets A,
      Assert (NL.not (NL.can acc (R.image (NL.both pred)))) ⊆
        Assert (NL.not (NL.can acc (R'.image (NL.both pred)))) ↔
      ∀ y ∈ R', ∃ x ∈ R, x.atoms ⊆ y.atoms := by
  rintro R - R' -
  refine ⟨fun h y hy => by_contra fun hn => ?_,
    fun hle w hw => NL.not_can_both_image_eq_one.mpr fun y hy v hv => ?_⟩
  · push Not at hn
    obtain ⟨u, hu⟩ := hI ↑y.atoms
    obtain ⟨w, hw⟩ := hU {u} (Finset.singleton_nonempty u)
    have hRw : NL.not (NL.can acc (R.image (NL.both pred))) w = 1 :=
      NL.not_can_both_image_eq_one.mpr fun x hx v hv => by
        rw [hw, Finset.mem_singleton] at hv
        subst hv
        obtain ⟨m, hmx, hmy⟩ := Finset.not_subset.mp (hn x hx)
        exact ⟨m, hmx, (hu m).2 hmy⟩
    obtain ⟨m, hm, h0⟩ := NL.not_can_both_image_eq_one.mp (h hRw) y hy u
      (by rw [hw]; exact Finset.mem_singleton_self u)
    exact Truth.not_one_le_zero (((hu m).1 hm).symm.trans h0).le
  · obtain ⟨x, hx, hxy⟩ := hle y hy
    obtain ⟨m, hm, h0⟩ := NL.not_can_both_image_eq_one.mp hw x hx v hv
    exact ⟨m, hxy hm, h0⟩

open Classical in
/-- *Can't* with *both* of `R` is the strongest fully true alternative at `w` iff the alternatives
Taro may not drink in full there are exactly those that include a member of `R`. -/
theorem NL.notCanBoth_top_iff : ∀ R ∈ finSubsets A, ∀ w,
    (NL.not (NL.can acc (R.image (NL.both pred))) w = 1 ∧ ∀ R' ∈ finSubsets A,
      NL.not (NL.can acc (R'.image (NL.both pred))) w = 1 →
        ∀ y ∈ R', ∃ x ∈ R, x.atoms ⊆ y.atoms) ↔
    ∀ y ∈ A, (∀ v ∈ acc w, ∃ m ∈ y.atoms, pred m v = 0) ↔ ∃ x ∈ R, x.atoms ⊆ y.atoms := by
  rintro R ⟨-, hRA⟩ w
  simp only [NL.not_can_both_image_eq_one]
  refine ⟨fun ⟨h1, hmax⟩ y hy => ⟨fun hy0 => ?_, fun ⟨x, hx, hxy⟩ v hv => ?_⟩,
    fun h => ⟨fun x hx => (h x (hRA hx)).mpr ⟨x, hx, subset_rfl⟩,
      fun R' ⟨_, hR'A⟩ h' y hy => (h y (hR'A hy)).mp (h' y hy)⟩⟩
  · exact hmax {y} ⟨Finset.singleton_nonempty y, by simpa using hy⟩ (by simpa using hy0) y
      (Finset.mem_singleton_self y)
  · obtain ⟨m, hm, h0⟩ := h1 x hx v hv
    exact ⟨m, hxy hm, h0⟩

open Classical in
include hU hI in
/-- **The cells of *can't* with *both***: `w` is in the cell of *can't* with *both* of `R` iff the
alternatives Taro may not drink in full at `w` are exactly those that include a member of `R`. -/
theorem NL.mem_notCanBoth_cell [DecidableEq Individual] (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A)
    {R : Finset (Plural Individual)} (hR : R ∈ finSubsets A) {k : Set World} {w : World} :
    w ∈ (NL.not <$> (NL.can acc <$> ((NL.both pred <$> ·) <$>
      (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))).cell k
      (NL.not (NL.can acc (R.image (NL.both pred)))) ↔
    w ∈ k ∧ ∀ y ∈ A, (∀ v ∈ acc w, ∃ m ∈ y.atoms, pred m v = 0) ↔
      ∃ x ∈ R, x.atoms ⊆ y.atoms := by
  unfold Focus.cell
  rw [Functor.map_map, NL.assert_bothSums_alts ha hb _ hA NL.notCanBoth_sums, Set.mem_inter_iff]
  refine and_congr_right fun _ => ?_
  rw [mem_exh_image_iff _ (NL.notCanBoth_subset_iff hU hI) hR w]
  exact NL.notCanBoth_top_iff R hR w

open Classical in
/-- *Doesn't have to* with *both* asserts the same of the sums of `R` with itself as of `R`. -/
theorem NL.notMustBoth_sums [DecidableEq Individual] (R : Finset (Plural Individual)) :
    Assert (NL.not (NL.must acc ((Finset.image₂ NL.and R R).image (NL.both pred)))) =
      Assert (NL.not (NL.must acc (R.image (NL.both pred)))) := by
  ext w
  simp only [mem_assert, NL.not_must_both_image_eq_one]
  exact exists_congr fun v => and_congr_right fun _ => forall_mem_image₂_and_self
    fun x y ⟨m, hm, h0⟩ => ⟨m, Finset.mem_union_left _ hm, h0⟩

open Classical in
/-- *Doesn't have to* with *both*, of `R` or of `R'`, is the same alternative for the memberwise
sums of `R` and `R'`. -/
theorem NL.assert_notMustBoth_union [DecidableEq Individual] (R R' : Finset (Plural Individual)) :
    Assert (NL.not (NL.must acc (R.image (NL.both pred)))) ∪
        Assert (NL.not (NL.must acc (R'.image (NL.both pred)))) =
      Assert (NL.not (NL.must acc ((Finset.image₂ NL.and R R').image (NL.both pred)))) := by
  ext w
  simp only [Set.mem_union, mem_assert, NL.not_must_both_image_eq_one, ← exists_or,
    ← and_or_left]
  refine exists_congr fun v => and_congr_right fun _ =>
    ⟨?_, fun h => by_contra fun hn => ?_⟩
  · rintro (h | h) z hz <;> obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hz
    · obtain ⟨m, hm, h0⟩ := h x hx
      exact ⟨m, Finset.mem_union_left _ hm, h0⟩
    · obtain ⟨m, hm, h0⟩ := h y hy
      exact ⟨m, Finset.mem_union_right _ hm, h0⟩
  · push Not at hn
    obtain ⟨⟨x, hx, hx0⟩, y, hy, hy0⟩ := hn
    obtain ⟨m, hm, h0⟩ := h _ (Finset.mem_image₂_of_mem hx hy)
    rcases Finset.mem_union.mp hm with hm | hm
    exacts [hx0 m hm h0, hy0 m hm h0]

/-- *Taro doesn't have to drink both of x ⊕ y* is the union of the alternatives for `x` and for
`y`. -/
theorem NL.assert_notMustBoth_and [DecidableEq Individual] (u v : Plural Individual) :
    Assert (NL.not (NL.must acc {NL.both pred (NL.and u v)})) =
      Assert (NL.not (NL.must acc {NL.both pred u})) ∪
        Assert (NL.not (NL.must acc {NL.both pred v})) := by
  ext w
  simp only [mem_assert, Set.mem_union, NL.not_must_both_eq_one, NL.and, Finset.mem_union,
    or_and_right, exists_or, and_or_left]

include hU hI in
/-- With unconstrained accessibility and independent atoms,
*Taro doesn't have to drink both of `u`* entails the same for `v` only if the atoms of `u` are
among those of `v`. -/
theorem NL.notMustBoth_not_subset {u v : Plural Individual} (huv : ¬ u.atoms ⊆ v.atoms) :
    ¬ Assert (NL.not (NL.must acc {NL.both pred u})) ⊆
      Assert (NL.not (NL.must acc {NL.both pred v})) := fun h => by
  obtain ⟨m, hmu, hmv⟩ := Finset.not_subset.mp huv
  obtain ⟨u0, hu0⟩ := hI.eq_zero_iff {m}
  obtain ⟨w, hw⟩ := hU {u0} (Finset.singleton_nonempty u0)
  obtain ⟨v', hv', m', hm', h0⟩ := NL.not_must_both_eq_one.mp
    (h (NL.not_must_both_eq_one.mpr
      ⟨u0, by rw [hw]; exact Finset.mem_singleton_self u0, m, hmu, (hu0 m).mpr rfl⟩))
  rw [hw, Finset.mem_singleton] at hv'
  subst hv'
  exact hmv (Set.mem_singleton_iff.mp ((hu0 m').mp h0) ▸ hm')

end

end Composition
