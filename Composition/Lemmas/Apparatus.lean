import Composition.Apparatus
import Composition.Questions

/-!
# Lemmas on the formal apparatus and the question semantics

Auxiliary: optional reading.  Nothing declared here occurs in a statement or in a definition
body of a readable file; `Composition.Audit` checks this at every build.
-/

namespace Composition

variable {World : Type}

/-! ## Truth values -/

section
variable {α : Type} {s : Finset α} {f : α → Truth}

theorem Truth.not_not (t : Truth) : Truth.not (Truth.not t) = t :=
  Subtype.ext (sub_sub_cancel (1 : ℚ) t)

theorem Truth.not_zero : Truth.not 0 = 1 :=
  Subtype.ext (sub_zero 1)

/-- Negation reverses the order of truth values. -/
theorem Truth.not_antitone : Antitone Truth.not := fun _ _ h =>
  sub_le_sub_left (Subtype.coe_le_coe.mpr h) 1

theorem Truth.eq_one {t : Truth} : t = 1 ↔ 1 ≤ t :=
  ⟨fun h => h.ge, le_antisymm Set.Icc.le_one⟩

theorem Truth.eq_zero {t : Truth} : t = 0 ↔ t ≤ 0 :=
  ⟨fun h => h.le, fun h => le_antisymm h Set.Icc.nonneg⟩

theorem Truth.not_one_le_zero : ¬ (1 : Truth) ≤ 0 := fun h =>
  absurd (Subtype.coe_le_coe.mpr h) (by simp)

/-- A maximum is `1` iff some value is `1`, and `0` iff every value is `0`. -/
theorem fold_max_eq_one : s.fold max 0 f = 1 ↔ ∃ x ∈ s, f x = 1 := by
  simp only [Truth.eq_one, Finset.le_fold_max, Truth.not_one_le_zero, false_or]
@[inherit_doc fold_max_eq_one]
theorem fold_max_eq_zero : s.fold max 0 f = 0 ↔ ∀ x ∈ s, f x = 0 := by
  simp only [Truth.eq_zero, Finset.fold_max_le, le_refl, true_and]

/-- A minimum is `1` iff every value is `1`, and `0` iff some value is `0`. -/
theorem fold_min_eq_one : s.fold min 1 f = 1 ↔ ∀ x ∈ s, f x = 1 := by
  simp only [Truth.eq_one, Finset.le_fold_min, le_refl, true_and]
@[inherit_doc fold_min_eq_one]
theorem fold_min_eq_zero : s.fold min 1 f = 0 ↔ ∃ x ∈ s, f x = 0 := by
  simp only [Truth.eq_zero, Finset.fold_min_le, Truth.not_one_le_zero, false_or]

/-- An average over a nonempty set is `1` iff every value is `1`. -/
theorem avg_eq_one (hs : s.Nonempty) :
    avg s f = 1 ↔ ∀ x ∈ s, f x = 1 := by
  have card_ne : (s.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  have sum_one : ∑ _x ∈ s, (1 : ℚ) = s.card := by rw [Finset.sum_const, nsmul_one]
  rw [← Set.Icc.coe_eq_one]
  change (∑ x ∈ s, (f x : ℚ)) / s.card = 1 ↔ _
  rw [div_eq_one_iff_eq card_ne, ← sum_one, Finset.sum_eq_sum_iff_of_le fun x _ => (f x).2.2]
  simp only [Set.Icc.coe_eq_one]

/-- An average is `0` iff every value is `0`. -/
theorem avg_eq_zero :
    avg s f = 0 ↔ ∀ x ∈ s, f x = 0 := by
  have empty_case : s = ∅ → ∀ x ∈ s, (f x : ℚ) = 0 := by
    rintro rfl x hx
    exact absurd hx (Finset.notMem_empty x)
  rw [← Set.Icc.coe_eq_zero]
  change (∑ x ∈ s, (f x : ℚ)) / s.card = 0 ↔ _
  rw [div_eq_zero_iff, Nat.cast_eq_zero, Finset.card_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun x _ => (f x).2.1, or_iff_left_of_imp empty_case]
  simp only [Set.Icc.coe_eq_zero]

end

/-! ## Fuzzy logic -/

theorem Fz.not_not (r : FuzzyP) : Fz.not (Fz.not r) = r :=
  funext fun w => Truth.not_not (r w)

/-- `bigOr` sends `{r}` to `r`. -/
theorem bigOr_singleton (r : FuzzyP) : bigOr {r} = r :=
  funext fun _ => max_eq_left Set.Icc.nonneg

open Classical in
/-- `bigOr` sends unions to `Fz.or`. -/
theorem bigOr_union (R S : Finset FuzzyP) : bigOr (R ∪ S) = Fz.or (bigOr R) (bigOr S) := by
  funext w
  apply le_antisymm
  · refine (Finset.fold_max_le _).mpr ⟨Set.Icc.nonneg, fun r hr => ?_⟩
    rcases Finset.mem_union.mp hr with h | h
    · exact le_max_of_le_left ((Finset.le_fold_max _).mpr (Or.inr ⟨r, h, le_rfl⟩))
    · exact le_max_of_le_right ((Finset.le_fold_max _).mpr (Or.inr ⟨r, h, le_rfl⟩))
  · exact max_le
      ((Finset.fold_max_le _).mpr ⟨Set.Icc.nonneg, fun r hr =>
        (Finset.le_fold_max _).mpr (Or.inr ⟨r, Finset.mem_union_left S hr, le_rfl⟩)⟩)
      ((Finset.fold_max_le _).mpr ⟨Set.Icc.nonneg, fun r hr =>
        (Finset.le_fold_max _).mpr (Or.inr ⟨r, Finset.mem_union_right R hr, le_rfl⟩)⟩)

/-! ## Modal operators -/

section
variable (acc : World → Finset World) {r : FuzzyP} {w : World}

/-- `□¬r = ¬◇r`, for any values. -/
theorem Fz.box_not (r : FuzzyP) : Fz.box acc (Fz.not r) = Fz.not (Fz.diamond acc r) := by
  funext w
  have h := Finset.fold_hom (s := acc w) (op := max) (op' := min) (b := 0) (f := r)
    (m := Truth.not) fun _ _ => Truth.not_antitone.map_max
  rwa [Truth.not_zero] at h

/-- `◇¬r = ¬□r`, for any values. -/
theorem Fz.diamond_not (r : FuzzyP) : Fz.diamond acc (Fz.not r) = Fz.not (Fz.box acc r) := by
  rw [← Fz.not_not (Fz.diamond acc _), ← Fz.box_not, Fz.not_not]

/-- `◇r` is fully true iff `r` is fully true at some accessible world, and fully false iff `r` is
fully false at every one. -/
theorem Fz.diamond_eq_one : Fz.diamond acc r w = 1 ↔ ∃ v ∈ acc w, r v = 1 := fold_max_eq_one
@[inherit_doc Fz.diamond_eq_one]
theorem Fz.diamond_eq_zero : Fz.diamond acc r w = 0 ↔ ∀ v ∈ acc w, r v = 0 := fold_max_eq_zero

/-- `□r` is fully true iff `r` is fully true at every accessible world, and fully false iff `r` is
fully false at some. -/
theorem Fz.box_eq_one : Fz.box acc r w = 1 ↔ ∀ v ∈ acc w, r v = 1 := fold_min_eq_one
@[inherit_doc Fz.box_eq_one]
theorem Fz.box_eq_zero : Fz.box acc r w = 0 ↔ ∃ v ∈ acc w, r v = 0 := fold_min_eq_zero

end

/-! ## Assertion and matching -/

theorem mem_assert {r : FuzzyP} {w : World} : w ∈ Assert r ↔ r w = 1 :=
  Iff.rfl

/-- **The cell of an indexed alternative**: when `P x` entails `P y` exactly when `le y x`,
`P x` is the strongest alternative fully true at `w` iff it is fully true there and every
alternative fully true there is below `x`. -/
theorem mem_exh_image_iff {ι : Type} {A : Set ι} {P : ι → FuzzyP} (le : ι → ι → Prop)
    (ent : ∀ x ∈ A, ∀ y ∈ A, Assert (P x) ⊆ Assert (P y) ↔ le y x) {x : ι} (hx : x ∈ A)
    (w : World) :
    w ∈ exh ((Assert ·) '' (P '' A)) (Assert (P x)) ↔
    P x w = 1 ∧ ∀ y ∈ A, P y w = 1 → le y x := by
  rw [mem_exh]
  simp only [Set.forall_mem_image, mem_assert]
  exact and_congr_right fun _ => forall₂_congr fun y hy =>
    imp_congr_right fun _ => ent x hx y hy

/-- The union of two incomparable members `p`, `q` of `Q` is the strongest fully true member of `Q`
nowhere: wherever it is true, `p` or `q` is true, and stronger. -/
theorem exh_union_eq_empty {Q : Set (Set World)} {p q : Set World} (hp : p ∈ Q) (hq : q ∈ Q)
    (hnq : ¬ q ⊆ p) (hnp : ¬ p ⊆ q) : exh Q (p ∪ q) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun w hw => ?_
  obtain ⟨hwpq, hs⟩ := mem_exh.mp hw
  rcases hwpq with hwp | hwq
  · exact hnq (Set.subset_union_right.trans (hs p hp hwp))
  · exact hnp (Set.subset_union_left.trans (hs q hq hwq))

/-- Matching's two conditions, with the cells as sets or as membership: every cell meets `k`,
and every world of `k` lies in a cell. -/
theorem live_cover_iff {ι : Type} {A : Set ι} {C : ι → Set World} {k : Set World} :
    ((∀ x ∈ A, (k ∩ C x).Nonempty) ∧ k ⊆ ⋃ x ∈ A, C x) ↔
    ((∀ x ∈ A, ∃ w ∈ k, w ∈ C x) ∧ ∀ w ∈ k, ∃ x ∈ A, w ∈ C x) := by
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.subset_def, Set.mem_iUnion₂, exists_prop]

/-- **Indexed alternatives**: when `P x` entails `P y` exactly when `le y x`, and `C x` is the
set of worlds of `k` where `P x` is fully true and every alternative fully true is below `x` (the
cell of `P x`), the alternatives `P x` match `k` iff each cell `C x` meets `k` and the cells cover
`k`.  Only the worlds of `k` matter, so `C x` need describe the cell there only. -/
theorem matches_image_iff {ι : Type} {A : Set ι} {P : ι → FuzzyP} {k : Set World}
    (le : ι → ι → Prop) (C : ι → Set World)
    (ent : ∀ x ∈ A, ∀ y ∈ A, Assert (P x) ⊆ Assert (P y) ↔ le y x)
    (top : ∀ x ∈ A, ∀ w ∈ k, (P x w = 1 ∧ ∀ y ∈ A, P y w = 1 → le y x) ↔ w ∈ C x) :
    Matches k ((Assert ·) '' (P '' A)) ↔
    (∀ x ∈ A, (k ∩ C x).Nonempty) ∧ k ⊆ ⋃ x ∈ A, C x := by
  have key : ∀ x ∈ A, ∀ w ∈ k,
      w ∈ exh ((Assert ·) '' (P '' A)) (Assert (P x)) ↔ w ∈ C x :=
    fun x hx w hw => (mem_exh_image_iff le ent hx w).trans (top x hx w hw)
  rw [matches_iff]
  simp only [Set.forall_mem_image, Set.Nonempty, Set.mem_inter_iff, Set.subset_def,
    Set.mem_iUnion₂, exists_prop, Set.exists_mem_image]
  exact and_congr
    (forall₂_congr fun x hx => exists_congr fun w => and_congr_right fun hw => key x hx w hw)
    (forall₂_congr fun w hw => exists_congr fun x => and_congr_right fun hx => key x hx w hw)

end Composition
