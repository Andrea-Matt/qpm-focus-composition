import Composition.Ontology
import Composition.Lemmas.Apparatus

/-!
# Lemmas on the ontology

Auxiliary: optional reading.  Nothing declared here occurs in a statement or in a definition
body of a readable file; `Composition.Audit` checks this at every build.
-/

namespace Composition

variable {World : Type}

/-! ## Pluralities -/

section
variable {α : Type} (pred : α → FuzzyP) (x : Plural α) {w : World}

/-- **Homogeneity, positive side**: `⋆pred x` is fully true iff `pred` is fully true of every
atom of `x`. -/
theorem star_eq_one : ⋆pred x w = 1 ↔ ∀ m ∈ x.atoms, pred m w = 1 :=
  avg_eq_one x.nonempty

/-- **Homogeneity, negative side**: `⋆pred x` is fully false (so *not ⋆pred x* is fully
true) iff `pred` is fully false of every atom of `x`. -/
theorem star_eq_zero : ⋆pred x w = 0 ↔ ∀ m ∈ x.atoms, pred m w = 0 :=
  avg_eq_zero

/-- If `⋆pred` is fully true of a plurality, it is fully true of any with fewer atoms. -/
theorem star_eq_one_of_subset {y : Plural α} (h : y.atoms ⊆ x.atoms) :
    ⋆pred x w = 1 → ⋆pred y w = 1 := by
  rw [star_eq_one, star_eq_one]
  exact fun hx m hm => hx m (h hm)

end

/-! ## Independence -/

section
variable {α : Type} {pred : α → FuzzyP} (hI : Independent pred) (S : Set α)
include hI

/-- Under independence, some world makes `pred` fully true exactly on `S`. -/
theorem Independent.eq_one_iff : ∃ w, ∀ m, pred m w = 1 ↔ m ∈ S := by
  obtain ⟨w, hw⟩ := hI S
  refine ⟨w, fun m => ⟨fun h => by_contra fun hn => ?_, (hw m).1⟩⟩
  exact Truth.not_one_le_zero (h.symm.trans ((hw m).2 hn)).le

/-- Under independence, some world makes `pred` fully false exactly on `S`. -/
theorem Independent.eq_zero_iff : ∃ w, ∀ m, pred m w = 0 ↔ m ∈ S := by
  obtain ⟨w, hw⟩ := hI Sᶜ
  refine ⟨w, fun m => ⟨fun h => by_contra fun hn => ?_,
    fun hm => (hw m).2 (not_not_intro hm)⟩⟩
  exact Truth.not_one_le_zero (((hw m).1 hn).symm.trans h).le

end

/-! ## Focus -/

/-- The cells of a focus structure depend only on its alternatives. -/
theorem Focus.cell_congr {F G : Focus FuzzyP} (h : F.alts = G.alts) (k : Set World)
    (r : FuzzyP) : F.cell k r = G.cell k r := by
  unfold Focus.cell
  rw [h]

/-! ## Focus on sets -/

/-- A property of the nonempty finite subsets of a set of three holds of all of them if it holds
of the seven listed. -/
theorem forall_finSubsets_three {α : Type} [DecidableEq α] {a b c : α} {P : Finset α → Prop}
    (h : P {a} ∧ P {b} ∧ P {c} ∧ P {a, b} ∧ P {a, c} ∧ P {b, c} ∧ P {a, b, c}) :
    ∀ R ∈ finSubsets {a, b, c}, P R := by
  rintro R ⟨hne, hsub⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have key : ∀ m ∈ R, m = a ∨ m = b ∨ m = c := fun m hm => by simpa using hsub hm
  have eq : ∀ S : Finset α, P S → S ⊆ R → (∀ m ∈ R, m ∈ S) → P R :=
    fun S hP h h' => Finset.Subset.antisymm h h' ▸ hP
  by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;> by_cases hc : c ∈ R
  · exact eq _ h7 (by simp [Finset.insert_subset_iff, *]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h4 (by simp [Finset.insert_subset_iff, *]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h5 (by simp [Finset.insert_subset_iff, *]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h1 (by simp [*]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h6 (by simp [Finset.insert_subset_iff, *]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h2 (by simp [*]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · exact eq _ h3 (by simp [*]) fun m hm => by
      rcases key m hm with rfl | rfl | rfl <;> simp_all
  · obtain ⟨m, hm⟩ := hne
    rcases key m hm with rfl | rfl | rfl <;> contradiction

end Composition
