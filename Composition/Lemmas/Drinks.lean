import Composition.Examples.Drinks
import Composition.Lemmas.Ontology
import Composition.Lexicon
import Mathlib.Data.Finset.Powerset

/-!
# Lemmas on the model with three drinks

Auxiliary: optional reading.  The values of the sentences at the worlds of the model, the
pluralities of drinks listed, and the finite checks behind the permission states, for the
illustrations.
-/

namespace Composition.Drinks

open Drink

theorem pure_atoms {α : Type} {a : α} : (Plural.pure a).atoms = {a} :=
  rfl

theorem drank_only {d : Drink} {s : Finset Drink} : drank d (only s) = 1 ↔ d ∈ s := by
  by_cases h : d ∈ s <;> simp [drank, only, h]

theorem drank_only_eq_zero {d : Drink} {s : Finset Drink} : drank d (only s) = 0 ↔ d ∉ s := by
  by_cases h : d ∈ s <;> simp [drank, only, h]

theorem mem_acc {v : DrinkWorld} {s : Finset Drink} {V : List DrinkWorld} :
    v ∈ acc ⟨s, V⟩ ↔ v ∈ V := by
  simp [acc]

theorem acc_nonempty {s : Finset Drink} {v : DrinkWorld} {V : List DrinkWorld} :
    (acc ⟨s, v :: V⟩).Nonempty :=
  ⟨v, by simp [acc]⟩

/-- At `only s`, *Taro drank `x`* is fully true iff the atoms of `x` are in `s`. -/
theorem star_only {x : Plural Drink} {s : Finset Drink} :
    ⋆drank x (only s) = 1 ↔ x.atoms ⊆ s := by
  rw [star_eq_one]
  simp [drank_only, Finset.subset_iff]

/-- At `only s`, *Taro drank `x`* is fully false iff the atoms of `x` are among the drinks
not in `s`. -/
theorem star_only_eq_zero {x : Plural Drink} {s : Finset Drink} :
    ⋆drank x (only s) = 0 ↔ x.atoms ⊆ {appleJuice, beer, cider} \ s := by
  have h0 : ∀ m, drank m (only s) = 0 ↔ m ∉ s := fun m => by
    by_cases h : m ∈ s <;> simp [drank, only, h]
  rw [star_eq_zero]
  simp only [h0, Finset.subset_iff, Finset.mem_sdiff]
  exact forall₂_congr fun m _ => by cases m <;> simp

/-- Every plurality with atoms in `s` has its atoms in `t` iff `s ⊆ t`. -/
theorem forall_plural_subset {s t : Finset Drink} :
    (∀ y : Plural Drink, y.atoms ⊆ s → y.atoms ⊆ t) ↔ s ⊆ t := by
  refine ⟨fun h => ?_, fun h y hy => hy.trans h⟩
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact Finset.empty_subset t
  · exact h ⟨s, hs⟩ subset_rfl

/-- `forall_plural_subset`, with the pluralities quantified over as alternatives. -/
theorem forall_univ_plural_subset {s t : Finset Drink} :
    (∀ y ∈ (Set.univ : Set (Plural Drink)), y.atoms ⊆ s → y.atoms ⊆ t) ↔ s ⊆ t := by
  simpa using forall_plural_subset

/-- A property of all pluralities of drinks, from the seven sets of atoms they can have. -/
theorem forall_plural {Ψ : Plural Drink → Prop}
    (h : ∀ s : Finset Drink, (s = {appleJuice} ∨ s = {beer} ∨ s = {cider} ∨
      s = {appleJuice, beer} ∨ s = {appleJuice, cider} ∨ s = {beer, cider} ∨
      s = {appleJuice, beer, cider}) → ∀ x : Plural Drink, x.atoms = s → Ψ x) :
    ∀ x ∈ (Set.univ : Set (Plural Drink)), Ψ x := by
  intro x _
  refine forall_finSubsets_three (a := appleJuice) (b := beer) (c := cider)
    (P := fun S => ∀ x : Plural Drink, x.atoms = S → Ψ x)
    ⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp),
      h _ (by simp)⟩ x.atoms ⟨x.nonempty, fun m _ => by cases m <;> simp⟩ x rfl

/-- A property of all pluralities of drinks is a property of each of the seven. -/
theorem forall_plural_iff {Ψ : Plural Drink → Prop} :
    (∀ y, Ψ y) ↔ Ψ (Plural.pure appleJuice) ∧ Ψ (Plural.pure beer) ∧ Ψ (Plural.pure cider) ∧
      Ψ (NL.and (Plural.pure appleJuice) (Plural.pure beer)) ∧
      Ψ (NL.and (Plural.pure appleJuice) (Plural.pure cider)) ∧
      Ψ (NL.and (Plural.pure beer) (Plural.pure cider)) ∧
      Ψ (NL.and (NL.and (Plural.pure appleJuice) (Plural.pure beer)) (Plural.pure cider)) := by
  refine ⟨fun h => ⟨h _, h _, h _, h _, h _, h _, h _⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ y => forall_plural (fun s hs x hx => ?_) y trivial⟩
  have key : ∀ z : Plural Drink, x.atoms = z.atoms → Ψ z → Ψ x := fun ⟨_, _⟩ h hz => by
    obtain ⟨_, _⟩ := x
    simp only at h
    subst h
    exact hz
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [key _ (hx.trans (by decide)) h1, key _ (hx.trans (by decide)) h2,
    key _ (hx.trans (by decide)) h3, key _ (hx.trans (by decide)) h4,
    key _ (hx.trans (by decide)) h5, key _ (hx.trans (by decide)) h6,
    key _ (hx.trans (by decide)) h7]

/-- At `only s`, `s` nonempty, the plurality of the drinks in `s` is the greatest that Taro
drank. -/
theorem greatest_only {s : Finset Drink} (hs : s.Nonempty) :
    ∃ x ∈ (Set.univ : Set (Plural Drink)), ⋆drank x (only s) = 1 ∧
      ∀ y ∈ (Set.univ : Set (Plural Drink)), ⋆drank y (only s) = 1 →
        y.atoms ⊆ x.atoms :=
  ⟨⟨s, hs⟩, trivial, star_only.mpr subset_rfl, fun _ _ hy => star_only.mp hy⟩

/-- At `only s`, the plurality of the drinks not in `s` (if any) is the greatest that Taro
drank none of. -/
theorem greatest_only_eq_zero {s : Finset Drink}
    (hs : (({appleJuice, beer, cider} : Finset Drink) \ s).Nonempty) :
    ∃ x ∈ (Set.univ : Set (Plural Drink)), ⋆drank x (only s) = 0 ∧
      ∀ y ∈ (Set.univ : Set (Plural Drink)), ⋆drank y (only s) = 0 →
        y.atoms ⊆ x.atoms :=
  ⟨⟨_, hs⟩, trivial, star_only_eq_zero.mpr subset_rfl,
    fun _ _ hy => star_only_eq_zero.mp hy⟩

/-! ## Permission states -/

/-- The three drinks, as a finite set. -/
abbrev threeDrinks : Finset Drink := {appleJuice, beer, cider}

theorem mem_permissionStates {s : Finset Drink} {w : DrinkWorld} :
    w ∈ permissionStates s ↔ ∃ L ∈ antichains, w = ⟨s, L.map only⟩ :=
  Iff.rfl

theorem mem_acc_map {s : Finset Drink} {L : List (Finset Drink)} {v : DrinkWorld} :
    v ∈ acc ⟨s, L.map only⟩ ↔ ∃ t ∈ L, only t = v := by
  rw [mem_acc, List.mem_map]

/-- From the permission state of `L`, Taro is allowed `y` iff its atoms are part of a member of
`L`. -/
theorem exists_acc_star {s : Finset Drink} {L : List (Finset Drink)} {y : Plural Drink} :
    (∃ v ∈ acc ⟨s, L.map only⟩, ⋆drank y v = 1) ↔ ∃ t ∈ L, y.atoms ⊆ t := by
  simp only [mem_acc_map, exists_exists_and_eq_and, star_only]

/-- The sets of atoms of a nonempty finite set of pluralities: a nonempty set of nonempty sets of
drinks. -/
theorem image_atoms_mem {R : Finset (Plural Drink)} (hR : R ∈ finSubsets Set.univ) :
    R.image Plural.atoms ∈ threeDrinks.powerset.powerset ∧ (R.image Plural.atoms).Nonempty ∧
      ∀ x ∈ R.image Plural.atoms, x.Nonempty := by
  refine ⟨Finset.mem_powerset.mpr fun x hx => ?_, hR.1.image _, fun x hx => ?_⟩ <;>
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
  · exact Finset.mem_powerset.mpr fun m _ => by cases m <;> simp
  · exact y.nonempty

theorem antichains_nonempty : ∀ L ∈ antichains, L ≠ [] ∧ ∀ t ∈ L, t.Nonempty := by
  decide +kernel

/-- Every antichain is the set of atoms of a nonempty finite set of pluralities. -/
theorem exists_index {L : List (Finset Drink)} (hL : L ∈ antichains) :
    ∃ R ∈ finSubsets (Set.univ : Set (Plural Drink)), R.image Plural.atoms = L.toFinset := by
  classical
  obtain ⟨hne, hne'⟩ := antichains_nonempty L hL
  have ht : ∀ t ∈ L.toFinset, t.Nonempty := fun t ht => hne' t (List.mem_toFinset.mp ht)
  refine ⟨L.toFinset.attach.image fun t => ⟨t.1, ht _ t.2⟩, ⟨?_, fun _ _ => trivial⟩, ?_⟩
  · obtain ⟨t, htL⟩ := List.exists_mem_of_ne_nil L hne
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_attach _ ⟨t, List.mem_toFinset.mpr htL⟩)⟩
  · ext x
    simp

open Classical in
/-- The cell condition of *can* at the permission state of `L`, on sets of atoms. -/
theorem can_cond_iff {s : Finset Drink} {L : List (Finset Drink)} {R : Finset (Plural Drink)} :
    (∀ y ∈ (Set.univ : Set (Plural Drink)),
      (∃ v ∈ acc ⟨s, L.map only⟩, ⋆drank y v = 1) ↔ ∃ x ∈ R, y.atoms ⊆ x.atoms) ↔
    ∀ y ∈ threeDrinks.powerset, y.Nonempty →
      ((∃ t ∈ L, y ⊆ t) ↔ ∃ x ∈ R.image Plural.atoms, y ⊆ x) := by
  simp only [exists_acc_star, Finset.mem_image, exists_exists_and_eq_and, Set.mem_univ,
    forall_const]
  exact ⟨fun h y _ hy => h ⟨y, hy⟩,
    fun h y => h y.atoms (Finset.mem_powerset.mpr fun m _ => by cases m <;> simp) y.nonempty⟩

open Classical in
/-- The cell condition of *must* at the permission state of `L`, on sets of atoms. -/
theorem must_cond_iff {s : Finset Drink} {L : List (Finset Drink)} {R : Finset (Plural Drink)} :
    ((∀ v ∈ acc ⟨s, L.map only⟩, ∃ x ∈ R, ⋆drank x v = 1) ∧
      ∀ x ∈ R, ∃ v ∈ acc ⟨s, L.map only⟩,
        ∀ y ∈ (Set.univ : Set (Plural Drink)), ⋆drank y v = 1 → y.atoms ⊆ x.atoms) ↔
    (∀ t ∈ L, ∃ x ∈ R.image Plural.atoms, x ⊆ t) ∧
      ∀ x ∈ R.image Plural.atoms, ∃ t ∈ L, t ⊆ x := by
  simp only [mem_acc_map, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, star_only, Finset.mem_image]
  exact and_congr_right fun _ => forall₂_congr fun x _ => exists_congr fun t =>
    and_congr_right fun _ => forall_univ_plural_subset

set_option maxRecDepth 100000 in
/-- Every nonempty set of nonempty sets of drinks allows, under *can*, what some antichain
allows. -/
theorem can_live : ∀ T ∈ threeDrinks.powerset.powerset, T.Nonempty → (∀ x ∈ T, x.Nonempty) →
    ∃ L ∈ antichains, ∀ y ∈ threeDrinks.powerset, y.Nonempty →
      ((∃ t ∈ L, y ⊆ t) ↔ ∃ x ∈ T, y ⊆ x) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Distinct antichains allow different things under *can*. -/
theorem can_inj : ∀ L ∈ antichains, ∀ L' ∈ antichains,
    (∀ y ∈ threeDrinks.powerset, y.Nonempty → ((∃ t ∈ L, y ⊆ t) ↔ ∃ t ∈ L', y ⊆ t)) →
      L = L' := by
  decide +kernel

/-! ## Prohibition states -/

theorem mem_prohibitionStates {s : Finset Drink} {w : DrinkWorld} :
    w ∈ prohibitionStates s ↔ ∃ L ∈ antichains, w = prohibitionState s L :=
  Iff.rfl

theorem mem_drinkSets (t : Finset Drink) : t ∈ drinkSets := by
  have h : ∀ t ∈ threeDrinks.powerset, t ∈ drinkSets := by decide
  exact h t (Finset.mem_powerset.mpr fun m _ => by cases m <;> simp)

/-- From the prohibition state of `L`, Taro may not drink `y` in full iff its atoms include a
member of `L`. -/
theorem prohibited_iff {s : Finset Drink} {L : List (Finset Drink)} {y : Plural Drink} :
    (∀ v ∈ acc (prohibitionState s L), ∃ m ∈ y.atoms, drank m v = 0) ↔
      ∃ t ∈ L, t ⊆ y.atoms := by
  simp only [prohibitionState, mem_acc_map, List.mem_filter, decide_eq_true_eq,
    forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    obtain ⟨m, hm, h0⟩ := h _ y.atoms (mem_drinkSets _) hn rfl
    exact drank_only_eq_zero.mp h0 hm
  · rintro ⟨x, hx, hxy⟩ _ t _ ht rfl
    obtain ⟨m, hm, hmt⟩ := Finset.not_subset.mp fun hyt => ht x hx (hxy.trans hyt)
    exact ⟨m, hm, drank_only_eq_zero.mpr hmt⟩

open Classical in
/-- The cell condition of *can't* with *both* at the prohibition state of `L`, on sets of atoms. -/
theorem cant_cond_iff {s : Finset Drink} {L : List (Finset Drink)} {R : Finset (Plural Drink)} :
    (∀ y ∈ (Set.univ : Set (Plural Drink)),
      (∀ v ∈ acc (prohibitionState s L), ∃ m ∈ y.atoms, drank m v = 0) ↔
        ∃ x ∈ R, x.atoms ⊆ y.atoms) ↔
    ∀ y ∈ threeDrinks.powerset, y.Nonempty →
      ((∃ t ∈ L, t ⊆ y) ↔ ∃ x ∈ R.image Plural.atoms, x ⊆ y) := by
  simp only [prohibited_iff, Finset.mem_image, exists_exists_and_eq_and, Set.mem_univ,
    forall_const]
  exact ⟨fun h y _ hy => h ⟨y, hy⟩,
    fun h y => h y.atoms (Finset.mem_powerset.mpr fun m _ => by cases m <;> simp) y.nonempty⟩

set_option maxRecDepth 100000 in
/-- Every nonempty set of nonempty sets of drinks prohibits, under *can't* with *both*, what some
antichain prohibits. -/
theorem cant_live : ∀ T ∈ threeDrinks.powerset.powerset, T.Nonempty → (∀ x ∈ T, x.Nonempty) →
    ∃ L ∈ antichains, ∀ y ∈ threeDrinks.powerset, y.Nonempty →
      ((∃ t ∈ L, t ⊆ y) ↔ ∃ x ∈ T, x ⊆ y) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Distinct antichains prohibit different things under *can't* with *both*. -/
theorem cant_inj : ∀ L ∈ antichains, ∀ L' ∈ antichains,
    (∀ y ∈ threeDrinks.powerset, y.Nonempty → ((∃ t ∈ L, t ⊆ y) ↔ ∃ t ∈ L', t ⊆ y)) →
      L = L' := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Every nonempty set of nonempty sets of drinks requires, under *must*, what some antichain
requires. -/
theorem must_live : ∀ T ∈ threeDrinks.powerset.powerset, T.Nonempty → (∀ x ∈ T, x.Nonempty) →
    ∃ L ∈ antichains, (∀ t ∈ L, ∃ x ∈ T, x ⊆ t) ∧ ∀ x ∈ T, ∃ t ∈ L, t ⊆ x := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Distinct antichains require different things under *must*. -/
theorem must_inj : ∀ L ∈ antichains, ∀ L' ∈ antichains,
    (∀ t ∈ L, ∃ t' ∈ L', t' ⊆ t) → (∀ t' ∈ L', ∃ t ∈ L, t ⊆ t') → L = L' := by
  decide +kernel

/-- A set of worlds of the states `st L` of the antichains `L`, characterized by a condition `P`
on antichains that holds of at most one antichain, is the singleton of the state of the one it
holds of. -/
theorem eq_singleton_of_unique {st : List (Finset Drink) → DrinkWorld} {C : Set DrinkWorld}
    {P : List (Finset Drink) → Prop}
    (hC : ∀ w, w ∈ C ↔ ∃ L ∈ antichains, w = st L ∧ P L)
    (huniq : ∀ L ∈ antichains, ∀ L' ∈ antichains, P L → P L' → L = L')
    {L : List (Finset Drink)} (hL : L ∈ antichains) (h : P L) : C = {st L} := by
  ext w
  rw [hC, Set.mem_singleton_iff]
  constructor
  · rintro ⟨L', hL', rfl, h'⟩
    rw [huniq L' hL' L hL h' h]
  · rintro rfl
    exact ⟨L, hL, rfl, h⟩

end Composition.Drinks
