import Composition.Lemmas.Lexicon
import Composition.Lemmas.Drinks

/-!
# Predictions with modals

The modals (duality, free choice, double prohibition), then four focus cases: *can* and *must*
with *[a]_F or [b]_F*, and *can't* and *doesn't have to* with *both [a]_F and [b]_F*.  As without
modals, each case is stated by the exact contexts it matches (`_matches_iff`, or `_fails` when
there are none), and each case that matches is illustrated in the model with three drinks
(`Drinks`).  Each section declares the variables of its general theorems; a hypothesis used only
inside a proof (`hU`, `hI`) is added to a theorem by `include … in` above it, and the illustrations
use none of the variables.  Readable.
-/

namespace Composition

variable {World Individual : Type}

/-! ## The modals: duality, free choice, double prohibition -/

section
variable (acc : World → Finset World) {w : World}

/-- **Duality on singletons**: *can r* is *not must not r*. -/
theorem NL.can_eq_not_must_not (r : FuzzyP) :
    NL.can acc {r} = NL.not (NL.must acc {NL.not r}) := by
  unfold NL.not
  rw [NL.can_singleton, NL.must_singleton, Fz.box_not, Fz.not_not]

/-- **Duality on singletons**: *must r* is *not can not r*. -/
theorem NL.must_eq_not_can_not (r : FuzzyP) :
    NL.must acc {r} = NL.not (NL.can acc {NL.not r}) := by
  unfold NL.not
  rw [NL.can_singleton, NL.must_singleton, Fz.diamond_not, Fz.not_not]

open Classical in
/-- **`must` sees only the disjunction**: *must (r or s)* is *must (r ∨ s)*, for any
values. -/
theorem NL.must_or (r s : FuzzyP) :
    NL.must acc (NL.or {r} {s}) = NL.must acc {Fz.or r s} := by
  rw [NL.must, NL.must, NL.or, bigOr_union, bigOr_singleton, bigOr_singleton, bigOr_singleton]

open Classical in
/-- **Free choice**: *can (r or s)* is fully true iff each of `r`, `s` is fully true at some
accessible world. -/
theorem NL.freeChoice {r s : FuzzyP} :
    NL.can acc (NL.or {r} {s}) w = 1 ↔
    (∃ v ∈ acc w, r v = 1) ∧ ∃ v ∈ acc w, s v = 1 := by
  rw [NL.or, NL.can_eq_one acc ((Finset.singleton_nonempty r).mono Finset.subset_union_left)]
  simp

open Classical in
/-- **Double prohibition**: *not can (r or s)* is fully true iff neither `r` nor `s` is true to
any degree at an accessible world. -/
theorem NL.doubleProhibition {r s : FuzzyP} :
    NL.not (NL.can acc (NL.or {r} {s})) w = 1 ↔
    (∀ v ∈ acc w, r v = 0) ∧ ∀ v ∈ acc w, s v = 0 := by
  rw [NL.not_eq_one, NL.or, NL.can_eq_zero]
  simp

end

/-! ## Disjunction under a modal

*Taro can drink [a]_F or [b]_F* and *Taro must drink [a]_F or [b]_F*.  *Or* joins the disjuncts
lifted inside focus (`Focus.finsets`) and `⋆pred` applies to each member, so the modal takes a
focused set whose alternatives are the images of the nonempty finite sets `R` of alternatives
(`NL.or_finsets_alts`): the alternative indexed by `R = {x₁, …, xₙ}` is the modal applied to
`R.image (⋆pred)`, *Taro can (must) drink x₁ or … or xₙ*.  Under *can* each member is allowed;
under *must* every accessible world makes Taro drink one of them.  Accessibility is
unconstrained and the atoms are independent; `⋆pred x` is *Taro drinks x*. -/

section
variable (acc : World → Finset World) (hU : Unconstrained acc) (pred : Individual → FuzzyP)
  (hI : Independent pred) {A : Set (Plural Individual)} {a b : Plural Individual} (ha : a ∈ A)
  (hb : b ∈ A) {k : Set World}

open Classical in
include hU hI in
/-- ***Can* with *[a]_F or [b]_F* (free choice)**: *Taro can drink [a]_F or [b]_F* matches `k` iff
* (a) every alternative is the strongest true one at some world of `k`: `k` leaves every answer
  open; and
* (b) at every world of `k` some alternative is the strongest true one.

The alternatives are indexed by the nonempty finite sets `R` of members of `A`
(`NL.or_finsets_alts`): *can R* is *Taro can drink x₁ or … or xₙ*.  The strongest true alternative
at `w` is *can R* (`w` is in `cell R`) iff the members of `A` Taro is allowed there are exactly
those that are part of a member of `R`. -/
theorem NL.canOr_matches_iff :
    (NL.can acc <$> ((⋆pred <$> ·) <$>
      (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).Matches k ↔
    let cell R := {w | ∀ y ∈ A, (∃ v ∈ acc w, ⋆pred y v = 1) ↔ ∃ x ∈ R, y.atoms ⊆ x.atoms}
    (∀ R ∈ finSubsets A, ∃ w ∈ k, w ∈ cell R) ∧ ∀ w ∈ k, ∃ R ∈ finSubsets A, w ∈ cell R :=
  (NL.set_matches_iff pred _ _ (NL.or_finsets_alts pred ha hb) _ (NL.can_subset_iff acc hU pred hI)
    (fun R => {w | ∀ y ∈ A, (∃ v ∈ acc w, ⋆pred y v = 1) ↔ ∃ x ∈ R, y.atoms ⊆ x.atoms})
    fun R hR w _ => NL.can_top_iff acc pred R hR w).trans live_cover_iff

open Classical Drinks Drinks.Drink in
/-- ***Can* with *[a]_F or [b]_F*, illustrated** (model: `Drinks`).  The alternatives are all the
pluralities of drinks (`Set.univ`).  The context, `permissionStates s`, has eighteen
possibilities, one for each antichain `L` of sets of drinks: from it, the accessible worlds are
those where Taro drank exactly the drinks of a member of `L`.  What Taro actually drank there is
left open (`s`).

*Taro can drink [apple juice]_F or [beer]_F* matches the context.  Its 127 indices `R` give
eighteen distinct alternatives, and each `R` selects exactly one possibility, the one whose
antichain `L` is the set of maximal members of `R`.  Six of them are listed;
*can drink apple juice, or apple juice and beer* selects the possibility where apple juice and
beer together are allowed. -/
theorem NL.canOr_illustration (s : Finset Drink) :
    let F := NL.can Drinks.acc <$> ((⋆drank <$> ·) <$>
      (NL.or <$> (Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)).finsets <*>
        (Foc Set.univ (Plural.pure beer) (Set.mem_univ _)).finsets))
    let k : Set DrinkWorld := permissionStates s
    F.Matches k ∧
    (∀ R ∈ finSubsets Set.univ, ∃ w, F.cell k (NL.can Drinks.acc (R.image (⋆drank))) = {w}) ∧
    F.cell k (NL.can Drinks.acc {⋆drank (Plural.pure appleJuice)}) =
      {⟨s, [only {appleJuice}]⟩} ∧
    F.cell k (NL.can Drinks.acc {⋆drank (Plural.pure appleJuice), ⋆drank (Plural.pure beer)}) =
      {⟨s, [only {appleJuice}, only {beer}]⟩} ∧
    F.cell k (NL.can Drinks.acc {⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))}) =
      {⟨s, [only {appleJuice, beer}]⟩} ∧
    F.cell k (NL.can Drinks.acc {⋆drank (Plural.pure appleJuice),
        ⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))}) =
      {⟨s, [only {appleJuice, beer}]⟩} ∧
    F.cell k (NL.can Drinks.acc {⋆drank (Plural.pure appleJuice), ⋆drank (Plural.pure beer),
        ⋆drank (Plural.pure cider)}) =
      {⟨s, [only {appleJuice}, only {beer}, only {cider}]⟩} ∧
    F.cell k (NL.can Drinks.acc {⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer)),
        ⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider)),
        ⋆drank (NL.and (Plural.pure beer) (Plural.pure cider))}) =
      {⟨s, [only {appleJuice, beer}, only {appleJuice, cider}, only {beer, cider}]⟩} := by
  intro F k
  have cell : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ w,
      w ∈ F.cell k (NL.can Drinks.acc (R.image (⋆drank))) ↔
      ∃ L ∈ antichains, w = ⟨s, L.map only⟩ ∧ ∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, y ⊆ t) ↔ ∃ x ∈ R.image Plural.atoms, y ⊆ x) := fun R hR w => by
    rw [NL.mem_canOr_cell Drinks.acc unconstrained drank independent _ _ hR, mem_permissionStates]
    constructor
    · rintro ⟨⟨L, hL, rfl⟩, h⟩
      exact ⟨L, hL, rfl, can_cond_iff.mp h⟩
    · rintro ⟨L, hL, rfl, h⟩
      exact ⟨⟨L, hL, rfl⟩, can_cond_iff.mpr h⟩
  have cell_eq : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ S, R.image (⋆drank) = S →
      ∀ L ∈ antichains, (∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, y ⊆ t) ↔ ∃ x ∈ R.image Plural.atoms, y ⊆ x)) →
      F.cell k (NL.can Drinks.acc S) = {⟨s, L.map only⟩} := by
    rintro R hR S rfl L hL h
    exact eq_singleton_of_unique (cell R hR) (fun L hL L' hL' h h' =>
      can_inj L hL L' hL' fun y hy hyn => (h y hy hyn).trans (h' y hy hyn).symm) hL h
  have live : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∃ L ∈ antichains,
      ∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, y ⊆ t) ↔ ∃ x ∈ R.image Plural.atoms, y ⊆ x) := fun R hR =>
    can_live _ (image_atoms_mem hR).1 (image_atoms_mem hR).2.1 (image_atoms_mem hR).2.2
  refine ⟨(NL.canOr_matches_iff Drinks.acc unconstrained drank independent _ _).mpr
      ⟨fun R hR => ?_, fun w hw => ?_⟩, fun R hR => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, mem_permissionStates.mpr ⟨L, hL, rfl⟩, can_cond_iff.mpr h⟩
  · obtain ⟨L, hL, rfl⟩ := mem_permissionStates.mp hw
    obtain ⟨R, hR, hRL⟩ := exists_index hL
    exact ⟨R, hR, can_cond_iff.mpr fun y _ _ => by rw [hRL]; simp⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, cell_eq R hR _ rfl L hL h⟩
  · exact cell_eq {Plural.pure appleJuice} (by simp [finSubsets]) _ (by simp) [{appleJuice}]
      (by decide) (by simp [pure_atoms])
  · exact cell_eq {Plural.pure appleJuice, Plural.pure beer} (by simp [finSubsets]) _ (by simp)
      [{appleJuice}, {beer}] (by decide) (by simp [pure_atoms])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer)} (by simp [finSubsets]) _
      (by simp) [{appleJuice, beer}] (by decide) (by simp [pure_atoms, NL.and])
  · exact cell_eq {Plural.pure appleJuice, NL.and (Plural.pure appleJuice) (Plural.pure beer)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice, beer}] (by decide)
      (by
        simp only [Finset.mem_powerset, List.mem_cons, List.not_mem_nil, or_false,
          exists_eq_left, Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, ↓existsAndEq, true_and]
        decide)
  · exact cell_eq {Plural.pure appleJuice, Plural.pure beer, Plural.pure cider}
      (by simp [finSubsets]) _ (by simp) [{appleJuice}, {beer}, {cider}] (by decide)
      (by simp [pure_atoms])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer),
        NL.and (Plural.pure appleJuice) (Plural.pure cider),
        NL.and (Plural.pure beer) (Plural.pure cider)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice, beer}, {appleJuice, cider}, {beer, cider}]
      (by decide) (by simp [pure_atoms, NL.and, Finset.image_insert])

open Classical in
include hU hI in
/-- ***Must* with *[a]_F or [b]_F***: in a context `k` whose worlds each have an accessible
world (`hS`), *Taro must drink [a]_F or [b]_F* matches `k` iff
* (a) every alternative is the strongest true one at some world of `k`: `k` leaves every answer
  open; and
* (b) at every world of `k` some alternative is the strongest true one.

The alternatives are indexed as for *can*: *must R* is *Taro must drink x₁ or … or xₙ*.  The
strongest true alternative at `w` is *must R* (`w` is in `cell R`) iff every accessible world makes
Taro drink a member of `R`, and each member `x` of `R` has an accessible world where every
alternative he drinks is part of `x`.  At a world with no accessible world, which `hS` excludes,
every *must* alternative would be vacuously true. -/
theorem NL.mustOr_matches_iff (hS : ∀ w ∈ k, (acc w).Nonempty) :
    (NL.must acc <$> ((⋆pred <$> ·) <$>
      (NL.or <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets))).Matches k ↔
    let cell R := {w | (∀ v ∈ acc w, ∃ x ∈ R, ⋆pred x v = 1) ∧
      ∀ x ∈ R, ∃ v ∈ acc w, ∀ y ∈ A, ⋆pred y v = 1 → y.atoms ⊆ x.atoms}
    (∀ R ∈ finSubsets A, ∃ w ∈ k, w ∈ cell R) ∧ ∀ w ∈ k, ∃ R ∈ finSubsets A, w ∈ cell R :=
  (NL.set_matches_iff pred _ _ (NL.or_finsets_alts pred ha hb) _
    (NL.must_subset_iff acc hU pred hI)
    (fun R => {w | (∀ v ∈ acc w, ∃ x ∈ R, ⋆pred x v = 1) ∧
      ∀ x ∈ R, ∃ v ∈ acc w, ∀ y ∈ A, ⋆pred y v = 1 → y.atoms ⊆ x.atoms})
    fun R hR w hw => NL.must_top_iff acc pred R hR w (hS w hw)).trans live_cover_iff

open Classical Drinks Drinks.Drink in
/-- ***Must* with *[a]_F or [b]_F*, illustrated** (model: `Drinks`).  The alternatives and the
context (`permissionStates s`) are those of *can*.

*Taro must drink [apple juice]_F or [beer]_F* matches the context.  Its 127 indices `R` give
eighteen distinct alternatives, and each `R` selects exactly one possibility, the one whose
antichain `L` is the set of minimal members of `R`.  Six of them are listed;
*must drink apple juice, or apple juice and beer* selects the possibility where apple juice alone
is required, while under *can* it selects that of apple juice and beer. -/
theorem NL.mustOr_illustration (s : Finset Drink) :
    let F := NL.must Drinks.acc <$> ((⋆drank <$> ·) <$>
      (NL.or <$> (Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)).finsets <*>
        (Foc Set.univ (Plural.pure beer) (Set.mem_univ _)).finsets))
    let k : Set DrinkWorld := permissionStates s
    F.Matches k ∧
    (∀ R ∈ finSubsets Set.univ, ∃ w, F.cell k (NL.must Drinks.acc (R.image (⋆drank))) = {w}) ∧
    F.cell k (NL.must Drinks.acc {⋆drank (Plural.pure appleJuice)}) =
      {⟨s, [only {appleJuice}]⟩} ∧
    F.cell k (NL.must Drinks.acc {⋆drank (Plural.pure appleJuice), ⋆drank (Plural.pure beer)}) =
      {⟨s, [only {appleJuice}, only {beer}]⟩} ∧
    F.cell k (NL.must Drinks.acc {⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))}) =
      {⟨s, [only {appleJuice, beer}]⟩} ∧
    F.cell k (NL.must Drinks.acc {⋆drank (Plural.pure appleJuice),
        ⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))}) =
      {⟨s, [only {appleJuice}]⟩} ∧
    F.cell k (NL.must Drinks.acc {⋆drank (Plural.pure appleJuice), ⋆drank (Plural.pure beer),
        ⋆drank (Plural.pure cider)}) =
      {⟨s, [only {appleJuice}, only {beer}, only {cider}]⟩} ∧
    F.cell k (NL.must Drinks.acc {⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer)),
        ⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider)),
        ⋆drank (NL.and (Plural.pure beer) (Plural.pure cider))}) =
      {⟨s, [only {appleJuice, beer}, only {appleJuice, cider}, only {beer, cider}]⟩} := by
  intro F k
  have hS : ∀ w ∈ k, (Drinks.acc w).Nonempty := fun w hw => by
    obtain ⟨L, hL, rfl⟩ := mem_permissionStates.mp hw
    obtain ⟨hne, -⟩ := antichains_nonempty L hL
    cases L with
    | nil => exact absurd rfl hne
    | cons t L' => exact acc_nonempty
  have cell : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ w,
      w ∈ F.cell k (NL.must Drinks.acc (R.image (⋆drank))) ↔
      ∃ L ∈ antichains, w = ⟨s, L.map only⟩ ∧ ((∀ t ∈ L, ∃ x ∈ R.image Plural.atoms, x ⊆ t) ∧
        ∀ x ∈ R.image Plural.atoms, ∃ t ∈ L, t ⊆ x) := fun R hR w => by
    rw [NL.mem_mustOr_cell Drinks.acc unconstrained drank independent _ _ hS hR,
      mem_permissionStates]
    constructor
    · rintro ⟨⟨L, hL, rfl⟩, h⟩
      exact ⟨L, hL, rfl, must_cond_iff.mp h⟩
    · rintro ⟨L, hL, rfl, h⟩
      exact ⟨⟨L, hL, rfl⟩, must_cond_iff.mpr h⟩
  have cell_eq : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ S, R.image (⋆drank) = S →
      ∀ L ∈ antichains, ((∀ t ∈ L, ∃ x ∈ R.image Plural.atoms, x ⊆ t) ∧
        ∀ x ∈ R.image Plural.atoms, ∃ t ∈ L, t ⊆ x) →
      F.cell k (NL.must Drinks.acc S) = {⟨s, L.map only⟩} := by
    rintro R hR S rfl L hL h
    refine eq_singleton_of_unique (cell R hR) (fun L hL L' hL' h h' => must_inj L hL L' hL'
      (fun t ht => ?_) fun t ht => ?_) hL h
    · obtain ⟨x, hx, hxt⟩ := h.1 t ht
      obtain ⟨t', ht', htx⟩ := h'.2 x hx
      exact ⟨t', ht', htx.trans hxt⟩
    · obtain ⟨x, hx, hxt⟩ := h'.1 t ht
      obtain ⟨t', ht', htx⟩ := h.2 x hx
      exact ⟨t', ht', htx.trans hxt⟩
  have live : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∃ L ∈ antichains,
      (∀ t ∈ L, ∃ x ∈ R.image Plural.atoms, x ⊆ t) ∧
        ∀ x ∈ R.image Plural.atoms, ∃ t ∈ L, t ⊆ x := fun R hR =>
    must_live _ (image_atoms_mem hR).1 (image_atoms_mem hR).2.1 (image_atoms_mem hR).2.2
  refine ⟨(NL.mustOr_matches_iff Drinks.acc unconstrained drank independent _ _ hS).mpr
      ⟨fun R hR => ?_, fun w hw => ?_⟩, fun R hR => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, mem_permissionStates.mpr ⟨L, hL, rfl⟩, must_cond_iff.mpr h⟩
  · obtain ⟨L, hL, rfl⟩ := mem_permissionStates.mp hw
    obtain ⟨R, hR, hRL⟩ := exists_index hL
    refine ⟨R, hR, must_cond_iff.mpr ?_⟩
    rw [hRL]
    exact ⟨fun t ht => ⟨t, List.mem_toFinset.mpr ht, subset_rfl⟩,
      fun x hx => ⟨x, List.mem_toFinset.mp hx, subset_rfl⟩⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, cell_eq R hR _ rfl L hL h⟩
  · exact cell_eq {Plural.pure appleJuice} (by simp [finSubsets]) _ (by simp) [{appleJuice}]
      (by decide) (by simp [pure_atoms])
  · exact cell_eq {Plural.pure appleJuice, Plural.pure beer} (by simp [finSubsets]) _ (by simp)
      [{appleJuice}, {beer}] (by decide) (by simp [pure_atoms])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer)} (by simp [finSubsets]) _
      (by simp) [{appleJuice, beer}] (by decide) (by simp [pure_atoms, NL.and])
  · exact cell_eq {Plural.pure appleJuice, NL.and (Plural.pure appleJuice) (Plural.pure beer)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice}] (by decide)
      (by simp [pure_atoms, NL.and, Finset.image_insert])
  · exact cell_eq {Plural.pure appleJuice, Plural.pure beer, Plural.pure cider}
      (by simp [finSubsets]) _ (by simp) [{appleJuice}, {beer}, {cider}] (by decide)
      (by simp [pure_atoms])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer),
        NL.and (Plural.pure appleJuice) (Plural.pure cider),
        NL.and (Plural.pure beer) (Plural.pure cider)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice, beer}, {appleJuice, cider}, {beer, cider}]
      (by decide) (by simp [pure_atoms, NL.and, Finset.image_insert])

end

/-! ## *Both* under a negated modal

*Taro can't drink both [a]_F and [b]_F* and *Taro doesn't have to drink both [a]_F and [b]_F*.
As with *or*, each conjunct is lifted inside focus (`Focus.finsets`); *and* sums the lifted sets
memberwise (`Finset.image₂ NL.and`), and *both* applies to each sum.  The alternative indexed by
`S` and `T` is the negated modal applied to the set of *Taro drinks both of `x ⊕ y`*, for
`x ∈ S` and `y ∈ T`.  *Can't* says of this set that each member is prohibited, and
*doesn't have to*, that some accessible world leaves part of each member undrunk.

Without modals, *Taro didn't drink both [a]_F and [b]_F* matches no context
(`NL.notBoth_fails`), because *not both x ⊕ y* is the union of *not both x* and *not both y*.
Since `◇` distributes over `∨`, *doesn't have to* keeps this union and fails in the same way;
`□` does not distribute over `∨`, so *can't* matches.  Accessibility is unconstrained and the
atoms are independent. -/

section
variable (acc : World → Finset World) (hU : Unconstrained acc) (pred : Individual → FuzzyP)
  (hI : Independent pred) {A : Set (Plural Individual)} {a b : Plural Individual} (ha : a ∈ A)
  (hb : b ∈ A) {k : Set World} [DecidableEq Individual]

open Classical in
include hU hI in
/-- ***Can't* with *both [a]_F and [b]_F***: when the alternatives are closed under sums,
*Taro can't drink both [a]_F and [b]_F* matches `k` iff
* (a) every alternative is the strongest true one at some world of `k`: `k` leaves every answer
  open; and
* (b) at every world of `k` some alternative is the strongest true one.

With `A` closed under sums, the alternatives are indexed by the nonempty finite sets `R` of members
of `A`: *can't R* is *Taro can't drink both of x₁, and … and can't drink both of xₙ*, each member
prohibited in full.  The strongest true alternative at `w` is *can't R* (`w` is in `cell R`) iff
the alternatives Taro is not allowed to drink in full there are exactly those that include a
member of `R`. -/
theorem NL.notCanBoth_matches_iff (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A) :
    (NL.not <$> (NL.can acc <$> ((NL.both pred <$> ·) <$>
      (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))).Matches k ↔
    let cell R := {w | ∀ y ∈ A,
      (∀ v ∈ acc w, ∃ m ∈ y.atoms, pred m v = 0) ↔ ∃ x ∈ R, x.atoms ⊆ y.atoms}
    (∀ R ∈ finSubsets A, ∃ w ∈ k, w ∈ cell R) ∧ ∀ w ∈ k, ∃ R ∈ finSubsets A, w ∈ cell R := by
  unfold Focus.Matches
  rw [Functor.map_map, NL.assert_bothSums_alts ha hb _ hA NL.notCanBoth_sums]
  exact (matches_image_iff _ (fun R => {w | ∀ y ∈ A,
      (∀ v ∈ acc w, ∃ m ∈ y.atoms, pred m v = 0) ↔ ∃ x ∈ R, x.atoms ⊆ y.atoms})
    (NL.notCanBoth_subset_iff hU hI) fun R hR w _ => NL.notCanBoth_top_iff R hR w).trans
    live_cover_iff

open Classical Drinks Drinks.Drink in
/-- ***Can't* with *both [a]_F and [b]_F*, illustrated** (model: `Drinks`).  The alternatives are
all the pluralities of drinks (`Set.univ`), the three drinks closed under sums, as
`NL.notCanBoth_matches_iff` assumes.  The context, `prohibitionStates s`, has eighteen
possibilities, one for each antichain `L` of sets of drinks: from it, the accessible worlds are
those where Taro drank a set of drinks that includes no member of `L`, so the members of `L` are
the minimal combinations he may not drink in full.  What Taro actually drank there is left open
(`s`).

*Taro can't drink both [apple juice]_F and [beer]_F* matches the context.  Its 127 indices `R`
give eighteen distinct alternatives, and each `R` selects exactly one possibility, the one whose
antichain `L` is the set of minimal members of `R`.  Six of them are listed;
*can't drink apple juice, and can't drink both beer and cider* selects the possibility whose
minimal prohibitions are these two. -/
theorem NL.notCanBoth_illustration (s : Finset Drink) :
    let F := NL.not <$> (NL.can Drinks.acc <$> ((NL.both drank <$> ·) <$>
      (Finset.image₂ NL.and <$>
        (Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)).finsets <*>
        (Foc Set.univ (Plural.pure beer) (Set.mem_univ _)).finsets)))
    let k : Set DrinkWorld := prohibitionStates s
    F.Matches k ∧
    (∀ R ∈ finSubsets Set.univ,
      ∃ w, F.cell k (NL.not (NL.can Drinks.acc (R.image (NL.both drank)))) = {w}) ∧
    F.cell k (NL.not (NL.can Drinks.acc {NL.both drank (Plural.pure appleJuice)})) =
      {prohibitionState s [{appleJuice}]} ∧
    F.cell k (NL.not (NL.can Drinks.acc
        {NL.both drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))})) =
      {prohibitionState s [{appleJuice, beer}]} ∧
    F.cell k (NL.not (NL.can Drinks.acc
        {NL.both drank (Plural.pure appleJuice), NL.both drank (Plural.pure beer)})) =
      {prohibitionState s [{appleJuice}, {beer}]} ∧
    F.cell k (NL.not (NL.can Drinks.acc {NL.both drank (Plural.pure appleJuice),
        NL.both drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))})) =
      {prohibitionState s [{appleJuice}]} ∧
    F.cell k (NL.not (NL.can Drinks.acc {NL.both drank (Plural.pure appleJuice),
        NL.both drank (NL.and (Plural.pure beer) (Plural.pure cider))})) =
      {prohibitionState s [{appleJuice}, {beer, cider}]} ∧
    F.cell k (NL.not (NL.can Drinks.acc
        {NL.both drank (NL.and (Plural.pure appleJuice) (Plural.pure beer)),
          NL.both drank (NL.and (Plural.pure appleJuice) (Plural.pure cider)),
          NL.both drank (NL.and (Plural.pure beer) (Plural.pure cider))})) =
      {prohibitionState s [{appleJuice, beer}, {appleJuice, cider}, {beer, cider}]} := by
  intro F k
  have hA : ∀ x ∈ (Set.univ : Set (Plural Drink)), ∀ y ∈ Set.univ, NL.and x y ∈ Set.univ :=
    fun _ _ _ _ => Set.mem_univ _
  have cell : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ w,
      w ∈ F.cell k (NL.not (NL.can Drinks.acc (R.image (NL.both drank)))) ↔
      ∃ L ∈ antichains, w = prohibitionState s L ∧ ∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, t ⊆ y) ↔ ∃ x ∈ R.image Plural.atoms, x ⊆ y) := fun R hR w => by
    rw [NL.mem_notCanBoth_cell unconstrained independent _ _ hA hR, mem_prohibitionStates]
    constructor
    · rintro ⟨⟨L, hL, rfl⟩, h⟩
      exact ⟨L, hL, rfl, cant_cond_iff.mp h⟩
    · rintro ⟨L, hL, rfl, h⟩
      exact ⟨⟨L, hL, rfl⟩, cant_cond_iff.mpr h⟩
  have cell_eq : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∀ S,
      R.image (NL.both drank) = S → ∀ L ∈ antichains,
      (∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, t ⊆ y) ↔ ∃ x ∈ R.image Plural.atoms, x ⊆ y)) →
      F.cell k (NL.not (NL.can Drinks.acc S)) = {prohibitionState s L} := by
    rintro R hR S rfl L hL h
    exact eq_singleton_of_unique (cell R hR) (fun L hL L' hL' h h' =>
      cant_inj L hL L' hL' fun y hy hyn => (h y hy hyn).trans (h' y hy hyn).symm) hL h
  have live : ∀ R ∈ finSubsets (Set.univ : Set (Plural Drink)), ∃ L ∈ antichains,
      ∀ y ∈ threeDrinks.powerset, y.Nonempty →
        ((∃ t ∈ L, t ⊆ y) ↔ ∃ x ∈ R.image Plural.atoms, x ⊆ y) := fun R hR =>
    cant_live _ (image_atoms_mem hR).1 (image_atoms_mem hR).2.1 (image_atoms_mem hR).2.2
  refine ⟨(NL.notCanBoth_matches_iff Drinks.acc unconstrained drank independent _ _ hA).mpr
      ⟨fun R hR => ?_, fun w hw => ?_⟩, fun R hR => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, mem_prohibitionStates.mpr ⟨L, hL, rfl⟩, cant_cond_iff.mpr h⟩
  · obtain ⟨L, hL, rfl⟩ := mem_prohibitionStates.mp hw
    obtain ⟨R, hR, hRL⟩ := exists_index hL
    exact ⟨R, hR, cant_cond_iff.mpr fun y _ _ => by rw [hRL]; simp⟩
  · obtain ⟨L, hL, h⟩ := live R hR
    exact ⟨_, cell_eq R hR _ rfl L hL h⟩
  · exact cell_eq {Plural.pure appleJuice} (by simp [finSubsets]) _ (by simp) [{appleJuice}]
      (by decide) (by simp [pure_atoms])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer)} (by simp [finSubsets]) _
      (by simp) [{appleJuice, beer}] (by decide) (by simp [pure_atoms, NL.and])
  · exact cell_eq {Plural.pure appleJuice, Plural.pure beer} (by simp [finSubsets]) _ (by simp)
      [{appleJuice}, {beer}] (by decide) (by simp [pure_atoms])
  · exact cell_eq {Plural.pure appleJuice, NL.and (Plural.pure appleJuice) (Plural.pure beer)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice}] (by decide)
      (by
        simp only [Finset.mem_powerset, List.mem_cons, List.not_mem_nil, or_false,
          exists_eq_left, Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, ↓existsAndEq, true_and]
        decide)
  · exact cell_eq {Plural.pure appleJuice, NL.and (Plural.pure beer) (Plural.pure cider)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice}, {beer, cider}] (by decide)
      (by simp [pure_atoms, NL.and, Finset.image_insert])
  · exact cell_eq {NL.and (Plural.pure appleJuice) (Plural.pure beer),
        NL.and (Plural.pure appleJuice) (Plural.pure cider),
        NL.and (Plural.pure beer) (Plural.pure cider)}
      (by simp [finSubsets]) _ (by simp) [{appleJuice, beer}, {appleJuice, cider}, {beer, cider}]
      (by decide) (by simp [pure_atoms, NL.and, Finset.image_insert])

open Classical in
include hU hI in
/-- ***Doesn't have to* with *both [a]_F and [b]_F* fails**:
*Taro doesn't have to drink both [a]_F and [b]_F* matches no context whenever `A` has two
alternatives `x`, `y`, neither part of the other.  Condition (a) fails, as for unembedded
*not both*: the alternatives include those for `{x}`, `{y}` and `{x ⊕ y}`, and
*Taro doesn't have to drink both of `x ⊕ y`* is the union of the other two, so it is the strongest
true alternative nowhere.  In the three-drink model, with the context of *can* and *must* with
*or*, *Taro doesn't have to drink both apple juice and beer* is true in sixteen of the eighteen
possibilities, and in each *Taro doesn't have to drink apple juice* or
*Taro doesn't have to drink beer* is true too, and stronger. -/
theorem NL.notMustBoth_fails {x y : Plural Individual} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : ¬ x.atoms ⊆ y.atoms) (hyx : ¬ y.atoms ⊆ x.atoms) : ∀ k,
    ¬ (NL.not <$> (NL.must acc <$> ((NL.both pred <$> ·) <$>
      (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))).Matches k := by
  intro k
  have mem : ∀ {u v}, u ∈ A → v ∈ A →
      Assert (NL.not (NL.must acc {NL.both pred (NL.and u v)})) ∈
        (Assert ·) '' (NL.not <$> (NL.must acc <$> ((NL.both pred <$> ·) <$>
          (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))).alts :=
    fun hu hv => ⟨_, by rw [Functor.map_map]; exact NL.bothSums_mem_alts ha hb _ hu hv, rfl⟩
  have single : ∀ {u}, u ∈ A → Assert (NL.not (NL.must acc {NL.both pred u})) ∈
      (Assert ·) '' (NL.not <$> (NL.must acc <$> ((NL.both pred <$> ·) <$>
        (Finset.image₂ NL.and <$> (Foc A a ha).finsets <*> (Foc A b hb).finsets)))).alts :=
    fun {u} hu => NL.and_self u ▸ mem hu hu
  exact not_matches_of_union (single hx) (single hy) (NL.assert_notMustBoth_and x y ▸ mem hx hy)
    (NL.notMustBoth_not_subset hU hI hyx) (NL.notMustBoth_not_subset hU hI hxy)

end

end Composition
