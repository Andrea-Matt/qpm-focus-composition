import Composition.Lemmas.Lexicon
import Composition.Lemmas.Drinks

/-!
# Predictions without modals

Focus without coordination, conjunction, negation, negated conjunction, the failure of negated
*both*, and disjunction, over pluralities.  Each case is stated by the exact contexts it matches
(`_matches_iff`, for any model meeting the hypotheses, or `_fails` when there are none).  Each case
that matches is then illustrated in the model with three drinks (`Drinks`): a context, the fact
that the sentence matches it, and the cell each alternative selects.  Readable.
-/

namespace Composition

variable {World Individual : Type}

/-! In every section `pred` is a predicate of atoms, `⋆pred` its plural (`⋆pred x` is
*Taro drank x*), and `A` the pluralities the context supplies as alternatives; `y` is part of `x`
when the atoms of `y` are among those of `x`.  The atoms are independent (`hI`).  Each section
declares the variables of its general theorems; a hypothesis used only inside a proof (`hI`, `hA`)
is added to a theorem by `include … in` above it.  The illustrations use none of the variables.
The first illustration has the three single drinks as alternatives (`atomicDrinks`); all the others
have all the pluralities of drinks (`Set.univ`), that is, the three drinks closed under sums. -/

/-! ## Focus without coordination -/

section
variable (pred : Individual → FuzzyP) (hI : Independent pred) {A : Set (Plural Individual)}
  {a : Plural Individual} (ha : a ∈ A) {k : Set World}

include hI in
/-- **Focus without coordination**: *Taro drank [a]_F* matches `k` iff
* (a) every alternative is the strongest true one at some world of `k`: `k` leaves every answer
  open; and
* (b) at every world of `k` some alternative is the strongest true one.

The strongest true alternative at `w` is `x` (`w` is in `cell x`) iff Taro drank `x` there and
every alternative he drank there is part of `x`.  If the alternatives are single atoms, (b) says
that Taro drank exactly one of them (*which drink did Taro drink?*); if they are finitely many and
closed under sums, that he drank one of them (*what did Taro drink?*).  The alternatives are
pluralities (a single atom is a plurality of one), so that conjunction can reduce to this case
(below). -/
theorem NL.focus_matches_iff : (⋆pred <$> Foc A a ha).Matches k ↔
    let cell x := {w | ⋆pred x w = 1 ∧ ∀ y ∈ A, ⋆pred y w = 1 → y.atoms ⊆ x.atoms}
    (∀ x ∈ A, ∃ w ∈ k, w ∈ cell x) ∧ ∀ w ∈ k, ∃ x ∈ A, w ∈ cell x :=
  (matches_image_iff (fun y x => y.atoms ⊆ x.atoms)
    (fun x => {w | ⋆pred x w = 1 ∧ ∀ y ∈ A, ⋆pred y w = 1 → y.atoms ⊆ x.atoms})
    (fun x _ y _ => hI.star_subset_iff x y) fun _ _ _ _ => Iff.rfl).trans live_cover_iff

open Drinks Drinks.Drink in
/-- **Focus without coordination, illustrated with single drinks** (model: `Drinks`).  The
alternatives are the three drinks, each a plurality of one atom, and the context has three
possibilities: Taro drank apple juice only, beer only, cider only.

*Taro drank [beer]_F* matches the context, and each alternative selects the possibility where Taro
drank that drink.  A possibility where he drank two of them would lie in no cell: no single drink
is the strongest true alternative there. -/
theorem NL.focus_illustration :
    let F := ⋆drank <$> Foc atomicDrinks (Plural.pure beer) (by simp [atomicDrinks])
    let k : Set DrinkWorld := {only {appleJuice}, only {beer}, only {cider}}
    F.Matches k ∧
    F.cell k (⋆drank (Plural.pure appleJuice)) = {only {appleJuice}} ∧
    F.cell k (⋆drank (Plural.pure beer)) = {only {beer}} ∧
    F.cell k (⋆drank (Plural.pure cider)) = {only {cider}} := by
  intro F k
  refine ⟨(NL.focus_matches_iff drank independent _).mpr ?_, ?_, ?_, ?_⟩
  · simp [k, atomicDrinks, star_only, pure_atoms]
  all_goals
    ext w
    refine (NL.mem_focus_cell independent _ (by simp [atomicDrinks])).trans ?_
    constructor
    · rintro ⟨hk, h1, -⟩
      simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl <;> simp_all [star_only, pure_atoms]
    · rintro rfl
      simp [k, atomicDrinks, star_only, pure_atoms]

end

/-! ## Conjunction -/

section
variable (pred : Individual → FuzzyP) {A : Set (Plural Individual)} {a b : Plural Individual}
  (ha : a ∈ A) (hb : b ∈ A) {k : Set World} [DecidableEq Individual]
  (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A)

include hA in
/-- **Conjunction**: when the alternatives are closed under sums, *Taro drank [a]_F and [b]_F*
matches exactly the contexts that *Taro drank [a]_F* and *Taro drank [b]_F* each match: all three
have the alternatives `A`.  So (a) and (b) are those of focus without coordination
(`NL.focus_matches_iff`), with the same cells. -/
theorem NL.and_matches_iff : (⋆pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb)).Matches k ↔
    (⋆pred <$> Foc A a ha).Matches k := by
  change Matches k ((Assert ·) '' (⋆pred '' (NL.and <$> Foc A a ha <*> Foc A b hb).alts)) ↔ _
  rw [NL.and_alts ha hb hA]
  rfl

open Drinks Drinks.Drink in
/-- **Conjunction, illustrated** (model: `Drinks`).  The alternatives are all the pluralities of
drinks (`Set.univ`), the three drinks closed under sums, as `NL.and_matches_iff` assumes.  The
context, `drankSomething`, has seven possibilities, one for each nonempty set of drinks Taro drank.

*Taro drank [apple juice]_F and [beer]_F* matches the context, and each alternative
*Taro drank x* selects the possibility where Taro drank exactly the drinks of `x`. -/
theorem NL.and_illustration :
    let F := ⋆drank <$> (NL.and <$> Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _) <*>
      Foc Set.univ (Plural.pure beer) (Set.mem_univ _))
    let k : Set DrinkWorld := drankSomething
    F.Matches k ∧
    F.cell k (⋆drank (Plural.pure appleJuice)) = {only {appleJuice}} ∧
    F.cell k (⋆drank (Plural.pure beer)) = {only {beer}} ∧
    F.cell k (⋆drank (Plural.pure cider)) = {only {cider}} ∧
    F.cell k (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))) =
      {only {appleJuice, beer}} ∧
    F.cell k (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider))) =
      {only {appleJuice, cider}} ∧
    F.cell k (⋆drank (NL.and (Plural.pure beer) (Plural.pure cider))) = {only {beer, cider}} ∧
    F.cell k (⋆drank (NL.and (NL.and (Plural.pure appleJuice) (Plural.pure beer))
      (Plural.pure cider))) =
      {only {appleJuice, beer, cider}} := by
  intro F k
  have hF : ∀ r, F.cell k r =
      (⋆drank <$> Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)).cell k r :=
    Focus.cell_congr (congrArg (⋆drank '' ·) (NL.and_alts _ _ fun _ _ _ _ => Set.mem_univ _)) k
  refine ⟨(NL.and_matches_iff drank _ _ fun _ _ _ _ => Set.mem_univ _).mpr
    ((NL.focus_matches_iff drank independent _).mpr ⟨?_, ?_⟩), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine forall_plural fun s hs x hx => ?_
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [k, drankSomething, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right,
        exists_or, exists_eq_left, Set.mem_ofPred_eq, star_only, forall_univ_plural_subset,
        hx] <;> decide
  · intro w hw
    simp only [k, drankSomething, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact greatest_only (by simp)
  all_goals
    rw [hF]
    ext w
    refine (NL.mem_focus_cell independent _ (Set.mem_univ _)).trans ?_
    constructor
    · rintro ⟨hk, h1, h2⟩
      simp only [k, drankSomething, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Set.mem_singleton _
        | (simp only [star_only, forall_univ_plural_subset] at h1 h2
           simp +decide at h1 h2)
    · rintro rfl
      simp only [star_only, forall_univ_plural_subset]
      simp +decide [k, drankSomething]

end

/-! ## Negation -/

section
variable (pred : Individual → FuzzyP) (hI : Independent pred) {A : Set (Plural Individual)}
  {a : Plural Individual} (ha : a ∈ A) {k : Set World}

include hI in
/-- **Negation**: *Taro didn't drink [a]_F* (*which didn't he drink?*) matches `k` iff
* (a) every alternative is the strongest true one at some world of `k`: `k` leaves every answer
  open; and
* (b) at every world of `k` some alternative is the strongest true one.

The strongest true alternative at `w` is *Taro didn't drink `x`* (`w` is in `cell x`) iff Taro
drank none of `x` there (by homogeneity, `⋆pred x` is fully false) and every alternative he drank
none of there is part of `x`. -/
theorem NL.notFocus_matches_iff : (NL.not <$> (⋆pred <$> Foc A a ha)).Matches k ↔
    let cell x := {w | ⋆pred x w = 0 ∧ ∀ y ∈ A, ⋆pred y w = 0 → y.atoms ⊆ x.atoms}
    (∀ x ∈ A, ∃ w ∈ k, w ∈ cell x) ∧ ∀ w ∈ k, ∃ x ∈ A, w ∈ cell x := by
  change Matches k ((Assert ·) '' (NL.not '' (⋆pred '' A))) ↔ _
  rw [Set.image_image NL.not (⋆pred) A]
  exact (matches_image_iff (fun y x => y.atoms ⊆ x.atoms)
    (fun x => {w | ⋆pred x w = 0 ∧ ∀ y ∈ A, ⋆pred y w = 0 → y.atoms ⊆ x.atoms})
    (fun x _ y _ => hI.not_star_subset_iff x y)
    fun _ _ _ _ => by simp only [NL.not_eq_one, Set.mem_ofPred_eq]).trans live_cover_iff

open Drinks Drinks.Drink in
/-- **Negation, illustrated** (model: `Drinks`).  The alternatives are all the pluralities of
drinks (`Set.univ`).  The context, `leftSomethingOut`, has seven possibilities, one for each set of
drinks Taro drank that leaves some drink out.

*Taro didn't drink [beer]_F* matches the context, and each alternative *Taro didn't drink x*
selects the possibility where Taro drank exactly the drinks outside `x`. -/
theorem NL.notFocus_illustration :
    let F := NL.not <$> (⋆drank <$> Foc Set.univ (Plural.pure beer) (Set.mem_univ _))
    let k : Set DrinkWorld := leftSomethingOut
    F.Matches k ∧
    F.cell k (NL.not (⋆drank (Plural.pure appleJuice))) = {only {beer, cider}} ∧
    F.cell k (NL.not (⋆drank (Plural.pure beer))) = {only {appleJuice, cider}} ∧
    F.cell k (NL.not (⋆drank (Plural.pure cider))) = {only {appleJuice, beer}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer)))) =
      {only {cider}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider)))) =
      {only {beer}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure beer) (Plural.pure cider)))) =
      {only {appleJuice}} ∧
    F.cell k (NL.not (⋆drank
      (NL.and (NL.and (Plural.pure appleJuice) (Plural.pure beer)) (Plural.pure cider)))) =
      {only ∅} := by
  intro F k
  refine ⟨(NL.notFocus_matches_iff drank independent _).mpr ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine forall_plural fun s hs x hx => ?_
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [k, leftSomethingOut, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right,
        exists_or, exists_eq_left, Set.mem_ofPred_eq, star_only_eq_zero,
        forall_univ_plural_subset, hx] <;>
        decide
  · intro w hw
    simp only [k, leftSomethingOut, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact greatest_only_eq_zero (by decide)
  all_goals
    ext w
    refine (NL.mem_notFocus_cell independent _ (Set.mem_univ _)).trans ?_
    constructor
    · rintro ⟨hk, h1, h2⟩
      simp only [k, leftSomethingOut, Set.mem_insert_iff, Set.mem_singleton_iff] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact Set.mem_singleton _
        | (simp only [star_only_eq_zero, forall_univ_plural_subset] at h1 h2
           simp +decide at h1 h2)
    · rintro rfl
      simp only [star_only_eq_zero, forall_univ_plural_subset]
      simp +decide [k, leftSomethingOut]

end

/-! ## Negated homogeneous conjunction -/

section
variable (pred : Individual → FuzzyP) {A : Set (Plural Individual)} {a b : Plural Individual}
  (ha : a ∈ A) (hb : b ∈ A) {k : Set World} [DecidableEq Individual]
  (hA : ∀ x ∈ A, ∀ y ∈ A, NL.and x y ∈ A)

include hA in
/-- **Negated homogeneous conjunction**: when the alternatives are closed under sums,
*Taro didn't drink [a]_F and [b]_F* matches exactly the contexts that *Taro didn't drink [a]_F*
and *Taro didn't drink [b]_F* each match.  So (a) and (b) are those of negation
(`NL.notFocus_matches_iff`), with the same cells.  By homogeneity it means *neither*. -/
theorem NL.notAnd_matches_iff :
    (NL.not <$> (⋆pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb))).Matches k ↔
    (NL.not <$> (⋆pred <$> Foc A a ha)).Matches k := by
  change Matches k
    ((Assert ·) '' (NL.not '' (⋆pred '' (NL.and <$> Foc A a ha <*> Foc A b hb).alts))) ↔ _
  rw [NL.and_alts ha hb hA]
  rfl

open Drinks Drinks.Drink in
/-- **Negated homogeneous conjunction, illustrated** (model: `Drinks`).  The alternatives and the
context (`leftSomethingOut`) are those of negation.

*Taro didn't drink [apple juice]_F and [beer]_F* matches the context, with the cells of negation:
each alternative *Taro didn't drink x* selects the possibility where Taro drank exactly the drinks
outside `x`.  Contrast *Taro didn't drink both [apple juice]_F and [beer]_F*, below. -/
theorem NL.notAnd_illustration :
    let F := NL.not <$> (⋆drank <$>
      (NL.and <$> Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _) <*>
        Foc Set.univ (Plural.pure beer) (Set.mem_univ _)))
    let k : Set DrinkWorld := leftSomethingOut
    F.Matches k ∧
    F.cell k (NL.not (⋆drank (Plural.pure appleJuice))) = {only {beer, cider}} ∧
    F.cell k (NL.not (⋆drank (Plural.pure beer))) = {only {appleJuice, cider}} ∧
    F.cell k (NL.not (⋆drank (Plural.pure cider))) = {only {appleJuice, beer}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer)))) =
      {only {cider}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider)))) =
      {only {beer}} ∧
    F.cell k (NL.not (⋆drank (NL.and (Plural.pure beer) (Plural.pure cider)))) =
      {only {appleJuice}} ∧
    F.cell k (NL.not (⋆drank
      (NL.and (NL.and (Plural.pure appleJuice) (Plural.pure beer)) (Plural.pure cider)))) =
      {only ∅} := by
  intro F k
  have hF : ∀ r, F.cell k r =
      (NL.not <$> (⋆drank <$> Foc Set.univ (Plural.pure beer) (Set.mem_univ _))).cell k r :=
    Focus.cell_congr (congrArg (fun A => NL.not '' (⋆drank '' A))
      (NL.and_alts _ _ fun _ _ _ _ => Set.mem_univ _)) k
  obtain ⟨hm, h1, h2, h3, h4, h5, h6, h7⟩ := NL.notFocus_illustration
  exact ⟨(NL.notAnd_matches_iff drank _ _ fun _ _ _ _ => Set.mem_univ _).mpr hm,
    (hF _).trans h1, (hF _).trans h2, (hF _).trans h3, (hF _).trans h4, (hF _).trans h5,
    (hF _).trans h6, (hF _).trans h7⟩

end

/-! ## Negated *both* -/

section
variable (pred : Individual → FuzzyP) (hI : Independent pred) {A : Set (Plural Individual)}
  {a b : Plural Individual} (ha : a ∈ A) (hb : b ∈ A) [DecidableEq Individual]

include hI in
/-- **Negated *both* fails**: *Taro didn't drink both [a]_F and [b]_F* matches no context whenever
`A` has two alternatives `x`, `y`, neither part of the other.  Condition (a) fails:
*not both x ⊕ y* is the union of *not both x* and *not both y*, so it is the strongest true
alternative nowhere.  In the three-drink model, with the context of negation, *Taro didn't drink
both apple juice and beer* is true in six of the seven possibilities, and in each
*Taro didn't drink apple juice* or *Taro didn't drink beer* is true too, and stronger.  The
predicate is `pred`, not `⋆pred`: *both* distributes it over the atoms itself (`NL.both`). -/
theorem NL.notBoth_fails {x y : Plural Individual} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : ¬ x.atoms ⊆ y.atoms) (hyx : ¬ y.atoms ⊆ x.atoms) : ∀ k,
    ¬ (NL.not <$> (NL.both pred <$> (NL.and <$> Foc A a ha <*> Foc A b hb))).Matches k := by
  intro k h
  obtain ⟨w, -, hw⟩ := (matches_iff.mp h).1 _
    ⟨_, ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  rw [NL.exh_notBoth_eq_empty hI ha hb hx hy hxy hyx] at hw
  exact hw

end

/-! ## Disjunction -/

section
variable (pred : Individual → FuzzyP) {A : Set (Plural Individual)} {a b : Plural Individual}
  (ha : a ∈ A) (hb : b ∈ A) {k : Set World}

open Classical in
/-- **Disjunction, member by member**: unembedded, the disjuncts of *Taro drank [a]_F or [b]_F*
enter as singletons outside focus, and the predicate applies to each member; both members match
`k` iff *Taro drank [a]_F* does.  So (a) and (b) are those of focus without coordination
(`NL.focus_matches_iff`), for each member. -/
theorem NL.or_matches_iff :
    (∀ F ∈ (⋆pred <$> ·) <$> NL.or {Foc A a ha} {Foc A b hb}, F.Matches k) ↔
    (⋆pred <$> Foc A a ha).Matches k := by
  simp only [Finset.fmap_def, Finset.forall_mem_image]
  exact NL.forall_mem_or.trans (and_self_iff (a := (⋆pred <$> Foc A a ha).Matches k))

open Classical Drinks Drinks.Drink in
/-- **Disjunction, member by member, illustrated** (model: `Drinks`).  The alternatives and the
context (`drankSomething`) are those of conjunction.

Both members, *Taro drank [apple juice]_F* and *Taro drank [beer]_F*, match the context, each with
the cells of focus without coordination: each alternative *Taro drank x* selects the possibility
where Taro drank exactly the drinks of `x`. -/
theorem NL.or_illustration :
    let S := (⋆drank <$> ·) <$> NL.or {Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)}
      {Foc Set.univ (Plural.pure beer) (Set.mem_univ _)}
    let k : Set DrinkWorld := drankSomething
    ∀ F ∈ S, F.Matches k ∧
      F.cell k (⋆drank (Plural.pure appleJuice)) = {only {appleJuice}} ∧
      F.cell k (⋆drank (Plural.pure beer)) = {only {beer}} ∧
      F.cell k (⋆drank (Plural.pure cider)) = {only {cider}} ∧
      F.cell k (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure beer))) =
        {only {appleJuice, beer}} ∧
      F.cell k (⋆drank (NL.and (Plural.pure appleJuice) (Plural.pure cider))) =
        {only {appleJuice, cider}} ∧
      F.cell k (⋆drank (NL.and (Plural.pure beer) (Plural.pure cider))) = {only {beer, cider}} ∧
      F.cell k (⋆drank (NL.and (NL.and (Plural.pure appleJuice) (Plural.pure beer))
        (Plural.pure cider))) =
        {only {appleJuice, beer, cider}} := by
  intro S k
  obtain ⟨hm, h1, h2, h3, h4, h5, h6, h7⟩ := NL.and_illustration
  have hF : ∀ {c : Plural Drink} (hc : c ∈ Set.univ) r,
      (⋆drank <$> Foc Set.univ c hc).cell k r =
      (⋆drank <$> (NL.and <$> Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _) <*>
        Foc Set.univ (Plural.pure beer) (Set.mem_univ _))).cell k r := fun _ =>
    Focus.cell_congr
      (congrArg (⋆drank '' ·) (NL.and_alts _ _ fun _ _ _ _ => Set.mem_univ _)).symm k
  have hm' : (⋆drank <$> Foc Set.univ (Plural.pure appleJuice) (Set.mem_univ _)).Matches k :=
    (NL.and_matches_iff drank _ _ fun _ _ _ _ => Set.mem_univ _).mp hm
  simp only [S, Finset.fmap_def, Finset.forall_mem_image]
  refine NL.forall_mem_or.mpr ⟨?_, ?_⟩ <;>
    exact ⟨hm', (hF _ _).trans h1, (hF _ _).trans h2, (hF _ _).trans h3, (hF _ _).trans h4,
      (hF _ _).trans h5, (hF _ _).trans h6, (hF _ _).trans h7⟩

end

end Composition
