import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Interval.Set.Instances

/-!
# The formal apparatus

Truth values, fuzzy logic (`Fz.`), the modal operators, and assertion, which turns a fuzzy
proposition into a set of worlds for the question semantics (`Questions.lean`).  Readable.
-/

namespace Composition

variable {World : Type}

/-! ## Truth values -/

/-- Truth values: the rationals in `[0, 1]`. -/
abbrev Truth := Set.Icc (0 : ℚ) 1

set_option hygiene false in
/-- Fuzzy propositions: functions from worlds to truth values. -/
notation "FuzzyP" => World → Truth

/-- Negation of a truth value: `1 - t`. -/
def Truth.not (t : Truth) : Truth := ⟨1 - t, Set.Icc.one_sub_mem t.2⟩

/-- The average of `f` over `s` (`0` if `s` is empty). -/
def avg {α : Type} (s : Finset α) (f : α → Truth) : Truth :=
  ⟨(∑ x ∈ s, f x : ℚ) / s.card, by
    have sum_le : ∑ x ∈ s, (f x : ℚ) ≤ s.card := by
      simpa only [nsmul_one] using Finset.sum_le_card_nsmul s _ 1 fun x _ => (f x).2.2
    exact ⟨div_nonneg (Finset.sum_nonneg fun x _ => (f x).2.1) s.card.cast_nonneg,
      div_le_one_of_le₀ sum_le s.card.cast_nonneg⟩⟩

/-! ## Fuzzy logic -/

/-- Negation flips truth values; classical disjunction is the maximum. -/
def Fz.not (r : FuzzyP) : FuzzyP := fun w => Truth.not (r w)
@[inherit_doc Fz.not]
def Fz.or (r s : FuzzyP) : FuzzyP := fun w => max (r w) (s w)

/-- The disjunction (maximum) of a finite set of propositions, `0` for the empty set.  It sends
`{r}` to `r` and unions to `Fz.or`. -/
def bigOr (R : Finset FuzzyP) : FuzzyP := fun w => R.fold max 0 (· w)

/-! ## Modal operators

Accessibility is finite, `acc : World → Finset World`, so maxima and minima over accessible
worlds exist among truth values. -/

/-- Fuzzy possibility and necessity: the best and the worst value at an accessible world (`0` and
`1` if none is accessible). -/
def Fz.diamond (acc : World → Finset World) (r : FuzzyP) : FuzzyP := fun w => (acc w).fold max 0 r
@[inherit_doc Fz.diamond]
def Fz.box (acc : World → Finset World) (r : FuzzyP) : FuzzyP := fun w => (acc w).fold min 1 r

/-- Accessibility is unconstrained: every nonempty finite set of worlds is the set of worlds
accessible from some world, so the model rules out no modal base. -/
def Unconstrained (acc : World → Finset World) : Prop :=
  ∀ V : Finset World, V.Nonempty → ∃ w, acc w = V

/-! ## Assertion

Matching works on sets of worlds; `Assert` turns a fuzzy proposition into a set of worlds: the
worlds where its value is 1. `w ∈ Assert r` is `r w = 1`. -/

/-- What `r` asserts: the worlds where it is fully true.  Matching sees only these. -/
def Assert (r : FuzzyP) : Set World := {w | r w = 1}

end Composition
