import Composition.Ontology

/-!
# A model with three drinks

The model of the illustrations: Taro, three drinks, and worlds that say what Taro drank and which
worlds are accessible from them; the contexts used by more than one illustration.  It meets the
hypotheses of the general results (`independent`, `unconstrained`).  Readable.
-/

namespace Composition.Drinks

/-- The three drinks. -/
inductive Drink | appleJuice | beer | cider
deriving DecidableEq

open Drink

/-- The worlds of the model: the type that instantiates the variable `World` of the general
results.  At `⟨s, V⟩`, Taro drank the drinks in `s` and nothing else, and the worlds accessible
from it are those in the list `V`. -/
inductive DrinkWorld where
  | mk (drinks : Finset Drink) (accessible : List DrinkWorld)

/-- `only s`: Taro drank the drinks in `s` and nothing else, and no world is accessible.  The
possibilities of the illustrations without modals, and the worlds accessible from the permission
states of the modal ones. -/
def only (s : Finset Drink) : DrinkWorld := ⟨s, []⟩

open Classical in
/-- Accessibility: from `⟨s, V⟩`, the worlds in `V`. -/
noncomputable def acc : DrinkWorld → Finset DrinkWorld
  | ⟨_, V⟩ => V.toFinset

/-- *Taro drank `d`*: fully true at `⟨s, V⟩` iff `d` is in `s`. -/
def drank (d : Drink) : DrinkWorld → Truth
  | ⟨s, _⟩ => if d ∈ s then 1 else 0

/-- The three drinks, each a plurality of one atom: the alternatives of the illustrations with
single drinks.  The others take all the pluralities of drinks (`Set.univ`). -/
def atomicDrinks : Set (Plural Drink) :=
  {Plural.pure appleJuice, Plural.pure beer, Plural.pure cider}

/-! ## The contexts of the illustrations

Each context used by more than one illustration, and the prohibition states. -/

/-- The context of conjunction and disjunction: in each of its seven worlds Taro drank exactly the
drinks of a nonempty set. -/
def drankSomething : Set DrinkWorld :=
  {only {appleJuice}, only {beer}, only {cider},
    only {appleJuice, beer}, only {appleJuice, cider}, only {beer, cider},
    only {appleJuice, beer, cider}}

/-- The context of negation and negated conjunction: in each of its seven worlds Taro drank
exactly the drinks of a set that leaves some drink out. -/
def leftSomethingOut : Set DrinkWorld :=
  {only ∅, only {appleJuice}, only {beer}, only {cider},
    only {appleJuice, beer}, only {appleJuice, cider}, only {beer, cider}}

/-- The eighteen antichains of nonempty sets of drinks (no member is part of another), as lists:
the distinct ways of saying which combinations of drinks are permitted outcomes. -/
def antichains : List (List (Finset Drink)) :=
  [[{appleJuice}], [{beer}], [{cider}],
    [{appleJuice, beer}], [{appleJuice, cider}], [{beer, cider}], [{appleJuice, beer, cider}],
    [{appleJuice}, {beer}], [{appleJuice}, {cider}], [{beer}, {cider}],
    [{appleJuice}, {beer, cider}], [{beer}, {appleJuice, cider}], [{cider}, {appleJuice, beer}],
    [{appleJuice, beer}, {appleJuice, cider}], [{appleJuice, beer}, {beer, cider}],
    [{appleJuice, cider}, {beer, cider}],
    [{appleJuice}, {beer}, {cider}],
    [{appleJuice, beer}, {appleJuice, cider}, {beer, cider}]]

/-- The context of *can* and *must* with *or*: eighteen permission states, one for each
antichain `L`.  From it, the accessible worlds are `only t` for `t` in `L`; what Taro actually
drank there is left open (`s`). -/
def permissionStates (s : Finset Drink) : Set DrinkWorld :=
  {w | ∃ L ∈ antichains, w = ⟨s, L.map only⟩}

/-- The eight sets of drinks. -/
def drinkSets : List (Finset Drink) :=
  [∅, {appleJuice}, {beer}, {cider}, {appleJuice, beer}, {appleJuice, cider}, {beer, cider},
    {appleJuice, beer, cider}]

/-- The prohibition state of an antichain `L`: from it, the accessible worlds are `only t` for
every set `t` of drinks that includes no member of `L`, so the members of `L` are the minimal
combinations Taro may not drink in full.  What Taro actually drank there is left open (`s`). -/
def prohibitionState (s : Finset Drink) (L : List (Finset Drink)) : DrinkWorld :=
  ⟨s, (drinkSets.filter fun t => decide (∀ x ∈ L, ¬ x ⊆ t)).map only⟩

/-- The context of *can't* with *both*: eighteen prohibition states, one for each antichain. -/
def prohibitionStates (s : Finset Drink) : Set DrinkWorld :=
  {w | ∃ L ∈ antichains, w = prohibitionState s L}

/-! ## The hypotheses of the general results -/

open Classical in
/-- The drinks are independent: for any set of them, Taro drank exactly those somewhere. -/
theorem independent : Independent drank := fun S =>
  ⟨only (({appleJuice, beer, cider} : Finset Drink).filter (· ∈ S)), fun m => by
    cases m <;> simp +contextual [drank, only]⟩

/-- Accessibility is unconstrained: any nonempty finite set of worlds is the set accessible from
some world. -/
theorem unconstrained : Unconstrained acc := fun V _ =>
  ⟨⟨∅, V.toList⟩, by simp [acc]⟩

end Composition.Drinks
