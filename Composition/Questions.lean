import Mathlib.Data.Set.Lattice.Indexed

/-!
# Question semantics

Questions as sets of propositions (sets of worlds), exhaustification (`exh_krifka`), and
question–partition matching, with its characterization.  Nothing here depends on truth values
or on the ontology.  Readable.
-/

namespace Composition

variable {World : Type}

/-! ## Matching

A question is a set of propositions.  It partitions a context `k` into cells: `u`, `v` are
equivalent iff they verify the same members of the question. -/

/-- The exhaustivity operator, `exh_krifka`: `p`, and no alternative that `p` does not entail. -/
def exh (Q : Set (Set World)) (p : Set World) : Set World :=
  p \ ⋃ q ∈ {q ∈ Q | ¬ p ⊆ q}, q

/-- `Q` does not distinguish `u` from `v`. -/
def Agree (Q : Set (Set World)) (u v : World) : Prop := ∀ p ∈ Q, (u ∈ p ↔ v ∈ p)

/-- The cells `Q` induces on `k`. -/
def partition (k : Set World) (Q : Set (Set World)) : Set (Set World) :=
  {{v ∈ k | Agree Q w v} | w ∈ k}

/-- **Question–partition matching** (Fox 2018): `p ↦ k ∩ exh Q p` is a bijection from `Q` onto
the cells of `k`. -/
def Matches (k : Set World) (Q : Set (Set World)) : Prop :=
  Set.BijOn (fun p => k ∩ exh Q p) Q (partition k Q)

/-- `exh Q p` holds at `w` iff `p` holds at `w` and entails every member of `Q` that holds there:
for `p ∈ Q`, `p` is the strongest member of `Q` true at `w`. -/
theorem mem_exh {Q : Set (Set World)} {p : Set World} {w : World} :
    w ∈ exh Q p ↔ w ∈ p ∧ ∀ q ∈ Q, w ∈ q → p ⊆ q := by
  simp only [exh, Set.mem_sdiff, Set.mem_iUnion₂, Set.mem_ofPred_eq, not_exists]
  exact and_congr_right fun _ => ⟨fun h q hq hw => by_contra fun hn => h q ⟨hq, hn⟩ hw,
    fun h q ⟨hq, hn⟩ hw => hn (h q hq hw)⟩

/-- **Matching, characterized**: `Q` matches `k` iff the cell `exh Q p` of each alternative meets
`k` (every answer is live), and the cells cover `k` (Dayal's maximal answer exists throughout
`k`). -/
theorem matches_iff {k : Set World} {Q : Set (Set World)} :
    Matches k Q ↔
    (∀ p ∈ Q, (k ∩ exh Q p).Nonempty) ∧ k ⊆ ⋃ p ∈ Q, exh Q p := by
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.subset_def, Set.mem_iUnion₂, exists_prop]
  have self : ∀ {w}, w ∈ k → w ∈ {v | v ∈ k ∧ Agree Q w v} :=
    fun hw => ⟨hw, fun _ _ => Iff.rfl⟩
  have cell : ∀ {p}, p ∈ Q → ∀ {w}, w ∈ k → w ∈ exh Q p →
      k ∩ exh Q p = {v | v ∈ k ∧ Agree Q w v} := by
    intro p hp w hwk hw
    obtain ⟨hwp, hws⟩ := mem_exh.mp hw
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, mem_exh]
    constructor
    · rintro ⟨hvk, hvp, hvs⟩
      exact ⟨hvk, fun q hq => ⟨fun hwq => hws q hq hwq hvp, fun hvq => hvs q hq hvq hwp⟩⟩
    · rintro ⟨hvk, hag⟩
      exact ⟨hvk, (hag p hp).mp hwp, fun q hq hvq => hws q hq ((hag q hq).mpr hvq)⟩
  refine ⟨fun h => ⟨fun p hp => ?_, fun w hw => ?_⟩, fun ⟨live, cover⟩ => ?_⟩
  · obtain ⟨w, hwk, e⟩ := h.1 hp
    have hw : w ∈ k ∩ exh Q p := by rw [show k ∩ exh Q p = _ from e.symm]; exact self hwk
    exact ⟨w, hwk, hw.2⟩
  · obtain ⟨p, hp, e⟩ := h.2.2 ⟨w, hw, rfl⟩
    have hw' : w ∈ k ∩ exh Q p := by rw [show k ∩ exh Q p = _ from e]; exact self hw
    exact ⟨p, hp, hw'.2⟩
  refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, ?_⟩
  · obtain ⟨w, hwk, hw⟩ := live p hp
    exact ⟨w, hwk, (cell hp hwk hw).symm⟩
  · obtain ⟨w, hwk, hw⟩ := live p hp
    have hw' : w ∈ k ∩ exh Q p' := by
      rw [← show k ∩ exh Q p = k ∩ exh Q p' from h]; exact ⟨hwk, hw⟩
    exact ((mem_exh.mp hw).2 p' hp' (mem_exh.mp hw'.2).1).antisymm
      ((mem_exh.mp hw'.2).2 p hp (mem_exh.mp hw).1)
  · rintro c ⟨w, hwk, rfl⟩
    obtain ⟨p, hp, hw⟩ := cover w hwk
    exact ⟨p, hp, cell hp hwk hw⟩

/-- **Two incomparable alternatives and their disjunction fail** in every context: the
disjunction is the strongest true alternative nowhere. -/
theorem not_matches_of_union {k : Set World} {Q : Set (Set World)} {p q : Set World}
    (hp : p ∈ Q) (hq : q ∈ Q) (hpq : p ∪ q ∈ Q) (hnq : ¬ q ⊆ p) (hnp : ¬ p ⊆ q) :
    ¬ Matches k Q := by
  intro h
  obtain ⟨w, -, hw⟩ := (matches_iff.mp h).1 _ hpq
  obtain ⟨hwpq, hs⟩ := mem_exh.mp hw
  rcases hwpq with hwp | hwq
  · exact hnq (Set.subset_union_right.trans (hs p hp hwp))
  · exact hnp (Set.subset_union_left.trans (hs q hq hwq))

end Composition
