import DeciNSSE.Complexity.SummaryBounds
import DeciNSSE.Complexity.SummaryComplete
import DeciNSSE.Complexity.SummarySound
import DeciNSSE.Main

/-! # Entailment by the summary search

A reader with the rejected-path property has a hole exactly when the empty word
is a hole or the summary search of its table succeeds, at the depth bound
`holeDepthBound N` and the dictionary bound at that depth. Over the empty
alphabet only the empty word is tested. For the label monitors this gives
decision procedures in each tree domain. For a system with `k` variables at
arity `n`, the search graph of a label monitor has at most
`2^((n + 1)^2 * 2^2^(20k + 20))` configurations, so a configuration fits in
`(n + 1)^2 * 2^2^(20k + 20)` bits.

## Main declarations

- `Summary.readerSearch`: the summary search of a reader at its bounds.
- `Summary.hole_iff_summarySearch`: hole existence through the summary search,
  for readers with the rejected-path property and a nonempty alphabet.
- `Summary.decideHole`: the resulting computable hole decision.
- `Summary.card_config_label_le`: the size of the search graph of a label monitor.
- `decideEntailsSummary`, `decideEntailsRegSummary`, `decideEntailsFinSummary`:
  entailment over arbitrary, regular and finite trees, with the correctness
  theorems `decideEntailsSummary_correct`, `decideEntailsRegSummary_correct` and
  `decideEntailsFinSummary_correct`.
-/

set_option autoImplicit false

namespace DeciNSSE

namespace Complexity.Summary

open Holes RejectedTail LetteredHierarchy HierarchyDepth ElementaryBound

section Search

variable {Q : Type*} [Fintype Q] [DecidableEq Q] {n : ℕ} (M : DFA (Fin n) Q)
  (R : Q → Q → Prop) [DecidableRel R] (T : Set Q) [DecidablePred (· ∈ T)]

/-- The summary search of a reader's table, with levels up to the hole depth bound and
at most the dictionary bound of blocks per level. -/
def readerSearch : Bool :=
  summarySearch (Table.ofReader M R T) (holeDepthBound (Fintype.card Q))
    (dictionaryBound (Fintype.card Q) (holeDepthBound (Fintype.card Q)))

/-- A reader with the rejected-path property over a nonempty alphabet has a hole exactly
when the empty word is a hole or the summary search succeeds. -/
theorem hole_iff_summarySearch [NeZero n] [RejectedPath M R T] :
    (∃ w, IsReaderHole M R T w) ↔ IsReaderHole M R T [] ∨ readerSearch M R T = true := by
  constructor
  · intro hh
    rcases (hole_iff_bounded_depth M R T).mp hh with h0 | ⟨w, hw0, hw, i, hi, hu⟩
    · exact Or.inl h0
    · refine Or.inr (summarySearch_complete le_rfl ?_
        ((LevelMaps.depth_le_of_isUnary hu).trans hi))
      rw [Table.toLettered_ofReader]
      exact (isHole_ofReader_iff M R T hw0).mpr hw
  · rintro (h0 | hs)
    · exact ⟨[], h0⟩
    · obtain ⟨w, hw, -⟩ := summarySearch_sound hs
      rw [Table.toLettered_ofReader] at hw
      exact ⟨w, (isHole_ofReader_iff M R T hw.ne_nil).mp hw⟩

omit [Fintype Q] [DecidableEq Q] [DecidableRel R] [DecidablePred (· ∈ T)] in
/-- Over the empty alphabet the only word is the empty word. -/
theorem hole_iff_nil_of_eq_zero (hn : n = 0) :
    (∃ w, IsReaderHole M R T w) ↔ IsReaderHole M R T [] := by
  subst hn
  refine ⟨fun ⟨w, hw⟩ => ?_, fun h => ⟨[], h⟩⟩
  cases w with
  | nil => exact hw
  | cons a _ => exact a.elim0

/-- The hole decision by the summary search. Over the empty alphabet it tests the empty
word only. -/
@[instance_reducible] def decideHole [RejectedPath M R T] :
    Decidable (∃ w, IsReaderHole M R T w) :=
  if hn : n = 0 then
    decidable_of_iff _ (hole_iff_nil_of_eq_zero M R T hn).symm
  else
    haveI : NeZero n := ⟨hn⟩
    decidable_of_iff _ (hole_iff_summarySearch M R T).symm

end Search

section Monitors

open Monitor

variable {n : ℕ} {c : Fin n → Bool} {k : ℕ} {ϕ : Constraint n k} {x y : V k}

/-- The search graph of a label monitor for a system with `k` variables at arity `n` has
at most `2^((n + 1)^2 * 2^2^(20k + 20))` configurations. -/
theorem card_config_label_le (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) :
    let P := (Monitor.family c).monitor ϕ x y θ
    Fintype.card (Config P.Q n (holeDepthBound (Fintype.card P.Q))
        (dictionaryBound (Fintype.card P.Q) (holeDepthBound (Fintype.card P.Q)))) ≤
      2 ^ ((n + 1) ^ 2 * 2 ^ 2 ^ (20 * k + 20)) := by
  intro P
  have hc : Fintype.card P.Q = 2 * 4 ^ (2 * k) := card_state (2 * k)
  refine (card_config_le _ _ _).trans (Nat.pow_le_pow_right (by decide) ?_)
  rw [hc]
  exact configBits_label_le n k

/-- The summary hole decision of a side monitor. -/
@[instance_reducible] def decideSideHoles {θ : Side} (P : SideMonitor n c ϕ x y θ) :
    Decidable (∃ w, P.Hole w) :=
  Summary.decideHole P.M P.R P.T

variable (Pl : SideMonitor n c ϕ x y .l) (Pr : SideMonitor n c ϕ x y .r)

/-- Entailment over arbitrary trees from two side monitors. Satisfiability is tested
first; the summary searches run only on satisfiable systems. -/
@[instance_reducible] def decideEntailsOfMonitors : Decidable (Entails c ϕ x y) :=
  letI := Summary.decideSideHoles Pl
  letI := Summary.decideSideHoles Pr
  decidable_of_iff _ (entails_iff_of_monitors Pl Pr).symm

/-- Entailment over regular trees, by regular transfer. -/
@[instance_reducible] def decideEntailsRegOfMonitors : Decidable (EntailsReg c ϕ x y) :=
  letI := Summary.decideEntailsOfMonitors Pl Pr
  decidable_of_iff _ (entailsReg_iff_entails c ϕ x y).symm

/-- Entailment over finite trees, by finite satisfiability and the unrestricted
decision. -/
@[instance_reducible] def decideEntailsFinOfMonitors : Decidable (EntailsFin c ϕ x y) :=
  letI := Summary.decideEntailsOfMonitors Pl Pr
  decidable_of_iff _ (entailsFin_iff_decider c ϕ x y).symm

end Monitors

end Complexity.Summary

section Deciders

open Complexity

variable {n k : ℕ}

/-- Decide entailment over arbitrary trees for the given variance, by the summary search
of the label monitors. -/
@[instance_reducible] def decideEntailsSummary (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) : Decidable (Entails c ϕ x y) :=
  Summary.decideEntailsOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r)

/-- Decide entailment over regular trees for the given variance, by the summary search. -/
@[instance_reducible] def decideEntailsRegSummary (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) : Decidable (EntailsReg c ϕ x y) :=
  Summary.decideEntailsRegOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r)

/-- Decide entailment over finite trees for the given variance, by the summary search. -/
@[instance_reducible] def decideEntailsFinSummary (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) : Decidable (EntailsFin c ϕ x y) :=
  Summary.decideEntailsFinOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r)

/-- The summary decision returns true exactly when unrestricted entailment holds. -/
theorem decideEntailsSummary_correct (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsSummary c ϕ x y) = true ↔ Entails c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsSummary c ϕ x y)

/-- The summary decision returns true exactly when regular-tree entailment holds. -/
theorem decideEntailsRegSummary_correct (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsRegSummary c ϕ x y) = true ↔ EntailsReg c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsRegSummary c ϕ x y)

/-- The summary decision returns true exactly when finite-tree entailment holds. -/
theorem decideEntailsFinSummary_correct (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsFinSummary c ϕ x y) = true ↔ EntailsFin c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsFinSummary c ϕ x y)

end Deciders

end DeciNSSE
