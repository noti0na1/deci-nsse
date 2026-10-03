import DeciNSSE.RejectedTail.BoundedTail
import DeciNSSE.RejectedTail.Depth

/-! # Decidability of non-structural subtype entailment

Entailment over finite or infinite trees reduces to unsatisfiability or the absence
of holes in two finite monitors. A bound on the rejected tail gives a bound on
canonical hierarchy depth, and bounded depth gives a finite search for holes.
Regular-tree entailment agrees with infinite-tree entailment; finite-tree
entailment also holds whenever the constraints have no finite solution.
-/

namespace DeciNSSE

variable {k : ℕ}

namespace Bridge

open RejectedTail

/-- The hierarchy depth bound obtained from the quadratic rejected-tail bound. -/
def rejectedTailDepthBound (ϕ : Constraint k) (x y : V k) (side : Side) : ℕ :=
  2 * Fintype.card (State ϕ x y side) * max 1 (rejectedTailBound ϕ x y side) - 1

/-- Holes with bounded rejected tail lie within `rejectedTailDepthBound`. -/
theorem rejectedTailDepthBound_spec (ϕ : Constraint k) (x y : V k) (side : Side) :
    RejectedTailDepth ϕ x y side (rejectedTailBound ϕ x y side)
      (rejectedTailDepthBound ϕ x y side) :=
  rejectedTailDepth ϕ x y side (rejectedTailBound ϕ x y side)

end Bridge

/-- Decide whether every solution by finite or infinite trees satisfies `x ≤ y`. -/
def decideEntails (ϕ : Constraint k) (x y : V k) : Decidable (Entails ϕ x y) :=
  Bridge.decideEntailsOfRejectedTailDepth ϕ x y (Bridge.rejectedTailDepthBound ϕ x y)
    (Bridge.rejectedTailDepthBound_spec ϕ x y)

/-- The entailment decision returns true exactly when the constraints entail `x ≤ y`. -/
theorem decideEntails_correct (ϕ : Constraint k) (x y : V k) :
    @decide (Entails ϕ x y) (decideEntails ϕ x y) = true ↔ Entails ϕ x y :=
  @decide_eq_true_iff (Entails ϕ x y) (decideEntails ϕ x y)

/-- Decide entailment over regular trees using its equivalence with infinite-tree entailment. -/
def decideEntailsReg (ϕ : Constraint k) (x y : V k) : Decidable (EntailsReg ϕ x y) := by
  letI := decideEntails ϕ x y
  exact decidable_of_iff (Entails ϕ x y) entails_iff_entailsReg

/-- The regular-tree decision returns true exactly when regular-tree entailment holds. -/
theorem decideEntailsReg_correct (ϕ : Constraint k) (x y : V k) :
    @decide (EntailsReg ϕ x y) (decideEntailsReg ϕ x y) = true ↔ EntailsReg ϕ x y :=
  @decide_eq_true_iff (EntailsReg ϕ x y) (decideEntailsReg ϕ x y)

/-- Decide finite-tree entailment, including the case of no finite solution. -/
def decideEntailsFin (ϕ : Constraint k) (x y : V k) : Decidable (EntailsFin ϕ x y) :=
  if hs : satFinB ϕ = false then
    isTrue (entailsFin_iff_decider.mpr (Or.inl hs))
  else
    letI := decideEntails ϕ x y
    decidable_of_iff (Entails ϕ x y) (by
      rw [entailsFin_iff_decider, or_iff_right hs])

/-- The finite-tree decision returns true exactly when finite-tree entailment holds. -/
theorem decideEntailsFin_correct (ϕ : Constraint k) (x y : V k) :
    @decide (EntailsFin ϕ x y) (decideEntailsFin ϕ x y) = true ↔ EntailsFin ϕ x y :=
  @decide_eq_true_iff (EntailsFin ϕ x y) (decideEntailsFin ϕ x y)

end DeciNSSE
