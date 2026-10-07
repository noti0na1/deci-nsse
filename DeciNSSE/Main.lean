import DeciNSSE.Monitor.Bridge
import DeciNSSE.Monitor.Decision

/-! # Decidability of non-structural subtype entailment

Entailment for one constructor of any finite arity and variance is decidable
over arbitrary, regular and finite trees. Satisfiability and two finite hole
searches decide unrestricted entailment; transfer gives the other two domains.
-/

namespace DeciNSSE

/-- Decide entailment over arbitrary trees for the given variance. -/
@[instance_reducible] def decideEntails {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) : Decidable (Entails c ϕ x y) :=
  Monitor.decideEntailsOf (Monitor.family c) ϕ x y

/-- Decide entailment over regular trees for the given variance. -/
@[instance_reducible] def decideEntailsReg {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Decidable (EntailsReg c ϕ x y) :=
  Monitor.decideEntailsRegOf (Monitor.family c) ϕ x y

/-- Decide entailment over finite trees for the given variance. -/
@[instance_reducible] def decideEntailsFin {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Decidable (EntailsFin c ϕ x y) :=
  Monitor.decideEntailsFinOf (Monitor.family c) ϕ x y

/-- The decision returns true exactly when unrestricted entailment holds. -/
theorem decideEntails_correct {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    @decide _ (decideEntails c ϕ x y) = true ↔ Entails c ϕ x y :=
  Monitor.decideEntailsOf_correct _ ϕ x y

/-- The decision returns true exactly when regular-tree entailment holds. -/
theorem decideEntailsReg_correct {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsReg c ϕ x y) = true ↔ EntailsReg c ϕ x y :=
  Monitor.decideEntailsRegOf_correct _ ϕ x y

/-- The decision returns true exactly when finite-tree entailment holds. -/
theorem decideEntailsFin_correct {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsFin c ϕ x y) = true ↔ EntailsFin c ϕ x y :=
  Monitor.decideEntailsFinOf_correct _ ϕ x y

end DeciNSSE
