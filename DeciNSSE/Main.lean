import DeciNSSE.Monitor.Bridge
import DeciNSSE.Monitor.Decision

/-! # Decidability of non-structural subtype entailment

Entailment for one constructor of any finite arity and variance is decidable
over arbitrary, regular and finite trees. Satisfiability and two finite hole
searches decide unrestricted entailment; transfer gives the other two domains.
Importing this module is enough for the three decision procedures.

The deciders are `@[instance_reducible] def`s rather than instances because each
proposition has several of them (these, the summary and arity-one deciders, and the packed
decider) and instance search should not choose one silently; the attribute gives them the
reducibility of an instance where they are installed with `letI` or passed to `@decide`.

## Compiled code

The `@[csimp]` lemma `Solver.decideEntails_eq_decideEntailsPacked`, in `Solver.Complete`,
makes compiled code of `decideEntails` run `Solver.decideEntailsPacked` whenever
`DeciNSSE.Solver` is imported. That decider uses packed Boolean checks and computes the
reader state count from its formula. `decideEntailsReg` and `decideEntailsFin` are not
redirected. They evaluate the packaged side monitors, whose `Fintype` instance enumerates
every reader state.

## Main declarations

- `decideEntails`, `decideEntailsReg`, `decideEntailsFin`: entailment over arbitrary,
  regular and finite trees, for every arity and variance.
- `decideEntails_correct`, `decideEntailsReg_correct`, `decideEntailsFin_correct`: each
  decision returns true exactly when the entailment holds.
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
