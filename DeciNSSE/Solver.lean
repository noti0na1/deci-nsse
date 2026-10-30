import DeciNSSE.Solver.Complete
import DeciNSSE.Solver.Search
import DeciNSSE.Solver.Extraction
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.List

/-! # A total certifying entailment solver

Search results are checked before they become answers. Exhausted fuel falls
back to the complete decider. Refutations carry regular countermodels unless
they are not requested.
-/

namespace DeciNSSE
open Certificates
variable {n k : ℕ}

/-- A regular assignment whose unfolding satisfies `ϕ` and violates `x ≤ y`. -/
structure Countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) where
  graphs : V k → RGraph n
  correct : Sat c (RGraph.unfold ∘ graphs) ϕ ∧
    ¬ Tree.Le c (graphs x).unfold (graphs y).unfold

/-- Evidence for an answer, including the complete-decision fallback. -/
inductive SolverEvidence (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) where
  | entailed (certificate : Entailment n)
      (checked : Solver.Checked.checkEntailment c ϕ x y certificate = true)
  | complete (checked : @decide _ (decideEntails c ϕ x y) = true)
  | refuted (certificate : Refutation n)
      (checked : Solver.Checked.checkRefutation c ϕ x y certificate = true)
      (model : Option (Countermodel c ϕ x y))

/-- An answer retains its evidence and records whether search exhausted its fuel. -/
structure Result (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) where
  evidence : SolverEvidence c ϕ x y
  usedFallback : Bool

/-- The Boolean answer certified by the evidence. -/
def Result.answer {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    (r : Result c ϕ x y) : Bool :=
  match r.evidence with
  | .entailed .. | .complete .. => true
  | .refuted .. => false

/-- Every result certifies its Boolean answer over arbitrary trees. -/
theorem Result.correct {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    (r : Result c ϕ x y) : r.answer = true ↔ Entails c ϕ x y := by
  rcases r with ⟨e, fallback⟩
  cases e with
  | entailed cert h =>
    exact iff_of_true rfl (Solver.Checked.checkEntailment_sound c ϕ x y cert h)
  | complete h => exact iff_of_true rfl ((decideEntails_correct c ϕ x y).mp h)
  | refuted cert h _ =>
    exact iff_of_false (by simp [Result.answer]) (Certificates.checkRefutation_sound c ϕ x y cert
      ((Solver.Checked.checkRefutation_eq c ϕ x y cert).symm.trans h))

namespace Solver

/-- The reachable regular countermodel of an accepted refutation. -/
def countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Refutation n) (h : Checked.checkRefutation c ϕ x y cert = true) :
    Countermodel c ϕ x y :=
  let model := extractReachable c ϕ x y cert.side cert.word
  have hu : Unsafe c ϕ x y cert.side cert.word :=
    (refutesB_iff_unsafe c ϕ x y cert.side cert.word).mp (by
      have hc := (Checked.checkRefutation_eq c ϕ x y cert).symm.trans h
      exact hc)
  have he : RGraph.unfold ∘ model =
      RGraph.unfold ∘ extractRegular c ϕ x y cert.side cert.word :=
    funext (extractReachable_unfold c ϕ x y cert.side cert.word)
  have hs : Sat c (RGraph.unfold ∘ model) ϕ ∧
      ¬ Tree.Le c (model x).unfold (model y).unfold := by
    have hspec := extractRegular_of_unsafe hu
    rw [he]
    exact ⟨hspec.1, by
      rw [show (model x).unfold = _ from congrFun he x,
        show (model y).unfold = _ from congrFun he y]
      exact hspec.2⟩
  ⟨model, hs⟩

/-- Answer an accepted refutation, building its countermodel only if `withModel`. -/
def refuted (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Refutation n) (h : Checked.checkRefutation c ϕ x y cert = true)
    (fallback withModel : Bool) : Result c ϕ x y :=
  ⟨.refuted cert h (if withModel then some (countermodel c ϕ x y cert h) else none), fallback⟩

private def decodedRefutation (j : ℕ) : Refutation n :=
  match Encodable.decode (α := Bool × List (Fin n)) j with
  | none => ⟨.l, []⟩
  | some (side, word) => ⟨if side then .r else .l, word⟩

/-- Failure of the complete decider provides a computably searchable certificate. -/
def completeRefutation (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (h : ¬ Entails c ϕ x y) : {cert : Refutation n // Checked.checkRefutation c ϕ x y cert = true} :=
  have hex : ∃ j, Checked.checkRefutation c ϕ x y (decodedRefutation j) = true := by
    obtain ⟨θ, w, hw⟩ := (not_entails_iff_refutesB c ϕ x y).mp h
    have hc : Checked.checkRefutation c ϕ x y ⟨θ, w⟩ = true := by
      rw [Checked.checkRefutation_eq]
      exact hw
    cases θ
    · exact ⟨Encodable.encode (false, w), by simpa [decodedRefutation] using hc⟩
    · exact ⟨Encodable.encode (true, w), by simpa [decodedRefutation] using hc⟩
  ⟨decodedRefutation (Nat.find hex), Nat.find_spec hex⟩

/-- The complete decider settles every remaining query. -/
def fallback (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (withModel : Bool) : Result c ϕ x y :=
  if h : @decide _ (decideEntails c ϕ x y) = true then ⟨.complete h, true⟩
  else
    let cert := completeRefutation c ϕ x y (fun he => h ((decideEntails_correct c ϕ x y).mpr he))
    refuted c ϕ x y cert.val cert.property true withModel

end Solver

/-- Run a bounded certificate search, then use the complete decision procedure.
Countermodels of negative answers are built only if `withModel`. -/
def solveWithFuel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (fuel : ℕ) (window : ℕ := 0) (withModel : Bool := true) : Result c ϕ x y :=
  if h : Solver.Checked.checkEntailment c ϕ x y .unsat = true then
    ⟨.entailed .unsat h, false⟩
  else
    match Solver.Search.search c ϕ x y fuel window with
    | some (.entailment cert) =>
      if hc : Solver.Checked.checkEntailment c ϕ x y cert = true then
        ⟨.entailed cert hc, false⟩
      else Solver.fallback c ϕ x y withModel
    | some (.refutation cert) =>
      if hc : Solver.Checked.checkRefutation c ϕ x y cert = true then
        Solver.refuted c ϕ x y cert hc false withModel
      else Solver.fallback c ϕ x y withModel
    | none => Solver.fallback c ϕ x y withModel

/-- Solve with a default budget of one hundred thousand search turns. -/
def solve (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) : Result c ϕ x y :=
  solveWithFuel c ϕ x y 100000

/-- Every returned answer is correct, independently of search fuel. -/
theorem solveWithFuel_correct (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (fuel window : ℕ) (withModel : Bool) :
    (solveWithFuel c ϕ x y fuel window withModel).answer = true ↔ Entails c ϕ x y :=
  Result.correct _

/-- The executable solver decides entailment over arbitrary trees. -/
theorem solve_correct (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    (solve c ϕ x y).answer = true ↔ Entails c ϕ x y := Result.correct _

end DeciNSSE
