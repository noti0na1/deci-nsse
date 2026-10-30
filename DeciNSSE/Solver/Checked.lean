import DeciNSSE.Solver.Reader

/-! # Checking certificates with packed readers -/

namespace DeciNSSE.Solver.Checked
open Certificates Holes Monitor
open scoped List
variable {n k : ℕ}

/-- Satisfiability with the packed closure shared by all label tests. -/
def satB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool :=
  let ψ := signed c ϕ
  let d := derivedRows ψ
  let lowerF := fun (x : V (2 * k)) => (lowerLits ψ).any fun p => (d p.2).getLsbD x.val
  let lowerTop := fun (x : V (2 * k)) => (topVars ψ).any fun u => (d u).getLsbD x.val
  let upperF := fun x => (upperLits ψ).any fun p => (d x).getLsbD p.1.val
  let upperBot := fun x => (botVars ψ).any fun v => (d x).getLsbD v.val
  !((List.finRange (2 * k)).any fun x =>
    (lowerTop x && upperBot x) || (lowerTop x && upperF x) || (lowerF x && upperBot x))

theorem satB_eq (c : Fin n → Bool) (ϕ : Constraint n k) : satB c ϕ = Monitor.satB c ϕ := by
  apply Bool.eq_iff_iff.mpr
  simp only [satB, Monitor.satB, satInfB, labelClashB, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.any_eq_true, List.mem_finRange, true_and,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bit_derivedRows, mem_derivedPairs, or_assoc]

/-- Cache prefix states before testing all pairs of cuts. -/
def checkHole (r : Reader n (2 * k)) (w : List (Fin n)) : Bool :=
  let qs := Mask.table fun i : Fin (w.length + 1) => r.machine.eval (w.take i)
  decide (r.accept (r.machine.eval w) = false ∧
    ∀ s e : Fin (w.length + 1), s.val < e.val → w.drop e <+: w.drop s →
      admitted (qs s) (qs e) = false)

theorem checkHole_iff (r : Reader n (2 * k)) (w : List (Fin n)) :
    checkHole r w = true ↔ IsReaderHole r.machine (fun s t => admitted s t = true)
      {s | r.accept s = false} w := by
  simp only [checkHole, decide_eq_true_eq, Mask.table_eq, isReaderHole_iff,
    Set.mem_ofPred_eq, Bool.eq_false_iff]
  apply and_congr_right
  intro _
  constructor
  · intro h s e hse he hp
    exact h ⟨s, by omega⟩ ⟨e, by omega⟩ hse hp
  · intro h s e hse hp
    exact h s e hse (by have := e.isLt; omega) hp

/-- The packed implementation of the refutation checker. -/
def checkRefutation (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Refutation n) : Bool :=
  let ψ := Events.sideSystem c ϕ cert.side
  let q := Events.sideQuery x y cert.side
  satB c ϕ && checkHole (reader ψ q.1 q.2) cert.word

/-- The packed and finite-set refutation checkers agree exactly. -/
theorem checkRefutation_eq (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Refutation n) :
    checkRefutation c ϕ x y cert = Certificates.checkRefutation c ϕ x y cert := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkRefutation, Certificates.checkRefutation, Bool.and_eq_true,
    decide_eq_true_eq, checkHole_iff, reader_hole, satB_eq]

/-- Check the same covering product over the packed reader states. -/
def checkSide (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (cert : Cover (Fin n)) : Bool :=
  let ψ := Events.sideSystem c ϕ θ
  let q := Events.sideQuery x y θ
  let r := reader ψ q.1 q.2
  checkCover r.machine (fun s t => admitted s t = true) {s | r.accept s = false} cert

theorem checkSide_sound (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (cert : Cover (Fin n)) (h : checkSide c ϕ x y θ cert = true) :
    ∀ w, ¬ (sideMonitor c ϕ x y θ).Hole w := by
  intro w hw
  exact checkCover_sound _ _ _ cert h w ((reader_hole _ _ _ w).mpr hw)

/-- Entailment uses unsatisfiability or two accepted covers. -/
def checkEntailment (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Entailment n → Bool
  | .unsat => !(satB c ϕ)
  | .cover l r => checkSide c ϕ x y .l l && checkSide c ϕ x y .r r

theorem checkEntailment_sound (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Entailment n) (h : checkEntailment c ϕ x y cert = true) : Entails c ϕ x y := by
  cases cert with
  | unsat =>
    apply Certificates.checkEntailment_sound c ϕ x y .unsat
    simpa only [checkEntailment, satB_eq, Certificates.checkEntailment] using h
  | cover l r =>
    simp only [checkEntailment, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h
    apply (entails_iff_of_monitors (sideMonitor c ϕ x y .l) (sideMonitor c ϕ x y .r)).mpr
    exact Or.inr ⟨fun ⟨w, hw⟩ => checkSide_sound c ϕ x y .l l hl w hw,
      fun ⟨w, hw⟩ => checkSide_sound c ϕ x y .r r hr w hw⟩

end DeciNSSE.Solver.Checked
