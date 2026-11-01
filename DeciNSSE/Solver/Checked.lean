import DeciNSSE.Solver.Reader

/-! # Checking certificates with packed readers

The executable checkers run the packed side readers of `Solver.Reader` and the packed
closure. They are the checkers used by `solve` and by the certificate command.

There are three entry points for refutations:
- the semantic check `refutesB c ϕ x y θ w`, with `refutesB_iff_unsafe` and
  `refutesB_correct` (in `Countermodels`);
- the certificate check `Certificates.checkRefutation c ϕ x y cert`, which is `refutesB`
  on the side and word of `cert` by definition (`Certificates.checkRefutation_eq_refutesB`);
- the packed check `Solver.Checked.checkRefutationPacked`, equal to both by
  `checkRefutationPacked_eq_refutesB`.

Entailment certificates have the specification `Certificates.checkEntailment` and the
packed check `checkEntailmentPacked`, with its own soundness theorem.

## Main declarations

- `Solver.Checked.packedSatB`, `Solver.Checked.packedSatB_eq`: packed satisfiability,
  equal to `Monitor.satB`.
- `Solver.Checked.checkHole`, `Solver.Checked.checkHole_iff`: the packed hole check of one
  word.
- `Solver.Checked.checkRefutationPacked`, `Solver.Checked.checkRefutationPacked_eq_refutesB`:
  the packed refutation check, equal to `refutesB`.
- `Solver.Checked.checkSidePacked`, `Solver.Checked.checkEntailmentPacked`,
  `Solver.Checked.checkEntailmentPacked_sound`: the packed cover and entailment checks.
-/

namespace DeciNSSE.Solver.Checked
open Certificates Holes Monitor
open scoped List
variable {n k : ℕ}

/-- Satisfiability with the packed closure shared by all label tests. -/
def packedSatB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool :=
  let ψ := signed c ϕ
  let d := derivedRows ψ
  let lowerF := fun (x : V (2 * k)) => (lowerLits ψ).any fun p => (d p.2).getLsbD x.val
  let lowerTop := fun (x : V (2 * k)) => (topVars ψ).any fun u => (d u).getLsbD x.val
  let upperF := fun x => (upperLits ψ).any fun p => (d x).getLsbD p.1.val
  let upperBot := fun x => (botVars ψ).any fun v => (d x).getLsbD v.val
  !((List.finRange (2 * k)).any fun x =>
    (lowerTop x && upperBot x) || (lowerTop x && upperF x) || (lowerF x && upperBot x))

/-- Packed satisfiability agrees with the specification `Monitor.satB`. -/
theorem packedSatB_eq (c : Fin n → Bool) (ϕ : Constraint n k) :
    packedSatB c ϕ = Monitor.satB c ϕ := by
  apply Bool.eq_iff_iff.mpr
  simp only [packedSatB, Monitor.satB, satInfB, labelClashB, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.any_eq_true, List.mem_finRange, true_and,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, bit_derivedRows, mem_derivedPairs,
    or_assoc]

/-- Cache prefix states before testing all pairs of cuts. -/
def checkHole (r : PackedReader n (2 * k)) (w : List (Fin n)) : Bool :=
  let qs := Mask.table fun i : Fin (w.length + 1) => r.machine.eval (w.take i)
  decide (r.accept (r.machine.eval w) = false ∧
    ∀ s e : Fin (w.length + 1), s.val < e.val → w.drop e <+: w.drop s →
      admitted (qs s) (qs e) = false)

/-- The packed hole check accepts exactly the holes of the packed reader. -/
theorem checkHole_iff (r : PackedReader n (2 * k)) (w : List (Fin n)) :
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

/-- The packed hole check of one side accepts exactly the holes of its side monitor. -/
theorem checkHole_iff_hole (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)
    (w : List (Fin n)) :
    checkHole (packedSideReader c ϕ x y θ) w = true ↔ (sideMonitor c ϕ x y θ).Hole w :=
  (checkHole_iff _ w).trans (packedSideReader_hole c ϕ x y θ w)

/-- The packed implementation of the refutation checker. -/
def checkRefutationPacked (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Refutation n) : Bool :=
  packedSatB c ϕ && checkHole (packedSideReader c ϕ x y cert.side) cert.word

/-- The packed refutation checker computes `refutesB`, hence also
`Certificates.checkRefutation`. -/
theorem checkRefutationPacked_eq_refutesB (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) (cert : Refutation n) :
    checkRefutationPacked c ϕ x y cert = refutesB c ϕ x y cert.side cert.word := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkRefutationPacked, refutesB, Bool.and_eq_true, decide_eq_true_eq,
    checkHole_iff, packedSideReader_hole, packedSatB_eq]

/-- Check the same covering product over the packed reader states. -/
def checkSidePacked (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (cert : Cover (Fin n)) : Bool :=
  let r := packedSideReader c ϕ x y θ
  checkCover r.machine (fun s t => admitted s t = true) {s | r.accept s = false} cert

/-- An accepted packed cover excludes every hole of its side. -/
theorem checkSidePacked_sound (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (cert : Cover (Fin n)) (h : checkSidePacked c ϕ x y θ cert = true) :
    ∀ w, ¬ (sideMonitor c ϕ x y θ).Hole w := by
  intro w hw
  exact checkCover_sound _ _ _ cert h w ((packedSideReader_hole c ϕ x y θ w).mpr hw)

/-- Entailment uses unsatisfiability or two accepted covers. -/
def checkEntailmentPacked (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Entailment n → Bool
  | .unsat => !(packedSatB c ϕ)
  | .cover l r => checkSidePacked c ϕ x y .l l && checkSidePacked c ϕ x y .r r

/-- An accepted packed entailment certificate proves arbitrary-tree entailment. -/
theorem checkEntailmentPacked_sound (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (cert : Entailment n) (h : checkEntailmentPacked c ϕ x y cert = true) :
    Entails c ϕ x y := by
  cases cert with
  | unsat =>
    apply Certificates.checkEntailment_sound c ϕ x y .unsat
    simpa only [checkEntailmentPacked, packedSatB_eq, Certificates.checkEntailment] using h
  | cover l r =>
    simp only [checkEntailmentPacked, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h
    apply (entails_iff_of_monitors (sideMonitor c ϕ x y .l) (sideMonitor c ϕ x y .r)).mpr
    exact Or.inr ⟨fun ⟨w, hw⟩ => checkSidePacked_sound c ϕ x y .l l hl w hw,
      fun ⟨w, hw⟩ => checkSidePacked_sound c ϕ x y .r r hr w hw⟩

end DeciNSSE.Solver.Checked
