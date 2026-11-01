import DeciNSSE.Certificates.Product
import DeciNSSE.Countermodels

/-! # Certificates for subtype entailment

A refutation supplies a hole on one side of a satisfiable query. Entailment
supplies either an unsatisfiability check or closed covering products for both
sides. The conclusions concern arbitrary trees and, by transfer, regular trees;
entailment certificates also prove finite-tree entailment. The checkers read the
label reader `Monitor.sideReader` of each side directly. The executable checkers
of `Solver.Checked` run the same checks with packed readers.

## Main declarations

- `Certificates.Refutation`, `Certificates.Entailment`: the two certificate types.
- `Certificates.checkRefutation`: the refutation check, which is `refutesB` by
  definition (`Certificates.checkRefutation_eq_refutesB`).
- `Certificates.checkSide`, `Certificates.checkEntailment`: the cover check of one side
  and the entailment check.
- `Certificates.checkRefutation_sound`, `Certificates.checkEntailment_sound`: soundness
  over arbitrary trees, with the variants `checkRefutation_sound_regular`,
  `checkEntailment_sound_regular` and `checkEntailment_sound_finite`. A refutation does not
  refute finite entailment, which may hold because the system has no finite solution.
-/

namespace DeciNSSE.Certificates
open Monitor Holes

variable {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- A refutation names a side and a word in its hole language. -/
structure Refutation (n : ℕ) where
  /-- The side of the query. -/
  side : Side
  /-- A hole of the reader of that side. -/
  word : List (Fin n)

/-- Entailment is certified by unsatisfiability or by a cover of each side. -/
inductive Entailment (n : ℕ) where
  /-- The system is unsatisfiable. -/
  | unsat
  /-- Covering products for the top-prefix side `left` and the bottom-prefix side
  `right`. -/
  | cover (left right : Cover (Fin n))

/-- Check satisfiability and the supplied hole: the Boolean check `refutesB` on the side
and the word of the certificate. -/
def checkRefutation (cert : Refutation n) : Bool :=
  refutesB c ϕ x y cert.side cert.word

/-- The refutation check is `refutesB` by definition. -/
theorem checkRefutation_eq_refutesB (cert : Refutation n) :
    checkRefutation c ϕ x y cert = refutesB c ϕ x y cert.side cert.word := rfl

/-- Check the finite covering product of one query side. -/
def checkSide (θ : Side) (cert : Cover (Fin n)) : Bool :=
  checkCover (sideReader c ϕ x y θ) admission (sideTarget c ϕ θ) cert

/-- Check an unsatisfiability certificate or both side covers. -/
def checkEntailment : Entailment n → Bool
  | .unsat => !(satB c ϕ)
  | .cover left right => checkSide c ϕ x y .l left && checkSide c ϕ x y .r right

/-- An accepted refutation disproves arbitrary-tree entailment. -/
theorem checkRefutation_sound (cert : Refutation n)
    (h : checkRefutation c ϕ x y cert = true) : ¬ Entails c ϕ x y :=
  refutesB_correct h

/-- An accepted entailment certificate proves arbitrary-tree entailment. -/
theorem checkEntailment_sound (cert : Entailment n)
    (h : checkEntailment c ϕ x y cert = true) : Entails c ϕ x y := by
  cases cert with
  | unsat =>
    exact entails_of_satB_false (by simpa [checkEntailment] using h)
  | cover left right =>
    simp only [checkEntailment, Bool.and_eq_true] at h
    obtain ⟨hl, hr⟩ := h
    apply (entails_iff_of_monitors (sideMonitor c ϕ x y .l) (sideMonitor c ϕ x y .r)).mpr
    right
    exact ⟨fun ⟨w, hw⟩ => checkCover_sound _ _ _ left hl w hw,
      fun ⟨w, hw⟩ => checkCover_sound _ _ _ right hr w hw⟩

/-- The same entailment certificate proves regular-tree entailment. -/
theorem checkEntailment_sound_regular (cert : Entailment n)
    (h : checkEntailment c ϕ x y cert = true) : EntailsReg c ϕ x y :=
  (entailsReg_iff_entails c ϕ x y).mpr (checkEntailment_sound c ϕ x y cert h)

/-- The same entailment certificate proves finite-tree entailment. -/
theorem checkEntailment_sound_finite (cert : Entailment n)
    (h : checkEntailment c ϕ x y cert = true) : EntailsFin c ϕ x y :=
  (entailsFin_iff c ϕ x y).mpr (Or.inr (checkEntailment_sound c ϕ x y cert h))

/-- The same refutation disproves regular-tree entailment. -/
theorem checkRefutation_sound_regular (cert : Refutation n)
    (h : checkRefutation c ϕ x y cert = true) : ¬ EntailsReg c ϕ x y :=
  fun he => checkRefutation_sound c ϕ x y cert h ((entailsReg_iff_entails c ϕ x y).mp he)

end DeciNSSE.Certificates
