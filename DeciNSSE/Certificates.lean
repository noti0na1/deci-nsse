import DeciNSSE.Certificates.Product
import DeciNSSE.Monitor.Bridge
import DeciNSSE.Monitor.Decision

/-! # Certificates for subtype entailment

A refutation supplies a hole on one side of a satisfiable query. Entailment
supplies either an unsatisfiability check or closed covering products for both
sides. The conclusions concern arbitrary trees and, by transfer, regular trees.
-/

set_option autoImplicit false
namespace DeciNSSE.Certificates
open Monitor Holes Events

variable {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- A refutation names a side and a word in its hole language. -/
structure Refutation (n : ℕ) where
  side : Side
  word : List (Fin n)

/-- Entailment is certified by unsatisfiability or by a cover of each side. -/
inductive Entailment (n : ℕ) where
  | unsat
  | cover (left right : Cover (Fin n))

/-- The label reader of one side, as in `sideMonitor`. The checkers use it
directly: the packaged monitor also carries a `Fintype` instance, and
evaluating that instance would enumerate every reader state. -/
abbrev sideReader (θ : Side) :=
  reader (sideSystem c ϕ θ) (sideQuery x y θ).1 (sideQuery x y θ).2

/-- Check satisfiability and the supplied hole. -/
def checkRefutation (cert : Refutation n) : Bool :=
  satB c ϕ && decide (IsReaderHole (sideReader c ϕ x y cert.side) admission
    (target (sideSystem c ϕ cert.side)) cert.word)

/-- Check the finite covering product of one query side. -/
def checkSide (θ : Side) (cert : Cover (Fin n)) : Bool :=
  checkCover (sideReader c ϕ x y θ) admission (target (sideSystem c ϕ θ)) cert

/-- Check an unsatisfiability certificate or both side covers. -/
def checkEntailment : Entailment n → Bool
  | .unsat => !(satB c ϕ)
  | .cover left right => checkSide c ϕ x y .l left && checkSide c ϕ x y .r right

/-- An accepted refutation disproves arbitrary-tree entailment. -/
theorem checkRefutation_sound (cert : Refutation n)
    (h : checkRefutation c ϕ x y cert = true) : ¬ Entails c ϕ x y := by
  simp only [checkRefutation, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, hh⟩ := h
  have hu := (sideMonitor c ϕ x y cert.side).hole_iff_unsafe
    ((satB_iff c ϕ).mp hs) cert.word |>.mp hh
  intro he
  exact (entails_iff_not_sideUnsafe c ϕ x y).mp he cert.side cert.word hu

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

/-- The same refutation disproves regular-tree entailment. -/
theorem checkRefutation_sound_regular (cert : Refutation n)
    (h : checkRefutation c ϕ x y cert = true) : ¬ EntailsReg c ϕ x y :=
  fun he => checkRefutation_sound c ϕ x y cert h ((entailsReg_iff_entails c ϕ x y).mp he)

end DeciNSSE.Certificates
