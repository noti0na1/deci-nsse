import DeciNSSE.Monitor.Interface
import DeciNSSE.Satisfiability.FiniteVariance
import DeciNSSE.Transfer.Finite
import DeciNSSE.Transfer.Regular

/-! # Entailment from finite monitors

Satisfiability is tested before either hole search. The absence of holes on
both sides decides arbitrary-tree entailment; regular and finite transfer
give the corresponding decisions in the restricted domains.
-/

set_option autoImplicit false

namespace DeciNSSE.Monitor

variable {n : ℕ} {c : Fin n → Bool} {k : ℕ}

section Equation

variable {ϕ : Constraint n k} {x y : V k}

/-- With both side monitors, entailment is unsatisfiability or the absence of holes. -/
theorem entails_iff_of_monitors (Pl : SideMonitor n c ϕ x y .l)
    (Pr : SideMonitor n c ϕ x y .r) :
    Entails c ϕ x y ↔
      satB c ϕ = false ∨ ((¬ ∃ w, Pl.Hole w) ∧ (¬ ∃ w, Pr.Hole w)) := by
  rw [entails_iff_not_sideUnsafe, satB_eq_false_iff]
  by_cases hs : ∃ ρ, Sat c ρ ϕ
  · simp only [hs, not_true_eq_false, false_or]
    constructor
    · intro h
      exact ⟨fun ⟨w, hw⟩ => h .l w ((Pl.hole_iff_unsafe hs w).mp hw),
        fun ⟨w, hw⟩ => h .r w ((Pr.hole_iff_unsafe hs w).mp hw)⟩
    · rintro ⟨hl, hr⟩ θ w hu
      cases θ
      · exact hl ⟨w, (Pl.hole_iff_unsafe hs w).mpr hu⟩
      · exact hr ⟨w, (Pr.hole_iff_unsafe hs w).mpr hu⟩
  · simp only [hs, not_false_eq_true, true_or, iff_true]
    intro θ w
    exact not_sideUnsafe_of_unsat hs w

/-- An unsatisfiable system entails everything. -/
theorem entails_of_satB_false (h : satB c ϕ = false) : Entails c ϕ x y :=
  fun ρ hρ => absurd ⟨ρ, hρ⟩ ((satB_eq_false_iff c ϕ).mp h)

/-- On a satisfiable system, entailment is the absence of holes on both sides. -/
theorem entails_iff_no_holes (Pl : SideMonitor n c ϕ x y .l)
    (Pr : SideMonitor n c ϕ x y .r) (h : satB c ϕ = true) :
    Entails c ϕ x y ↔ (¬ ∃ w, Pl.Hole w) ∧ (¬ ∃ w, Pr.Hole w) := by
  rw [entails_iff_of_monitors Pl Pr, h]
  simp

/-- Finite entailment is finite unsatisfiability or unrestricted entailment. -/
theorem entailsFin_iff_decider (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    EntailsFin c ϕ x y ↔ satFinB c ϕ = false ∨ Entails c ϕ x y := by
  rw [entailsFin_iff, satFinB_eq_false_iff]

end Equation

section Monitors

variable {ϕ : Constraint n k} {x y : V k}

/-- Entailment over arbitrary trees, from the two side monitors. Satisfiability
is tested first; the hole searches run only on satisfiable systems. -/
@[instance_reducible] def decideEntailsOfMonitors (Pl : SideMonitor n c ϕ x y .l)
    (Pr : SideMonitor n c ϕ x y .r) : Decidable (Entails c ϕ x y) :=
  if h : satB c ϕ = true then
    letI := Pl.decideHoles
    letI := Pr.decideHoles
    decidable_of_iff _ (entails_iff_no_holes Pl Pr h).symm
  else
    isTrue (entails_of_satB_false (Bool.eq_false_iff.mpr h))

/-- Decide regular entailment using the two side monitors and regular transfer. -/
@[instance_reducible] def decideEntailsRegOfMonitors (Pl : SideMonitor n c ϕ x y .l)
    (Pr : SideMonitor n c ϕ x y .r) : Decidable (EntailsReg c ϕ x y) :=
  letI := decideEntailsOfMonitors Pl Pr
  decidable_of_iff _ (entailsReg_iff_entails c ϕ x y).symm

/-- Decide finite entailment by finite satisfiability and the two side monitors. -/
@[instance_reducible] def decideEntailsFinOfMonitors (Pl : SideMonitor n c ϕ x y .l)
    (Pr : SideMonitor n c ϕ x y .r) : Decidable (EntailsFin c ϕ x y) :=
  if h : satFinB c ϕ = true then
    letI := decideEntailsOfMonitors Pl Pr
    decidable_of_iff (Entails c ϕ x y) (by rw [entailsFin_iff_decider, h]; simp)
  else
    isTrue (entailsFin_of_not_satFinB (Bool.eq_false_iff.mpr h) x y)

end Monitors

section Family

/-- Entailment over arbitrary trees, conditional on a monitor family. -/
@[instance_reducible] def decideEntailsOf (F : Family n c) (ϕ : Constraint n k)
    (x y : V k) : Decidable (Entails c ϕ x y) :=
  decideEntailsOfMonitors (F.monitor ϕ x y .l) (F.monitor ϕ x y .r)

/-- Entailment over regular trees, conditional on a monitor family. -/
@[instance_reducible] def decideEntailsRegOf (F : Family n c) (ϕ : Constraint n k)
    (x y : V k) : Decidable (EntailsReg c ϕ x y) :=
  decideEntailsRegOfMonitors (F.monitor ϕ x y .l) (F.monitor ϕ x y .r)

/-- Entailment over finite trees, conditional on a monitor family. -/
@[instance_reducible] def decideEntailsFinOf (F : Family n c) (ϕ : Constraint n k)
    (x y : V k) : Decidable (EntailsFin c ϕ x y) :=
  decideEntailsFinOfMonitors (F.monitor ϕ x y .l) (F.monitor ϕ x y .r)

/-- The monitor-family decision returns true exactly when unrestricted entailment holds. -/
theorem decideEntailsOf_correct (F : Family n c) (ϕ : Constraint n k) (x y : V k) :
    @decide _ (decideEntailsOf F ϕ x y) = true ↔ Entails c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsOf F ϕ x y)

/-- The monitor-family decision returns true exactly when regular-tree entailment holds. -/
theorem decideEntailsRegOf_correct (F : Family n c) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsRegOf F ϕ x y) = true ↔ EntailsReg c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsRegOf F ϕ x y)

/-- The monitor-family decision returns true exactly when finite-tree entailment holds. -/
theorem decideEntailsFinOf_correct (F : Family n c) (ϕ : Constraint n k)
    (x y : V k) :
    @decide _ (decideEntailsFinOf F ϕ x y) = true ↔ EntailsFin c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsFinOf F ϕ x y)

end Family

end DeciNSSE.Monitor
