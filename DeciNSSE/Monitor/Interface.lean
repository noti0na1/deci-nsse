import DeciNSSE.RejectedTail.Decision
import DeciNSSE.Satisfiability.FiniteVariance
import DeciNSSE.Transfer.Safety

/-! # The semantic monitor interface

A side monitor combines a finite reader, a decidable target and admissions,
the rejected-path invariant, and a hole/unsafety equivalence for satisfiable
systems. A family supplies these data for every constraint system and query.
-/

set_option autoImplicit false

namespace DeciNSSE.Monitor

open Holes RejectedTail

variable {n : ℕ} {c : Fin n → Bool} {k : ℕ}

/-- Decide variance satisfiability through the covariant signed translation. -/
def satB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool := satInfB (signed c ϕ)

/-- The Boolean satisfiability test succeeds exactly when a solution exists. -/
theorem satB_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satB c ϕ = true ↔ ∃ ρ, Sat c ρ ϕ :=
  (satInfB_iff _).trans (sat_iff_signed_sat c ϕ).symm

theorem satB_eq_false_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satB c ϕ = false ↔ ¬ ∃ ρ, Sat c ρ ϕ := by
  rw [← satB_iff, Bool.not_eq_true]

/-- The interface. A finite monitor for the side `θ` of the query
`ϕ ⊨? x ≤ y` at arity `n` and variance `c`: a reader over `Fin n` with finite,
decidable state space, a decidable relation and target, a rejected-path
instance, and the semantic side bridge under satisfiability. -/
structure SideMonitor (n : ℕ) (c : Fin n → Bool) {k : ℕ} (ϕ : Constraint n k) (x y : V k)
    (θ : Side) where

  Q : Type
  [instFintype : Fintype Q]
  [instDecEq : DecidableEq Q]

  M : DFA (Fin n) Q

  R : Q → Q → Prop
  [instDecRel : DecidableRel R]

  T : Set Q
  [instDecT : DecidablePred (· ∈ T)]
  [instRejected : RejectedPath M R T]

  bridge : (∃ ρ, Sat c ρ ϕ) → ∀ w, IsReaderHole M R T w ↔ Unsafe c ϕ x y θ w

attribute [scoped instance] SideMonitor.instFintype SideMonitor.instDecEq
  SideMonitor.instDecRel SideMonitor.instDecT SideMonitor.instRejected

namespace SideMonitor

variable {ϕ : Constraint n k} {x y : V k} {θ : Side}

/-- The hole language of the packaged reader. -/
def Hole (P : SideMonitor n c ϕ x y θ) (w : List (Fin n)) : Prop := IsReaderHole P.M P.R P.T w

/-- The finite hole search of the generic back end, for the packaged reader. -/
@[instance_reducible] def decideHoles (P : SideMonitor n c ϕ x y θ) :
    Decidable (∃ w, P.Hole w) :=
  DeciNSSE.RejectedTail.decideHole P.M P.R P.T

/-- Under satisfiability, holes are exactly the unsafe words of the side. -/
theorem hole_iff_unsafe (P : SideMonitor n c ϕ x y θ) (hs : ∃ ρ, Sat c ρ ϕ)
    (w : List (Fin n)) : P.Hole w ↔ Unsafe c ϕ x y θ w :=
  P.bridge hs w

/-- Hole existence is witnessed within the explicit length bound. -/
theorem hole_iff_bounded (P : SideMonitor n c ϕ x y θ) :
    (∃ w, P.Hole w) ↔
      ∃ w, P.Hole w ∧ w.length ≤ RejectedTail.holeLengthBound (Fintype.card P.Q) :=
  RejectedTail.hole_iff_bounded_length P.M P.R P.T

/-- In a satisfiable system, every unsafe side has a bounded witness. -/
theorem unsafe_iff_bounded (P : SideMonitor n c ϕ x y θ) (hs : ∃ ρ, Sat c ρ ϕ) :
    (∃ w, Unsafe c ϕ x y θ w) ↔
      ∃ w, Unsafe c ϕ x y θ w ∧
        w.length ≤ RejectedTail.holeLengthBound (Fintype.card P.Q) := by
  have h := P.hole_iff_bounded
  simp only [P.hole_iff_unsafe hs] at h
  exact h

end SideMonitor

/-- A monitor family at arity `n` and variance `c`: a side monitor for every
system, query and side. It is data, so deciders parametric in it stay
computable. -/
structure Family (n : ℕ) (c : Fin n → Bool) where

  monitor : ∀ {k : ℕ} (ϕ : Constraint n k) (x y : V k) (θ : Side),
    SideMonitor n c ϕ x y θ

section Trivial

variable {ϕ : Constraint n k} {x y : V k} {θ : Side}

/-- An unsatisfiable system has no unsafe word. -/
theorem not_sideUnsafe_of_unsat (h : ¬ ∃ ρ, Sat c ρ ϕ) (w : List (Fin n)) :
    ¬ Unsafe c ϕ x y θ w := by
  cases θ
  · rintro ⟨ρ, hs, _⟩; exact h ⟨ρ, hs⟩
  · rintro ⟨ρ, hs, _⟩; exact h ⟨ρ, hs⟩

end Trivial

end DeciNSSE.Monitor
