import DeciNSSE.Constraints.Dual
import DeciNSSE.Monitor.Events
import DeciNSSE.Transfer.Safety
import DeciNSSE.Transfer.ThreeSpine

/-! # Events and unsafe words

The events of a side are the events of one covariant query: the signed
translation with the query `(x⁺, y⁺)` on the top-prefix side, and its order
dual with the reversed query `(y⁺, x⁺)` on the bottom-prefix side. For a
satisfiable system, the unsafe words of a side are exactly those without its
events. Satisfiability excludes clashes inherited from the original
constraints; without that hypothesis, the event-free criterion alone need not
give a model.
-/

namespace DeciNSSE.Events

open Spine.Closure

open FiniteVariance

variable {n k : ℕ}

section Dual

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)}

theorem flipClosed_dual (hf : FlipClosed ψ) : FlipClosed (Constraint.dual ψ) := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  have h : dualFlip (ConstraintDual.lit m) = ConstraintDual.lit (dualFlip m) := by cases m <;> rfl
  rw [h]
  exact (ConstraintDual.lit_mem _).mpr (hf m hm)

theorem signCoherent_dual (hc : SignCoherent c ψ) :
    SignCoherent c (Constraint.dual ψ) :=
  ⟨fun u a h i => hc.2 a u ((ConstraintDual.lit_mem (Lit.fLe a u)).mp h) i,
    fun a u h i => hc.1 u a ((ConstraintDual.lit_mem (Lit.leF u a)).mp h) i⟩

end Dual

section Events

variable (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- The covariant system read on side `θ`: the signed translation on the left
and its order dual on the right. -/
def sideSystem : Side → Constraint n (2 * k)
  | .l => signed c ϕ
  | .r => Constraint.dual (signed c ϕ)

/-- The query read on side `θ`: `(x⁺, y⁺)` on the left, reversed on the right. -/
def sideQuery : Side → V (2 * k) × V (2 * k)
  | .l => (sv x false, sv y false)
  | .r => (sv y false, sv x false)

/-- The events of side `θ`: the events of its covariant system and query. -/
def SideOccurs (θ : Side) (w : List (Fin n)) : Prop :=
  Occurs (sideSystem c ϕ θ) (sideQuery x y θ).1 (sideQuery x y θ).2 w

end Events

section Bridge

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- Under satisfiability, the unsafe words of a side are the words without
its events. The right side is the left side of the order dual. -/
theorem sideUnsafe_iff_not_events (hs : ∃ ρ, Sat c ρ ϕ) (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ SideOccurs c ϕ x y θ w := by
  have hs' := (sat_iff_signed_sat c ϕ).mp hs
  cases θ
  · have h := three_spine_iff_not_events (w := w) (X := sv x false) (Y := sv y false)
      (signed_flipClosed c ϕ) (signed_signCoherent c ϕ) hs'
    simp only [flipV_sv, Bool.not_false] at h
    exact (leftUnsafe_iff_threeSpine c ϕ x y w).trans h
  · have h := three_spine_iff_not_events (w := w) (X := sv y false) (Y := sv x false)
      (flipClosed_dual (signed_flipClosed c ϕ)) (signCoherent_dual (signed_signCoherent c ϕ))
      (ConstraintDual.satisfiable hs')
    simp only [flipV_sv, Bool.not_false] at h
    refine (rightUnsafe_iff_threeSpine c ϕ x y w).trans (Iff.trans ?_ h)
    constructor
    · rintro ⟨A, hA, h₁, h₂, h₃⟩
      exact ⟨Tree.dual ∘ A, (ConstraintDual.sat A).mpr hA, (covPrefTop_dual w _).mpr h₁,
        (covPrefBot_dual w _).mpr h₂, fun h => h₃ ((covPrefTop_dual w _).mp h)⟩
    · rintro ⟨A, hA, h₁, h₂, h₃⟩
      exact ⟨Tree.dual ∘ A, ConstraintDual.sat_of_dual hA, (covPrefBot_dual w _).mpr h₁,
        (covPrefTop_dual w _).mpr h₂, fun h => h₃ ((covPrefBot_dual w _).mp h)⟩

end Bridge

end DeciNSSE.Events
