import DeciNSSE.Constraints.Dual
import DeciNSSE.Monitor.Clash
import DeciNSSE.Transfer.Safety

/-! # Events and unsafe words

The events of a side are the events of one covariant query: the signed
translation with the query `(x⁺, y⁺)` on the top-prefix side, and its order
dual with the reversed query `(y⁺, x⁺)` on the bottom-prefix side. The unsafe
words of a side are the sign-fixed top-prefix witnesses of its query, hence
exactly the words whose four-spine extension has no label clash. For a
satisfiable system these are the words without events. Satisfiability excludes
clashes inherited from the original constraints; without that hypothesis, the
event-free criterion alone need not give a model.
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

theorem sideSystem_flipClosed (θ : Side) : FlipClosed (sideSystem c ϕ θ) := by
  cases θ
  · exact signed_flipClosed c ϕ
  · exact flipClosed_dual (signed_flipClosed c ϕ)

theorem sideSystem_signCoherent (θ : Side) : SignCoherent c (sideSystem c ϕ θ) := by
  cases θ
  · exact signed_signCoherent c ϕ
  · exact signCoherent_dual (signed_signCoherent c ϕ)

/-- A satisfiable system has no label clash on either side. -/
theorem sideSystem_not_labelClash (hs : ∃ ρ, Sat c ρ ϕ) (θ : Side) :
    ¬ LabelClash (sideSystem c ϕ θ) := by
  obtain ⟨ρ, hρ⟩ := hs
  have h : Covariant.Sat (normalized c ρ) (signed c ϕ) := (sat_iff_signed c ρ ϕ).mp hρ
  cases θ
  · exact fun hc => hc.unsatisfiable ⟨_, h⟩
  · exact fun hc => hc.unsatisfiable (ConstraintDual.satisfiable ⟨_, h⟩)

/-- Variance solutions are the sign-fixed solutions of the signed translation. -/
theorem exists_normalized_iff (P : (V (2 * k) → Tree n) → Prop) :
    (∃ ρ, Sat c ρ ϕ ∧ P (normalized c ρ)) ↔
      ∃ A, Covariant.Sat A (signed c ϕ) ∧ Signed.dual A = A ∧ P A := by
  constructor
  · rintro ⟨ρ, hs, hp⟩
    exact ⟨_, (sat_iff_signed c ρ ϕ).mp hs, normalized_fixed c ρ, hp⟩
  · rintro ⟨A, hA, hfix, hp⟩
    obtain ⟨ρ, hρ, rfl⟩ := (fixed_solution_correspondence c ϕ A).mp ⟨hA, hfix⟩
    exact ⟨ρ, hρ, hp⟩

/-- An unsafe word of a side is a sign-fixed top-prefix witness of its covariant query. -/
theorem sideUnsafe_iff_fixedWitness (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ∃ A, Covariant.Sat A (sideSystem c ϕ θ) ∧ Signed.dual A = A ∧
      covPrefTop w (A (sideQuery x y θ).1) ∧ ¬ covPrefTop w (A (sideQuery x y θ).2) := by
  cases θ
  · simp only [Unsafe, prefTop_iff_normalize, ← normalized_sv]
    exact exists_normalized_iff (fun A => covPrefTop w (A (sv x false)) ∧
      ¬ covPrefTop w (A (sv y false)))
  · simp only [Unsafe, sideSystem, sideQuery, prefBot_iff_normalize, ← normalized_sv]
    refine (exists_normalized_iff (fun A => covPrefBot w (A (sv y false)) ∧
      ¬ covPrefBot w (A (sv x false)))).trans ⟨?_, ?_⟩
    · rintro ⟨A, hA, hfix, hy, hx⟩
      refine ⟨Tree.dual ∘ A, (ConstraintDual.sat A).mpr hA, ?_, by simpa using hy,
        by simpa using hx⟩
      change Tree.dual ∘ Signed.dual A = _
      rw [hfix]
    · rintro ⟨A, hA, hfix, hy, hx⟩
      refine ⟨Tree.dual ∘ A, ConstraintDual.sat_of_dual hA, ?_, by simpa using hy,
        by simpa using hx⟩
      change Tree.dual ∘ Signed.dual A = _
      rw [hfix]

/-- A word is unsafe on a side exactly when the four-spine extension of its
covariant query has no label clash. No satisfiability hypothesis is needed. -/
theorem sideUnsafe_iff_not_labelClash (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ LabelClash
      (Spine.extension c (sideSystem c ϕ θ) (sideQuery x y θ).1 (sideQuery x y θ).2 w) :=
  (sideUnsafe_iff_fixedWitness θ w).trans
    (fixedWitness_iff_not_labelClash (sideSystem_flipClosed θ) (sideSystem_signCoherent θ))

/-- Under satisfiability, the unsafe words of a side are the words without
its events. The right side is the left side of the order dual. -/
theorem sideUnsafe_iff_not_events (hs : ∃ ρ, Sat c ρ ϕ) (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ SideOccurs c ϕ x y θ w := by
  rw [sideUnsafe_iff_not_labelClash, labelClash_extension_iff_occurs (sideSystem_flipClosed θ)
    (sideSystem_signCoherent θ) (sideSystem_not_labelClash hs θ)]
  rfl

end Bridge

end DeciNSSE.Events
