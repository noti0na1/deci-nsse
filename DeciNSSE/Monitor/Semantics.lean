import DeciNSSE.Constraints.Dual
import DeciNSSE.Monitor.Events
import DeciNSSE.Transfer.Safety
import DeciNSSE.Transfer.ThreeSpine

/-! # Events and unsafe words

For a satisfiable system, unsafe words are exactly those without events.
Satisfiability excludes clashes inherited from the original constraints;
without that hypothesis, the event-free criterion alone need not give a model.
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

@[simp] theorem eqBot_mem_dual {K : ℕ} {φ : Constraint n K} {v : V K} :
    Lit.eqBot v ∈ Constraint.dual φ ↔ Lit.eqTop v ∈ φ :=
  ConstraintDual.lit_mem (Lit.eqTop v)

@[simp] theorem eqTop_mem_dual {K : ℕ} {φ : Constraint n K} {v : V K} :
    Lit.eqTop v ∈ Constraint.dual φ ↔ Lit.eqBot v ∈ φ :=
  ConstraintDual.lit_mem (Lit.eqBot v)

@[simp] theorem leF_mem_dual {K : ℕ} {φ : Constraint n K} {v : V K} {b : Fin n → V K} :
    Lit.leF v b ∈ Constraint.dual φ ↔ Lit.fLe b v ∈ φ :=
  ConstraintDual.lit_mem (Lit.fLe b v)

@[simp] theorem uSet_dual {K : ℕ} (φ : Constraint n K) (Z : V K) (w : List (Fin n)) (j : ℕ) :
    USet (Constraint.dual φ) Z w j = LSet φ Z w j := by
  ext v; exact ConstraintDual.upper_iff

@[simp] theorem lSet_dual {K : ℕ} (φ : Constraint n K) (Z : V K) (w : List (Fin n)) (j : ℕ) :
    LSet (Constraint.dual φ) Z w j = USet φ Z w j := by
  ext v; exact ConstraintDual.lower_iff

end Dual

section Events

variable (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- A left event occurs in the signed translation of the query. -/
def leftOccurs (w : List (Fin n)) : Prop := Occurs (signed c ϕ) (sv x false) (sv y false) w

/-- Right events: the left events of the order dual with the query reversed. -/
def rightOccurs (w : List (Fin n)) : Prop :=
  Occurs (Constraint.dual (signed c ϕ)) (sv y false) (sv x false) w

/-- The events of side `θ`. -/
def SideOccurs : Side → List (Fin n) → Prop
  | .l, w => leftOccurs c ϕ x y w
  | .r, w => rightOccurs c ϕ x y w

/-- The events of side `θ`, computably. -/
def eventsB : Side → List (Fin n) → Bool
  | .l, w => occursB (signed c ϕ) (sv x false) (sv y false) w
  | .r, w => occursB (Constraint.dual (signed c ϕ)) (sv y false) (sv x false) w

variable {c ϕ x y}

/-- The Boolean side test decides the semantic event predicate. -/
theorem eventsB_iff (θ : Side) (w : List (Fin n)) :
    eventsB c ϕ x y θ w = true ↔ SideOccurs c ϕ x y θ w := by
  cases θ <;> exact occursB_iff

instance (θ : Side) (w : List (Fin n)) : Decidable (SideOccurs c ϕ x y θ w) :=
  decidable_of_iff _ (eventsB_iff θ w)

end Events

section Bridge

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- The left side bridge. -/
theorem sideUnsafe_l_iff (hs : ∃ ρ, Sat c ρ ϕ) (w : List (Fin n)) :
    Unsafe c ϕ x y .l w ↔ ¬ leftOccurs c ϕ x y w := by
  have h := three_spine_iff_not_events (w := w) (X := sv x false) (Y := sv y false)
    (signed_flipClosed c ϕ) (signed_signCoherent c ϕ) ((sat_iff_signed_sat c ϕ).mp hs)
  simp only [flipV_sv, Bool.not_false] at h
  exact (leftUnsafe_iff_threeSpine c ϕ x y w).trans h

/-- The right side bridge, by order duality. -/
theorem sideUnsafe_r_iff (hs : ∃ ρ, Sat c ρ ϕ) (w : List (Fin n)) :
    Unsafe c ϕ x y .r w ↔ ¬ rightOccurs c ϕ x y w := by
  have h := three_spine_iff_not_events (w := w) (X := sv y false) (Y := sv x false)
    (flipClosed_dual (signed_flipClosed c ϕ)) (signCoherent_dual (signed_signCoherent c ϕ))
    (ConstraintDual.satisfiable ((sat_iff_signed_sat c ϕ).mp hs))
  simp only [flipV_sv, Bool.not_false] at h
  refine (rightUnsafe_iff_threeSpine c ϕ x y w).trans (Iff.trans ?_ h)
  constructor
  · rintro ⟨A, hA, h₁, h₂, h₃⟩
    exact ⟨Tree.dual ∘ A, (ConstraintDual.sat A).mpr hA, (covPrefTop_dual w _).mpr h₁,
      (covPrefBot_dual w _).mpr h₂, fun h => h₃ ((covPrefTop_dual w _).mp h)⟩
  · rintro ⟨A, hA, h₁, h₂, h₃⟩
    exact ⟨Tree.dual ∘ A, ConstraintDual.sat_of_dual hA, (covPrefBot_dual w _).mpr h₁,
      (covPrefTop_dual w _).mpr h₂, fun h => h₃ ((covPrefBot_dual w _).mp h)⟩

theorem sideUnsafe_iff_not_events (hs : ∃ ρ, Sat c ρ ϕ) (θ : Side)
    (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ SideOccurs c ϕ x y θ w := by
  cases θ
  · exact sideUnsafe_l_iff hs w
  · exact sideUnsafe_r_iff hs w

end Bridge

end DeciNSSE.Events
