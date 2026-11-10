import DeciNSSE.Satisfiability.Decide
import DeciNSSE.Satisfiability.VarianceShape

/-! # Satisfiability with variance

A variance system is satisfiable exactly when its signed translation has no label
clash. Every depth bound of the least shapes of the signed translation bounds the
variance shape, so a finite signed solution gives a finite variance solution. Both
kinds of satisfiability are therefore decided by the covariant tests on the signed
translation.

## Main declarations

- `satFin_iff_signed`: the signed translation preserves and reflects finite
  satisfiability.
- `satB`, `satB_iff`, `satB_eq_false_iff`: the executable satisfiability test for every
  variance.
- `satFinB`, `satFinB_iff`, `satFinB_eq_false_iff`: the executable finite satisfiability
  test for every variance.
- `entailsFin_of_not_satFinB`: without finite solutions, finite entailment holds.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- Signed translation preserves and reflects finite satisfiability: without label and
cycle clashes, the variance shape is a solution of bounded depth. -/
theorem satFin_iff_signed (c : Fin n → Bool) (ϕ : Constraint n k) :
    SatisfiableFin c ϕ ↔
      (∃ σ : V (2 * k) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c ϕ)) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun z => FTree.normalize c (sign z) (σ (base z)), ?_⟩
    have he : (FTree.toTree ∘ fun z => FTree.normalize c (sign z) (σ (base z))) =
        normalized c (FTree.toTree ∘ σ) := by
      funext z; simp [normalized]
    rw [he]
    exact (sat_iff_signed c _ ϕ).mp hσ
  · intro hs
    obtain ⟨hl, hc⟩ := satFin_iff.mp hs
    obtain ⟨σ, he⟩ := FTree.exists_eq_of_depth (varianceShape_depth (leastShape_depth hc))
    exact ⟨σ, by rw [he]; exact varianceShape_sat hl⟩

/-- Executable satisfiability for any variance: the signed translation has no label
clash. -/
def satB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool := !labelClashB (signed c ϕ)

/-- The satisfiability test succeeds exactly when a solution exists. -/
theorem satB_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satB c ϕ = true ↔ Satisfiable c ϕ := by
  rw [satisfiable_iff_signed_not_labelClash, satB, Bool.not_eq_true', Bool.eq_false_iff, Ne,
    labelClashB_iff]

/-- The satisfiability test fails exactly when no solution exists. -/
theorem satB_eq_false_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satB c ϕ = false ↔ ¬ Satisfiable c ϕ := by
  rw [← satB_iff, Bool.not_eq_true]

/-- Executable finite satisfiability for any variance: the covariant finite
decision on the signed translation. -/
def satFinB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool := Covariant.satFinB (signed c ϕ)

/-- The finite variance satisfiability test succeeds exactly when a finite solution exists. -/
theorem satFinB_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satFinB c ϕ = true ↔ SatisfiableFin c ϕ :=
  (Covariant.satFinB_iff _).trans (satFin_iff_signed c ϕ).symm

/-- The finite satisfiability test fails exactly when no finite solution exists. -/
theorem satFinB_eq_false_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satFinB c ϕ = false ↔ ¬ SatisfiableFin c ϕ := by
  rw [← satFinB_iff, Bool.not_eq_true]

/-- When the finite satisfiability test fails, every finite entailment holds vacuously. -/
theorem entailsFin_of_not_satFinB {c : Fin n → Bool} {ϕ : Constraint n k}
    (h : satFinB c ϕ = false) (x y : V k) : EntailsFin c ϕ x y :=
  fun σ hσ => absurd ⟨σ, hσ⟩ ((satFinB_eq_false_iff c ϕ).mp h)

end DeciNSSE
