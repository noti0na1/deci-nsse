import DeciNSSE.Satisfiability.Decide
import DeciNSSE.Semantics.Selector

/-! # Finite satisfiability with variance

The polarity selector converts a finite signed solution to a finite variance
solution. Finite satisfiability is therefore decided by the covariant test
on the signed translation.
-/

namespace DeciNSSE.FiniteVariance

variable {n k : ℕ}

/-- The selector applied to the least shape `B` of `signed c ϕ`. -/
noncomputable def selectedShape (c : Fin n → Bool) (ϕ : Constraint n k) :
    V (2 * k) → Tree n :=
  select c (leastShape (signed c ϕ)) (leastShape_sameShape_dual (signed_flipClosed c ϕ))

/-- Without a signed label clash, the selected least shape satisfies the signed system. -/
theorem selectedShape_sat {c : Fin n → Bool} {ϕ : Constraint n k}
    (hl : ¬ LabelClash (signed c ϕ)) : Covariant.Sat (selectedShape c ϕ) (signed c ϕ) :=
  select_sat (leastShape_sat hl) _

/-- The selected least shape is fixed by sign duality. -/
theorem selectedShape_fixed (c : Fin n → Bool) (ϕ : Constraint n k) :
    Signed.dual (selectedShape c ϕ) = selectedShape c ϕ := select_fixed _ _ _

@[simp] theorem selectedShape_domain (c : Fin n → Bool) (ϕ : Constraint n k)
    (z : V (2 * k)) (π : List (Fin n)) :
    ((selectedShape c ϕ z).fn π).isSome = ((leastShape (signed c ϕ) z).fn π).isSome :=
  select_domain _ _ _ _ _

/-- Without signed cycle clashes, the selector has the bounded depth of the least shape. -/
theorem selectedShape_depth {c : Fin n → Bool} {ϕ : Constraint n k}
    (hc : ¬ CycleClash (signed c ϕ)) (z : V (2 * k)) (π : List (Fin n))
    (hπ : ((selectedShape c ϕ z).fn π).isSome) : π.length ≤ (2 * k) * (2 * k) + 1 :=
  select_depth c _ _ (leastShape_depth hc) z π hπ

/-- Without a signed label clash, the decoded selector solves the source system. -/
theorem decoded_selectedShape_sat {c : Fin n → Bool} {ϕ : Constraint n k}
    (hl : ¬ LabelClash (signed c ϕ)) : Sat c (decoded c (selectedShape c ϕ)) ϕ := by
  apply (sat_iff_signed c _ ϕ).mpr
  rw [normalized_decoded c (selectedShape_fixed c ϕ)]
  exact selectedShape_sat hl

/-- A finite signed solution yields the specified, bounded source solution. -/
theorem finite_selected_solution {c : Fin n → Bool} {ϕ : Constraint n k}
    (hs : ∃ σ : V (2 * k) → FTree n, Covariant.Sat (FTree.toTree ∘ σ) (signed c ϕ)) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      FTree.toTree ∘ σ = decoded c (selectedShape c ϕ) := by
  obtain ⟨hl, hc⟩ := satFin_iff.mp hs
  have hρ := decoded_selectedShape_sat hl
  have hd (u : V k) : ∀ π, ((decoded c (selectedShape c ϕ) u).fn π).isSome →
      π.length ≤ (2 * k) * (2 * k) + 1 := by
    intro π hπ
    apply selectedShape_depth hc (sv u false) π
    simpa [decoded] using hπ
  obtain ⟨σ, he⟩ := FTree.exists_eq_of_depth hd
  exact ⟨σ, by rw [he]; exact hρ, he⟩

end DeciNSSE.FiniteVariance

namespace DeciNSSE

open FiniteVariance

variable {n k : ℕ}

/-- Satisfiability is preserved and reflected by the signed translation: a
signed solution has no label clash, so the selected least shape decodes to a
variance solution. -/
theorem sat_iff_signed_sat (c : Fin n → Bool) (ϕ : Constraint n k) :
    (∃ ρ, Sat c ρ ϕ) ↔ ∃ A, Covariant.Sat A (signed c ϕ) :=
  ⟨sat_implies_signed_sat c ϕ,
    fun h => ⟨_, decoded_selectedShape_sat (fun hc => hc.unsatisfiable h)⟩⟩

/-- Signed translation preserves and reflects finite satisfiability. -/
theorem satFin_iff_signed (c : Fin n → Bool) (ϕ : Constraint n k) :
    (∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ) ↔
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
    obtain ⟨σ, hσ, _⟩ := finite_selected_solution hs
    exact ⟨σ, hσ⟩

/-- Executable finite satisfiability for any variance: the covariant finite
decision on the signed translation. -/
def satFinB (c : Fin n → Bool) (ϕ : Constraint n k) : Bool := Covariant.satFinB (signed c ϕ)

/-- The finite variance satisfiability test succeeds exactly when a finite solution exists. -/
theorem satFinB_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satFinB c ϕ = true ↔ ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ :=
  (Covariant.satFinB_iff _).trans (satFin_iff_signed c ϕ).symm

/-- The finite satisfiability test fails exactly when no finite solution exists. -/
theorem satFinB_eq_false_iff (c : Fin n → Bool) (ϕ : Constraint n k) :
    satFinB c ϕ = false ↔
      ¬ ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ := by
  rw [← satFinB_iff, Bool.not_eq_true]

/-- Rejection makes every finite entailment hold vacuously. -/
theorem entailsFin_of_not_satFinB {c : Fin n → Bool} {ϕ : Constraint n k}
    (h : satFinB c ϕ = false) (x y : V k) : EntailsFin c ϕ x y :=
  fun σ hσ => absurd ⟨σ, hσ⟩ ((satFinB_eq_false_iff c ϕ).mp h)

end DeciNSSE
