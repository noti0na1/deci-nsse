import DeciNSSE.Satisfiability.LeastGraph
import DeciNSSE.Transfer.Safety

/-! # Transfer to regular trees

A satisfiable path-witness system has a regular solution. Consequently every
failed unrestricted entailment has a regular counterexample, and regular-tree
entailment coincides with unrestricted entailment.
-/

namespace DeciNSSE

variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {ν : List (Fin 2)}

/-- A satisfiable right mismatch system yields a regular-tree counterexample. -/
theorem not_entailsReg_of_sat_unsafe
    (h : ∃ ρ', Sat ρ' (rUnsafe ϕ x y ν)) : ¬ EntailsReg ϕ x y := by
  obtain ⟨σ, hσ⟩ := sat_regular_of_sat h
  obtain ⟨hϕ, hxy⟩ := Safety.rUnsafe_sound hσ
  intro he
  exact hxy (he (σ ∘ Fin.castAdd _) hϕ)

/-- A satisfiable left mismatch system yields a regular-tree counterexample. -/
theorem not_entailsReg_of_sat_lUnsafe
    (h : ∃ ρ', Sat ρ' (lUnsafe ϕ x y ν)) : ¬ EntailsReg ϕ x y := by
  obtain ⟨σ, hσ⟩ := sat_regular_of_sat h
  obtain ⟨hϕ, hxy⟩ := Safety.lUnsafe_sound hσ
  intro he
  exact hxy (he (σ ∘ Fin.castAdd _) hϕ)

/-- Unrestricted-tree and regular-tree entailment coincide. -/
theorem entails_iff_entailsReg : Entails ϕ x y ↔ EntailsReg ϕ x y := by
  constructor
  · exact Entails.toReg
  · intro h
    by_contra hn
    obtain ⟨ν, hr | hl⟩ := not_entails_iff.mp hn
    · exact not_entailsReg_of_sat_unsafe hr h
    · exact not_entailsReg_of_sat_lUnsafe hl h

/-- A constraint system with no finite solution entails every inequality over finite trees. -/
theorem entailsFin_of_not_satFin
    (h : ¬ ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ) : EntailsFin ϕ x y := by
  intro σ hσ
  exact False.elim (h ⟨σ, hσ⟩)

end DeciNSSE
