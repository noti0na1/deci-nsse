import DeciNSSE.Automata.CapAutomaton
import DeciNSSE.Automata.CapExpr

/-! # Decomposing the periodic language

The periodic part of an automaton language is a union of prefix languages
concatenated with caps of loop languages. This form permits finite-monoid coverage.
-/

namespace DeciNSSE.CapAutomaton

open Words

variable {Q : Type} [Fintype Q] [DecidableEq Q] (P : CapAutomaton Q)

def Pre (q : Q) : Set Word := {w | P.Runs P.init w q}
def Loop (q₁ q₂ : Q) : Set Word := {w | P.Runs q₁ w q₂}

theorem langP_eq : P.LangP = ⋃ q₁, ⋃ q₂,
    {_w : Word | P.pedge q₂ q₁ = true} ∩
      (concat (P.Pre q₁) (Cap (P.Loop q₁ q₂)) : Set Word) := by
  ext w
  simp only [LangP, Set.mem_ofPred_eq, Set.mem_iUnion, Pre, Loop, Cap]
  constructor
  · rintro ⟨π, v, q₁, q₂, μ, rfl, hπ, hμ, he, hv⟩
    exact ⟨q₁, q₂, he, π, hπ, v, ⟨μ, hμ, hv⟩, rfl⟩
  · rintro ⟨q₁, q₂, he, π, hπ, v, ⟨μ, hμ, hv⟩, rfl⟩
    exact ⟨π, v, q₁, q₂, μ, rfl, hπ, hμ, he, hv⟩

end DeciNSSE.CapAutomaton
