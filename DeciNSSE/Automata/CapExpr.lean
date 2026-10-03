import Mathlib.Computability.Language

/-! # Concatenation of word languages

Language concatenation expresses a path prefix followed by a periodic cap
in the decomposition of automaton acceptance.
-/

namespace DeciNSSE

/-- Concatenation of two binary-word languages. -/
abbrev concat (L₁ L₂ : Language (Fin 2)) : Language (Fin 2) := L₁ * L₂

end DeciNSSE
