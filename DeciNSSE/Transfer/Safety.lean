import DeciNSSE.Constraints.Basic

/-! # Semantic unsafety

An unsafe word is a finite top- or bottom-prefix witness in a satisfying
valuation. Entailment holds exactly when neither side has such a witness.
-/

section

namespace DeciNSSE

/-- The top-prefix and bottom-prefix sides of an order failure. -/
inductive Side | l | r
  deriving DecidableEq, Repr

end DeciNSSE

end

section

namespace DeciNSSE

variable {n m k : ℕ}

/-- Unsafety of a word on a side, for solutions of variance `c` and the query `x ≤ y`. -/
def Unsafe (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Side → List (Fin n) → Prop
  | .l, w => ∃ ρ, Sat c ρ ϕ ∧ prefTop c w (ρ x) ∧ ¬ prefTop c w (ρ y)
  | .r, w => ∃ ρ, Sat c ρ ϕ ∧ prefBot c w (ρ y) ∧ ¬ prefBot c w (ρ x)

/-- Entailment holds iff no word is unsafe on either side. -/
theorem entails_iff_not_sideUnsafe (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Entails c ϕ x y ↔ ∀ θ w, ¬ Unsafe c ϕ x y θ w := by
  rw [entails_iff_safe]
  constructor
  · intro h θ w
    cases θ
    · rintro ⟨ρ, hs, ht, hn⟩; exact hn ((h w ρ hs).1 ht)
    · rintro ⟨ρ, hs, hb, hn⟩; exact hn ((h w ρ hs).2 hb)
  · intro h w ρ hs
    refine ⟨fun ht => ?_, fun hb => ?_⟩
    · by_contra hn; exact h .l w ⟨ρ, hs, ht, hn⟩
    · by_contra hn; exact h .r w ⟨ρ, hs, hb, hn⟩

end DeciNSSE

end
