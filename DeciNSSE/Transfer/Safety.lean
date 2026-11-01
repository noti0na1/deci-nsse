import DeciNSSE.Constraints.Basic

/-! # Semantic unsafety

An order failure of `x ≤ y` in a valuation is witnessed by a finite word on one of two
sides: on the top-prefix side `x` reaches top along the word and `y` does not; on the
bottom-prefix side `y` reaches bottom and `x` does not. An unsafe word is such a witness
in a satisfying valuation. Entailment holds exactly when neither side has an unsafe word.
Every decision procedure reduces to the search for unsafe words on the two sides.

## Main declarations

- `Side`: the top-prefix side `Side.l` and the bottom-prefix side `Side.r`.
- `Unsafe`: unsafety of a word on a side.
- `entails_iff_not_sideUnsafe`: entailment is the absence of unsafe words.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- The top-prefix and bottom-prefix sides of an order failure of `x ≤ y`. -/
inductive Side
  /-- The top-prefix side: along the word, `x` reaches top and `y` does not. -/
  | l
  /-- The bottom-prefix side: along the word, `y` reaches bottom and `x` does not. -/
  | r
  deriving DecidableEq, Repr

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
