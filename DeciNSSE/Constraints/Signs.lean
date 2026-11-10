import DeciNSSE.Satisfiability.VarianceShape

/-! # Sign coherence of path bounds

Closure preserves variable signs in a sign-coherent system. Upper and lower
path judgments change sign by exactly the accumulated path polarity.

## Main declarations

- `Signs.derives_sign`: closure preserves signs.
- `Signs.upperAt_sign`, `Signs.lowerAt_sign`: path judgments shift the sign by the
  polarity of the path.
-/

namespace DeciNSSE.Signs

open SignDuality

variable {n k : ℕ}

section Coherent

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)}

/-- The closure of a sign-coherent system never changes sign. -/
theorem derives_sign (hψ : SignCoherent c ψ) {u v : V (2 * k)} (h : Derives ψ u v) :
    sign u = sign v := by
  induction h with
  | refl => rfl
  | trans _ _ h₁ h₂ => exact h₁.trans h₂
  | decomp i hl _ hu ih => rw [hψ.2 _ _ hl i, hψ.1 _ _ hu i, ih]

/-- An upper path judgment shifts the sign by the polarity of the path. -/
theorem upperAt_sign (hψ : SignCoherent c ψ) {π : List (Fin n)} {u v : V (2 * k)}
    (h : UpperAt ψ π u v) : sign v = Bool.xor (sign u) (polarity c π) := by
  induction h with
  | nil hd => simp [derives_sign hψ hd]
  | cons hd hl _ ih =>
    rw [ih, hψ.1 _ _ hl, ← derives_sign hψ hd, polarity_cons, Bool.xor_assoc]

/-- A lower path judgment shifts the sign by the polarity of the path. -/
theorem lowerAt_sign (hψ : SignCoherent c ψ) {π : List (Fin n)} {u v : V (2 * k)}
    (h : LowerAt ψ π u v) : sign v = Bool.xor (sign u) (polarity c π) := by
  induction h with
  | nil hd => simp [derives_sign hψ hd]
  | @cons a z y x π i hl hd _ ih =>
    have h1 := hψ.2 _ _ hl i
    have h2 := derives_sign hψ hd
    rw [polarity_cons]
    revert ih h1 h2
    generalize sign (a i) = A
    generalize sign z = Z
    generalize sign y = Y
    generalize sign x = X
    generalize c i = C
    generalize polarity c π = P
    revert A Z Y X C P
    decide

end Coherent

end DeciNSSE.Signs
