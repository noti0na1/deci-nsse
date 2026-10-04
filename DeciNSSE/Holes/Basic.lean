import Mathlib.Computability.DFA
import DeciNSSE.Words

/-! # Comparisons and holes of finite automata

A comparison consists of positions `s < e ≤ w.length` such that `w.drop e`
is a prefix of `w.drop s`. Equivalently, the suffix at `s` has period `e - s`.
It witnesses the reader states at its endpoints. A hole reaches a target state
and has no comparison whose endpoint states satisfy the admission relation.
The definitions apply to any alphabet, including the binary path alphabet.
-/

namespace DeciNSSE.Holes
variable {α Q : Type*}

/-- The state reached after the first `i` letters, or after the whole word if `i ≥ w.length`. -/
def runPrefix (M : DFA α Q) (w : List α) (i : ℕ) : Q := M.eval (w.take i)

/-- A comparison witnesses the reader states at its two endpoints. -/
def WitnessedPair (M : DFA α Q) (w : List α) (p q : Q) : Prop :=
  ∃ s e, s < e ∧ e ≤ w.length ∧ runPrefix M w s = p ∧ runPrefix M w e = q ∧
    w.drop e <+: w.drop s

/-- A word reaching the target set with no admitted comparison. -/
def IsReaderHole (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) : Prop :=
  runPrefix M w w.length ∈ T ∧ ∀ p q, WitnessedPair M w p q → ¬ R p q

/-- Hole membership is a target condition together with absence of admitted comparisons. -/
theorem isReaderHole_iff (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) :
    IsReaderHole M R T w ↔ M.eval w ∈ T ∧
      ∀ s e, s < e → e ≤ w.length → w.drop e <+: w.drop s →
        ¬ R (M.eval (w.take s)) (M.eval (w.take e)) := by
  constructor
  · rintro ⟨ht, hn⟩
    refine ⟨by simpa [runPrefix] using ht, ?_⟩
    intro s e hse he hp
    exact hn _ _ ⟨s, e, hse, he, rfl, rfl, hp⟩
  · rintro ⟨ht, hn⟩
    refine ⟨by simpa [runPrefix] using ht, ?_⟩
    rintro p q ⟨s, e, hse, he, rfl, rfl, hp⟩
    exact hn s e hse he hp

end DeciNSSE.Holes
