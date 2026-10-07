import Mathlib

/-! # Holes of finite readers

A hole reaches the target set and has no admitted suffix comparison.
A comparison uses cuts `s < e ≤ |w|` with `w.drop e` a prefix of `w.drop s`,
so terminal comparisons are included.
-/

set_option autoImplicit false

namespace DeciNSSE.Holes
open scoped List

section General
variable {α Q : Type*}

/-- The state reached after the first `i` letters. -/
def runPrefix (M : DFA α Q) (w : List α) (i : ℕ) : Q := M.eval (w.take i)

/-- A witnessed pair: a suffix coincidence `w[e:] ⪯ w[s:]` with `s < e`. -/
def WitnessedPair (M : DFA α Q) (w : List α) (p q : Q) : Prop :=
  ∃ s e, s < e ∧ e ≤ w.length ∧ runPrefix M w s = p ∧ runPrefix M w e = q ∧
    w.drop e <+: w.drop s

/-- A hole reaches the target and has no admitted witnessed pair. -/
def IsReaderHole (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) : Prop :=
  runPrefix M w w.length ∈ T ∧ ∀ p q, WitnessedPair M w p q → ¬ R p q

/-- Hole membership is a target condition and absence of admitted comparisons. -/
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

end General

end DeciNSSE.Holes
