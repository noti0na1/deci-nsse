import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra

/-! # Holes of finite readers

A hole reaches the target set and has no admitted suffix comparison.
A comparison uses cuts `s < e ≤ |w|` with `w.drop e` a prefix of `w.drop s`,
so terminal comparisons are included.

## Main declarations

- `runPrefix`: the state after the first `i` letters.
- `CoAlignment.IsComp`: comparisons, including terminal cuts.
- `IsReaderHole`: holes of a reader `(M, R, T)`.
- `isReaderHole_iff`: holes in terms of comparisons.

Reader declarations are in `DeciNSSE.Holes`; comparisons are in `DeciNSSE.CoAlignment`.
-/

namespace DeciNSSE.CoAlignment
open scoped List

/-- A comparison `(s,e)` of `u`: `s < e ≤ |u|` and `u[e:] ⪯ u[s:]`. -/
def IsComp {α : Type*} (u : List α) (s e : ℕ) : Prop :=
  s < e ∧ e ≤ u.length ∧ u.drop e <+: u.drop s

end DeciNSSE.CoAlignment

namespace DeciNSSE.Holes
open scoped List

section General
variable {α Q : Type*}

/-- The state reached after the first `i` letters. -/
def runPrefix (M : DFA α Q) (w : List α) (i : ℕ) : Q := M.eval (w.take i)

/-- A hole reaches the target and has no admitted comparison. -/
def IsReaderHole (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) : Prop :=
  runPrefix M w w.length ∈ T ∧
    ∀ s e, CoAlignment.IsComp w s e → ¬ R (runPrefix M w s) (runPrefix M w e)

/-- Hole membership is a target condition and absence of admitted comparisons. -/
theorem isReaderHole_iff (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) :
    IsReaderHole M R T w ↔ M.eval w ∈ T ∧
      ∀ s e, s < e → e ≤ w.length → w.drop e <+: w.drop s →
        ¬ R (M.eval (w.take s)) (M.eval (w.take e)) := by
  simp only [IsReaderHole, CoAlignment.IsComp, runPrefix, List.take_length, and_imp]

end General

end DeciNSSE.Holes
