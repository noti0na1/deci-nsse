import Mathlib.Computability.DFA
import DeciNSSE.Words

/-! # Comparisons and holes of finite automata

A comparison has positions s < e whose suffixes satisfy drop e ≤prefix drop s.
It witnesses the pair of states at those positions. A hole reaches a target
state and witnesses no admitted pair. Both binary and arbitrary alphabets
are treated independently of the constraint semantics.
-/

namespace DeciNSSE.Holes
open Words

variable {Q : Type*}

/-- The state reached after the first `i` letters of a binary word. -/
def run (M : DFA (Fin 2) Q) (w : Word) (i : ℕ) : Q := M.eval (w.take i)

/-- A pair of states occurs at a comparison `s < e` with `w.drop e` a prefix of `w.drop s`. -/
def Witnessed (M : DFA (Fin 2) Q) (w : Word) (p q : Q) : Prop :=
  ∃ s e, s < e ∧ e ≤ w.length ∧ run M w s = p ∧ run M w e = q ∧
    w.drop e <+: w.drop s

/-- A word reaches the target set and witnesses no admitted pair of states. -/
def AbsHole (M : DFA (Fin 2) Q) (R : Q → Q → Prop) (T : Set Q) (w : Word) : Prop :=
  run M w w.length ∈ T ∧ ∀ p q, Witnessed M w p q → ¬ R p q

variable {α : Type*}

/-- The state reached after a prefix over an arbitrary alphabet. -/
def runG (M : DFA α Q) (w : List α) (i : ℕ) : Q := M.eval (w.take i)

/-- A pair of states is witnessed by a suffix-prefix comparison over an arbitrary alphabet. -/
def WitnessedG (M : DFA α Q) (w : List α) (p q : Q) : Prop :=
  ∃ s e, s < e ∧ e ≤ w.length ∧ runG M w s = p ∧ runG M w e = q ∧
    w.drop e <+: w.drop s

/-- A target-reaching word over an arbitrary alphabet with no admitted comparison. -/
def AbsHoleG (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) : Prop :=
  runG M w w.length ∈ T ∧ ∀ p q, WitnessedG M w p q → ¬ R p q

/-- The general and binary definitions of a hole agree on binary words. -/
theorem absHoleG_iff_absHole (M : DFA (Fin 2) Q) (R : Q → Q → Prop) (T : Set Q)
    (w : Word) : AbsHoleG M R T w ↔ AbsHole M R T w := Iff.rfl

end DeciNSSE.Holes
