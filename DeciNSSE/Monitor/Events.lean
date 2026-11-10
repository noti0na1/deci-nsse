import DeciNSSE.Satisfiability.VarianceShape

/-! # Readiness and periodic admission events

The events of a covariant query `ψ ⊨? X ≤ Y` along a word are stated on the upper
path bounds of `X` and the lower path bounds of `Y` at the cuts of the word.
Readiness is tested at every cut, including zero and the terminal cut. The
child test is letter-free and remains meaningful at the terminal cut and at
arity zero. Self-admission allows both orientations of sign-flipped labels;
sign coherence relates these events to the spine clash formulas.

## Main declarations

- `Events.ReadyAt`, `Events.ChildAt`: readiness and the child condition along a path.
- `Events.Occurs`: a readiness, terminal child, cross or self event along a word.
-/

namespace DeciNSSE.Events

open SignDuality

variable {n K k : ℕ}

/-- Readiness along a path: an upper bound of `X` is bottom, a lower bound of `Y` is
top, or an upper bound of `X` is a lower bound of `Y`. -/
def ReadyAt (ψ : Constraint n K) (X Y : V K) (π : List (Fin n)) : Prop :=
  (∃ v, UpperAt ψ π X v ∧ Lit.eqBot v ∈ ψ) ∨ (∃ v, LowerAt ψ π v Y ∧ Lit.eqTop v ∈ ψ) ∨
    ∃ v, UpperAt ψ π X v ∧ LowerAt ψ π v Y

/-- The letter-free child condition along a path: an upper bound of `X` carries an
upper constructor literal. -/
def ChildAt (ψ : Constraint n K) (X : V K) (π : List (Fin n)) : Prop :=
  ∃ v, UpperAt ψ π X v ∧ ∃ b, Lit.leF v b ∈ ψ

/-- An event occurs along the word: readiness at a cut, the child condition at the end,
or a comparison `(s, e)` with a cross admission (a lower bound of `Y` at `s` is an upper
bound of `X` at `e`) or a self admission (an upper bound of `X` at `s` is the sign flip
of one at `e`). -/
def Occurs (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) : Prop :=
  (∃ j ≤ w.length, ReadyAt ψ X Y (w.take j)) ∨ ChildAt ψ X w ∨
    ∃ s e, s < e ∧ e ≤ w.length ∧ w.drop e <+: w.drop s ∧
      ((∃ v, LowerAt ψ (w.take s) v Y ∧ UpperAt ψ (w.take e) X v) ∨
        ∃ v, UpperAt ψ (w.take s) X v ∧ UpperAt ψ (w.take e) X (flipV v))

section Words

variable {w : List (Fin n)}

theorem prefix_of_take_eq {a b d : ℕ} (ha : a + d = w.length)
    (h : (w.drop a).take d = (w.drop b).take d) : w.drop a <+: w.drop b := by
  have hl : (w.drop a).take d = w.drop a := List.take_of_length_le (by simp; omega)
  rw [← hl, h]
  exact List.take_prefix _ _

theorem take_eq_of_prefix {s e : ℕ} (h : w.drop e <+: w.drop s) :
    (w.drop e).take (w.length - e) = (w.drop s).take (w.length - e) := by
  have h1 : (w.drop e).take (w.length - e) = w.drop e := List.take_of_length_le (by simp)
  rw [h1]
  have h2 := List.prefix_iff_eq_take.mp h
  rw [List.length_drop] at h2
  exact h2

end Words

end DeciNSSE.Events
