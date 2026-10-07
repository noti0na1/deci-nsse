import DeciNSSE.RejectedTail.Basic

/-! # Return gaps of rejected words

Let a word `w` reach the target and let `J` be its first rejected cut. If a
comparison `s < e` joins two cuts with equal reader states, removing the factor
between them leaves the prefix of length `|w| - (e-s)`, which reaches the same
state as `w`. This cut is rejected, so it does not precede `J`, and
`e - s ≤ |w| - J`. The bound holds for every reader.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

variable {α Q : Type*}

theorem comparison_cut_eq_take {w : List α} {s e : ℕ}
    (hse : s < e) (he : e ≤ w.length) (hp : w.drop e <+: w.drop s) :
    (w.take s ++ w.drop e) = w.take (w.length - (e-s)) := by
  have hpre : (w.take s ++ w.drop e) <+: w := by
    have hh := (List.prefix_append_right_inj (w.take s)).mpr hp
    simpa only [List.take_append_drop] using hh
  have hlen : ((w.take s ++ w.drop e)).length = w.length - (e-s) := by
    simp only [List.length_append, List.length_take, List.length_drop]
    omega
  simpa only [hlen] using List.prefix_iff_eq_take.mp hpre

theorem eval_cut (M : DFA α Q) {w : List α} {i j : ℕ}
    (hloop : M.eval (w.take i) = M.eval (w.take j)) :
    M.eval (w.take i ++ w.drop j) = M.eval w := by
  simp only [DFA.eval, DFA.evalFrom_of_append] at *
  rw [hloop, ← DFA.evalFrom_of_append, List.take_append_drop]

/-- A comparison between equal reader states is no longer than the rejected tail. -/
def ReturnGap (M : DFA α Q) (T : Set Q) : Prop :=
  ∀ (w : List α) (J s e : ℕ), M.eval w ∈ T → IsFirstRejectedPrefix M T w J →
    s < e → e ≤ w.length → w.drop e <+: w.drop s →
    M.eval (w.take s) = M.eval (w.take e) → e-s ≤ w.length-J

/-- Every reader has the return gap: cutting out the return leaves a rejected prefix. -/
theorem return_gap (M : DFA α Q) (T : Set Q) : ReturnGap M T := by
  intro w J s e hw hJ hse he hp heq
  have hm : M.eval (w.take (w.length-(e-s))) = M.eval w := by
    rw [← comparison_cut_eq_take hse he hp]
    exact eval_cut M heq
  have hmJ : J ≤ w.length-(e-s) := by
    by_contra hn
    apply hJ.2.2 (w.length-(e-s)) (by omega)
    simpa only [hm] using hw
  omega

end DeciNSSE.RejectedTail
