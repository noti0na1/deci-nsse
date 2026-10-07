import DeciNSSE.RejectedTail.Refinement

/-! # Return gaps in the refined reader

Equal refined states at two cuts of a rejected word bound their displacement
by the length of the rejected tail. The predecessor bit excludes a return
across the first rejected cut.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Refinement

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

/-- The return-gap interface used by the support/depth argument. -/
def ReturnGap (M : DFA α Q) (T : Set Q) : Prop :=
  ∀ (w : List α) (J s e : ℕ), M.eval w ∈ T → IsFirstRejectedPrefix M T w J →
    s < e → e ≤ w.length → w.drop e <+: w.drop s →
    M.eval (w.take s) = M.eval (w.take e) → e-s ≤ (w.length-J)-1

/-- Fresh start and the predecessor bit enforce the strict gap. -/
theorem return_gap (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [DecidablePred (· ∈ T)] [h : RejectedPath M R T] :
    ReturnGap (reader M T) (target M T) := by
  intro w J s e hw hJ hse he hp heq
  have hr : M.eval w ∈ T := by
    simpa only [target, Set.mem_ofPred_eq, project_eval] using hw
  have hJ' := (firstRejectedPrefix_iff M T w J).mp hJ
  have hm : (reader M T).eval (w.take (w.length-(e-s))) = (reader M T).eval w := by
    rw [← comparison_cut_eq_take hse he hp]
    exact eval_cut _ heq
  have hmle : w.length-(e-s) ≤ w.length := Nat.sub_le _ _
  have hmlt : w.length-(e-s) < w.length := by omega
  have hwne : w ≠ [] := by intro hz; simp [hz] at he; omega
  have hmpos : 0 < w.length-(e-s) := by
    by_contra hn
    have hz : w.length-(e-s) = 0 := by omega
    have hnone : (reader M T).eval w = none := by
      simpa only [hz, List.take_zero, DFA.eval_nil, reader] using hm.symm
    exact eval_ne_none M T hwne hnone
  have hmJ : J ≤ w.length-(e-s) := by
    by_contra hn
    apply hJ.2.2 (w.length-(e-s)) (by omega)
    simpa only [hm] using hw
  have hstrict : J < w.length-(e-s) := by
    by_contra hn
    have hmJ' : w.length-(e-s) = J := by omega
    have hJpos : 0 < J := by omega
    have hpred : M.eval (w.take (J-1)) ∉ T := hJ'.2.2 (J-1) (by omega)
    have heq' : (reader M T).eval (w.take J) =
        (reader M T).eval (w.take w.length) := by
      simpa only [hmJ', List.take_length] using hm
    have hlast := (equal_predecessors M T hJpos (by omega) hJ'.1 le_rfl heq').mp hpred
    have hreject : M.eval (w.take (w.length-1)) ∈ T :=
      h.between _ _ w (List.take_prefix_take_left (by omega))
        (List.take_prefix _ _) hJ'.2.1 hr
    exact hlast hreject
  omega

end DeciNSSE.RejectedTail
