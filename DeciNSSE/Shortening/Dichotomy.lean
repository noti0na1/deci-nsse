import DeciNSSE.RejectedTail.Decision

/-! # Periodic continuations and rejected dead ends

## Main declarations

- `hole_dichotomy` selects a short periodic spelling or a finite dead-end hole.
- `short_hole_of_omega` bounds a finite witness in the periodic case.
-/

namespace DeciNSSE.Shortening
open Holes RejectedTail
variable {α Q : Type*} (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)

/-- A dead end is a rejected state all of whose one-letter successors lie outside the target. -/
def DeadEnd (q : Q) : Prop := q ∈ T ∧ ∀ a, M.step q a ∉ T

/-- An omega-hole is an eventually periodic spelling that is eventually always rejected and has
no admitted pair of equal infinite suffixes. -/
def OmegaHole (W : ℕ → α) : Prop :=
  (∃ A d, 0 < d ∧ PeriodicFrom W A d) ∧
  (∃ J, ∀ j ≥ J, M.eval (streamPrefix W j) ∈ T) ∧ NoInfiniteAdmission M R W

/-- Truncate using the first rejected cut. Betweenness makes every later
prefix rejected, even when rejection was given only eventually. -/
private theorem truncate (W : ℕ → α) {A d : ℕ} [rp : RejectedPath M R T]
    (hd : 0 < d) (per : PeriodicFrom W A d) (clear : NoInfiniteAdmission M R W)
    (ev : ∃ j, ∀ k ≥ j, M.eval (streamPrefix W k) ∈ T) :
    ∃ J, (∀ j, M.eval (streamPrefix W j) ∈ T → J ≤ j) ∧
      IsReaderHole M R T (streamPrefix W (A + J + d)) ∧
      ∀ k ≥ J, M.eval (streamPrefix W k) ∈ T := by
  classical
  obtain ⟨j, hj⟩ := ev
  have hit : ∃ t, M.eval (streamPrefix W t) ∈ T := ⟨j, hj j le_rfl⟩
  let J := Nat.find hit
  have first : M.eval (streamPrefix W J) ∈ T := Nat.find_spec hit
  have after (k) (hk : J ≤ k) : M.eval (streamPrefix W k) ∈ T :=
    rp.between _ _ _ (streamPrefix_prefix W hk) (streamPrefix_prefix W (le_max_left k j))
      first (hj _ (le_max_right ..))
  have hJ : IsFirstRejectedPrefix M T (streamPrefix W (A+J+d)) J := by
    refine ⟨by simp; omega, by rwa [streamPrefix_take W (by omega)], ?_⟩
    intro i hi
    rw [streamPrefix_take W (by omega)]
    exact Nat.find_min hit hi
  exact ⟨J, fun _ h => Nat.find_min' hit h,
    (periodic_truncation M R T rp.cone W hd per clear (after _ (by omega)) hJ).1, after⟩

variable [Fintype Q]

/-- From a hole in a closed family of rejected states, select one successor
per state. Ultimately periodic iteration gives a short period. -/
private theorem closed_lasso [RejectedPath M R T] {v : List α} (hv : IsReaderHole M R T v)
    (P : Q → Prop) (start : P (M.eval v)) (reject : ∀ q, P q → q ∈ T)
    (next : ∀ q, P q → ∃ a, P (M.step q a)) :
    ∃ W A d, OmegaHole M R T W ∧ PeriodicFrom W A d ∧
      A ≤ Fintype.card Q ∧ 0 < d ∧ d ≤ Fintype.card Q := by
  classical
  let letter (q : Q) := if h : P q then (next q h).choose else (next _ start).choose
  let f (q : Q) := M.step q (letter q)
  let q (i : ℕ) := f^[i] (M.eval v)
  have step (i : ℕ) : q (i + 1) = f (q i) := Function.iterate_succ_apply' ..
  have inv (i : ℕ) : P (q i) := by
    induction i with
    | zero => exact start
    | succ i ih =>
      rw [step]; simpa [f, letter, ih] using (next _ ih).choose_spec
  let tail (i : ℕ) := letter (q i)
  let W := spliceStream v tail 0
  have run (i : ℕ) : M.eval (streamPrefix W (v.length + i)) = q i := by
    induction i with
    | zero => simp [W, spliceStream_prefix, q]
    | succ i ih =>
      rw [← Nat.add_assoc, streamPrefix_succ, DFA.eval_append_singleton, ih, step]
      congr 1
      simp [W, tail]
  have ev (j) (hj : v.length ≤ j) : M.eval (streamPrefix W j) ∈ T := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [run]; exact reject _ (inv i)
  have clear := extension_noInfiniteAdmission M R T W hv (spliceStream_prefix ..).symm ev
  obtain ⟨m, d, hd, hN, hp⟩ := trajectory_period f q step
  have per : PeriodicFrom W (v.length + m) d := by
    intro k hk
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hk
    simpa only [W, Nat.add_assoc, spliceStream_after, Nat.zero_add, tail]
      using congrArg letter (hp i)
  obtain ⟨A, _, ha, _, hm⟩ := exists_periodicOnset per
  obtain ⟨u, hu, he, hper, hclear⟩ := compress_periodic_prefix M R hd ha clear hm
  refine ⟨_, u.length, d,
    ⟨⟨u.length, d, hd, hper⟩, ⟨u.length + v.length, ?_⟩, hclear⟩,
    hper, hu, hd, hN⟩
  intro k hk
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (show u.length ≤ k by omega)
  rw [spliceStream_eval M he]
  exact ev _ (by omega)

/-- Period boundaries follow one transition on the state set. An eventual
target can thus be reached at a boundary within one state count of periods. -/
private theorem early_periodic_hit (W : ℕ → α) {A d : ℕ} (hd : 0 < d)
    (per : PeriodicFrom W A d) (ev : ∃ j, ∀ k ≥ j, M.eval (streamPrefix W k) ∈ T) :
    ∃ j ≤ A + Fintype.card Q * d, M.eval (streamPrefix W j) ∈ T := by
  let block := streamPrefix (fun i => W (A + i)) d
  let f (q : Q) := M.evalFrom q block
  let q := M.eval (streamPrefix W A)
  have run (k : ℕ) : M.eval (streamPrefix W (A + k*d)) = f^[k] q := by
    induction k with
    | zero => simp [q]
    | succ k ih =>
      rw [Nat.succ_mul, ← Nat.add_assoc, streamPrefix_add]
      change M.evalFrom M.start (_ ++ _) = _
      rw [DFA.evalFrom_of_append]
      change M.evalFrom (M.eval _) _ = _
      rw [ih, Function.iterate_succ_apply']
      congr 1
      change streamPrefix _ d = streamPrefix _ d
      congr 1; funext i
      rw [show A + k * d + i = A + i + k * d by omega]
      exact periodicFrom_mul per (by omega) k
  obtain ⟨k, h⟩ := ev
  have ht := h (A+k*d) (by nlinarith)
  rw [run] at ht
  obtain ⟨i, _, hi, he⟩ := LetteredHierarchy.iterate_small f q k
  exact ⟨A+i*d, Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _, by rwa [run, he]⟩

/-- A rejected-path reader has a hole exactly when it has a dead-end hole or an omega-hole whose
periodic onset and positive period are each at most the state count. -/
theorem hole_dichotomy [RejectedPath M R T] :
    (∃ w, IsReaderHole M R T w) ↔
      (∃ W A d, OmegaHole M R T W ∧ PeriodicFrom W A d ∧
        A ≤ Fintype.card Q ∧ 0 < d ∧ d ≤ Fintype.card Q) ∨
      ∃ w, IsReaderHole M R T w ∧ DeadEnd M T (M.eval w) := by
  classical
  constructor
  · rintro ⟨v,hv⟩
    by_cases dead : ∃ w, IsReaderHole M R T w ∧ DeadEnd M T (M.eval w)
    · exact Or.inr dead
    let P (q : Q) := ∃ w, IsReaderHole M R T w ∧ M.eval w = q
    apply Or.inl (closed_lasso M R T hv P ⟨v,hv,rfl⟩ _ _)
    · rintro _ ⟨w, hw, rfl⟩
      exact ((isReaderHole_iff ..).mp hw).1
    · rintro _ ⟨w, hw, rfl⟩
      have can : ∃ a, M.step (M.eval w) a ∈ T := by
        by_contra! none
        exact dead ⟨w, hw, ((isReaderHole_iff ..).mp hw).1, none⟩
      obtain ⟨a,ha⟩ := can
      have he := M.eval_append_singleton w a
      exact ⟨a, w ++ [a],
        rejected_extension M R T hw (List.prefix_append ..) (he.symm ▸ ha), he⟩
  · rintro (⟨W,A,d,h,per,_,hd,_⟩ | ⟨w,hw,_⟩)
    · obtain ⟨_,_,hh,_⟩ := truncate M R T W hd per h.2.2 h.2.1
      exact ⟨_,hh⟩
    · exact ⟨_,hw⟩

/-- An omega-hole in an `N`-state rejected-path reader yields a finite hole of length at most
`N² + 3N`. -/
theorem short_hole_of_omega [RejectedPath M R T] {W : ℕ → α} (h : OmegaHole M R T W) :
    ∃ w, IsReaderHole M R T w ∧ w.length ≤ Fintype.card Q ^ 2 + 3 * Fintype.card Q := by
  obtain ⟨⟨A,d,hd,per⟩,ev,clear⟩ := h
  obtain ⟨J,_,hole,after⟩ := truncate M R T W hd per clear ev
  let P (q : Q) := ∃ i ≥ J, M.eval (streamPrefix W i) = q
  have closed : ∀ q, P q → ∃ a, P (M.step q a) := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨W i, i+1, by omega, by rw [streamPrefix_succ, DFA.eval_append_singleton]⟩
  obtain ⟨U,a,b,hu,hp,ha,hb,hbN⟩ :=
    closed_lasso M R T hole P ⟨A+J+d, by omega, rfl⟩
      (fun _ ⟨i, hi, he⟩ => he ▸ after i hi) closed
  obtain ⟨j,minJ,hh,_⟩ := truncate M R T U hb hp hu.2.2 hu.2.1
  obtain ⟨i,hi,hit⟩ := early_periodic_hit M T U hb hp hu.2.1
  refine ⟨_,hh,?_⟩
  rw [streamPrefix_length]
  have := minJ _ hit
  have := Nat.mul_le_mul_left (Fintype.card Q) hbN
  nlinarith

end DeciNSSE.Shortening
