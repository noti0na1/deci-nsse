import DeciNSSE.RejectedTail.Basic

/-! # Predecessor refinement of a reader

A refined state records the current state and whether its predecessor was
accepted; a separate start state represents the empty prefix. The reader has
`2*N + 1` states and preserves holes word by word. Equal positive refined states
have equally accepted predecessors, which makes the return-gap argument apply.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail.Refinement
open Holes RejectedTail
variable {α Q : Type*}

/-- A current reader state with its predecessor bit, or the distinguished start. -/
abbrev State (Q : Type*) := Option (Q × Bool)

/-- Forget the predecessor bit and recover the original state. -/
def project (M : DFA α Q) : State Q → Q
  | none => M.start
  | some (q, _) => q

/-- Record the current state and whether the preceding prefix was accepted. -/
def reader (M : DFA α Q) (T : Set Q) [DecidablePred (· ∈ T)] :
    DFA α (State Q) where
  start := none
  step q a := some (M.step (project M q) a, decide (project M q ∉ T))
  accept := ∅

/-- Pull back admissions along the projection to the original reader. -/
def relation (M : DFA α Q) (R : Q → Q → Prop) : State Q → State Q → Prop :=
  fun p q => R (project M p) (project M q)

/-- Pull back the rejected target along the projection. -/
def target (M : DFA α Q) (T : Set Q) : Set (State Q) :=
  {q | project M q ∈ T}

variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
variable [DecidablePred (· ∈ T)]

@[simp] theorem project_eval (w : List α) :
    project M ((reader M T).eval w) = M.eval w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    simp only [DFA.eval_append_singleton]
    change M.step (project M ((reader M T).eval w)) a = _
    rw [ih]

@[simp] theorem eval_append (w : List α) (a : α) :
    (reader M T).eval (w ++ [a]) = some (M.eval (w ++ [a]), decide (M.eval w ∉ T)) := by
  rw [DFA.eval_append_singleton]
  change some (M.step (project M ((reader M T).eval w)) a,
    decide (project M ((reader M T).eval w) ∉ T)) = _
  rw [project_eval, DFA.eval_append_singleton]

theorem eval_ne_none {w : List α} (hw : w ≠ []) : (reader M T).eval w ≠ none := by
  induction w using List.reverseRecOn with
  | nil => exact (hw rfl).elim
  | append_singleton w a _ => simp only [eval_append, ne_eq, reduceCtorEq, not_false_eq_true]

@[simp] theorem firstRejectedPrefix_iff (w : List α) (J : ℕ) :
    IsFirstRejectedPrefix (reader M T) (target M T) w J ↔ IsFirstRejectedPrefix M T w J := by
  simp only [IsFirstRejectedPrefix, target, Set.mem_ofPred_eq, project_eval]

/-- Exact wordwise preservation includes the empty word and terminal cuts. -/
@[simp] theorem hole_iff (w : List α) :
    IsReaderHole (reader M T) (relation M R) (target M T) w ↔ IsReaderHole M R T w := by
  simp only [Holes.isReaderHole_iff, target, relation, Set.mem_ofPred_eq, project_eval]

/-- Equal positive refined states have equally accepted predecessor prefixes. -/
theorem equal_predecessors {w : List α} {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hil : i ≤ w.length) (hjl : j ≤ w.length)
    (heq : (reader M T).eval (w.take i) = (reader M T).eval (w.take j)) :
    M.eval (w.take (i-1)) ∉ T ↔ M.eval (w.take (j-1)) ∉ T := by
  have hie : w.take i = w.take (i-1) ++ [w[i-1]] := by
    simpa only [Nat.sub_add_cancel hi] using
      (List.take_succ_eq_append_getElem (l := w) (by omega : i-1 < w.length))
  have hje : w.take j = w.take (j-1) ++ [w[j-1]] := by
    simpa only [Nat.sub_add_cancel hj] using
      (List.take_succ_eq_append_getElem (l := w) (by omega : j-1 < w.length))
  rw [hie, hje, eval_append, eval_append] at heq
  have hb := congrArg Prod.snd (Option.some.inj heq)
  simpa only [decide_eq_decide] using hb

end DeciNSSE.RejectedTail.Refinement
