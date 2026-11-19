import DeciNSSE.Complexity.Tiling.Controller

/-! # Execution of the token controller

## Main declarations

- `Controller.read_run` relates register execution to the numbered table.
- `Controller.final_iff` characterizes rejection by a completed parse.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
variable {D : Type*} {t : ℕ} [DecidableEq D] (I : Square D)

/-- A token read by the tiling controller carries a cell letter or a field delimiter. -/
abbrev Letter (D : Type*) := Token (CellLetter D)

/-- Execute the token transitions from a given control on a word, returning the final control if
every transition succeeds. -/
def run (s : Control D) : List (Letter D) → Option (Control D)
  | [] => some s
  | a :: w => (tokenStep I s a).bind fun q => run q w

/-- Execution on a concatenation continues from the control returned by its first word. -/
theorem run_append (s : Control D) (v w : List (Letter D)) :
    run I s (v ++ w) = (run I s v).bind (fun q => run I q w) := by
  induction v generalizing s with
  | nil => rfl
  | cons a v ih => simp [run, ih, Option.bind_assoc]

/-- A successful execution splits at any word boundary into two successful executions with a
common intermediate control. -/
theorem run_split {s r : Control D} {v w : List (Letter D)} :
    run I s (v++w) = some r ↔ ∃ q, run I s v = some q ∧ run I q w = some r := by
  rw [run_append, Option.bind_eq_some_iff]

/-- The enumeration contains the initial control of copy zero. -/
theorem start_mem (e : D ≃ Fin t) : beginPhase D 0 false ∈ (numbering I e).states := by
  simp only [numbering]
  exact (discover_spec (alphabet e) (tokenStep I) (allowance I t) (beginPhase D 0 false)
    (fun _ => True) trivial (by simp)).1

private theorem step_read (e : D ≃ Fin t) (q : Fin (numbering I e).table.size) (a : Letter D) :
    (numbering I e).read ((numbering I e).table.step q a) =
      ((numbering I e).read q).bind (fun s => tokenStep I s a) := by
  let P := numbering I e
  change P.read (P.table.step q a) = (P.read q).bind _
  apply Option.ext
  intro r
  rw [P.read_step, Option.bind_eq_some_iff]
  constructor
  · exact fun ⟨s,hs,_,hr,_⟩ => ⟨s,hs,hr⟩
  · rintro ⟨s,hs,hr⟩
    have hm : s ∈ P.states := by
      have hm : s ∈ P.names := List.mem_of_getElem? hs
      exact P.mem_states_of_mem_names (start_mem I e) hm
    refine ⟨s,hs,?_,hr,P.mem_names (names_closed I e hm hr)⟩
    cases s with
    | none => cases hr
    | some r => rfl

/-- Reading back the numbered state after a word gives the result of executing that word on the
registers. -/
theorem read_run (e : D ≃ Fin t) (w : List (Letter D)) :
    (numbering I e).read ((numbering I e).table.dfa.eval w) = run I (beginPhase D 0 false) w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, run_append]
    change (numbering I e).read ((numbering I e).table.step _ _) = _
    rw [step_read, ih]
    cases run I (beginPhase D 0 false) w <;> simp [run]

/-- A word reaches a numbered target exactly when register execution completes the last packet. -/
theorem final_iff (e : D ≃ Fin t) (w : List (Letter D)) :
    (tokenReader I e).dfa.eval w ∈ (tokenReader I e).target ↔
      run I (beginPhase D 0 false) w = some none := by
  unfold tokenReader
  rw [Numbering.target_iff]
  change (∃ s, (numbering I e).read ((numbering I e).table.dfa.eval w) = some s ∧
      s.isNone = true) ↔ _
  rw [read_run]
  simp

/-- Two runs reach an admitted pair exactly when both return live registers satisfying the token
admission test. -/
theorem pair_iff (e : D ≃ Fin t) (a b : List (Letter D)) :
    ((tokenReader I e).dfa.eval a,(tokenReader I e).dfa.eval b) ∈ (tokenReader I e).pairs ↔
      ∃ r s, run I (beginPhase D 0 false) a = some (some r) ∧
        run I (beginPhase D 0 false) b = some (some s) ∧
        tokenAdmission (2*I.p) (some r) (some s) = true := by
  let P := numbering I e
  change (P.table.dfa.eval a,P.table.dfa.eval b) ∈ P.table.pairs ↔ _
  have irr (q) : P.rel q q = false := by cases q <;> simp [P,numbering,tokenAdmission]
  rw [P.pair_iff irr]
  change (∃ r s, (numbering I e).read ((numbering I e).table.dfa.eval a) = some r ∧
    (numbering I e).read ((numbering I e).table.dfa.eval b) = some s ∧
      tokenAdmission _ r s = true) ↔ _
  rw [read_run, read_run]
  constructor
  · rintro ⟨(_ | r),(_ | s),hr,hs,h⟩ <;> first | cases h | exact ⟨r,s,hr,hs,h⟩
  · exact fun ⟨r,s,hr,hs,h⟩ => ⟨some r,some s,hr,hs,h⟩

end DeciNSSE.Complexity.Tiling.Controller
