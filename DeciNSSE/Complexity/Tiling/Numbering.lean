import DeciNSSE.Complexity.Tiling.Enumeration

/-! # Runs of a numbered table

## Main declarations

- `Numbering.read_step` characterizes a successful transition on control states.
- `Numbering.target_iff` and `Numbering.pair_iff` transport targets and admissions.
-/

namespace DeciNSSE.Complexity.Tiling
variable {α σ : Type*}

/-- A finite list of control states, partial transitions, targets and admissions specifies a
numbered stopping table with an extra sink. -/
structure Numbering (α σ : Type*) where
  /-- The finite list of control states to number. -/
  states : List σ
  /-- The initial control state. -/
  start : σ
  /-- The partial transition on one input letter. -/
  go : σ → α → Option σ
  /-- The Boolean target test. -/
  final : σ → Bool
  /-- The Boolean admission test on an ordered pair of controls. -/
  rel : σ → σ → Bool
  /-- The start control is outside the target. -/
  initial : final start = false

namespace Numbering
variable [DecidableEq σ] (P : Numbering α σ)

/-- Compile the finite control into a stopping table by numbering its states. -/
abbrev table := StoppingTable.ofStates P.states P.start P.go P.final P.rel P.initial

/-- Number the start first and keep the other entries of the state list in their original order. -/
abbrev names := P.start :: P.states.erase P.start

/-- Look up the control state at an index, returning `none` at the sink. -/
def read (q : Fin P.table.size) := P.names[q.val]?

/-- The numbered start reads back as the initial control state. -/
@[simp] theorem read_start : P.read P.table.start = some P.start := rfl

/-- The permanent sink has no associated control state. -/
@[simp] theorem read_sink : P.read P.table.sink = none :=
  List.getElem?_eq_none (le_refl P.names.length)

/-- An index is a target exactly when it names a control state satisfying the final test. -/
theorem target_iff (q : Fin P.table.size) :
    q ∈ P.table.target ↔ ∃ s, P.read q = some s ∧ P.final s = true := by
  change q ∈ Finset.univ.filter (fun q => (P.read q).any P.final) ↔ _
  constructor
  · intro h
    have hf : (P.read q).any P.final = true := (Finset.mem_filter.mp h).2
    cases hs : P.read q with
    | none => simp [hs] at hf
    | some s => exact ⟨s, rfl, by simpa [hs] using hf⟩
  · rintro ⟨s,hs,hf⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hs, hf]⟩

/-- For an irreflexive control relation, a numbered pair is admitted exactly when its two
control states are related. -/
theorem pair_iff (irr : ∀ s, P.rel s s = false) (q r : Fin P.table.size) :
    (q,r) ∈ P.table.pairs ↔
      ∃ s t, P.read q = some s ∧ P.read r = some t ∧ P.rel s t = true := by
  change (q,r) ∈ Finset.univ.filter (fun p => p.1 ≠ p.2 ∧
    (P.read p.1).any (fun s => (P.read p.2).any (P.rel s))) ↔ _
  cases hs : P.read q <;> cases ht : P.read r <;> simp [hs, ht]
  intro h he
  subst r
  grind

private theorem read_code (s : σ) :
    P.names[P.names.idxOf s]? = if s ∈ P.names then some s else none := by
  split <;> rename_i h
  · exact List.getElem?_idxOf h
  · rw [List.idxOf_eq_length h]; simp

/-- Every listed control state receives an index. -/
theorem mem_names {s : σ} (hs : s ∈ P.states) : s ∈ P.names := by
  by_cases h : s = P.start
  · simp [names, h]
  · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne h).mpr hs)

/-- If the enumeration includes the start, every numbered name belongs to the original list. -/
theorem mem_states_of_mem_names (hi : P.start ∈ P.states) {s : σ}
    (hs : s ∈ P.names) : s ∈ P.states := by
  rcases List.mem_cons.mp hs with h | h
  · exact h ▸ hi
  · exact List.mem_of_mem_erase h

/-- A transition reads back as `r` exactly when a named nonfinal control takes the specified
letter to the numbered state `r`. -/
theorem read_step (q : Fin P.table.size) (a : α) (r : σ) :
    P.read (P.table.step q a) = some r ↔
      ∃ s, P.read q = some s ∧ P.final s = false ∧ P.go s a = some r ∧ r ∈ P.names := by
  by_cases ht : q ∈ P.table.target
  · rw [P.table.stop _ ht, read_sink]
    obtain ⟨s, hs, hf⟩ := (P.target_iff q).mp ht
    simp [hs, hf]
  · have eq : P.table.step q a = ((P.read q).bind (fun s => P.go s a)).elim P.table.sink
        (fun s => ⟨P.names.idxOf s, Nat.lt_succ_of_le List.idxOf_le_length⟩) := ite_eq_right ht
    rw [eq]
    cases hs : P.read q with
    | none => simp
    | some s =>
      have hf : P.final s = false := Bool.eq_false_iff.mpr
        (fun h => ht ((P.target_iff q).mpr ⟨s,hs,h⟩))
      cases he : P.go s a with
      | none => simp [he]
      | some v => simp only [Option.bind_some, he, Option.elim_some,
          Option.some.injEq, exists_eq_left', hf, true_and]
                  change P.names[P.names.idxOf v]? = some r ↔ _
                  rw [read_code]; split <;> grind

end Numbering
end DeciNSSE.Complexity.Tiling
