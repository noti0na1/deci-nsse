import DeciNSSE.Holes.Basic

/-! # Finite stopping tables

## Main declarations

- `StoppingTable` carries the target, irreflexive admission relation and sink.
- `StoppingTable.ofStates` numbers a list of controller states and adds the sink.
-/

namespace DeciNSSE.Complexity.Tiling
open Holes
variable {α σ : Type*}

/-- Finite tables with an absorbing nontarget sink and irreflexive admissions. -/
structure StoppingTable (α : Type*) where
  /-- The number of states in the table. -/
  size : ℕ
  /-- The initial state. -/
  start : Fin size
  /-- The absorbing state entered after a target. -/
  sink : Fin size
  /-- The transition on a state and an input letter. -/
  step : Fin size → α → Fin size
  /-- The states designated as rejected endpoints. -/
  target : Finset (Fin size)
  /-- The ordered state pairs whose suffix comparisons are admitted. -/
  pairs : Finset (Fin size × Fin size)
  /-- The start state is outside the target. -/
  start_clear : start ∉ target
  /-- The absorbing sink is outside the target. -/
  sink_clear : sink ∉ target
  /-- Every transition from the sink returns to the sink. -/
  absorb : ∀ a, step sink a = sink
  /-- Every transition from a target goes directly to the sink. -/
  stop : ∀ q ∈ target, ∀ a, step q a = sink
  /-- A state never admits a comparison with itself. -/
  irrefl : ∀ q, (q, q) ∉ pairs

/-- The table's deterministic reader uses its designated start and target set. -/
def StoppingTable.dfa (M : StoppingTable α) : DFA α (Fin M.size) :=
  ⟨M.step, M.start, ↑M.target⟩

/-- A table hole is a word reaching a target without an admitted comparison of suffixes. -/
def StoppingTable.Hole (M : StoppingTable α) :=
  IsReaderHole M.dfa (fun q r => (q, r) ∈ M.pairs) (↑M.target)

/-- Number the start first. The index just past the list is the permanent sink.
Missing transitions, including transitions to unlisted states, go to the sink. -/
def StoppingTable.ofStates [DecidableEq σ] (states : List σ) (initial : σ)
    (go : σ → α → Option σ) (final : σ → Bool) (rel : σ → σ → Bool)
    (hi : final initial = false) : StoppingTable α :=
  let xs := initial :: states.erase initial
  let read (q : Fin (xs.length + 1)) := xs[q.val]?
  let sink : Fin (xs.length + 1) := ⟨xs.length, by omega⟩
  let code (s : σ) : Fin (xs.length + 1) :=
    ⟨xs.idxOf s, Nat.lt_succ_of_le List.idxOf_le_length⟩
  let targets := Finset.univ.filter (fun q => (read q).any final)
  { size := xs.length + 1
    start := ⟨0, by omega⟩
    sink := sink
    target := targets
    pairs := Finset.univ.filter (fun p => p.1 ≠ p.2 ∧
      (read p.1).any (fun s => (read p.2).any (rel s)))
    step q a := if q ∈ targets then sink else ((read q).bind (fun s => go s a)).elim sink code
    start_clear := by simp [targets, read, xs, hi]
    sink_clear := by simp [targets, read, sink]
    absorb a := by simp [targets, read, sink]
    stop q h a := ite_eq_left h
    irrefl q := by simp }

/-- Decode one codeword at a time. Phase zero is a token boundary. A left
transition retains a partial code, and a right transition emits a letter and
resets the phase. Only boundary states carry targets or admissions. -/
def StoppingTable.decode {β : Type*} (M : StoppingTable α) (phases : ℕ)
    (parse : ℕ → β → Option (ℕ ⊕ α)) : StoppingTable β :=
  let states := (List.finRange M.size).flatMap fun q => (List.range phases).map (q, ·)
  let go (s : Fin M.size × ℕ) (a : β) := (parse s.2 a).map fun
    | .inl phase => (s.1, phase)
    | .inr letter => (M.step s.1 letter, 0)
  let final (s : Fin M.size × ℕ) := s.2 == 0 && s.1 ∈ M.target
  let rel (s r : Fin M.size × ℕ) := s.2 == 0 && r.2 == 0 && (s.1, r.1) ∈ M.pairs
  ofStates states (M.start, 0) go final rel (by simp [final, M.start_clear])

/-- Breadth-first enumeration with a bound on the number of processed states.
A state enters the queue only on its first discovery. -/
def discover [DecidableEq σ] (alphabet : List α) (go : σ → α → Option σ)
    (fuel : ℕ) (initial : σ) : List σ :=
  let rec visit : ℕ → List σ → List σ → List σ
    | 0, _, seen => seen
    | _ + 1, [], seen => seen
    | i + 1, s :: todo, seen =>
      let fresh := ((alphabet.filterMap (go s)).eraseDups).filter (· ∉ seen)
      visit i (todo ++ fresh) (fresh ++ seen)
  visit fuel [initial] [initial]

end DeciNSSE.Complexity.Tiling
