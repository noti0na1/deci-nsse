import DeciNSSE.Complexity.Tiling.Tables
import DeciNSSE.Complexity.Tiling.Tracks

/-! # The constraint list emitted from a stopping table

## Main declarations

- `emit` builds the backbone and marker literals.
- `emit_size` bounds the variables and literals.
-/

namespace DeciNSSE.Complexity.Tiling
variable {n : ℕ}
/-- A query packages a constraint list and its variable count together with the two variables to
compare. -/
structure Query (n : ℕ) where
  /-- The number of variables allocated to the system. -/
  vars : ℕ
  /-- The emitted list of flat constraints. -/
  system : Constraint n vars
  /-- The variable on the left of the query. -/
  x : V vars
  /-- The variable on the right of the query. -/
  y : V vars

namespace Emitter
variable (M : StoppingTable (Fin n))

/-- The emitter allocates `3 * M.size + 1` variables. -/
abbrev K := 3 * M.size + 1

/-- The upper backbone variable represents state `q` on an upper trace. -/
def u (q : Fin M.size) : V (K M) := ⟨q.val, by dsimp [K]; omega⟩

/-- The lower backbone variable represents state `q` on a lower trace. -/
def l (q : Fin M.size) : V (K M) := ⟨M.size + q.val, by dsimp [K]; omega⟩

/-- The variable equated to top occupies the start state's spare marker index. -/
def top : V (K M) := ⟨2 * M.size + M.start.val, by dsimp [K]; omega⟩

/-- The dummy variable supplies a child when a state has no upper backbone or incoming admission
marker to offer. -/
def dummy : V (K M) := ⟨3 * M.size, by dsimp [K]; omega⟩

/-- The marker for `q` records admissions from that state. At the start it is the lower backbone
itself. -/
def marker (q : Fin M.size) : V (K M) :=
  if q = M.start then l M q else ⟨2 * M.size + q.val, by dsimp [K]; omega⟩

/-- List the upper child choices for a successor, including its incoming admission markers and a
dummy if needed. -/
def upper (r : Fin M.size) :=
  let xs := (if r ∈ M.target then [] else [u M r]) ++
    ((List.finRange M.size).filter fun a => (a, r) ∈ M.pairs).map (marker M)
  if xs.isEmpty then [dummy M] else xs

/-- The lower child choices of a successor are its lower backbone and its marker. -/
def lower (r : Fin M.size) := [l M r, marker M r]

/-- Form child vectors by varying one direction through its choices and taking the first choice
in each other direction. -/
def vectors {k : ℕ} (choices : Fin n → List (V k)) (fallback : V k) :=
  (List.finRange n).flatMap fun i => (choices i).map fun v j =>
    if i = j then v else (choices j).headD fallback

/-- Emit the constructor literals for one state, using the top variable for all lower children
at a target. -/
def row (q : Fin M.size) : Constraint n (K M) :=
  if q ∈ M.target then [Lit.fLe (fun _ => top M) (l M q)]
  else (vectors (fun i => upper M (M.step q i)) (dummy M)).map (Lit.leF (u M q)) ++
    (vectors (fun i => lower M (M.step q i)) (dummy M)).map (fun a => Lit.fLe a (l M q))

/-- Collect the constructor literals for all states and equate the designated top variable to
top. -/
def system : Constraint n (K M) := .eqTop (top M) :: (List.finRange M.size).flatMap (row M)

end Emitter
open Emitter

/-- Build a covariant system with upper and lower backbones and a marker for each state. The
start marker is its lower backbone. -/
def emit (M : StoppingTable (Fin n)) : Query n :=
  ⟨K M, system M, u M M.start, l M M.start⟩

/-- Concatenating one list of length at most `b` per entry of `xs` uses at most `xs.length * b`
letters. -/
theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (b : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ b) : (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := h x List.mem_cons_self
    have h₂ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]; omega

private theorem vectors_length {k : ℕ} (choices : Fin n → List (V k)) (d : V k)
    {b : ℕ} (h : ∀ i, (choices i).length ≤ b) : (vectors choices d).length ≤ n * b := by
  unfold vectors
  simpa using flatMap_length_le (List.finRange n) _ b (fun i _ => by simpa using h i)

/-- The emitter uses `3*M.size+1` variables, and its literal count is at most quadratic in the
state count and linear in arity. -/
theorem emit_size (M : StoppingTable (Fin n)) : (emit M).vars = 3 * M.size + 1 ∧
    (emit M).system.length ≤ M.size * (1 + n * (M.size + 3)) + 1 := by
  refine ⟨rfl, ?_⟩
  change @List.length (Lit n (3 * M.size + 1)) (_ :: (List.finRange M.size).flatMap _) ≤ _
  rw [List.length_cons]
  apply Nat.add_le_add_right
  apply (flatMap_length_le _ _ _ ?_).trans (by rw [List.length_finRange])
  intro q _
  unfold row
  split
  · simp
  · rw [List.length_append, List.length_map, List.length_map]
    have incoming : ∀ r : Fin M.size, _ := fun r => by
      have h := List.length_filter_le (fun a => decide ((a, r) ∈ M.pairs)) (List.finRange M.size)
      rw [List.length_finRange] at h
      exact h
    apply (Nat.add_le_add (vectors_length _ _ (b := M.size + 1) ?_)
      (vectors_length _ _ (b := 2) (by simp [lower]))).trans (by ring_nf; omega)
    intro i
    dsimp only [upper]
    have h := incoming (M.step q i)
    split_ifs <;> simp only [List.length_singleton, List.length_append, List.length_map,
      List.length_nil] <;> omega

end DeciNSSE.Complexity.Tiling
