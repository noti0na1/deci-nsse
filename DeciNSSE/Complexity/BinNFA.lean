import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.FinRange

/-! # Binary automata

The hardness reduction starts from universality of nondeterministic automata
over the alphabet `Fin 2`. A `BinNFA m` has the states `Fin m`, Boolean
predicates for initial and final states, and a list of transitions; `Accepts`
is its language.

Automata with structured states are given by step functions. `Runs next p w`
says that some run of the step function `next` from `p` reads `w`, all states
being final. Through an injective index into `Fin m`, a step function on finitely
many listed states becomes a `BinNFA` (`BinNFA.ofStep`) with the same language
(`BinNFA.accepts_ofStep`).

## Main declarations
- `BinNFA`, `BinNFA.Path`, `BinNFA.AcceptsFrom`, `BinNFA.Accepts`
- `Runs`, the runs of a step function
- `BinNFA.ofStep`, `BinNFA.exists_path_ofStep`, `BinNFA.accepts_ofStep`,
  `BinNFA.length_trans_ofStep_le`
-/

namespace DeciNSSE.Complexity

/-- A nondeterministic automaton over the letters `Fin 2` with the states `Fin m`. -/
structure BinNFA (m : ℕ) where
  /-- The initial states. -/
  init : Fin m → Bool
  /-- The final states. -/
  final : Fin m → Bool
  /-- The transitions `(p, a, q)`, read as `p` goes to `q` on the letter `a`. -/
  trans : List (Fin m × Fin 2 × Fin m)

namespace BinNFA

variable {m : ℕ} (M : BinNFA m)

/-- Some run of the automaton reads the word from the first state to the second. -/
def Path : Fin m → List (Fin 2) → Fin m → Prop
  | p, [], q => p = q
  | p, a :: w, q => ∃ p', (p, a, p') ∈ M.trans ∧ Path p' w q

/-- The word is accepted from the given state. -/
def AcceptsFrom (p : Fin m) (w : List (Fin 2)) : Prop :=
  ∃ q, M.final q = true ∧ M.Path p w q

/-- The word is accepted from some initial state. -/
def Accepts (w : List (Fin 2)) : Prop :=
  ∃ p, M.init p = true ∧ M.AcceptsFrom p w

@[simp] theorem path_nil (p q : Fin m) : M.Path p [] q ↔ p = q := Iff.rfl

@[simp] theorem path_cons (p q : Fin m) (a : Fin 2) (w : List (Fin 2)) :
    M.Path p (a :: w) q ↔ ∃ p', (p, a, p') ∈ M.trans ∧ M.Path p' w q := Iff.rfl

/-- Runs split at every factorization of the word. -/
theorem path_append (p q : Fin m) (u v : List (Fin 2)) :
    M.Path p (u ++ v) q ↔ ∃ s, M.Path p u s ∧ M.Path s v q := by
  induction u generalizing p with
  | nil => simp
  | cons a u ih =>
    simp only [List.cons_append, path_cons, ih]
    constructor
    · rintro ⟨p', hp', s, hs, hv⟩; exact ⟨s, ⟨p', hp', hs⟩, hv⟩
    · rintro ⟨s, ⟨p', hp', hs⟩, hv⟩; exact ⟨p', hp', s, hs, hv⟩

@[simp] theorem acceptsFrom_nil (p : Fin m) : M.AcceptsFrom p [] ↔ M.final p = true := by
  simp [AcceptsFrom]

/-- A transition followed by a word accepted from its target is accepted. -/
theorem acceptsFrom_cons {p q : Fin m} {a : Fin 2} {w : List (Fin 2)}
    (ht : (p, a, q) ∈ M.trans) (hw : M.AcceptsFrom q w) : M.AcceptsFrom p (a :: w) := by
  obtain ⟨r, hr, hpath⟩ := hw
  exact ⟨r, hr, q, ht, hpath⟩

end BinNFA

/-! ### Step functions -/

/-- Some run of the step function `next` from the given state reads the whole word.
All states are final, so the run may end anywhere. -/
def Runs {S α : Type*} (next : S → α → List S) : S → List α → Prop
  | _, [] => True
  | p, a :: w => ∃ q ∈ next p a, Runs next q w

section Runs

variable {S α : Type*} (next : S → α → List S)

@[simp] theorem runs_nil (p : S) : Runs next p [] := trivial

@[simp] theorem runs_cons (p : S) (a : α) (w : List α) :
    Runs next p (a :: w) ↔ ∃ q ∈ next p a, Runs next q w := Iff.rfl

end Runs

namespace BinNFA

variable {S : Type*} {m : ℕ}

/-- The binary automaton, all of whose states are final, of the step function `next` on
the listed states, with the initial states `starts`, through the index `idx`. -/
def ofStep (states starts : List S) (next : S → Fin 2 → List S) (idx : S → Fin m) :
    BinNFA m where
  init i := starts.any fun p => idx p == i
  final _ := true
  trans := states.flatMap fun p =>
    (List.finRange 2).flatMap fun a => (next p a).map fun q => (idx p, a, idx q)

variable {states starts : List S} {next : S → Fin 2 → List S} {idx : S → Fin m}

/-- With an injective index, the transitions from the index of `p` are those of `p`. -/
theorem mem_trans_ofStep (hidx : Function.Injective idx) (hall : ∀ p, p ∈ states) (p : S)
    (a : Fin 2) (j : Fin m) :
    (idx p, a, j) ∈ (ofStep states starts next idx).trans ↔ ∃ q ∈ next p a, idx q = j := by
  simp only [ofStep, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro ⟨s, -, b, q, hq, hs, rfl, rfl⟩
    obtain rfl := hidx hs
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨p, hall p, a, q, hq, rfl, rfl, rfl⟩

/-- With an injective index, runs from the index of `p` are the runs of `p`. -/
theorem exists_path_ofStep (hidx : Function.Injective idx) (hall : ∀ p, p ∈ states)
    (p : S) (u : List (Fin 2)) :
    (∃ j, (ofStep states starts next idx).Path (idx p) u j) ↔ Runs next p u := by
  induction u generalizing p with
  | nil => simp
  | cons a u ih =>
    simp only [path_cons, mem_trans_ofStep hidx hall, runs_cons]
    constructor
    · rintro ⟨j, _, ⟨q, hq, rfl⟩, hpath⟩
      exact ⟨q, hq, (ih q).1 ⟨j, hpath⟩⟩
    · rintro ⟨q, hq, hrun⟩
      obtain ⟨j, hpath⟩ := (ih q).2 hrun
      exact ⟨j, idx q, ⟨q, hq, rfl⟩, hpath⟩

/-- **Structured automata as binary automata.** With an injective index, the automaton
accepts a word iff some initial state has a run on it. -/
theorem accepts_ofStep (hidx : Function.Injective idx) (hall : ∀ p, p ∈ states)
    (u : List (Fin 2)) :
    (ofStep states starts next idx).Accepts u ↔ ∃ p ∈ starts, Runs next p u := by
  simp only [Accepts, AcceptsFrom]
  constructor
  · rintro ⟨i, hi, j, -, hpath⟩
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ starts, idx p = i := by simpa [ofStep] using hi
    exact ⟨p, hp, (exists_path_ofStep hidx hall p u).1 ⟨j, hpath⟩⟩
  · rintro ⟨p, hp, hrun⟩
    obtain ⟨j, hpath⟩ := (exists_path_ofStep hidx hall p u).2 hrun
    exact ⟨idx p, by simpa [ofStep] using ⟨p, hp, rfl⟩, j, rfl, hpath⟩

/-- With at most `c` successors for each state and letter, the automaton has at most `2 c`
transitions per listed state. -/
theorem length_trans_ofStep_le {c : ℕ} (h : ∀ p a, (next p a).length ≤ c) :
    (ofStep states starts next idx).trans.length ≤ states.length * (2 * c) := by
  have hp (p : S) : ((List.finRange 2).flatMap fun a =>
      (next p a).map fun q => (idx p, a, idx q)).length ≤ 2 * c := by
    rw [List.length_flatMap]
    refine (List.sum_le_length_nsmul _ c fun x hx => ?_).trans (by simp)
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    simpa using h p a
  rw [ofStep, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ (2 * c) fun x hx => ?_).trans (by simp [mul_comm])
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  exact hp p

end BinNFA

end DeciNSSE.Complexity
