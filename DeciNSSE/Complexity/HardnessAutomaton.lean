import DeciNSSE.Semantics.Characterisation

/-! # Binary automata and the doubling code

The source problem of the hardness reduction is universality of nondeterministic
automata over the alphabet `Fin 2`. A `BinNFA m` has the states `Fin m`, Boolean
predicates for initial and final states, and a list of transitions; `Accepts`
is its language.

The reduction reads words through the doubling code `code w = e(w) 1`, where `e`
replaces each letter `a` by `0 a`, written over the constructor directions
`Fin n` with `2 ≤ n`. The code is prefix free (`eq_of_code_prefix`).

## Main declarations
- `BinNFA`, `BinNFA.Path`, `BinNFA.AcceptsFrom`, `BinNFA.Accepts`
- `Hardness.dir`, `Hardness.pad`, `Hardness.code`, `Hardness.eq_of_code_prefix`
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

/-- Runs split at every factorisation of the word. -/
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

namespace Hardness

variable {n : ℕ} (hn : 2 ≤ n)

/-- A binary letter as a constructor direction. -/
def dir (a : Fin 2) : Fin n := ⟨a.val, by omega⟩

@[simp] theorem dir_val (a : Fin 2) : (dir hn a).val = a.val := rfl

/-- Distinct letters give distinct directions. -/
theorem dir_injective : Function.Injective (dir hn) := by
  intro a b h
  exact Fin.ext (by simpa using congrArg Fin.val h)

theorem dir_one_ne_zero : dir hn 1 ≠ dir hn 0 := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

/-- The doubling `e`: each letter `a` becomes the two directions `0 a`. -/
def pad (w : List (Fin 2)) : List (Fin n) :=
  w.flatMap fun a => [dir hn 0, dir hn a]

/-- The code `e(w) 1` of a binary word. -/
def code (w : List (Fin 2)) : List (Fin n) := pad hn w ++ [dir hn 1]

@[simp] theorem pad_nil : pad hn [] = [] := rfl

@[simp] theorem pad_cons (a : Fin 2) (w : List (Fin 2)) :
    pad hn (a :: w) = dir hn 0 :: dir hn a :: pad hn w := rfl

theorem pad_append (u v : List (Fin 2)) : pad hn (u ++ v) = pad hn u ++ pad hn v := by
  simp [pad]

theorem pad_snoc (w : List (Fin 2)) (a : Fin 2) :
    pad hn (w ++ [a]) = pad hn w ++ [dir hn 0] ++ [dir hn a] := by
  simp [pad_append]

@[simp] theorem code_nil : code hn [] = [dir hn 1] := rfl

@[simp] theorem code_cons (a : Fin 2) (w : List (Fin 2)) :
    code hn (a :: w) = dir hn 0 :: dir hn a :: code hn w := rfl

@[simp] theorem code_ne_nil (w : List (Fin 2)) : code hn w ≠ [] := by
  simp [code]

/-- Codes use only the two binary directions. -/
theorem val_lt_two_of_mem_code {w : List (Fin 2)} {i : Fin n} (hi : i ∈ code hn w) :
    i.val < 2 := by
  induction w with
  | nil => simp at hi; simp [hi]
  | cons a w ih =>
    simp only [code_cons, List.mem_cons] at hi
    rcases hi with rfl | rfl | hi
    · simp
    · simp
    · exact ih hi

/-- The code is prefix free. -/
theorem eq_of_code_prefix : ∀ {v w : List (Fin 2)}, code hn v <+: code hn w → v = w
  | [], [], _ => rfl
  | [], b :: w, h => by
    simp only [code_nil, code_cons, List.cons_prefix_cons] at h
    exact absurd h.1 (dir_one_ne_zero hn)
  | a :: v, [], h => by
    simp only [code_nil, code_cons, List.cons_prefix_cons] at h
    exact absurd h.1.symm (dir_one_ne_zero hn)
  | a :: v, b :: w, h => by
    simp only [code_cons, List.cons_prefix_cons] at h
    rw [dir_injective hn h.2.1, eq_of_code_prefix h.2.2]

end Hardness

end DeciNSSE.Complexity
