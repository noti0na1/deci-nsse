import DeciNSSE.Complexity.Counter
import DeciNSSE.Complexity.HardnessAutomaton

/-! # The counter automaton over binary letters

The tokens are coded by two bits, `0 ↦ 00`, `1 ↦ 01`, `# ↦ 10` and `$ ↦ 11`, and
`counterWord k` is the code of the counter record `H`, of length `2 (k + 1) 2^k`.
The binary automaton has the states `q`, `(q, 0)` and `(q, 1)` for every state `q`
of the token automaton, all final: from `q` it reads the first bit `a` of a code
into `(q, a)`, and from `(q, a)` the second bit `b` into every successor of `q` on
the token coded by `a b`. So a binary word has a run from `q` iff its longest prefix
of even length decodes to a token word with a run from `q` (`runs_binNext_iff`), and
the binary automaton accepts exactly the words that do not begin with `counterWord k`.

A step function on structured states, all final, becomes a `BinNFA` through an
injective index (`BinNFA.ofStep`); here the index maps the `9 k + 27` binary states
injectively into `Fin (9 k + 27)`.

## Main declarations
- `BinNFA.ofStep`, `BinNFA.accepts_ofStep`
- `Counter.code`, `Counter.decode`, `Counter.code_prefix_iff`
- `Counter.counterNFA`, `Counter.counterWord`
- `Counter.counterNFA_final`, `Counter.counterNFA_accepts_iff`,
  `Counter.length_counterWord`
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity

namespace BinNFA

open Counter

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

end BinNFA

namespace Counter

open Tok St

variable {k : ℕ}

/-! ### The two-bit code -/

/-- The two-bit code `0 ↦ 00`, `1 ↦ 01`, `# ↦ 10`, `$ ↦ 11` of a token. -/
def bits : Tok → List (Fin 2)
  | bit false => [0, 0]
  | bit true => [0, 1]
  | sep => [1, 0]
  | stop => [1, 1]

/-- The token with the two-bit code `a b`. -/
def tok (a b : Fin 2) : Tok := if a = 0 then bit (b = 1) else if b = 0 then sep else stop

/-- The code of a token word. -/
def code (w : List Tok) : List (Fin 2) := w.flatMap bits

/-- The token word coded by the longest prefix of even length. -/
def decode : List (Fin 2) → List Tok
  | a :: b :: u => tok a b :: decode u
  | _ => []

/-- The code of the token coded by `a b` is `a b`. -/
theorem bits_tok (a b : Fin 2) : bits (tok a b) = [a, b] := by
  fin_cases a <;> fin_cases b <;> rfl

@[simp] theorem length_bits (t : Tok) : (bits t).length = 2 := by
  rcases t with (_ | _) | _ | _ <;> rfl

@[simp] theorem length_code (w : List Tok) : (code w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rw [code, List.flatMap_cons, List.length_append, ← code, ih, length_bits,
      List.length_cons]
    ring

/-- Decoding inverts the code. -/
theorem decode_code_append (w : List Tok) (r : List (Fin 2)) :
    decode (code w ++ r) = w ++ decode r := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rw [code, List.flatMap_cons, List.append_assoc, ← code]
    cases t with
    | bit b => cases b <;> simp [bits, decode, tok, ih]
    | sep => simp [bits, decode, tok, ih]
    | stop => simp [bits, decode, tok, ih]

/-- The code of the decoding of a word is a prefix of the word. -/
theorem code_decode_prefix : ∀ u : List (Fin 2), code (decode u) <+: u
  | [] => List.prefix_rfl
  | [_] => List.nil_prefix
  | a :: b :: u => by
    rw [decode, code, List.flatMap_cons, ← code, bits_tok]
    simpa [List.cons_prefix_cons] using code_decode_prefix u

/-- A binary word begins with the code of `w` iff its decoding begins with `w`. -/
theorem code_prefix_iff (w : List Tok) (u : List (Fin 2)) : code w <+: u ↔ w <+: decode u := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨decode r, (decode_code_append w r).symm⟩
  · rintro ⟨r, hr⟩
    refine List.IsPrefix.trans ⟨code r, ?_⟩ (code_decode_prefix u)
    rw [← hr, code, code, code, List.flatMap_append]

/-! ### The binary automaton -/

/-- The states of the binary automaton: `(q, none)` is `q`, and `(q, some a)` is `q`
after the first bit `a` of a code. -/
abbrev BinSt (k : ℕ) := St k × Option (Fin 2)

/-- The binary step function. -/
def binNext (k : ℕ) : BinSt k → Fin 2 → List (BinSt k)
  | (q, none), a => [(q, some a)]
  | (q, some a), b => (next k q (tok a b)).map fun r => (r, none)

/-- A binary word has a run from `q` iff its decoding has a token run from `q`. -/
theorem runs_binNext_iff (q : St k) :
    ∀ u : List (Fin 2), Runs (binNext k) (q, none) u ↔ Runs (next k) q (decode u)
  | [] => by simp [decode]
  | [a] => by simp [binNext, decode]
  | a :: b :: u => by
    simp only [runs_cons, binNext, List.mem_cons, List.not_mem_nil, or_false, exists_eq_left,
      List.mem_map, decode]
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, hrun⟩
      exact ⟨r, hr, (runs_binNext_iff r u).1 hrun⟩
    · rintro ⟨r, hr, hrun⟩
      exact ⟨(r, none), ⟨r, hr, rfl⟩, (runs_binNext_iff r u).2 hrun⟩

/-- All states of the token automaton. -/
def allStates (k : ℕ) : List (St k) :=
  [done, zero, carry false, carry true, ones false, ones true] ++
    (List.finRange (k + 1)).map fmt ++
    (List.finRange (k + 1)).flatMap fun j => [wait false j, wait true j]

theorem mem_allStates (q : St k) : q ∈ allStates k := by
  rcases q with _ | p | _ | (_ | _) | ⟨(_ | _), j⟩ | (_ | _) <;> simp [allStates]

/-- All states of the binary automaton. -/
def binStates (k : ℕ) : List (BinSt k) :=
  (allStates k).flatMap fun q => [(q, none), (q, some 0), (q, some 1)]

theorem mem_binStates (q : BinSt k) : q ∈ binStates k := by
  obtain ⟨q, o⟩ := q
  simp only [binStates, List.mem_flatMap]
  refine ⟨q, mem_allStates q, ?_⟩
  rcases o with _ | a
  · simp
  · fin_cases a <;> simp

/-- The index of a token state, below `3 k + 9`. -/
def index : St k → ℕ
  | done => 0
  | fmt p => 1 + p
  | zero => k + 2
  | carry c => k + 3 + c.toNat
  | wait b j => k + 5 + 2 * j + b.toNat
  | ones o => 3 * k + 7 + o.toNat

theorem index_lt (q : St k) : index q < 3 * k + 9 := by
  rcases q with _ | p | _ | (_ | _) | ⟨(_ | _), j⟩ | (_ | _) <;> simp [index] <;> omega

/-- Distinct token states have distinct indices. -/
theorem index_injective : Function.Injective (index (k := k)) := by
  intro q q' h
  rcases q with _ | p | _ | (_ | _) | ⟨(_ | _), j⟩ | (_ | _) <;>
    rcases q' with _ | p' | _ | (_ | _) | ⟨(_ | _), j'⟩ | (_ | _) <;>
    simp only [index, Bool.toNat_false, Bool.toNat_true] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (simp only [fmt.injEq, wait.injEq, true_and]; exact Fin.ext (by omega))

/-- The offset of the pending bit within the three binary states of a token state. -/
def offset : Option (Fin 2) → ℕ
  | none => 0
  | some a => a + 1

theorem offset_le (o : Option (Fin 2)) : offset o ≤ 2 := by
  rcases o with _ | a
  · exact Nat.zero_le 2
  · simp only [offset]; omega

/-- The index of a binary state in `Fin (9 k + 27)`. -/
def binIndex (k : ℕ) (q : BinSt k) : Fin (9 * k + 27) :=
  ⟨3 * index q.1 + offset q.2, by have := index_lt q.1; have := offset_le q.2; omega⟩

/-- Distinct binary states have distinct indices. -/
theorem binIndex_injective : Function.Injective (binIndex k) := by
  rintro ⟨q, o⟩ ⟨q', o'⟩ h
  simp only [binIndex, Fin.mk.injEq] at h
  have ho := offset_le o
  have ho' := offset_le o'
  obtain rfl : q = q' := index_injective (by omega)
  have hoo : offset o = offset o' := by omega
  rcases o with _ | a <;> rcases o' with _ | a' <;> simp only [offset] at hoo
  · rfl
  · exact absurd hoo (by omega)
  · exact absurd hoo (by omega)
  · exact congrArg (fun a => (q, some a)) (Fin.ext (by omega))

/-- The binary counter automaton, with `9 k + 27` states, all final. -/
def counterNFA (k : ℕ) : BinNFA (9 * k + 27) :=
  BinNFA.ofStep (binStates k) ((initial k).map fun q => (q, none)) (binNext k) (binIndex k)

/-- The binary code `W` of the counter record `H`. -/
def counterWord (k : ℕ) : List (Fin 2) := code (counter k)

/-- Every state of the counter automaton is final. -/
theorem counterNFA_final (q : Fin (9 * k + 27)) : (counterNFA k).final q = true := rfl

/-- **The binary counter automaton** accepts exactly the words that do not begin with
`counterWord k`. -/
theorem counterNFA_accepts_iff (u : List (Fin 2)) :
    (counterNFA k).Accepts u ↔ ¬ counterWord k <+: u := by
  rw [counterNFA, BinNFA.accepts_ofStep binIndex_injective mem_binStates, counterWord,
    code_prefix_iff, ← exists_runs_iff]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hrun⟩
    exact ⟨q, hq, (runs_binNext_iff q u).1 hrun⟩
  · rintro ⟨q, hq, hrun⟩
    exact ⟨(q, none), ⟨q, hq, rfl⟩, (runs_binNext_iff q u).2 hrun⟩

/-- The word `W` has length `2 (k + 1) 2^k`. -/
theorem length_counterWord : (counterWord k).length = 2 * (k + 1) * 2 ^ k := by
  rw [counterWord, length_code, length_counter, mul_assoc]

end Counter

end DeciNSSE.Complexity
