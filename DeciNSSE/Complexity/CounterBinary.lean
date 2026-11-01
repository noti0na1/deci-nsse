import DeciNSSE.Complexity.Counter
import DeciNSSE.Words
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! # The counter automaton over binary letters

The tokens are coded by two bits, `0 ↦ 00`, `1 ↦ 01`, `# ↦ 10` and `$ ↦ 11`, and
`counterWord k` is the code of the counter record `H`, of length `2 (k + 1) 2^k`.
The binary automaton has the states `q`, `(q, 0)` and `(q, 1)` for every state `q`
of the token automaton, all final: from `q` it reads the first bit `a` of a code
into `(q, a)`, and from `(q, a)` the second bit `b` into every successor of `q` on
the token coded by `a b`. So a binary word has a run from `q` iff its longest prefix
of even length decodes to a token word with a run from `q` (`runs_binNext_iff`), and
the binary automaton accepts exactly the words that do not begin with `counterWord k`.

The binary automaton is the `BinNFA` of this step function (`BinNFA.ofStep`), through
an index that maps the `9 k + 27` binary states injectively into `Fin (9 k + 27)`.
Each state has at most two successors on each bit, so it has at most `36 k + 108`
transitions.

## Main declarations
- `Counter.encode`, `Counter.decode`, `Counter.encode_prefix_iff`
- `Counter.counterNFA`, `Counter.counterWord`
- `Counter.counterNFA_final`, `Counter.counterNFA_accepts_iff`,
  `Counter.length_counterWord`, `Counter.counterWord_ne_nil`
- `Counter.length_trans_counterNFA_le`: the transition count
-/

namespace DeciNSSE.Complexity

namespace Counter

open Token State

variable {k : ℕ}

/-! ### The two-bit code -/

/-- The two-bit code `0 ↦ 00`, `1 ↦ 01`, `# ↦ 10`, `$ ↦ 11` of a token. -/
def bits : Token → List (Fin 2)
  | bit false => [0, 0]
  | bit true => [0, 1]
  | sep => [1, 0]
  | stop => [1, 1]

/-- The token with the two-bit code `a b`. -/
def tokenOfBits (a b : Fin 2) : Token :=
  if a = 0 then bit (b = 1) else if b = 0 then sep else stop

/-- The two-bit code of a token word. -/
def encode (w : List Token) : List (Fin 2) := w.flatMap bits

/-- The token word coded by the longest prefix of even length. -/
def decode : List (Fin 2) → List Token
  | a :: b :: u => tokenOfBits a b :: decode u
  | _ => []

/-- The code of the token coded by `a b` is `a b`. -/
theorem bits_tokenOfBits (a b : Fin 2) : bits (tokenOfBits a b) = [a, b] := by
  fin_cases a <;> fin_cases b <;> rfl

@[simp] theorem length_bits (t : Token) : (bits t).length = 2 := by
  rcases t with (_ | _) | _ | _ <;> rfl

@[simp] theorem length_encode (w : List Token) : (encode w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rw [encode, List.flatMap_cons, List.length_append, ← encode, ih, length_bits,
      List.length_cons]
    ring

/-- Decoding inverts the code. -/
theorem decode_encode_append (w : List Token) (r : List (Fin 2)) :
    decode (encode w ++ r) = w ++ decode r := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    rw [encode, List.flatMap_cons, List.append_assoc, ← encode]
    cases t with
    | bit b => cases b <;> simp [bits, decode, tokenOfBits, ih]
    | sep => simp [bits, decode, tokenOfBits, ih]
    | stop => simp [bits, decode, tokenOfBits, ih]

/-- The code of the decoding of a word is a prefix of the word. -/
theorem encode_decode_prefix : ∀ u : List (Fin 2), encode (decode u) <+: u
  | [] => List.prefix_rfl
  | [_] => List.nil_prefix
  | a :: b :: u => by
    rw [decode, encode, List.flatMap_cons, ← encode, bits_tokenOfBits]
    simpa [List.cons_prefix_cons] using encode_decode_prefix u

/-- A binary word begins with the code of `w` iff its decoding begins with `w`. -/
theorem encode_prefix_iff (w : List Token) (u : List (Fin 2)) :
    encode w <+: u ↔ w <+: decode u := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨decode r, (decode_encode_append w r).symm⟩
  · rintro ⟨r, hr⟩
    refine List.IsPrefix.trans ⟨encode r, ?_⟩ (encode_decode_prefix u)
    rw [← hr, encode, encode, encode, List.flatMap_append]

/-! ### The binary automaton -/

/-- The states of the binary automaton: `(q, none)` is `q`, and `(q, some a)` is `q`
after the first bit `a` of a code. -/
abbrev BinState (k : ℕ) := State k × Option (Fin 2)

/-- The binary step function. -/
def binNext (k : ℕ) : BinState k → Fin 2 → List (BinState k)
  | (q, none), a => [(q, some a)]
  | (q, some a), b => (next k q (tokenOfBits a b)).map fun r => (r, none)

/-- A binary word has a run from `q` iff its decoding has a token run from `q`. -/
theorem runs_binNext_iff (q : State k) :
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
def allStates (k : ℕ) : List (State k) :=
  [done, zero, carry false, carry true, ones false, ones true] ++
    (List.finRange (k + 1)).map fmt ++
    (List.finRange (k + 1)).flatMap fun j => [wait false j, wait true j]

theorem mem_allStates (q : State k) : q ∈ allStates k := by
  rcases q with _ | p | _ | (_ | _) | ⟨(_ | _), j⟩ | (_ | _) <;> simp [allStates]

/-- All states of the binary automaton. -/
def binStates (k : ℕ) : List (BinState k) :=
  (allStates k).flatMap fun q => [(q, none), (q, some 0), (q, some 1)]

theorem mem_binStates (q : BinState k) : q ∈ binStates k := by
  obtain ⟨q, o⟩ := q
  simp only [binStates, List.mem_flatMap]
  refine ⟨q, mem_allStates q, ?_⟩
  rcases o with _ | a
  · simp
  · fin_cases a <;> simp

/-- The index of a token state, below `3 k + 9`. -/
def index : State k → ℕ
  | done => 0
  | fmt p => 1 + p
  | zero => k + 2
  | carry c => k + 3 + c.toNat
  | wait b j => k + 5 + 2 * j + b.toNat
  | ones o => 3 * k + 7 + o.toNat

theorem index_lt (q : State k) : index q < 3 * k + 9 := by
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
def binIndex (k : ℕ) (q : BinState k) : Fin (9 * k + 27) :=
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
def counterWord (k : ℕ) : List (Fin 2) := encode (counterRecord k)

/-- Every state of the counter automaton is final. -/
theorem counterNFA_final (q : Fin (9 * k + 27)) : (counterNFA k).final q = true := rfl

/-- **The binary counter automaton** accepts exactly the words that do not begin with
`counterWord k`. -/
theorem counterNFA_accepts_iff (u : List (Fin 2)) :
    (counterNFA k).Accepts u ↔ ¬ counterWord k <+: u := by
  rw [counterNFA, BinNFA.accepts_ofStep binIndex_injective mem_binStates, counterWord,
    encode_prefix_iff, ← exists_runs_iff]
  simp only [List.mem_map]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, hrun⟩
    exact ⟨q, hq, (runs_binNext_iff q u).1 hrun⟩
  · rintro ⟨q, hq, hrun⟩
    exact ⟨(q, none), ⟨q, hq, rfl⟩, (runs_binNext_iff q u).2 hrun⟩

/-- The word `W` has length `2 (k + 1) 2^k`. -/
theorem length_counterWord : (counterWord k).length = 2 * (k + 1) * 2 ^ k := by
  rw [counterWord, length_encode, length_counterRecord, mul_assoc]

variable (k) in
/-- The counter word is not empty. -/
theorem counterWord_ne_nil : counterWord k ≠ [] := by
  intro h
  have hlen := length_counterWord (k := k)
  rw [h, List.length_nil] at hlen
  have : 0 < 2 * (k + 1) * 2 ^ k := by positivity
  omega

/-- A token state has at most two successors on each token. -/
theorem length_next_le (q : State k) (t : Token) : (next k q t).length ≤ 2 := by
  cases q <;> cases t <;> simp only [next] <;> (try split_ifs) <;> simp

/-- A binary state has at most two successors on each bit. -/
theorem length_binNext_le (p : BinState k) (a : Fin 2) : (binNext k p a).length ≤ 2 := by
  obtain ⟨q, _ | b⟩ := p
  · simp [binNext]
  · simpa [binNext] using length_next_le q (tokenOfBits b a)

variable (k) in
/-- The counter automaton has at most `36 k + 108` transitions. -/
theorem length_trans_counterNFA_le : (counterNFA k).trans.length ≤ 36 * k + 108 := by
  have hall : (allStates k).length ≤ 3 * k + 9 := by
    have := Words.length_flatMap_le (List.finRange (k + 1))
      (fun j => [State.wait false j, State.wait true j]) (c := 2) fun _ _ => le_rfl
    simp only [allStates, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_finRange] at this ⊢
    omega
  have hbin : (binStates k).length ≤ 9 * k + 27 :=
    (Words.length_flatMap_le (allStates k) (fun q => [(q, none), (q, some 0), (q, some 1)])
      (c := 3) fun _ _ => le_rfl).trans (by omega)
  refine (BinNFA.length_trans_ofStep_le (c := 2) length_binNext_le).trans ?_
  calc (binStates k).length * (2 * 2) ≤ (9 * k + 27) * 4 := Nat.mul_le_mul_right _ hbin
    _ = 36 * k + 108 := by ring

end Counter

end DeciNSSE.Complexity
