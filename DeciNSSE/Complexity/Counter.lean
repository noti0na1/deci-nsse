import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

/-! # A small automaton for the words that do not extend a binary counter

Over the tokens `0`, `1`, `#` and `$`, let `H = C₀ # C₁ # ⋯ # C_{2^k-1} $`, where
`Cⱼ` is the `k`-bit binary expansion of `j`, least significant bit first; it has
length `(k + 1) 2^k`. A nondeterministic automaton with `3 k + 9` states, all
final, has a run on a word exactly when the word does not begin with `H`. Its
states are

- `E`, which loops on every token;
- `F p`, `p ≤ k`, which checks the format: blocks of `k` bits separated by `#`,
  closed by `$`;
- `I`, which checks that the first block is zero;
- `C c`, which tracks the carry `c` of an increment and, at every bit, spawns a
  checker `W b k` for the bit `b` expected at the same offset of the next block;
- `W b j`, which skips `j` tokens other than `$` and then reaches `E` on a bit
  other than the expected bit `b`;
- `O o`, which records whether the current block is all ones so far, and
  checks that `#` follows only blocks that are not all ones and that `$` follows
  the all-ones block.

A branch reaches `E` when it finds a deviation from `H`, and dies where it
confirms its part of `H`. Each component has a closed form on a word cut
into blocks (`runs_carry_block_iff`, `runs_ones_record_cons`, …). When all four
initial branches die, the format branch cuts the word into blocks
(`exists_record_of_not_runs_fmt`), and the counting step
(`not_runs_carry_ones_iff`) forces the blocks to be the counts `0, …, 2^k - 1`.

## Main declarations
- `Counter.Tok`, `Counter.St`, `Counter.next`, `Counter.Runs`, `Counter.initial`
- `Counter.toBits`, `Counter.record`, `Counter.counter`
- `Counter.exists_runs_iff`: some initial state has a run on `w` iff `w` does
  not begin with `counter k`
- `Counter.length_counter`: `(counter k).length = (k + 1) * 2 ^ k`
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity

namespace Counter

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

/-- The tokens: a bit, the block separator `#` and the end marker `$`. -/
inductive Tok
  /-- A bit of a block. -/
  | bit (b : Bool)
  /-- The separator `#` between blocks. -/
  | sep
  /-- The end marker `$`. -/
  | stop
  deriving DecidableEq

open Tok

variable {k : ℕ}

/-- The states of the counter automaton. -/
inductive St (k : ℕ)
  /-- `E`: a deviation was found. -/
  | done
  /-- `F p`: the format checker, `p` bits into the current block. -/
  | fmt (p : Fin (k + 1))
  /-- `I`: the first block is zero so far. -/
  | zero
  /-- `C c`: the increment checker, with the carry `c` into the next bit. -/
  | carry (c : Bool)
  /-- `W b j`: the bit `b` is due after `j` more tokens other than `$`. -/
  | wait (b : Bool) (j : Fin (k + 1))
  /-- `O o`: `o` records whether the current block is all ones so far. -/
  | ones (o : Bool)
  deriving DecidableEq

open St

/-- One step down in `Fin (k + 1)`, stopping at zero. -/
def down (j : Fin (k + 1)) : Fin (k + 1) := ⟨(j : ℕ) - 1, by omega⟩

@[simp] theorem val_down (j : Fin (k + 1)) : (down j : ℕ) = j - 1 := rfl

/-- The transitions of the counter automaton; a missing transition kills the branch. -/
def next (k : ℕ) : St k → Tok → List (St k)
  | done, _ => [done]
  | fmt p, bit _ => if h : p.val < k then [fmt ⟨p.val + 1, by omega⟩] else [done]
  | fmt p, sep => if p.val = k then [fmt 0] else [done]
  | fmt p, stop => if p.val < k then [done] else []
  | zero, bit b => if b then [done] else [zero]
  | zero, _ => []
  | carry c, bit b => [carry (c && b), wait (b ^^ c) (Fin.last k)]
  | carry _, sep => [carry true]
  | carry _, stop => []
  | wait b j, bit b' =>
    if (j : ℕ) = 0 then (if b' = b then [] else [done]) else [wait b (down j)]
  | wait b j, sep => if (j : ℕ) = 0 then [] else [wait b (down j)]
  | wait _ _, stop => []
  | ones o, bit b => [ones (o && b)]
  | ones o, sep => if o then [done] else [ones true]
  | ones o, stop => if o then [] else [done]

/-- The initial states `F 0`, `I`, `C 1` and `O 1`. -/
def initial (k : ℕ) : List (St k) := [fmt 0, zero, carry true, ones true]

/-! ### Blocks and the counter -/

/-- The `k`-bit binary expansion of `j`, least significant bit first. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, j => decide (j % 2 = 1) :: toBits k (j / 2)

/-- Adding the carry `c` to a block, least significant bit first; the final carry is
dropped. -/
def addCarry : Bool → List Bool → List Bool
  | _, [] => []
  | c, b :: B => (b ^^ c) :: addCarry (c && b) B

/-- The record `B # B₁ # ⋯ # Bₘ $` of the blocks `B, B₁, …, Bₘ`. -/
def record (B : List Bool) (Bs : List (List Bool)) : List Tok :=
  B.map bit ++ Bs.flatMap (fun B' => sep :: B'.map bit) ++ [stop]

/-- The record `H = C₀ # C₁ # ⋯ # C_{2^k-1} $` of a `k`-bit binary counter. -/
def counter (k : ℕ) : List Tok :=
  record (toBits k 0) ((List.range' 1 (2 ^ k - 1)).map (toBits k))

@[simp] theorem length_toBits (k j : ℕ) : (toBits k j).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [toBits, ih]

@[simp] theorem addCarry_false (B : List Bool) : addCarry false B = B := by
  induction B with
  | nil => rfl
  | cons b B ih => simp [addCarry, ih]

/-- The expansion of zero is all zeros. -/
theorem toBits_zero (k : ℕ) : toBits k 0 = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih => simp [toBits, ih, List.replicate_succ]

/-- Below the top count, adding one to the expansion of `j` gives that of `j + 1`. -/
theorem addCarry_toBits {k j : ℕ} (hj : j + 1 < 2 ^ k) :
    addCarry true (toBits k j) = toBits k (j + 1) := by
  induction k generalizing j with
  | zero => simp at hj
  | succ k ih =>
    rw [pow_succ] at hj
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h1 : (j + 1) % 2 = 1 := by omega
      have h2 : (j + 1) / 2 = j / 2 := by omega
      simp [toBits, addCarry, h, h1, h2]
    · have h1 : (j + 1) % 2 = 0 := by omega
      have h2 : (j + 1) / 2 = j / 2 + 1 := by omega
      simp [toBits, addCarry, h, h1, h2, ih (j := j / 2) (by omega)]

/-- The expansion of `j < 2^k` is all ones exactly for the top count. -/
theorem all_toBits {k j : ℕ} (hj : j < 2 ^ k) :
    (toBits k j).all id = true ↔ j = 2 ^ k - 1 := by
  induction k generalizing j with
  | zero => simp at hj; simp [toBits, hj]
  | succ k ih =>
    rw [pow_succ] at hj ⊢
    have := ih (j := j / 2) (by omega)
    simp only [toBits, List.all_cons, id, Bool.and_eq_true, decide_eq_true_eq] at this ⊢
    rw [this]
    omega

theorem record_nil (B : List Bool) : record B [] = B.map bit ++ [stop] := by
  simp [record]

theorem record_cons (B B' : List Bool) (Bs : List (List Bool)) :
    record B (B' :: Bs) = B.map bit ++ sep :: record B' Bs := by
  simp [record]

/-- A record of blocks of length `k` has `k + 1` tokens per block. -/
theorem length_record {B : List Bool} {Bs : List (List Bool)} (hB : B.length = k)
    (hBs : ∀ B' ∈ Bs, B'.length = k) : (record B Bs).length = (Bs.length + 1) * (k + 1) := by
  induction Bs generalizing B with
  | nil => simp [record_nil, hB]
  | cons B' Bs ih =>
    rw [record_cons, List.length_append, List.length_cons,
      ih (hBs B' List.mem_cons_self) fun B'' h => hBs B'' (List.mem_cons_of_mem _ h)]
    simp only [List.length_map, hB, List.length_cons]
    ring

/-- Expansions have `k` bits. -/
theorem length_of_mem_map_toBits {l : List ℕ} {B : List Bool} (hB : B ∈ l.map (toBits k)) :
    B.length = k := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hB
  exact length_toBits k j

/-- The counter has `2^k` blocks of `k + 1` tokens. -/
theorem length_counter (k : ℕ) : (counter k).length = (k + 1) * 2 ^ k := by
  rw [counter, length_record (length_toBits k 0) fun _ => length_of_mem_map_toBits]
  simp only [List.length_map, List.length_range']
  rw [Nat.sub_add_cancel Nat.one_le_two_pow, mul_comm]

/-! ### The components in closed form -/

/-- The state `E` runs on every word. -/
@[simp] theorem runs_done (w : List Tok) : Runs (next k) done w := by
  induction w with
  | nil => trivial
  | cons a w ih => exact ⟨done, by simp [next], ih⟩

/-- A checker `W b j` with `j > 0` reads a token other than `$` one step down. -/
theorem next_wait_of_ne {b : Bool} {j : Fin (k + 1)} (hj : (j : ℕ) ≠ 0) {a : Tok}
    (ha : a ≠ stop) : next k (wait b j) a = [wait b (down j)] := by
  cases a with
  | bit => simp [next, hj]
  | sep => simp [next, hj]
  | stop => exact absurd rfl ha

/-- A checker `W b j` survives `j` tokens other than `$` followed by `t` iff `t` is the
bit other than the expected `b`. -/
theorem runs_wait_iff {b : Bool} {u : List Tok} (hu : stop ∉ u) {j : Fin (k + 1)}
    (hj : (j : ℕ) = u.length) (t : Tok) (v : List Tok) :
    Runs (next k) (wait b j) (u ++ t :: v) ↔ t = bit (!b) := by
  induction u generalizing j with
  | nil =>
    simp only [List.length_nil] at hj
    cases t with
    | bit b' => cases b <;> cases b' <;> simp [next, hj]
    | sep => simp [next, hj]
    | stop => simp [next]
  | cons a u ih =>
    simp only [List.length_cons] at hj
    simp only [List.mem_cons, not_or] at hu
    rw [List.cons_append, runs_cons, next_wait_of_ne (by omega) (Ne.symm hu.1)]
    simp only [List.mem_singleton, exists_eq_left]
    exact ih hu.2 (by simp; omega)

/-- A checker dies at a `$` that comes before the expected bit. -/
theorem not_runs_wait_stop {b : Bool} {u : List Tok} (hu : stop ∉ u) {j : Fin (k + 1)}
    (hj : u.length < j) (v : List Tok) : ¬ Runs (next k) (wait b j) (u ++ stop :: v) := by
  induction u generalizing j with
  | nil => simp [next]
  | cons a u ih =>
    simp only [List.length_cons] at hj
    simp only [List.mem_cons, not_or] at hu
    rw [List.cons_append, runs_cons, next_wait_of_ne (by omega) (Ne.symm hu.1)]
    simp only [List.mem_singleton, exists_eq_left]
    exact ih hu.2 (by simp; omega)

/-- The increment checker with carry `c` on a block `B`, then `#` and the next block
`Q ++ R`, where `Q` sits at the offsets of the bits of the current block already read:
some branch survives iff `R` is not `B` plus `c`, or the checker survives from the next
block on. -/
theorem runs_carry_block_iff {B Q R : List Bool} (c : Bool) (hk : B.length + Q.length = k)
    (hR : R.length = B.length) (u : List Tok) :
    Runs (next k) (carry c) (B.map bit ++ sep :: (Q ++ R).map bit ++ u) ↔
      addCarry c B ≠ R ∨ Runs (next k) (carry true) ((Q ++ R).map bit ++ u) := by
  induction B generalizing c Q R with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at hR
    subst hR
    simp [next, addCarry]
  | cons b B ih =>
    cases R with
    | nil => simp at hR
    | cons r R =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hR hk
    have hw := runs_wait_iff (k := k) (b := b ^^ c)
      (u := B.map bit ++ sep :: Q.map bit) (by simp) (j := Fin.last k)
      (by simp; omega) (bit r) (R.map bit ++ u)
    have hb := ih (c && b) (Q := Q ++ [r]) (R := R) (by simp; omega) hR
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append] at hw hb ⊢
    simp only [runs_cons, next, List.mem_cons, exists_eq_or_imp, exists_eq_left,
      List.not_mem_nil, or_false, addCarry]
    rw [hb, hw]
    cases r <;> cases b <;> cases c <;> simp

/-- The increment checker dies on the last block. -/
theorem not_runs_carry_stop {B : List Bool} (c : Bool) (hB : B.length ≤ k) (v : List Tok) :
    ¬ Runs (next k) (carry c) (B.map bit ++ stop :: v) := by
  induction B generalizing c with
  | nil => simp [next]
  | cons b B ih =>
    simp only [List.length_cons] at hB
    simp only [List.map_cons, List.cons_append, runs_cons, next, List.mem_cons,
      exists_eq_or_imp, exists_eq_left, List.not_mem_nil, or_false, not_or]
    exact ⟨ih _ (by omega), not_runs_wait_stop (by simp) (by simp; omega) v⟩

/-- The increment checker dies on a record of one block. -/
theorem not_runs_carry_record_nil {B : List Bool} (hB : B.length ≤ k) (v : List Tok) :
    ¬ Runs (next k) (carry true) (record B [] ++ v) := by
  simpa [record_nil] using not_runs_carry_stop true hB v

/-- On two blocks of length `k`, the increment checker survives iff the second block is
not the first plus one, or it survives on the rest. -/
theorem runs_carry_record_cons {B B' : List Bool} (hB : B.length = k) (hB' : B'.length = k)
    (Bs : List (List Bool)) (v : List Tok) :
    Runs (next k) (carry true) (record B (B' :: Bs) ++ v) ↔
      addCarry true B ≠ B' ∨ Runs (next k) (carry true) (record B' Bs ++ v) := by
  have h := runs_carry_block_iff (k := k) (Q := []) (R := B') true (by simpa using hB)
    (by rw [hB, hB']) (Bs.flatMap (fun B'' => sep :: B''.map bit) ++ [stop] ++ v)
  simp only [List.nil_append] at h
  simpa [record, List.append_assoc] using h

/-- The all-ones checker reads a block of bits. -/
theorem runs_ones_bits (o : Bool) (B : List Bool) (u : List Tok) :
    Runs (next k) (ones o) (B.map bit ++ u) ↔ Runs (next k) (ones (o && B.all id)) u := by
  induction B generalizing o with
  | nil => simp
  | cons b B ih => simp [next, ih, Bool.and_assoc]

/-- On the last block, the all-ones checker survives iff the block is not all ones. -/
theorem runs_ones_record_nil (B : List Bool) (v : List Tok) :
    Runs (next k) (ones true) (record B [] ++ v) ↔ B.all id = false := by
  rw [record_nil, List.append_assoc, runs_ones_bits]
  cases B.all id <;> simp [next]

/-- Before `#`, the all-ones checker survives iff the block is all ones, or it survives on
the rest. -/
theorem runs_ones_record_cons (B B' : List Bool) (Bs : List (List Bool)) (v : List Tok) :
    Runs (next k) (ones true) (record B (B' :: Bs) ++ v) ↔
      B.all id = true ∨ Runs (next k) (ones true) (record B' Bs ++ v) := by
  rw [record_cons, List.append_assoc, runs_ones_bits]
  cases B.all id <;> simp [next]

/-- The zero checker survives iff the first block contains a one. -/
theorem runs_zero_record_iff (B : List Bool) (Bs : List (List Bool)) (v : List Tok) :
    Runs (next k) zero (record B Bs ++ v) ↔ true ∈ B := by
  obtain ⟨t, w, ht, hw⟩ :
      ∃ t w, (t = sep ∨ t = stop) ∧ record B Bs ++ v = B.map bit ++ t :: w := by
    cases Bs with
    | nil => exact ⟨stop, v, Or.inr rfl, by simp [record_nil]⟩
    | cons B' Bs => exact ⟨sep, record B' Bs ++ v, Or.inl rfl, by simp [record_cons]⟩
  rw [hw]
  clear hw
  induction B with
  | nil => rcases ht with rfl | rfl <;> simp [next]
  | cons b B ih => cases b <;> simp [next, ih]

/-- The format checker reads a partial block of bits. -/
theorem runs_fmt_bits {P : List Bool} {p : Fin (k + 1)} (hP : (p : ℕ) + P.length = k)
    (u : List Tok) :
    Runs (next k) (fmt p) (P.map bit ++ u) ↔ Runs (next k) (fmt (Fin.last k)) u := by
  induction P generalizing p with
  | nil =>
    have : p = Fin.last k := Fin.ext (by simpa using hP)
    simp [this]
  | cons b P ih =>
    simp only [List.length_cons] at hP
    have hp : (p : ℕ) < k := by omega
    simp only [List.map_cons, List.cons_append, runs_cons, next, hp, dite_true,
      List.mem_cons, exists_eq_left, List.not_mem_nil, or_false]
    refine ih ?_
    simp only
    omega

/-- The format checker dies on every record of blocks of length `k`. -/
theorem not_runs_fmt_record {B : List Bool} {Bs : List (List Bool)} (hB : B.length = k)
    (hBs : ∀ B' ∈ Bs, B'.length = k) (v : List Tok) :
    ¬ Runs (next k) (fmt 0) (record B Bs ++ v) := by
  induction Bs generalizing B with
  | nil =>
    rw [record_nil, List.append_assoc, runs_fmt_bits (by simpa using hB)]
    simp [next]
  | cons B' Bs ih =>
    rw [record_cons, List.append_assoc, runs_fmt_bits (by simpa using hB)]
    simpa [next] using ih (hBs B' List.mem_cons_self) fun B'' h =>
      hBs B'' (List.mem_cons_of_mem _ h)

/-- Where the format checker dies, it has read the rest of a block and then `$`, or `#`
followed by a word on which it dies again. -/
theorem not_runs_fmt_cases {p : Fin (k + 1)} {w : List Tok} (h : ¬ Runs (next k) (fmt p) w) :
    ∃ P : List Bool, (p : ℕ) + P.length = k ∧ ((∃ v, w = P.map bit ++ stop :: v) ∨
      ∃ w', w = P.map bit ++ sep :: w' ∧ ¬ Runs (next k) (fmt 0) w') := by
  induction w generalizing p with
  | nil => exact absurd trivial h
  | cons t w ih =>
    cases t with
    | bit b =>
      by_cases hp : (p : ℕ) < k
      · simp only [runs_cons, next, hp, dite_true, List.mem_cons, exists_eq_left,
          List.not_mem_nil, or_false] at h
        obtain ⟨P, hP, hw⟩ := ih h
        refine ⟨b :: P, by simp at hP ⊢; omega, ?_⟩
        simpa using hw
      · simp [next, hp] at h
    | sep =>
      by_cases hp : (p : ℕ) = k
      · simp only [runs_cons, next, hp, ite_true, List.mem_cons, exists_eq_left,
          List.not_mem_nil, or_false] at h
        exact ⟨[], by simpa using hp, Or.inr ⟨w, rfl, h⟩⟩
      · simp [next, hp] at h
    | stop =>
      by_cases hp : (p : ℕ) < k
      · simp [next, hp] at h
      · exact ⟨[], by simp; omega, Or.inl ⟨w, rfl⟩⟩

/-- A word on which the format checker dies begins with a record of blocks of length `k`. -/
theorem exists_record_of_not_runs_fmt {w : List Tok} (h : ¬ Runs (next k) (fmt 0) w) :
    ∃ B Bs v, B.length = k ∧ (∀ B' ∈ Bs, B'.length = k) ∧ w = record B Bs ++ v := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    obtain ⟨P, hP, ⟨v, rfl⟩ | ⟨w', rfl, hw'⟩⟩ := not_runs_fmt_cases h
    · exact ⟨P, [], v, by simpa using hP, by simp, by simp [record_nil]⟩
    · obtain ⟨B, Bs, v, hB, hBs, rfl⟩ := ih _ (by subst hn; simp; omega) hw' rfl
      refine ⟨P, B :: Bs, v, by simpa using hP, ?_, by simp [record_cons]⟩
      simpa [hB] using hBs

/-! ### Counting and the main theorem -/

/-- The counting step: from the expansion of `j`, the increment and all-ones checkers
both die exactly on the record of the counts `j, j + 1, …, 2^k - 1`. -/
theorem not_runs_carry_ones_iff {j : ℕ} (hj : j < 2 ^ k) {Bs : List (List Bool)}
    (hBs : ∀ B ∈ Bs, B.length = k) (v : List Tok) :
    (¬ Runs (next k) (carry true) (record (toBits k j) Bs ++ v) ∧
        ¬ Runs (next k) (ones true) (record (toBits k j) Bs ++ v)) ↔
      Bs = (List.range' (j + 1) (2 ^ k - 1 - j)).map (toBits k) := by
  induction Bs generalizing j with
  | nil =>
    rw [runs_ones_record_nil, Bool.not_eq_false, all_toBits hj]
    simp only [not_runs_carry_record_nil (length_toBits k j).le, not_false_eq_true,
      true_and, List.nil_eq, List.map_eq_nil_iff, List.range'_eq_nil_iff]
    omega
  | cons B' Bs ih =>
    have hB' := hBs B' List.mem_cons_self
    have hBs' : ∀ B ∈ Bs, B.length = k := fun B h => hBs B (List.mem_cons_of_mem _ h)
    rw [runs_carry_record_cons (length_toBits k j) hB', runs_ones_record_cons]
    by_cases htop : j = 2 ^ k - 1
    · have : 2 ^ k - 1 - j = 0 := by omega
      simp [this, (all_toBits hj).2 htop]
    · have hj' : j + 1 < 2 ^ k := by omega
      have hall : (toBits k j).all id = false := by
        rw [← Bool.not_eq_true, all_toBits hj]; exact htop
      have hsplit : 2 ^ k - 1 - j = (2 ^ k - 1 - (j + 1)) + 1 := by omega
      rw [addCarry_toBits hj', hall, hsplit, List.range'_succ, List.map_cons,
        List.cons.injEq, ← ih hj' hBs']
      simp only [ne_eq, not_or, not_not, Bool.false_eq_true, false_or]
      constructor
      · rintro ⟨⟨rfl, hc⟩, ho⟩
        exact ⟨rfl, hc, ho⟩
      · rintro ⟨rfl, hc, ho⟩
        exact ⟨⟨rfl, hc⟩, ho⟩

/-- **The counter automaton.** Some initial state has a run on `w` exactly when `w` does
not begin with the counter record `H`. -/
theorem exists_runs_iff (w : List Tok) :
    (∃ q ∈ initial k, Runs (next k) q w) ↔ ¬ counter k <+: w := by
  rw [← not_iff_not, not_not]
  simp only [initial, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, not_or]
  constructor
  · rintro ⟨hF, hI, hC, hO⟩
    obtain ⟨B, Bs, v, hB, hBs, rfl⟩ := exists_record_of_not_runs_fmt hF
    rw [runs_zero_record_iff] at hI
    have hB0 : B = toBits k 0 := by
      rw [toBits_zero, List.eq_replicate_iff]
      exact ⟨hB, fun b hb => by cases b <;> simp_all⟩
    subst hB0
    have hcount := (not_runs_carry_ones_iff (Nat.two_pow_pos k) hBs v).1 ⟨hC, hO⟩
    rw [Nat.sub_zero, zero_add] at hcount
    exact ⟨v, by rw [counter, hcount]⟩
  · rintro ⟨v, rfl⟩
    have hBs : ∀ B ∈ (List.range' 1 (2 ^ k - 1)).map (toBits k), B.length = k :=
      fun _ => length_of_mem_map_toBits
    have hcount := (not_runs_carry_ones_iff (j := 0) (Nat.two_pow_pos k) hBs v).2 (by simp)
    refine ⟨not_runs_fmt_record (length_toBits k 0) hBs v, ?_, hcount⟩
    rw [counter, runs_zero_record_iff, toBits_zero]
    simp

end Counter

end DeciNSSE.Complexity
