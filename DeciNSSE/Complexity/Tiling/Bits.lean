import DeciNSSE.Complexity.Tiling.FixedCode

/-! # Fixed-width binary numerals

## Main declarations

- `digits` spells a natural number most significant bit first.
- `binaryCode` numbers proper prefixes in breadth-first order and decodes
  leaves by their numeric value.
-/

namespace DeciNSSE.Complexity.Tiling
namespace Bits

/-- Spell `x` using its low `k` bits, most significant bit first. -/
def digits (k x : ℕ) : List (Fin 2) :=
  (List.range k).reverse.map fun i => if x.testBit i then 1 else 0

/-- Read a binary word as a natural number, most significant bit first. -/
def value (s : List (Fin 2)) := s.foldl (fun (n : ℕ) b => 2*n + b.val) 0

/-- A binary spelling of width `k` has exactly `k` letters. -/
@[simp] theorem length_digits (k x : ℕ) : (digits k x).length = k := by simp [digits]

/-- Appending a bit doubles the previous value and adds the bit. -/
@[simp] theorem value_snoc (s : List (Fin 2)) (b : Fin 2) :
    value (s ++ [b]) = 2 * value s + b.val := by simp [value, List.foldl_append]

private theorem digits_succ (k x : ℕ) : digits (k+1) x =
    digits k (x/2) ++ [⟨x%2, Nat.mod_lt _ (by decide)⟩] := by
  simp only [digits, List.range_succ_eq_map, List.reverse_cons, ← List.map_reverse,
    List.map_append, List.map_map, List.map_singleton]
  congr 1
  · apply List.map_inj_left.mpr; intro i _
    simp [Nat.testBit_div_two]
  · congr 1
    rw [Nat.testBit_zero]
    split <;> apply Fin.ext <;> simp_all

/-- Spelling a word's value at its original width recovers the word, including leading zeros. -/
theorem digits_value (s : List (Fin 2)) : digits s.length (value s) = s := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s b ih =>
    rw [List.length_append, List.length_singleton, digits_succ, value_snoc]
    rw [show (2 * value s + b.val) / 2 = value s by omega, ih]
    congr 2; apply Fin.ext; simp

/-- A number below `2 ^ k` is recovered from its spelling of width `k`. -/
theorem value_digits {k x : ℕ} (hx : x < 2 ^ k) : value (digits k x) = x := by
  induction k generalizing x with
  | zero =>
    have : x = 0 := by simpa using hx
    subst x; rfl
  | succ k ih =>
    rw [digits_succ, value_snoc, ih (by rw [pow_succ] at hx; omega)]
    simp; omega

/-- The value of a binary word is less than two raised to its length. -/
theorem value_lt (s : List (Fin 2)) : value s < 2 ^ s.length := by
  induction s using List.reverseRecOn with
  | nil => decide
  | append_singleton s b ih =>
    rw [List.length_append, List.length_singleton, pow_succ, value_snoc]; omega

private def phase (p : List (Fin 2)) := 2 ^ p.length - 1 + value p
private def phases (k : ℕ) := 2 ^ k - 1

private theorem phase_snoc (p : List (Fin 2)) (b : Fin 2) :
    phase (p ++ [b]) = 2 * phase p + 1 + b.val := by
  have := Nat.two_pow_pos p.length
  simp only [phase, List.length_append, List.length_singleton, pow_succ, value_snoc]; omega

private theorem phase_lt (p : List (Fin 2)) (k : ℕ) : phase p < phases k ↔ p.length < k := by
  have hp := value_lt p
  have hpos := Nat.two_pow_pos p.length
  have hpos' := Nat.two_pow_pos k
  unfold phase phases
  constructor
  · intro h; by_contra! hle
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    omega
  · intro h
    have hl := Nat.pow_le_pow_right (by decide : 0 < 2) h
    rw [pow_succ] at hl
    omega

/-- Extend a proper binary prefix by one bit, moving to a new prefix state or decoding the
completed numeral. -/
def parse {α : Type*} (k : ℕ) (decode : ℕ → Option α) (j : ℕ) (b : Fin 2) :
    Option (ℕ ⊕ α) :=
  let next := 2*j + 1 + b.val
  if next < 2 ^ k - 1 then some (.inl next) else (decode (next - (2 ^ k - 1))).map Sum.inr

/-- Build a fixed-width binary code for symbols numbered below `2 ^ k`, given a decoder for the
assigned numbers. -/
def binaryCode {α : Type*} (k : ℕ) (hk : 0 < k) (number : α → ℕ)
    (decode : ℕ → Option α)
    (bound : ∀ a, number a < 2 ^ k) (inverse : ∀ i a, decode i = some a ↔ number a = i) :
    FixedCode α (Fin 2) where
  spell a := digits k (number a)
  width := k
  pos := hk
  length a := length_digits ..
  inj := by
    intro x y he
    have eq := congrArg value he
    rw [value_digits (bound x), value_digits (bound y)] at eq
    exact Option.some.inj (((inverse _ x).mpr eq).symm.trans ((inverse _ y).mpr rfl))
  phases := phases k
  parse := parse k decode
  partialWord p i := p.length < k ∧ phase p = i
  initial := ⟨hk, rfl⟩
  bounded := fun {p i} ⟨hl,he⟩ => he ▸ (phase_lt p k).mpr hl
  boundary := by
    intro p h
    by_contra ne
    have := (phase_lt p 1).mp (by rw [h.2]; decide)
    simp_all
  advance := by
    rintro p _ b v ⟨hl,rfl⟩ h
    change (if 2*phase p+1+b.val < phases k then _ else _) = some v at h
    rw [← phase_snoc] at h
    split at h
    · next he => cases h; exact ⟨(phase_lt _ _).mp he, rfl⟩
    · next he =>
      have len : (p++[b]).length = k := by
        rw [phase_lt] at he; simp at he ⊢; omega
      have eq : phase (p ++ [b]) - (2^k-1) = value (p ++ [b]) := by simp [phase, len]
      simp only [eq, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      change digits k (number a) = p ++ [b]
      rw [(inverse _ _).mp ha, ← len, digits_value]
  complete := by
    rintro a p b r _ ⟨hl,rfl⟩ he
    have len := congrArg List.length he
    rw [length_digits, List.length_append, List.length_cons] at len
    by_cases hr : r = []
    · subst r
      have leq : (p ++ [b]).length = k := by simp_all
      have ge : ¬phase (p ++ [b]) < phases k := by rw [phase_lt, leq]; omega
      have eq : phase (p ++ [b]) - (2^k-1) = value (p ++ [b]) := by simp [phase, leq]
      have hv := congrArg value he
      rw [value_digits (bound a)] at hv
      simp only [ite_true, parse, ← phase_snoc]
      change (if phase _ < phases k then _ else _) = _
      rw [ite_eq_right ge, eq, (inverse _ _).mpr hv]; rfl
    · have lt : (p++[b]).length < k := by have := List.length_pos_iff.mpr hr; simp_all
      have bnd := (phase_lt _ _).mpr lt
      simp only [hr, ite_false]
      refine ⟨phase (p++[b]), ?_, lt, rfl⟩
      change (if 2*phase p+1+b.val < phases k then _ else _) = _
      rw [← phase_snoc, ite_eq_left bnd]

end Bits
end DeciNSSE.Complexity.Tiling
