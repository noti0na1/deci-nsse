import DeciNSSE.Complexity.Tiling.Packets
import DeciNSSE.Complexity.Tiling.Bits

/-! # Address bits and grid order

## Main declarations

- `Addr.bits` reads the physical address slots in a cell record.
- `Addr.index` is the address in the selected traversal.
- `map_index_order` numbers the cells consecutively from zero.
-/

namespace DeciNSSE.Complexity.Tiling
open Controller
variable {D : Type*}

/-- An address is a column and a row, each below the side length `2 ^ p`. -/
abbrev Addr (p : ℕ) := Fin (2^p) × Fin (2^p)

namespace Addr
variable {p : ℕ}

/-- Number a cell in row-major order for the master or column-major order for the probes. -/
def index (master : Bool) (a : Addr p) :=
  if master then 2^p * a.2.val + a.1.val else 2^p * a.1.val + a.2.val

/-- Read the physical address bit at a slot, with column bits first and row bits second. -/
def bits (a : Addr p) (i : ℕ) :=
  if i < p then a.1.val.testBit i else a.2.val.testBit (i-p)

/-- The significance of an address slot is less than the total number of address bits. -/
theorem rank_lt (master : Bool) {i : ℕ} (hi : i < 2*p) : bitRank p master i < 2*p := by
  unfold bitRank; split_ifs <;> omega

/-- Applying the traversal's bit-rank permutation twice recovers the physical slot. -/
theorem rank_inverse (master : Bool) {i : ℕ} (hi : i < 2*p) :
    bitRank p master (bitRank p master i) = i := by
  unfold bitRank; split_ifs <;> omega

/-- Reading the traversal index at the rank of a slot gives the physical bit stored in that
slot. -/
theorem index_bit (a : Addr p) (master : Bool) (i : ℕ) (hi : i < 2*p) :
    (index master a).testBit (bitRank p master i) = bits a i := by
  cases master <;> simp only [index, bitRank, bits, Bool.false_eq_true, ite_false, ite_true,
    Nat.testBit_two_pow_mul_add _ a.1.isLt, Nat.testBit_two_pow_mul_add _ a.2.isLt]
  all_goals split_ifs <;> simp_all; omega

/-- Every traversal index lies below the number of cells in the square. -/
theorem index_lt (a : Addr p) (master : Bool) : index master a < 2^(2*p) := by
  rw [show 2*p=p+p by omega, pow_add]
  have h₁ := a.1.isLt
  have h₂ := a.2.isLt
  cases master <;> simp only [index, ite_true, Bool.false_eq_true, ite_false] <;>
    first | nlinarith [Nat.mul_le_mul_left (2^p) h₁, Nat.mul_le_mul_left (2^p) h₂]

/-- Within either traversal the index determines both coordinates. -/
theorem index_inj (master : Bool) : Function.Injective (index (p := p) master) := by
  intro x y he
  have hm := congrArg (· % (2^p)) he
  have hd := congrArg (· / (2^p)) he
  cases master <;> simp [index, Nat.mod_eq_of_lt, Nat.mul_add_div (Nat.two_pow_pos p),
    Nat.div_eq_of_lt, x.1.isLt, x.2.isLt, y.1.isLt, y.2.isLt] at hm hd <;>
    apply Prod.ext <;> apply Fin.ext <;> assumption

/-- Carry into bit `i` is present exactly when all less significant bits are one. -/
theorem increment_testBit (v i : ℕ) :
    (v+1).testBit i = (v.testBit i ^^ decide (∀ j : Fin i, v.testBit j = true)) := by
  induction i generalizing v with
  | zero =>
    simp [Nat.testBit_zero]
    apply Bool.eq_iff_iff.mpr; simp; omega
  | succ i ih =>
    have carry : (∀ j : Fin (i+1), v.testBit j = true) ↔ v.testBit 0 = true ∧
        ∀ j : Fin i, (v/2).testBit j = true := by
      rw [Fin.forall_fin_succ]; simp [Nat.testBit_div_two]
    have eq : decide (∀ j : Fin (i+1), v.testBit j = true) =
        decide (v.testBit 0 = true ∧ ∀ j : Fin i, (v/2).testBit j = true) :=
      Bool.eq_iff_iff.mpr (by simpa using carry)
    rw [Nat.testBit_succ, Nat.testBit_succ, eq]
    by_cases ho : v%2=1
    · rw [show (v+1)/2 = v/2+1 by omega, ih]
      simp [Nat.testBit_zero, ho]
    · rw [show (v+1)/2 = v/2 by omega]; simp [Nat.testBit_zero, ho]

/-- Two numbers below `2 ^ p` are equal if their first `p` bits agree. -/
theorem bits_ext {x y : ℕ} (hx : x < 2^p) (hy : y < 2^p)
    (he : ∀ i < p, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < p
  · exact he i hi
  · have h' := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi)
    rw [Nat.testBit_lt_two_pow (hx.trans_le h'), Nat.testBit_lt_two_pow (hy.trans_le h')]

/-- Equality of all physical address bits implies equality of the cells. -/
theorem bits_inj {a b : Addr p} (h : ∀ i < 2*p, bits a i = bits b i) : a = b := by
  apply Prod.ext <;> apply Fin.ext
  · apply bits_ext a.1.isLt b.1.isLt
    intro j hj; simpa [bits,hj] using h j (by omega)
  · apply bits_ext a.2.isLt b.2.isLt
    intro j hj; simpa [bits] using h (j+p) (by omega)

/-- A coordinate is zero exactly when all of its `p` bits are zero. -/
theorem zero_bits {x : Fin (2^p)} : (∀ j < p, x.val.testBit j = false) ↔ x.val = 0 := by
  constructor
  · intro h; exact bits_ext x.isLt (Nat.two_pow_pos p) (by simpa using h)
  · intro h; simp [h]

/-- A coordinate is the last one on its axis exactly when all of its `p` bits are one. -/
theorem last_bits {x : Fin (2^p)} : (∀ j < p, x.val.testBit j = true) ↔ x.val + 1 = 2^p := by
  have pos := Nat.two_pow_pos p
  constructor
  · intro h
    have he : x.val = 2^p-1 := bits_ext x.isLt (by omega) (by intro i hi; simp [h i hi,hi])
    omega
  · intro h j hj
    rw [show x.val=2^p-1 by omega]; simp [hj]

end Addr

/-- List the addresses in traversal order, with the master advancing through rows and the probes
through columns. -/
def order (s : ℕ) (master : Bool) := if master then rowOrder s else colOrder s

/-- The traversal indices of the ordered cells are the consecutive integers starting at zero. -/
theorem map_index_order (p : ℕ) (master : Bool) :
    ((order (2^p) master).map (Addr.index master)) = List.range (2^(2*p)) := by
  let s := 2^p
  have one (x : Fin s) :
      (List.finRange s).map (fun y => s*x.val + y.val) = List.range' (s*x.val) s := by
    apply List.ext_getElem <;> simp
  have rows (k : ℕ) :
      ((List.range k).flatMap (fun i => List.range' (s*i) s)) = List.range (s*k) := by
    induction k with
    | zero => simp
    | succ k ih => rw [List.range_succ, List.flatMap_append, ih, Nat.mul_succ, List.range_add]
                   simp [List.range'_eq_map_range]
  have idx : (List.finRange s).flatMap (fun x => List.range' (s*x.val) s) = List.range (s*s) := by
    have he : (List.finRange s).map Fin.val = List.range s := by apply List.ext_getElem <;> simp
    have h := rows s
    rw [← he, List.flatMap_map] at h
    exact h
  rw [show 2^(2*p) = s*s by dsimp [s]; rw [show 2*p=p+p by omega, pow_add]]
  cases master <;>
    simp only [order, rowOrder, colOrder, Bool.false_eq_true, ite_false, ite_true, List.map_flatMap,
      List.map_map, Function.comp_def, Addr.index] <;>
    change (List.finRange s).flatMap
      (fun a => (List.finRange s).map (fun x => s*a.val+x.val)) = _ <;>
    simpa only [one] using idx

/-- The cell at position `i` in either traversal has index `i`. -/
theorem index_order_get (p : ℕ) (master : Bool) (i : ℕ) (hi : i < (order (2^p) master).length) :
    Addr.index master (p := p) (order (2^p) master)[i] = i := by
  have he := congrArg (fun xs : List ℕ => xs[i]?) (map_index_order p master)
  have hl := congrArg List.length (map_index_order p master)
  simp only [List.length_map, List.length_range] at hl
  simpa [List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by simpa [hl] using hi : i < (List.range (2^(2*p))).length)] using he

end DeciNSSE.Complexity.Tiling
