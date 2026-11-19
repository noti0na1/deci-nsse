import DeciNSSE.Complexity.Tiling.GridFacts
import DeciNSSE.Complexity.Tiling.PhaseRuns

/-! # Registers while reading a cell record

## Main declarations

- `slot_run` evaluates each address slot for every bit checker.
- `at_bit_forced` and `at_tile_forced` constrain the symbols in a successful run.
- `bits_flags` and `bits_next` recover the four boundary flags and the next expected bit.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
variable {D : Type*} [DecidableEq D] (I : Square D)

/-- Spell the record marker followed by the first `n` physical bits of an address. -/
def slotText (a : Addr I.p) (n : ℕ) : List (Letter D) :=
  [.data .record] ++ (List.range n).map (fun i => .data (.bit (a.bits i)))

/-- Test a Boolean predicate at all slot indices below `n`. -/
def bitAll (n : ℕ) (f : ℕ → Bool) := (List.range n).all f

/-- Compute the registers after the record marker and `n` bits of the given address. -/
def slots (r : Registers D) (a : Addr I.p) (n : ℕ) : Registers D :=
  { r with
    slot := n+1
    color := some (.data (if n=0 then .record else .bit (a.bits (n-1))))
    current := if r.copy < n then a.bits r.copy else false
    carry := bitAll n (fun i =>
      !decide (bitRank I.p r.master i < bitRank I.p r.master r.copy) || a.bits i)
    colZero := bitAll n (fun i => i ≥ I.p || !a.bits i)
    colLast := bitAll n (fun i => i ≥ I.p || a.bits i)
    rowZero := bitAll n (fun i => i < I.p || !a.bits i)
    rowLast := bitAll n (fun i => i < I.p || a.bits i) }

/-- Test whether the checker may start a record after the preceding address. -/
def canStart (r : Registers D) := !(r.copy == 2*I.p && r.seen && r.colLast && r.rowLast)

/-- At a record boundary the marker initializes the bit slots if another record is allowed. -/
theorem slot_record (r : Registers D) (hr : r.slot = 0) (a : Addr I.p) :
    tokenStep I (some r) (.data .record) =
      if canStart I r then some (some (slots I r a 0)) else none := by
  simp [tokenStep,slots,bitAll,hr,canStart]; split <;> simp_all

private theorem slot_bit (r : Registers D) (a : Addr I.p) {n : ℕ} (hn : n < 2*I.p) :
    tokenStep I (some (slots I r a n)) (.data (.bit (a.bits n))) =
      if r.copy = n ∧ a.bits n ≠ r.expected then none else some (some (slots I r a (n+1))) := by
  have tail : n+1 ≠ 2*I.p+2 := by omega
  have small : n+1 ≤ 2*I.p := by omega
  have update : (if n=r.copy then a.bits n else if r.copy<n then a.bits r.copy else false) =
      (if r.copy<n+1 then a.bits r.copy else false) := by split_ifs <;> simp_all <;> omega
  have bad : (r.copy < 2*I.p && n == r.copy && a.bits n != r.expected) =
      decide (r.copy=n ∧ a.bits n ≠ r.expected) := by
    apply Bool.eq_iff_iff.mpr
    simp; grind
  simp only [tokenStep, slots, Option.bind_eq_bind, Option.bind, tail, ite_false, Nat.succ_ne_zero,
    small, ite_true, readBit, Nat.add_sub_cancel, bitAll, List.range_succ, List.all_append,
    List.all_cons, List.all_nil, Bool.and_true,bad,decide_eq_true_eq,update]
  by_cases h : r.copy=n ∧ a.bits n ≠ r.expected
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h]; rfl

/-- A prefix through `n` address bits succeeds if a record may start and the selected bit, when
already read, matches its expected value. -/
theorem slot_run (r : Registers D) (hr : r.slot=0) (a : Addr I.p) {n : ℕ} (hn : n ≤ 2*I.p) :
    run I (some r) (slotText I a n) =
      if canStart I r && (r.copy ≥ n || a.bits r.copy == r.expected)
      then some (some (slots I r a n)) else none := by
  induction n with
  | zero => simp [slotText,run,slot_record I r hr a]
  | succ n ih =>
    have text : slotText I a (n+1) = slotText I a n ++ [.data (.bit (a.bits n))] := by
      simp [slotText,List.range_succ]
    rw [text,run_append,ih (by omega)]
    simp only [run]
    have st := slot_bit I r a (by omega : n<2*I.p)
    by_cases start : canStart I r <;> by_cases lt : r.copy < n <;> by_cases eq : r.copy=n <;>
      by_cases bit : a.bits r.copy = r.expected <;>
      simp_all <;> grind

omit [DecidableEq D] in
/-- A complete encoded record consists of the marker and all address slots followed by the tile
token. -/
theorem encoded_record (a : Addr I.p) (d : D) :
    (record I.p a.1 a.2 d).map Token.data = slotText I a (2*I.p) ++ [.data (.tile d)] := by
  simp [record,slotText,show 2*I.p=I.p+I.p by omega,List.range_add,List.map_map,
    Function.comp_def,List.append_assoc,Addr.bits,Nat.add_comm I.p]
  omega

/-- At its assigned slot a successful bit checker forces the token to spell the expected address
bit. -/
theorem at_bit_forced (r : Registers D) (a : Addr I.p) {j} (hj : j < 2*I.p)
    (guard : r.copy=j) (expect : r.expected=a.bits j) {x q}
    (h : tokenStep I (some (slots I r a j)) x = some q) : x = .data (.bit (a.bits j)) := by
  have idx : (slots I r a j).slot = j+1 := rfl
  have hn : j ≠ 2*I.p+1 := by omega
  rcases x with (b | _ | d) | _ | _ <;> simp [tokenStep,idx,hn,show j+1≤2*I.p by omega] at h
  by_contra! ne
  have hbit : b ≠ a.bits j := fun he => ne (he ▸ rfl)
  simp [readBit,slots,guard,expect,hj,hbit] at h

/-- After all address slots, a successful transition must read a tile token. -/
theorem at_tile_forced (r : Registers D) (a : Addr I.p) {x q}
    (h : tokenStep I (some (slots I r a (2*I.p))) x = some q) : ∃ d, x = .data (.tile d) := by
  rcases x with (b | _ | d) | _ | _ <;> simp_all [tokenStep,slots]

omit [DecidableEq D]

private theorem col_flag (a : Addr I.p) (b : Bool) :
    bitAll (2*I.p) (fun i => decide (i ≥ I.p) || (a.bits i == b)) = true ↔
      ∀ i < I.p, a.1.val.testBit i = b := by
  simp only [bitAll,List.all_eq_true,List.mem_range,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · intro h i hi
    simpa [Addr.bits,hi] using (h i (by omega)).resolve_left (by omega)
  · intro h i _
    by_cases hi : i < I.p
    · exact Or.inr (by simpa [Addr.bits,hi] using h i hi)
    · exact Or.inl (by omega)

private theorem row_flag (a : Addr I.p) (b : Bool) :
    bitAll (2*I.p) (fun i => decide (i < I.p) || (a.bits i == b)) = true ↔
      ∀ i < I.p, a.2.val.testBit i = b := by
  simp only [bitAll,List.all_eq_true,List.mem_range,Bool.or_eq_true,decide_eq_true_eq,beq_iff_eq]
  constructor
  · intro h i hi
    simpa [Addr.bits] using (h (i+I.p) (by omega)).resolve_left (by omega)
  · intro h i hlen
    by_cases hi : i < I.p
    · exact Or.inl hi
    · exact Or.inr (by simpa [Addr.bits,hi] using h (i-I.p) (by omega))

/-- The four completed address flags identify zero and the last coordinate on each of the two
axes. -/
theorem bits_flags (r : Registers D) (a : Addr I.p) :
    let s := slots I r a (2*I.p)
    s.colZero = decide (a.1.val = 0) ∧ s.colLast = decide (a.1.val+1 = 2^I.p) ∧
    s.rowZero = decide (a.2.val = 0) ∧ s.rowLast = decide (a.2.val+1 = 2^I.p) := by
  dsimp only
  refine ⟨Bool.eq_iff_iff.mpr ?_,Bool.eq_iff_iff.mpr ?_,
    Bool.eq_iff_iff.mpr ?_,Bool.eq_iff_iff.mpr ?_⟩
  · simpa [slots] using (col_flag I a false).trans Addr.zero_bits
  · simpa [slots] using (col_flag I a true).trans Addr.last_bits
  · simpa [slots] using (row_flag I a false).trans Addr.zero_bits
  · simpa [slots] using (row_flag I a true).trans Addr.last_bits

/-- The selected bit XOR its carry is that bit of the successor traversal index. -/
theorem bits_next (r : Registers D) (a : Addr I.p) (guard : r.copy < 2*I.p) :
    let s := slots I r a (2*I.p)
    (s.current ^^ s.carry) = (Addr.index r.master a+1).testBit (bitRank I.p r.master r.copy) := by
  dsimp [slots]
  rw [ite_eq_left guard, Addr.increment_testBit, ← Addr.index_bit a r.master r.copy guard]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [bitAll]
  constructor
  · intro h j
    let i := bitRank I.p r.master j.val
    have hj := j.isLt
    have small := Addr.rank_lt r.master guard
    have hi : i < 2*I.p := Addr.rank_lt _ (by omega)
    have inv : bitRank I.p r.master i = j := Addr.rank_inverse _ (by omega)
    have bit := h i hi
    rw [inv] at bit
    rw [← inv,Addr.index_bit _ _ _ hi]
    grind
  · intro h i hi
    by_cases below : bitRank I.p r.master i < bitRank I.p r.master r.copy
    · exact Or.inr (by rw [← Addr.index_bit _ _ _ hi]; exact h ⟨_,below⟩)
    · exact Or.inl (by omega)

end DeciNSSE.Complexity.Tiling.Controller
