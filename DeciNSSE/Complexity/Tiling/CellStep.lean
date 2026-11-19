import DeciNSSE.Complexity.Tiling.RecordRun

/-! # Record boundaries in the two traversals

## Main declarations

- `Frame` describes the registers of one checker at a record boundary.
- `read_cell` computes one complete authenticated-address record including its probe payload.
- `next_frame` propagates the boundary invariant to the successor address.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
variable {D : Type*} [DecidableEq D] (I : Square D)

/-- The square of side `2 ^ p` contains `2 ^ (2*p)` cells. -/
abbrev total (p : ℕ) := 2^(2*p)

/-- The checker index ranges over the physical address bits and one final tile checker. -/
abbrev Guard (p : ℕ) := Fin (2*p+1)

/-- At a record boundary the registers specify the checker, traversal, next address and previous
tile. The capped counter records progress along the initial row. -/
def Frame (r : Registers D) (j : Guard I.p) (m : Bool) (i : ℕ) (prev : Option D) : Prop :=
  r.copy = j.val ∧ r.master = m ∧ r.slot = 0 ∧ r.seen = decide (i ≠ 0) ∧
    (i ≠ 0 → (r.colLast && r.rowLast) = decide (i = total I.p)) ∧
    (j.val < 2*I.p → r.expected = i.testBit (bitRank I.p m j.val)) ∧
    (j.val = 2*I.p → r.previous = prev) ∧
    r.count = (if m then min (min i I.side) I.initial.length else 0)

omit [DecidableEq D] in
/-- Fresh registers satisfy the boundary conditions at traversal index zero. -/
theorem initial_frame (j : Guard I.p) (m) : Frame I {copy := j, master := m} j m 0 none := by
  simp [Frame]

/-- A tile at the given address satisfies every applicable side condition, including the
initial-row prefix. -/
def Boundary (a : Addr I.p) (d : D) : Prop :=
  (a.2.val=0 → d ∈ I.initial[a.1.val]?.getD I.rest) ∧
  (a.1.val=0 → d ∈ I.left) ∧ (a.1.val+1=I.side → d ∈ I.right) ∧
    (a.2.val+1=I.side → d ∈ I.bottom)

/-- Within a row or column the previous tile and the current tile must satisfy the directed
compatibility relation for that traversal. -/
def Neighbor (m : Bool) (prev : Option D) (a : Addr I.p) (d : D) : Prop :=
  (if m then a.1.val else a.2.val) ≠ 0 →
    ∀ b, prev = some b → (b,d) ∈ (if m then I.horizontal else I.vertical)

/-- A master cell must satisfy its boundary tests, and each traversal must satisfy its neighbor
test. -/
def CellOK (m : Bool) (prev : Option D) (a : Addr I.p) (d : D) :=
  (m = true → Boundary I a d) ∧ Neighbor I m prev a d

/-- Encode a cell record, including its trailing data and stop delimiter when it is a probe. -/
def cellText (m : Bool) (a : Addr I.p) (d : D) (payload : List (CellLetter D)) : List (Letter D) :=
  (record I.p a.1 a.2 d).map Token.data ++ if m then [] else payload.map Token.data ++ [.stop]

private def tileOK (s : Registers D) (d : D) : Bool :=
  !(s.master && !boundaryOK I s d ||
    s.copy == 2*I.p && !(if s.master then s.colZero else s.rowZero) &&
      !s.previous.all (fun prev => (prev,d) ∈ (if s.master then I.horizontal else I.vertical)))

private def tileState (s : Registers D) (d : D) : Registers D :=
  {s with slot := if s.master then 0 else 2*I.p+2, seen := true, color := some (.data (.tile d))
          expected := s.current ^^ s.carry, previous := if s.copy = 2*I.p then some d else none
          count := if s.master && s.rowZero then min (s.count+1) I.initial.length else s.count}

/-- Compute the registers at the next record boundary after reading the given cell and tile. -/
def nextState (r : Registers D) (a : Addr I.p) (d : D) : Registers D :=
  {tileState I (slots I r a (2*I.p)) d with
    slot := 0, color := if r.master then some (.data (.tile d)) else some .stop}

private theorem read_tile_eq (s : Registers D) (d : D) :
    readTile I s d = if tileOK I s d then some (tileState I s d) else none := by
  let bad := s.master && !boundaryOK I s d ||
    s.copy == 2*I.p && !(if s.master then s.colZero else s.rowZero) &&
    !s.previous.all (fun prev => (prev,d) ∈ (if s.master then I.horizontal else I.vertical))
  change (if bad then none else some (tileState I s d)) = if !bad then _ else _
  cases bad <;> rfl

private theorem tile_step (r : Registers D) (a : Addr I.p) (d : D) :
    let s := slots I r a (2*I.p)
    tokenStep I (some s) (.data (.tile d)) =
      if tileOK I s d then some (some (tileState I s d)) else none := by
  dsimp only
  have slot : (slots I r a (2*I.p)).slot = 2*I.p+1 := rfl
  simp [tokenStep,slot,read_tile_eq]
  split <;> rfl

private theorem payload_ends (r : Registers D) (hp : r.slot = 2*I.p+2) (v : List (CellLetter D)) :
    run I (some r) (v.map Token.data ++ [.stop]) =
      some (some {r with slot := 0,color := some .stop}) := by
  induction v generalizing r with
  | nil => simp [run,tokenStep,hp]
  | cons a v ih => simpa [run,tokenStep,hp] using ih {r with color := some (.data a)} hp

omit [DecidableEq D] in
private theorem index_last (a : Addr I.p) (m : Bool) :
    a.1.val+1 = I.side ∧ a.2.val+1 = I.side ↔ Addr.index m a+1 = total I.p := by
  let s := I.side
  have bound (x y : Fin s) : x.val+1=s ∧ y.val+1=s ↔ s*y.val+x.val+1=s*s := by
    constructor
    · rintro ⟨hx,hy⟩; nlinarith [congrArg (s * ·) hy]
    · intro h
      have := Nat.mul_le_mul_left s y.isLt
      by_cases eq : y.val+1=s
      · exact ⟨by nlinarith [congrArg (s * ·) eq],eq⟩
      · have lt : y.val+2 ≤ s := by omega
        have := Nat.mul_le_mul_left s lt
        nlinarith [x.isLt]
  rw [show total I.p = s*s by dsimp [total,s]; rw [show 2*I.p=I.p+I.p by omega,pow_add]]
  cases m
  · exact and_comm.trans (bound _ _)
  · exact bound _ _

omit [DecidableEq D] in
private theorem index_first_row (a : Addr I.p) :
    a.2.val=0 ↔ Addr.index true a < I.side := by
  simp only [Addr.index,ite_true]
  constructor
  · intro e; simp [e]
  · intro h; by_contra! ne
    have := Nat.mul_le_mul_left I.side (show 1 ≤ a.2.val by omega)
    change _ < 2^I.p at h
    dsimp [Square.side] at this
    omega

omit [DecidableEq D] in
/-- Before the last address has been consumed, a checker at a record boundary may start another
record. -/
theorem can_start {r : Registers D} {j : Guard I.p} {m i prev} (h : Frame I r j m i prev)
    (hi : i < total I.p) : canStart I r = true := by
  obtain ⟨_,_,_,seen,last,_⟩ := h
  by_cases hz : i=0
  · simp [canStart,seen,hz]
  · simp [canStart,Bool.and_assoc,seen,hz,last hz,hi.ne]

/-- The expected address is read successfully through any prefix of its physical bit slots. -/
theorem slot_success {r : Registers D} {j : Guard I.p} {m i prev} (h : Frame I r j m i prev)
    (a : Addr I.p) (index : Addr.index m a = i) {k} (hk : k ≤ 2*I.p) :
    run I (some r) (slotText I a k) = some (some (slots I r a k)) := by
  have start := can_start I h (index ▸ Addr.index_lt a m)
  obtain ⟨copy,_,zero,_,_,expect,_,_⟩ := h
  rw [slot_run I r zero a hk,start,copy]
  by_cases lt : j.val < k
  · have small := lt.trans_le hk
    rw [expect small,← index,Addr.index_bit a m _ small]; simp
  · simp [show k ≤ j.val by omega]

private theorem boundary_eq {r : Registers D} {j : Guard I.p} {i prev}
    (fr : Frame I r j true i prev)
    (a : Addr I.p) (index : Addr.index true a=i) (d) :
    boundaryOK I (slots I r a (2*I.p)) d = true ↔ Boundary I a d := by
  obtain ⟨cz,cl,rz,rl⟩ := bits_flags I r a
  have count := fr.2.2.2.2.2.2.2
  change r.count = min (min i I.side) I.initial.length at count
  have carry (hy : a.2.val=0) : I.initial[r.count]? = I.initial[a.1.val]? := by
    have eq : i=a.1.val := by simpa [Addr.index,hy] using index.symm
    rw [count,eq,Nat.min_eq_left a.1.isLt.le]
    by_cases small : a.1.val ≤ I.initial.length
    · rw [Nat.min_eq_left small]
    · rw [Nat.min_eq_right (by omega),
        List.getElem?_eq_none (by omega : I.initial.length ≤ a.1.val)]
      simp
  unfold boundaryOK
  rw [rz,cz,rl,cl]
  change ((!(decide (a.2.val=0))
    || decide (d ∈ I.initial[r.count]?.getD I.rest)) && _ && _ && _) = true ↔ _
  by_cases hy : a.2.val=0
  · rw [carry hy]; simp [Boundary,hy,← imp_iff_not_or,and_assoc]
  · simp [Boundary,hy,← imp_iff_not_or,and_assoc]

private theorem tile_eq {r : Registers D} {j : Guard I.p} {m i prev} (fr : Frame I r j m i prev)
    (a : Addr I.p) (index : Addr.index m a=i) (d) :
    tileOK I (slots I r a (2*I.p)) d = true ↔
      (m=true → Boundary I a d) ∧ (j.val=2*I.p → Neighbor I m prev a d) := by
  obtain ⟨cz,_,rz,_⟩ := bits_flags I r a
  have copy : (slots I r a (2*I.p)).copy = j := fr.1
  have master : (slots I r a (2*I.p)).master = m := fr.2.1
  have previous (hj : j.val=2*I.p) : (slots I r a (2*I.p)).previous = prev := fr.2.2.2.2.2.2.1 hj
  unfold tileOK
  rw [copy,master,rz,cz]
  cases m with
  | false =>
    by_cases last : j.val = 2*I.p
    · rw [previous last]
      cases prev <;> simp [Neighbor,last]
      tauto
    · simp [last]
  | true =>
    have bnd := boundary_eq I fr a index d
    by_cases last : j.val = 2*I.p
    · rw [previous last]
      cases prev <;> simp [Neighbor,last,bnd]
      tauto
    · simp [last,bnd]

open Classical in
/-- Reading a whole cell reaches the next boundary exactly when that checker's boundary and
adjacency tests pass. -/
theorem read_cell {r : Registers D} {j : Guard I.p} {m i prev} (fr : Frame I r j m i prev)
    (a : Addr I.p) (index : Addr.index m a=i) (d payload) :
    run I (some r) (cellText I m a d payload) =
      if (m=true → Boundary I a d) ∧ (j.val=2*I.p → Neighbor I m prev a d)
      then some (some (nextState I r a d)) else none := by
  classical
  rw [cellText,encoded_record,List.append_assoc,run_append,slot_success I fr a index le_rfl]
  simp only [Option.bind_some, List.singleton_append, run, tile_step]
  by_cases ok : tileOK I (slots I r a (2*I.p)) d = true
  · rw [ite_eq_left ok,ite_eq_left ((tile_eq I fr a index d).mp ok)]
    cases m with
    | true => simp [run,nextState,tileState,slots,fr.2.1]
    | false =>
      let s := tileState I (slots I r a (2*I.p)) d
      have slot : s.slot=2*I.p+2 := by simp [s,tileState,slots,fr.2.1]
      simpa [nextState,fr.2.1,s] using payload_ends I s slot payload
  · rw [ite_eq_right ok,ite_eq_right (fun h => ok ((tile_eq I fr a index d).mpr h))]
    rfl

omit [DecidableEq D] in
/-- Completing the record for the current address advances the boundary invariant by one cell
and remembers its tile. -/
theorem next_frame {r : Registers D} {j : Guard I.p} {m i prev} (fr : Frame I r j m i prev)
    (a : Addr I.p) (index : Addr.index m a=i) (d : D) :
    Frame I (nextState I r a d) j m (i+1) (some d) := by
  obtain ⟨copy,master,_,_,_,_,_,count⟩ := fr
  let s := slots I r a (2*I.p)
  obtain ⟨cz,cl,rz,rl⟩ := bits_flags I r a
  refine ⟨copy,master,rfl,by simp [nextState,tileState],?_,?_,?_,?_⟩
  · intro _
    change ((slots I r a (2*I.p)).colLast && (slots I r a (2*I.p)).rowLast) = _
    rw [cl,rl]
    apply Bool.eq_iff_iff.mpr
    simpa [←index] using index_last I a m
  · intro small
    change ((slots I r a (2*I.p)).current ^^ (slots I r a (2*I.p)).carry) = _
    rw [bits_next I r a (copy ▸ small),copy,master,index]
  · intro last
    simp [nextState,tileState,slots,copy,last]
  · change (if r.master && (slots I r a (2*I.p)).rowZero
        then min (r.count+1) I.initial.length else r.count) = _
    rw [rz,master,count]
    cases m with
    | false => simp
    | true =>
      have eq := index_first_row I a
      rw [index] at eq
      by_cases row : a.2.val=0 <;> simp [row] <;> omega

end DeciNSSE.Complexity.Tiling.Controller
