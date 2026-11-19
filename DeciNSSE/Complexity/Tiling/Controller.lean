import DeciNSSE.Complexity.Tiling.Source
import DeciNSSE.Complexity.Tiling.Numbering

/-! # Address and tile checkers

The bit chosen by the copy index is checked in both traversals. The final
copy checks the horizontal edges of the master and the vertical edges of the
exposed records. The four boundary flags describe the record being read.

## Main declarations

- `Token`, `CellLetter` distinguish field delimiters, bits and tiles.
- `tokenReader` compiles the reachable register states of these checkers.
-/

namespace DeciNSSE.Complexity.Tiling

/-- A token carries a data letter, ends a probe or master, or separates the probes from
the master. -/
inductive Token (α : Type*) where
  /-- A letter inside a probe or master. -/
  | data (a : α)
  /-- The delimiter ending a probe or a master. -/
  | stop
  /-- The delimiter between the probes and the master. -/
  | bang
  deriving DecidableEq

/-- Decide token equality by comparing the delimiters or the enclosed data letters. -/
add_decl_doc instDecidableEqToken

/-- A cell record uses a record marker, address bits and a tile from the input alphabet. -/
inductive CellLetter (D : Type*) where
  /-- One bit of a column or row coordinate. -/
  | bit (b : Bool)
  /-- The marker at the start of a cell record. -/
  | record
  /-- The tile at the address of a record. -/
  | tile (d : D)
  deriving DecidableEq

/-- Decide equality of record markers, address bits and tile letters. -/
add_decl_doc instDecidableEqCellLetter

variable {D : Type*} {t : ℕ}

namespace Controller

/-- One copy's controller records its field, progress through the current record, bit-checking
data and boundary information. -/
structure Registers (D : Type*) where
  /-- The index of the checker reading this packet. -/
  copy : ℕ
  /-- True in the master traversal and false in the probe traversal. -/
  master : Bool
  /-- The preceding token in this field, or the sentinel at its start. -/
  color : Option (Token (CellLetter D)) := none
  /-- The current position in a record, with a separate slot for a probe's trailing data. -/
  slot : ℕ := 0
  /-- Whether this traversal has already read a tile. -/
  seen : Bool := false
  /-- The bit expected at this checker's slot in the next address. -/
  expected : Bool := false
  /-- The value read at this checker's slot in the current address. -/
  current : Bool := false
  /-- Whether all less significant bits read so far are one. -/
  carry : Bool := true
  /-- Whether all column bits read so far are zero. -/
  colZero : Bool := true
  /-- Whether all row bits read so far are zero. -/
  rowZero : Bool := true
  /-- Whether all column bits read so far are one. -/
  colLast : Bool := true
  /-- Whether all row bits read so far are one. -/
  rowLast : Bool := true
  /-- The preceding tile remembered by the final checker. -/
  previous : Option D := none
  /-- The number of initial-row master tiles read, capped at the length of the boundary prefix. -/
  count : ℕ := 0
  deriving DecidableEq

/-- Two live controls are equal exactly when all of their registers agree. -/
add_decl_doc instDecidableEqRegisters

/-- Live controls hold the checker registers, and `none` denotes the completed input. A
transition reaching that control returns `some none`. -/
abbrev Control (D : Type*) := Option (Registers D)

/-- Start the probe or master traversal of copy `j` with fresh registers. -/
def beginPhase (D : Type*) (j : ℕ) (master : Bool) : Control D :=
  some { copy := j, master := master }

/-- The rank of a physical bit slot is its significance in row-major or column-major order. -/
def bitRank (p : ℕ) (master : Bool) (i : ℕ) : ℕ :=
  if master then i else if i < p then p + i else i - p

/-- Check the selected address bit, accumulate the carry and boundary flags, and advance to the
next slot. -/
def readBit (p : ℕ) (r : Registers D) (bit : Bool) : Option (Registers D) := do
  let i := r.slot - 1
  if r.copy < 2 * p && i == r.copy && bit != r.expected then none else
    let less := bitRank p r.master i < bitRank p r.master r.copy
    return { r with
      color := some (.data (.bit bit)), slot := r.slot + 1
      current := if i = r.copy then bit else r.current
      carry := r.carry && (!decide less || bit)
      colZero := r.colZero && (i ≥ p || !bit), colLast := r.colLast && (i ≥ p || bit)
      rowZero := r.rowZero && (i < p || !bit), rowLast := r.rowLast && (i < p || bit) }

/-- Test the current master tile against every boundary condition indicated by the four
coordinate flags. -/
def boundaryOK [DecidableEq D] (I : Square D) (r : Registers D) (d : D) : Bool :=
  (!r.rowZero || d ∈ I.initial[r.count]?.getD I.rest) &&
    (!r.colZero || d ∈ I.left) && (!r.colLast || d ∈ I.right) && (!r.rowLast || d ∈ I.bottom)

/-- Finish a record by checking its tile and updating the expected next bit, previous tile and
boundary counter. -/
def readTile [DecidableEq D] (I : Square D) (r : Registers D) (d : D) :
    Option (Registers D) := do
  let fastZero := if r.master then r.colZero else r.rowZero
  let ok := r.previous.all fun prev =>
    (prev, d) ∈ (if r.master then I.horizontal else I.vertical)
  if (r.master && !boundaryOK I r d) || (r.copy == 2 * I.p && !fastZero && !ok) then none
  else return { r with
    slot := if r.master then 0 else 2 * I.p + 2
    seen := true, color := some (.data (.tile d))
    expected := xor r.current r.carry
    previous := if r.copy = 2 * I.p then some d else none
    count := if r.master && r.rowZero then min (r.count + 1) I.initial.length else r.count }

/-- Read one token in the current record, payload or delimiter position. A successful delimiter
transition closes the probe or master field when its last record is complete. -/
def tokenStep [DecidableEq D] (I : Square D) (q : Control D) (a : Token (CellLetter D)) :
    Option (Control D) := do
  let r ← q
  let last := 2 * I.p
  let complete := r.seen && (r.copy != last || (r.colLast && r.rowLast))
  if r.slot = last + 2 then
    match a with
    | .bang => none
    | .stop => return some { r with color := some a, slot := 0 }
    | .data _ => return some { r with color := some a }
  else if r.slot = 0 then
    match a with
    | .bang => if !r.master && complete then some (beginPhase D r.copy true) else none
    | .stop =>
      if r.master && complete then
        if r.copy = last then some none else some (beginPhase D (r.copy + 1) false)
      else none
    | .data .record =>
      if r.copy == last && r.seen && r.colLast && r.rowLast then none
      else return some { r with
        slot := 1, color := some a, current := false, carry := true
        colZero := true, colLast := true, rowZero := true, rowLast := true }
    | _ => none
  else if r.slot ≤ last then
    match a with
    | .data (.bit b) => return some (← readBit I.p r b)
    | _ => none
  else
    match a with
    | .data (.tile d) => return some (← readTile I r d)
    | _ => none

/-- Admit comparisons from earlier copies to the same field of the last copy, or from a
data-colored probe cut to the last master, when the colors differ. -/
def tokenAdmission [DecidableEq D] (last : ℕ) : Control D → Control D → Bool
  | some r, some s =>
    let afterData := match r.color with | some (.data _) => true | _ => false
    s.copy == last && r.color != s.color &&
      ((r.copy < last && r.master == s.master) ||
        (r.copy == last && !r.master && s.master && afterData))
  | _, _ => false

/-- The alphabet lists every tile once under the supplied numbering. -/
def alphabet (e : D ≃ Fin t) : List (Token (CellLetter D)) :=
  [.data (.bit false), .data (.bit true), .data .record, .stop, .bang] ++
    (List.finRange t).map (fun i => .data (.tile (e.symm i)))

/-- This polynomial bounds the number of token controls processed for a square with `t` tile
types. -/
def allowance (I : Square D) (t : ℕ) :=
  4096 * (I.p + 1) ^ 2 * (t + 6) ^ 2 * (I.initial.length + 1)

/-- Number the register states reached by the token controller with the given tile numbering. -/
def numbering [DecidableEq D] (I : Square D) (e : D ≃ Fin t) :
    Numbering (Token (CellLetter D)) (Control D) where
  states := discover (alphabet e) (tokenStep I) (allowance I t) (beginPhase D 0 false)
  start := beginPhase D 0 false
  go := tokenStep I
  final := Option.isNone
  rel := tokenAdmission (2 * I.p)
  initial := rfl

end Controller
open Controller

/-- Compile a token table from reachable register states. The enumeration
allowance counts the copy, slot, color, previous tile, boundary counter and
Boolean registers. -/
def tokenReader [DecidableEq D] (I : Square D) (e : D ≃ Fin t) :
    StoppingTable (Token (CellLetter D)) :=
  (numbering I e).table

namespace Controller

/-- The copy index, record slot and initial-row counter of a live control lie within their
finite ranges. -/
def Within (I : Square D) : Control D → Prop
  | none => True
  | some r => r.copy ≤ 2 * I.p ∧ r.slot ≤ 2 * I.p + 2 ∧ r.count ≤ I.initial.length

/-- A successful token transition preserves the register ranges. -/
theorem step_within [DecidableEq D] (I : Square D) (s : Control D) (hs : Within I s)
    (a : Token (CellLetter D)) (q : Control D) (h : tokenStep I s a = some q) : Within I q := by
  cases s with
  | none => simp [tokenStep] at h
  | some r =>
    obtain ⟨hj, hp, hc⟩ := hs
    by_cases payload : r.slot = 2 * I.p + 2
    · cases a <;> simp_all [tokenStep, Within] <;> subst_vars <;> simp_all
    by_cases start : r.slot = 0
    · rcases a with (b | _ | d) | _ | _ <;>
        simp_all [tokenStep, Within, beginPhase] <;> grind [Within]
    by_cases bits : r.slot ≤ 2 * I.p
    · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep, payload, start, bits, readBit] at h
      simp_all [Within]
      grind [Within]
    · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep, payload, start, bits, readTile] at h
      simp_all [Within]
      grind [Within]

private def cellEquiv : CellLetter D ≃ Bool ⊕ Unit ⊕ D where
  toFun | .bit b => .inl b | .record => .inr (.inl ()) | .tile d => .inr (.inr d)
  invFun | .inl b => .bit b | .inr (.inl _) => .record | .inr (.inr d) => .tile d
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with b | ⟨_ | _⟩ <;> rfl

private def tokenEquiv {α : Type*} : Token α ≃ α ⊕ Bool where
  toFun | .data a => .inl a | .stop => .inr false | .bang => .inr true
  invFun | .inl a => .data a | .inr false => .stop | .inr true => .bang
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with a | (_ | _) <;> rfl

private abbrev Flags := Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool
private abbrev RegisterCode (I : Square D) :=
  Fin (2 * I.p + 1) × Fin (2 * I.p + 3) × Fin (I.initial.length + 1) ×
    Option (Token (CellLetter D)) × Option D × Flags

private def pack (I : Square D) (s : Control D) (h : Within I s) : Option (RegisterCode I) :=
  match s with
  | none => none
  | some r => some (⟨r.copy, by have := h.1; omega⟩, ⟨r.slot, by have := h.2.1; omega⟩,
      ⟨r.count, by have := h.2.2; omega⟩, r.color, r.previous, r.master, r.seen, r.expected,
      r.current, r.carry, r.colZero, r.rowZero, r.colLast, r.rowLast)

private theorem pack_injective (I : Square D) (s q : Control D) (hs : Within I s) (hq : Within I q)
    (he : pack I s hs = pack I q hq) : s = q := by
  cases s with
  | none => cases q <;> simp_all [pack]
  | some r =>
    cases q with
    | none => cases he
    | some v => cases r; cases v; simp_all [pack, Fin.mk.injEq]

private theorem register_count [DecidableEq D] (I : Square D) (e : D ≃ Fin t)
    (xs : List (Control D)) (hn : xs.Nodup) (hp : ∀ s ∈ xs, Within I s) :
    xs.length + 1 ≤ 4096 * (I.p + 1) ^ 2 * (t + 6) ^ 2 * (I.initial.length + 1) := by
  let : Fintype D := Fintype.ofEquiv (Fin t) e.symm
  let : Fintype (CellLetter D) := Fintype.ofEquiv _ cellEquiv.symm
  let : Fintype (Token (CellLetter D)) := Fintype.ofEquiv _ tokenEquiv.symm
  let code (q : xs.toFinset) := pack I q.val (hp _ (List.mem_toFinset.mp q.property))
  have inj : Function.Injective code := fun x y h => Subtype.ext (pack_injective I _ _
    (hp _ (List.mem_toFinset.mp x.property)) (hp _ (List.mem_toFinset.mp y.property)) h)
  have count := Fintype.card_le_of_injective code inj
  rw [Fintype.card_coe, List.toFinset_card_of_nodup hn] at count
  have ht := Fintype.card_congr (tokenEquiv (α := CellLetter D))
  have hc := Fintype.card_congr (cellEquiv (D := D))
  have he := Fintype.card_congr e
  simp [RegisterCode, Flags, ht, hc, he] at count
  apply (Nat.add_le_add_right count 1).trans
  ring_nf
  omega

/-- The enumerated alphabet contains every delimiter and every data token. -/
theorem mem_alphabet (e : D ≃ Fin t) (a : Token (CellLetter D)) : a ∈ alphabet e := by
  rcases a with ((_ | _) | _ | d) | _ | _ <;> simp [alphabet]
  exact ⟨e d,e.symm_apply_apply d⟩

/-- Every successful successor of an enumerated reachable control is also present in the
numbering. -/
theorem names_closed [DecidableEq D] (I : Square D) (e : D ≃ Fin t) {s a q}
    (hs : s ∈ (numbering I e).states)
    (h : tokenStep I s a = some q) : q ∈ (numbering I e).states := by
  simp only [numbering] at hs ⊢
  exact discover_closed (alphabet e) (tokenStep I) (allowance I t) (beginPhase D 0 false) (Within I)
    (by simp [beginPhase,Within]) (fun s hi a _ q => step_within I s hi a q)
    (fun xs hn hp => (Nat.le_succ _).trans (register_count I e xs hn hp))
    s hs a (mem_alphabet e a) q h

end Controller

/-- The numbered token table has at most
`4096 * (I.p + 1) ^ 2 * (t + 6) ^ 2 * (I.initial.length + 1)` states, including its absorbing
sink. -/
theorem tokenReader_size [DecidableEq D] (I : Square D) (e : D ≃ Fin t) :
    (tokenReader I e).size ≤ 4096 * (I.p + 1) ^ 2 * (t + 6) ^ 2 * (I.initial.length + 1) := by
  simp only [tokenReader, numbering, Numbering.table]
  obtain ⟨hin,nd,inv⟩ := discover_spec (alphabet e) (tokenStep I) (allowance I t)
    (beginPhase D 0 false)
    (Within I) (by simp [Within,beginPhase]) (fun s hs a _ q => step_within I s hs a q)
  apply (StoppingTable.ofStates_size _ (beginPhase D 0 false) (tokenStep I) Option.isNone
    (tokenAdmission (2*I.p)) rfl hin).le.trans
  exact Controller.register_count I e _ nd inv

end DeciNSSE.Complexity.Tiling
