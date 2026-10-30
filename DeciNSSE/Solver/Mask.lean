import DeciNSSE.Constraints.Closure

/-! # Finite sets represented by bit vectors -/

namespace DeciNSSE.Solver.Mask

attribute [-simp] BitVec.getLsbD_eq_getElem

variable {m : ℕ} {α : Type}

/-- Decode the membership bits. -/
def decode (s : BitVec m) : Finset (Fin m) :=
  Finset.univ.filter fun i => s.getLsbD i = true

@[simp] theorem mem_decode (s : BitVec m) (i : Fin m) :
    i ∈ decode s ↔ s.getLsbD i = true := by simp [decode]

/-- A single membership bit. -/
def singleton (i : Fin m) : BitVec m := (1 : BitVec m) <<< i.val

@[simp] theorem bit_singleton (i j : Fin m) :
    (singleton i).getLsbD j = true ↔ i = j := by
  simp only [singleton, BitVec.ofNat_eq_ofNat, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  have := i.isLt
  have := j.isLt
  simp only [Fin.ext_iff]
  omega

/-- Union of a list of masks. -/
def union (xs : List α) (f : α → BitVec m) : BitVec m :=
  xs.foldl (fun s x => s ||| f x) (BitVec.zero m)

theorem bit_fold (xs : List α) (f : α → BitVec m) (s : BitVec m) (i : Fin m) :
    (xs.foldl (fun s x => s ||| f x) s).getLsbD i = true ↔
      s.getLsbD i = true ∨ ∃ x ∈ xs, (f x).getLsbD i = true := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp [ih, or_assoc]

@[simp] theorem bit_union (xs : List α) (f : α → BitVec m) (i : Fin m) :
    (union xs f).getLsbD i = true ↔ ∃ x ∈ xs, (f x).getLsbD i = true := by
  simp [union, bit_fold]

/-- Encode a finite list without retaining duplicate entries. -/
def ofList (xs : List (Fin m)) : BitVec m := union xs singleton

@[simp] theorem bit_ofList (xs : List (Fin m)) (i : Fin m) :
    (ofList xs).getLsbD i = true ↔ i ∈ xs := by simp [ofList]

/-- Encode a finite set. -/
def encode (s : Finset (Fin m)) : BitVec m := ofList (s.sort (· ≤ ·))

@[simp] theorem bit_encode (s : Finset (Fin m)) (i : Fin m) :
    (encode s).getLsbD i = true ↔ i ∈ s := by simp [encode]

@[simp] theorem decode_encode (s : Finset (Fin m)) : decode (encode s) = s := by
  ext i; simp

/-- An array-backed finite function. -/
structure Table (m : ℕ) (β : Type) where
  values : Vector β m
  deriving DecidableEq

def Table.get {β : Type} (t : Table m β) (i : Fin m) : β := t.values[i]

instance {β : Type} : CoeFun (Table m β) (fun _ => Fin m → β) := ⟨Table.get⟩

/-- Tabulate all values before any lookup. -/
def table {β : Type} (f : Fin m → β) : Table m β := ⟨Vector.ofFn f⟩

@[simp] theorem table_eq {β : Type} (f : Fin m → β) :
    (table f : Fin m → β) = f := by
  funext i; simp [table, Table.get]

theorem Table.ext_fun {β : Type} {s t : Table m β}
    (h : (s : Fin m → β) = (t : Fin m → β)) : s = t := by
  cases s with
  | mk sv =>
    cases t with
    | mk tv =>
      congr 1
      apply Vector.ext
      intro i hi
      exact congrFun h ⟨i, hi⟩

/-- Relational image using bitwise unions. -/
def image (rows : Fin m → BitVec m) (s : BitVec m) : BitVec m :=
  union ((List.finRange m).filter fun i => s.getLsbD i.val) rows

@[simp] theorem bit_image (rows : Fin m → BitVec m) (s : BitVec m) (j : Fin m) :
    (image rows s).getLsbD j = true ↔
      ∃ i : Fin m, s.getLsbD i = true ∧ (rows i).getLsbD j = true := by
  simp only [image, bit_union, List.mem_filter, List.mem_finRange, true_and]

/-- A nonempty bitwise intersection. -/
def meets (s t : BitVec m) : Bool := s &&& t != BitVec.zero m

@[simp] theorem meets_iff (s t : BitVec m) :
    meets s t = true ↔ ∃ i : Fin m, s.getLsbD i = true ∧ t.getLsbD i = true := by
  simp only [meets, bne_iff_ne]
  constructor
  · contrapose!
    intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < m
    · have := h ⟨i, hi⟩
      simp only [BitVec.getLsbD_and]
      cases hs : s.getLsbD i <;> cases ht : t.getLsbD i <;> simp_all
    · simp [BitVec.getLsbD_of_ge, Nat.le_of_not_lt hi]
  · rintro ⟨i, hs, ht⟩ he
    have := congrArg (fun v : BitVec m => v.getLsbD i) he
    simp [hs, ht] at this

end DeciNSSE.Solver.Mask
