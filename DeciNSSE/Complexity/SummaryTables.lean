import DeciNSSE.Holes.BoundedDepth

/-! # Lettered monitors given by finite tables

The summary search stores the current monitor explicitly. A table is a lettered
monitor whose admissions and target are Boolean functions, so that over finite
alphabets and cores it ranges over a finite type and its holes are tested by
evaluation. The level-zero table of a reader is its lettered monitor.

## Main declarations

- `Summary.Table`: a lettered monitor with Boolean tables, and
  `Summary.Table.toLettered`, the monitor it denotes.
- `Summary.Table.ofReader`: the table of a reader, with
  `Summary.Table.toLettered_ofReader`.
- `Summary.Table.holeB`, `Summary.Table.holeB_iff`: a Boolean hole test.
- `Summary.card_table`, `Summary.card_table_le`: the number of tables.
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity.Summary
open CoAlignment LetteredHierarchy
open scoped List

/-- A lettered monitor given by finite Boolean tables. -/
structure Table (Γ C : Type*) where
  /-- The initial core. -/
  start : C
  /-- The core transition on a letter. -/
  κ : Γ → C → C
  /-- Admission for comparisons ending before the terminal cut. -/
  Λ : Lab Γ C → Lab Γ C → Bool
  /-- Admission for comparisons ending at the terminal cut. -/
  Λf : Lab Γ C → Lab Γ C → Bool
  /-- The target condition on the final core and letter. -/
  Tf : C → Γ → Bool

namespace Table
variable {Γ C : Type*} (T : Table Γ C)

/-- The lettered monitor of a table. -/
def toLettered : Lettered Γ C where
  start := T.start
  κ := T.κ
  Λ L L' := T.Λ L L' = true
  Λf L L' := T.Λf L L' = true
  Tf c a := T.Tf c a = true

@[simp] theorem toLettered_start : T.toLettered.start = T.start := rfl
@[simp] theorem toLettered_κ : T.toLettered.κ = T.κ := rfl
@[simp] theorem toLettered_Λ (L L' : Lab Γ C) : T.toLettered.Λ L L' ↔ T.Λ L L' = true := Iff.rfl
@[simp] theorem toLettered_Λf (L L' : Lab Γ C) : T.toLettered.Λf L L' ↔ T.Λf L L' = true :=
  Iff.rfl
@[simp] theorem toLettered_Tf (c : C) (a : Γ) : T.toLettered.Tf c a ↔ T.Tf c a = true := Iff.rfl

/-- The table of the level-zero monitor of a reader `(M, R, F)`. -/
def ofReader {Q : Type*} (M : DFA Γ Q) (R : Q → Q → Prop) [DecidableRel R] (F : Set Q)
    [DecidablePred (· ∈ F)] : Table Γ Q where
  start := M.start
  κ a c := M.step c a
  Λ L L' := match L' with
    | none => false
    | some p => decide (R (stOf M L) (stOf M (some p)))
  Λf L L' := match L' with
    | none => false
    | some p => decide (R (stOf M L) (stOf M (some p)))
  Tf c a := decide (M.step c a ∈ F)

/-- The table of a reader denotes its lettered monitor. -/
theorem toLettered_ofReader {Q : Type*} (M : DFA Γ Q) (R : Q → Q → Prop) [DecidableRel R]
    (F : Set Q) [DecidablePred (· ∈ F)] :
    (ofReader M R F).toLettered = LetteredHierarchy.ofReader M R F := by
  have hΛ : (fun L L' => (ofReader M R F).Λ L L' = true) = readerΛ M R := by
    funext L L'
    rcases L' with _ | p <;> simp [ofReader, readerΛ]
  have hTf : (fun c a => (ofReader M R F).Tf c a = true) = fun c a => M.step c a ∈ F := by
    funext c a; simp [ofReader]
  simp only [toLettered, LetteredHierarchy.ofReader]
  congr 1

section Hole
variable [DecidableEq Γ]

/-- The Boolean hole test: the final label is a target, and no terminal or interior
comparison is admitted. -/
def holeB (v : List Γ) : Bool :=
  (match T.toLettered.label v v.length with
    | some (c, a) => T.Tf c a
    | none => false) &&
  (List.range v.length).all (fun s =>
    !T.Λf (T.toLettered.label v s) (T.toLettered.label v v.length)) &&
  (List.range v.length).all (fun e => (List.range e).all fun s =>
    !(decide (v.drop e <+: v.drop s) && T.Λ (T.toLettered.label v s) (T.toLettered.label v e)))

theorem holeB_iff (v : List Γ) : T.holeB v = true ↔ T.toLettered.IsHole v := by
  unfold holeB Lettered.IsHole
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rw [and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · rcases T.toLettered.label v v.length with _ | ⟨c, a⟩ <;> simp
  · refine forall_congr' fun s => imp_congr_right fun _ => ?_
    simp
  · constructor
    · rintro h s e ⟨hse, he, hc⟩ hev hΛ
      rcases h e hev s hse with h1 | h1
      · exact h1 hc
      · rw [toLettered_Λ, h1] at hΛ; exact Bool.false_ne_true hΛ
    · intro h e he s hs
      by_cases hc : v.drop e <+: v.drop s
      · right
        have := h s e ⟨hs, he.le, hc⟩ he
        rwa [toLettered_Λ, Bool.not_eq_true] at this
      · exact Or.inl hc

end Hole

/-- Tables as tuples of their fields. -/
def equivProd : Table Γ C ≃ C × (Γ → C → C) × (Lab Γ C → Lab Γ C → Bool) ×
    (Lab Γ C → Lab Γ C → Bool) × (C → Γ → Bool) where
  toFun T := (T.start, T.κ, T.Λ, T.Λf, T.Tf)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype Γ] [DecidableEq Γ] [Fintype C] [DecidableEq C]

instance instDecEqTable : DecidableEq (Table Γ C) := fun T T' =>
  decidable_of_iff (T.start = T'.start ∧ T.κ = T'.κ ∧ T.Λ = T'.Λ ∧ T.Λf = T'.Λf ∧ T.Tf = T'.Tf)
    (by cases T; cases T'; simp)

instance instFintypeTable : Fintype (Table Γ C) := Fintype.ofEquiv _ equivProd.symm

end Table

section Card
variable (Γ C : Type*) [Fintype Γ] [DecidableEq Γ] [Fintype C] [DecidableEq C]

/-- The number of tables: the number of choices of each field. -/
theorem card_table : Fintype.card (Table Γ C) =
    Fintype.card C * (Fintype.card C ^ Fintype.card C) ^ Fintype.card Γ *
      (2 ^ (Fintype.card C * Fintype.card Γ + 1)) ^ (Fintype.card C * Fintype.card Γ + 1) *
      (2 ^ (Fintype.card C * Fintype.card Γ + 1)) ^ (Fintype.card C * Fintype.card Γ + 1) *
      (2 ^ Fintype.card Γ) ^ Fintype.card C := by
  rw [Fintype.card_congr Table.equivProd]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_bool]
  ring

/-- A table with `M` cores over `h` letters takes at most `3 (M (h + 1) + 1)²` bits. -/
theorem card_table_le : Fintype.card (Table Γ C) ≤
    2 ^ (3 * (Fintype.card C * (Fintype.card Γ + 1) + 1) ^ 2) := by
  rw [card_table]
  set M := Fintype.card C
  set h := Fintype.card Γ
  have hM : M ≤ 2 ^ M := Nat.lt_two_pow_self.le
  have hMM : (M ^ M) ^ h ≤ 2 ^ (M * M * h) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hM M) h
  calc M * (M ^ M) ^ h * (2 ^ (M * h + 1)) ^ (M * h + 1) * (2 ^ (M * h + 1)) ^ (M * h + 1) *
        (2 ^ h) ^ M
      ≤ 2 ^ M * 2 ^ (M * M * h) * (2 ^ (M * h + 1)) ^ (M * h + 1) *
          (2 ^ (M * h + 1)) ^ (M * h + 1) * (2 ^ h) ^ M := by gcongr
    _ = 2 ^ (M + M * M * h + 2 * (M * h + 1) ^ 2 + h * M) := by ring
    _ ≤ 2 ^ (3 * (M * (h + 1) + 1) ^ 2) := by
        apply Nat.pow_le_pow_right (by decide)
        nlinarith [Nat.zero_le (M * h), Nat.zero_le M, Nat.zero_le (M * M * h)]

end Card

end DeciNSSE.Complexity.Summary
