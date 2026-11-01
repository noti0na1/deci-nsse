import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

/-! # Binary letters as constructor directions

The reductions of the complexity results read binary words along the first two
directions of a constructor of arity `n ≥ 2`. A letter `a : Fin 2` is the
direction `embedDir hn a`. Two child vectors are used in flat literals and in
their solutions:

- `binaryChildren u v w`: `u` in direction `0`, `v` in direction `1`, and `w` in
  every other direction;
- `letterChildren a u v`: `u` in the direction of the letter `a`, and `v` in every
  other direction.

## Main declarations
- `Directions.embedDir`, `Directions.embedDir_injective`
- `Directions.binaryChildren`, `Directions.comp_binaryChildren`
- `Directions.letterChildren`, `Directions.comp_letterChildren`
-/

namespace DeciNSSE.Complexity.Directions

variable {n : ℕ} (hn : 2 ≤ n)

/-- A binary letter as a constructor direction. -/
def embedDir (a : Fin 2) : Fin n := ⟨a.val, by omega⟩

/-- The direction of a letter has the letter's value. -/
@[simp] theorem embedDir_val (a : Fin 2) : (embedDir hn a).val = a.val := rfl

/-- Distinct letters give distinct directions. -/
theorem embedDir_injective : Function.Injective (embedDir hn) := by
  intro a b h
  exact Fin.ext (by simpa using congrArg Fin.val h)

/-- The letters `0` and `1` give different directions. -/
theorem embedDir_one_ne_zero : embedDir hn 1 ≠ embedDir hn 0 := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

/-- The children `(u, v, w, …, w)` of a constructor: variables in a flat literal, or
their values. -/
def binaryChildren {α : Type*} (u v w : α) : Fin n → α :=
  fun i => if i.val = 0 then u else if i.val = 1 then v else w

/-- Applying a map to the children of `binaryChildren`. -/
theorem comp_binaryChildren {α β : Type*} (g : α → β) (u v w : α) :
    g ∘ (binaryChildren u v w : Fin n → α) = binaryChildren (g u) (g v) (g w) := by
  funext i
  simp only [Function.comp_apply, binaryChildren]
  split_ifs <;> rfl

/-- Direction `0` holds the first child. -/
@[simp] theorem binaryChildren_embedDir_zero {α : Type*} (u v w : α) :
    binaryChildren u v w (embedDir hn 0) = u := by simp [binaryChildren, embedDir]

/-- Direction `1` holds the second child. -/
@[simp] theorem binaryChildren_embedDir_one {α : Type*} (u v w : α) :
    binaryChildren u v w (embedDir hn 1) = v := by simp [binaryChildren, embedDir]

/-- The children `(u @ a, v, …, v)` of a constructor, variables in a flat literal or their
values: `u` in the direction of the binary letter `a`, and `v` in every other direction. -/
def letterChildren {α : Type*} (a : Fin 2) (u v : α) : Fin n → α :=
  fun i => if i.val = a.val then u else v

/-- Applying a map to the children of `letterChildren`. -/
theorem comp_letterChildren {α β : Type*} (g : α → β) (a : Fin 2) (u v : α) :
    g ∘ (letterChildren a u v : Fin n → α) = letterChildren a (g u) (g v) := by
  funext i
  simp only [Function.comp_apply, letterChildren]
  split_ifs <;> rfl

/-- The direction of the letter holds the distinguished child. -/
@[simp] theorem letterChildren_embedDir {α : Type*} (a : Fin 2) (u v : α) :
    letterChildren a u v (embedDir hn a) = u := by simp [letterChildren, embedDir]

end DeciNSSE.Complexity.Directions
