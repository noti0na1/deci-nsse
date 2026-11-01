import DeciNSSE.Complexity.Directions
import Mathlib.Data.List.Basic

/-! # The doubling code

The hardness reduction reads binary words through the doubling code
`doublingCode w = e(w) 1`, where the doubling `e` replaces each letter `a` by
`0 a`, written over the constructor directions `Fin n` with `2 ≤ n`. The code is
prefix free (`eq_of_doublingCode_prefix`).

## Main declarations
- `Hardness.doubling`, `Hardness.doublingCode`
- `Hardness.eq_of_doublingCode_prefix`
-/

namespace DeciNSSE.Complexity.Hardness

open Directions

variable {n : ℕ} (hn : 2 ≤ n)

/-- The doubling `e`: each letter `a` becomes the two directions `0 a`. -/
def doubling (w : List (Fin 2)) : List (Fin n) :=
  w.flatMap fun a => [embedDir hn 0, embedDir hn a]

/-- The doubling code `e(w) 1` of a binary word. -/
def doublingCode (w : List (Fin 2)) : List (Fin n) := doubling hn w ++ [embedDir hn 1]

@[simp] theorem doubling_nil : doubling hn [] = [] := rfl

@[simp] theorem doubling_cons (a : Fin 2) (w : List (Fin 2)) :
    doubling hn (a :: w) = embedDir hn 0 :: embedDir hn a :: doubling hn w := rfl

theorem doubling_append (u v : List (Fin 2)) :
    doubling hn (u ++ v) = doubling hn u ++ doubling hn v := by
  simp [doubling]

theorem doubling_snoc (w : List (Fin 2)) (a : Fin 2) :
    doubling hn (w ++ [a]) = doubling hn w ++ [embedDir hn 0] ++ [embedDir hn a] := by
  simp [doubling_append]

@[simp] theorem doublingCode_nil : doublingCode hn [] = [embedDir hn 1] := rfl

@[simp] theorem doublingCode_cons (a : Fin 2) (w : List (Fin 2)) :
    doublingCode hn (a :: w) = embedDir hn 0 :: embedDir hn a :: doublingCode hn w := rfl

@[simp] theorem doublingCode_ne_nil (w : List (Fin 2)) : doublingCode hn w ≠ [] := by
  simp [doublingCode]

/-- Codes use only the two binary directions. -/
theorem val_lt_two_of_mem_doublingCode {w : List (Fin 2)} {i : Fin n}
    (hi : i ∈ doublingCode hn w) : i.val < 2 := by
  induction w with
  | nil => simp at hi; simp [hi]
  | cons a w ih =>
    simp only [doublingCode_cons, List.mem_cons] at hi
    rcases hi with rfl | rfl | hi
    · simp
    · simp
    · exact ih hi

/-- The code is prefix free. -/
theorem eq_of_doublingCode_prefix :
    ∀ {v w : List (Fin 2)}, doublingCode hn v <+: doublingCode hn w → v = w
  | [], [], _ => rfl
  | [], b :: w, h => by
    simp only [doublingCode_nil, doublingCode_cons, List.cons_prefix_cons] at h
    exact absurd h.1 (embedDir_one_ne_zero hn)
  | a :: v, [], h => by
    simp only [doublingCode_nil, doublingCode_cons, List.cons_prefix_cons] at h
    exact absurd h.1.symm (embedDir_one_ne_zero hn)
  | a :: v, b :: w, h => by
    simp only [doublingCode_cons, List.cons_prefix_cons] at h
    rw [embedDir_injective hn h.2.1, eq_of_doublingCode_prefix h.2.2]

end DeciNSSE.Complexity.Hardness
