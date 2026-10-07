import DeciNSSE.Holes.Supports

/-! # Start cores in the hierarchy

Start cores are distinct along a run. Their contribution bounds word length
when no original cores remain, and controls the suffix after the last live core.
-/

section

set_option autoImplicit false

namespace DeciNSSE.StartCores

open scoped List

section StartCores
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

/-- The marker count in the start-core recurrence. -/
def cnt (D0 : Lettered α Q) (w : List α) (j : ℕ) : ℕ :=
  ((hierOf w j).take (sCount D0 w j)).count (markOf w j)

theorem sCount_succ_cnt (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) = min (hierOf w (j + 1)).length (1 + cnt D0 w j) :=
  sCount_succ D0 hw j

theorem cnt_le (D0 : Lettered α Q) (w : List α) (j : ℕ) : cnt D0 w j ≤ sCount D0 w j := by
  have h1 := List.count_le_length (l := (hierOf w j).take (sCount D0 w j)) (a := markOf w j)
  have h2 := List.length_take_le (sCount D0 w j) (hierOf w j)
  unfold cnt; omega

theorem sCount_succ_le (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) ≤ sCount D0 w j + 1 := by
  rw [sCount_succ_cnt D0 hw j]
  have := cnt_le D0 w j
  omega

variable [Fintype Q] [DecidableEq Q]

end StartCores

end DeciNSSE.StartCores

end

section

set_option autoImplicit false

namespace DeciNSSE.StartCores
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

open scoped List

universe u v

section Descent
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

theorem sCount_le_level (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) :
    ∀ i, sCount D0 w i ≤ i
  | 0 => by rw [sCount_zero]
  | i + 1 => (sCount_succ_le D0 hw i).trans (Nat.succ_le_succ (sCount_le_level D0 hw i))

end Descent

end DeciNSSE.StartCores

end
