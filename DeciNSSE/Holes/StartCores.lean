import DeciNSSE.Holes.Supports

/-! # Start cores in the hierarchy

Start cores are distinct along a run. Their contribution bounds word length
when no original cores remain, and controls the suffix after the last live core.

## Main declarations

- `cnt`, `sCount_succ_cnt`: the marker count in the start-count recurrence.
- `sCount_succ_le`, `sCount_le_level`: the start count grows by at most one
  per level.

The declarations are in the namespace `DeciNSSE.StartCores`.
-/

section

namespace DeciNSSE.StartCores

open scoped List

section StartCores
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

/-- The marker count in the start-core recurrence. -/
def cnt (D0 : Lettered α Q) (w : List α) (j : ℕ) : ℕ :=
  ((hierOf w j).take (sCount D0 w j)).count (markOf w j)

/-- The start-count recurrence `s_{j+1} = min(|u_{j+1}|, 1 + cnt_j)`. -/
theorem sCount_succ_cnt (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) = min (hierOf w (j + 1)).length (1 + cnt D0 w j) :=
  sCount_succ D0 hw j

/-- The marker count is at most the start count. -/
theorem cnt_le (D0 : Lettered α Q) (w : List α) (j : ℕ) : cnt D0 w j ≤ sCount D0 w j := by
  have h1 := List.count_le_length (l := (hierOf w j).take (sCount D0 w j)) (a := markOf w j)
  have h2 := List.length_take_le (sCount D0 w j) (hierOf w j)
  unfold cnt; omega

/-- The start count grows by at most one per level. -/
theorem sCount_succ_le (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) ≤ sCount D0 w j + 1 := by
  rw [sCount_succ_cnt D0 hw j]
  have := cnt_le D0 w j
  omega

end StartCores

end DeciNSSE.StartCores

end

section

namespace DeciNSSE.StartCores
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

open scoped List

universe u v

section Descent
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- The start count of level `i` is at most `i`. -/
theorem sCount_le_level (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) :
    ∀ i, sCount D0 w i ≤ i
  | 0 => by rw [sCount_zero]
  | i + 1 => (sCount_succ_le D0 hw i).trans (Nat.succ_le_succ (sCount_le_level D0 hw i))

end Descent

end DeciNSSE.StartCores

end
