import DeciNSSE.Holes.BoundedDepth

/-! # Canonical hierarchy depth

A non-unary hierarchy level strictly decreases in length. Thus every word
reaches a unary level, and the least such level defines its canonical depth.
-/

namespace DeciNSSE.HierarchyDepth
open DeciNSSE.LetteredHierarchy

universe u

section Depth
variable {α : Type u} [DecidableEq α] [Inhabited α]

theorem getLast?_hierOf_of_ne_nil {w : List α} {k : ℕ} (h : hierOf w k ≠ []) :
    (hierOf w k).getLast? = some (markOf w k) := by
  rw [markOf, List.getLastD_eq_getLast?]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
    (by simpa using h : (hierOf w k).getLast? ≠ none)
  simp [ha]

/-- Desubstitution strictly shortens every non-unary canonical level. -/
theorem length_hierOf_succ_lt {w : List α} {k : ℕ} (h : ¬ IsUnary (hierOf w k)) :
    (hierOf w (k + 1)).length < (hierOf w k).length := by
  have hn : hierOf w k ≠ [] := by
    rintro hn; exact h (by rw [hn]; intro a ha; simp at ha)
  have hlast := getLast?_hierOf_of_ne_nil hn
  have hexp : expand (markOf w k) (hierOf w (k + 1)) = hierOf w k := by
    rw [hierOf_succ, expand_cutAt hlast]
  have hcnt : (hierOf w k).count (markOf w k) = (hierOf w (k + 1)).length := by
    rw [← hexp, count_expand _ (avoid_hierOf k)]
  rw [← hcnt]
  have hle := List.count_le_length (a := markOf w k) (l := hierOf w k)
  rcases Nat.lt_or_ge ((hierOf w k).count (markOf w k)) (hierOf w k).length with hlt | hge
  · exact hlt
  · exfalso
    have heq := List.count_eq_length.mp (le_antisymm hle hge)
    exact h fun a ha b hb => by rw [← heq a ha, ← heq b hb]

/-- Every word reaches a unary level after finitely many canonical desubstitutions. -/
theorem exists_isUnary_hierOf (w : List α) : ∃ k, IsUnary (hierOf w k) := by
  by_contra hne
  push Not at hne
  have key : ∀ k, (hierOf w k).length + k ≤ w.length := by
    intro k
    induction k with
    | zero => simp [hierOf]
    | succ k ih => have := length_hierOf_succ_lt (hne k); omega
  have := key (w.length + 1)
  omega

/-- The first unary level of the canonical desubstitution hierarchy. -/
def depth (w : List α) : ℕ := Nat.find (exists_isUnary_hierOf w)

theorem isUnary_depth (w : List α) : IsUnary (hierOf w (depth w)) :=
  Nat.find_spec (exists_isUnary_hierOf w)

theorem not_isUnary_of_lt_depth {w : List α} {k : ℕ} (hk : k < depth w) :
    ¬ IsUnary (hierOf w k) :=
  Nat.find_min (exists_isUnary_hierOf w) hk

end Depth

end DeciNSSE.HierarchyDepth
