import DeciNSSE.RejectedTail.BoundedTail
import DeciNSSE.RejectedTail.Depth

/-! # Decidable holes for finite readers

A hole can be chosen with a quadratic rejected tail. The return gap turns this
tail bound into a depth bound in the number of reader states, and bounded-depth
compression gives an executable finite search over words, including the empty
alphabet.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Holes LetteredHierarchy HierarchyDepth
variable {α Q : Type*}

/-- The depth bound combines the quadratic tail bound with the state count. -/
def holeDepthBound (N : ℕ) : ℕ :=
  2 * N * (N^2+4*N+1) - 1

/-- An explicit total witness-length bound, including epsilon. -/
def holeLengthBound (N : ℕ) : ℕ :=
  BoundedDepth.holeBound N (holeDepthBound N) 0

variable [DecidableEq α] [Fintype Q] [DecidableEq Q]
variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) [RejectedPath M R T]

/-- The rejected-tail and depth bounds reduce hole existence to bounded depth. -/
theorem hole_iff_bounded_depth [Inhabited α] :
    (∃ w, IsReaderHole M R T w) ↔
      IsReaderHole M R T [] ∨
      ∃ w, w ≠ [] ∧ IsReaderHole M R T w ∧ InL (holeDepthBound (Fintype.card Q)) 0 w := by
  constructor
  · intro hh
    obtain ⟨w,J,hw,hJ,hb⟩ := boundedRejectedTail_of_rejectedPath M R T hh
    by_cases hn : w = []
    · exact Or.inl (hn ▸ hw)
    · refine Or.inr ⟨w, hn, hw, depth w, ?_, Or.inl (isUnary_depth w)⟩
      have hd := rejected_depth M R T hn ((Holes.isReaderHole_iff _ _ _ _).mp hw).1 hJ
      apply hd.trans
      simp only [holeDepthBound]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 1)) 1
  · rintro (hh | ⟨w,_,hh,_⟩)
    · exact ⟨[], hh⟩
    · exact ⟨w, hh⟩

/-- A total finite witness bound on the hole language. -/
theorem hole_iff_bounded_length_of_inhabited [Inhabited α] :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ holeLengthBound (Fintype.card Q) := by
  constructor
  · intro hh
    rcases (hole_iff_bounded_depth M R T).mp hh with hnil | hnon
    · exact ⟨[], hnil, Nat.zero_le _⟩
    · obtain ⟨w,_,hw,_,hlen⟩ := (BoundedDepth.exists_reader_hole_InL_iff_bounded
        M R T (holeDepthBound (Fintype.card Q)) 0).mp hnon
      exact ⟨w, hw, hlen⟩
  · rintro ⟨w,hw,_⟩
    exact ⟨w,hw⟩

/-- The explicit length bound also covers the empty alphabet. -/
theorem hole_iff_bounded_length :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ holeLengthBound (Fintype.card Q) := by
  classical
  by_cases hn : Nonempty α
  · let : Inhabited α := Classical.inhabited_of_nonempty hn
    exact hole_iff_bounded_length_of_inhabited M R T
  · have hem (w : List α) : w = [] := by
      cases w with
      | nil => rfl
      | cons a w => exact (hn ⟨a⟩).elim
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,hw,by simp [hem w]⟩
    · rintro ⟨w,hw,_⟩
      exact ⟨w,hw⟩

/-- Finite executable search, with no default alphabet letter. -/
theorem hole_iff_search [Fintype α] :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w ∈ Packets.boundedLists (Finset.univ : Finset α)
        (holeLengthBound (Fintype.card Q)), IsReaderHole M R T w := by
  rw [hole_iff_bounded_length M R T]
  simp only [Packets.mem_boundedLists, Finset.mem_univ, implies_true,
    and_true]
  exact exists_congr (fun _ => and_comm)

/-- Computable decision for every finite-alphabet rejected-path instance. -/
def decideHole [Fintype α] [DecidableRel R] [DecidablePred (· ∈ T)] :
    Decidable (∃ w, IsReaderHole M R T w) :=
  decidable_of_iff _ (hole_iff_search M R T).symm

end DeciNSSE.RejectedTail
