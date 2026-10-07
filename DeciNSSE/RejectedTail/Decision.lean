import DeciNSSE.RejectedTail.BoundedTail
import DeciNSSE.RejectedTail.Depth

/-! # Decidable holes for finite readers

Predecessor refinement preserves holes and supplies the return-gap invariant.
A quadratic tail bound gives a depth bound, and bounded-depth compression
gives an executable finite search over words, including the empty alphabet.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Refinement
open Holes LetteredHierarchy HierarchyDepth
variable {α Q : Type*}

/-- The depth bound combines the quadratic tail bound with the refined state count. -/
def holeDepthBound (N : ℕ) : ℕ :=
  2 * (2*N+1) * max 1 (N^2+4*N) - 1

/-- An explicit total witness-length bound, including epsilon. -/
def holeLengthBound (N : ℕ) : ℕ :=
  BoundedDepth.holeBound (2*N+1) (holeDepthBound N) 0

@[simp] theorem card_state [Fintype Q] :
    Fintype.card (State Q) = 2 * Fintype.card Q + 1 := by
  simp [State, Fintype.card_prod, Nat.mul_comm]

variable [DecidableEq α] [Fintype Q] [DecidableEq Q]
variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
variable [DecidablePred (· ∈ T)] [RejectedPath M R T]

/-- The rejected-tail and refined depth bounds reduce hole existence to bounded depth. -/
theorem hole_iff_bounded_depth [Inhabited α] :
    (∃ w, IsReaderHole M R T w) ↔
      IsReaderHole (reader M T) (relation M R) (target M T) [] ∨
      ∃ w, w ≠ [] ∧ IsReaderHole (reader M T) (relation M R) (target M T) w ∧
        InL (holeDepthBound (Fintype.card Q)) 0 w := by
  constructor
  · intro hh
    obtain ⟨w,J,hw,hJ,hb⟩ := boundedRejectedTail_of_rejectedPath M R T hh
    have hrw := (hole_iff M R T w).mpr hw
    by_cases hn : w = []
    · exact Or.inl (hn ▸ hrw)
    · refine Or.inr ⟨w, hn, hrw, depth w, ?_, Or.inl (isUnary_depth w)⟩
      have hd := rejected_depth (reader M T) (relation M R) (target M T)
        (return_gap M R T) hn ((Holes.isReaderHole_iff _ _ _ _).mp hrw).1
        ((firstRejectedPrefix_iff M T w J).mpr hJ)
      apply hd.trans
      simp only [card_state, holeDepthBound]
      exact Nat.sub_le_sub_right (Nat.mul_le_mul_left _ (max_le_max_left 1 hb)) 1
  · rintro (hh | ⟨w,_,hh,_⟩)
    · exact ⟨[], (hole_iff M R T []).mp hh⟩
    · exact ⟨w, (hole_iff M R T w).mp hh⟩

/-- A total finite witness bound on the original hole language. -/
theorem hole_iff_bounded_length_of_inhabited [Inhabited α] :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ holeLengthBound (Fintype.card Q) := by
  constructor
  · intro hh
    rcases (hole_iff_bounded_depth M R T).mp hh with hnil | hnon
    · exact ⟨[], (hole_iff M R T []).mp hnil, Nat.zero_le _⟩
    · obtain ⟨w,_,hw,_,hlen⟩ :=
        (BoundedDepth.exists_reader_hole_InL_iff_bounded
          (reader M T) (relation M R) (target M T) (holeDepthBound (Fintype.card Q)) 0).mp hnon
      exact ⟨w, (hole_iff M R T w).mp hw, by simpa only [holeLengthBound, card_state] using hlen⟩
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
def decideHole [Fintype α] [DecidableRel R] :
    Decidable (∃ w, IsReaderHole M R T w) :=
  decidable_of_iff _ (hole_iff_search M R T).symm

end DeciNSSE.RejectedTail
