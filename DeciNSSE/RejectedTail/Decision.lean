import DeciNSSE.RejectedTail.BoundedTail
import DeciNSSE.RejectedTail.Depth
import DeciNSSE.Holes.ElementaryBound

/-! # Decidable holes for finite readers

A hole can be chosen with a quadratic rejected tail. The return gap turns this
tail bound into a depth bound in the number of reader states. Elementary
bounded-depth compression gives an executable finite search over words,
including the empty alphabet.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Holes LetteredHierarchy HierarchyDepth
variable {α Q : Type*}

/-- The depth bound combines the quadratic tail bound with the state count. -/
def holeDepthBound (N : ℕ) : ℕ :=
  2 * N * (N^2+4*N+1) - 1

/-- An elementary witness-length bound, including epsilon. -/
def holeLengthBound (N : ℕ) : ℕ :=
  ElementaryBound.lengthBound N (holeDepthBound N)

/-- The total witness allowance is doubly exponential in a degree-seven polynomial. -/
theorem holeLengthBound_le (N : ℕ) :
    holeLengthBound N ≤ 2 ^ 2 ^ (4096 * (N + 1) ^ 7) := by
  let t := N + 1
  let d := holeDepthBound N
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hN : N ≤ t := by dsimp [t]; omega
  have hd : d ≤ 12 * t ^ 3 := by
    calc
      d ≤ 2 * N * (N ^ 2 + 4 * N + 1) := Nat.sub_le _ _
      _ ≤ 2 * t * (6 * t ^ 2) := by
        gcongr
        dsimp [t]
        nlinarith
      _ = 12 * t ^ 3 := by ring
  have ht3 : t ≤ t ^ 3 := by simpa using Nat.pow_le_pow_right ht (show 1 ≤ 3 by decide)
  have ht7 : t ≤ t ^ 7 := by simpa using Nat.pow_le_pow_right ht (show 1 ≤ 7 by decide)
  have h37 : t ^ 3 ≤ t ^ 7 := Nat.pow_le_pow_right ht (by decide)
  have hN7 : N ≤ t ^ 7 := hN.trans ht7
  have hN2 : N ^ 2 ≤ t ^ 7 :=
    (Nat.pow_le_pow_left hN 2).trans (Nat.pow_le_pow_right ht (by decide))
  have hd7 : d ≤ 12 * t ^ 7 := hd.trans (Nat.mul_le_mul_left _ h37)
  have h1 : 1 ≤ t ^ 7 := Nat.one_le_pow _ _ ht
  have hprod : 4 * N * (N + d) * (d + 1) ≤ 676 * t ^ 7 := by
    calc
      _ ≤ 4 * t * (13 * t ^ 3) * (13 * t ^ 3) := by
        gcongr <;> omega
      _ = 676 * t ^ 7 := by ring
  have hE : ElementaryBound.dictionaryExponent N d ≤ 722 * t ^ 7 := by
    unfold ElementaryBound.dictionaryExponent
    omega
  apply (ElementaryBound.lengthBound_le N d).trans
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.pow_le_pow_right (by decide)
  change 5 * ElementaryBound.dictionaryExponent N d + 3 ≤ 4096 * t ^ 7
  omega

variable [DecidableEq α] [Fintype Q] [DecidableEq Q]
variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) [RejectedPath M R T]

/-- The rejected-tail and depth bounds reduce hole existence to bounded depth. -/
theorem hole_iff_bounded_depth [Inhabited α] :
    (∃ w, IsReaderHole M R T w) ↔
      IsReaderHole M R T [] ∨
      ∃ w, w ≠ [] ∧ IsReaderHole M R T w ∧ InL (holeDepthBound (Fintype.card Q)) w := by
  constructor
  · intro hh
    obtain ⟨w,J,hw,hJ,hb⟩ := boundedRejectedTail_of_rejectedPath M R T hh
    by_cases hn : w = []
    · exact Or.inl (hn ▸ hw)
    · refine Or.inr ⟨w, hn, hw, depth w, ?_, isUnary_depth w⟩
      have hd := rejected_depth M T hn ((Holes.isReaderHole_iff _ _ _ _).mp hw).1 hJ
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
    · obtain ⟨w, hw0, hw, hL⟩ := hnon
      obtain ⟨v, hv, _, hlen⟩ := ElementaryBound.exists_short_hole
        ((isHole_ofReader_iff M R T hw0).mpr hw) hL
      exact ⟨v, (isHole_ofReader_iff M R T hv.ne_nil).mp hv, hlen⟩
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
