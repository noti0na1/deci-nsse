import DeciNSSE.Holes.StartCores
import DeciNSSE.Holes.Supports
import DeciNSSE.Holes.Depth

/-! # Counting levels of decreasing supports

A decreasing sequence of nonempty supports can have only finitely many
constant stretches of bounded width. Empty support bounds the remaining
word length, giving canonical depth at most 2N·B − 1 for width bound B.
-/

namespace DeciNSSE.RejectedTail
open CoAlignment LetteredHierarchy Supports HierarchyDepth StartCores

variable {α Q : Type*} [DecidableEq α] [Inhabited α] [DecidableEq Q]
variable (E : Lettered α Q) {w : List α}

/--
Nonempty decreasing supports with constant stretches of width at most `B` last at most `|Q|·B`
levels.
-/
theorem support_prefix_count [Fintype Q] (hw : w ≠ []) {B q : ℕ} (hB : 0 < B)
    (hn : ∀ j < q, (supp E w j).Nonempty)
    (hs : ∀ a b, a ≤ b → b < q → supp E w a = supp E w b → b + 1 - a ≤ B) :
    q ≤ Fintype.card Q * B := by
  have count : ∀ c j L, (supp E w j).card ≤ c → j + L ≤ q → L ≤ c * B := by
    intro c
    induction c with
    | zero =>
      intro j L hc hl
      by_cases hL : L = 0
      · simp [hL]
      · have := Finset.card_pos.mpr (hn j (by omega)); omega
    | succ c ih =>
      intro j L hc hl
      by_cases hb : L ≤ B
      · rw [Nat.succ_mul]; omega
      · have hj : j + B < q := by omega
        have hne : supp E w (j + B) ≠ supp E w j := by
          intro he
          have := hs j (j + B) (by omega) hj he.symm
          omega
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨supp_anti E hw (by omega : j ≤ j + B), hne⟩)
        have hh := ih (j + B) (L - B) (by omega) (by omega)
        rw [Nat.succ_mul]
        omega
  exact count (Fintype.card Q) 0 q (Finset.card_le_univ _) (by omega)

/-- The remaining canonical depth is bounded by the length at any nonempty level minus one. -/
theorem depth_le_level_add_length (hw : w ≠ []) (q : ℕ) :
    depth w ≤ q + (hierOf w q).length - 1 := by
  by_cases hq : depth w ≤ q
  · have := List.length_pos_iff.mpr (hierOf_ne_nil hw q); omega
  · have decrease : ∀ t, q + t ≤ depth w →
        (hierOf w (q + t)).length + t ≤ (hierOf w q).length := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        intro ht
        have hp := ih (by omega)
        have hd := length_hierOf_succ_lt (not_isUnary_of_lt_depth (by omega : q + t < depth w))
        have he : q + (t + 1) = q + t + 1 := by omega
        rw [he]
        omega
    have hd := decrease (depth w - q) (by omega)
    have he : q + (depth w - q) = depth w := by omega
    rw [he] at hd
    have := List.length_pos_iff.mpr (hierOf_ne_nil hw (depth w))
    omega

/-- Empty support at level `q` bounds canonical depth by `2q − 1`. -/
theorem depth_le_of_empty_support (hw : w ≠ []) {q : ℕ} (he : supp E w q = ∅) :
    depth w ≤ 2 * q - 1 := by
  have hall : ∀ x < (hierOf w q).length,
      isStart q ((tower E (markOf w) q).core (hierOf w q) x) = true := by
    intro x hx
    rw [isStart_eq_true_iff]
    cases ho : orig q ((tower E (markOf w) q).core (hierOf w q) x) with
    | none => rfl
    | some z =>
      have hz : z ∈ supp E w q := mem_supp.mpr ⟨x, hx, ho⟩
      rw [he] at hz
      exact (Finset.notMem_empty z hz).elim
  have hlen : (hierOf w q).length ≤ sCount E w q := by
    have := (startCore_invariants E hw q).1 ((hierOf w q).length - 1)
      (by have := List.length_pos_iff.mpr (hierOf_ne_nil hw q); omega)
    have hh := this.mp (hall _ (by have := List.length_pos_iff.mpr (hierOf_ne_nil hw q); omega))
    omega
  have := sCount_le_level E hw q
  have := depth_le_level_add_length hw q
  omega

/-- A width bound `B` for equal nonempty supports gives depth at most `2|Q|·B − 1`. -/
theorem depth_le_of_support_width [Fintype Q] (hw : w ≠ []) {B : ℕ} (hB : 0 < B)
    (hs : ∀ a b, a ≤ b → b ≤ depth w → supp E w a = supp E w b →
      (supp E w a).Nonempty → b + 1 - a ≤ B) :
    depth w ≤ 2 * Fintype.card Q * B - 1 := by
  classical
  by_cases hex : ∃ q, q ≤ depth w ∧ supp E w q = ∅
  · let q := Nat.find hex
    have hq := Nat.find_spec hex
    have hn : ∀ j < q, (supp E w j).Nonempty := by
      intro j hj
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      exact Nat.find_min hex hj ⟨by dsimp [q] at hj; omega, he⟩
    have hc := support_prefix_count E hw hB hn
      (fun a b hab hb he => hs a b hab (by dsimp [q] at hb; omega) he (hn a (by omega)))
    have hd := depth_le_of_empty_support E hw hq.2
    have he : 2 * Fintype.card Q * B = 2 * (Fintype.card Q * B) := Nat.mul_assoc _ _ _
    rw [he]
    omega
  · have hn : ∀ j < depth w + 1, (supp E w j).Nonempty := by
      intro j hj
      exact Finset.nonempty_iff_ne_empty.mpr (fun he => hex ⟨j, by omega, he⟩)
    have hc := support_prefix_count E hw hB hn
      (fun a b hab hb he => hs a b hab (by omega) he (hn a (by omega)))
    have he : 2 * Fintype.card Q * B = 2 * (Fintype.card Q * B) := Nat.mul_assoc _ _ _
    rw [he]
    omega
end DeciNSSE.RejectedTail
