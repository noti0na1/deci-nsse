import DeciNSSE.Holes.Hierarchy

/-! # Supports of hierarchy levels

Each derived core is either a new start core or comes from an original state.
The finite sets of original states occurring at successive levels decrease,
providing the supports used to bound hierarchy depth.
-/

namespace DeciNSSE.Supports
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

universe u v

section Orig
variable {Q : Type v}

/-- Recover the original core, if a derived core is not one of the new start cores. -/
def orig : (i : ℕ) → Cores Q i → Option Q
  | 0, q => some q
  | _ + 1, none => none
  | i + 1, some c => orig i c

theorem isStart_eq_true_iff : ∀ (i : ℕ) (c : Cores Q i), isStart i c = true ↔ orig i c = none
  | 0, q => by simp [isStart, orig]
  | i + 1, none => by simp [isStart, orig, stLift]
  | i + 1, some c => by
      simp only [isStart, orig, stLift]
      exact isStart_eq_true_iff i c

end Orig

section Supports
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α] [DecidableEq Q]

/-- The finite set of original cores occurring before the end of a canonical hierarchy level. -/
def supp (D0 : Lettered α Q) (w : List α) (j : ℕ) : Finset Q :=
  ((List.range (hierOf w j).length).filterMap
    fun x => orig j ((tower D0 (markOf w) j).core (hierOf w j) x)).toFinset

theorem mem_supp {D0 : Lettered α Q} {w : List α} {j : ℕ} {q : Q} :
    q ∈ supp D0 w j ↔ ∃ x < (hierOf w j).length,
      orig j ((tower D0 (markOf w) j).core (hierOf w j) x) = some q := by
  simp [supp, List.mem_filterMap]

theorem supp_succ_subset (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    supp D0 w (j + 1) ⊆ supp D0 w j := by
  intro q hq
  obtain ⟨x, hx, hxq⟩ := mem_supp.mp hq
  rcases x with _ | k
  · have h0 : (tower D0 (markOf w) (j + 1)).core (hierOf w (j + 1)) 0 = none :=
      der_core_zero (tower D0 (markOf w) j) (markOf w j) (hierOf w (j + 1))
    rw [h0] at hxq
    simp [orig] at hxq
  · have hk : k < (hierOf w (j + 1)).length := by omega
    have h := der_core_succ_eq (tower D0 (markOf w) j) (markOf w j) (hierOf w (j + 1)) k hk
    rw [expand_hierOf hw j] at h
    have h' : (tower D0 (markOf w) (j + 1)).core (hierOf w (j + 1)) (k + 1) =
        some ((tower D0 (markOf w) j).core (hierOf w j)
          (cutP (markOf w j) (hierOf w (j + 1)) (k + 1) - 1)) := h
    rw [h'] at hxq
    simp only [orig] at hxq
    refine mem_supp.mpr ⟨_, ?_, hxq⟩
    have h1 := cutP_le_length (markOf w j) (hierOf w (j + 1)) (k + 1)
    have h2 := cutP_succ_pos (markOf w j) (hierOf w (j + 1)) k hk
    rw [expand_hierOf hw j] at h1
    omega

/-- The supports of the canonical hierarchy decrease with the level. -/
theorem supp_anti (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) {i j : ℕ} (hij : i ≤ j) :
    supp D0 w j ⊆ supp D0 w i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact subset_rfl
  | succ d ih => exact (supp_succ_subset D0 hw (i + d)).trans (ih (by omega))

end Supports

section ExpandLetters
variable {Γ : Type*}

theorem getElem?_expand_cutP (ℓ : Γ) (v : List (List Γ)) {k : ℕ} (hk : k < v.length) {p : ℕ}
    (hp : p < v[k].length) : (expand ℓ v)[cutP ℓ v k + p]? = v[k][p]? := by
  rw [expand_split ℓ v k hk, List.getElem?_append_right (by simp [cutP])]
  rw [show cutP ℓ v k + p - (expand ℓ (List.take k v)).length = p by simp [cutP]]
  rw [List.getElem?_append_left hp]

theorem getElem?_expand_marker (ℓ : Γ) (v : List (List Γ)) {k : ℕ} (hk : k < v.length) :
    (expand ℓ v)[cutP ℓ v k + v[k].length]? = some ℓ := by
  rw [expand_split ℓ v k hk, List.getElem?_append_right (by simp [cutP])]
  rw [show cutP ℓ v k + v[k].length - (expand ℓ (List.take k v)).length = v[k].length by
    simp [cutP]]
  rw [List.getElem?_append_right le_rfl]
  simp

end ExpandLetters

end DeciNSSE.Supports
