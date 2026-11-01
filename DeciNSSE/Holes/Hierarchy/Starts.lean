import DeciNSSE.Holes.Hierarchy.Canonical

/-! # Start cores of the canonical hierarchy

Each derived monitor adds one start core. Along the canonical hierarchy of a
nonempty word, the indices whose core is a start core form a prefix `[0, s_j)`
of level `j`, their cores are pairwise distinct, and reading never returns to
a start core. The start count `s_j` satisfies a recurrence through the markers.

## Main declarations

- `der_core_succ_eq`: the derived core after block `k` is the core before the
  marker that ends it.
- `stLift`, `startCores_der`, `startCores_der_distinct`: start cores through
  one derived monitor.
- `isStart`, `sCount`: the start cores of level `i` and the start count `s_j`.
- `startCore_invariants`: the prefix, distinctness and closure invariants.
- `sCount_zero`, `sCount_succ`: the recurrence for `s_j`.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment
open scoped List

section StartOne
variable {Γ C : Type*} (D : Lettered Γ C) (ℓ : Γ)

/-- `σ_ℓ(v)[: P_k] = σ_ℓ(v[:k])`. -/
theorem take_expand_cutP (v : List (List Γ)) (k : ℕ) :
    (expand ℓ v).take (cutP ℓ v k) = expand ℓ (v.take k) := by
  have h : expand ℓ v = expand ℓ (v.take k) ++ expand ℓ (v.drop k) := by
    rw [← expand_append, List.take_append_drop]
  rw [h]; exact List.take_left' rfl

/-- `σ_ℓ(v)[: P_{k+1} - 1] = σ_ℓ(v[:k]) X_k` (everything before the marker ending block `k`). -/
theorem take_expand_pre (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (expand ℓ v).take (cutP ℓ v (k + 1) - 1) = expand ℓ (v.take k) ++ v[k] := by
  rw [expand_split ℓ v k hk, ← List.append_assoc]
  refine List.take_left' ?_
  rw [cutP_succ ℓ v k hk]; simp [cutP]

/-- Every cut after a block is positive. -/
theorem cutP_succ_pos (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    1 ≤ cutP ℓ v (k + 1) := by
  rw [cutP_succ ℓ v k hk]; omega

/-- The cuts after blocks are strictly increasing. -/
theorem cutP_succ_strictMono (v : List (List Γ)) {k m : ℕ} (hkm : k < m) (hm : m < v.length) :
    cutP ℓ v (k + 1) < cutP ℓ v (m + 1) := by
  have h1 := cutP_succ ℓ v m hm
  have h2 := cutP_mono ℓ v (show k + 1 ≤ m by omega)
  omega

/-- The level-`(j+1)` core at index `k+1` is the level-`j` core
at index `E_k - 1` (just before the marker that ends block `k`). -/
theorem der_core_succ_eq (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (der D ℓ).core v (k + 1) = some (D.core (expand ℓ v) (cutP ℓ v (k + 1) - 1)) := by
  rw [der_core_succ D ℓ v k hk, fcore_core D ℓ v k hk, core_eq_kst, take_expand_pre ℓ v k hk]

/-- Start-core flags on `Option C`: the new start core `none` is one; `some c` is one iff
`c` is. -/
def stLift (st : C → Bool) : Option C → Bool
  | none => true
  | some c => st c

/-- Reading never leaves the non-start cores. -/
theorem stLift_closed (st : C → Bool) (hcl : ∀ c a, st c = false → st (D.κ a c) = false) :
    ∀ (c : Option C) (X : List Γ), stLift st c = false → stLift st ((der D ℓ).κ X c) = false
  | none, _, h => absurd h (by simp [stLift])
  | some c, X, h => by
      simp only [der_κ, fcore, stLift] at h ⊢
      have key : ∀ (w : List Γ) (c : C), st c = false → st (kst D c w) = false := by
        intro w
        induction w with
        | nil => exact fun _ h => h
        | cons a w ih => exact fun c h => ih _ (hcl c a h)
      exact key _ _ h

variable [DecidableEq Γ]

/-- An expansion of blocks avoiding `ℓ` has one marker per block. -/
theorem count_expand {v : List (List Γ)} (hv : ∀ X ∈ v, ℓ ∉ X) :
    (expand ℓ v).count ℓ = v.length := by
  induction v with
  | nil => simp
  | cons X v ih =>
    rw [expand_cons, List.count_append, List.count_cons_self,
      List.count_eq_zero.mpr (hv X List.mem_cons_self),
      ih (fun Y hY => hv Y (List.mem_cons_of_mem _ hY))]
    simp

/-- The prefix of length `s` contains more than `k` markers iff it contains the whole of
blocks `0..k`. -/
theorem count_take_expand {v : List (List Γ)} (hv : ∀ X ∈ v, ℓ ∉ X) {k : ℕ} (hk : k < v.length)
    (s : ℕ) : k + 1 ≤ ((expand ℓ v).take s).count ℓ ↔ cutP ℓ v (k + 1) ≤ s := by
  have hvt : ∀ m, ∀ X ∈ v.take m, ℓ ∉ X := fun m X hX => hv X (List.mem_of_mem_take hX)
  constructor
  · intro h
    by_contra hlt
    have hle : s ≤ cutP ℓ v (k + 1) - 1 := by omega
    obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := expand ℓ v) hle
    have h1 : ((expand ℓ v).take s).count ℓ ≤
        ((expand ℓ v).take (cutP ℓ v (k + 1) - 1)).count ℓ := by
      rw [← ht, List.count_append]; omega
    rw [take_expand_pre ℓ v k hk, List.count_append, count_expand ℓ (hvt k),
      List.count_eq_zero.mpr (hv _ (List.getElem_mem hk)), List.length_take,
      Nat.min_eq_left (by omega)] at h1
    omega
  · intro h
    obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := expand ℓ v) h
    rw [← ht, List.count_append, take_expand_cutP, count_expand ℓ (hvt _), List.length_take,
      Nat.min_eq_left (by omega)]
    omega

/-- If the start cores of the run of `σ_ℓ(v)` occupy
the prefix `[0, s)`, those of `v` in `Der(𝔇, ℓ)` occupy the prefix `[0, s')` with
`s' = min(|v|, 1 + #{x < s : σ_ℓ(v)[x] = ℓ})`. -/
theorem startCores_der (st : C → Bool) (v : List (List Γ)) (hℓ : ∀ X ∈ v, ℓ ∉ X) (s : ℕ)
    (hpre : ∀ x < (expand ℓ v).length, st (D.core (expand ℓ v) x) = true ↔ x < s) :
    ∀ x < v.length, stLift st ((der D ℓ).core v x) = true ↔
      x < min v.length (1 + ((expand ℓ v).take s).count ℓ) := by
  intro x hx
  rcases x with _ | k
  · simp [der_core_zero, stLift]; omega
  · rw [der_core_succ_eq D ℓ v k (by omega)]
    simp only [stLift]
    have hlt : cutP ℓ v (k + 1) - 1 < (expand ℓ v).length := by
      have := cutP_le_length ℓ v (k + 1)
      have := cutP_succ_pos ℓ v k (by omega)
      omega
    rw [hpre _ hlt]
    have := count_take_expand ℓ hℓ (k := k) (by omega) s
    have := cutP_succ_pos ℓ v k (by omega)
    constructor
    · intro h; exact lt_min hx (by omega)
    · intro h; have := lt_of_lt_of_le h (min_le_right _ _); omega

omit [DecidableEq Γ] in

/-- Distinct start cores below give distinct
start cores above. -/
theorem startCores_der_distinct (st : C → Bool) (v : List (List Γ))
    (hdist : ∀ x y, x < (expand ℓ v).length → y < (expand ℓ v).length →
      st (D.core (expand ℓ v) x) = true → st (D.core (expand ℓ v) y) = true → x ≠ y →
      D.core (expand ℓ v) x ≠ D.core (expand ℓ v) y) :
    ∀ x y, x < v.length → y < v.length → stLift st ((der D ℓ).core v x) = true →
      stLift st ((der D ℓ).core v y) = true → x ≠ y →
      (der D ℓ).core v x ≠ (der D ℓ).core v y := by
  have hlt : ∀ k, k < v.length → cutP ℓ v (k + 1) - 1 < (expand ℓ v).length := by
    intro k hk
    have := cutP_le_length ℓ v (k + 1)
    have := cutP_succ_pos ℓ v k hk
    omega
  intro x y hx hy hsx hsy hxy
  rcases x with _ | k <;> rcases y with _ | m
  · exact absurd rfl hxy
  · rw [der_core_zero, der_core_succ_eq D ℓ v m (by omega)]; simp
  · rw [der_core_zero, der_core_succ_eq D ℓ v k (by omega)]; simp
  · rw [der_core_succ_eq D ℓ v k (by omega)] at hsx ⊢
    rw [der_core_succ_eq D ℓ v m (by omega)] at hsy ⊢
    simp only [stLift] at hsx hsy
    simp only [ne_eq, Option.some.injEq]
    refine hdist _ _ (hlt k (by omega)) (hlt m (by omega)) hsx hsy ?_
    have h1 := cutP_succ_pos ℓ v k (by omega)
    have h2 := cutP_succ_pos ℓ v m (by omega)
    rcases Nat.lt_or_gt_of_ne (show k ≠ m by omega) with h | h
    · have := cutP_succ_strictMono ℓ v h (by omega); omega
    · have := cutP_succ_strictMono ℓ v h (by omega); omega

end StartOne

section StartTower
universe u v
variable {α : Type u} {Q : Type v}

/-- Start cores at level `i`: none at level `0` (where `⋆ = q0 ∈ Q`); at level `i+1` the new
`⋆_{i+1} = none` and the start cores of level `i`. -/
def isStart : (i : ℕ) → Cores Q i → Bool
  | 0, _ => false
  | i + 1, c => stLift (isStart i) c

/-- Among the first `n` indices, `min s n` lie below `s`. -/
theorem countP_range_lt (n s : ℕ) :
    (List.range n).countP (fun x => decide (x < s)) = min s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : n < s <;> simp [h] <;> omega

/-- A predicate that holds exactly on the prefix `[0, s)` of `[0, n)` holds `s` times. -/
theorem countP_range_of_prefix {n s : ℕ} {p : ℕ → Bool} (hs : s ≤ n)
    (hp : ∀ x < n, p x = true ↔ x < s) : (List.range n).countP p = s := by
  rw [List.countP_congr (q := fun x => decide (x < s)) (fun x hx => by
    rw [List.mem_range] at hx; simp [hp x hx]), countP_range_lt, Nat.min_eq_left hs]

variable [DecidableEq α] [Inhabited α]

/-- `s_j`: the number of indices of `u_j` whose core is a start core. -/
def sCount (D0 : Lettered α Q) (w : List α) (j : ℕ) : ℕ :=
  (List.range (hierOf w j).length).countP
    (fun x => isStart j ((tower D0 (markOf w) j).core (hierOf w j) x))

/-- For a nonempty `w`, at every level `j` of its canonical
hierarchy, the start-core indices of the run of `u_j` form the prefix `[0, s_j)`,
`s_j ≤ |u_j|`, and their cores are pairwise distinct; transitions never leave the
non-start cores. -/
theorem startCore_invariants (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) : ∀ j,
    (∀ x < (hierOf w j).length,
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) x) = true ↔ x < sCount D0 w j) ∧
    sCount D0 w j ≤ (hierOf w j).length ∧
    (∀ x y, x < (hierOf w j).length → y < (hierOf w j).length →
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) x) = true →
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) y) = true → x ≠ y →
      (tower D0 (markOf w) j).core (hierOf w j) x ≠
        (tower D0 (markOf w) j).core (hierOf w j) y) ∧
    (∀ c a, isStart j c = false → isStart j ((tower D0 (markOf w) j).κ a c) = false)
  | 0 => by
      have h0 : sCount D0 w 0 = 0 := by simp [sCount, isStart]
      refine ⟨fun x _ => by simp [h0, isStart], by omega, fun x y _ _ hx => by
        simp [isStart] at hx, fun _ _ _ => rfl⟩
  | j + 1 => by
      obtain ⟨hpre, hsle, hdist, hcl⟩ := startCore_invariants D0 hw j
      have hu := expand_hierOf hw j
      set s' := min (hierOf w (j + 1)).length
        (1 + ((hierOf w j).take (sCount D0 w j)).count (markOf w j)) with hs'
      have hpre' : ∀ x < (hierOf w (j + 1)).length,
          isStart (j + 1) ((tower D0 (markOf w) (j + 1)).core (hierOf w (j + 1)) x) = true ↔
            x < s' := by
        have := startCores_der (tower D0 (markOf w) j) (markOf w j) (isStart j)
          (hierOf w (j + 1)) (avoid_hierOf j) (sCount D0 w j) (by rw [hu]; exact hpre)
        rw [hu] at this
        exact this
      have hseq : sCount D0 w (j + 1) = s' :=
        countP_range_of_prefix (min_le_left _ _) hpre'
      refine ⟨by rw [hseq]; exact hpre', by rw [hseq]; exact min_le_left _ _, ?_, ?_⟩
      · have := startCores_der_distinct (tower D0 (markOf w) j) (markOf w j) (isStart j)
          (hierOf w (j + 1)) (by rw [hu]; exact hdist)
        exact this
      · exact stLift_closed (tower D0 (markOf w) j) (markOf w j) (isStart j) hcl

/-- `s_0 = 0`. -/
theorem sCount_zero (D0 : Lettered α Q) (w : List α) : sCount D0 w 0 = 0 := by
  simp [sCount, isStart]

/-- `s_{j+1} = min(|u_{j+1}|, 1 + #{x < s_j : u_j[x] = ℓ_j})`, so `s_1 = 1`. -/
theorem sCount_succ (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) = min (hierOf w (j + 1)).length
      (1 + ((hierOf w j).take (sCount D0 w j)).count (markOf w j)) := by
  have hu := expand_hierOf hw j
  obtain ⟨hpre, -, -, -⟩ := startCore_invariants D0 hw j
  refine countP_range_of_prefix (min_le_left _ _) ?_
  have := startCores_der (tower D0 (markOf w) j) (markOf w j) (isStart j)
    (hierOf w (j + 1)) (avoid_hierOf j) (sCount D0 w j) (by rw [hu]; exact hpre)
  rw [hu] at this
  exact this

end StartTower

end DeciNSSE.LetteredHierarchy
