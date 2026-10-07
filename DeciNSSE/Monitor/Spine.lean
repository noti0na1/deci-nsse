import DeciNSSE.Transfer.RankedExtension

/-! # The three-spine extension

One lower and two upper spines impose the prefix conditions for a left
witness. Fresh positive spine positions and fillers are disjoint sources and
sinks. At cut zero the spines use old variables, which may coincide; separation
applies to fresh positions and does not assume distinct roots.
-/

namespace DeciNSSE.Spine.Closure

open Safety

variable {n K : ℕ}

/-- Offset of an upper spine block: `Q` (`false`) after `P`, `Y` (`true`) after `Q`. -/
def zoff (m : ℕ) : Bool → ℕ
  | false => m
  | true => 2 * m

theorem zoff_le (m : ℕ) (s : Bool) : zoff m s ≤ 2 * m := by
  cases s <;> simp [zoff]; omega

theorem le_zoff (m : ℕ) (s : Bool) : m ≤ zoff m s := by
  cases s <;> simp [zoff]; omega

/-- The old root of an upper spine: `Xm` for `Q`, `Y` for `Y`. -/
def zroot (Xm Y : V K) : Bool → V K
  | false => Xm
  | true => Y

@[simp] theorem zroot_false (Xm Y : V K) : zroot Xm Y false = Xm := rfl
@[simp] theorem zroot_true (Xm Y : V K) : zroot Xm Y true = Y := rfl

/-- `P_j`, with `P_0 = X`. -/
def pv (X : V K) (m j : ℕ) : V (K + (3 * m + 2)) :=
  if h : 0 < j ∧ j ≤ m then ⟨K + j - 1, by omega⟩ else Fin.castAdd _ X

/-- `Q_j` (`s = false`, `Q_0 = Xm`) and `Y_j` (`s = true`, `Y_0 = Y`). -/
def zv (Xm Y : V K) (m : ℕ) (s : Bool) (j : ℕ) : V (K + (3 * m + 2)) :=
  if h : 0 < j ∧ j ≤ m then ⟨K + zoff m s + j - 1, by have := zoff_le m s; omega⟩
  else Fin.castAdd _ (zroot Xm Y s)

/-- The shared bottom filler `B`. -/
def botV (K m : ℕ) : V (K + (3 * m + 2)) := ⟨K + 3 * m, by omega⟩

/-- The shared top filler `T`. -/
def topV (K m : ℕ) : V (K + (3 * m + 2)) := ⟨K + 3 * m + 1, by omega⟩

section Layout

variable {X Xm Y : V K} {m : ℕ}

@[simp] theorem pv_zero (X : V K) (m : ℕ) : pv X m 0 = Fin.castAdd _ X := by simp [pv]

@[simp] theorem zv_zero (Xm Y : V K) (m : ℕ) (s : Bool) :
    zv Xm Y m s 0 = Fin.castAdd _ (zroot Xm Y s) := by simp [zv]

theorem pv_val (X : V K) (m j : ℕ) :
    (pv X m j).val = if 0 < j ∧ j ≤ m then K + j - 1 else X.val := by
  unfold pv; split_ifs <;> rfl

theorem zv_val (Xm Y : V K) (m : ℕ) (s : Bool) (j : ℕ) :
    (zv Xm Y m s j).val =
      if 0 < j ∧ j ≤ m then K + zoff m s + j - 1 else (zroot Xm Y s).val := by
  unfold zv; split_ifs <;> rfl

@[simp] theorem botV_val (K m : ℕ) : (botV K m).val = K + 3 * m := rfl
@[simp] theorem topV_val (K m : ℕ) : (topV K m).val = K + 3 * m + 1 := rfl

theorem castAdd_val (u : V K) : (Fin.castAdd (3 * m + 2) u).val = u.val := rfl

theorem pv_eq_castAdd {j : ℕ} (hj : j ≤ m) {u : V K}
    (h : pv X m j = Fin.castAdd _ u) : j = 0 ∧ u = X := by
  have hv := congrArg Fin.val h
  rw [pv_val, castAdd_val] at hv
  split_ifs at hv with hc
  · have := u.isLt; omega
  · exact ⟨by omega, Fin.ext hv.symm⟩

theorem zv_eq_castAdd {s : Bool} {j : ℕ} (hj : j ≤ m) {u : V K}
    (h : zv Xm Y m s j = Fin.castAdd _ u) : j = 0 ∧ u = zroot Xm Y s := by
  have hv := congrArg Fin.val h
  rw [zv_val, castAdd_val] at hv
  split_ifs at hv with hc
  · have := u.isLt; have := le_zoff m s; omega
  · exact ⟨by omega, Fin.ext hv.symm⟩

theorem pv_inj {j j' : ℕ} (hj : j ≤ m) (hj' : j' ≤ m)
    (h : pv X m j = pv X m j') : j = j' := by
  have hv := congrArg Fin.val h
  rw [pv_val, pv_val] at hv
  have := X.isLt
  split_ifs at hv <;> omega

theorem zv_eq_zv {s s' : Bool} {j j' : ℕ} (hj : j ≤ m) (hj' : j' ≤ m)
    (h : zv Xm Y m s j = zv Xm Y m s' j') : j = j' ∧ zroot Xm Y s = zroot Xm Y s' := by
  have hv := congrArg Fin.val h
  rw [zv_val, zv_val] at hv
  have h1 := (zroot Xm Y s).isLt
  have h2 := (zroot Xm Y s').isLt
  split_ifs at hv with ha hb hb
  · have hs : s = s' := by
      cases s <;> cases s' <;> simp [zoff] at hv ⊢ <;> omega
    subst hs
    exact ⟨by cases s <;> simp [zoff] at hv <;> omega, rfl⟩
  · have := le_zoff m s; omega
  · have := le_zoff m s'; omega
  · exact ⟨by omega, Fin.ext hv⟩

theorem pv_eq_zv {s : Bool} {j k : ℕ} (hj : j ≤ m) (hk : k ≤ m)
    (h : pv X m j = zv Xm Y m s k) : j = 0 ∧ k = 0 ∧ X = zroot Xm Y s := by
  have hv := congrArg Fin.val h
  rw [pv_val, zv_val] at hv
  have h1 := X.isLt
  have h2 := (zroot Xm Y s).isLt
  have := le_zoff m s
  split_ifs at hv <;> first | omega | exact ⟨by omega, by omega, Fin.ext hv⟩

theorem botV_ne_castAdd (u : V K) : botV K m ≠ Fin.castAdd _ u := by
  intro h; have := congrArg Fin.val h; simp at this; have := u.isLt; omega

theorem topV_ne_castAdd (u : V K) : topV K m ≠ Fin.castAdd _ u := by
  intro h; have := congrArg Fin.val h; simp at this; have := u.isLt; omega

theorem botV_ne_pv {j : ℕ} (hj : j ≤ m) : botV K m ≠ pv X m j := by
  intro h; have hv := congrArg Fin.val h; rw [botV_val, pv_val] at hv
  have := X.isLt; split_ifs at hv <;> omega

theorem topV_ne_zv {s : Bool} {j : ℕ} (hj : j ≤ m) : topV K m ≠ zv Xm Y m s j := by
  intro h; have hv := congrArg Fin.val h; rw [topV_val, zv_val] at hv
  have := (zroot Xm Y s).isLt; have := zoff_le m s; split_ifs at hv <;> omega

theorem botV_ne_topV : botV K m ≠ topV K m := by
  intro h; have := congrArg Fin.val h; simp at this

end Layout

/-- The fresh literals of `Ψ_w`. -/
def spineBlock (X Xm Y : V K) (w : List (Fin n)) : Constraint n (K + (3 * w.length + 2)) :=
  lowerSteps (pv X w.length) (botV K w.length) w ++
    (upperSteps (zv Xm Y w.length false) (topV K w.length) w ++
    (upperSteps (zv Xm Y w.length true) (topV K w.length) w ++
    [.eqTop (pv X w.length w.length), .eqBot (zv Xm Y w.length false w.length),
      .leF (zv Xm Y w.length true w.length) (fun _ => topV K w.length),
      .eqBot (botV K w.length), .eqTop (topV K w.length)]))

/-- Add one lower and two upper spines enforcing the three prefix conditions. -/
def _root_.DeciNSSE.Spine.extension (ψ : Constraint n K) (X Xm Y : V K) (w : List (Fin n)) :
    Constraint n (K + (3 * w.length + 2)) :=
  ψ.lift _ ++ spineBlock X Xm Y w

section Literals

variable {ψ : Constraint n K} {X Xm Y : V K} {w : List (Fin n)}

theorem mem_spineBlock {l : Lit n (K + (3 * w.length + 2))} :
    l ∈ spineBlock X Xm Y w ↔
      l ∈ lowerSteps (pv X w.length) (botV K w.length) w ∨
      l ∈ upperSteps (zv Xm Y w.length false) (topV K w.length) w ∨
      l ∈ upperSteps (zv Xm Y w.length true) (topV K w.length) w ∨
      l = .eqTop (pv X w.length w.length) ∨ l = .eqBot (zv Xm Y w.length false w.length) ∨
      l = .leF (zv Xm Y w.length true w.length) (fun _ => topV K w.length) ∨
      l = .eqBot (botV K w.length) ∨ l = .eqTop (topV K w.length) := by
  simp only [spineBlock, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]

/-- Lower constructor literals: lifted from `ψ`, or a `P`-link. -/
theorem mem_fLe {a : Fin n → V (K + (3 * w.length + 2))} {u : V (K + (3 * w.length + 2))}
    (h : Lit.fLe a u ∈ Spine.extension ψ X Xm Y w) :
    (∃ a' u', Lit.fLe a' u' ∈ ψ ∧ a = Fin.castAdd _ ∘ a' ∧ u = Fin.castAdd _ u') ∨
      ∃ j, ∃ hj : j < w.length,
        a = spineChildren w[j] (pv X w.length (j + 1)) (botV K w.length) ∧
          u = pv X w.length j := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (Spine.fLe_mem_lift h)
  · right
    rcases mem_spineBlock.mp h with h | h | h | h | h | h | h | h
    · obtain ⟨j, hj, he⟩ := mem_lowerSteps_iff.mp h
      simp only [lowerLink, Lit.fLe.injEq] at he
      exact ⟨j, hj, he.1, he.2⟩
    · exact absurd h (fLe_not_mem_upperSteps _ _ _ _ _)
    · exact absurd h (fLe_not_mem_upperSteps _ _ _ _ _)
    all_goals simp at h

/-- Upper constructor literals: lifted from `ψ`, a `Q`- or `Y`-link, or `Y_m ≤ f(T̄)`. -/
theorem mem_leF {v : V (K + (3 * w.length + 2))} {b : Fin n → V (K + (3 * w.length + 2))}
    (h : Lit.leF v b ∈ Spine.extension ψ X Xm Y w) :
    (∃ v' b', Lit.leF v' b' ∈ ψ ∧ v = Fin.castAdd _ v' ∧ b = Fin.castAdd _ ∘ b') ∨
      (∃ s j, ∃ hj : j < w.length, v = zv Xm Y w.length s j ∧
        b = spineChildren w[j] (zv Xm Y w.length s (j + 1)) (topV K w.length)) ∨
      (v = zv Xm Y w.length true w.length ∧ b = fun _ => topV K w.length) := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (Spine.leF_mem_lift h)
  · right
    rcases mem_spineBlock.mp h with h | h | h | h | h | h | h | h
    · exact absurd h (leF_not_mem_lowerSteps _ _ _ _ _)
    · obtain ⟨j, hj, he⟩ := mem_upperSteps_iff.mp h
      simp only [upperLink, Lit.leF.injEq] at he
      exact Or.inl ⟨false, j, hj, he.1, he.2⟩
    · obtain ⟨j, hj, he⟩ := mem_upperSteps_iff.mp h
      simp only [upperLink, Lit.leF.injEq] at he
      exact Or.inl ⟨true, j, hj, he.1, he.2⟩
    · simp at h
    · simp at h
    · simp only [Lit.leF.injEq] at h
      exact Or.inr h
    · simp at h
    · simp at h

theorem mem_eqTop {u : V (K + (3 * w.length + 2))} (h : Lit.eqTop u ∈ Spine.extension ψ X Xm Y w) :
    (∃ u', Lit.eqTop u' ∈ ψ ∧ u = Fin.castAdd _ u') ∨
      u = pv X w.length w.length ∨ u = topV K w.length := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (Spine.eqTop_mem_lift h)
  · right
    rcases mem_spineBlock.mp h with h | h | h | h | h | h | h | h
    · exact absurd h (eqTop_not_mem_lowerSteps _ _ _ _)
    · exact absurd h (eqTop_not_mem_upperSteps _ _ _ _)
    · exact absurd h (eqTop_not_mem_upperSteps _ _ _ _)
    · simp only [Lit.eqTop.injEq] at h; exact Or.inl h
    · simp at h
    · simp at h
    · simp at h
    · simp only [Lit.eqTop.injEq] at h; exact Or.inr h

theorem mem_eqBot {v : V (K + (3 * w.length + 2))} (h : Lit.eqBot v ∈ Spine.extension ψ X Xm Y w) :
    (∃ v', Lit.eqBot v' ∈ ψ ∧ v = Fin.castAdd _ v') ∨
      v = zv Xm Y w.length false w.length ∨ v = botV K w.length := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl (Spine.eqBot_mem_lift h)
  · right
    rcases mem_spineBlock.mp h with h | h | h | h | h | h | h | h
    · exact absurd h (eqBot_not_mem_lowerSteps _ _ _ _)
    · exact absurd h (eqBot_not_mem_upperSteps _ _ _ _)
    · exact absurd h (eqBot_not_mem_upperSteps _ _ _ _)
    · simp at h
    · simp only [Lit.eqBot.injEq] at h; exact Or.inl h
    · simp at h
    · simp only [Lit.eqBot.injEq] at h; exact Or.inr h
    · simp at h

theorem lift_mem {l : Lit n K} (hl : l ∈ ψ) :
    l.rename (Fin.castAdd (3 * w.length + 2)) ∈ Spine.extension ψ X Xm Y w :=
  List.mem_append_left _ (Spine.mem_lift_of_mem hl)

theorem block_mem {l : Lit n (K + (3 * w.length + 2))} (hl : l ∈ spineBlock X Xm Y w) :
    l ∈ Spine.extension ψ X Xm Y w :=
  List.mem_append_right _ hl

/-- The `P`-link at `P_j`. -/
theorem pLink_mem {j : ℕ} (hj : j < w.length) :
    Lit.fLe (spineChildren w[j] (pv X w.length (j + 1)) (botV K w.length))
      (pv X w.length j) ∈ Spine.extension ψ X Xm Y w :=
  block_mem (mem_spineBlock.mpr (Or.inl (mem_lowerSteps_iff.mpr ⟨j, hj, rfl⟩)))

/-- The `Q`-link (`s = false`) or `Y`-link (`s = true`) at `Z_j`. -/
theorem zLink_mem (s : Bool) {j : ℕ} (hj : j < w.length) :
    Lit.leF (zv Xm Y w.length s j)
      (spineChildren w[j] (zv Xm Y w.length s (j + 1)) (topV K w.length)) ∈
        Spine.extension ψ X Xm Y w := by
  apply block_mem
  apply mem_spineBlock.mpr
  cases s
  · exact Or.inr (Or.inl (mem_upperSteps_iff.mpr ⟨j, hj, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl (mem_upperSteps_iff.mpr ⟨j, hj, rfl⟩)))

theorem eqTop_pv_mem : Lit.eqTop (pv X w.length w.length) ∈ Spine.extension ψ X Xm Y w :=
  block_mem (mem_spineBlock.mpr (by simp))

theorem eqBot_qv_mem :
    Lit.eqBot (zv Xm Y w.length false w.length) ∈ Spine.extension ψ X Xm Y w :=
  block_mem (mem_spineBlock.mpr (by simp))

theorem yTerm_mem :
    Lit.leF (zv Xm Y w.length true w.length) (fun _ => topV K w.length) ∈
      Spine.extension ψ X Xm Y w :=
  block_mem (mem_spineBlock.mpr (by simp))

/-- Every upper spine variable `Z_k`, `k ≤ m`, roots an upper literal of `Ψ_w`:
a link (`k < m`), `Y_m ≤ f(T̄)`, or `Q_m = ⊥`. -/
theorem zv_upper_root (s : Bool) {k : ℕ} (hk : k ≤ w.length) :
    (∃ b, Lit.leF (zv Xm Y w.length s k) b ∈ Spine.extension ψ X Xm Y w) ∨
      (s = false ∧ k = w.length ∧
        Lit.eqBot (zv Xm Y w.length false w.length) ∈ Spine.extension ψ X Xm Y w) := by
  rcases Nat.lt_or_ge k w.length with hlt | hge
  · exact Or.inl ⟨_, zLink_mem s hlt⟩
  · have hk' : k = w.length := le_antisymm hk hge
    subst hk'
    cases s
    · exact Or.inr ⟨rfl, rfl, eqBot_qv_mem⟩
    · exact Or.inl ⟨_, yTerm_mem⟩

/-- Every `P_j`, `j ≤ m`, roots a lower literal: a link (`j < m`) or `P_m = ⊤`. -/
theorem pv_lower_root {j : ℕ} (hj : j ≤ w.length) :
    (j < w.length ∧ ∃ a, Lit.fLe a (pv X w.length j) ∈ Spine.extension ψ X Xm Y w) ∨
      (j = w.length ∧ Lit.eqTop (pv X w.length w.length) ∈ Spine.extension ψ X Xm Y w) := by
  rcases Nat.lt_or_ge j w.length with hlt | hge
  · exact Or.inl ⟨hlt, _, pLink_mem hlt⟩
  · exact Or.inr ⟨le_antisymm hj hge, eqTop_pv_mem⟩

end Literals

/-- Sources: `P_1..P_m` and `B`. -/
def Source (K m : ℕ) (z : V (K + (3 * m + 2))) : Prop :=
  K ≤ z.val ∧ (z.val < K + m ∨ z.val = K + 3 * m)

/-- Sinks: `Q_1..Q_m`, `Y_1..Y_m` and `T`. -/
def Sink (K m : ℕ) (z : V (K + (3 * m + 2))) : Prop :=
  (K + m ≤ z.val ∧ z.val < K + 3 * m) ∨ z.val = K + 3 * m + 1

section Classes

variable {X Xm Y : V K} {m : ℕ}

theorem source_pv {j : ℕ} (h : 0 < j ∧ j ≤ m) : Source K m (pv X m j) := by
  unfold Source; rw [pv_val, ite_eq_left h]; omega

theorem source_botV : Source K m (botV K m) := by simp [Source]

theorem sink_zv (s : Bool) {j : ℕ} (h : 0 < j ∧ j ≤ m) : Sink K m (zv Xm Y m s j) := by
  unfold Sink; rw [zv_val, ite_eq_left h]; have := zoff_le m s; have := le_zoff m s; omega

theorem sink_topV : Sink K m (topV K m) := by simp [Sink]

theorem not_sink_pv (j : ℕ) : ¬ Sink K m (pv X m j) := by
  unfold Sink; rw [pv_val]; have := X.isLt; split_ifs <;> omega

theorem not_source_zv (s : Bool) (j : ℕ) : ¬ Source K m (zv Xm Y m s j) := by
  unfold Source; rw [zv_val]; have := (zroot Xm Y s).isLt; have := le_zoff m s
  have := zoff_le m s; split_ifs <;> omega

theorem pv_lt_succ {j : ℕ} (hj : j < m) : (pv X m j).val < (pv X m (j + 1)).val := by
  rw [pv_val, pv_val]; have := X.isLt; split_ifs <;> omega

theorem zv_lt_succ (s : Bool) {j : ℕ} (hj : j < m) :
    (zv Xm Y m s j).val < (zv Xm Y m s (j + 1)).val := by
  rw [zv_val, zv_val]; have := (zroot Xm Y s).isLt; have := le_zoff m s
  split_ifs <;> omega

theorem pv_lt_botV (j : ℕ) : (pv X m j).val < (botV K m).val := by
  rw [pv_val, botV_val]; have := X.isLt; split_ifs <;> omega

theorem zv_lt_topV (s : Bool) (j : ℕ) : (zv Xm Y m s j).val < (topV K m).val := by
  rw [zv_val, topV_val]; have := (zroot Xm Y s).isLt; have := zoff_le m s
  split_ifs <;> omega

end Classes

section Extension

variable (ψ : Constraint n K) (X Xm Y : V K) (w : List (Fin n))

/-- `Ψ_w` is a ranked source/sink extension of `ψ`. -/
theorem extension_ranked :
    Ranked.Extension ψ (Spine.extension ψ X Xm Y w) (Source K w.length) (Sink K w.length)
      Fin.val where
  source_not_old := by intro z h; unfold Source at h; omega
  sink_not_old := by intro z h; unfold Sink at h; omega
  source_not_sink := by intro z h; unfold Source at h; unfold Sink; omega
  variable_cases := by
    intro z
    by_cases h : z.val < K
    · exact Or.inl ⟨⟨z.val, h⟩, rfl⟩
    · right; unfold Source Sink; have := z.isLt; omega
  old_mem := fun _ hl => lift_mem hl
  lower := by
    intro a c h
    rcases mem_fLe h with h | ⟨j, hj, rfl, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨fun i => ?_, not_sink_pv _⟩
      rcases spineChildren_eq_or w[j] i (pv X w.length (j + 1)) (botV K w.length) with h | h <;>
        rw [h]
      · exact ⟨source_pv ⟨by omega, by omega⟩, pv_lt_succ hj⟩
      · exact ⟨source_botV, pv_lt_botV j⟩
  upper := by
    intro c b h
    rcases mem_leF h with h | ⟨s, j, hj, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨fun i => ?_, not_source_zv _ _⟩
      rcases spineChildren_eq_or w[j] i (zv Xm Y w.length s (j + 1)) (topV K w.length) with
        h | h <;> rw [h]
      · exact ⟨sink_zv s ⟨by omega, by omega⟩, zv_lt_succ s hj⟩
      · exact ⟨sink_topV, zv_lt_topV s j⟩
    · exact Or.inr ⟨fun _ => ⟨sink_topV, zv_lt_topV true _⟩, not_source_zv _ _⟩

variable {ψ X Xm Y w}

/-- A derivation into a source is an identity. -/
theorem derives_into_source {a b : V (K + (3 * w.length + 2))}
    (h : Derives (Spine.extension ψ X Xm Y w) a b) (hb : Source K w.length b) : a = b :=
  (extension_ranked ψ X Xm Y w).derives_into_source h hb

/-- A derivation out of a sink is an identity. -/
theorem derives_out_of_sink {a b : V (K + (3 * w.length + 2))}
    (h : Derives (Spine.extension ψ X Xm Y w) a b) (ha : Sink K w.length a) : b = a :=
  (extension_ranked ψ X Xm Y w).derives_out_of_sink h ha

/-- Between old variables the closure of `Ψ_w` is that of `ψ`. -/
theorem derives_old_iff (u v : V K) :
    Derives (Spine.extension ψ X Xm Y w) (Fin.castAdd _ u) (Fin.castAdd _ v) ↔ Derives ψ u v :=
  (extension_ranked ψ X Xm Y w).derives_original u v

theorem derives_lift {u v : V K} (h : Derives ψ u v) :
    Derives (Spine.extension ψ X Xm Y w) (Fin.castAdd _ u) (Fin.castAdd _ v) :=
  (derives_old_iff u v).mpr h

end Extension

section Semantics

variable {ψ : Constraint n K} {X Xm Y : V K} {w : List (Fin n)}

/-- The canonical extension of an old assignment: spine variables follow the
traces of their roots along `w`, `B = ⊥`, `T = ⊤`. -/
def extend (A : V K → Tree n) (X Xm Y : V K) (w : List (Fin n))
    (z : V (K + (3 * w.length + 2))) : Tree n :=
  if h : z.val < K then A ⟨z.val, h⟩
  else if z.val < K + w.length then trace (A X) (w.take (z.val - K + 1))
  else if z.val < K + 2 * w.length then trace (A Xm) (w.take (z.val - (K + w.length) + 1))
  else if z.val < K + 3 * w.length then
    trace (A Y) (w.take (z.val - (K + 2 * w.length) + 1))
  else if z.val = K + 3 * w.length then Tree.bot else Tree.top

theorem extend_old (A : V K → Tree n) (u : V K) :
    extend A X Xm Y w (Fin.castAdd _ u) = A u := by
  simp [extend, u.isLt]

theorem extend_restrict (A : V K → Tree n) :
    extend A X Xm Y w ∘ Fin.castAdd _ = A := by
  funext u; exact extend_old A u

theorem extend_pv (A : V K → Tree n) {j : ℕ} (hj : j ≤ w.length) :
    extend A X Xm Y w (pv X w.length j) = trace (A X) (w.take j) := by
  by_cases h0 : j = 0
  · subst h0; simp [extend_old]
  · have hp : 0 < j ∧ j ≤ w.length := ⟨by omega, hj⟩
    have e : (pv X w.length j).val = K + j - 1 := by rw [pv_val, ite_eq_left hp]
    unfold extend
    rw [dite_eq_right (by omega), ite_eq_left (by omega), e]
    congr 2; omega

theorem extend_zv (A : V K → Tree n) (s : Bool) {j : ℕ} (hj : j ≤ w.length) :
    extend A X Xm Y w (zv Xm Y w.length s j) = trace (A (zroot Xm Y s)) (w.take j) := by
  by_cases h0 : j = 0
  · subst h0; simp [extend_old]
  · have hp : 0 < j ∧ j ≤ w.length := ⟨by omega, hj⟩
    have e : (zv Xm Y w.length s j).val = K + zoff w.length s + j - 1 := by
      rw [zv_val, ite_eq_left hp]
    unfold extend
    cases s
    · simp only [zoff] at e
      rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), e]
      simp only [zroot]; congr 2; omega
    · simp only [zoff] at e
      rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), e]
      simp only [zroot]; congr 2; omega

theorem extend_botV (A : V K → Tree n) :
    extend A X Xm Y w (botV K w.length) = Tree.bot := by
  have e : (botV K w.length).val = K + 3 * w.length := rfl
  unfold extend
  rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega)]

theorem extend_topV (A : V K → Tree n) :
    extend A X Xm Y w (topV K w.length) = Tree.top := by
  have e : (topV K w.length).val = K + 3 * w.length + 1 := rfl
  unfold extend
  rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega)]

/-- The spine extension is satisfied exactly when the original and added literals hold. -/
theorem sat_threeSpine_iff (B : V (K + (3 * w.length + 2)) → Tree n) :
    Covariant.Sat B (Spine.extension ψ X Xm Y w) ↔ Covariant.Sat (B ∘ Fin.castAdd _) ψ ∧
      Covariant.Sat B (lowerSteps (pv X w.length) (botV K w.length) w) ∧
      Covariant.Sat B (upperSteps (zv Xm Y w.length false) (topV K w.length) w) ∧
      Covariant.Sat B (upperSteps (zv Xm Y w.length true) (topV K w.length) w) ∧
      B (pv X w.length w.length) = Tree.top ∧
      B (zv Xm Y w.length false w.length) = Tree.bot ∧
      B (zv Xm Y w.length true w.length) ≤ Tree.node (fun _ => B (topV K w.length)) ∧
      B (botV K w.length) = Tree.bot ∧ B (topV K w.length) = Tree.top := by
  simp only [Spine.extension, spineBlock, sat_append, sat_lift, sat_cons, sat_nil, and_true]
  rfl

/-- A solution `A` of `ψ` extends to a solution of `Ψ_w` iff
(i) `A X` has a `⊤` on a prefix of `w`, (ii) `A Xm` has a `⊥` on a prefix of
`w`, and (iii) `A Y` has no `⊤` on a prefix of `w`. -/
theorem extension_restrict_iff (A : V K → Tree n) (hA : Covariant.Sat A ψ) :
    (∃ B, B ∘ Fin.castAdd _ = A ∧ Covariant.Sat B (Spine.extension ψ X Xm Y w)) ↔
      covPrefTop w (A X) ∧ covPrefBot w (A Xm) ∧ ¬ covPrefTop w (A Y) := by
  simp only [covPrefTop, covPrefBot, ← trace_eq_top_iff, ← trace_eq_bot_iff]
  constructor
  · rintro ⟨B, rfl, hB⟩
    obtain ⟨-, hP, hQ, hY, hPm, hQm, hYm, -, hT⟩ := (sat_threeSpine_iff B).mp hB
    have bP := Spine.lowerSteps_bound B _ _ _ hP
    have bQ := Spine.upperSteps_bound B _ _ _ hQ
    have bY := Spine.upperSteps_bound B _ _ _ hY
    simp only [pv_zero, zv_zero, zroot_false, zroot_true, Function.comp_apply] at bP bQ bY ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [hPm] at bP; exact (Tree.top_le_iff _).mp bP
    · rw [hQm] at bQ; exact (Tree.le_bot_iff _).mp bQ
    · rw [hT] at hYm
      exact (Spine.le_node_top_iff _).mp (le_trans bY hYm)
  · rintro ⟨hx, hxm, hy⟩
    refine ⟨extend A X Xm Y w, extend_restrict A, (sat_threeSpine_iff _).mpr ?_⟩
    refine ⟨by rw [extend_restrict]; exact hA, ?_, ?_, ?_, ?_, ?_, ?_, extend_botV A, extend_topV A⟩
    · exact Spine.lowerSteps_sat _ _ _ _ (A X) (fun j hj => extend_pv A hj) (extend_botV A)
        (by rw [hx]; exact Tree.top_ne_bot)
    · exact Spine.upperSteps_sat _ _ _ _ (A Xm) (fun j hj => extend_zv A false hj)
        (extend_topV A) (by rw [hxm]; exact Tree.bot_ne_top)
    · exact Spine.upperSteps_sat _ _ _ _ (A Y) (fun j hj => extend_zv A true hj)
        (extend_topV A) hy
    · rw [extend_pv A le_rfl, List.take_length]; exact hx
    · rw [extend_zv A false le_rfl, List.take_length]; exact hxm
    · rw [extend_zv A true le_rfl, List.take_length, extend_topV]
      exact (Spine.le_node_top_iff _).mpr hy

/-- satisfiability form. -/
theorem extension_sat_iff :
    (∃ B, Covariant.Sat B (Spine.extension ψ X Xm Y w)) ↔
      ∃ A, Covariant.Sat A ψ ∧ covPrefTop w (A X) ∧ covPrefBot w (A Xm) ∧ ¬ covPrefTop w (A Y) := by
  constructor
  · rintro ⟨B, hB⟩
    have hA : Covariant.Sat (B ∘ Fin.castAdd _) ψ := ((sat_threeSpine_iff B).mp hB).1
    exact ⟨_, hA, (extension_restrict_iff _ hA).mp ⟨B, rfl, hB⟩⟩
  · rintro ⟨A, hA, h⟩
    obtain ⟨B, -, hB⟩ := (extension_restrict_iff A hA).mpr h
    exact ⟨B, hB⟩

end Semantics

end DeciNSSE.Spine.Closure
