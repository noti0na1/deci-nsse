import DeciNSSE.Holes.Cores

/-! # Suffix occurrences and ordinary cores

Bridge suffixes characterise the original positions retained by successive
hierarchy levels. The greatest retained position determines a suffix whose
occurrences control comparisons between equal supports.
-/

namespace DeciNSSE.CoreOccurrences
open DeciNSSE.LetteredHierarchy DeciNSSE.Cores

universe u

section Expansion
variable {α : Type u}

theorem expandTo_append (ℓ : (i : ℕ) → Alph α i) :
    ∀ h (a b : List (Alph α h)),
      expandTo ℓ h (a ++ b) = expandTo ℓ h a ++ expandTo ℓ h b
  | 0, _, _ => rfl
  | h + 1, a, b => by
      simp only [expandTo, expand_append, expandTo_append ℓ h]

variable [DecidableEq α] [Inhabited α]

def bridge (w : List α) : ℕ → List α
  | 0 => []
  | h + 1 => bridge w h ++ expandTo (markOf w) h [markOf w h]

theorem drop_before_cut {Γ : Type*} (ℓ : Γ) (v : List (List Γ))
    (x : ℕ) (hx : x < v.length) :
    (expand ℓ v).drop (cutP ℓ v (x + 1) - 1) = ℓ :: expand ℓ (v.drop (x + 1)) := by
  rw [expand_split ℓ v x hx, ← List.append_assoc]
  apply List.drop_left'
  rw [cutP_succ ℓ v x hx]
  simp [cutP]

theorem corePos_live_mono {w : List α} (hw : w ≠ []) :
    ∀ h x y, x ≤ y → y < (hierOf w h).length →
      ∀ p, corePos w h x = some p → ∃ q, corePos w h y = some q
  | 0, x, y, _, _, _, _ => ⟨y, rfl⟩
  | h + 1, 0, _, _, _, _, hp => by simp [corePos] at hp
  | h + 1, x + 1, 0, hxy, _, _, _ => by omega
  | h + 1, x + 1, y + 1, hxy, hy, p, hp => by
      apply corePos_live_mono hw h _ _ ?_ ?_ p hp
      · exact Nat.sub_le_sub_right (cutP_mono _ _ hxy) 1
      · have hc := cutP_le_length (markOf w h) (hierOf w (h + 1)) (y + 1)
        have hp := cutP_succ_pos (markOf w h) (hierOf w (h + 1)) y (by omega)
        rw [expand_hierOf hw h] at hc
        omega

theorem drop_corePos {w : List α} (hw : w ≠ []) :
    ∀ h x, x < (hierOf w h).length → ∀ p, corePos w h x = some p →
      w.drop p = bridge w h ++ expandTo (markOf w) h ((hierOf w h).drop x)
  | 0, x, _, p, hp => by
      have : x = p := Option.some.inj hp
      subst p
      rfl
  | h + 1, 0, _, _, hp => by simp [corePos] at hp
  | h + 1, x + 1, hx, p, hp => by
      have hc := cutP_le_length (markOf w h) (hierOf w (h + 1)) (x + 1)
      have hpos := cutP_succ_pos (markOf w h) (hierOf w (h + 1)) x (by omega)
      rw [expand_hierOf hw h] at hc
      have hi : cutP (markOf w h) (hierOf w (h + 1)) (x + 1) - 1 <
          (hierOf w h).length := by omega
      rw [drop_corePos hw h _ hi p hp]
      rw [← expand_hierOf hw h, drop_before_cut _ _ x (by omega)]
      change bridge w h ++ expandTo (markOf w) h
        ([markOf w h] ++ expand (markOf w h) ((hierOf w (h + 1)).drop (x + 1))) = _
      rw [expandTo_append, ← List.append_assoc]
      rfl

theorem drop_hier_last {w : List α} (hw : w ≠ []) (h : ℕ) :
    (hierOf w h).drop ((hierOf w h).length - 1) = [markOf w h] := by
  rw [List.drop_length_sub_one (hierOf_ne_nil hw h)]
  simp [markOf, List.getLast?_eq_some_getLast (hierOf_ne_nil hw h)]

theorem corePos_succ_iff {w : List α} (hw : w ≠ []) (h p : ℕ) :
    (∃ y < (hierOf w (h + 1)).length, corePos w (h + 1) y = some p) ↔
      ∃ x, x + 1 < (hierOf w h).length ∧
        (hierOf w h)[x]? = some (markOf w h) ∧ corePos w h x = some p := by
  have hu := hierOf_ne_nil hw h
  have hh : hierOf (hierOf w h) 1 = hierOf w (h + 1) := rfl
  have hm : markOf (hierOf w h) 0 = markOf w h := rfl
  constructor
  · rintro ⟨y, hy, hp⟩
    cases y with
    | zero => simp [corePos] at hp
    | succ y =>
      let x := cutP (markOf w h) (hierOf w (h + 1)) (y + 1) - 1
      have hx : ∃ z < (hierOf (hierOf w h) 1).length,
          corePos (hierOf w h) 1 z = some x := ⟨y + 1, hh.symm ▸ hy, rfl⟩
      obtain ⟨hlt, he⟩ := (corePos_one_iff hu x).mp hx
      exact ⟨x, hlt, he, hp⟩
  · rintro ⟨x, hx, hm', hp⟩
    obtain ⟨y, hy, he⟩ := (corePos_one_iff hu x).mpr ⟨hx, hm'⟩
    cases y with
    | zero => simp [corePos] at he
    | succ y =>
      have he' : cutP (markOf w h) (hierOf w (h + 1)) (y + 1) - 1 = x :=
        Option.some.inj he
      refine ⟨y + 1, hy, ?_⟩
      change corePos w h _ = some p
      rw [he']
      exact hp

theorem corePos_iff_bridge {w : List α} (hw : w ≠ []) :
    ∀ h p, (∃ x < (hierOf w h).length, corePos w h x = some p) ↔
      p + (bridge w h).length < w.length ∧ bridge w h <+: w.drop p
  | 0, p => by
      simp only [hierOf, corePos, bridge, List.length_nil, Nat.add_zero,
        List.nil_prefix, and_true, Option.some.injEq]
      exact ⟨fun ⟨x, hx, he⟩ => he ▸ hx, fun hp => ⟨p, hp, rfl⟩⟩
  | h + 1, p => by
      constructor
      · rintro ⟨x, hx, hp⟩
        have he := drop_corePos hw (h + 1) x hx p hp
        have hne : (hierOf w (h + 1)).drop x ≠ [] := by
          intro he
          have := List.drop_eq_nil_iff.mp he
          omega
        have hpos := List.length_pos_iff.mpr (expandTo_ne_nil (markOf w) (h + 1) _ hne)
        have hlen := congrArg List.length he
        have hpw := corePos_lt hw (h + 1) x hx p hp
        simp only [List.length_drop, List.length_append] at hlen
        exact ⟨by omega, he ▸ List.prefix_append _ _⟩
      · rintro ⟨hlt, hpref⟩
        have hsmall : p + (bridge w h).length < w.length := by
          simp only [bridge, List.length_append] at hlt
          omega
        have hpre : bridge w h <+: w.drop p :=
          (List.prefix_append _ _).trans hpref
        obtain ⟨x, hx, hp⟩ := (corePos_iff_bridge hw h p).mpr ⟨hsmall, hpre⟩
        have he := drop_corePos hw h x hx p hp
        have hpref' : expandTo (markOf w) h [markOf w h] <+:
            expandTo (markOf w) h ((hierOf w h).drop x) := by
          rw [he] at hpref
          exact (List.prefix_append_right_inj _).mp hpref
        have hdecode : [markOf w h] <+: (hierOf w h).drop x :=
          (expandTo_prefix_iff (markOf w) h _ _
            (admissible_of_subset _ _ _ _ (by simpa using markOf_mem hw h)
              (admissible_hierOf hw h))
            (admissible_of_subset _ _ _ _ (List.drop_subset _ _) (admissible_hierOf hw h))).mp hpref'
        have hm : (hierOf w h)[x]? = some (markOf w h) := by
          simpa only [List.singleton_prefix_iff_head?_eq_some, List.head?_drop] using hdecode
        have hxn : x + 1 < (hierOf w h).length := by
          by_contra hn
          have hxlast : x = (hierOf w h).length - 1 := by omega
          rw [hxlast, drop_hier_last hw h] at he
          have hlen := congrArg List.length he
          change (w.drop p).length = (bridge w (h + 1)).length at hlen
          simp only [List.length_drop] at hlen
          omega
        exact (corePos_succ_iff hw h p).mpr ⟨x, hxn, hm, hp⟩

theorem rho_eq_bridge {w r : List α} {h : ℕ} (hr : rho w h = some r) :
    r = bridge w (h + 1) := by
  by_cases hw : w = []
  · simp [rho, hw] at hr
  · simp only [rho, ite_eq_right hw, Option.map_eq_some_iff] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    have hn := List.length_pos_iff.mpr (hierOf_ne_nil hw h)
    rw [drop_corePos hw h _ (by omega) p hp, drop_hier_last hw h]
    rfl

theorem rho_defined_of_live {w : List α} (hw : w ≠ []) (h x p : ℕ)
    (hx : x < (hierOf w h).length) (hp : corePos w h x = some p) :
    ∃ r, rho w h = some r := by
  obtain ⟨q, hq⟩ := corePos_live_mono hw h x ((hierOf w h).length - 1)
    (by omega) (by omega) p hp
  exact ⟨w.drop q, by simp [rho, hw, hq]⟩

theorem no_live_succ_of_rho_none {w : List α} (hw : w ≠ []) (h : ℕ)
    (hr : rho w h = none) :
    ¬ ∃ x < (hierOf w (h + 1)).length, ∃ p, corePos w (h + 1) x = some p := by
  rintro ⟨x, hx, p, hp⟩
  obtain ⟨y, hy, _, hp'⟩ := (corePos_succ_iff hw h p).mp ⟨x, hx, hp⟩
  obtain ⟨r, he⟩ := rho_defined_of_live hw h y p (by omega) hp'
  rw [hr] at he
  cases he

theorem corePos_succ_iff_occurrence {w : List α} (hw : w ≠ []) (h p : ℕ) :
    (∃ x < (hierOf w (h + 1)).length, corePos w (h + 1) x = some p) ↔
      ∃ r, rho w h = some r ∧ p + r.length < w.length ∧ r <+: w.drop p := by
  cases hr : rho w h with
  | none =>
    constructor
    · rintro ⟨x, hx, hp⟩
      exact (no_live_succ_of_rho_none hw h hr ⟨x, hx, p, hp⟩).elim
    · rintro ⟨r, he, _⟩
      cases he
  | some r =>
    rw [corePos_iff_bridge hw]
    have he := rho_eq_bridge hr
    simp [he]

end Expansion

end DeciNSSE.CoreOccurrences

namespace DeciNSSE.CoreOccurrences
open DeciNSSE.Cores DeciNSSE.LetteredHierarchy

universe u
variable {α : Type u} [DecidableEq α]

/-- The original positions represented by ordinary cores at a canonical hierarchy level. -/
def ordinaryCores [Inhabited α] (w : List α) (j : ℕ) : Set ℕ :=
  {p | ∃ x < (hierOf w j).length, corePos w j x = some p}

end DeciNSSE.CoreOccurrences

namespace DeciNSSE.CoreOccurrences
open DeciNSSE.Cores DeciNSSE.LetteredHierarchy
universe u
variable {α : Type u} [DecidableEq α]

private theorem corePos_order [Inhabited α] {w : List α} (hw : w ≠ []) :
    ∀ j x y, x ≤ y → y < (hierOf w j).length →
      ∀ p q, corePos w j x = some p → corePos w j y = some q → p ≤ q
  | 0, x, y, hxy, _, p, q, hp, hq => by
      have hp' : x = p := Option.some.inj hp
      have hq' : y = q := Option.some.inj hq
      omega
  | j + 1, 0, _, _, _, _, _, hp, _ => by simp [corePos] at hp
  | j + 1, x + 1, 0, hxy, _, _, _, _, _ => by omega
  | j + 1, x + 1, y + 1, hxy, hy, p, q, hp, hq => by
      apply corePos_order hw j _ _ ?_ ?_ p q hp hq
      · exact Nat.sub_le_sub_right (cutP_mono _ _ (by omega)) 1
      · have hc := cutP_le_length (markOf w j) (hierOf w (j + 1)) (y + 1)
        have hpos := cutP_succ_pos (markOf w j) (hierOf w (j + 1)) y (by omega)
        rw [expand_hierOf hw j] at hc
        omega

theorem rho_at_greatest [Inhabited α] {w : List α} {j f : ℕ}
    (hw : w ≠ []) (hmax : IsGreatest (ordinaryCores w j) f) :
    rho w j = some (w.drop f) := by
  obtain ⟨x, hx, hp⟩ := hmax.1
  have hlast : (hierOf w j).length - 1 < (hierOf w j).length := by omega
  obtain ⟨q, hq⟩ := corePos_live_mono hw j x ((hierOf w j).length - 1)
    (by omega) hlast f hp
  have hqf := hmax.2 (show q ∈ ordinaryCores w j from ⟨_, hlast, hq⟩)
  have hfq := corePos_order hw j x _ (by omega) hlast f q hp hq
  have he : q = f := by omega
  subst q
  simp [rho, hw, hq]

end DeciNSSE.CoreOccurrences
