import DeciNSSE.Holes.Supports

/-! # Persistent cores and support plateaus

Prefix decoding follows cores through admissible expansions. Equal nonempty
supports at two levels force a repeated original reader core.
-/

set_option autoImplicit false

namespace DeciNSSE.Cores
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.Supports
open scoped List

universe u v

section PrefixCode
variable {Γ : Type*}

/-- The one-level packet code reflects prefixes, including empty packet bodies. -/
theorem expand_prefix_iff {ℓ : Γ} {a b : List (List Γ)}
    (ha : ∀ X ∈ a, ℓ ∉ X) (hb : ∀ X ∈ b, ℓ ∉ X) :
    expand ℓ a <+: expand ℓ b ↔ a <+: b := by
  obtain ⟨a', rfl⟩ := lift_avoid ha
  obtain ⟨b', rfl⟩ := lift_avoid hb
  rw [← mcode_enc, ← mcode_enc, DeciNSSE.Desubstitution.MarkerCode.enc_prefix_iff,
    prefix_map_inj Subtype.val_injective]

variable {α : Type u}

/-- Prefix decoding through the entire admissible tower). -/
theorem expandTo_prefix_iff (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (a b : List (Alph α j)), Admissible ℓ j a → Admissible ℓ j b →
      (expandTo ℓ j a <+: expandTo ℓ j b ↔ a <+: b)
  | 0, _, _, _, _ => Iff.rfl
  | j + 1, a, b, ha, hb => by
      change expandTo ℓ j (expand (ℓ j) a) <+:
        expandTo ℓ j (expand (ℓ j) b) ↔ a <+: b
      rw [expandTo_prefix_iff ℓ j _ _ ha.2 hb.2, expand_prefix_iff ha.1 hb.1]

/-- Admissibility is inherited by a word using a subset of the letters. -/
theorem admissible_of_subset (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (a b : List (Alph α j)), a ⊆ b → Admissible ℓ j b → Admissible ℓ j a
  | 0, _, _, _, _ => trivial
  | j + 1, a, b, hab, hb => by
      refine ⟨fun X hX => hb.1 X (hab hX), admissible_of_subset ℓ j _ _ ?_ hb.2⟩
      intro x hx
      obtain ⟨X, hX, hx⟩ := List.mem_flatMap.mp hx
      exact List.mem_flatMap.mpr ⟨X, hab hX, hx⟩

variable [DecidableEq α] [Inhabited α]

end PrefixCode

section Coordinates
variable {α : Type u} [DecidableEq α] [Inhabited α]

/-- The original position of a live core. `none` represents a symbolic start core.
At a successor level the core is that of the preceding packet's closing marker. -/
def corePos (w : List α) : ℕ → ℕ → Option ℕ
  | 0, x => some x
  | _ + 1, 0 => none
  | h + 1, x + 1 =>
      corePos w h (cutP (markOf w h) (hierOf w (h + 1)) (x + 1) - 1)

/-- The hierarchy form is partial: an undefined final core does not give a chain word. -/
def rho (w : List α) (h : ℕ) : Option (List α) :=
  if w = [] then none else
    (corePos w h ((hierOf w h).length - 1)).map (w.drop ·)

/-- A live core really is a position in the original word. -/
theorem corePos_lt {w : List α} (hw : w ≠ []) :
    ∀ h x, x < (hierOf w h).length → ∀ p, corePos w h x = some p → p < w.length
  | 0, x, hx, p, hp => by
      have he : x = p := Option.some.inj hp
      simpa [← he, hierOf] using hx
  | h + 1, 0, _, _, hp => by simp [corePos] at hp
  | h + 1, x + 1, hx, p, hp => by
      apply corePos_lt hw h _ ?_ p hp
      have hc := cutP_le_length (markOf w h) (hierOf w (h + 1)) (x + 1)
      have hp := cutP_succ_pos (markOf w h) (hierOf w (h + 1)) x (by omega)
      rw [expand_hierOf hw h] at hc
      omega

variable {Q : Type v}

/-- The positional core map realizes the existing tower's original-state map. -/
theorem orig_core_eq (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) :
    ∀ h x, x < (hierOf w h).length →
      orig h ((tower D0 (markOf w) h).core (hierOf w h) x) =
        (corePos w h x).map (D0.core w)
  | 0, _, _ => rfl
  | h + 1, 0, _ => rfl
  | h + 1, x + 1, hx => by
      have he := der_core_succ_eq (tower D0 (markOf w) h) (markOf w h)
        (hierOf w (h + 1)) x (by omega)
      rw [expand_hierOf hw h] at he
      change orig (h + 1) ((der (tower D0 (markOf w) h) (markOf w h)).core
        (hierOf w (h + 1)) (x + 1)) = _
      rw [he]
      change orig h _ = (corePos w h _).map (D0.core w)
      apply orig_core_eq D0 hw h
      have hc := cutP_le_length (markOf w h) (hierOf w (h + 1)) (x + 1)
      have hp := cutP_succ_pos (markOf w h) (hierOf w (h + 1)) x (by omega)
      rw [expand_hierOf hw h] at hc
      omega

variable [DecidableEq Q]

/-- Support as the states at all live positional cores. This does not yet identify
those positions with occurrences of `rho`. -/
theorem mem_supp_iff_corePos (D0 : Lettered α Q) {w : List α} (hw : w ≠ [])
    (h : ℕ) (q : Q) :
    q ∈ supp D0 w h ↔ ∃ x < (hierOf w h).length,
      ∃ p, corePos w h x = some p ∧ D0.core w p = q := by
  rw [mem_supp]
  constructor
  · rintro ⟨x, hx, he⟩
    rw [orig_core_eq D0 hw h x hx, Option.map_eq_some_iff] at he
    exact ⟨x, hx, he⟩
  · rintro ⟨x, hx, p, hp, hq⟩
    exact ⟨x, hx, by rw [orig_core_eq D0 hw h x hx, hp]; simp [hq]⟩

end Coordinates

section Occurrences
variable {α : Type u} [DecidableEq α] [Inhabited α]

variable {Q : Type v} [DecidableEq Q]

/-- At the first level, live cores are exactly non-final occurrences of the marker. -/
theorem corePos_one_iff {w : List α} (hw : w ≠ []) (p : ℕ) :
    (∃ x < (hierOf w 1).length, corePos w 1 x = some p) ↔
      p + 1 < w.length ∧ w[p]? = some (markOf w 0) := by
  let ℓ := markOf w 0
  let v := hierOf w 1
  have hex : expand ℓ v = w := expand_hierOf hw 0
  have hav : ∀ X ∈ v, ℓ ∉ X := avoid_hierOf 0
  constructor
  · rintro ⟨x, hx, hp⟩
    change x < v.length at hx
    cases x with
    | zero => simp [corePos] at hp
    | succ k =>
        have he : cutP ℓ v (k + 1) - 1 = p := Option.some.inj hp
        have hcut := cutP_succ ℓ v k (by omega)
        have hpos := cutP_succ_pos ℓ v k (by omega)
        have hcut' := cutP_succ ℓ v (k + 1) hx
        have hle := cutP_le_length ℓ v (k + 1 + 1)
        rw [hex] at hle
        refine ⟨by omega, ?_⟩
        have hg := getElem?_expand_marker ℓ v (show k < v.length by omega)
        rw [hex] at hg
        have hidx : p = cutP ℓ v k + v[k].length := by omega
        rw [hidx]
        exact hg
  · rintro ⟨hp, hmark⟩
    have hlt : p < (expand ℓ v).length := by rw [hex]; omega
    obtain ⟨k, hk, o, ho, hpo⟩ := pos_decomp ℓ v hlt
    have hoe : o = v[k].length := by
      by_contra hne
      have hol : o < v[k].length := by omega
      have hg := getElem?_expand_cutP ℓ v hk hol
      rw [hex, ← hpo, hmark] at hg
      exact hav v[k] (List.getElem_mem hk) (List.mem_of_getElem? hg.symm)
    have hcut := cutP_succ ℓ v k hk
    have hx : k + 1 < v.length := by
      by_contra hn
      have he : k + 1 = v.length := by omega
      have htotal : cutP ℓ v (k + 1) = w.length := by
        rw [he, ← length_expand, hex]
      omega
    refine ⟨k + 1, hx, ?_⟩
    change some (cutP ℓ v (k + 1) - 1) = some p
    congr 1
    omega

end Occurrences

end DeciNSSE.Cores
