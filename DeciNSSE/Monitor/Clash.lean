import DeciNSSE.Monitor.Closure
import DeciNSSE.Monitor.Events

/-! # Clashes of the four-spine extension

Every new label clash of the four-spine extension is a readiness, terminal
child, cross or self event, and each event creates a clash. The lower spine
from `σY` adds no event: against old upper bounds it gives top readiness,
against the upper spine from `σX` the sign dual of a bridge from `X` to `Y`,
that is readiness or a cross admission, and against the upper spine from `Y`
it never clashes.
-/

namespace DeciNSSE.Spine.Closure

open FiniteVariance Events

variable {n k : ℕ}

/-- A label clash is a derived pair from a lower root to an upper root with
incompatible labels. -/
theorem labelClash_iff_roots {N : ℕ} (Φ : Constraint n N) :
    LabelClash Φ ↔ ∃ u v, Derives Φ u v ∧
      ((Lit.eqTop u ∈ Φ ∧ Lit.eqBot v ∈ Φ) ∨
        (Lit.eqTop u ∈ Φ ∧ ∃ b, Lit.leF v b ∈ Φ) ∨
        ((∃ a, Lit.fLe a u ∈ Φ) ∧ Lit.eqBot v ∈ Φ)) := by
  constructor
  · rintro ⟨x, ⟨⟨u, hu, hux⟩, ⟨v, hv, hxv⟩⟩ | ⟨⟨u, hu, hux⟩, ⟨v, b, hv, hxv⟩⟩ |
      ⟨⟨a, u, hu, hux⟩, ⟨v, hv, hxv⟩⟩⟩
    · exact ⟨u, v, hux.trans hxv, Or.inl ⟨hu, hv⟩⟩
    · exact ⟨u, v, hux.trans hxv, Or.inr (Or.inl ⟨hu, b, hv⟩)⟩
    · exact ⟨u, v, hux.trans hxv, Or.inr (Or.inr ⟨⟨a, hu⟩, hv⟩)⟩
  · rintro ⟨u, v, h, ⟨hu, hv⟩ | ⟨hu, b, hv⟩ | ⟨⟨a, hu⟩, hv⟩⟩
    · exact ⟨v, Or.inl ⟨⟨u, hu, h⟩, ⟨v, hv, .refl v⟩⟩⟩
    · exact ⟨v, Or.inr (Or.inl ⟨⟨u, hu, h⟩, ⟨v, b, hv, .refl v⟩⟩)⟩
    · exact ⟨v, Or.inr (Or.inr ⟨⟨a, u, hu, h⟩, ⟨v, hv, .refl v⟩⟩)⟩

section Events

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

@[simp] theorem lroot_false : lroot X Y false = X := rfl

@[simp] theorem lroot_true : lroot X Y true = flipV Y := rfl

/-- A bottom below a lower spine is readiness at its cut. -/
theorem occurs_of_low_bot (hf : FlipClosed ψ) (s : Bool) {j : ℕ} (hj : j ≤ w.length)
    {v : V (2 * k)} (hU : UAt ψ (lroot X Y s) w j v) (hv : Lit.eqBot v ∈ ψ) : Occurs ψ X Y w := by
  cases s
  · exact Or.inl ⟨j, hj, Or.inl ⟨v, hU, hv⟩⟩
  · have hL : LAt ψ w (flipV (flipV Y)) j (flipV v) := (lAt_flip_iff hf).mpr (by simpa using hU)
    rw [flipV_flipV] at hL
    exact Or.inl ⟨j, hj, Or.inr (Or.inl ⟨flipV v, hL, hf _ hv⟩)⟩

/-- A top above an upper spine is readiness at its cut. -/
theorem occurs_of_up_top (hf : FlipClosed ψ) (s : Bool) {j : ℕ} (hj : j ≤ w.length)
    {u : V (2 * k)} (hL : LAt ψ w (flipV (lroot X Y s)) j u) (hu : Lit.eqTop u ∈ ψ) :
    Occurs ψ X Y w := by
  cases s
  · exact occurs_of_low_bot hf false hj ((lAt_flip_iff hf).mp hL) (hf _ hu)
  · rw [lroot_true, flipV_flipV] at hL
    exact Or.inl ⟨j, hj, Or.inr (Or.inl ⟨u, hL, hu⟩)⟩

/-- A bridge from `X` to `Y` ending at the terminal cut is readiness or a cross admission. -/
theorem occurs_of_bridge_cross {j : ℕ} (hj : j ≤ w.length) (h : BridgeF ψ X w Y w.length j) :
    Occurs ψ X Y w := by
  obtain ⟨a, b, d, ha, hb, hw, v, hU, hL⟩ := h
  have hp : w.drop a <+: w.drop b := prefix_of_take_eq ha hw
  rcases Nat.lt_or_ge b a with hba | hab
  · exact Or.inr (Or.inr ⟨b, a, hba, by omega, hp, Or.inl ⟨v, hL, hU⟩⟩)
  · obtain rfl : a = b := by omega
    exact Or.inl ⟨a, by omega, Or.inr (Or.inr ⟨v, hU, hL⟩)⟩

/-- A bridge from `X` to `σX` ending at the terminal cut is a self admission. -/
theorem occurs_of_bridge_self (hf : FlipClosed ψ) (hc : SignCoherent c ψ) {j : ℕ}
    (hj : j ≤ w.length) (h : BridgeF ψ X w (flipV X) j w.length) : Occurs ψ X Y w := by
  obtain ⟨a, b, d, ha, hb, hw, v, hU, hL⟩ := h
  have hp : w.drop b <+: w.drop a := prefix_of_take_eq hb hw.symm
  rcases Nat.lt_or_ge a b with hab | hba
  · exact Or.inr (Or.inr ⟨a, b, hab, by omega, hp,
      Or.inr (self_iff.mpr ⟨v, hU, (lAt_flip_iff hf).mp hL⟩)⟩)
  · obtain rfl : a = b := by omega
    exact (not_uAt_lAt_flip hc hU hL).elim

/-- A bridge from the terminal top `P_m` to an upper spine position is an event. -/
theorem occurs_of_top_bridge (hf : FlipClosed ψ) (hc : SignCoherent c ψ) (s : Bool) {j : ℕ}
    (hj : j ≤ w.length) (h : BridgeF ψ X w (flipV (lroot X Y s)) w.length j) : Occurs ψ X Y w := by
  cases s
  · have h' := bridgeF_flip hf h
    rw [lroot_false, flipV_flipV] at h'
    exact occurs_of_bridge_self hf hc hj h'
  · rw [lroot_true, flipV_flipV] at h
    exact occurs_of_bridge_cross hj h

/-- A bridge from a lower spine position to the terminal bottom `Q_m` is an event. -/
theorem occurs_of_bot_bridge (hf : FlipClosed ψ) (hc : SignCoherent c ψ) (s : Bool) {j : ℕ}
    (hj : j ≤ w.length) (h : BridgeF ψ (lroot X Y s) w (flipV X) j w.length) : Occurs ψ X Y w := by
  cases s
  · exact occurs_of_bridge_self hf hc hj h
  · have h' := bridgeF_flip hf h
    rw [lroot_true, flipV_flipV, flipV_flipV] at h'
    exact occurs_of_bridge_cross hj h'

end Events

section Main

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

/-- A bottom filler bounds no clash from above. -/
theorem lower_root_ne_bfill {u : V (2 * (k + (2 * w.length + 2)))} {q : Bool}
    (hd : Derives (Spine.extension c ψ X Y w) u (bfill w q))
    (hu : Lit.eqTop u ∈ Spine.extension c ψ X Y w ∨
      ∃ a, Lit.fLe a u ∈ Spine.extension c ψ X Y w) : False := by
  obtain rfl := derives_into_source hd (source_bfill q)
  rcases hu with hu | ⟨a, hu⟩
  · rcases mem_eqTop hu with ⟨_, -, h⟩ | h | ⟨q', h⟩
    · exact bfill_ne_lift q _ h
    · exact bfill_ne_lv q le_rfl h
    · exact bfill_ne_flipV_bfill q q' h
  · rcases mem_fLe hu with ⟨_, _, -, -, h⟩ | ⟨_, _, hj, -, h⟩ | ⟨-, h⟩
    · exact bfill_ne_lift q _ h
    · exact bfill_ne_lv q hj.le h
    · exact bfill_ne_lv q le_rfl h

/-- A top filler bounds no clash from below. -/
theorem upper_root_ne_tfill {v : V (2 * (k + (2 * w.length + 2)))} {q : Bool}
    (hd : Derives (Spine.extension c ψ X Y w) (flipV (bfill w q)) v)
    (hv : Lit.eqBot v ∈ Spine.extension c ψ X Y w ∨
      ∃ b, Lit.leF v b ∈ Spine.extension c ψ X Y w) : False := by
  obtain rfl := derives_out_of_sink hd (sink_flipV_bfill q)
  have hl (u : V (2 * k)) (h : flipV (bfill w q) = lift u) : False :=
    bfill_ne_lift q (flipV u) (by rw [← flipV_lift, ← h, flipV_flipV])
  rcases hv with hv | ⟨b, hv⟩
  · rcases mem_eqBot hv with ⟨v, -, h⟩ | h | ⟨q', h⟩
    · exact hl v h
    · exact bfill_ne_lv q le_rfl (flipV_injective h)
    · exact bfill_ne_flipV_bfill q' q h.symm
  · rcases mem_leF hv with ⟨v, _, -, h, -⟩ | ⟨_, _, hj, -, h⟩ | ⟨-, h⟩
    · exact hl v h
    · exact bfill_ne_lv q hj.le (flipV_injective h)
    · exact bfill_ne_lv q le_rfl (flipV_injective h)

/-- Every clash of the four-spine extension is a clash of `ψ` or an event. -/
theorem events_of_clash (hf : FlipClosed ψ) (hc : SignCoherent c ψ)
    (h : LabelClash (Spine.extension c ψ X Y w)) : LabelClash ψ ∨ Occurs ψ X Y w := by
  obtain ⟨u, v, hd, hcl⟩ := (labelClash_iff_roots _).mp h
  have I := derives_inv hd
  rcases hcl with ⟨hu, hv⟩ | ⟨hu, b, hv⟩ | ⟨⟨a, hu⟩, hv⟩
  · rcases mem_eqTop hu with ⟨u', hu', rfl⟩ | rfl | ⟨q, rfl⟩
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | ⟨q, rfl⟩
      · exact Or.inl ⟨v', Or.inl ⟨⟨u', hu', I.oo u' v' rfl rfl⟩, ⟨v', hv', .refl _⟩⟩⟩
      · exact Or.inr (occurs_of_up_top hf false le_rfl (I.ou false u' _ le_rfl rfl rfl) hu')
      · exact (lower_root_ne_bfill hd (Or.inl hu)).elim
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | ⟨q, rfl⟩
      · exact Or.inr (occurs_of_low_bot hf false le_rfl (I.lo false _ v' le_rfl rfl rfl) hv')
      · exact Or.inr (occurs_of_bot_bridge hf hc false le_rfl
          (I.lu false false _ _ le_rfl le_rfl rfl rfl))
      · exact (lower_root_ne_bfill hd (Or.inl hu)).elim
    · exact (upper_root_ne_tfill hd (Or.inl hv)).elim
  · have hvb : ∃ b', Lit.leF v b' ∈ Spine.extension c ψ X Y w := ⟨b, hv⟩
    rcases mem_eqTop hu with ⟨u', hu', rfl⟩ | rfl | ⟨q, rfl⟩
    · rcases mem_leF hv with ⟨v', b', hv', rfl, rfl⟩ | ⟨s, j, hj, -, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inl ⟨v', Or.inr (Or.inl ⟨⟨u', hu', I.oo u' v' rfl rfl⟩, ⟨v', b', hv', .refl _⟩⟩)⟩
      · exact Or.inr (occurs_of_up_top hf s hj.le (I.ou s u' j hj.le rfl rfl) hu')
      · exact Or.inr (occurs_of_up_top hf true le_rfl (I.ou true u' _ le_rfl rfl rfl) hu')
    · rcases mem_leF hv with ⟨v', b', hv', rfl, rfl⟩ | ⟨s, j, hj, -, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨v', I.lo false _ v' le_rfl rfl rfl, b', hv'⟩))
      · exact Or.inr (occurs_of_top_bridge hf hc s hj.le
          (I.lu false s _ j le_rfl hj.le rfl rfl))
      · exact Or.inr (occurs_of_top_bridge hf hc true le_rfl
          (I.lu false true _ _ le_rfl le_rfl rfl rfl))
    · exact (upper_root_ne_tfill hd (Or.inr hvb)).elim
  · rcases mem_fLe hu with ⟨a', u', hu', rfl, rfl⟩ | ⟨s, j, hj, -, rfl⟩ | ⟨-, rfl⟩
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | ⟨q, rfl⟩
      · exact Or.inl ⟨v', Or.inr (Or.inr ⟨⟨a', u', hu', I.oo u' v' rfl rfl⟩, ⟨v', hv', .refl _⟩⟩)⟩
      · have hU := (lAt_flip_iff hf).mp (I.ou false u' _ le_rfl rfl rfl)
        exact Or.inr (Or.inr (Or.inl ⟨flipV u', hU, flipV ∘ a', hf _ hu'⟩))
      · exact (lower_root_ne_bfill hd (Or.inr ⟨_, hu⟩)).elim
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | ⟨q, rfl⟩
      · exact Or.inr (occurs_of_low_bot hf s hj.le (I.lo s j v' hj.le rfl rfl) hv')
      · exact Or.inr (occurs_of_bot_bridge hf hc s hj.le
          (I.lu s false j _ hj.le le_rfl rfl rfl))
      · exact (lower_root_ne_bfill hd (Or.inr ⟨_, hu⟩)).elim
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | ⟨q, rfl⟩
      · exact Or.inr (occurs_of_low_bot hf true le_rfl (I.lo true _ v' le_rfl rfl rfl) hv')
      · exact Or.inr (occurs_of_bot_bridge hf hc true le_rfl
          (I.lu true false _ _ le_rfl le_rfl rfl rfl))
      · exact (lower_root_ne_bfill hd (Or.inr ⟨_, hu⟩)).elim

/-- A clash of `ψ` is a clash of the extension. -/
theorem clash_of_clash (h : LabelClash ψ) : LabelClash (Spine.extension c ψ X Y w) := by
  obtain ⟨u, v, hd, hc⟩ := (labelClash_iff_roots ψ).mp h
  refine (labelClash_iff_roots _).mpr ⟨_, _, derives_lift hd, ?_⟩
  rcases hc with ⟨hu, hv⟩ | ⟨hu, b, hv⟩ | ⟨⟨a, hu⟩, hv⟩
  · exact Or.inl ⟨lift_mem hu, lift_mem hv⟩
  · exact Or.inr (Or.inl ⟨lift_mem hu, _, lift_mem hv⟩)
  · exact Or.inr (Or.inr ⟨⟨_, lift_mem hu⟩, lift_mem hv⟩)

/-- A clash at a position `P_j` of the spine from `X` against an upper root carrying `⊥`. -/
theorem clash_P_bot {j : ℕ} (hj : j ≤ w.length) {v : V (2 * (k + (2 * w.length + 2)))}
    (hd : Derives (Spine.extension c ψ X Y w) (lv c X Y w false j) v)
    (hv : Lit.eqBot v ∈ Spine.extension c ψ X Y w) : LabelClash (Spine.extension c ψ X Y w) := by
  refine (labelClash_iff_roots _).mpr ⟨_, _, hd, ?_⟩
  rcases Nat.lt_or_ge j w.length with hlt | hge
  · exact Or.inr (Or.inr ⟨⟨_, link_mem false hlt⟩, hv⟩)
  · obtain rfl : j = w.length := le_antisymm hj hge
    exact Or.inl ⟨top_mem, hv⟩

/-- A clash at a lower root carrying `⊤` against a position `Y_j` of the spine from `Y`. -/
theorem clash_top_Y {j : ℕ} (hj : j ≤ w.length) {u : V (2 * (k + (2 * w.length + 2)))}
    (hd : Derives (Spine.extension c ψ X Y w) u (flipV (lv c X Y w true j)))
    (hu : Lit.eqTop u ∈ Spine.extension c ψ X Y w) : LabelClash (Spine.extension c ψ X Y w) := by
  refine (labelClash_iff_roots _).mpr ⟨_, _, hd, Or.inr (Or.inl ⟨hu, ?_⟩)⟩
  rcases Nat.lt_or_ge j w.length with hlt | hge
  · exact ⟨_, flip_link_mem true hlt⟩
  · obtain rfl : j = w.length := le_antisymm hj hge
    exact ⟨_, flip_end_mem⟩

/-- Every event yields a clash of the extension. -/
theorem clash_of_occurs (hf : FlipClosed ψ) (h : Occurs ψ X Y w) :
    LabelClash (Spine.extension c ψ X Y w) := by
  have hPY {j j' : ℕ} (hj : j ≤ w.length) (hj' : j' ≤ w.length) (hB : BridgeF ψ X w Y j j') :
      Derives (Spine.extension c ψ X Y w) (lv c X Y w false j) (flipV (lv c X Y w true j')) :=
    derives_bridge hf hj hj' (by simpa using hB)
  rcases h with ⟨j, hj, ⟨v, hU, hv⟩ | ⟨u, hL, hu⟩ | ⟨v, hU, hL⟩⟩ | ⟨v, hU, b, hv⟩ |
    ⟨s, e, hse, he, hp, ⟨v, hL, hU⟩ | hself⟩
  · exact clash_P_bot hj (derives_lv_of_uAt false j hj v hU) (lift_mem hv)
  · exact clash_top_Y hj
      (derives_up_of_lAt hf true hj (by simpa using (show LAt ψ w Y j u from hL))) (lift_mem hu)
  · exact clash_top_Y le_rfl (hPY le_rfl le_rfl
      ⟨j, j, w.length - j, by omega, by omega, rfl, v, hU, hL⟩) top_mem
  · exact (labelClash_iff_roots _).mpr ⟨_, _, derives_lv_of_uAt false _ le_rfl v hU,
      Or.inr (Or.inl ⟨top_mem, _, lift_mem hv⟩)⟩
  · exact clash_top_Y (by omega) (hPY le_rfl (by omega)
      ⟨e, s, w.length - e, by omega, rfl, take_eq_of_prefix hp, v, hU, hL⟩) top_mem
  · obtain ⟨v, hU, hU'⟩ := self_iff.mp hself
    have hB : BridgeF ψ X w (flipV X) (s + (w.length - e)) w.length :=
      ⟨s, e, w.length - e, rfl, by omega, (take_eq_of_prefix hp).symm, v, hU,
        (lAt_flip_iff hf).mpr (by simpa using (show UAt ψ X w e (flipV v) from hU'))⟩
    exact clash_P_bot (by omega) (derives_bridge (s' := false) hf (by omega) le_rfl hB) bot_mem

/-- The clashes of the four-spine extension are exactly the clashes of `ψ` and the events. -/
theorem labelClash_extension_iff (hf : FlipClosed ψ) (hc : SignCoherent c ψ) :
    LabelClash (Spine.extension c ψ X Y w) ↔ LabelClash ψ ∨ Occurs ψ X Y w :=
  ⟨events_of_clash hf hc, fun h => h.elim clash_of_clash (clash_of_occurs hf)⟩

/-- Without a clash in `ψ`, the clashes of the four-spine extension are exactly the events. -/
theorem labelClash_extension_iff_occurs (hf : FlipClosed ψ) (hc : SignCoherent c ψ)
    (hn : ¬ LabelClash ψ) : LabelClash (Spine.extension c ψ X Y w) ↔ Occurs ψ X Y w := by
  rw [labelClash_extension_iff hf hc]
  exact ⟨fun h => h.resolve_left hn, Or.inr⟩

end Main

end DeciNSSE.Spine.Closure
