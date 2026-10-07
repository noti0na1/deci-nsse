import DeciNSSE.Monitor.Closure
import DeciNSSE.Satisfiability.Least

/-! # Clashes of the spine extension

Every new label clash is a readiness, terminal child, cross or self event.
Conversely, each event creates a clash, giving an exact criterion for
satisfiability of the extension.
-/

namespace DeciNSSE.Spine.Closure

variable {n K : ℕ}

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

/-- The six root and path obstructions to satisfying the three-spine extension. -/
def Events (ψ : Constraint n K) (X Xm Y : V K) (w : List (Fin n)) : Prop :=
  (∃ j ≤ w.length, ∃ v, UAt ψ X w j v ∧ Lit.eqBot v ∈ ψ) ∨
  (∃ v b, UAt ψ X w w.length v ∧ Lit.leF v b ∈ ψ) ∨
  (∃ s, ∃ k ≤ w.length, ∃ u, LAt ψ w (zroot Xm Y s) k u ∧ Lit.eqTop u ∈ ψ) ∨
  (∃ a u, LAt ψ w Xm w.length u ∧ Lit.fLe a u ∈ ψ) ∨
  (∃ s, ∃ k ≤ w.length, BridgeF ψ X w (zroot Xm Y s) w.length k) ∨
  (∃ j ≤ w.length, BridgeF ψ X w Xm j w.length)

section Main

variable {ψ : Constraint n K} {X Xm Y : V K} {w : List (Fin n)}

theorem eqBot_topV_not_mem : Lit.eqBot (topV K w.length) ∉ Spine.extension ψ X Xm Y w := by
  intro h
  rcases mem_eqBot h with ⟨_, -, h⟩ | h | h
  · exact topV_ne_castAdd _ h
  · exact topV_ne_zv le_rfl h
  · exact botV_ne_topV h.symm

theorem leF_topV_not_mem (b : Fin n → V (K + (3 * w.length + 2))) :
    Lit.leF (topV K w.length) b ∉ Spine.extension ψ X Xm Y w := by
  intro h
  rcases mem_leF h with ⟨_, _, -, h, -⟩ | ⟨_, _, hj, h, -⟩ | ⟨h, -⟩
  · exact topV_ne_castAdd _ h
  · exact topV_ne_zv hj.le h
  · exact topV_ne_zv le_rfl h

theorem eqTop_botV_not_mem : Lit.eqTop (botV K w.length) ∉ Spine.extension ψ X Xm Y w := by
  intro h
  rcases mem_eqTop h with ⟨_, -, h⟩ | h | h
  · exact botV_ne_castAdd _ h
  · exact botV_ne_pv le_rfl h
  · exact botV_ne_topV h

theorem fLe_botV_not_mem (a : Fin n → V (K + (3 * w.length + 2))) :
    Lit.fLe a (botV K w.length) ∉ Spine.extension ψ X Xm Y w := by
  intro h
  rcases mem_fLe h with ⟨_, _, -, -, h⟩ | ⟨_, hj, -, h⟩
  · exact botV_ne_castAdd _ h
  · exact botV_ne_pv hj.le h

/-- `T` bounds no clash from below: its only derived successor is itself. -/
theorem upper_root_ne_topV {u v : V (K + (3 * w.length + 2))}
    (hd : Derives (Spine.extension ψ X Xm Y w) u v) (hu : u = topV K w.length)
    (hv : Lit.eqBot v ∈ Spine.extension ψ X Xm Y w ∨
      ∃ b, Lit.leF v b ∈ Spine.extension ψ X Xm Y w) : False := by
  subst hu
  obtain rfl := derives_out_of_sink hd sink_topV
  rcases hv with hv | ⟨b, hv⟩
  · exact eqBot_topV_not_mem hv
  · exact leF_topV_not_mem b hv

/-- `B` bounds no clash from above. -/
theorem lower_root_ne_botV {u v : V (K + (3 * w.length + 2))}
    (hd : Derives (Spine.extension ψ X Xm Y w) u v) (hv : v = botV K w.length)
    (hu : Lit.eqTop u ∈ Spine.extension ψ X Xm Y w ∨
      ∃ a, Lit.fLe a u ∈ Spine.extension ψ X Xm Y w) : False := by
  subst hv
  obtain rfl := derives_into_source hd source_botV
  rcases hu with hu | ⟨a, hu⟩
  · exact eqTop_botV_not_mem hu
  · exact fLe_botV_not_mem a hu

/-- Every clash of `Ψ_w` is a clash of `ψ` or a generic event. -/
theorem events_of_clash (h : LabelClash (Spine.extension ψ X Xm Y w)) :
    LabelClash ψ ∨ Events ψ X Xm Y w := by
  obtain ⟨u, v, hd, hc⟩ := (labelClash_iff_roots _).mp h
  have I := derives_inv hd
  rcases hc with ⟨hu, hv⟩ | ⟨hu, b, hv⟩ | ⟨⟨a, hu⟩, hv⟩
  · rcases mem_eqTop hu with ⟨u', hu', rfl⟩ | rfl | rfl
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | rfl
      · exact Or.inl ⟨v', Or.inl ⟨⟨u', hu', I.oo u' v' rfl rfl⟩, ⟨v', hv', .refl _⟩⟩⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨false, w.length, le_rfl, u', I.oz false u' _ le_rfl rfl rfl, hu'⟩)))
      · exact (lower_root_ne_botV hd rfl (Or.inl hu)).elim
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | rfl
      · exact Or.inr (Or.inl ⟨w.length, le_rfl, v', I.po _ v' le_rfl rfl rfl, hv'⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨false, w.length, le_rfl, I.pz false _ _ le_rfl le_rfl rfl rfl⟩)))))
      · exact (lower_root_ne_botV hd rfl (Or.inl hu)).elim
    · exact (upper_root_ne_topV hd rfl (Or.inl hv)).elim
  · rcases mem_eqTop hu with ⟨u', hu', rfl⟩ | rfl | rfl
    · rcases mem_leF hv with ⟨v', b', hv', rfl, rfl⟩ | ⟨s, k, hk, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨v', Or.inr (Or.inl ⟨⟨u', hu', I.oo u' v' rfl rfl⟩,
          ⟨v', b', hv', .refl _⟩⟩)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, k, hk.le, u', I.oz s u' k hk.le rfl rfl, hu'⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨true, w.length, le_rfl, u', I.oz true u' _ le_rfl rfl rfl, hu'⟩)))
    · rcases mem_leF hv with ⟨v', b', hv', rfl, rfl⟩ | ⟨s, k, hk, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨v', b', I.po _ v' le_rfl rfl rfl, hv'⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨s, k, hk.le, I.pz s _ k le_rfl hk.le rfl rfl⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨true, w.length, le_rfl, I.pz true _ _ le_rfl le_rfl rfl rfl⟩)))))
    · exact (upper_root_ne_topV hd rfl (Or.inr ⟨b, hv⟩)).elim
  · rcases mem_fLe hu with ⟨a', u', hu', rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | rfl
      · exact Or.inl ⟨v', Or.inr (Or.inr ⟨⟨a', u', hu', I.oo u' v' rfl rfl⟩,
          ⟨v', hv', .refl _⟩⟩)⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨a', u', I.oz false u' _ le_rfl rfl rfl, hu'⟩))))
      · exact (lower_root_ne_botV hd rfl (Or.inr ⟨_, hu⟩)).elim
    · rcases mem_eqBot hv with ⟨v', hv', rfl⟩ | rfl | rfl
      · exact Or.inr (Or.inl ⟨j, hj.le, v', I.po j v' hj.le rfl rfl, hv'⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨j, hj.le, I.pz false j _ hj.le le_rfl rfl rfl⟩)))))
      · exact (lower_root_ne_botV hd rfl (Or.inr ⟨_, hu⟩)).elim

/-- A clash of `ψ` is a clash of `Ψ_w`. -/
theorem clash_of_clash (h : LabelClash ψ) : LabelClash (Spine.extension ψ X Xm Y w) := by
  obtain ⟨u, v, hd, hc⟩ := (labelClash_iff_roots ψ).mp h
  refine (labelClash_iff_roots _).mpr ⟨_, _, derives_lift hd, ?_⟩
  rcases hc with ⟨hu, hv⟩ | ⟨hu, b, hv⟩ | ⟨⟨a, hu⟩, hv⟩
  · exact Or.inl ⟨lift_mem hu, lift_mem hv⟩
  · exact Or.inr (Or.inl ⟨lift_mem hu, _, lift_mem hv⟩)
  · exact Or.inr (Or.inr ⟨⟨_, lift_mem hu⟩, lift_mem hv⟩)

/-- A clash at a lower root `P_j` (`j ≤ m`) against an upper root `v` carrying `⊥`. -/
theorem clash_pv_bot {j : ℕ} (hj : j ≤ w.length) {v : V (K + (3 * w.length + 2))}
    (hd : Derives (Spine.extension ψ X Xm Y w) (pv X w.length j) v)
    (hv : Lit.eqBot v ∈ Spine.extension ψ X Xm Y w) : LabelClash (Spine.extension ψ X Xm Y w) := by
  refine (labelClash_iff_roots _).mpr ⟨_, _, hd, ?_⟩
  rcases pv_lower_root (ψ := ψ) (Xm := Xm) (Y := Y) hj with ⟨-, a, ha⟩ | ⟨rfl, ht⟩
  · exact Or.inr (Or.inr ⟨⟨a, ha⟩, hv⟩)
  · exact Or.inl ⟨ht, hv⟩

/-- A clash at a lower root `u` carrying `⊤` against an upper root `Z_k` (`k ≤ m`). -/
theorem clash_top_zv (s : Bool) {k : ℕ} (hk : k ≤ w.length) {u : V (K + (3 * w.length + 2))}
    (hd : Derives (Spine.extension ψ X Xm Y w) u (zv Xm Y w.length s k))
    (hu : Lit.eqTop u ∈ Spine.extension ψ X Xm Y w) : LabelClash (Spine.extension ψ X Xm Y w) := by
  refine (labelClash_iff_roots _).mpr ⟨_, _, hd, ?_⟩
  rcases zv_upper_root (ψ := ψ) (X := X) s hk with ⟨b, hb⟩ | ⟨rfl, rfl, hb⟩
  · exact Or.inr (Or.inl ⟨hu, b, hb⟩)
  · exact Or.inl ⟨hu, hb⟩

/-- Every generic event yields a clash of `Ψ_w`. -/
theorem clash_of_events (h : Events ψ X Xm Y w) :
    LabelClash (Spine.extension ψ X Xm Y w) := by
  rcases h with ⟨j, hj, v, hU, hv⟩ | ⟨v, b, hU, hv⟩ | ⟨s, k, hk, u, hL, hu⟩ | ⟨a, u, hL, hu⟩ |
    ⟨s, k, hk, hB⟩ | ⟨j, hj, hB⟩
  · exact clash_pv_bot hj (derives_pv_of_uAt j hj v hU) (lift_mem hv)
  · exact (labelClash_iff_roots _).mpr ⟨_, _, derives_pv_of_uAt _ le_rfl v hU,
      Or.inr (Or.inl ⟨eqTop_pv_mem, _, lift_mem hv⟩)⟩
  · exact clash_top_zv s hk (derives_zv_of_lAt s k hk u hL) (lift_mem hu)
  · exact (labelClash_iff_roots _).mpr
      ⟨_, _, derives_zv_of_lAt (X := X) false _ le_rfl u hL,
        Or.inr (Or.inr ⟨⟨_, lift_mem hu⟩, eqBot_qv_mem⟩)⟩
  · exact clash_top_zv s hk (derives_pv_zv_of_bridge le_rfl hk hB) eqTop_pv_mem
  · exact clash_pv_bot hj (derives_pv_zv_of_bridge (s := false) hj le_rfl hB) eqBot_qv_mem

/-- The clashes of `Ψ_w` are exactly the clashes of `ψ` and
the generic events. -/
theorem labelClash_extension_iff :
    LabelClash (Spine.extension ψ X Xm Y w) ↔ LabelClash ψ ∨ Events ψ X Xm Y w :=
  ⟨events_of_clash, fun h => h.elim clash_of_clash clash_of_events⟩

/-- With `ψ` satisfiable: a solution of `ψ` meeting the three spine conditions
exists iff no generic event occurs. -/
theorem threeSpine_unsafe_iff (hs : ∃ A, Covariant.Sat A ψ) :
    (∃ A, Covariant.Sat A ψ ∧ covPrefTop w (A X) ∧ covPrefBot w (A Xm) ∧ ¬ covPrefTop w (A Y)) ↔
      ¬ Events ψ X Xm Y w := by
  rw [← extension_sat_iff, satisfiable_iff_not_labelClash, labelClash_extension_iff]
  have hψ : ¬ LabelClash ψ := satisfiable_iff_not_labelClash.mp hs
  exact not_congr ⟨fun h => h.resolve_left hψ, Or.inr⟩

end Main

end DeciNSSE.Spine.Closure
