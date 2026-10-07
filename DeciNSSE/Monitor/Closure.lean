import DeciNSSE.Constraints.Signs
import DeciNSSE.Monitor.Spine

/-! # Closure of the four-spine extension

Explicit path formulas describe derivations between old variables and spine
positions: from a lower position to an old variable, from an old variable to an
upper position, and from a lower to an upper position. Source and sink
separation makes the list of possible new derivations exhaustive.
-/

namespace DeciNSSE.Spine.Closure

open FiniteVariance

variable {n K : ℕ}

section Sets

variable (ψ : Constraint n K) (X : V K) (w : List (Fin n))

/-- `v ∈ U_j`: an upper path bound of `X` along `w[:j]`. -/
def UAt (j : ℕ) (v : V K) : Prop := UpperAt ψ (w.take j) X v

/-- `v ∈ L^Z_k`: a lower path bound of `Z` along `w[:k]`. -/
def LAt (Z : V K) (k : ℕ) (v : V K) : Prop := LowerAt ψ (w.take k) v Z

/-- The bridge formula (2): two cuts `a ≤ j`, `b ≤ k` with `j - a = k - b = d`,
`w[a:j] = w[b:k]` and a common element of `U_a` and `L^Z_b`. -/
def BridgeF (Z : V K) (j k : ℕ) : Prop :=
  ∃ a b d, a + d = j ∧ b + d = k ∧ (w.drop a).take d = (w.drop b).take d ∧
    ∃ v, UAt ψ X w a v ∧ LAt ψ w Z b v

end Sets

section Facts

variable {ψ : Constraint n K} {X Z : V K} {w : List (Fin n)}

@[simp] theorem uAt_zero {v : V K} : UAt ψ X w 0 v ↔ Derives ψ X v := by
  simp [UAt]

@[simp] theorem lAt_zero {v : V K} : LAt ψ w Z 0 v ↔ Derives ψ v Z := by
  simp [LAt]

theorem uAt_trans {j : ℕ} {u v : V K} (h : UAt ψ X w j u) (hd : Derives ψ u v) :
    UAt ψ X w j v := by
  have := UpperAt.comp h (UpperAt.nil hd)
  simpa [UAt] using this

theorem lAt_trans {k : ℕ} {u v : V K} (hd : Derives ψ u v) (h : LAt ψ w Z k v) :
    LAt ψ w Z k u := by
  have := LowerAt.comp (LowerAt.nil hd) h
  simpa [LAt] using this

theorem uAt_succ {j : ℕ} (hj : j < w.length) {v : V K} {b : Fin n → V K}
    (h : UAt ψ X w j v) (hb : Lit.leF v b ∈ ψ) : UAt ψ X w (j + 1) (b w[j]) := by
  unfold UAt at h ⊢
  rw [take_succ_of_lt hj]
  exact UpperAt.comp h (.cons (.refl v) hb (.nil (.refl _)))

theorem lAt_succ {k : ℕ} (hk : k < w.length) {u : V K} {a : Fin n → V K}
    (h : LAt ψ w Z k u) (ha : Lit.fLe a u ∈ ψ) : LAt ψ w Z (k + 1) (a w[k]) := by
  unfold LAt at h ⊢
  rw [take_succ_of_lt hk]
  exact LowerAt.comp (.cons ha (.refl u) (.nil (.refl _))) h

theorem bridge_base {j k : ℕ} {v : V K} (hu : UAt ψ X w j v) (hl : LAt ψ w Z k v) :
    BridgeF ψ X w Z j k :=
  ⟨j, k, 0, rfl, rfl, by simp, v, hu, hl⟩

theorem bridge_zero_left {k : ℕ} (h : BridgeF ψ X w Z 0 k) : LAt ψ w Z k X := by
  obtain ⟨a, b, d, ha, hb, -, v, hu, hl⟩ := h
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ d = 0 := by omega
  simp only [Nat.add_zero] at hb
  subst hb
  exact lAt_trans (uAt_zero.mp hu) hl

theorem bridge_zero_right {j : ℕ} (h : BridgeF ψ X w Z j 0) : UAt ψ X w j Z := by
  obtain ⟨a, b, d, ha, hb, -, v, hu, hl⟩ := h
  obtain ⟨rfl, rfl⟩ : b = 0 ∧ d = 0 := by omega
  simp only [Nat.add_zero] at ha
  subst ha
  exact uAt_trans hu (lAt_zero.mp hl)

/-- Letters at equal offsets inside the common factor agree. -/
theorem getElem_of_take_drop_eq {a b d t : ℕ} (h : (w.drop a).take d = (w.drop b).take d)
    (ht : t < d) (ha : a + t < w.length) (hb : b + t < w.length) :
    w[a + t] = w[b + t] := by
  have := congrArg (fun l => l[t]?) h
  simp only [List.getElem?_take, ht, ite_true, List.getElem?_drop] at this
  rw [List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb] at this
  exact Option.some.inj this

theorem take_drop_succ {a d : ℕ} (h : a + d < w.length) :
    (w.drop a).take (d + 1) = (w.drop a).take d ++ [w[a + d]] := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h]; rfl

/-- Extend formula (2) by one common letter. -/
theorem bridge_succ {j k : ℕ} (hj : j < w.length) (hk : k < w.length) (he : w[j] = w[k])
    (h : BridgeF ψ X w Z j k) : BridgeF ψ X w Z (j + 1) (k + 1) := by
  obtain ⟨a, b, d, ha, hb, hw, v, hu, hl⟩ := h
  subst ha; subst hb
  refine ⟨a, b, d + 1, by omega, by omega, ?_, v, hu, hl⟩
  rw [take_drop_succ hj, take_drop_succ hk, hw, he]

end Facts

section Flip

variable {k : ℕ} {ψ : Constraint n (2 * k)} {X Z : V (2 * k)} {w : List (Fin n)}

/-- `L^{σX}_j = σ U_j`. -/
theorem lAt_flip_iff (hf : FlipClosed ψ) {j : ℕ} {u : V (2 * k)} :
    LAt ψ w (flipV X) j u ↔ UAt ψ X w j (flipV u) := by
  unfold LAt UAt
  have h := lowerAt_flip_iff hf (π := w.take j) (x := u) (y := flipV X)
  rw [flipV_flipV] at h
  exact h.symm

/-- Purity: `U_j` and `L^{σX}_j` are disjoint, since their signs differ. -/
theorem not_uAt_lAt_flip {c : Fin n → Bool} (hc : SignCoherent c ψ) {j : ℕ} {v : V (2 * k)}
    (hu : UAt ψ X w j v) (hl : LAt ψ w (flipV X) j v) : False := by
  have h₁ := Signs.upperAt_sign hc hu
  have h₂ := Signs.lowerAt_sign hc hl
  rw [sign_flipV, h₁] at h₂
  revert h₂
  cases sign X <;> cases polarity c (w.take j) <;> decide

/-- Sign duality exchanges the two sides of a bridge. -/
theorem bridgeF_flip (hf : FlipClosed ψ) {j j' : ℕ} (h : BridgeF ψ X w Z j j') :
    BridgeF ψ (flipV Z) w (flipV X) j' j := by
  obtain ⟨a, b, d, ha, hb, hw, v, hu, hl⟩ := h
  refine ⟨b, a, d, hb, ha, hw.symm, flipV v, ?_, ?_⟩
  · have h := (lAt_flip_iff hf (X := flipV Z) (w := w) (j := b) (u := v)).mp
    rw [flipV_flipV] at h
    exact h hl
  · exact (lAt_flip_iff hf).mpr (by rwa [flipV_flipV])

end Flip

section Invariant

variable {k : ℕ} (c : Fin n → Bool) (ψ : Constraint n (2 * k)) (X Y : V (2 * k))
  (w : List (Fin n))

/-- The closure invariant: old-to-old pairs, lower position to old variable,
old variable to upper position, and lower to upper position. Upper positions
are the sign duals `σ (lv s j)` of lower positions, with roots `σ (lroot s)`. -/
structure Inv (a b : V (2 * (k + (2 * w.length + 2)))) : Prop where
  oo : ∀ u v, a = lift u → b = lift v → Derives ψ u v
  lo : ∀ s j v, j ≤ w.length → a = lv c X Y w s j → b = lift v → UAt ψ (lroot X Y s) w j v
  ou : ∀ s u j, j ≤ w.length → a = lift u → b = flipV (lv c X Y w s j) →
    LAt ψ w (flipV (lroot X Y s)) j u
  lu : ∀ s s' j j', j ≤ w.length → j' ≤ w.length → a = lv c X Y w s j →
    b = flipV (lv c X Y w s' j') → BridgeF ψ (lroot X Y s) w (flipV (lroot X Y s')) j j'

variable {c ψ X Y w}

theorem inv_old_old {u v : V (2 * k)} (h : Derives ψ u v) :
    Inv c ψ X Y w (lift u) (lift v) where
  oo := by
    intro u' v' hu hv
    obtain rfl := lift_injective hu
    obtain rfl := lift_injective hv
    exact h
  lo := by
    intro s j v' hj hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu.symm
    obtain rfl := lift_injective hv
    exact uAt_zero.mpr h
  ou := by
    intro s u' j hj hu hv
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj hv.symm
    obtain rfl := lift_injective hu
    exact lAt_zero.mpr h
  lu := by
    intro s s' j j' hj hj' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu.symm
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj' hv.symm
    exact bridge_base (uAt_zero.mpr (.refl _)) (lAt_zero.mpr h)

theorem inv_old_up {s : Bool} {j : ℕ} (hj : j ≤ w.length) {u : V (2 * k)}
    (h : LAt ψ w (flipV (lroot X Y s)) j u) :
    Inv c ψ X Y w (lift u) (flipV (lv c X Y w s j)) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj hv
    obtain rfl := lift_injective hu
    exact lAt_zero.mp h
  lo := by
    intro s' j' v' hj' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj' hu.symm
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj hv
    exact uAt_zero.mpr (lAt_zero.mp h)
  ou := by
    intro s' u' j' hj' hu hv
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj' (flipV_injective hv)
    obtain rfl := lift_injective hu
    rw [← hr]; exact h
  lu := by
    intro s'' s' j'' j' hj'' hj' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj'' hu.symm
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj' (flipV_injective hv)
    rw [← hr]
    exact bridge_base (uAt_zero.mpr (.refl _)) h

theorem inv_low_old {s : Bool} {j : ℕ} (hj : j ≤ w.length) {v : V (2 * k)}
    (h : UAt ψ (lroot X Y s) w j v) : Inv c ψ X Y w (lv c X Y w s j) (lift v) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu
    obtain rfl := lift_injective hv
    exact uAt_zero.mp h
  lo := by
    intro s' j' v' hj' hu hv
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj' hu
    obtain rfl := lift_injective hv
    rw [← hr]; exact h
  ou := by
    intro s' u' j' hj' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj' hv.symm
    exact lAt_zero.mpr (uAt_zero.mp h)
  lu := by
    intro s'' s' j'' j' hj'' hj' hu hv
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj'' hu
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj' hv.symm
    rw [← hr]
    exact bridge_base h (lAt_zero.mpr (.refl _))

theorem inv_low_up {s s' : Bool} {j j' : ℕ} (hj : j ≤ w.length) (hj' : j' ≤ w.length)
    (h : BridgeF ψ (lroot X Y s) w (flipV (lroot X Y s')) j j') :
    Inv c ψ X Y w (lv c X Y w s j) (flipV (lv c X Y w s' j')) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj' hv
    exact lAt_zero.mp (bridge_zero_left h)
  lo := by
    intro s'' j'' v' hj'' hu hv
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj'' hu
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj' hv
    rw [← hr]
    exact bridge_zero_right h
  ou := by
    intro s'' u' j'' hj'' hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj hu
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj' hj'' (flipV_injective hv)
    rw [← hr]
    exact bridge_zero_left h
  lu := by
    intro s₁ s₂ j₁ j₂ hj₁ hj₂ hu hv
    obtain ⟨rfl, hr⟩ := lv_eq_lv hj hj₁ hu
    obtain ⟨rfl, hr'⟩ := lv_eq_lv hj' hj₂ (flipV_injective hv)
    rw [← hr, ← hr']; exact h

theorem inv_bfill (q : Bool) (b : V (2 * (k + (2 * w.length + 2)))) :
    Inv c ψ X Y w (bfill w q) b where
  oo := fun _ _ hu _ => absurd hu (bfill_ne_lift q _)
  lo := fun _ _ _ hj hu _ => absurd hu (bfill_ne_lv q hj)
  ou := fun _ _ _ _ hu _ => absurd hu (bfill_ne_lift q _)
  lu := fun _ _ _ _ hj _ hu _ => absurd hu (bfill_ne_lv q hj)

theorem inv_tfill (q : Bool) (a : V (2 * (k + (2 * w.length + 2)))) :
    Inv c ψ X Y w a (flipV (bfill w q)) where
  oo := fun _ v _ hv =>
    (bfill_ne_lift q (flipV v) (by rw [← flipV_lift, ← hv, flipV_flipV])).elim
  lo := fun _ _ v _ _ hv =>
    (bfill_ne_lift q (flipV v) (by rw [← flipV_lift, ← hv, flipV_flipV])).elim
  ou := fun _ _ _ hj _ hv => (bfill_ne_lv q hj (flipV_injective hv)).elim
  lu := fun _ _ _ _ _ hj' _ hv => (bfill_ne_lv q hj' (flipV_injective hv)).elim

theorem inv_refl (a : V (2 * (k + (2 * w.length + 2)))) : Inv c ψ X Y w a a where
  oo := by
    intro u v hu hv
    obtain rfl := lift_injective (hu.symm.trans hv)
    exact .refl _
  lo := by
    intro s j v hj hu hv
    obtain ⟨rfl, rfl⟩ := lv_eq_lift hj (hu.symm.trans hv)
    exact uAt_zero.mpr (.refl _)
  ou := by
    intro s u j hj hu hv
    obtain ⟨rfl, rfl⟩ := flipV_lv_eq_lift hj (hv.symm.trans hu)
    exact lAt_zero.mpr (.refl _)
  lu := by
    intro s s' j j' hj hj' hu hv
    obtain ⟨rfl, rfl, hr⟩ := lv_eq_flipV_lv hj hj' (hu.symm.trans hv)
    exact bridge_base (uAt_zero.mpr (.refl _)) (lAt_zero.mpr (by rw [← hr]; exact .refl _))

/-- Transitivity through an old variable. -/
theorem inv_trans_old {a b : V (2 * (k + (2 * w.length + 2)))} {u : V (2 * k)}
    (h₁ : Inv c ψ X Y w a (lift u)) (h₂ : Inv c ψ X Y w (lift u) b) : Inv c ψ X Y w a b where
  oo := fun u' v hu hv => (h₁.oo u' u hu rfl).trans (h₂.oo u v rfl hv)
  lo := fun s j v hj hu hv => uAt_trans (h₁.lo s j u hj hu rfl) (h₂.oo u v rfl hv)
  ou := fun s u' j hj hu hv => lAt_trans (h₁.oo u' u hu rfl) (h₂.ou s u j hj rfl hv)
  lu := fun s s' j j' hj hj' hu hv => bridge_base (h₁.lo s j u hj hu rfl) (h₂.ou s' u j' hj' rfl hv)

/-- Every derived pair satisfies the four clauses of the closure invariant. -/
theorem derives_inv {a b : V (2 * (k + (2 * w.length + 2)))}
    (h : Derives (Spine.extension c ψ X Y w) a b) : Inv c ψ X Y w a b := by
  induction h with
  | refl a => exact inv_refl a
  | @trans a m b h₁ h₂ ih₁ ih₂ =>
    rcases variable_cases m with ⟨m', rfl⟩ | hm | hm
    · exact inv_trans_old ih₁ ih₂
    · obtain rfl := derives_into_source h₁ hm; exact ih₂
    · obtain rfl := derives_out_of_sink h₂ hm; exact ih₁
  | @decomp A B u v i hl _ hu ih =>
    rcases mem_fLe hl with ⟨A', u', hl', rfl, rfl⟩ | ⟨s, j, hj, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases mem_leF hu with ⟨v', B', hu', rfl, rfl⟩ | ⟨s', j', hj', rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Function.comp_apply, endKids] at ih ⊢
    · exact inv_old_old (.decomp i hl' (ih.oo u' v' rfl rfl) hu')
    · by_cases hi : i = w[j']
      · subst hi
        rw [kids_self]
        exact inv_old_up (by omega) (lAt_succ hj' (ih.ou s' u' j' hj'.le rfl rfl) hl')
      · rw [kids_of_ne hi]; exact inv_tfill _ _
    · exact inv_tfill _ _
    · by_cases hi : i = w[j]
      · subst hi
        rw [kids_self]
        exact inv_low_old (by omega) (uAt_succ hj (ih.lo s j v' hj.le rfl rfl) hu')
      · rw [kids_of_ne hi]; exact inv_bfill _ _
    · by_cases hi : i = w[j]
      · by_cases hi' : i = w[j']
        · have he : w[j] = w[j'] := hi.symm.trans hi'
          have e₁ : kids c X Y w s j w[j] i = lv c X Y w s (j + 1) := by rw [hi, kids_self]
          have e₂ : kids c X Y w s' j' w[j'] i = lv c X Y w s' (j' + 1) := by rw [hi', kids_self]
          rw [e₁, e₂]
          exact inv_low_up (by omega) (by omega)
            (bridge_succ hj hj' he (ih.lu s s' j j' hj.le hj'.le rfl rfl))
        · rw [kids_of_ne hi']; exact inv_tfill _ _
      · rw [kids_of_ne hi]; exact inv_bfill _ _
    · exact inv_tfill _ _
    · exact inv_bfill _ _
    · exact inv_bfill _ _
    · exact inv_bfill _ _

end Invariant

section Backward

variable {k : ℕ} {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)}
  {w : List (Fin n)}

theorem derives_lv_of_uAt (s : Bool) : ∀ j, j ≤ w.length → ∀ v, UAt ψ (lroot X Y s) w j v →
    Derives (Spine.extension c ψ X Y w) (lv c X Y w s j) (lift v)
  | 0, _, v, h => by rw [lv_zero]; exact derives_lift (uAt_zero.mp h)
  | j + 1, hj, v, h => by
    unfold UAt at h
    rw [take_succ_of_lt (by omega)] at h
    obtain ⟨z, hz, hp⟩ := UpperAt.factor h
    cases hp with
    | @cons _ z' b _ _ _ hd hl hp =>
      have ih := derives_lv_of_uAt s j (by omega) z hz
      have hstep := Derives.decomp (w[j]'(by omega)) (link_mem (ψ := ψ) s (by omega))
        (ih.trans (derives_lift hd)) (lift_mem hl)
      rw [kids_self] at hstep
      exact hstep.trans (derives_lift (upperAt_nil_iff.mp hp))

theorem derives_up_of_lAt (hf : FlipClosed ψ) (s : Bool) {j : ℕ} (hj : j ≤ w.length)
    {u : V (2 * k)} (h : LAt ψ w (flipV (lroot X Y s)) j u) :
    Derives (Spine.extension c ψ X Y w) (lift u) (flipV (lv c X Y w s j)) := by
  have hd := derives_flip (extension_flipClosed hf)
    (derives_lv_of_uAt (c := c) s j hj _ ((lAt_flip_iff hf).mp h))
  rwa [flipV_lift, flipV_flipV] at hd

/-- Descend a lower and an upper spine along a common factor. -/
theorem derives_descend {s s' : Bool} {a b : ℕ} :
    ∀ d, a + d ≤ w.length → b + d ≤ w.length → (w.drop a).take d = (w.drop b).take d →
      Derives (Spine.extension c ψ X Y w) (lv c X Y w s a) (flipV (lv c X Y w s' b)) →
      Derives (Spine.extension c ψ X Y w) (lv c X Y w s (a + d)) (flipV (lv c X Y w s' (b + d)))
  | 0, _, _, _, h => h
  | d + 1, ha, hb, hw, h => by
    have hw' : (w.drop a).take d = (w.drop b).take d := by
      have := congrArg (List.take d) hw
      simpa [List.take_take] using this
    have ih := derives_descend d (by omega) (by omega) hw' h
    have he : w[a + d]'(by omega) = w[b + d]'(by omega) :=
      getElem_of_take_drop_eq hw (by omega) (by omega) (by omega)
    have hstep := Derives.decomp (w[a + d]'(by omega)) (link_mem (ψ := ψ) s (by omega)) ih
      (flip_link_mem (ψ := ψ) s' (by omega : b + d < w.length))
    rw [kids_self, Function.comp_apply, he, kids_self] at hstep
    exact hstep

theorem derives_bridge (hf : FlipClosed ψ) {s s' : Bool} {j j' : ℕ} (hj : j ≤ w.length)
    (hj' : j' ≤ w.length) (h : BridgeF ψ (lroot X Y s) w (flipV (lroot X Y s')) j j') :
    Derives (Spine.extension c ψ X Y w) (lv c X Y w s j) (flipV (lv c X Y w s' j')) := by
  obtain ⟨a, b, d, rfl, rfl, hw, v, hu, hl⟩ := h
  exact derives_descend d hj hj' hw
    ((derives_lv_of_uAt s a (by omega) v hu).trans (derives_up_of_lAt hf s' (by omega) hl))

end Backward

end DeciNSSE.Spine.Closure
