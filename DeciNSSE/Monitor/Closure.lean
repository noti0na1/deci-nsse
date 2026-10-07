import DeciNSSE.Monitor.Spine

/-! # Closure of the spine extension

Explicit path formulas describe derivations between old variables and spine
positions. Source and sink separation makes the list of possible new
derivations exhaustive.
-/

namespace DeciNSSE.Spine.Closure

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

theorem take_succ_of_lt {j : ℕ} (hj : j < w.length) : w.take (j + 1) = w.take j ++ [w[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl

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

section Invariant

variable (ψ : Constraint n K) (X Xm Y : V K) (w : List (Fin n))

/-- The closure invariant for old-to-old, spine-to-old, old-to-spine and spine-to-spine pairs. -/
structure Inv (a b : V (K + (3 * w.length + 2))) : Prop where
  oo : ∀ u v : V K, a = Fin.castAdd _ u → b = Fin.castAdd _ v → Derives ψ u v
  po : ∀ j (v : V K), j ≤ w.length → a = pv X w.length j → b = Fin.castAdd _ v →
    UAt ψ X w j v
  oz : ∀ s (u : V K) k, k ≤ w.length → a = Fin.castAdd _ u → b = zv Xm Y w.length s k →
    LAt ψ w (zroot Xm Y s) k u
  pz : ∀ s j k, j ≤ w.length → k ≤ w.length → a = pv X w.length j →
    b = zv Xm Y w.length s k → BridgeF ψ X w (zroot Xm Y s) j k

variable {ψ X Xm Y w}

theorem inv_old_old {u v : V K} (h : Derives ψ u v) :
    Inv ψ X Xm Y w (Fin.castAdd _ u) (Fin.castAdd _ v) where
  oo := by
    intro u' v' hu hv
    obtain rfl := Fin.castAdd_inj.mp hu
    obtain rfl := Fin.castAdd_inj.mp hv
    exact h
  po := by
    intro j v' hj hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu.symm
    obtain rfl := Fin.castAdd_inj.mp hv
    exact uAt_zero.mpr h
  oz := by
    intro s u' k hk hu hv
    obtain ⟨rfl, hz⟩ := zv_eq_castAdd hk hv.symm
    obtain rfl := Fin.castAdd_inj.mp hu
    rw [← hz]
    exact lAt_zero.mpr h
  pz := by
    intro s j k hj hk hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu.symm
    obtain ⟨rfl, hz⟩ := zv_eq_castAdd hk hv.symm
    rw [← hz]
    exact bridge_base (uAt_zero.mpr (.refl _)) (lAt_zero.mpr h)

theorem inv_old_zv {s : Bool} {k : ℕ} (hk : k ≤ w.length) {u : V K}
    (h : LAt ψ w (zroot Xm Y s) k u) :
    Inv ψ X Xm Y w (Fin.castAdd _ u) (zv Xm Y w.length s k) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := zv_eq_castAdd hk hv
    obtain rfl := Fin.castAdd_inj.mp hu
    exact lAt_zero.mp h
  po := by
    intro j v' hj hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu.symm
    obtain ⟨rfl, rfl⟩ := zv_eq_castAdd hk hv
    exact uAt_zero.mpr (lAt_zero.mp h)
  oz := by
    intro s' u' k' hk' hu hv
    obtain ⟨rfl, hz⟩ := zv_eq_zv hk hk' hv
    obtain rfl := Fin.castAdd_inj.mp hu
    rw [← hz]; exact h
  pz := by
    intro s' j k' hj hk' hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu.symm
    obtain ⟨rfl, hz⟩ := zv_eq_zv hk hk' hv
    rw [← hz]
    exact bridge_base (uAt_zero.mpr (.refl _)) h

theorem inv_pv_old {j : ℕ} (hj : j ≤ w.length) {v : V K} (h : UAt ψ X w j v) :
    Inv ψ X Xm Y w (pv X w.length j) (Fin.castAdd _ v) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu
    obtain rfl := Fin.castAdd_inj.mp hv
    exact uAt_zero.mp h
  po := by
    intro j' v' hj' hu hv
    obtain rfl := pv_inj hj hj' hu
    obtain rfl := Fin.castAdd_inj.mp hv
    exact h
  oz := by
    intro s u' k hk hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu
    obtain ⟨rfl, hz⟩ := zv_eq_castAdd hk hv.symm
    rw [hz] at h
    exact lAt_zero.mpr (uAt_zero.mp h)
  pz := by
    intro s j' k hj' hk hu hv
    obtain rfl := pv_inj hj hj' hu
    obtain ⟨rfl, hz⟩ := zv_eq_castAdd hk hv.symm
    rw [hz] at h
    exact bridge_base h (lAt_zero.mpr (.refl _))

theorem inv_pv_zv {s : Bool} {j k : ℕ} (hj : j ≤ w.length) (hk : k ≤ w.length)
    (h : BridgeF ψ X w (zroot Xm Y s) j k) :
    Inv ψ X Xm Y w (pv X w.length j) (zv Xm Y w.length s k) where
  oo := by
    intro u' v' hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu
    obtain ⟨rfl, rfl⟩ := zv_eq_castAdd hk hv
    exact lAt_zero.mp (bridge_zero_left h)
  po := by
    intro j' v' hj' hu hv
    obtain rfl := pv_inj hj hj' hu
    obtain ⟨rfl, rfl⟩ := zv_eq_castAdd hk hv
    exact bridge_zero_right h
  oz := by
    intro s' u' k' hk' hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj hu
    obtain ⟨rfl, hz⟩ := zv_eq_zv hk hk' hv
    rw [← hz]
    exact bridge_zero_left h
  pz := by
    intro s' j' k' hj' hk' hu hv
    obtain rfl := pv_inj hj hj' hu
    obtain ⟨rfl, hz⟩ := zv_eq_zv hk hk' hv
    rw [← hz]; exact h

theorem inv_botV (b : V (K + (3 * w.length + 2))) : Inv ψ X Xm Y w (botV K w.length) b where
  oo := fun _ _ hu _ => absurd hu (botV_ne_castAdd _)
  po := fun _ _ hj hu _ => absurd hu (botV_ne_pv hj)
  oz := fun _ _ _ _ hu _ => absurd hu (botV_ne_castAdd _)
  pz := fun _ _ _ hj _ hu _ => absurd hu (botV_ne_pv hj)

theorem inv_topV (a : V (K + (3 * w.length + 2))) : Inv ψ X Xm Y w a (topV K w.length) where
  oo := fun _ _ _ hv => absurd hv (topV_ne_castAdd _)
  po := fun _ _ _ _ hv => absurd hv (topV_ne_castAdd _)
  oz := fun _ _ _ hk _ hv => absurd hv (topV_ne_zv hk)
  pz := fun _ _ _ _ hk _ hv => absurd hv (topV_ne_zv hk)

theorem inv_refl (a : V (K + (3 * w.length + 2))) : Inv ψ X Xm Y w a a where
  oo := by
    intro u v hu hv
    obtain rfl := Fin.castAdd_inj.mp (hu.symm.trans hv)
    exact .refl _
  po := by
    intro j v hj hu hv
    obtain ⟨rfl, rfl⟩ := pv_eq_castAdd hj (hu.symm.trans hv)
    exact uAt_zero.mpr (.refl _)
  oz := by
    intro s u k hk hu hv
    obtain ⟨rfl, rfl⟩ := zv_eq_castAdd hk (hv.symm.trans hu)
    exact lAt_zero.mpr (.refl _)
  pz := by
    intro s j k hj hk hu hv
    obtain ⟨rfl, rfl, hz⟩ := pv_eq_zv hj hk (hu.symm.trans hv)
    rw [← hz]
    exact bridge_base (uAt_zero.mpr (.refl _)) (lAt_zero.mpr (.refl _))

/-- Transitivity through an old variable. -/
theorem inv_trans_old {a b : V (K + (3 * w.length + 2))} {c : V K}
    (h₁ : Inv ψ X Xm Y w a (Fin.castAdd _ c)) (h₂ : Inv ψ X Xm Y w (Fin.castAdd _ c) b) :
    Inv ψ X Xm Y w a b where
  oo := fun u v hu hv => (h₁.oo u c hu rfl).trans (h₂.oo c v rfl hv)
  po := fun j v hj hu hv => uAt_trans (h₁.po j c hj hu rfl) (h₂.oo c v rfl hv)
  oz := fun s u k hk hu hv => lAt_trans (h₁.oo u c hu rfl) (h₂.oz s c k hk rfl hv)
  pz := fun s j k hj hk hu hv => bridge_base (h₁.po j c hj hu rfl) (h₂.oz s c k hk rfl hv)

/-- Every derived pair satisfies the four endpoint clauses of the closure invariant. -/
theorem derives_inv {a b : V (K + (3 * w.length + 2))}
    (h : Derives (Spine.extension ψ X Xm Y w) a b) : Inv ψ X Xm Y w a b := by
  induction h with
  | refl a => exact inv_refl a
  | @trans a c b h₁ h₂ ih₁ ih₂ =>
    rcases (extension_ranked ψ X Xm Y w).variable_cases c with ⟨c', rfl⟩ | hc | hc
    · exact inv_trans_old ih₁ ih₂
    · obtain rfl := derives_into_source h₁ hc; exact ih₂
    · obtain rfl := derives_out_of_sink h₂ hc; exact ih₁
  | @decomp A Bv u v i hl _ hu ih =>
    rcases mem_fLe hl with ⟨A', u', hl', rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩ <;>
      rcases mem_leF hu with ⟨v', B', hu', rfl, rfl⟩ | ⟨s, k, hk, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact inv_old_old (.decomp i hl' (ih.oo u' v' rfl rfl) hu')
    · by_cases hi : i = w[k]
      · subst hi
        simp only [Function.comp_apply, spineChildren_self]
        exact inv_old_zv (by omega) (lAt_succ hk (ih.oz s u' k hk.le rfl rfl) hl')
      · rw [spineChildren_of_ne hi]; exact inv_topV _
    · exact inv_topV _
    · by_cases hi : i = w[j]
      · subst hi
        simp only [Function.comp_apply, spineChildren_self]
        exact inv_pv_old (by omega) (uAt_succ hj (ih.po j v' hj.le rfl rfl) hu')
      · rw [spineChildren_of_ne hi]; exact inv_botV _
    · by_cases hi : i = w[j]
      · by_cases hi' : i = w[k]
        · have he : w[j] = w[k] := hi.symm.trans hi'
          have e1 : spineChildren w[j] (pv X w.length (j + 1)) (botV K w.length) i =
              pv X w.length (j + 1) := by rw [hi, spineChildren_self]
          have e2 : spineChildren w[k] (zv Xm Y w.length s (k + 1)) (topV K w.length) i =
              zv Xm Y w.length s (k + 1) := by rw [hi', spineChildren_self]
          rw [e1, e2]
          exact inv_pv_zv (by omega) (by omega)
            (bridge_succ hj hk he (ih.pz s j k hj.le hk.le rfl rfl))
        · rw [spineChildren_of_ne hi']; exact inv_topV _
      · rw [spineChildren_of_ne hi]; exact inv_botV _
    · exact inv_topV _

end Invariant

section Backward

variable {ψ : Constraint n K} {X Xm Y : V K} {w : List (Fin n)}

theorem derives_pv_of_uAt : ∀ j, j ≤ w.length → ∀ v : V K, UAt ψ X w j v →
    Derives (Spine.extension ψ X Xm Y w) (pv X w.length j) (Fin.castAdd _ v)
  | 0, _, v, h => by rw [pv_zero]; exact derives_lift (uAt_zero.mp h)
  | j + 1, hj, v, h => by
    unfold UAt at h
    rw [take_succ_of_lt (by omega)] at h
    obtain ⟨z, hz, hp⟩ := UpperAt.factor h
    cases hp with
    | @cons _ z' b _ _ _ hd hl hp =>
      have ih := derives_pv_of_uAt j (by omega) z hz
      have hstep := Derives.decomp (w[j]'(by omega)) (pLink_mem (ψ := ψ) (Xm := Xm) (Y := Y)
        (by omega : j < w.length)) (ih.trans (derives_lift hd)) (lift_mem hl)
      simp only [spineChildren_self, Function.comp_apply] at hstep
      exact hstep.trans (derives_lift (upperAt_nil_iff.mp hp))

theorem derives_zv_of_lAt (s : Bool) : ∀ k, k ≤ w.length → ∀ v : V K,
    LAt ψ w (zroot Xm Y s) k v →
    Derives (Spine.extension ψ X Xm Y w) (Fin.castAdd _ v) (zv Xm Y w.length s k)
  | 0, _, v, h => by rw [zv_zero]; exact derives_lift (lAt_zero.mp h)
  | k + 1, hk, v, h => by
    unfold LAt at h
    rw [take_succ_of_lt (by omega)] at h
    obtain ⟨z, hz, hp⟩ := LowerAt.factor h
    cases hp with
    | @cons a z' _ _ _ _ hl hd hp =>
      have ih := derives_zv_of_lAt s k (by omega) z hz
      have hstep := Derives.decomp (w[k]'(by omega)) (lift_mem hl)
        ((derives_lift hd).trans ih) (zLink_mem (ψ := ψ) (X := X) s (by omega : k < w.length))
      simp only [spineChildren_self, Function.comp_apply] at hstep
      exact (derives_lift (lowerAt_nil_iff.mp hp)).trans hstep

/-- Descend both spines along a common factor. -/
theorem derives_descend {s : Bool} {a b : ℕ} :
    ∀ d, a + d ≤ w.length → b + d ≤ w.length →
      (w.drop a).take d = (w.drop b).take d →
      Derives (Spine.extension ψ X Xm Y w) (pv X w.length a) (zv Xm Y w.length s b) →
      Derives (Spine.extension ψ X Xm Y w) (pv X w.length (a + d)) (zv Xm Y w.length s (b + d))
  | 0, _, _, _, h => h
  | d + 1, ha, hb, hw, h => by
    have hw' : (w.drop a).take d = (w.drop b).take d := by
      have := congrArg (List.take d) hw
      simpa [List.take_take] using this
    have ih := derives_descend d (by omega) (by omega) hw' h
    have he : w[a + d]'(by omega) = w[b + d]'(by omega) :=
      getElem_of_take_drop_eq hw (by omega) (by omega) (by omega)
    have hstep := Derives.decomp (w[a + d]'(by omega))
      (pLink_mem (ψ := ψ) (Xm := Xm) (Y := Y) (by omega : a + d < w.length)) ih
      (zLink_mem (ψ := ψ) (X := X) s (by omega : b + d < w.length))
    rw [spineChildren_self, he, spineChildren_self] at hstep
    exact hstep

theorem derives_pv_zv_of_bridge {s : Bool} {j k : ℕ} (hj : j ≤ w.length) (hk : k ≤ w.length)
    (h : BridgeF ψ X w (zroot Xm Y s) j k) :
    Derives (Spine.extension ψ X Xm Y w) (pv X w.length j) (zv Xm Y w.length s k) := by
  obtain ⟨a, b, d, rfl, rfl, hw, v, hu, hl⟩ := h
  exact derives_descend d hj hk hw
    ((derives_pv_of_uAt a (by omega) v hu).trans (derives_zv_of_lAt s b (by omega) v hl))

end Backward

end DeciNSSE.Spine.Closure
