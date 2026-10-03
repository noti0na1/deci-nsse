import DeciNSSE.Transfer.Regular

/-! # Transfer to finite trees

The variable chains for path witnesses preserve cycle clashes. If the original
constraints have a finite solution, failed unrestricted entailment therefore
has a finite counterexample. Finite entailment is equivalent to unrestricted
entailment or finite unsatisfiability.
-/

namespace DeciNSSE

variable {k m : ℕ}

theorem Derives.map {ϕ : Constraint k} {ψ : Constraint m} (r : V k → V m)
    (hr : ∀ l ∈ ϕ, l.rename r ∈ ψ) {a b : V k} (h : Derives ϕ a b) :
    Derives ψ (r a) (r b) := by
  induction h with
  | refl a => exact .refl _
  | trans _ _ ih ih' => exact .trans ih ih'
  | decomp_left hl _ hu ih => exact .decomp_left (hr _ hl) ih (hr _ hu)
  | decomp_right hl _ hu ih => exact .decomp_right (hr _ hl) ih (hr _ hu)

theorem LowerAt.map {ϕ : Constraint k} {ψ : Constraint m} (r : V k → V m)
    (hr : ∀ l ∈ ϕ, l.rename r ∈ ψ) {π : List (Fin 2)} {a b : V k}
    (h : LowerAt ϕ π a b) : LowerAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | cons hl hd _ ih =>
    exact .cons (hr _ hl) (hd.map r hr) (by simpa only [apply_ite] using ih)

theorem UpperAt.map {ϕ : Constraint k} {ψ : Constraint m} (r : V k → V m)
    (hr : ∀ l ∈ ϕ, l.rename r ∈ ψ) {π : List (Fin 2)} {a b : V k}
    (h : UpperAt ϕ π a b) : UpperAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | cons hd hl _ ih =>
    exact .cons (hd.map r hr) (hr _ hl) (by simpa only [apply_ite] using ih)

namespace TransferFin

open Safety

variable {n : ℕ}

/-- Fresh lower-chain and bottom variables in the extended variable set. -/
def Source (z : V (k + (2 * n + 2))) : Prop :=
  k ≤ z.val ∧ (z.val < k + n ∨ z.val = k + 2 * n)

/-- Fresh upper-chain and top variables in the extended variable set. -/
def Sink (z : V (k + (2 * n + 2))) : Prop :=
  (k + n ≤ z.val ∧ z.val < k + 2 * n) ∨ z.val = k + 2 * n + 1

theorem source_not_old {z : V (k + (2 * n + 2))} (h : Source z) : ¬ z.val < k := by
  unfold Source at h; omega

theorem sink_not_old {z : V (k + (2 * n + 2))} (h : Sink z) : ¬ z.val < k := by
  unfold Sink at h; omega

theorem source_not_sink {z : V (k + (2 * n + 2))} (h : Source z) : ¬ Sink z := by
  unfold Source at h; unfold Sink; omega

theorem variable_cases (z : V (k + (2 * n + 2))) :
    (∃ u : V k, z = Fin.castAdd _ u) ∨ Source z ∨ Sink z := by
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val, h⟩, rfl⟩
  · right; unfold Source Sink; have := z.isLt; omega

/--
A constraint extension by increasing source and sink chains, preserving the original literals.
-/
structure Extension (ϕ : Constraint k) (ψ : Constraint (k + (2 * n + 2))) : Prop where
  old_mem : ∀ l ∈ ϕ, l.rename (Fin.castAdd _) ∈ ψ
  lower : ∀ a b c, Lit.fLe a b c ∈ ψ →
    (∃ a' b' c' : V k, Lit.fLe a' b' c' ∈ ϕ ∧
      a = Fin.castAdd _ a' ∧ b = Fin.castAdd _ b' ∧ c = Fin.castAdd _ c') ∨
    (Source a ∧ Source b ∧ ¬ Sink c ∧ c.val < a.val ∧ c.val < b.val)
  upper : ∀ c a b, Lit.leF c a b ∈ ψ →
    (∃ c' a' b' : V k, Lit.leF c' a' b' ∈ ϕ ∧
      c = Fin.castAdd _ c' ∧ a = Fin.castAdd _ a' ∧ b = Fin.castAdd _ b') ∨
    (Sink a ∧ Sink b ∧ ¬ Source c ∧ c.val < a.val ∧ c.val < b.val)

variable {ϕ : Constraint k} {ψ : Constraint (k + (2 * n + 2))}

theorem Extension.upper_children (e : Extension ϕ ψ) {c a b : V (k + (2 * n + 2))}
    (h : Lit.leF c a b ∈ ψ) : ¬ Source a ∧ ¬ Source b := by
  rcases e.upper _ _ _ h with ⟨c', a', b', _, rfl, rfl, rfl⟩ | ⟨ha, hb, _⟩
  · exact ⟨fun h => source_not_old h a'.isLt, fun h => source_not_old h b'.isLt⟩
  · exact ⟨fun h => source_not_sink h ha, fun h => source_not_sink h hb⟩

theorem Extension.lower_children (e : Extension ϕ ψ) {a b c : V (k + (2 * n + 2))}
    (h : Lit.fLe a b c ∈ ψ) : ¬ Sink a ∧ ¬ Sink b := by
  rcases e.lower _ _ _ h with ⟨a', b', c', _, rfl, rfl, rfl⟩ | ⟨ha, hb, _⟩
  · exact ⟨fun h => sink_not_old h a'.isLt, fun h => sink_not_old h b'.isLt⟩
  · exact ⟨source_not_sink ha, source_not_sink hb⟩

theorem Extension.derives_into_source (e : Extension ϕ ψ)
    {a b : V (k + (2 * n + 2))} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp_left _ _ hu => exact False.elim ((e.upper_children hu).1 hb)
  | decomp_right _ _ hu => exact False.elim ((e.upper_children hu).2 hb)

theorem Extension.derives_out_of_sink (e : Extension ϕ ψ)
    {a b : V (k + (2 * n + 2))} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp_left hl _ _ => exact False.elim ((e.lower_children hl).1 ha)
  | decomp_right hl _ _ => exact False.elim ((e.lower_children hl).2 ha)

theorem Extension.middle_original (e : Extension ϕ ψ)
    {u v : V k} {w : V (k + (2 * n + 2))}
    (hl : Derives ψ (Fin.castAdd _ u) w)
    (hr : Derives ψ w (Fin.castAdd _ v)) : ∃ t : V k, w = Fin.castAdd _ t := by
  rcases variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (source_not_old (he ▸ hs) u.isLt)
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (sink_not_old (he ▸ ht) v.isLt)

theorem Extension.derives_reflect (e : Extension ϕ ψ)
    {a b : V (k + (2 * n + 2))} (h : Derives ψ a b) :
    ∀ u v : V k, a = Fin.castAdd _ u → b = Fin.castAdd _ v → Derives ϕ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    have he : u = v := Fin.castAdd_injective _ _ (hu.symm.trans hv)
    subst v; exact .refl _
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | decomp_left hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ _ hl with ⟨a', b', c', hl', ha', _, hc⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ _ hu with ⟨d', e', f', hu', hd, he, _⟩ | ⟨ht, _⟩
      · have h₁ : a' = u := Fin.castAdd_injective _ _ (ha'.symm.trans ha)
        have h₂ : e' = v := Fin.castAdd_injective _ _ (he.symm.trans hb)
        subst a'; subst e'
        exact .decomp_left hl' (ih _ _ hc hd) hu'
      · exact False.elim (sink_not_old ht (by rw [hb]; exact v.isLt))
    · exact False.elim (source_not_old hs (by rw [ha]; exact u.isLt))
  | decomp_right hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ _ hl with ⟨a', b', c', hl', _, hb', hc⟩ | ⟨_, hs, _⟩
    · rcases e.upper _ _ _ hu with ⟨d', e', f', hu', hd, _, hf⟩ | ⟨_, ht, _⟩
      · have h₁ : b' = u := Fin.castAdd_injective _ _ (hb'.symm.trans ha)
        have h₂ : f' = v := Fin.castAdd_injective _ _ (hf.symm.trans hb)
        subst b'; subst f'
        exact .decomp_right hl' (ih _ _ hc hd) hu'
      · exact False.elim (sink_not_old ht (by rw [hb]; exact v.isLt))
    · exact False.elim (source_not_old hs (by rw [ha]; exact u.isLt))

theorem Extension.derives_original (e : Extension ϕ ψ) (u v : V k) :
    Derives ψ (Fin.castAdd _ u) (Fin.castAdd _ v) ↔ Derives ϕ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

theorem Extension.lowerAt_source (e : Extension ϕ ψ)
    {π : List (Fin 2)} {a b : V (k + (2 * n + 2))} (h : LowerAt ψ π a b)
    (hb : Source b) : Source a ∧ b.val ≤ a.val ∧ (π ≠ [] → b.val < a.val) := by
  induction h with
  | nil hd =>
    have he := e.derives_into_source hd hb
    subst he
    exact ⟨hb, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons z₁ z₂ z b a π i hl hd hp ih =>
    have he := e.derives_into_source hd hb
    subst z
    rcases e.lower _ _ _ hl with ⟨a', b', c', _, _, _, hc⟩ |
      ⟨h₁, h₂, _, hlt₁, hlt₂⟩
    · exact False.elim (source_not_old hb (by rw [hc]; exact c'.isLt))
    · have hs : Source (if i = 0 then z₁ else z₂) := by split <;> assumption
      have hlt : b.val < (if i = 0 then z₁ else z₂).val := by
        split <;> assumption
      obtain ⟨ha, hle, _⟩ := ih hs
      exact ⟨ha, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

theorem Extension.upperAt_sink (e : Extension ϕ ψ)
    {π : List (Fin 2)} {a b : V (k + (2 * n + 2))} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ a.val ≤ b.val ∧ (π ≠ [] → a.val < b.val) := by
  induction h with
  | nil hd =>
    have he := e.derives_out_of_sink hd ha
    subst he
    exact ⟨ha, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons a z z₁ z₂ b π i hd hl hp ih =>
    have he := e.derives_out_of_sink hd ha
    subst z
    rcases e.upper _ _ _ hl with ⟨c', a', b', _, hc, _, _⟩ |
      ⟨h₁, h₂, _, hlt₁, hlt₂⟩
    · exact False.elim (sink_not_old ha (by rw [hc]; exact c'.isLt))
    · have hs : Sink (if i = 0 then z₁ else z₂) := by split <;> assumption
      have hlt : a.val < (if i = 0 then z₁ else z₂).val := by split <;> assumption
      obtain ⟨hb, hle, _⟩ := ih hs
      exact ⟨hb, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

theorem Extension.lowerAt_reflect (e : Extension ϕ ψ)
    {π : List (Fin 2)} {a b : V (k + (2 * n + 2))} (h : LowerAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd _ u → b = Fin.castAdd _ v → LowerAt ϕ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons z₁ z₂ z b a π i hl hd hp ih =>
    rintro u v rfl rfl
    rcases e.lower _ _ _ hl with ⟨a', b', c', hl', rfl, rfl, rfl⟩ | ⟨h₁, h₂, _⟩
    · apply LowerAt.cons hl' ((e.derives_original _ _).mp hd)
      exact ih _ _ rfl (by split <;> rfl)
    · have hs : Source (if i = 0 then z₁ else z₂) := by split <;> assumption
      exact False.elim (source_not_old (e.lowerAt_source hp hs).1 u.isLt)

theorem Extension.upperAt_reflect (e : Extension ϕ ψ)
    {π : List (Fin 2)} {a b : V (k + (2 * n + 2))} (h : UpperAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd _ u → b = Fin.castAdd _ v → UpperAt ϕ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z z₁ z₂ b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ _ hl with ⟨c', a', b', hl', rfl, rfl, rfl⟩ | ⟨h₁, h₂, _⟩
    · apply UpperAt.cons ((e.derives_original _ _).mp hd) hl'
      exact ih _ _ (by split <;> rfl) rfl
    · have hs : Sink (if i = 0 then z₁ else z₂) := by split <;> assumption
      exact False.elim (sink_not_old (e.upperAt_sink hp hs).1 v.isLt)

theorem Extension.lowerAt_original (e : Extension ϕ ψ) (π : List (Fin 2)) (u v : V k) :
    LowerAt ψ π (Fin.castAdd _ u) (Fin.castAdd _ v) ↔ LowerAt ϕ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

theorem Extension.upperAt_original (e : Extension ϕ ψ) (π : List (Fin 2)) (u v : V k) :
    UpperAt ψ π (Fin.castAdd _ u) (Fin.castAdd _ v) ↔ UpperAt ϕ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

theorem Extension.cycle_original (e : Extension ϕ ψ) {π : List (Fin 2)}
    {a b : V (k + (2 * n + 2))} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u : V k, a = Fin.castAdd _ u) ∧ (∃ v : V k, b = Fin.castAdd _ v) := by
  have hsa : ¬ Source a := fun hs => (Nat.lt_irrefl _) ((e.lowerAt_source hl hs).2.2 hn)
  have htb : ¬ Sink b := fun ht => (Nat.lt_irrefl _) ((e.upperAt_sink hu ht).2.2 hn)
  constructor
  · rcases variable_cases a with h | hs | ht
    · exact h
    · exact False.elim (hsa hs)
    · have he := e.derives_out_of_sink hd ht
      exact False.elim (htb (he ▸ ht))
  · rcases variable_cases b with h | hs | ht
    · exact h
    · have he := e.derives_into_source hd hs
      exact False.elim (hsa (he ▸ hs))
    · exact False.elim (htb ht)

/-- Adding source and sink chains preserves cycle clashes. -/
theorem Extension.cycleClash_iff (e : Extension ϕ ψ) : CycleClash ψ ↔ CycleClash ϕ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
    exact ⟨π, u, v, hn, (e.lowerAt_original ..).mp hl,
      (e.derives_original ..).mp hd, (e.upperAt_original ..).mp hu⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, Fin.castAdd _ u, Fin.castAdd _ v, hn, hl.map _ e.old_mem,
      hd.map _ e.old_mem, hu.map _ e.old_mem⟩

theorem mem_lowerSteps {v : ℕ → V m} {b : V m} {ν : List (Fin 2)} {l : Lit m}
    (h : l ∈ lowerSteps v b ν) :
    ∃ j i, j < ν.length ∧ l = lowerLink i (v j) (v (j + 1)) b := by
  induction ν generalizing v with
  | nil => simp [lowerSteps] at h
  | cons i ν ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, i, by simp, rfl⟩
    · obtain ⟨j, i', hj, he⟩ := ih h
      exact ⟨j + 1, i', by simp; omega, he⟩

theorem mem_upperSteps {v : ℕ → V m} {t : V m} {ν : List (Fin 2)} {l : Lit m}
    (h : l ∈ upperSteps v t ν) :
    ∃ j i, j < ν.length ∧ l = upperLink i (v j) (v (j + 1)) t := by
  induction ν generalizing v with
  | nil => simp [upperSteps] at h
  | cons i ν ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, i, by simp, rfl⟩
    · obtain ⟨j, i', hj, he⟩ := ih h
      exact ⟨j + 1, i', by simp; omega, he⟩

theorem source_xv (x : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ n) :
    Source (xv x n j) := by
  simp only [Source, xv, dif_pos hj]; omega

theorem sink_yv (y : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ n) :
    Sink (yv y n j) := by
  simp only [Sink, yv, dif_pos hj]; omega

theorem source_bv : Source (bv k n) := by simp [Source, bv]
theorem sink_tv : Sink (tv k n) := by simp [Sink, tv]

theorem not_sink_xv (x : V k) (j : ℕ) : ¬ Sink (xv x n j) := by
  unfold xv Sink
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem not_source_yv (y : V k) (j : ℕ) : ¬ Source (yv y n j) := by
  unfold yv Source
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem xv_lt_next (x : V k) {j : ℕ} (hj : j < n) :
    (xv x n j).val < (xv x n (j + 1)).val := by
  unfold xv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem yv_lt_next (y : V k) {j : ℕ} (hj : j < n) :
    (yv y n j).val < (yv y n (j + 1)).val := by
  unfold yv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem xv_lt_bv (x : V k) (j : ℕ) : (xv x n j).val < (bv k n).val := by
  unfold xv bv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem yv_lt_tv (y : V k) (j : ℕ) : (yv y n j).val < (tv k n).val := by
  unfold yv tv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem lowerSteps_fLe {x : V k} {ν : List (Fin 2)}
    {a b c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a b c ∈ lowerSteps (xv x ν.length) (bv k ν.length) ν) :
    Source a ∧ Source b ∧ ¬ Sink c ∧ c.val < a.val ∧ c.val < b.val := by
  obtain ⟨j, i, hj, he⟩ := mem_lowerSteps h
  have hs := source_xv x (show 0 < j + 1 ∧ j + 1 ≤ ν.length by omega)
  fin_cases i <;> simp only [lowerLink, Fin.isValue] at he
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hs, source_bv, not_sink_xv _ _, xv_lt_next _ hj, xv_lt_bv _ _⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨source_bv, hs, not_sink_xv _ _, xv_lt_bv _ _, xv_lt_next _ hj⟩

theorem upperSteps_leF {y : V k} {ν : List (Fin 2)}
    {c a b : V (k + (2 * ν.length + 2))}
    (h : Lit.leF c a b ∈ upperSteps (yv y ν.length) (tv k ν.length) ν) :
    Sink a ∧ Sink b ∧ ¬ Source c ∧ c.val < a.val ∧ c.val < b.val := by
  obtain ⟨j, i, hj, he⟩ := mem_upperSteps h
  have hs := sink_yv y (show 0 < j + 1 ∧ j + 1 ≤ ν.length by omega)
  fin_cases i <;> simp only [upperLink, Fin.isValue] at he
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨hs, sink_tv, not_source_yv _ _, yv_lt_next _ hj, yv_lt_tv _ _⟩
  · obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨sink_tv, hs, not_source_yv _ _, yv_lt_tv _ _, yv_lt_next _ hj⟩

theorem leF_not_mem_lowerSteps (v : ℕ → V m) (b c a a' : V m) (ν : List (Fin 2)) :
    Lit.leF c a a' ∉ lowerSteps v b ν := by
  intro h
  obtain ⟨_, i, _, he⟩ := mem_lowerSteps h
  unfold lowerLink at he; split_ifs at he

theorem fLe_not_mem_upperSteps (v : ℕ → V m) (t a a' c : V m) (ν : List (Fin 2)) :
    Lit.fLe a a' c ∉ upperSteps v t ν := by
  intro h
  obtain ⟨_, i, _, he⟩ := mem_upperSteps h
  unfold upperLink at he; split_ifs at he

theorem fLe_mem_lift {a b c : V (k + m)} (h : Lit.fLe a b c ∈ ϕ.lift m) :
    ∃ a' b' c' : V k, Lit.fLe a' b' c' ∈ ϕ ∧
      a = Fin.castAdd _ a' ∧ b = Fin.castAdd _ b' ∧ c = Fin.castAdd _ c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp [Lit.lift, Lit.rename] at he
  case fLe a' b' c' => exact ⟨a', b', c', hl, he.1.symm, he.2.1.symm, he.2.2.symm⟩

theorem leF_mem_lift {c a b : V (k + m)} (h : Lit.leF c a b ∈ ϕ.lift m) :
    ∃ c' a' b' : V k, Lit.leF c' a' b' ∈ ϕ ∧
      c = Fin.castAdd _ c' ∧ a = Fin.castAdd _ a' ∧ b = Fin.castAdd _ b' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp [Lit.lift, Lit.rename] at he
  case leF c' a' b' => exact ⟨c', a', b', hl, he.1.symm, he.2.1.symm, he.2.2.symm⟩

theorem rUnsafe_extension (ϕ : Constraint k) (x y : V k) (ν : List (Fin 2)) :
    Extension ϕ (rUnsafe ϕ x y ν) := by
  constructor
  · intro l hl
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  · intro a b c h
    simp [rUnsafe, noBotChain, botChain, fLe_not_mem_upperSteps] at h
    rcases h with h | h | ⟨rfl, rfl, rfl⟩
    · exact Or.inl (fLe_mem_lift h)
    · exact Or.inr (lowerSteps_fLe h)
    · exact Or.inr ⟨source_bv, source_bv, not_sink_xv _ _, xv_lt_bv _ _, xv_lt_bv _ _⟩
  · intro c a b h
    simp [rUnsafe, noBotChain, botChain, leF_not_mem_lowerSteps] at h
    rcases h with h | h
    · exact Or.inl (leF_mem_lift h)
    · exact Or.inr (upperSteps_leF h)

theorem lUnsafe_extension (ϕ : Constraint k) (x y : V k) (ν : List (Fin 2)) :
    Extension ϕ (lUnsafe ϕ x y ν) := by
  constructor
  · intro l hl
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  · intro a b c h
    simp [lUnsafe, topChain, noTopChain, fLe_not_mem_upperSteps] at h
    rcases h with h | h
    · exact Or.inl (fLe_mem_lift h)
    · exact Or.inr (lowerSteps_fLe h)
  · intro c a b h
    simp [lUnsafe, topChain, noTopChain, leF_not_mem_lowerSteps] at h
    rcases h with h | h | ⟨rfl, rfl, rfl⟩
    · exact Or.inl (leF_mem_lift h)
    · exact Or.inr (upperSteps_leF h)
    · exact Or.inr ⟨sink_tv, sink_tv, not_source_yv _ _, yv_lt_tv _ _, yv_lt_tv _ _⟩

end TransferFin

open TransferFin

variable {ϕ : Constraint k} {x y : V k} {ν : List (Fin 2)}
  {w : V (k + (2 * ν.length + 2))} {j : ℕ}

/-- The right mismatch extension has a cycle clash exactly when the original constraints do. -/
theorem cycleClash_unsafe_iff : CycleClash (rUnsafe ϕ x y ν) ↔ CycleClash ϕ :=
  (rUnsafe_extension ϕ x y ν).cycleClash_iff

/-- The left mismatch extension has a cycle clash exactly when the original constraints do. -/
theorem cycleClash_lUnsafe_iff : CycleClash (lUnsafe ϕ x y ν) ↔ CycleClash ϕ :=
  (lUnsafe_extension ϕ x y ν).cycleClash_iff

/-- A satisfiable right mismatch system has a finite solution if the original system does. -/
theorem satFin_unsafe_of_sat
    (hf : ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ)
    (hi : ∃ ρ', Sat ρ' (rUnsafe ϕ x y ν)) :
    ∃ σ' : V (k + (2 * ν.length + 2)) → FTree,
      Sat (FTree.toTree ∘ σ') (rUnsafe ϕ x y ν) := by
  apply satFin_iff.mpr
  exact ⟨satisfiable_iff_not_labelClash.mp hi,
    fun hc => (satFin_iff.mp hf).2 (cycleClash_unsafe_iff.mp hc)⟩

/-- A satisfiable left mismatch system has a finite solution if the original system does. -/
theorem satFin_lUnsafe_of_sat
    (hf : ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ)
    (hi : ∃ ρ', Sat ρ' (lUnsafe ϕ x y ν)) :
    ∃ σ' : V (k + (2 * ν.length + 2)) → FTree,
      Sat (FTree.toTree ∘ σ') (lUnsafe ϕ x y ν) := by
  apply satFin_iff.mpr
  exact ⟨satisfiable_iff_not_labelClash.mp hi,
    fun hc => (satFin_iff.mp hf).2 (cycleClash_lUnsafe_iff.mp hc)⟩

/-- Finite entailment is equivalent to finite unsatisfiability or unrestricted entailment. -/
theorem entailsFin_iff : EntailsFin ϕ x y ↔
    (¬ (∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ) ∨ Entails ϕ x y) := by
  classical
  constructor
  · intro he
    by_contra hn
    obtain ⟨hf, hi⟩ := not_or.mp hn
    have hf' := not_not.mp hf
    obtain ⟨ν, hr | hl⟩ := not_entails_iff.mp hi
    · obtain ⟨σ, hσ⟩ := satFin_unsafe_of_sat hf' hr
      obtain ⟨hϕ, hxy⟩ := Safety.rUnsafe_sound hσ
      exact hxy (he (σ ∘ Fin.castAdd _) hϕ)
    · obtain ⟨σ, hσ⟩ := satFin_lUnsafe_of_sat hf' hl
      obtain ⟨hϕ, hxy⟩ := Safety.lUnsafe_sound hσ
      exact hxy (he (σ ∘ Fin.castAdd _) hϕ)
  · rintro (hf | hi)
    · exact entailsFin_of_not_satFin hf
    · exact hi.toFin

/-- Finite entailment reduces to the finite-satisfiability decision and unrestricted entailment. -/
theorem entailsFin_iff_decider :
    EntailsFin ϕ x y ↔ (satFinB ϕ = false ∨ Entails ϕ x y) := by
  rw [entailsFin_iff, ← satFinB_iff]
  simp

end DeciNSSE
