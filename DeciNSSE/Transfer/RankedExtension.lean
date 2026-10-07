import DeciNSSE.Constraints.PathBounds
import DeciNSSE.Transfer.Spines

/-! # Ranked source and sink extensions

New lower children are sources and new upper children are sinks, with ranks
strictly increasing along their nonempty paths. Separation prevents new
derivations between old variables and prevents new self-cycles.
-/

namespace DeciNSSE

namespace Ranked

variable {n k m : ℕ}

/-- Abstract fresh classes and a natural-number rank. Every fresh lower
(upper) constructor literal has all children in the source (sink) class, a
non-sink (non-source) root, and strictly greater child ranks. -/
structure Extension (ϕ : Constraint n k) (ψ : Constraint n (k + m))
    (Source Sink : V (k + m) → Prop) (rank : V (k + m) → ℕ) : Prop where
  source_not_old : ∀ {z}, Source z → ¬ z.val < k
  sink_not_old : ∀ {z}, Sink z → ¬ z.val < k
  source_not_sink : ∀ {z}, Source z → ¬ Sink z
  variable_cases : ∀ z, (∃ u : V k, z = Fin.castAdd m u) ∨ Source z ∨ Sink z
  old_mem : ∀ l ∈ ϕ, l.rename (Fin.castAdd m) ∈ ψ
  lower : ∀ a c, Lit.fLe a c ∈ ψ →
    (∃ a' c', Lit.fLe a' c' ∈ ϕ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c') ∨
    ((∀ i, Source (a i) ∧ rank c < rank (a i)) ∧ ¬ Sink c)
  upper : ∀ c b, Lit.leF c b ∈ ψ →
    (∃ c' b', Lit.leF c' b' ∈ ϕ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b') ∨
    ((∀ i, Sink (b i) ∧ rank c < rank (b i)) ∧ ¬ Source c)

variable {ϕ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

theorem Extension.not_source_old (e : Extension ϕ ψ Source Sink rank) (u : V k) :
    ¬ Source (Fin.castAdd m u) := fun h => e.source_not_old h u.isLt

theorem Extension.not_sink_old (e : Extension ϕ ψ Source Sink rank) (u : V k) :
    ¬ Sink (Fin.castAdd m u) := fun h => e.sink_not_old h u.isLt

theorem Extension.upper_children (e : Extension ϕ ψ Source Sink rank)
    {c : V (k + m)} {b : Fin n → V (k + m)} (h : Lit.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by
  rcases e.upper _ _ h with ⟨c', b', _, rfl, rfl⟩ | ⟨hb, _⟩
  · exact e.not_source_old (b' i)
  · exact e.source_not_sink.mt (not_not.mpr (hb i).1)

theorem Extension.lower_children (e : Extension ϕ ψ Source Sink rank)
    {a : Fin n → V (k + m)} {c : V (k + m)} (h : Lit.fLe a c ∈ ψ) (i : Fin n) :
    ¬ Sink (a i) := by
  rcases e.lower _ _ h with ⟨a', c', _, rfl, rfl⟩ | ⟨ha, _⟩
  · exact e.not_sink_old (a' i)
  · exact e.source_not_sink (ha i).1

/-- Only reflexivity and transitivity can end in a source. -/
theorem Extension.derives_into_source (e : Extension ϕ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp i _ _ hu => exact False.elim (e.upper_children hu i hb)

/-- Dually, only reflexivity and transitivity can start in a sink. -/
theorem Extension.derives_out_of_sink (e : Extension ϕ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp i hl _ _ => exact False.elim (e.lower_children hl i ha)

/-- A transitivity intermediate between old endpoints must itself be old. -/
theorem Extension.middle_original (e : Extension ϕ ψ Source Sink rank)
    {u v : V k} {w : V (k + m)}
    (hl : Derives ψ (Fin.castAdd m u) w)
    (hr : Derives ψ w (Fin.castAdd m v)) : ∃ t : V k, w = Fin.castAdd m t := by
  rcases e.variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (e.not_source_old u (he ▸ hs))
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (e.not_sink_old v (he ▸ ht))

theorem Extension.derives_reflect (e : Extension ϕ ψ Source Sink rank)
    {a b : V (k + m)} (h : Derives ψ a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → Derives ϕ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    have he : u = v := Fin.castAdd_injective _ _ (hu.symm.trans hv)
    subst v; exact .refl _
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | @decomp a b z w i hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ hl with ⟨a', z', hl', rfl, rfl⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ hu with ⟨w', b', hu', rfl, rfl⟩ | ⟨ht, _⟩
      · have h₁ : a' i = u := Fin.castAdd_injective _ _ ha
        have h₂ : b' i = v := Fin.castAdd_injective _ _ hb
        subst u; subst v
        exact .decomp i hl' (ih _ _ rfl rfl) hu'
      · exact False.elim (e.not_sink_old v (hb ▸ (ht i).1))
    · exact False.elim (e.not_source_old u (ha ▸ (hs i).1))

/-- The closure between old variables is unchanged by the extension. -/
theorem Extension.derives_original (e : Extension ϕ ψ Source Sink rank) (u v : V k) :
    Derives ψ (Fin.castAdd m u) (Fin.castAdd m v) ↔ Derives ϕ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

/-- A lower path ending at a source stays among sources, strictly increasing
the rank whenever the path is nonempty. This also excludes old endpoints. -/
theorem Extension.lowerAt_source (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : LowerAt ψ π a b)
    (hb : Source b) : Source a ∧ rank b ≤ rank a ∧ (π ≠ [] → rank b < rank a) := by
  induction h with
  | nil hd =>
    have he := e.derives_into_source hd hb
    subst he
    exact ⟨hb, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons c z b a π i hl hd hp ih =>
    have he := e.derives_into_source hd hb
    subst z
    rcases e.lower _ _ hl with ⟨c', z', _, _, rfl⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_source_old z' hb)
    · obtain ⟨ha, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨ha, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- The symmetric rank invariant for upper paths starting at a sink. -/
theorem Extension.upperAt_sink (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ rank a ≤ rank b ∧ (π ≠ [] → rank a < rank b) := by
  induction h with
  | nil hd =>
    have he := e.derives_out_of_sink hd ha
    subst he
    exact ⟨ha, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons a z c b π i hd hl hp ih =>
    have he := e.derives_out_of_sink hd ha
    subst z
    rcases e.upper _ _ hl with ⟨z', c', _, rfl, _⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_sink_old z' ha)
    · obtain ⟨hb, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨hb, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩

/-- Lower paths between original variables cannot use a fresh constructor edge. -/
theorem Extension.lowerAt_reflect (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : LowerAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → LowerAt ϕ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons c z b a π i hl hd hp ih =>
    rintro u v rfl rfl
    rcases e.lower _ _ hl with ⟨c', z', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact LowerAt.cons hl' ((e.derives_original _ _).mp hd) (ih _ _ rfl rfl)
    · exact False.elim (e.not_source_old u (e.lowerAt_source hp (hc i).1).1)

/-- Upper paths between original variables cannot use a fresh constructor edge. -/
theorem Extension.upperAt_reflect (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (h : UpperAt ψ π a b) :
    ∀ u v : V k, a = Fin.castAdd m u → b = Fin.castAdd m v → UpperAt ϕ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z c b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ hl with ⟨z', c', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact UpperAt.cons ((e.derives_original _ _).mp hd) hl' (ih _ _ rfl rfl)
    · exact False.elim (e.not_sink_old v (e.upperAt_sink hp (hc i).1).1)

theorem Extension.lowerAt_original (e : Extension ϕ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    LowerAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ LowerAt ϕ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

theorem Extension.upperAt_original (e : Extension ϕ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    UpperAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ UpperAt ϕ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

/-- Both witnesses of a nonempty lower/upper cycle must be original variables. -/
theorem Extension.cycle_original (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u : V k, a = Fin.castAdd m u) ∧ (∃ v : V k, b = Fin.castAdd m v) := by
  have hsa : ¬ Source a := fun hs => (Nat.lt_irrefl _) ((e.lowerAt_source hl hs).2.2 hn)
  have htb : ¬ Sink b := fun ht => (Nat.lt_irrefl _) ((e.upperAt_sink hu ht).2.2 hn)
  constructor
  · rcases e.variable_cases a with h | hs | ht
    · exact h
    · exact False.elim (hsa hs)
    · have he := e.derives_out_of_sink hd ht
      exact False.elim (htb (he ▸ ht))
  · rcases e.variable_cases b with h | hs | ht
    · exact h
    · have he := e.derives_into_source hd hs
      exact False.elim (hsa (he ▸ hs))
    · exact False.elim (htb ht)

/-- A nonempty lower/upper cycle of the extension is one of the original constraint. -/
theorem Extension.cycle_reflect (e : Extension ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v : V k, LowerAt ϕ π u u ∧ Derives ϕ u v ∧ UpperAt ϕ π v v := by
  obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
  exact ⟨u, v, (e.lowerAt_original ..).mp hl, (e.derives_original ..).mp hd,
    (e.upperAt_original ..).mp hu⟩

end Ranked

namespace Spine

variable {n k m : ℕ}

/-- The fresh lower block together with the bottom filler. -/
def Source (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  k ≤ z.val ∧ (z.val < k + L ∨ z.val = k + 2 * L)

/-- The fresh upper block together with the top filler. -/
def Sink (k L : ℕ) (z : V (k + (2 * L + 2))) : Prop :=
  (k + L ≤ z.val ∧ z.val < k + 2 * L) ∨ z.val = k + 2 * L + 1

variable {L : ℕ}

theorem source_not_old {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ z.val < k := by
  unfold Source at h; omega

theorem sink_not_old {z : V (k + (2 * L + 2))} (h : Sink k L z) : ¬ z.val < k := by
  unfold Sink at h; omega

theorem source_not_sink {z : V (k + (2 * L + 2))} (h : Source k L z) : ¬ Sink k L z := by
  unfold Source at h; unfold Sink; omega

theorem variable_cases (z : V (k + (2 * L + 2))) :
    (∃ u : V k, z = Fin.castAdd _ u) ∨ Source k L z ∨ Sink k L z := by
  by_cases h : z.val < k
  · exact Or.inl ⟨⟨z.val, h⟩, rfl⟩
  · right; unfold Source Sink; have := z.isLt; omega

theorem source_xv (x : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Source k L (xv x L j) := by
  simp only [Source, xv, dite_eq_left hj]; omega

theorem sink_yv (y : V k) {j : ℕ} (hj : 0 < j ∧ j ≤ L) : Sink k L (yv y L j) := by
  simp only [Sink, yv, dite_eq_left hj]; omega

theorem source_bv : Source k L (bv k L) := by simp [Source, bv]
theorem sink_tv : Sink k L (tv k L) := by simp [Sink, tv]

theorem not_sink_xv (x : V k) (j : ℕ) : ¬ Sink k L (xv x L j) := by
  unfold xv Sink
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem not_source_yv (y : V k) (j : ℕ) : ¬ Source k L (yv y L j) := by
  unfold yv Source
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem xv_lt_next (x : V k) {j : ℕ} (hj : j < L) :
    (xv x L j).val < (xv x L (j + 1)).val := by
  unfold xv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem yv_lt_next (y : V k) {j : ℕ} (hj : j < L) :
    (yv y L j).val < (yv y L (j + 1)).val := by
  unfold yv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

theorem xv_lt_bv (x : V k) (j : ℕ) : (xv x L j).val < (bv k L).val := by
  unfold xv bv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := x.isLt <;> omega

theorem yv_lt_tv (y : V k) (j : ℕ) : (yv y L j).val < (tv k L).val := by
  unfold yv tv
  split_ifs <;> simp only [Fin.val_castAdd] <;> have := y.isLt <;> omega

/-- A lower step: every child (the next spine variable or the bottom filler)
is a source of strictly greater index. -/
theorem lowerSteps_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ lowerSteps (xv x ν.length) (bv k ν.length) ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_lowerSteps_iff.mp h
  simp only [lowerLink, Lit.fLe.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_sink_xv _ _⟩
  rcases spineChildren_eq_or ν[j] i (xv x ν.length (j + 1)) (bv k ν.length) with h | h <;>
    rw [h]
  · exact ⟨source_xv x ⟨by omega, by omega⟩, xv_lt_next x hj⟩
  · exact ⟨source_bv, xv_lt_bv x j⟩

/-- An upper step: every child (the next spine variable or the top filler)
is a sink of strictly greater index. -/
theorem upperSteps_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ upperSteps (yv y ν.length) (tv k ν.length) ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  obtain ⟨j, hj, he⟩ := mem_upperSteps_iff.mp h
  simp only [upperLink, Lit.leF.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  refine ⟨fun i => ?_, not_source_yv _ _⟩
  rcases spineChildren_eq_or ν[j] i (yv y ν.length (j + 1)) (tv k ν.length) with h | h <;>
    rw [h]
  · exact ⟨sink_yv y ⟨by omega, by omega⟩, yv_lt_next y hj⟩
  · exact ⟨sink_tv, yv_lt_tv y j⟩

theorem noBotChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ noBotChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.fLe.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨source_bv, xv_lt_bv x _⟩, not_sink_xv _ _⟩

theorem topChain_fLe {x : V k} {ν : List (Fin n)}
    {a : Fin n → V (k + (2 * ν.length + 2))} {c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a c ∈ topChain x ν) :
    (∀ i, Source k ν.length (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact lowerSteps_fLe h
  · simp [reduceCtorEq] at h

theorem noTopChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ noTopChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Lit.leF.injEq,
      reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun _ => ⟨sink_tv, yv_lt_tv y _⟩, not_source_yv _ _⟩

theorem botChain_leF {y : V k} {ν : List (Fin n)}
    {c : V (k + (2 * ν.length + 2))} {b : Fin n → V (k + (2 * ν.length + 2))}
    (h : Lit.leF c b ∈ botChain y ν) :
    (∀ i, Sink k ν.length (b i) ∧ c.val < (b i).val) ∧ ¬ Source k ν.length c := by
  rcases List.mem_append.mp h with h | h
  · exact upperSteps_leF h
  · simp [reduceCtorEq] at h

theorem fLe_not_mem_botChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ botChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem fLe_not_mem_noTopChain (y : V k) (ν : List (Fin n))
    (a : Fin n → V (k + (2 * ν.length + 2))) (c : V (k + (2 * ν.length + 2))) :
    Lit.fLe a c ∉ noTopChain y ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact fLe_not_mem_upperSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem leF_not_mem_noBotChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ noBotChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem leF_not_mem_topChain (x : V k) (ν : List (Fin n))
    (c : V (k + (2 * ν.length + 2))) (b : Fin n → V (k + (2 * ν.length + 2))) :
    Lit.leF c b ∉ topChain x ν := by
  intro h
  rcases List.mem_append.mp h with h | h
  · exact leF_not_mem_lowerSteps _ _ _ _ _ h
  · simp [reduceCtorEq] at h

theorem fLe_mem_lift {ϕ : Constraint n k} {a : Fin n → V (k + m)} {c : V (k + m)}
    (h : Lit.fLe a c ∈ ϕ.lift m) :
    ∃ a' c', Lit.fLe a' c' ∈ ϕ ∧ a = Fin.castAdd m ∘ a' ∧ c = Fin.castAdd m c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | fLe a' c' =>
    simp only [Lit.rename, Lit.fLe.injEq] at he
    exact ⟨a', c', hl, he.1.symm, he.2.symm⟩
  | leF _ _ => simp [Lit.rename] at he
  | eqBot _ => simp [Lit.rename] at he
  | eqTop _ => simp [Lit.rename] at he

theorem leF_mem_lift {ϕ : Constraint n k} {c : V (k + m)} {b : Fin n → V (k + m)}
    (h : Lit.leF c b ∈ ϕ.lift m) :
    ∃ c' b', Lit.leF c' b' ∈ ϕ ∧ c = Fin.castAdd m c' ∧ b = Fin.castAdd m ∘ b' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | leF c' b' =>
    simp only [Lit.rename, Lit.leF.injEq] at he
    exact ⟨c', b', hl, he.1.symm, he.2.symm⟩
  | fLe _ _ => simp [Lit.rename] at he
  | eqBot _ => simp [Lit.rename] at he
  | eqTop _ => simp [Lit.rename] at he

theorem eqBot_mem_lift {ϕ : Constraint n k} {c : V (k + m)}
    (h : Lit.eqBot c ∈ ϕ.lift m) : ∃ c', Lit.eqBot c' ∈ ϕ ∧ c = Fin.castAdd m c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | eqBot c' =>
    simp only [Lit.rename, Lit.eqBot.injEq] at he
    exact ⟨c', hl, he.symm⟩
  | fLe _ _ => simp [Lit.rename] at he
  | leF _ _ => simp [Lit.rename] at he
  | eqTop _ => simp [Lit.rename] at he

theorem eqTop_mem_lift {ϕ : Constraint n k} {c : V (k + m)}
    (h : Lit.eqTop c ∈ ϕ.lift m) : ∃ c', Lit.eqTop c' ∈ ϕ ∧ c = Fin.castAdd m c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l with
  | eqTop c' =>
    simp only [Lit.rename, Lit.eqTop.injEq] at he
    exact ⟨c', hl, he.symm⟩
  | fLe _ _ => simp [Lit.rename] at he
  | leF _ _ => simp [Lit.rename] at he
  | eqBot _ => simp [Lit.rename] at he

theorem mem_lift_of_mem {ϕ : Constraint n k} {l : Lit n k} (hl : l ∈ ϕ) :
    l.rename (Fin.castAdd m) ∈ ϕ.lift m := List.mem_map.mpr ⟨l, hl, rfl⟩

/-- Any fresh block whose constructor literals are classified like the chain
literals extends the lifted constraint. -/
theorem extension_of_append {ϕ : Constraint n k} {A : Constraint n (k + (2 * L + 2))}
    (hlow : ∀ a c, Lit.fLe a c ∈ A →
      (∀ i, Source k L (a i) ∧ c.val < (a i).val) ∧ ¬ Sink k L c)
    (hup : ∀ c b, Lit.leF c b ∈ A →
      (∀ i, Sink k L (b i) ∧ c.val < (b i).val) ∧ ¬ Source k L c) :
    Ranked.Extension ϕ (ϕ.lift _ ++ A) (Source k L) (Sink k L) Fin.val where
  source_not_old := source_not_old
  sink_not_old := sink_not_old
  source_not_sink := source_not_sink
  variable_cases := variable_cases
  old_mem := fun l hl => List.mem_append_left _ (mem_lift_of_mem hl)
  lower := by
    intro a c h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (fLe_mem_lift h)
    · exact Or.inr (hlow a c h)
  upper := by
    intro c b h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (leF_mem_lift h)
    · exact Or.inr (hup c b h)

/-- The right unsafety encoding satisfies the source/sink contract. -/
theorem rUnsafe_extension (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    Ranked.Extension ϕ (rUnsafe ϕ x y ν) (Source k ν.length) (Sink k ν.length)
      Fin.val := by
  have he : rUnsafe ϕ x y ν = ϕ.lift _ ++ (noBotChain x ν ++ botChain y ν) :=
    List.append_assoc _ _ _
  rw [he]
  apply extension_of_append
  · intro a c h
    rcases List.mem_append.mp h with h | h
    · exact noBotChain_fLe h
    · exact False.elim (fLe_not_mem_botChain _ _ _ _ h)
  · intro c b h
    rcases List.mem_append.mp h with h | h
    · exact False.elim (leF_not_mem_noBotChain _ _ _ _ h)
    · exact botChain_leF h

/-- The left unsafety encoding satisfies the source/sink contract. -/
theorem lUnsafe_extension (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    Ranked.Extension ϕ (lUnsafe ϕ x y ν) (Source k ν.length) (Sink k ν.length)
      Fin.val := by
  have he : lUnsafe ϕ x y ν = ϕ.lift _ ++ (topChain x ν ++ noTopChain y ν) :=
    List.append_assoc _ _ _
  rw [he]
  apply extension_of_append
  · intro a c h
    rcases List.mem_append.mp h with h | h
    · exact topChain_fLe h
    · exact False.elim (fLe_not_mem_noTopChain _ _ _ _ h)
  · intro c b h
    rcases List.mem_append.mp h with h | h
    · exact False.elim (leF_not_mem_topChain _ _ _ _ h)
    · exact noTopChain_leF h

end Spine

end DeciNSSE
