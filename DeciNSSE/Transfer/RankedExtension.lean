import DeciNSSE.Constraints.PathBounds

/-! # Ranked source and sink extensions

An extension embeds the old variables and adds fresh ones. New lower children
are sources and new upper children are sinks, with ranks strictly increasing
along their nonempty paths. Separation prevents new derivations between old
variables and prevents new self-cycles.
-/

namespace DeciNSSE

section Rename

variable {n k K : ℕ} {r : V k → V K} {ϕ : Constraint n k}

theorem fLe_mem_rename {a : Fin n → V K} {c : V K} (h : Lit.fLe a c ∈ ϕ.map (Lit.rename r)) :
    ∃ a' c', Lit.fLe a' c' ∈ ϕ ∧ a = r ∘ a' ∧ c = r c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp only [Lit.rename, Lit.fLe.injEq, reduceCtorEq] at he
  exact ⟨_, _, hl, he.1.symm, he.2.symm⟩

theorem leF_mem_rename {c : V K} {b : Fin n → V K} (h : Lit.leF c b ∈ ϕ.map (Lit.rename r)) :
    ∃ c' b', Lit.leF c' b' ∈ ϕ ∧ c = r c' ∧ b = r ∘ b' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp only [Lit.rename, Lit.leF.injEq, reduceCtorEq] at he
  exact ⟨_, _, hl, he.1.symm, he.2.symm⟩

theorem eqBot_mem_rename {c : V K} (h : Lit.eqBot c ∈ ϕ.map (Lit.rename r)) :
    ∃ c', Lit.eqBot c' ∈ ϕ ∧ c = r c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp only [Lit.rename, Lit.eqBot.injEq, reduceCtorEq] at he
  exact ⟨_, hl, he.symm⟩

theorem eqTop_mem_rename {c : V K} (h : Lit.eqTop c ∈ ϕ.map (Lit.rename r)) :
    ∃ c', Lit.eqTop c' ∈ ϕ ∧ c = r c' := by
  obtain ⟨l, hl, he⟩ := List.mem_map.mp h
  cases l <;> simp only [Lit.rename, Lit.eqTop.injEq, reduceCtorEq] at he
  exact ⟨_, hl, he.symm⟩

end Rename

namespace Ranked

variable {n k K : ℕ}

/-- An injective embedding `ι` of the old variables, abstract fresh classes and
a natural-number rank. Every fresh lower (upper) constructor literal has all
children in the source (sink) class, a non-sink (non-source) root, and
strictly greater child ranks. -/
structure Extension (ι : V k → V K) (ϕ : Constraint n k) (ψ : Constraint n K)
    (Source Sink : V K → Prop) (rank : V K → ℕ) : Prop where
  injective : Function.Injective ι
  not_source_old : ∀ u, ¬ Source (ι u)
  not_sink_old : ∀ u, ¬ Sink (ι u)
  source_not_sink : ∀ {z}, Source z → ¬ Sink z
  variable_cases : ∀ z, (∃ u, z = ι u) ∨ Source z ∨ Sink z
  old_mem : ∀ l ∈ ϕ, l.rename ι ∈ ψ
  lower : ∀ a c, Lit.fLe a c ∈ ψ →
    (∃ a' c', Lit.fLe a' c' ∈ ϕ ∧ a = ι ∘ a' ∧ c = ι c') ∨
    ((∀ i, Source (a i) ∧ rank c < rank (a i)) ∧ ¬ Sink c)
  upper : ∀ c b, Lit.leF c b ∈ ψ →
    (∃ c' b', Lit.leF c' b' ∈ ϕ ∧ c = ι c' ∧ b = ι ∘ b') ∨
    ((∀ i, Sink (b i) ∧ rank c < rank (b i)) ∧ ¬ Source c)

variable {ι : V k → V K} {ϕ : Constraint n k} {ψ : Constraint n K}
  {Source Sink : V K → Prop} {rank : V K → ℕ}

theorem Extension.upper_children (e : Extension ι ϕ ψ Source Sink rank)
    {c : V K} {b : Fin n → V K} (h : Lit.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by
  rcases e.upper _ _ h with ⟨c', b', _, rfl, rfl⟩ | ⟨hb, _⟩
  · exact e.not_source_old (b' i)
  · exact e.source_not_sink.mt (not_not.mpr (hb i).1)

theorem Extension.lower_children (e : Extension ι ϕ ψ Source Sink rank)
    {a : Fin n → V K} {c : V K} (h : Lit.fLe a c ∈ ψ) (i : Fin n) :
    ¬ Sink (a i) := by
  rcases e.lower _ _ h with ⟨a', c', _, rfl, rfl⟩ | ⟨ha, _⟩
  · exact e.not_sink_old (a' i)
  · exact e.source_not_sink (ha i).1

/-- Only reflexivity and transitivity can end in a source. -/
theorem Extension.derives_into_source (e : Extension ι ϕ ψ Source Sink rank)
    {a b : V K} (h : Derives ψ a b) (hb : Source b) : a = b := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih' hb
    exact (ih (he ▸ hb)).trans he
  | decomp i _ _ hu => exact False.elim (e.upper_children hu i hb)

/-- Dually, only reflexivity and transitivity can start in a sink. -/
theorem Extension.derives_out_of_sink (e : Extension ι ϕ ψ Source Sink rank)
    {a b : V K} (h : Derives ψ a b) (ha : Sink a) : b = a := by
  induction h with
  | refl => rfl
  | trans _ _ ih ih' =>
    have he := ih ha
    exact (ih' (he ▸ ha)).trans he
  | decomp i hl _ _ => exact False.elim (e.lower_children hl i ha)

/-- A transitivity intermediate between old endpoints must itself be old. -/
theorem Extension.middle_original (e : Extension ι ϕ ψ Source Sink rank)
    {u v : V k} {w : V K} (hl : Derives ψ (ι u) w) (hr : Derives ψ w (ι v)) :
    ∃ t, w = ι t := by
  rcases e.variable_cases w with h | hs | ht
  · exact h
  · have he := e.derives_into_source hl hs
    exact False.elim (e.not_source_old u (he ▸ hs))
  · have he := e.derives_out_of_sink hr ht
    exact False.elim (e.not_sink_old v (he ▸ ht))

theorem Extension.derives_reflect (e : Extension ι ϕ ψ Source Sink rank)
    {a b : V K} (h : Derives ψ a b) :
    ∀ u v, a = ι u → b = ι v → Derives ϕ u v := by
  induction h with
  | refl a =>
    intro u v hu hv
    obtain rfl := e.injective (hu.symm.trans hv)
    exact .refl _
  | trans hl hr ih ih' =>
    rintro u v rfl rfl
    obtain ⟨w, hw⟩ := e.middle_original hl hr
    exact .trans (ih u w rfl hw) (ih' w v hw rfl)
  | @decomp a b z w i hl _ hu ih =>
    rintro u v ha hb
    rcases e.lower _ _ hl with ⟨a', z', hl', rfl, rfl⟩ | ⟨hs, _⟩
    · rcases e.upper _ _ hu with ⟨w', b', hu', rfl, rfl⟩ | ⟨ht, _⟩
      · obtain rfl := e.injective ha
        obtain rfl := e.injective hb
        exact .decomp i hl' (ih _ _ rfl rfl) hu'
      · exact False.elim (e.not_sink_old v (hb ▸ (ht i).1))
    · exact False.elim (e.not_source_old u (ha ▸ (hs i).1))

/-- The closure between old variables is unchanged by the extension. -/
theorem Extension.derives_original (e : Extension ι ϕ ψ Source Sink rank) (u v : V k) :
    Derives ψ (ι u) (ι v) ↔ Derives ϕ u v :=
  ⟨fun h => e.derives_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

/-- A lower path ending at a source stays among sources, strictly increasing
the rank whenever the path is nonempty. This also excludes old endpoints. -/
theorem Extension.lowerAt_source (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (h : LowerAt ψ π a b)
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
theorem Extension.upperAt_sink (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (h : UpperAt ψ π a b)
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
theorem Extension.lowerAt_reflect (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (h : LowerAt ψ π a b) :
    ∀ u v, a = ι u → b = ι v → LowerAt ϕ π u v := by
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
theorem Extension.upperAt_reflect (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (h : UpperAt ψ π a b) :
    ∀ u v, a = ι u → b = ι v → UpperAt ϕ π u v := by
  induction h with
  | nil hd =>
    rintro u v rfl rfl
    exact .nil ((e.derives_original _ _).mp hd)
  | @cons a z c b π i hd hl hp ih =>
    rintro u v rfl rfl
    rcases e.upper _ _ hl with ⟨z', c', hl', rfl, rfl⟩ | ⟨hc, _⟩
    · exact UpperAt.cons ((e.derives_original _ _).mp hd) hl' (ih _ _ rfl rfl)
    · exact False.elim (e.not_sink_old v (e.upperAt_sink hp (hc i).1).1)

theorem Extension.lowerAt_original (e : Extension ι ϕ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    LowerAt ψ π (ι u) (ι v) ↔ LowerAt ϕ π u v :=
  ⟨fun h => e.lowerAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

theorem Extension.upperAt_original (e : Extension ι ϕ ψ Source Sink rank)
    (π : List (Fin n)) (u v : V k) :
    UpperAt ψ π (ι u) (ι v) ↔ UpperAt ϕ π u v :=
  ⟨fun h => e.upperAt_reflect h u v rfl rfl, fun h => h.map _ e.old_mem⟩

/-- Both witnesses of a nonempty lower/upper cycle must be original variables. -/
theorem Extension.cycle_original (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u, a = ι u) ∧ (∃ v, b = ι v) := by
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
theorem Extension.cycle_reflect (e : Extension ι ϕ ψ Source Sink rank)
    {π : List (Fin n)} {a b : V K} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v, LowerAt ϕ π u u ∧ Derives ϕ u v ∧ UpperAt ϕ π v v := by
  obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := e.cycle_original hn hl hd hu
  exact ⟨u, v, (e.lowerAt_original ..).mp hl, (e.derives_original ..).mp hd,
    (e.upperAt_original ..).mp hu⟩

end Ranked

end DeciNSSE
