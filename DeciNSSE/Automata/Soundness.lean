import DeciNSSE.Automata.Construction

/-! # Soundness of the constraint automata

Ordinary accepting paths and periodic caps imply path safety in every solution.
Universality of both automata therefore implies entailment.
-/

namespace DeciNSSE

open CState CapAutomaton Safety Construction

variable {k : ℕ} {ϕ : Constraint k} {α : V k → Tree}
  {x y u v : V k} {π π' : List (Fin 2)}

def LSafeAt (α : V k → Tree) (x y : V k) (π : List (Fin 2)) : Prop :=
  HasLabel (α x) π Sym.top → HasLabel (α y) π Sym.top

def RSafeAt (α : V k → Tree) (x y : V k) (π : List (Fin 2)) : Prop :=
  HasLabel (α y) π Sym.bot → HasLabel (α x) π Sym.bot

def UpperBoundAt (α : V k → Tree) (u : V k) (π : List (Fin 2)) (v : V k) : Prop :=
  α u ≤ PathBounds.embed Tree.top π (α v)

def LowerBoundAt (α : V k → Tree) (π : List (Fin 2)) (v u : V k) : Prop :=
  PathBounds.embed Tree.bot π (α v) ≤ α u

theorem UpperAt.upperBoundAt (h : UpperAt ϕ π u v) (hs : Sat α ϕ) :
    UpperBoundAt α u π v := h.le_embed hs

theorem LowerAt.lowerBoundAt (h : LowerAt ϕ π v u) (hs : Sat α ϕ) :
    LowerBoundAt α π v u := h.embed_le hs

theorem UpperBoundAt.trace_le (h : UpperBoundAt α u π v) :
    trace (α u) π ≤ α v := by
  simpa only [trace_embed] using trace_mono h π

theorem LowerBoundAt.le_trace (h : LowerBoundAt α π v u) :
    α v ≤ trace (α u) π := by
  simpa only [trace_embed] using trace_mono h π

namespace Soundness

theorem hasLabel_prefix {T : Tree} {σ τ : List (Fin 2)} {a : Sym}
    (hp : σ <+: τ) (h : HasLabel T σ a) : HasLabel T τ a := by
  obtain ⟨ν, hn, hl⟩ := h
  exact ⟨ν, hn.trans hp, hl⟩

theorem leaf_prefix_of_missing {T : Tree} {σ : List (Fin 2)} (h : T.fn σ = none) :
    ∃ τ, τ <+: σ ∧ (T.fn τ = some Sym.bot ∨ T.fn τ = some Sym.top) := by
  induction σ using List.reverseRecOn with
  | nil => exact (T.wf.1 h).elim
  | append_singleton σ i ih =>
    cases he : T.fn σ with
    | none =>
      obtain ⟨τ, hp, ht⟩ := ih he
      exact ⟨τ, hp.trans (List.prefix_append _ _), ht⟩
    | some a =>
      refine ⟨σ, List.prefix_append _ _, ?_⟩
      cases a with
      | bot => exact Or.inl he
      | top => exact Or.inr he
      | f => have := (T.child_isSome_iff σ i).mpr he; simp [h] at this

/-- An upper bound along a nonempty period preserves left safety on its periodic prefixes. -/
theorem leftSafe_of_periodic_upperBound (hn : π ≠ []) (hu : UpperBoundAt α u π v)
    (π' : List (Fin 2)) (hp : π' <+: π ++ π') : LSafeAt α u v π' := by
  intro hx
  by_cases hd : ((α v).fn π').isSome
  · have he : ((PathBounds.embed Tree.top π (α v)).fn (π ++ π')).isSome := by
      simpa only [PathBounds.embed_fn_append] using hd
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp
      ((Tree.subtree_isSome_iff _ _).mpr he)
    exact upper_bound_proper_prefix ⟨_, hu, hT⟩ hp
      (by intro heq; have := congrArg List.length heq; simp only [List.length_append] at this
          have := List.length_pos_iff.mpr hn; omega) hx
  · have hm : (α v).fn π' = none := by
      cases he : (α v).fn π' <;> simp_all
    obtain ⟨τ, hτ, hb | ht⟩ := leaf_prefix_of_missing hm
    · have hv : trace (α v) π' = Tree.bot :=
        (trace_eq_bot_iff _ _).mpr ⟨τ, hτ, hb⟩
      have hbot : trace (α u) (π ++ π') = Tree.bot := (Tree.le_bot_iff _).mp
        (by simpa only [trace_append, hv] using trace_mono hu.trace_le π')
      obtain ⟨σ, hσ, hs⟩ := (trace_eq_bot_iff _ _).mp hbot

      by_cases hlen : σ.length ≤ π'.length
      · have hσ' := List.prefix_of_prefix_length_le hσ hp hlen
        have hb' := (trace_eq_bot_iff _ _).mpr (⟨σ, hσ', hs⟩ : HasLabel (α u) π' .bot)
        have ht' := (trace_eq_top_iff _ _).mpr hx
        simp [hb'] at ht'
      · have hp' := List.prefix_of_prefix_length_le hp hσ (by omega)
        have ht' := (trace_eq_top_iff _ _).mpr (hasLabel_prefix hp' hx)
        have hb' := (trace_eq_bot_iff _ _).mpr
          (⟨σ, List.prefix_rfl, hs⟩ : HasLabel (α u) σ .bot)
        simp [hb'] at ht'
    · exact ⟨τ, hτ, ht⟩

/-- A lower bound along a period preserves right safety on its periodic prefixes. -/
theorem rightSafe_of_periodic_lowerBound (hl : LowerBoundAt α π u v)
    (π' : List (Fin 2)) (hp : π' <+: π ++ π') : RSafeAt α u v π' := by
  intro hy
  have hb := (trace_eq_bot_iff _ _).mpr (hasLabel_prefix hp hy)
  apply (trace_eq_bot_iff _ _).mp
  apply (Tree.le_bot_iff _).mp
  simpa only [← trace_append, hb] using trace_mono hl.le_trace π'

/-- Matching upper and lower path bounds transport left safety through their common prefix. -/
theorem leftSafe_prepend_bounds (hu : UpperBoundAt α x π u) (hl : LowerBoundAt α π v y)
    (hs : LSafeAt α u v π') : LSafeAt α x y (π ++ π') := by
  intro hx
  have hxu := trace_mono hu.trace_le π'
  have hut : trace (α u) π' = Tree.top := (Tree.top_le_iff _).mp
    (by simpa only [← trace_append, (trace_eq_top_iff _ _).mpr hx] using hxu)
  have hvt := (trace_eq_top_iff _ _).mpr (hs ((trace_eq_top_iff _ _).mp hut))
  apply (trace_eq_top_iff _ _).mp
  apply (Tree.top_le_iff _).mp
  simpa only [← trace_append, hvt] using trace_mono hl.le_trace π'

/-- Matching upper and lower path bounds transport right safety through their common prefix. -/
theorem rightSafe_prepend_bounds (hu : UpperBoundAt α x π u) (hl : LowerBoundAt α π v y)
    (hs : RSafeAt α u v π') : RSafeAt α x y (π ++ π') := by
  intro hy
  have hvb : trace (α v) π' = Tree.bot := (Tree.le_bot_iff _).mp
    (by simpa only [← trace_append, (trace_eq_bot_iff _ _).mpr hy]
          using trace_mono hl.le_trace π')
  have hub := (trace_eq_bot_iff _ _).mpr (hs ((trace_eq_bot_iff _ _).mp hvb))
  apply (trace_eq_bot_iff _ _).mp
  apply (Tree.le_bot_iff _).mp
  simpa only [← trace_append, hub] using trace_mono hu.trace_le π'

theorem pedge_l_iff {q r : CState k} :
    (construct ϕ x y .l).pedge q r = true ↔
      ∃ u v s, q = pair (some v) s ∧ r = pair (some u) (some v) := by
  cases q <;> cases r <;> simp [construct, pedgeB]
  rename_i a b c d
  cases a <;> cases c <;> cases d <;> simp [eq_comm]

theorem pedge_r_iff {q r : CState k} :
    (construct ϕ x y .r).pedge q r = true ↔
      ∃ u v s, q = pair s (some u) ∧ r = pair (some u) (some v) := by
  cases q <;> cases r <;> simp [construct, pedgeB]
  rename_i a b c d
  cases b <;> cases c <;> cases d <;> simp [eq_comm]

theorem pedge_self_final {θ : Side} {q : CState k}
    (h : (construct ϕ x y θ).pedge q q = true) :
    (construct ϕ x y θ).final q = true := by
  have hm : Move ϕ 0 q all := by
    cases θ with
    | l =>
      obtain ⟨u, v, s, hq, hr⟩ := pedge_l_iff.mp h
      rw [hr] at hq
      have he : u = v := by simpa [left] using congrArg left hq
      subst v
      rw [hr]
      exact .reflexivity (.refl u)
    | r =>
      obtain ⟨u, v, s, hq, hr⟩ := pedge_r_iff.mp h
      rw [hr] at hq
      have he : v = u := by simpa [right] using congrArg right hq
      subst v
      rw [hr]
      exact .reflexivity (.refl u)
  exact Bool.or_eq_true_iff.mpr (Or.inr ((moveB_iff _ _ _ _).mpr hm))

theorem empty_loop_memA {θ : Side} {q r : CState k}
    (hr : Runs (construct ϕ x y θ) (construct ϕ x y θ).init π q)
    (hm : Runs (construct ϕ x y θ) q [] r)
    (hp : (construct ϕ x y θ).pedge r q = true)
    (hw : Words.IsPrefixOfPower [] π') :
    π ++ π' ∈ LangA (construct ϕ x y θ) := by
  obtain rfl := (Words.isPrefixOfPower_nil_iff).mp hw
  obtain rfl := (runs_nil_iff _).mp hm
  rw [List.append_nil]
  exact ⟨q, hr, pedge_self_final hp⟩

theorem initial_run_bounds {θ : Side}
    (h : Runs (construct ϕ x y θ) (construct ϕ x y θ).init π
      (pair (some u) (some v))) : UpperAt ϕ π x u ∧ LowerAt ϕ π v y := by
  obtain ⟨a, ha, hu⟩ := runs_upper h rfl
  obtain ⟨b, hb, hl⟩ := runs_lower h rfl
  have hxa : x = a := by simpa [construct, left] using ha
  have hyb : y = b := by simpa [construct, right] using hb
  subst a b
  exact ⟨hu, hl⟩

end Soundness

theorem soundP_l (h : π ∈ LangP (construct ϕ x y .l)) : LSafe ϕ x y π := by
  obtain ⟨ρ, μ', q₁, q₂, μ, rfl, hr, hm, hp, hw⟩ := h
  by_cases hn : μ = []
  · subst μ
    exact soundA_l (Soundness.empty_loop_memA hr hm hp hw)
  obtain ⟨u, v, s, rfl, rfl⟩ := Soundness.pedge_l_iff.mp hp
  obtain ⟨hu, hl⟩ := Soundness.initial_run_bounds hr
  have hμ := (runs_pair_iff_upperAt hn).mp ⟨some v, s, hm⟩
  intro α hs
  exact Soundness.leftSafe_prepend_bounds (hu.upperBoundAt hs) (hl.lowerBoundAt hs)
    (Soundness.leftSafe_of_periodic_upperBound hn (hμ.upperBoundAt hs) μ' ((Words.prefix_pow_iff hn).mp hw))

theorem soundP_r (h : π ∈ LangP (construct ϕ x y .r)) : RSafe ϕ x y π := by
  obtain ⟨ρ, μ', q₁, q₂, μ, rfl, hr, hm, hp, hw⟩ := h
  by_cases hn : μ = []
  · subst μ
    exact soundA_r (Soundness.empty_loop_memA hr hm hp hw)
  obtain ⟨u, v, s, rfl, rfl⟩ := Soundness.pedge_r_iff.mp hp
  obtain ⟨hu, hl⟩ := Soundness.initial_run_bounds hr
  have hμ := (runs_pair_iff_lowerAt hn).mp ⟨some u, s, hm⟩
  intro α hs
  exact Soundness.rightSafe_prepend_bounds (hu.upperBoundAt hs) (hl.lowerBoundAt hs)
    (Soundness.rightSafe_of_periodic_lowerBound (hμ.lowerBoundAt hs) μ' ((Words.prefix_pow_iff hn).mp hw))

theorem sound_l (h : π ∈ Lang (construct ϕ x y .l)) : LSafe ϕ x y π :=
  h.elim soundA_l soundP_l

theorem sound_r (h : π ∈ Lang (construct ϕ x y .r)) : RSafe ϕ x y π :=
  h.elim soundA_r soundP_r

theorem entails_of_universal
    (hl : ∀ π, π ∈ Lang (construct ϕ x y .l))
    (hr : ∀ π, π ∈ Lang (construct ϕ x y .r)) : Entails ϕ x y :=
  entails_iff_safe.mpr (fun π => ⟨sound_l (hl π), sound_r (hr π)⟩)

end DeciNSSE
