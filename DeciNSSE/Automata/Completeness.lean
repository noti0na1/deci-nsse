import DeciNSSE.Words
import DeciNSSE.Transfer.Finite

/-! # Constraint chains and automaton completeness

Lower-bound chains encode a prescribed path. Their derivations factor into
original paths and chain segments, yielding the periodic witnesses needed
for completeness of the constraint automata.
-/

namespace DeciNSSE.Completeness

open Safety TransferFin Words

variable {k m : ℕ}

def chainConstraint (ϕ : Constraint k) (x : V k) (ν : Word) :
    Constraint (k + (2 * ν.length + 2)) :=
  ϕ.lift _ ++ noBotChain x ν

variable {ϕ : Constraint k} {x : V k} {ν : Word}

theorem chain_extension : Extension ϕ (chainConstraint ϕ x ν) := by
  constructor
  · intro l hl
    exact List.mem_append_left _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
  · intro a b c h
    simp [chainConstraint, noBotChain] at h
    rcases h with h | h | ⟨rfl, rfl, rfl⟩
    · exact Or.inl (fLe_mem_lift h)
    · exact Or.inr (lowerSteps_fLe h)
    · exact Or.inr ⟨source_bv, source_bv, not_sink_xv _ _, xv_lt_bv _ _, xv_lt_bv _ _⟩
  · intro c a b h
    simp [chainConstraint, noBotChain, leF_not_mem_lowerSteps] at h
    exact Or.inl (leF_mem_lift h)

theorem old_mem (l : Lit k) (hl : l ∈ ϕ) :
    l.rename (Fin.castAdd _) ∈ chainConstraint ϕ x ν :=
  chain_extension.old_mem l hl

theorem derives_original (u v : V k) :
    Derives (chainConstraint ϕ x ν) (Fin.castAdd _ u) (Fin.castAdd _ v) ↔
      Derives ϕ u v := chain_extension.derives_original u v

theorem upperAt_original (π : Word) (u v : V k) :
    UpperAt (chainConstraint ϕ x ν) π (Fin.castAdd _ u) (Fin.castAdd _ v) ↔
      UpperAt ϕ π u v := chain_extension.upperAt_original π u v

theorem lowerAt_original (π : Word) (u v : V k) :
    LowerAt (chainConstraint ϕ x ν) π (Fin.castAdd _ u) (Fin.castAdd _ v) ↔
      LowerAt ϕ π u v := chain_extension.lowerAt_original π u v

theorem derives_into_xchain {j : ℕ} (hj : 0 < j ∧ j ≤ ν.length)
    {w : V (k + (2 * ν.length + 2))}
    (h : Derives (chainConstraint ϕ x ν) w (xv x ν.length j)) :
    w = xv x ν.length j := chain_extension.derives_into_source h (source_xv x hj)

theorem leF_original {a b c : V (k + (2 * ν.length + 2))}
    (h : Lit.leF c a b ∈ chainConstraint ϕ x ν) :
    ∃ c' a' b' : V k, Lit.leF c' a' b' ∈ ϕ ∧
      c = Fin.castAdd _ c' ∧ a = Fin.castAdd _ a' ∧ b = Fin.castAdd _ b' := by
  simp [chainConstraint, noBotChain, leF_not_mem_lowerSteps] at h
  exact leF_mem_lift h

theorem mem_lowerSteps_iff {v : ℕ → V m} {b : V m} {μ : Word} {l : Lit m} :
    l ∈ lowerSteps v b μ ↔
      ∃ j, ∃ hj : j < μ.length, l = lowerLink μ[j] (v j) (v (j + 1)) b := by
  induction μ generalizing v with
  | nil => simp [lowerSteps]
  | cons i μ ih =>
    constructor
    · intro h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, by simp, rfl⟩
      · obtain ⟨j, hj, he⟩ := ih.mp h
        exact ⟨j + 1, by simpa using hj, he⟩
    · rintro ⟨j, hj, he⟩
      cases j with
      | zero => exact List.mem_cons.mpr (Or.inl he)
      | succ j =>
        apply List.mem_cons.mpr ∘ Or.inr
        exact ih.mpr ⟨j, by simpa using hj, he⟩

theorem xv_ne_bv (j : ℕ) : xv x ν.length j ≠ bv k ν.length :=
  fun h => (ne_of_lt (xv_lt_bv x j)) (congrArg Fin.val h)

theorem xv_eq_iff {j t : ℕ} (hj : j ≤ ν.length) (ht : t ≤ ν.length) :
    xv x ν.length j = xv x ν.length t ↔ j = t := by
  constructor
  · intro h
    exact congrArg Fin.val (xv_injective x ν.length (a₁ := ⟨j, by omega⟩)
      (a₂ := ⟨t, by omega⟩) h)
  · rintro rfl; rfl

theorem xv_eq_old {j : ℕ} (hj : j ≤ ν.length) {u : V k}
    (he : xv x ν.length j = Fin.castAdd _ u) : j = 0 ∧ x = u := by
  by_cases hz : j = 0
  · subst j
    exact ⟨rfl, Fin.ext (by simpa using congrArg Fin.val he)⟩
  · exact False.elim (source_not_old (source_xv x ⟨by omega, hj⟩)
      (by rw [he]; exact u.isLt))

theorem fLe_chain_root {a b c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a b c ∈ noBotChain x ν) :
    ∃ j ≤ ν.length, c = xv x ν.length j := by
  simp only [noBotChain, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq] at h
  rcases h with h | he
  · obtain ⟨j, hj, he⟩ := mem_lowerSteps_iff.mp h
    unfold lowerLink at he
    split_ifs at he <;> cases he <;> exact ⟨j, hj.le, rfl⟩
  · cases he
    exact ⟨ν.length, le_rfl, rfl⟩

theorem fLe_chain_child {a b c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a b c ∈ noBotChain x ν) {j : ℕ} (hj : j ≤ ν.length)
    (i : Fin 2) (he : (if i = 0 then a else b) = xv x ν.length j) :
    ∃ t, ∃ ht : t < ν.length,
      c = xv x ν.length t ∧ j = t + 1 ∧ i = ν[t] := by
  simp only [noBotChain, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq] at h
  rcases h with h | h
  · obtain ⟨t, ht, hl⟩ := mem_lowerSteps_iff.mp h
    have hn := xv_ne_bv (x := x) (ν := ν) j
    have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    have hv : ν[t] = 0 ∨ ν[t] = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hv with hv | hv <;>
      simp [lowerLink, hv] at hl <;> obtain ⟨rfl, rfl, rfl⟩ := hl
    · exact ⟨t, ht, rfl, (xv_eq_iff hj (by omega)).mp he.symm, hv.symm⟩
    · exact False.elim (hn he.symm)
    · exact False.elim (hn he.symm)
    · exact ⟨t, ht, rfl, (xv_eq_iff hj (by omega)).mp he.symm, hv.symm⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [ite_self] at he
    exact False.elim (xv_ne_bv j he.symm)

theorem lowerSteps_prefix {ψ : Constraint m} {v : ℕ → V m} {b : V m} {μ : Word}
    (hm : ∀ l ∈ lowerSteps v b μ, l ∈ ψ) (j : ℕ) (hj : j ≤ μ.length) :
    LowerAt ψ (μ.take j) (v j) (v 0) := by
  induction μ generalizing v j with
  | nil =>
    have : j = 0 := by simpa using hj
    subst j
    exact .nil (.refl _)
  | cons i μ ih =>
    cases j with
    | zero => exact .nil (.refl _)
    | succ j =>
      have hl := hm _ (List.mem_cons_self ..)
      have hp := ih (v := fun t => v (t + 1))
        (fun l h => hm l (List.mem_cons_of_mem _ h)) j (by simpa using hj)
      fin_cases i <;> simp only [lowerLink, Fin.isValue] at hl <;>
        exact .cons hl (.refl _) hp

theorem lowerSteps_interval {ψ : Constraint m} {v : ℕ → V m} {b : V m} {μ : Word}
    (hm : ∀ l ∈ lowerSteps v b μ, l ∈ ψ) {j t : ℕ} (hjt : j ≤ t)
    (ht : t ≤ μ.length) : LowerAt ψ ((μ.take t).drop j) (v t) (v j) := by
  induction j generalizing μ v t with
  | zero => simpa using lowerSteps_prefix hm t ht
  | succ j ih =>
    cases μ with
    | nil => simp at ht; omega
    | cons i μ =>
      cases t with
      | zero => omega
      | succ t =>
        exact ih (v := fun s => v (s + 1))
          (fun l h => hm l (List.mem_cons_of_mem _ h)) (by omega) (by simpa using ht)

theorem lowerAt_chain_interval {j t : ℕ} (hjt : j ≤ t) (ht : t ≤ ν.length) :
    LowerAt (chainConstraint ϕ x ν) ((ν.take t).drop j)
      (xv x ν.length t) (xv x ν.length j) :=
  lowerSteps_interval (fun _ h => List.mem_append_right _ (List.mem_append_left _ h)) hjt ht

theorem lowerAt_chain_prefix {j : ℕ} (hj : j ≤ ν.length) :
    LowerAt (chainConstraint ϕ x ν) (ν.take j)
      (xv x ν.length j) (Fin.castAdd _ x) := by
  simpa using lowerAt_chain_interval (ϕ := ϕ) (x := x) (ν := ν) (Nat.zero_le j) hj

theorem terminal_fLe : ∃ a b, Lit.fLe a b (xv x ν.length ν.length) ∈
    chainConstraint ϕ x ν :=
  ⟨bv k ν.length, bv k ν.length, by simp [chainConstraint, noBotChain]⟩

private theorem decomp_chain_upper
    {a b c d : V (k + (2 * ν.length + 2))} {u v : V k}
    (hl : Lit.fLe a b c ∈ chainConstraint ϕ x ν)
    (hd : Derives (chainConstraint ϕ x ν) c d)
    (hu : Lit.leF d (Fin.castAdd _ u) (Fin.castAdd _ v) ∈ chainConstraint ϕ x ν)
    (ih : ∀ j ≤ ν.length, ∀ w : V k, c = xv x ν.length j →
      d = Fin.castAdd _ w → UpperAt ϕ (ν.take j) x w)
    (i : Fin 2) {j : ℕ} (hj : j ≤ ν.length)
    (he : (if i = 0 then a else b) = xv x ν.length j) :
    UpperAt ϕ (ν.take j) x (if i = 0 then u else v) := by
  obtain ⟨d', u', v', hu', rfl, heu, hev⟩ := leF_original hu
  have eu : u = u' := Fin.castAdd_injective _ _ heu
  have ev : v = v' := Fin.castAdd_injective _ _ hev
  subst u'; subst v'
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨a', b', c', hl', rfl, rfl, rfl⟩ := fLe_mem_lift hl
    have he' : xv x ν.length j = Fin.castAdd _ (if i = 0 then a' else b') := by
      simpa only [apply_ite] using he.symm
    obtain ⟨rfl, rfl⟩ := xv_eq_old hj he'
    have hd' := (derives_original c' d').mp hd
    fin_cases i
    · exact .nil (.decomp_left hl' hd' hu')
    · exact .nil (.decomp_right hl' hd' hu')
  · obtain ⟨t, ht, hc, rfl, hi⟩ := fLe_chain_child hl hj i he
    have hp := ih t ht.le d' hc rfl
    have hstep : UpperAt ϕ [i] d' (if i = 0 then u else v) :=
      .cons (.refl _) hu' (.nil (.refl _))
    rw [List.take_succ_eq_append_getElem ht, ← hi]
    exact hp.comp hstep

theorem derives_chain_reflect {a b : V (k + (2 * ν.length + 2))}
    (h : Derives (chainConstraint ϕ x ν) a b) :
    ∀ j ≤ ν.length, ∀ v : V k, a = xv x ν.length j →
      b = Fin.castAdd _ v → UpperAt ϕ (ν.take j) x v := by
  induction h with
  | refl a =>
    intro j hj v ha hb
    obtain ⟨rfl, rfl⟩ := xv_eq_old hj (ha.symm.trans hb)
    exact .nil (.refl _)
  | @trans a b c hl hr ih ih' =>
    rintro j hj v rfl rfl
    rcases variable_cases b with ⟨w, rfl⟩ | hs | hs
    · simpa using (ih j hj w rfl rfl).comp
        (.nil ((derives_original w v).mp hr))
    · have he := chain_extension.derives_into_source hl hs
      exact ih' j hj v he.symm rfl
    · have he := chain_extension.derives_out_of_sink hr hs
      exact False.elim (sink_not_old (he ▸ hs) v.isLt)
  | @decomp_left a b c d u v hl hd hu ih =>
    rintro j hj w ha hb
    obtain ⟨d', u', v', _, rfl, rfl, rfl⟩ := leF_original hu
    have hw : u' = w := Fin.castAdd_injective _ _ hb
    subst w
    exact decomp_chain_upper hl hd hu ih 0 hj ha
  | @decomp_right a b c d u v hl hd hu ih =>
    rintro j hj w ha hb
    obtain ⟨d', u', v', _, rfl, rfl, rfl⟩ := leF_original hu
    have hw : v' = w := Fin.castAdd_injective _ _ hb
    subst w
    exact decomp_chain_upper hl hd hu ih 1 hj ha

theorem derives_chain_iff {j : ℕ} (hj : j ≤ ν.length) (v : V k) :
    Derives (chainConstraint ϕ x ν) (xv x ν.length j) (Fin.castAdd _ v) ↔
      UpperAt ϕ (ν.take j) x v := by
  constructor
  · intro h; exact derives_chain_reflect h j hj v rfl rfl
  · intro h
    exact upperAt_nil_iff.mp ((lowerAt_chain_prefix hj).decompose_upper
      (by simpa using (upperAt_original (ν.take j) x v).mpr h))

theorem not_lowerAt_xv_bv (j : ℕ) (π : Word) :
    ¬ LowerAt (chainConstraint ϕ x ν) π (xv x ν.length j) (bv k ν.length) := by
  intro h
  have hle := (chain_extension.lowerAt_source h source_bv).2.1
  exact (not_le_of_gt (xv_lt_bv x j)) hle

theorem fLe_chain_path {a b c : V (k + (2 * ν.length + 2))}
    (h : Lit.fLe a b c ∈ noBotChain x ν) {j : ℕ} {i : Fin 2} {π : Word}
    (hp : LowerAt (chainConstraint ϕ x ν) π (xv x ν.length j)
      (if i = 0 then a else b)) :
    ∃ t, ∃ ht : t < ν.length, c = xv x ν.length t ∧ i = ν[t] ∧
      LowerAt (chainConstraint ϕ x ν) π (xv x ν.length j) (xv x ν.length (t + 1)) := by
  simp only [noBotChain, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq] at h
  rcases h with h | h
  · obtain ⟨t, ht, hl⟩ := mem_lowerSteps_iff.mp h
    have hi : i = 0 ∨ i = 1 := by omega
    have hv : ν[t] = 0 ∨ ν[t] = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hv with hv | hv <;>
      simp [lowerLink, hv] at hl <;> obtain ⟨rfl, rfl, rfl⟩ := hl
    · exact ⟨t, ht, rfl, hv.symm, hp⟩
    · exact False.elim (not_lowerAt_xv_bv j π hp)
    · exact False.elim (not_lowerAt_xv_bv j π hp)
    · exact ⟨t, ht, rfl, hv.symm, hp⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [ite_self] at hp
    exact False.elim (not_lowerAt_xv_bv j π hp)

theorem lowerAt_chain_source {j t : ℕ} (hj : j ≤ ν.length)
    (ht : 0 < t ∧ t ≤ ν.length) {π : Word}
    (h : LowerAt (chainConstraint ϕ x ν) π (xv x ν.length j) (xv x ν.length t)) :
    t ≤ j ∧ ν.take j = ν.take t ++ π := by
  induction π generalizing t with
  | nil =>
    have he := derives_into_xchain ht (lowerAt_nil_iff.mp h)
    have hjt := (xv_eq_iff hj ht.2).mp he
    subst j
    exact ⟨le_rfl, by simp⟩
  | cons i π ih =>
    cases h with
    | @cons a b c _ _ _ _ hl hd hp =>
      have hc := derives_into_xchain ht hd
      subst c
      rcases List.mem_append.mp hl with hl | hl
      · obtain ⟨a', b', c', _, _, _, hc⟩ := fLe_mem_lift hl
        exact False.elim (source_not_old (source_xv x ht) (by rw [hc]; exact c'.isLt))
      · obtain ⟨s, hs, he, hi, hp⟩ := fLe_chain_path hl hp
        have hts := (xv_eq_iff ht.2 hs.le).mp he
        subst s
        obtain ⟨hle, heq⟩ := ih ⟨by omega, by omega⟩ hp
        refine ⟨by omega, ?_⟩
        rw [heq, List.take_succ_eq_append_getElem hs, ← hi]
        simp only [List.append_assoc, List.singleton_append]

theorem lowerAt_chain_factor {π : Word}
    {a b : V (k + (2 * ν.length + 2))}
    (h : LowerAt (chainConstraint ϕ x ν) π a b) :
    ∀ j ≤ ν.length, ∀ v : V k, a = xv x ν.length j → b = Fin.castAdd _ v →
      ∃ j' x' π' ρ, j' ≤ j ∧ ν.take j = ν.take j' ++ ρ ∧ π = π' ++ ρ ∧
        UpperAt ϕ (ν.take j') x x' ∧ LowerAt ϕ π' x' v := by
  induction h with
  | nil hd =>
    rintro j hj v rfl rfl
    exact ⟨j, v, [], [], le_rfl, by simp, rfl,
      (derives_chain_iff hj v).mp hd, .nil (.refl _)⟩
  | @cons a b c d w π i hl hd hp ih =>
    rintro j hj v rfl rfl
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨a', b', c', hl', rfl, rfl, rfl⟩ := fLe_mem_lift hl
      obtain ⟨j', x', π', ρ, hle, hpre, hπ, hu, hlower⟩ :=
        ih j hj (if i = 0 then a' else b') rfl (by split <;> rfl)
      exact ⟨j', x', i :: π', ρ, hle, hpre, by simp [hπ], hu,
        .cons hl' ((derives_original c' v).mp hd) hlower⟩
    · obtain ⟨t, ht, rfl, hi, hp⟩ := fLe_chain_path hl hp
      obtain ⟨hle, heq⟩ := lowerAt_chain_source hj ⟨by omega, by omega⟩ hp
      refine ⟨t, v, [], i :: π, by omega, ?_, rfl,
        (derives_chain_iff ht.le v).mp hd, .nil (.refl _)⟩
      rw [heq, List.take_succ_eq_append_getElem ht, ← hi]
      simp only [List.append_assoc, List.singleton_append]

theorem lowerAt_chain_iff {j : ℕ} (hj : j ≤ ν.length) (π : Word) (v : V k) :
    LowerAt (chainConstraint ϕ x ν) π (xv x ν.length j) (Fin.castAdd _ v) ↔
      ∃ j' x' π' ρ, j' ≤ j ∧ ν.take j = ν.take j' ++ ρ ∧ π = π' ++ ρ ∧
        UpperAt ϕ (ν.take j') x x' ∧ LowerAt ϕ π' x' v := by
  constructor
  · intro h; exact lowerAt_chain_factor h j hj v rfl rfl
  · rintro ⟨j', x', π', ρ, _, hpre, rfl, hu, hl⟩
    have hchain := lowerAt_chain_prefix (ϕ := ϕ) (x := x) hj
    rw [hpre] at hchain
    exact (hchain.decompose_lower ((upperAt_original _ x x').mpr hu)).comp
      ((lowerAt_original π' x' v).mpr hl)

theorem eqTop_original {a : V (k + (2 * ν.length + 2))}
    (h : Lit.eqTop a ∈ chainConstraint ϕ x ν) :
    ∃ a' : V k, Lit.eqTop a' ∈ ϕ ∧ a = Fin.castAdd _ a' := by
  simp only [chainConstraint, noBotChain, List.mem_append, List.mem_cons,
    List.not_mem_nil, reduceCtorEq, or_false] at h
  rcases h with h | h
  · obtain ⟨l, hl, he⟩ := List.mem_map.mp h
    cases l <;> simp [Lit.lift, Lit.rename] at he
    case eqTop a' => exact ⟨a', hl, he.symm⟩
  · obtain ⟨_, i, _, he⟩ := mem_lowerSteps h
    unfold lowerLink at he
    split_ifs at he

theorem eqBot_original_or_bv {a : V (k + (2 * ν.length + 2))}
    (h : Lit.eqBot a ∈ chainConstraint ϕ x ν) :
    (∃ a' : V k, Lit.eqBot a' ∈ ϕ ∧ a = Fin.castAdd _ a') ∨ a = bv k ν.length := by
  simp only [chainConstraint, noBotChain, List.mem_append, List.mem_cons,
    List.not_mem_nil, reduceCtorEq, or_false] at h
  rcases h with h | h | h
  · obtain ⟨l, hl, he⟩ := List.mem_map.mp h
    cases l <;> simp [Lit.lift, Lit.rename] at he
    case eqBot a' => exact Or.inl ⟨a', hl, he.symm⟩
  · obtain ⟨_, i, _, he⟩ := mem_lowerSteps h
    unfold lowerLink at he
    split_ifs at he
  · exact Or.inr (by simpa using h)

theorem not_lowerLabel_f_bv (π : Word) :
    ¬ LowerLabel (chainConstraint ϕ x ν) π .f (bv k ν.length) := by
  rintro ⟨v, a, b, hl, hp⟩
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨a', b', v', _, _, _, rfl⟩ := fLe_mem_lift hl
    exact source_not_old (chain_extension.lowerAt_source hp source_bv).1 v'.isLt
  · obtain ⟨j, _, rfl⟩ := fLe_chain_root hl
    exact not_lowerAt_xv_bv j π hp

theorem not_lowerLabel_top_bv (π : Word) :
    ¬ LowerLabel (chainConstraint ϕ x ν) π .top (bv k ν.length) := by
  rintro ⟨v, hl, hp⟩
  obtain ⟨v', _, rfl⟩ := eqTop_original hl
  exact source_not_old (chain_extension.lowerAt_source hp source_bv).1 v'.isLt

theorem lowerLabel_lift {π : Word} {g : Sym} {v : V k} (h : LowerLabel ϕ π g v) :
    LowerLabel (chainConstraint ϕ x ν) π g (Fin.castAdd _ v) := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨w, a, b, hl, hp⟩ := h
    exact ⟨Fin.castAdd _ w, Fin.castAdd _ a, Fin.castAdd _ b,
      old_mem _ hl, (lowerAt_original π w v).mpr hp⟩
  | top =>
    obtain ⟨w, hl, hp⟩ := h
    exact ⟨Fin.castAdd _ w, old_mem _ hl, (lowerAt_original π w v).mpr hp⟩

theorem lowerLabel_top_original_iff (π : Word) (v : V k) :
    LowerLabel (chainConstraint ϕ x ν) π .top (Fin.castAdd _ v) ↔
      LowerLabel ϕ π .top v := by
  constructor
  · rintro ⟨w, hl, hp⟩
    obtain ⟨w', hl', rfl⟩ := eqTop_original hl
    exact ⟨w', hl', (lowerAt_original π w' v).mp hp⟩
  · exact lowerLabel_lift

theorem lowerLabel_top_original {π : Word} {v : V k} (_hπ : π <+: ν)
    (h : LowerLabel (chainConstraint ϕ x ν) π .top (Fin.castAdd _ v)) :
    LowerLabel ϕ π .top v := (lowerLabel_top_original_iff π v).mp h

theorem lowerLabel_comp {ψ : Constraint m} {π ρ : Word} {g : Sym} {u v : V m}
    (h : LowerLabel ψ ρ g u) (hp : LowerAt ψ π u v) :
    LowerLabel ψ (π ++ ρ) g v := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨w, a, b, hl, hw⟩ := h
    exact ⟨w, a, b, hl, hw.comp hp⟩
  | top =>
    obtain ⟨w, hl, hw⟩ := h
    exact ⟨w, hl, hw.comp hp⟩

theorem lowerLabel_f_prefix {ψ : Constraint m} {π τ : Word} {v : V m}
    (h : LowerLabel ψ π .f v) (hτ : τ <+: π) : LowerLabel ψ τ .f v := by
  obtain ⟨ρ, rfl⟩ := hτ
  cases ρ with
  | nil => simpa using h
  | cons i ρ =>
    obtain ⟨w, a, b, hl, hp⟩ := h
    obtain ⟨u, hu, hu'⟩ := hp.factor
    cases hu' with
    | @cons a' b' c _ _ _ _ hl' hd _ =>
      exact ⟨c, a', b', hl', by simpa using (LowerAt.nil hd).comp hu⟩

theorem lowerLabel_f_chain_root :
    LowerLabel (chainConstraint ϕ x ν) ν .f (Fin.castAdd _ x) := by
  obtain ⟨a, b, hl⟩ := terminal_fLe (ϕ := ϕ) (x := x) (ν := ν)
  exact ⟨xv x ν.length ν.length, a, b, hl,
    by simpa using (lowerAt_chain_prefix (ϕ := ϕ) (x := x) (ν := ν) le_rfl)⟩

theorem chain_factor_period {j j' : ℕ} {π' ρ : Word}
    (hj : j ≤ ν.length) (hjj : j' ≤ j)
    (hpre : ν.take j = ν.take j' ++ ρ) (hν : ν = π' ++ ρ) :
    ∃ π₂, ν.take j' <+: ν ∧ π' = ν.take j' ++ π₂ ∧
      (π₂ ≠ [] → ∃ ν', ν = ν.take j' ++ ν' ∧ IsPrefixOfPower π₂ ν') := by
  have hj' : j' ≤ ν.length := le_trans hjj hj
  have hlen : (ν.take j').length ≤ π'.length := by
    have h₁ := congrArg List.length hpre
    have h₂ := congrArg List.length hν
    simp only [List.length_take, Nat.min_eq_left hj, Nat.min_eq_left hj',
      List.length_append] at h₁ ⊢
    simp only [List.length_append] at h₂
    omega
  have hpp : ν.take j' <+: π' :=
    List.prefix_of_prefix_length_le (List.take_prefix ..) ⟨ρ, hν.symm⟩ hlen
  obtain ⟨π₂, he⟩ := hpp
  have heν : ν = ν.take j' ++ (π₂ ++ ρ) := calc
    ν = π' ++ ρ := hν
    _ = (ν.take j' ++ π₂) ++ ρ := congrArg (· ++ ρ) he.symm
    _ = ν.take j' ++ (π₂ ++ ρ) := List.append_assoc ..
  have hρ : ρ <+: π₂ ++ ρ := by
    apply (List.prefix_append_right_inj (ν.take j')).mp
    calc
      ν.take j' ++ ρ = ν.take j := hpre.symm
      _ <+: ν := List.take_prefix ..
      _ = ν.take j' ++ (π₂ ++ ρ) := heν
  refine ⟨π₂, List.take_prefix .., he.symm, fun hn => ⟨π₂ ++ ρ, heν, ?_⟩⟩
  apply (prefix_pow_iff hn).mpr
  simpa only [List.append_assoc, List.prefix_append_right_inj] using hρ

theorem lowerLabel_f_chain_iff (y : V k) :
    LowerLabel (chainConstraint ϕ x ν) ν .f (Fin.castAdd _ y) ↔
      LowerLabel ϕ ν .f y ∨
        ∃ z π₁ π₂, π₁ <+: ν ∧ LowerAt ϕ (π₁ ++ π₂) z y ∧
          UpperAt ϕ π₁ x z ∧
          (π₂ ≠ [] → ∃ ν', ν = π₁ ++ ν' ∧ IsPrefixOfPower π₂ ν') := by
  constructor
  · rintro ⟨w, a, b, hl, hp⟩
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨a', b', w', hl', rfl, rfl, rfl⟩ := fLe_mem_lift hl
      exact Or.inl ⟨w', a', b', hl', (lowerAt_original ν w' y).mp hp⟩
    · obtain ⟨j, hj, rfl⟩ := fLe_chain_root hl
      obtain ⟨j', z, π', ρ, hjj, hpre, hν, hu, hlower⟩ :=
        (lowerAt_chain_iff hj ν y).mp hp
      obtain ⟨π₂, hprefix, he, hpow⟩ := chain_factor_period hj hjj hpre hν
      exact Or.inr ⟨z, ν.take j', π₂, hprefix, he ▸ hlower, hu, hpow⟩
  · rintro (h | ⟨z, π₁, π₂, hprefix, hl, hu, hpow⟩)
    · exact lowerLabel_lift h
    · obtain ⟨ν', hν⟩ := hprefix
      have hperiod : ν' <+: π₂ ++ ν' := by
        by_cases hn : π₂ = []
        · simp [hn]
        · obtain ⟨ρ, he, hρ⟩ := hpow hn
          have heρ : ν' = ρ := List.append_cancel_left (hν.trans he)
          subst ρ
          exact (prefix_pow_iff hn).mp hρ
      have hroot : LowerLabel (chainConstraint ϕ x ν) (π₁ ++ ν') .f
          (Fin.castAdd _ x) := by rw [hν]; exact lowerLabel_f_chain_root
      have hz := hroot.decompose ((upperAt_original π₁ x z).mpr hu)
      have hy := lowerLabel_comp hz ((lowerAt_original (π₁ ++ π₂) z y).mpr hl)
      apply lowerLabel_f_prefix hy
      rw [← hν, List.append_assoc, List.prefix_append_right_inj]
      exact hperiod

end DeciNSSE.Completeness
