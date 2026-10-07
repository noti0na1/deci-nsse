import DeciNSSE.Semantics.Order

/-! # Finite witnesses to order failure

A trace continues an extreme leaf label along every longer path. Order is
equivalent to preservation of top and bottom prefixes, so every failure has
a finite path witness.
-/

section

namespace DeciNSSE
variable {n : ℕ}
namespace Safety

/-- Follow one edge, keeping a reached leaf fixed. -/
def descend (t : Tree n) (i : Fin n) : Tree n :=
  if h : t.fn [] = some Sym.f then t.branch i h else t

@[simp] theorem descend_bot (i : Fin n) : descend Tree.bot i = Tree.bot := by
  simp [descend]

@[simp] theorem descend_top (i : Fin n) : descend Tree.top i = Tree.top := by
  simp [descend]

@[simp] theorem descend_node (a : Fin n → Tree n) (i : Fin n) :
    descend (Tree.node a) i = a i := by
  apply Tree.ext
  funext w
  simp [descend, Tree.branch]

/-- The subtree at a path, or the first leaf when the path leaves the domain. -/
def trace (t : Tree n) : List (Fin n) → Tree n
  | [] => t
  | i :: ν => trace (descend t i) ν

@[simp] theorem trace_nil (t : Tree n) : trace t [] = t := rfl
@[simp] theorem trace_cons (t : Tree n) (i : Fin n) (ν : List (Fin n)) :
    trace t (i :: ν) = trace (descend t i) ν := rfl
@[simp] theorem trace_bot (ν : List (Fin n)) : trace Tree.bot ν = Tree.bot := by
  induction ν <;> simp_all
@[simp] theorem trace_top (ν : List (Fin n)) : trace Tree.top ν = Tree.top := by
  induction ν <;> simp_all

theorem trace_append (t : Tree n) (ν μ : List (Fin n)) :
    trace t (ν ++ μ) = trace (trace t ν) μ := by
  induction ν generalizing t <;> simp_all

theorem descend_mono {t u : Tree n} (h : t ≤ u) (i : Fin n) :
    descend t i ≤ descend u i := by
  rcases (Tree.le_iff_root_cases _ _).mp h with rfl | rfl |
    ⟨a, b, rfl, rfl, hab⟩
  · simp
  · simp
  · simpa using hab i

theorem trace_mono {t u : Tree n} (h : t ≤ u) (ν : List (Fin n)) :
    trace t ν ≤ trace u ν := by
  induction ν generalizing t u with
  | nil => exact h
  | cons i ν ih => exact ih (descend_mono h i)

/-- A label occurs at some (possibly equal) prefix. -/
def HasLabel (t : Tree n) (ν : List (Fin n)) (s : Sym) : Prop :=
  ∃ τ, τ <+: ν ∧ t.fn τ = some s

@[simp] theorem hasLabel_nil (t : Tree n) (s : Sym) :
    HasLabel t [] s ↔ t.fn [] = some s := by simp [HasLabel]

@[simp] theorem hasLabel_bot (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.bot ν s ↔ s = Sym.bot := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

@[simp] theorem hasLabel_top (ν : List (Fin n)) (s : Sym) :
    HasLabel Tree.top ν s ↔ s = Sym.top := by
  constructor
  · rintro ⟨τ, _, h⟩; cases τ <;> simpa using h.symm
  · rintro rfl; exact ⟨[], List.nil_prefix, rfl⟩

theorem hasLabel_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n))
    (s : Sym) (hs : s ≠ Sym.f) :
    HasLabel (Tree.node a) (i :: w) s ↔ HasLabel (a i) w s := by
  constructor
  · rintro ⟨v, hp, h⟩
    cases v with
    | nil => exact False.elim (hs (Option.some.inj h).symm)
    | cons j v =>
      obtain ⟨z, he⟩ := hp
      have hij : j = i := (List.cons.inj he).1
      subst j
      exact ⟨v, ⟨z, (List.cons.inj he).2⟩, h⟩
  · rintro ⟨v, ⟨z, he⟩, h⟩
    exact ⟨i :: v, ⟨z, by simp [he]⟩, h⟩

theorem trace_eq_bot_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.bot ↔ HasLabel t ν Sym.bot := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ (by decide)]

theorem trace_eq_top_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.top ↔ HasLabel t ν Sym.top := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · rw [trace_cons, descend_node, ih, hasLabel_node_cons _ _ _ _ (by decide)]

/-- Proper prefixes of an existing path cannot carry a nullary symbol. -/
theorem not_hasLabel_of_label {t : Tree n} {ν : List (Fin n)} {a s : Sym}
    (h : t.fn ν = some a) (hs : s ≠ Sym.f) (ha : a ≠ s) : ¬ HasLabel t ν s := by
  rintro ⟨τ, hp, ht⟩
  by_cases he : τ = ν
  · subst τ; exact ha (Option.some.inj (h.symm.trans ht))
  · have hf := t.label_eq_f_of_proper_prefix hp he (by simp [h])
    exact hs (Option.some.inj (ht.symm.trans hf))

/-- A violation of the pathwise order is a failure of left or right safety. -/
theorem not_le_iff_unsafe (t u : Tree n) :
    ¬ t ≤ u ↔ ∃ ν, (trace t ν ≠ Tree.bot ∧ trace u ν = Tree.bot) ∨
      (trace t ν = Tree.top ∧ trace u ν ≠ Tree.top) := by
  classical
  constructor
  · intro h
    change ¬ (∀ ν a b, t.fn ν = some a → u.fn ν = some b → a ≤ b) at h
    push Not at h
    obtain ⟨ν, a, b, ht, hu, hab⟩ := h
    have hc : (b = Sym.bot ∧ a ≠ Sym.bot) ∨ (a = Sym.top ∧ b ≠ Sym.top) := by
      cases a <;> cases b <;> simp_all <;> exact absurd hab (by decide)
    refine ⟨ν, ?_⟩
    rcases hc with ⟨rfl, ha⟩ | ⟨rfl, hb⟩
    · exact Or.inl ⟨fun h => not_hasLabel_of_label ht (by decide) ha
        ((trace_eq_bot_iff _ _).mp h),
        (trace_eq_bot_iff _ _).mpr ⟨ν, List.prefix_refl _, hu⟩⟩
    · exact Or.inr ⟨(trace_eq_top_iff _ _).mpr ⟨ν, List.prefix_refl _, ht⟩,
        fun h => not_hasLabel_of_label hu (by decide) hb ((trace_eq_top_iff _ _).mp h)⟩
  · rintro ⟨ν, h⟩ hle
    have hm := trace_mono hle ν
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy] at hm; exact hx ((Tree.le_bot_iff _).mp hm)
    · rw [hx] at hm; exact hy ((Tree.top_le_iff _).mp hm)

end Safety

/-- A prefix of the word reaches top in the covariant tree. -/
abbrev covPrefTop (w : List (Fin n)) (t : Tree n) := Safety.HasLabel t w Sym.top
/-- A prefix of the word reaches bottom in the covariant tree. -/
abbrev covPrefBot (w : List (Fin n)) (t : Tree n) := Safety.HasLabel t w Sym.bot

theorem hasLabel_dual (t : Tree n) (w : List (Fin n)) (s : Sym) :
    Safety.HasLabel (Tree.dual t) w s ↔ Safety.HasLabel t w (Sym.flip true s) := by
  simp only [Safety.HasLabel, dual_fn]
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  cases t.fn τ with
  | none => simp
  | some a => cases a <;> cases s <;> simp [Sym.flip]

/-- Leaf duality exchanges top and bottom prefixes. -/
@[simp] theorem covPrefTop_dual (w : List (Fin n)) (t : Tree n) :
    covPrefTop w (Tree.dual t) ↔ covPrefBot w t := hasLabel_dual t w Sym.top

@[simp] theorem covPrefBot_dual (w : List (Fin n)) (t : Tree n) :
    covPrefBot w (Tree.dual t) ↔ covPrefTop w t := hasLabel_dual t w Sym.bot

/-- The covariant safety equivalence is the negation of the existing unsafety theorem. -/
theorem cov_le_iff_safe (t u : Tree n) :
    t ≤ u ↔ ∀ π, (covPrefTop π t → covPrefTop π u) ∧
      (covPrefBot π u → covPrefBot π t) := by
  have h := Safety.not_le_iff_unsafe t u
  simp only [ne_eq, Safety.trace_eq_bot_iff, Safety.trace_eq_top_iff] at h
  classical
  simp only [covPrefTop, covPrefBot]
  constructor
  · intro hle π
    constructor
    · intro ht
      by_contra hu
      exact (h.mpr ⟨π, Or.inr ⟨ht, hu⟩⟩) hle
    · intro hu
      by_contra ht
      exact (h.mpr ⟨π, Or.inl ⟨ht, hu⟩⟩) hle
  · intro hs
    by_contra hn
    obtain ⟨π, ⟨ht, hu⟩ | ⟨ht, hu⟩⟩ := h.mp hn
    · exact ht ((hs π).2 hu)
    · exact hu ((hs π).1 ht)

end DeciNSSE

end

section

namespace DeciNSSE
variable {n : ℕ}

/-- A prefix reaches top after variance normalisation. -/
def prefTop (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) : Prop :=
  ∃ ρ, ρ.IsPrefix π ∧ t.fn ρ = some (Sym.flip (polarity c ρ) Sym.top)

/-- A prefix reaches bottom after variance normalisation. -/
def prefBot (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) : Prop :=
  ∃ ρ, ρ.IsPrefix π ∧ t.fn ρ = some (Sym.flip (polarity c ρ) Sym.bot)

theorem normalize_label (c : Fin n → Bool) (t : Tree n) (π : List (Fin n)) (s : Sym) :
    (Tree.normalize c false t).fn π = some s ↔ t.fn π = some (Sym.flip (polarity c π) s) := by
  cases hp : polarity c π <;> cases ht : t.fn π with
  | none => simp [ht, hp]
  | some a => cases a <;> cases s <;> simp [ht, hp, Sym.flip]

theorem prefTop_iff_normalize (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) :
    prefTop c π t ↔ covPrefTop π (Tree.normalize c false t) := by
  simp only [prefTop, covPrefTop, Safety.HasLabel, normalize_label]

theorem prefBot_iff_normalize (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) :
    prefBot c π t ↔ covPrefBot π (Tree.normalize c false t) := by
  simp only [prefBot, covPrefBot, Safety.HasLabel, normalize_label]

/-- Variance order is equivalent to preservation of extreme prefixes. -/
theorem treeLe_iff_safe (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ ∀ π, (prefTop c π t → prefTop c π u) ∧
      (prefBot c π u → prefBot c π t) := by
  simp only [treeLe_iff_normalize, cov_le_iff_safe, prefTop_iff_normalize, prefBot_iff_normalize]

end DeciNSSE

end
