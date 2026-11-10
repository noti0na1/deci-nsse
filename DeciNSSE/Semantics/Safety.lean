import DeciNSSE.Semantics.Order

/-! # Finite witnesses to order failure

A trace continues an extreme leaf label along every longer path. Order is
equivalent to preservation of top and bottom prefixes, so every failure has
a finite path witness.

## Main declarations
- `Safety.descend`, `Safety.trace`, with `Safety.trace_append`, `Safety.trace_snoc` and
  `Safety.trace_mono`
- `Safety.descend_eq_bot_of_le`, `Safety.ne_top_of_le_node`, `Safety.ne_bot_of_node_le`:
  traces below and above constructors
- `Safety.trace_eq_bot_iff`, `Safety.trace_eq_top_iff`: a trace is an extreme leaf
  exactly when a prefix of the path carries its label
- `covPrefTop`, `covPrefBot`: top and bottom prefixes of a covariant tree, as traces
- `Safety.not_le_iff_unsafe`: an order failure is a path witness
- `prefTop`, `prefBot`, `treeLe_iff_safe`, and the covariant forms `prefTop_false_iff`
  and `prefBot_false_iff`
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

/-- Extending a path by one direction descends once more. -/
theorem trace_snoc (t : Tree n) (ν : List (Fin n)) (i : Fin n) :
    trace t (ν ++ [i]) = descend (trace t ν) i := by
  rw [trace_append]; rfl

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

/-- Below a node, a direction whose child is bottom leads to bottom. -/
theorem descend_eq_bot_of_le {t : Tree n} {a : Fin n → Tree n} (h : t ≤ Tree.node a)
    {i : Fin n} (hi : a i = Tree.bot) : descend t i = Tree.bot := by
  have := descend_mono h i
  rwa [descend_node, hi, Tree.le_bot_iff] at this

/-- A tree below a node is not top. -/
theorem ne_top_of_le_node {t : Tree n} {a : Fin n → Tree n} (h : t ≤ Tree.node a) :
    t ≠ Tree.top := by
  rintro rfl; exact Tree.node_ne_top a ((Tree.top_le_iff _).mp h)

/-- A tree above a node is not bottom. -/
theorem ne_bot_of_node_le {t : Tree n} {a : Fin n → Tree n} (h : Tree.node a ≤ t) :
    t ≠ Tree.bot := by
  rintro rfl; exact Tree.node_ne_bot a ((Tree.le_bot_iff _).mp h)

/-- A trace has an extreme root label exactly when a prefix of the path carries it. -/
theorem trace_root_iff (t : Tree n) (ν : List (Fin n)) {s : Sym} (hs : s ≠ Sym.f) :
    (trace t ν).fn [] = some s ↔ ∃ τ, τ <+: ν ∧ t.fn τ = some s := by
  induction ν generalizing t with
  | nil => simp
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · refine ⟨fun h => ⟨[], List.nil_prefix, by simpa using h⟩, ?_⟩
      rintro ⟨τ, _, h⟩
      cases τ with
      | nil => simpa using h
      | cons => simp at h
    · refine ⟨fun h => ⟨[], List.nil_prefix, by simpa using h⟩, ?_⟩
      rintro ⟨τ, _, h⟩
      cases τ with
      | nil => simpa using h
      | cons => simp at h
    · rw [trace_cons, descend_node, ih]
      constructor
      · rintro ⟨v, ⟨z, he⟩, h⟩
        exact ⟨i :: v, ⟨z, by simp [he]⟩, h⟩
      · rintro ⟨v, hp, h⟩
        cases v with
        | nil => exact absurd (Option.some.inj h).symm hs
        | cons j v =>
          obtain ⟨z, he⟩ := hp
          obtain rfl : j = i := (List.cons.inj he).1
          exact ⟨v, ⟨z, (List.cons.inj he).2⟩, h⟩

/-- A trace is bottom exactly when a prefix of the path carries bottom. -/
theorem trace_eq_bot_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.bot ↔ ∃ τ, τ <+: ν ∧ t.fn τ = some Sym.bot := by
  rw [← Tree.root_eq_bot_iff, trace_root_iff _ _ (by decide)]

/-- A trace is top exactly when a prefix of the path carries top. -/
theorem trace_eq_top_iff (t : Tree n) (ν : List (Fin n)) :
    trace t ν = Tree.top ↔ ∃ τ, τ <+: ν ∧ t.fn τ = some Sym.top := by
  rw [← Tree.root_eq_top_iff, trace_root_iff _ _ (by decide)]

/-- Proper prefixes of an existing path cannot carry a nullary symbol. -/
theorem not_prefix_label {t : Tree n} {ν : List (Fin n)} {a s : Sym}
    (h : t.fn ν = some a) (hs : s ≠ Sym.f) (ha : a ≠ s) :
    ¬ ∃ τ, τ <+: ν ∧ t.fn τ = some s := by
  rintro ⟨τ, hp, ht⟩
  by_cases he : τ = ν
  · subst τ; exact ha (Option.some.inj (h.symm.trans ht))
  · have hf := t.label_eq_f_of_proper_prefix hp he (by simp [h])
    exact hs (Option.some.inj (ht.symm.trans hf))

/-- Leaf duality commutes with traces. -/
theorem trace_dual (t : Tree n) (ν : List (Fin n)) :
    trace (Tree.dual t) ν = Tree.dual (trace t ν) := by
  induction ν generalizing t with
  | nil => rfl
  | cons i ν ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · rw [dual_node, trace_cons, trace_cons, descend_node, descend_node, ih]

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
    · exact Or.inl ⟨fun h => not_prefix_label ht (by decide) ha
        ((trace_eq_bot_iff _ _).mp h),
        (trace_eq_bot_iff _ _).mpr ⟨ν, List.prefix_refl _, hu⟩⟩
    · exact Or.inr ⟨(trace_eq_top_iff _ _).mpr ⟨ν, List.prefix_refl _, ht⟩,
        fun h => not_prefix_label hu (by decide) hb ((trace_eq_top_iff _ _).mp h)⟩
  · rintro ⟨ν, h⟩ hle
    have hm := trace_mono hle ν
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hy] at hm; exact hx ((Tree.le_bot_iff _).mp hm)
    · rw [hx] at hm; exact hy ((Tree.top_le_iff _).mp hm)

end Safety

/-- A prefix of the word reaches top in the covariant tree: the trace along the word
is top. -/
abbrev covPrefTop (w : List (Fin n)) (t : Tree n) : Prop := Safety.trace t w = Tree.top
/-- A prefix of the word reaches bottom in the covariant tree: the trace along the word
is bottom. -/
abbrev covPrefBot (w : List (Fin n)) (t : Tree n) : Prop := Safety.trace t w = Tree.bot

/-- Leaf duality exchanges top and bottom prefixes. -/
@[simp] theorem covPrefTop_dual (w : List (Fin n)) (t : Tree n) :
    covPrefTop w (Tree.dual t) ↔ covPrefBot w t := by
  rw [covPrefTop, Safety.trace_dual, dual_eq_top]

@[simp] theorem covPrefBot_dual (w : List (Fin n)) (t : Tree n) :
    covPrefBot w (Tree.dual t) ↔ covPrefTop w t := by
  rw [covPrefBot, Safety.trace_dual, dual_eq_bot]

/-- The covariant safety equivalence is the negation of the existing unsafety theorem. -/
theorem cov_le_iff_safe (t u : Tree n) :
    t ≤ u ↔ ∀ π, (covPrefTop π t → covPrefTop π u) ∧
      (covPrefBot π u → covPrefBot π t) := by
  have h := Safety.not_le_iff_unsafe t u
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

/-- A prefix reaches top after variance normalization. -/
def prefTop (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) : Prop :=
  ∃ ρ, ρ.IsPrefix π ∧ t.fn ρ = some (Sym.flip (polarity c ρ) Sym.top)

/-- A prefix reaches bottom after variance normalization. -/
def prefBot (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) : Prop :=
  ∃ ρ, ρ.IsPrefix π ∧ t.fn ρ = some (Sym.flip (polarity c ρ) Sym.bot)

theorem normalize_label (c : Fin n → Bool) (t : Tree n) (π : List (Fin n)) (s : Sym) :
    (Tree.normalize c false t).fn π = some s ↔ t.fn π = some (Sym.flip (polarity c π) s) := by
  cases hp : polarity c π <;> cases ht : t.fn π with
  | none => simp [ht, hp]
  | some a => cases a <;> cases s <;> simp [ht, hp, Sym.flip]

theorem prefTop_iff_normalize (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) :
    prefTop c π t ↔ covPrefTop π (Tree.normalize c false t) := by
  simp only [prefTop, covPrefTop, Safety.trace_eq_top_iff, normalize_label]

theorem prefBot_iff_normalize (c : Fin n → Bool) (π : List (Fin n)) (t : Tree n) :
    prefBot c π t ↔ covPrefBot π (Tree.normalize c false t) := by
  simp only [prefBot, covPrefBot, Safety.trace_eq_bot_iff, normalize_label]

/-- Covariant top prefixes are top traces. -/
theorem prefTop_false_iff (π : List (Fin n)) (t : Tree n) :
    prefTop (fun _ => false) π t ↔ Safety.trace t π = Tree.top := by
  rw [Safety.trace_eq_top_iff]
  simp only [prefTop, polarity_false, Sym.flip_false]

/-- Covariant bottom prefixes are bottom traces. -/
theorem prefBot_false_iff (π : List (Fin n)) (t : Tree n) :
    prefBot (fun _ => false) π t ↔ Safety.trace t π = Tree.bot := by
  rw [Safety.trace_eq_bot_iff]
  simp only [prefBot, polarity_false, Sym.flip_false]

/-- Variance order is equivalent to preservation of extreme prefixes. -/
theorem treeLe_iff_safe (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ ∀ π, (prefTop c π t → prefTop c π u) ∧
      (prefBot c π u → prefBot c π t) := by
  simp only [treeLe_iff_normalize, cov_le_iff_safe, prefTop_iff_normalize, prefBot_iff_normalize]

end DeciNSSE

end
