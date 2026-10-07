import DeciNSSE.Semantics.RegularOps

/-! # Regular satisfiability with variance

The median of a signed solution, its sign dual and the full constructor tree
is a solution fixed by sign duality. A top of the positive coordinate and a
bottom of the negative coordinate on a prefix survive this symmetrisation.
Regular signed solutions remain regular under symmetrisation and decoding.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- Constructor literals use three solutions; constants use the two equal leaves. -/
theorem sat_median_full {A B : V k → Tree n} {ϕ : Constraint n k}
    (ha : Covariant.Sat A ϕ) (hb : Covariant.Sat B ϕ) : Covariant.Sat (fun z => Tree.median (A z) (B z) Tree.full) ϕ := by
  intro l hl
  have h₁ := ha l hl
  have h₂ := hb l hl
  cases l with
  | leF u a =>
    have h := median_mono h₁ h₂ full_bounds.1
    rw [median_node] at h
    exact h
  | fLe a u =>
    have h := median_mono h₁ h₂ full_bounds.2
    rw [median_node] at h
    exact h
  | eqBot u =>
    change A u = Tree.bot at h₁
    change B u = Tree.bot at h₂
    change Tree.median (A u) (B u) Tree.full = Tree.bot
    simp [h₁, h₂]
  | eqTop u =>
    change A u = Tree.top at h₁
    change B u = Tree.top at h₂
    change Tree.median (A u) (B u) Tree.full = Tree.top
    simp [h₁, h₂]

/-- Median of a signed assignment, its sign-dual, and the all-constructor tree. -/
noncomputable def Signed.symmetrize (A : V (2 * k) → Tree n) (z : V (2 * k)) : Tree n :=
  Tree.median (A z) (Signed.dual A z) Tree.full

/-- Median symmetrisation preserves the signed constraints. -/
theorem symmetrize_sat (c : Fin n → Bool) {A : V (2 * k) → Tree n}
    {ϕ : Constraint n k} (h : Covariant.Sat A (signed c ϕ)) :
    Covariant.Sat (Signed.symmetrize A) (signed c ϕ) :=
  sat_median_full h (sat_signedDual c h)

/-- Median symmetrisation produces an assignment fixed by sign duality. -/
@[simp] theorem symmetrize_fixed (A : V (2 * k) → Tree n) :
    Signed.dual (Signed.symmetrize A) = Signed.symmetrize A := by
  funext z
  obtain ⟨u, p, rfl⟩ := sv_cases z
  simp only [signedDual_sv, Signed.symmetrize, dual_median, dual_full, Bool.not_not, dual_involutive]
  exact median_swap _ _ _

@[simp] theorem trace_median_full_top (a b : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.median a b Tree.full) w = .top ↔ Tree.trace a w = .top ∧ Tree.trace b w = .top := by
  simp only [trace_median, trace_full]
  cases Tree.trace a w <;> cases Tree.trace b w <;> decide

@[simp] theorem trace_median_full_bot (a b : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.median a b Tree.full) w = .bot ↔ Tree.trace a w = .bot ∧ Tree.trace b w = .bot := by
  simp only [trace_median, trace_full]
  cases Tree.trace a w <;> cases Tree.trace b w <;> decide

theorem symmetrize_prefTop (A : V (2 * k) → Tree n) (u : V k) (w : List (Fin n)) :
    covPrefTop w (Signed.symmetrize A (sv u false)) ↔
      covPrefTop w (A (sv u false)) ∧ covPrefBot w (A (sv u true)) := by
  rw [covPrefTop_iff_trace, Signed.symmetrize, trace_median_full_top]
  simp only [signedDual_sv, Bool.not_false, ← covPrefTop_iff_trace, covPrefTop_dual]

theorem symmetrize_prefBot (A : V (2 * k) → Tree n) (u : V k) (w : List (Fin n)) :
    covPrefBot w (Signed.symmetrize A (sv u false)) ↔
      covPrefBot w (A (sv u false)) ∧ covPrefTop w (A (sv u true)) := by
  rw [covPrefBot_iff_trace, Signed.symmetrize, trace_median_full_bot]
  simp only [signedDual_sv, Bool.not_false, ← covPrefBot_iff_trace, covPrefBot_dual]


namespace RegularVariance

/-- Median of a graph, the leaf swap of its sign-dual, and the all-constructor graph. -/
def symmetrizeGraph (σ : V (2 * k) → RGraph n) (z : V (2 * k)) : RGraph n :=
  medianGraph (σ z) (dualGraph (σ (sv (base z) (!(sign z))))) (RGraph.allF n)

/-- Graph symmetrisation unfolds to median symmetrisation of the represented assignment. -/
theorem unfold_symmetrizeGraph (σ : V (2 * k) → RGraph n) :
    RGraph.unfold ∘ symmetrizeGraph σ = Signed.symmetrize (RGraph.unfold ∘ σ) := by
  funext z
  simp only [Function.comp_apply, symmetrizeGraph, unfold_medianGraph, unfold_dualGraph, unfold_allF,
    Signed.symmetrize, Signed.dual]

/-- Decode the positive block of the symmetrized graph assignment. -/
def decodeGraph (c : Fin n → Bool) (σ : V (2 * k) → RGraph n) (u : V k) : RGraph n :=
  normalizeGraph c false (symmetrizeGraph σ (sv u false))

/-- Graph decoding unfolds to symmetrisation followed by decoding of the signed assignment. -/
theorem unfold_decodeGraph (c : Fin n → Bool) (σ : V (2 * k) → RGraph n) :
    RGraph.unfold ∘ decodeGraph c σ = decoded c (Signed.symmetrize (RGraph.unfold ∘ σ)) := by
  funext u
  simp only [Function.comp_apply, decodeGraph, unfold_normalizeGraph, decoded]
  rw [← Function.comp_apply (f := RGraph.unfold) (g := symmetrizeGraph σ), unfold_symmetrizeGraph]

end RegularVariance

open RegularVariance

/-- Decoding the regular symmetrization gives a regular source solution. -/
theorem sat_decodeGraph (c : Fin n → Bool) {ϕ : Constraint n k}
    {σ : V (2 * k) → RGraph n} (h : Covariant.Sat (RGraph.unfold ∘ σ) (signed c ϕ)) :
    Sat c (RGraph.unfold ∘ decodeGraph c σ) ϕ := by
  rw [unfold_decodeGraph, sat_iff_signed,
    normalized_decoded c (symmetrize_fixed (RGraph.unfold ∘ σ))]
  exact symmetrize_sat c h

end DeciNSSE
