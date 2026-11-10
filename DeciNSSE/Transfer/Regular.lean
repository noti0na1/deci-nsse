import DeciNSSE.Monitor.Semantics
import DeciNSSE.Satisfiability.ShapeGraph

/-! # Regular countermodel transfer

An unsafe word of a side leaves the four-spine extension of that side without
label clash. The variance shape of the variance extension is then a solution,
presented by a finite graph; restricted to the old variables it is a regular
countermodel that fails the query at the same word. Regular entailment therefore
coincides with unrestricted entailment.

## Main declarations

- `RegularTransfer.countermodel`, `RegularTransfer.countermodel_spec`,
  `RegularTransfer.countermodel_not_le`: the regular countermodel of a side and a word; when
  the word is unsafe it solves the system and fails the query at that word.
- `explicit_countermodel`, `regular_countermodel`, `entailsReg_iff_entails`: every
  failure of entailment has a regular countermodel.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace RegularTransfer

open Spine.Closure Events SignDuality

/-- The regular countermodel at the word `w` on side `θ`: the variance graphs of the
variance extension of the query of that side, read at the old variables. -/
def countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)
    (w : List (Fin n)) (z : V k) : RGraph n :=
  varianceGraph c (shapeGraph (Spine.extension c ϕ (sideQuery x y θ).1 (sideQuery x y θ).2 w))
    (Fin.castAdd _ z)

/-- The regular countermodel unfolds to the variance shape of the variance extension. -/
theorem unfold_countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)
    (w : List (Fin n)) :
    RGraph.unfold ∘ countermodel c ϕ x y θ w = varianceShape c
      (Spine.varianceExtension c ϕ (sideQuery x y θ).1 (sideQuery x y θ).2 w) ∘
        Fin.castAdd _ :=
  funext fun z => unfold_varianceGraph c (unfold_shapeGraph _) (Fin.castAdd _ z)

/-- A top-prefix witness of the query of a side fails the query at `w`: there `w` reaches a
polarized top in `x` but not in `y`, or a polarized bottom in `y` but not in `x`. -/
theorem not_safeAt_of_witness {c : Fin n → Bool} {x y : V k} {θ : Side} {w : List (Fin n)}
    {ρ : V k → Tree n} (hx : covPrefTop w (normalized c ρ (sideQuery x y θ).1))
    (hy : ¬ covPrefTop w (normalized c ρ (sideQuery x y θ).2)) :
    ¬ ((prefTop c w (ρ x) → prefTop c w (ρ y)) ∧ (prefBot c w (ρ y) → prefBot c w (ρ x))) := by
  intro h
  cases θ <;> simp only [sideQuery, normalized_sv, normalize_true, covPrefTop_dual,
    ← prefTop_iff_normalize, ← prefBot_iff_normalize] at hx hy
  · exact hy (h.1 hx)
  · exact hy (h.2 hx)

/-- A top-prefix witness of the query of a side fails the query. -/
theorem not_le_of_witness {c : Fin n → Bool} {x y : V k} {θ : Side} {w : List (Fin n)}
    {ρ : V k → Tree n} (hx : covPrefTop w (normalized c ρ (sideQuery x y θ).1))
    (hy : ¬ covPrefTop w (normalized c ρ (sideQuery x y θ).2)) : ¬ Tree.Le c (ρ x) (ρ y) :=
  fun hle => not_safeAt_of_witness hx hy ((treeLe_iff_safe c _ _).mp hle w)

/-- If `w` is unsafe on side `θ`, the regular assignment `countermodel c ϕ x y θ w`
solves the system and fails the query at `w`: there `w` reaches a polarized top in `x`
but not in `y`, or a polarized bottom in `y` but not in `x`. -/
theorem countermodel_spec {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k} {θ : Side}
    {w : List (Fin n)} (hu : Unsafe c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ countermodel c ϕ x y θ w) ϕ ∧
      ¬ ((prefTop c w (countermodel c ϕ x y θ w x).unfold →
          prefTop c w (countermodel c ϕ x y θ w y).unfold) ∧
        (prefBot c w (countermodel c ϕ x y θ w y).unfold →
          prefBot c w (countermodel c ϕ x y θ w x).unfold)) := by
  obtain ⟨hs, hx, hy⟩ := witness_of_sat
    (varianceShape_sat ((sideUnsafe_iff_not_labelClash θ w).mp hu))
  rw [← unfold_countermodel] at hs hx hy
  exact ⟨hs, not_safeAt_of_witness hx hy⟩

/-- If `w` is unsafe on side `θ`, the regular assignment `countermodel c ϕ x y θ w`
solves the system and fails the query. -/
theorem countermodel_not_le {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k} {θ : Side}
    {w : List (Fin n)} (hu : Unsafe c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ countermodel c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (countermodel c ϕ x y θ w x).unfold (countermodel c ϕ x y θ w y).unfold :=
  ⟨(countermodel_spec hu).1,
    fun hle => (countermodel_spec hu).2 ((treeLe_iff_safe c _ _).mp hle w)⟩

end RegularTransfer

open RegularTransfer

/-- The countermodel can be taken from the explicit regular family `countermodel`,
indexed by a side and an unsafe word. -/
theorem explicit_countermodel (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    (hn : ¬ Entails c ϕ x y) :
    ∃ θ w, Sat c (RGraph.unfold ∘ countermodel c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (countermodel c ϕ x y θ w x).unfold (countermodel c ϕ x y θ w y).unfold := by
  simp only [entails_iff_not_sideUnsafe, not_forall, not_not] at hn
  obtain ⟨θ, w, hu⟩ := hn
  exact ⟨θ, w, countermodel_not_le hu⟩

/-- Every non-entailment, at any arity and variance, has a regular countermodel. -/
theorem regular_countermodel (c : Fin n → Bool) {ϕ : Constraint n k} {x y : V k}
    (hn : ¬ Entails c ϕ x y) :
    ∃ σ : V k → RGraph n, Sat c (RGraph.unfold ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).unfold (σ y).unfold := by
  obtain ⟨θ, w, h⟩ := explicit_countermodel c hn
  exact ⟨_, h⟩

/-- Regular entailment equals entailment over all trees, for any arity and variance. -/
theorem entailsReg_iff_entails (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    EntailsReg c ϕ x y ↔ Entails c ϕ x y := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨σ, hσ, hle⟩ := regular_countermodel c hn
    exact hle (h σ hσ)
  · intro h σ hσ
    exact h _ hσ

end DeciNSSE
