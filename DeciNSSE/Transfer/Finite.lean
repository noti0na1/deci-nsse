import DeciNSSE.Satisfiability.Variance
import DeciNSSE.Transfer.Cycle
import DeciNSSE.Transfer.Regular

/-! # Finite countermodel transfer

When a system has a finite solution, every countermodel can be replaced by a
finite one. A finite solution excludes cycle clashes in the signed translation,
and the ranked four-spine extension adds none. The least shapes of the extension
therefore have bounded depth, and so does the variance shape. The regular
countermodel of an unsafe word thus has bounded depth, and its truncation at the
depth bound is a finite countermodel.

## Main declarations

- `FiniteTransfer.countermodel`, `FiniteTransfer.countermodel_toTree`,
  `FiniteTransfer.countermodel_spec`: the truncated regular countermodel, equal to the
  regular one under finite satisfiability, and a countermodel at an unsafe word.
- `finite_countermodel_transfer`, `entailsFin_iff`: finite entailment is finite vacuity
  or unrestricted entailment.
-/

namespace DeciNSSE

namespace FiniteTransfer

open Spine.Closure Events SignDuality

variable {n k : ℕ} {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k} {θ : Side}
  {w : List (Fin n)}

/-- Under finite satisfiability, the regular countermodel has bounded depth. -/
theorem countermodel_depth (hs : SatisfiableFin c ϕ) (z : V k) (π : List (Fin n))
    (hπ : ((RegularTransfer.countermodel c ϕ x y θ w z).unfold.fn π).isSome) :
    π.length ≤ (2 * (k + (2 * w.length + 2))) ^ 2 + 1 := by
  have hcy : ¬ CycleClash (Spine.extension c ϕ (sideQuery x y θ).1 (sideQuery x y θ).2 w) :=
    fun h => (satFin_iff.mp ((satFin_iff_signed c ϕ).mp hs)).2
      ((extension_ranked c _ _ w ϕ).cycleClash_iff.mp h)
  rw [show (RegularTransfer.countermodel c ϕ x y θ w z).unfold = _ from
    congrFun (RegularTransfer.unfold_countermodel c ϕ x y θ w) z] at hπ
  simpa only [Nat.pow_two] using varianceShape_depth (leastShape_depth hcy) _ π hπ

/-- The finite countermodel at the word `w` on side `θ`: the regular countermodel,
truncated at the depth bound of its four-spine extension. -/
def countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)
    (w : List (Fin n)) (z : V k) : FTree n :=
  FTree.ofTree ((2 * (k + (2 * w.length + 2))) ^ 2 + 1)
    (RegularTransfer.countermodel c ϕ x y θ w z).unfold

/-- Under finite satisfiability, truncation preserves the regular countermodel. -/
theorem countermodel_toTree (hs : SatisfiableFin c ϕ) (z : V k) :
    (countermodel c ϕ x y θ w z).toTree =
      (RegularTransfer.countermodel c ϕ x y θ w z).unfold :=
  FTree.toTree_ofTree (countermodel_depth hs z)

/-- On a finitely satisfiable system, the finite assignment `countermodel c ϕ x y θ w`
of an unsafe word solves the system and fails the query. -/
theorem countermodel_spec (hs : SatisfiableFin c ϕ) (hu : Unsafe c ϕ x y θ w) :
    Sat c (FTree.toTree ∘ countermodel c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (countermodel c ϕ x y θ w x).toTree (countermodel c ϕ x y θ w y).toTree := by
  have he (z : V k) := countermodel_toTree (x := x) (y := y) (θ := θ) (w := w) hs z
  obtain ⟨hsol, hbad⟩ := RegularTransfer.countermodel_not_le hu
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, he] using hsol
  · rwa [he, he]

end FiniteTransfer

open FiniteTransfer

/-- Finite countermodel transfer, for every arity and every variance: when the
system has a finite model, every countermodel can be replaced by a finite one. -/
theorem finite_countermodel_transfer {n k : ℕ} (c : Fin n → Bool)
    {ϕ : Constraint n k} {x y : V k}
    (hs : SatisfiableFin c ϕ)
    (hn : ¬ Entails c ϕ x y) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).toTree (σ y).toTree := by
  obtain ⟨θ, w, hu⟩ : ∃ θ w, Unsafe c ϕ x y θ w := by
    simpa only [entails_iff_not_sideUnsafe, not_forall, not_not] using hn
  exact ⟨_, FiniteTransfer.countermodel_spec hs hu⟩

/-- Finite entailment is finite vacuity or unrestricted entailment, for every arity
and every variance. -/
theorem entailsFin_iff {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    EntailsFin c ϕ x y ↔
      ¬ SatisfiableFin c ϕ ∨ Entails c ϕ x y := by
  classical
  constructor
  · intro he
    by_cases hs : ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ
    · right
      by_contra hn
      obtain ⟨σ, hσ, hxy⟩ := finite_countermodel_transfer c hs hn
      exact hxy (he σ hσ)
    · exact Or.inl hs
  · rintro (hs | he)
    · exact fun σ hσ => absurd ⟨σ, hσ⟩ hs
    · exact fun σ hσ => he (FTree.toTree ∘ σ) hσ

end DeciNSSE
