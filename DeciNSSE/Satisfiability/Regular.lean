import DeciNSSE.Semantics.RegularOps
import DeciNSSE.Transfer.ThreeSpine

/-! # Regular satisfiability with variance

Regular signed solutions remain regular under median symmetrisation and
decoding. Every satisfiable variance system has a regular solution.
-/

namespace DeciNSSE

variable {n k : ℕ}

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
