import DeciNSSE.Monitor.Semantics
import DeciNSSE.Satisfiability.ShapeGraph

/-! # Regular countermodel transfer

An unsafe word of a side leaves the four-spine extension of that side without
label clash. The selected least shape of the extension is then a solution fixed
by sign duality, presented by a finite graph; restricted to the old variables
it is a sign-fixed witness of the side. Decoding the witness gives a regular
countermodel at the same word. On the bottom-prefix side the witness belongs to
the order dual, so the decoding reads its negative coordinates. Regular
entailment therefore coincides with unrestricted entailment.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace RegularTransfer

open Spine.Closure Events FiniteVariance

/-- The witness graphs of the four-spine extension: its selected least shape,
presented by a finite graph and read at the old variables. -/
def witnessGraph (c : Fin n → Bool) (ψ : Constraint n (2 * k)) (X Y : V (2 * k))
    (w : List (Fin n)) (z : V (2 * k)) : RGraph n :=
  selectGraph c (shapeGraph (Spine.extension c ψ X Y w)) (lift z)

/-- Without a label clash in the four-spine extension of a flip-closed, sign-coherent
system, the witness graphs present a sign-fixed solution with a top of `X` and no top
of `Y` on the prefixes of `w`. -/
theorem witnessGraph_spec {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)}
    {w : List (Fin n)} (hf : FlipClosed ψ) (hc : SignCoherent c ψ)
    (hn : ¬ LabelClash (Spine.extension c ψ X Y w)) :
    Covariant.Sat (RGraph.unfold ∘ witnessGraph c ψ X Y w) ψ ∧
      Signed.dual (RGraph.unfold ∘ witnessGraph c ψ X Y w) =
        RGraph.unfold ∘ witnessGraph c ψ X Y w ∧
      covPrefTop w (witnessGraph c ψ X Y w X).unfold ∧
      ¬ covPrefTop w (witnessGraph c ψ X Y w Y).unfold := by
  obtain ⟨hs, hfix⟩ :=
    regular_fixed_solution c (extension_flipClosed hf) (extension_signCoherent hc) hn
  exact witness_of_sat hs hfix

/-- The decoded graphs meet a polarized top exactly where the positive coordinate meets
a top. -/
theorem prefTop_decodedGraph (c : Fin n → Bool) (g : V (2 * k) → RGraph n) (u : V k)
    (w : List (Fin n)) :
    prefTop c w (decodedGraph c g u).unfold ↔ covPrefTop w (g (sv u false)).unfold := by
  rw [prefTop_iff_normalize, decodedGraph, RGraph.unfold_normalize, normalize_involutive]

/-- The decoded graphs meet a polarized bottom exactly where the positive coordinate
meets a bottom. -/
theorem prefBot_decodedGraph (c : Fin n → Bool) (g : V (2 * k) → RGraph n) (u : V k)
    (w : List (Fin n)) :
    prefBot c w (decodedGraph c g u).unfold ↔ covPrefBot w (g (sv u false)).unfold := by
  rw [prefBot_iff_normalize, decodedGraph, RGraph.unfold_normalize, normalize_involutive]

/-- The regular countermodel at the word `w` on side `θ`: the decoded witness graphs of
the side. On the bottom-prefix side the witness solves the order dual, and its negative
coordinates are decoded. -/
def countermodel (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Side → List (Fin n) → V k → RGraph n
  | .l, w => decodedGraph c (witnessGraph c (signed c ϕ) (sv x false) (sv y false) w)
  | .r, w => decodedGraph c
      (witnessGraph c (Constraint.dual (signed c ϕ)) (sv y false) (sv x false) w ∘ flipV)

/-- If `w` is unsafe on side `θ`, the regular assignment `countermodel c ϕ x y θ w` is a
countermodel. -/
theorem countermodel_spec {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k} {θ : Side}
    {w : List (Fin n)} (hu : Unsafe c ϕ x y θ w) :
    Sat c (RGraph.unfold ∘ countermodel c ϕ x y θ w) ϕ ∧
      ¬ Tree.Le c (countermodel c ϕ x y θ w x).unfold (countermodel c ϕ x y θ w y).unfold := by
  obtain ⟨hs, hfix, hX, hY⟩ := witnessGraph_spec (sideSystem_flipClosed θ)
    (sideSystem_signCoherent θ) ((sideUnsafe_iff_not_labelClash θ w).mp hu)
  cases θ <;> simp only [sideSystem, sideQuery] at hs hfix hX hY
  · refine ⟨sat_decodedGraph c hs hfix, fun hle => hY ?_⟩
    exact (prefTop_decodedGraph c _ y w).mp
      (((treeLe_iff_safe c _ _).mp hle w).1 ((prefTop_decodedGraph c _ x w).mpr hX))
  · set g := witnessGraph c (Constraint.dual (signed c ϕ)) (sv y false) (sv x false) w
    have hd : RGraph.unfold ∘ (g ∘ flipV) = Tree.dual ∘ (RGraph.unfold ∘ g) :=
      funext fun z => fixed_flipV hfix z
    have hfix' : Signed.dual (RGraph.unfold ∘ (g ∘ flipV)) = RGraph.unfold ∘ (g ∘ flipV) := by
      rw [hd]
      change Tree.dual ∘ Signed.dual (RGraph.unfold ∘ g) = _
      rw [hfix]
    have hbot (u : V k) : prefBot c w (decodedGraph c (g ∘ flipV) u).unfold ↔
        covPrefTop w (g (sv u false)).unfold := by
      rw [prefBot_decodedGraph, ← Function.comp_apply (f := RGraph.unfold), hd,
        Function.comp_apply, covPrefBot_dual]
      rfl
    refine ⟨sat_decodedGraph c (hd ▸ ConstraintDual.sat_of_dual hs) hfix', fun hle => hY ?_⟩
    exact (hbot x).mp (((treeLe_iff_safe c _ _).mp hle w).2 ((hbot y).mpr hX))

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
  exact ⟨θ, w, countermodel_spec hu⟩

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
