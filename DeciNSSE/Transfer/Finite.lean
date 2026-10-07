import DeciNSSE.Monitor.Semantics
import DeciNSSE.Satisfiability.FiniteVariance
import DeciNSSE.Transfer.Cycle

/-! # Finite countermodel transfer

When a system has a finite solution, every countermodel can be replaced by a
finite one. A countermodel has an unsafe word on one side, so the four-spine
extension of that side has no label clash. The finite solution excludes cycle
clashes in the side system, and the ranked spine extension adds none. The least
shape of the extension therefore has bounded depth, selection keeps its domain,
and its restriction to the old variables is a finite sign-fixed witness of the
unsafe word. Decoding this witness gives a finite countermodel.
-/

namespace DeciNSSE

namespace FiniteTransfer

open Spine.Closure Events FiniteVariance

variable {n k : ℕ}

section Witness

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

/-- Without a cycle clash in `ψ`, a four-spine extension without label clash has
a finite sign-fixed witness: the selected least shape of the extension,
restricted to the old variables. -/
theorem finite_fixedWitness (hf : FlipClosed ψ) (hc : SignCoherent c ψ)
    (hl : ¬ LabelClash (Spine.extension c ψ X Y w)) (hcy : ¬ CycleClash ψ) :
    ∃ B : V (2 * k) → FTree n, Covariant.Sat (FTree.toTree ∘ B) ψ ∧
      Signed.dual (FTree.toTree ∘ B) = FTree.toTree ∘ B ∧
        covPrefTop w (B X).toTree ∧ ¬ covPrefTop w (B Y).toTree := by
  have hf' : FlipClosed (Spine.extension c ψ X Y w) := extension_flipClosed hf
  have hB := leastShape_sat hl
  have hM := select_sat_of_coherent (extension_signCoherent hc) hB
    (sat_signedDual_of_flipClosed hf' hB) (leastShape_sameShape_dual hf')
  have hcy' : ¬ CycleClash (Spine.extension c ψ X Y w) :=
    fun h => hcy ((extension_ranked c X Y w ψ).cycleClash_iff.mp h)
  obtain ⟨hA, hfix, hx, hy⟩ := witness_of_sat hM (select_fixed _ _ _)
  obtain ⟨B, he⟩ := FTree.exists_eq_of_depth
    (ρ := select c (leastShape (Spine.extension c ψ X Y w)) (leastShape_sameShape_dual hf') ∘ lift)
    fun z π hπ => select_depth c _ _ (leastShape_depth hcy') (lift z) π hπ
  have he' (z : V (2 * k)) : (B z).toTree = _ := congrFun he z
  exact ⟨B, he ▸ hA, he ▸ hfix, he' X ▸ hx, he' Y ▸ hy⟩

end Witness

section Sides

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- A finite solution leaves no cycle clash on either side. -/
theorem sideSystem_not_cycleClash (hs : SatisfiableFin c ϕ) (θ : Side) :
    ¬ CycleClash (sideSystem c ϕ θ) := by
  have h := (satFin_iff.mp ((satFin_iff_signed c ϕ).mp hs)).2
  cases θ
  · exact h
  · exact fun hc => h (cycleClash_dual_iff.mp hc)

/-- A finite sign-fixed solution of the signed translation whose query fails the
covariant order decodes to a finite countermodel. -/
theorem finite_countermodel_of_fixed {B : V (2 * k) → FTree n}
    (hB : Covariant.Sat (FTree.toTree ∘ B) (signed c ϕ))
    (hfix : Signed.dual (FTree.toTree ∘ B) = FTree.toTree ∘ B)
    (hxy : ¬ (B (sv x false)).toTree ≤ (B (sv y false)).toTree) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).toTree (σ y).toTree := by
  have hσ : FTree.toTree ∘ (fun u => FTree.normalize c false (B (sv u false))) =
      decoded c (FTree.toTree ∘ B) := by
    funext u; simp [decoded]
  refine ⟨fun u => FTree.normalize c false (B (sv u false)), ?_, fun hle => hxy ?_⟩
  · rw [hσ, sat_iff_signed, normalized_decoded c hfix]; exact hB
  · simpa only [treeLe_iff_normalize, FTree.normalize_toTree, normalize_involutive] using hle

/-- On a finitely satisfiable system, every unsafe word has a finite countermodel.
On the bottom-prefix side, the finite witness of the order dual is dualised back. -/
theorem finite_countermodel_of_unsafe (hs : SatisfiableFin c ϕ) {θ : Side} {w : List (Fin n)}
    (hu : Unsafe c ϕ x y θ w) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).toTree (σ y).toTree := by
  obtain ⟨B, hB, hfix, hX, hY⟩ := finite_fixedWitness (sideSystem_flipClosed θ)
    (sideSystem_signCoherent θ) ((sideUnsafe_iff_not_labelClash θ w).mp hu)
    (sideSystem_not_cycleClash hs θ)
  have hne : ¬ (B (sideQuery x y θ).1).toTree ≤ (B (sideQuery x y θ).2).toTree :=
    fun h => hY (((cov_le_iff_safe _ _).mp h w).1 hX)
  cases θ
  · exact finite_countermodel_of_fixed hB hfix hne
  · have hd : FTree.toTree ∘ (fun z => FTree.normalize (fun _ => false) true (B z)) =
        Tree.dual ∘ (FTree.toTree ∘ B) := funext fun z => FTree.normalize_toTree _ _ _
    refine finite_countermodel_of_fixed (B := fun z => FTree.normalize (fun _ => false) true (B z))
      (by rw [hd]; exact ConstraintDual.sat_of_dual hB) ?_ fun h => hne ?_
    · rw [hd]
      change Tree.dual ∘ Signed.dual (FTree.toTree ∘ B) = _
      rw [hfix]
    · rw [FTree.normalize_toTree, FTree.normalize_toTree] at h
      exact (dual_le_iff _ _).mp h

end Sides

end FiniteTransfer

open FiniteTransfer

/-- Finite countermodel transfer, for every arity and every variance: when the
system has a finite model, every countermodel can be replaced by a finite one. -/
theorem finite_countermodel_transfer {n k : ℕ} (c : Fin n → Bool)
    {ϕ : Constraint n k} {x y : V k}
    (hs : ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ)
    (hn : ¬ Entails c ϕ x y) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      ¬ Tree.Le c (σ x).toTree (σ y).toTree := by
  obtain ⟨θ, w, hu⟩ : ∃ θ w, Unsafe c ϕ x y θ w := by
    simpa only [entails_iff_not_sideUnsafe, not_forall, not_not] using hn
  exact finite_countermodel_of_unsafe hs hu

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
