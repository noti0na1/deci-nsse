import DeciNSSE.Transfer.Cycle
import DeciNSSE.Transfer.FiniteMedian

/-! # Finite countermodel transfer

When a finite solution exists, every countermodel has a finite counterpart.
Four spines enforce top at the positive source, bottom at its negative copy,
non-top at the positive target and non-bottom at its negative copy. Both
target inputs must be non-top because the finite third median input may be top;
the full constructor tree used for regular transfer need not be finite.
-/

namespace DeciNSSE

namespace FiniteTransfer

open Spine

variable {n k m : ℕ}

/-- All four prefix requirements, realised by an arbitrary solution, are realised
by a finite solution when the system is finitely satisfiable. -/
theorem finite_fourSpine {ψ : Constraint n m} {x y xm ym : V m} {w : List (Fin n)}
    {A : V m → Tree n}
    (hf : ∃ D : V m → FTree n, Covariant.Sat (FTree.toTree ∘ D) ψ) (ha : Covariant.Sat A ψ)
    (hx : covPrefTop w (A x)) (hy : ¬ covPrefTop w (A y))
    (hym : ¬ covPrefBot w (A ym)) (hxm : covPrefBot w (A xm)) :
    ∃ B : V m → FTree n, Covariant.Sat (FTree.toTree ∘ B) ψ ∧ covPrefTop w (B x).toTree ∧
      ¬ covPrefTop w (B y).toTree ∧ ¬ covPrefBot w (B ym).toTree ∧
        covPrefBot w (B xm).toTree := by
  obtain ⟨ρ'', -, hs⟩ := (fourSpine_restrict_iff ψ x y xm ym w A).mpr ⟨ha, hx, hy, hym, hxm⟩
  obtain ⟨B₂, hB₂⟩ := (fourExtension_satFin_iff ψ x y xm ym w).mpr ⟨⟨ρ'', hs⟩, hf⟩
  obtain ⟨hψ, hx', hy', hym', hxm'⟩ :=
    (fourSpine_restrict_iff ψ x y xm ym w _).mp ⟨FTree.toTree ∘ B₂, rfl, hB₂⟩
  exact ⟨fun z => B₂ (Fin.castAdd _ (Fin.castAdd _ z)), hψ, hx', hy', hym', hxm'⟩

/-- The signed coordinate of the same base variable with the opposite sign. -/
def flipV (z : V (2 * k)) : V (2 * k) := sv (base z) (!(sign z))

@[simp] theorem flipV_sv (u : V k) (p : Bool) : flipV (sv u p) = sv u (!p) := by
  simp [flipV]

/-- A fixed signed assignment swaps the leaves between the two signs. -/
theorem fixed_flipV {A : V (2 * k) → Tree n} (h : Signed.dual A = A) (z : V (2 * k)) :
    A (flipV z) = Tree.dual (A z) := by
  calc A (flipV z) = Signed.dual A (flipV z) := (congrFun h _).symm
    _ = Tree.dual (A z) := by simp [Signed.dual, flipV]

/-- The signed normalisation of a finite assignment is finite. -/
theorem normalized_finite (c : Fin n → Bool) (D : V k → FTree n) :
    FTree.toTree ∘ (fun z => FTree.normalize c (sign z) (D (base z))) =
      normalized c (FTree.toTree ∘ D) := by
  funext z; simp [normalized]

/-- A top/non-top witness of a signed normalisation has a finite counterpart,
again a normalisation of a finite variance-tree solution. -/
theorem finite_top_witness (c : Fin n → Bool) {ϕ : Constraint n k}
    {ρ : V k → Tree n} {u v : V (2 * k)} {w : List (Fin n)}
    (hf : ∃ D : V k → FTree n, Sat c (FTree.toTree ∘ D) ϕ)
    (hρ : Sat c ρ ϕ)
    (hu : covPrefTop w (normalized c ρ u)) (hv : ¬ covPrefTop w (normalized c ρ v)) :
    ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ ∧
      covPrefTop w (normalized c (FTree.toTree ∘ σ) u) ∧
        ¬ covPrefTop w (normalized c (FTree.toTree ∘ σ) v) := by
  obtain ⟨D, hD⟩ := hf
  have hDs : Covariant.Sat (FTree.toTree ∘ fun z => FTree.normalize c (sign z) (D (base z))) (signed c ϕ) := by
    rw [normalized_finite]; exact (sat_iff_signed c _ ϕ).mp hD
  have hfix := normalized_fixed c ρ
  have hum : covPrefBot w (normalized c ρ (flipV u)) := by
    rw [fixed_flipV hfix, covPrefBot_dual]; exact hu
  have hvm : ¬ covPrefBot w (normalized c ρ (flipV v)) := by
    rw [fixed_flipV hfix, covPrefBot_dual]; exact hv
  obtain ⟨B, hB, hbu, hbv, hbvm, hbum⟩ :=
    finite_fourSpine ⟨_, hDs⟩ ((sat_iff_signed c ρ ϕ).mp hρ) hu hv hvm hum
  have hM := symmetrizeFinite_sat hB hD
  have hfixM := symmetrizeFinite_fixed c B D
  let σ : V k → FTree n := fun z => FTree.normalize c false (symmetrizeFinite c B D (sv z false))
  have hσ : FTree.toTree ∘ σ = decoded c (FTree.toTree ∘ symmetrizeFinite c B D) := by
    funext z; simp only [Function.comp_apply, σ, FTree.normalize_toTree, decoded]
  have he : normalized c (FTree.toTree ∘ σ) = FTree.toTree ∘ symmetrizeFinite c B D := by
    rw [hσ, normalized_decoded c hfixM]
  have hS (z : V (2 * k)) : Signed.dual (FTree.toTree ∘ B) z = Tree.dual (B (flipV z)).toTree := rfl
  refine ⟨σ, (sat_iff_signed c _ ϕ).mpr (he ▸ hM), ?_, ?_⟩
  · rw [he, covPrefTop_iff_trace, Function.comp_apply, symmetrizeFinite_toTree, trace_median, hS,
      trace_dual, (covPrefTop_iff_trace _ _).mp hbu, (covPrefBot_iff_trace _ _).mp hbum]
    exact medianSym_self _ _
  · rw [he, covPrefTop_iff_trace, Function.comp_apply, symmetrizeFinite_toTree, trace_median, hS, trace_dual]
    apply medianSym_ne_top
    · exact fun h => hbv ((covPrefTop_iff_trace _ _).mpr h)
    · intro h
      apply hbvm
      rw [covPrefBot_iff_trace]
      revert h
      cases Tree.trace (B (flipV v)).toTree w <;> decide

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
  classical
  simp only [Entails, not_forall] at hn
  obtain ⟨ρ, hρ, hxy⟩ := hn
  have hcov : ¬ Tree.normalize c false (ρ x) ≤ Tree.normalize c false (ρ y) :=
    fun h => hxy ((treeLe_iff_normalize c _ _).mpr h)
  rw [cov_le_iff_safe] at hcov
  obtain ⟨w, hw⟩ := not_forall.mp hcov
  by_cases htop : covPrefTop w (Tree.normalize c false (ρ x)) ∧ ¬ covPrefTop w (Tree.normalize c false (ρ y))
  ·
    obtain ⟨hx, hy⟩ := htop
    obtain ⟨σ, hσ, hu, hv⟩ := finite_top_witness c hs hρ (u := sv x false)
      (v := sv y false) (w := w) (by rwa [normalized_sv]) (by rwa [normalized_sv])
    refine ⟨σ, hσ, fun hle => ?_⟩
    have h := ((cov_le_iff_safe _ _).mp ((treeLe_iff_normalize c _ _).mp hle) w).1
    rw [normalized_sv, Function.comp_apply] at hu hv
    exact hv (h hu)
  ·
    have hbot : covPrefBot w (Tree.normalize c false (ρ y)) ∧ ¬ covPrefBot w (Tree.normalize c false (ρ x)) := by
      by_contra hb
      apply hw
      constructor
      · intro hx; by_contra hy; exact htop ⟨hx, hy⟩
      · intro hy; by_contra hx; exact hb ⟨hy, hx⟩
    obtain ⟨hy, hx⟩ := hbot
    obtain ⟨σ, hσ, hu, hv⟩ := finite_top_witness c hs hρ (u := sv y true)
      (v := sv x true) (w := w)
      (by rwa [normalized_sv, normalize_true, covPrefTop_dual])
      (by rwa [normalized_sv, normalize_true, covPrefTop_dual])
    refine ⟨σ, hσ, fun hle => ?_⟩
    have h := ((cov_le_iff_safe _ _).mp ((treeLe_iff_normalize c _ _).mp hle) w).2
    rw [normalized_sv, normalize_true, covPrefTop_dual, Function.comp_apply] at hu hv
    exact hv (h hu)

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
