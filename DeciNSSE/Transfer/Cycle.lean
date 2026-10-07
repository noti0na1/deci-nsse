import DeciNSSE.Satisfiability.Finite
import DeciNSSE.Transfer.RankedExtension

/-! # Cycle preservation by spine extensions

Ranked source and sink extensions preserve cycle clashes exactly. The
four-spine extension consequently preserves the cycle obstruction to finite
satisfiability.
-/

section

namespace DeciNSSE.Spine

open Spine

variable {n k : ℕ}

/-- A left-unsafety block followed by a right-unsafety block on new endpoints. -/
def fourExtension (ψ : Constraint n k) (x y xm ym : V k) (w : List (Fin n)) :
    Constraint n ((k + (2 * w.length + 2)) + (2 * w.length + 2)) :=
  rUnsafe (lUnsafe ψ x y w) (Fin.castAdd _ ym) (Fin.castAdd _ xm) w

/-- Exact semantics of the composite: four prefix requirements on old variables. -/
theorem fourSpine_restrict_iff (ψ : Constraint n k) (x y xm ym : V k)
    (w : List (Fin n)) (ρ : V k → Tree n) :
    (∃ ρ'', (ρ'' ∘ Fin.castAdd _) ∘ Fin.castAdd _ = ρ ∧ Covariant.Sat ρ'' (Spine.fourExtension ψ x y xm ym w)) ↔
      Covariant.Sat ρ ψ ∧ covPrefTop w (ρ x) ∧ ¬ covPrefTop w (ρ y) ∧
        ¬ covPrefBot w (ρ ym) ∧ covPrefBot w (ρ xm) := by
  constructor
  · rintro ⟨ρ'', hr, hs⟩
    obtain ⟨hl, hym, hxm⟩ :=
      (rUnsafe_restrict_iff _ _ _ w (ρ'' ∘ Fin.castAdd _)).mp ⟨ρ'', rfl, hs⟩
    obtain ⟨hψ, hx, hy⟩ := (lUnsafe_restrict_iff ψ x y w ρ).mp ⟨_, hr, hl⟩
    have e₁ : ρ'' (Fin.castAdd _ (Fin.castAdd _ ym)) = ρ ym := congrFun hr ym
    have e₂ : ρ'' (Fin.castAdd _ (Fin.castAdd _ xm)) = ρ xm := congrFun hr xm
    simp only [Function.comp_apply, e₁, e₂] at hym hxm
    exact ⟨hψ, hx, hy, hym, hxm⟩
  · rintro ⟨hψ, hx, hy, hym, hxm⟩
    obtain ⟨ρ', hr, hl⟩ := (lUnsafe_restrict_iff ψ x y w ρ).mpr ⟨hψ, hx, hy⟩
    have e₁ : ρ' (Fin.castAdd _ ym) = ρ ym := congrFun hr ym
    have e₂ : ρ' (Fin.castAdd _ xm) = ρ xm := congrFun hr xm
    obtain ⟨ρ'', hr', hs⟩ := (rUnsafe_restrict_iff _ _ _ w ρ').mpr
      ⟨hl, by rw [e₁]; exact hym, by rw [e₂]; exact hxm⟩
    exact ⟨ρ'', by rw [hr', hr], hs⟩

end DeciNSSE.Spine

end

section

namespace DeciNSSE.FiniteTransfer

open Spine

variable {n k m : ℕ}

section Extension

variable {ϕ : Constraint n k} {ψ : Constraint n (k + m)}
  {Source Sink : V (k + m) → Prop} {rank : V (k + m) → ℕ}

theorem extension_cycleClash_iff (e : Ranked.Extension ϕ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash ϕ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.old_mem, hd.map _ e.old_mem, hu.map _ e.old_mem⟩

end Extension

theorem rUnsafe_cycleClash_iff (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    CycleClash (rUnsafe ϕ x y ν) ↔ CycleClash ϕ :=
  extension_cycleClash_iff (Spine.rUnsafe_extension ϕ x y ν)

theorem lUnsafe_cycleClash_iff (ϕ : Constraint n k) (x y : V k) (ν : List (Fin n)) :
    CycleClash (lUnsafe ϕ x y ν) ↔ CycleClash ϕ :=
  extension_cycleClash_iff (Spine.lUnsafe_extension ϕ x y ν)

/-- The two composed fresh blocks add no cycle clash. -/
theorem fourExtension_cycleClash_iff (ψ : Constraint n k) (x y xm ym : V k)
    (w : List (Fin n)) : CycleClash (Spine.fourExtension ψ x y xm ym w) ↔ CycleClash ψ :=
  (rUnsafe_cycleClash_iff _ _ _ w).trans (lUnsafe_cycleClash_iff ψ x y w)

/-- The four-spine system is finitely satisfiable exactly when it is satisfiable
and the base system is finitely satisfiable. -/
theorem fourExtension_satFin_iff (ψ : Constraint n k) (x y xm ym : V k)
    (w : List (Fin n)) :
    (∃ σ, Covariant.Sat (FTree.toTree ∘ σ) (Spine.fourExtension ψ x y xm ym w)) ↔
      (∃ ρ'', Covariant.Sat ρ'' (Spine.fourExtension ψ x y xm ym w)) ∧
        ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ψ := by
  constructor
  · rintro ⟨σ, hσ⟩
    have h := ((fourSpine_restrict_iff ψ x y xm ym w _).mp ⟨_, rfl, hσ⟩).1
    exact ⟨⟨_, hσ⟩, ⟨fun z => σ (Fin.castAdd _ (Fin.castAdd _ z)), h⟩⟩
  · rintro ⟨⟨ρ'', hρ''⟩, hf⟩
    apply satFin_iff.mpr
    exact ⟨fun hl => hl.unsatisfiable ⟨ρ'', hρ''⟩,
      fun hc => (satFin_iff.mp hf).2 ((fourExtension_cycleClash_iff ψ x y xm ym w).mp hc)⟩

end DeciNSSE.FiniteTransfer

end
