import DeciNSSE.Constraints.Dual
import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Transfer.RankedExtension

/-! # Cycle clashes under extension and duality

A ranked source and sink extension has exactly the cycle clashes of the
original system: a nonempty lower or upper self-path cannot pass through a
source or a sink, so both cycle variables are old. Order duality exchanges the
lower and the upper self-path of a cycle clash.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace Ranked

variable {K : ℕ} {ι : V k → V K} {ϕ : Constraint n k} {ψ : Constraint n K}
  {Source Sink : V K → Prop} {rank : V K → ℕ}

/-- A ranked extension has exactly the cycle clashes of the original system. -/
theorem Extension.cycleClash_iff (e : Extension ι ϕ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash ϕ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    obtain ⟨u, v, hl', hd', hu'⟩ := e.cycle_reflect hn hl hd hu
    exact ⟨π, u, v, hn, hl', hd', hu'⟩
  · rintro ⟨π, u, v, hn, hl, hd, hu⟩
    exact ⟨π, _, _, hn, hl.map _ e.old_mem, hd.map _ e.old_mem, hu.map _ e.old_mem⟩

end Ranked

/-- Order duality preserves cycle clashes, exchanging the two cycle variables. -/
theorem cycleClash_dual_iff {ψ : Constraint n k} :
    CycleClash (Constraint.dual ψ) ↔ CycleClash ψ := by
  constructor
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    exact ⟨π, b, a, hn, ConstraintDual.upper_iff.mp hu, ConstraintDual.derives_iff.mp hd,
      ConstraintDual.lower_iff.mp hl⟩
  · rintro ⟨π, a, b, hn, hl, hd, hu⟩
    exact ⟨π, b, a, hn, ConstraintDual.lower_iff.mpr hu, ConstraintDual.derives_iff.mpr hd,
      ConstraintDual.upper_iff.mpr hl⟩

end DeciNSSE
