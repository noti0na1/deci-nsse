import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Transfer.RankedExtension

/-! # Cycle clashes under extension

A ranked source and sink extension has exactly the cycle clashes of the
original system: a nonempty lower or upper self-path cannot pass through a
source or a sink, so both cycle variables are old.

## Main declarations

- `Ranked.Extension.cycleClash_iff`: a ranked extension has exactly the cycle clashes of
  the original system.
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

end DeciNSSE
