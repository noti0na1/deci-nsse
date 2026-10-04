import DeciNSSE.Coverage.CapInflation

/-! # Ordinary and periodic coverage

Full coverage combines ordinary acceptance with a prefix image and an
admitted cap root. Finite monoid data give a Boolean membership decision.
-/

namespace DeciNSSE.FullCoverage

open Words CapInflation
open scoped TerminalCopy

variable {H ι : Type*} [Monoid H]

section Membership
variable {α : Type*}

def FullCovered (μ : List α →* H) (VA : Set H) (V U : ι → Set H)
    (w : List α) : Prop :=
  μ w ∈ VA ∨ ∃ e π v, w = π ++ v ∧ μ π ∈ V e ∧ CapCovered μ (U e) v

def fullCoveredB [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]
    [Fintype ι] (μ : List α →* H) (VA : Set H) (V U : ι → Set H)
    [DecidablePred (· ∈ VA)] [∀ e, DecidablePred (· ∈ V e)]
    [∀ e, DecidablePred (· ∈ U e)] (w : List α) : Bool :=
  decide (μ w ∈ VA) || (List.range (w.length + 1)).any (fun i =>
    decide (∃ e, μ (w.take i) ∈ V e ∧ capCoveredB μ (U e) (w.drop i) = true))

theorem fullCoveredB_iff [Fintype α] [DecidableEq α] [Fintype H] [DecidableEq H]
    [Fintype ι] (μ : List α →* H) (VA : Set H) (V U : ι → Set H)
    [DecidablePred (· ∈ VA)] [∀ e, DecidablePred (· ∈ V e)]
    [∀ e, DecidablePred (· ∈ U e)] (w : List α) :
    fullCoveredB μ VA V U w = true ↔ FullCovered μ VA V U w := by
  simp only [fullCoveredB, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range, FullCovered]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i, _, e, hv, hu⟩
    exact ⟨e, w.take i, w.drop i, (List.take_append_drop i w).symm,
      hv, (capCoveredB_iff μ (U e) _).mp hu⟩
  · rintro ⟨e, π, v, rfl, hv, hu⟩
    refine ⟨π.length, by simp only [List.length_append]; omega, e, by simpa using hv, ?_⟩
    simpa using (capCoveredB_iff μ (U e) v).mpr hu

end Membership

end DeciNSSE.FullCoverage
