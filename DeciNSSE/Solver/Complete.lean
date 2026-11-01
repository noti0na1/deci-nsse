import DeciNSSE.Solver.Checked
import DeciNSSE.Main

/-! # Complete search without enumerating the reader state space

`Solver.decideEntailsPacked` decides arbitrary-tree entailment with the packed checks:
packed satisfiability, then the packed hole check of every word within the proved length
bound on each side. Only words are enumerated. The state count in the length bound is
computed from its formula, `2 * 4^(2*k)` (`Monitor.card_sideMonitor`), not from a finite
enumeration of the reader states.

## Compiled code of `decideEntails`

The `@[csimp]` lemma `Solver.decideEntails_eq_decideEntailsPacked` states
`@decideEntails = @decideEntailsPacked`. Every module that imports this one, and so
`DeciNSSE.Solver`, compiles the headline decider `decideEntails` to
`decideEntailsPacked`. The decision value is unchanged, since `Decidable` is a
subsingleton, and so the proofs about `decideEntails` are untouched. Only `decideEntails`
is redirected. `decideEntailsReg`, `decideEntailsFin` and the summary and arity-one
deciders still evaluate the packaged side monitors. These carry the `Fintype` instance of
the reader states, so evaluating them enumerates every reader state.

## Main declarations

- `Solver.noHolesB`, `Solver.noHolesB_iff`: the bounded packed hole search of one side.
- `Solver.decideEntailsPacked`: the complete packed decider.
- `Solver.decideEntails_eq_decideEntailsPacked`: the `@[csimp]` substitution.
-/

namespace DeciNSSE.Solver
open Monitor Holes
variable {n k : ℕ}

/-- Whether no word within the proved length bound passes the packed hole check of the
side `θ`. -/
def noHolesB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) : Bool :=
  let r := packedSideReader c ϕ x y θ
  let words := Packets.boundedLists (Finset.univ : Finset (Fin n))
    (RejectedTail.holeLengthBound (2 * 4 ^ (2 * k)))
  @decide (∀ w ∈ words, Checked.checkHole r w = false)
    (Finset.decidableDforallFinset (s := words))

/-- The bounded packed search succeeds exactly when the side monitor has no hole. -/
theorem noHolesB_iff (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    noHolesB c ϕ x y θ = true ↔ ¬ ∃ w, (sideMonitor c ϕ x y θ).Hole w := by
  have hb := (sideMonitor c ϕ x y θ).hole_iff_bounded
  rw [card_sideMonitor] at hb
  rw [hb]
  have hh (w : List (Fin n)) : Checked.checkHole (packedSideReader c ϕ x y θ) w = false ↔
      ¬ (sideMonitor c ϕ x y θ).Hole w := by
    rw [Bool.eq_false_iff]
    exact not_congr (Checked.checkHole_iff_hole c ϕ x y θ w)
  simp only [noHolesB, decide_eq_true_eq, Packets.mem_boundedLists,
    Finset.mem_univ, implies_true, and_true, hh, not_exists, not_and]
  change (∀ w, w.length ≤ _ → ¬ (sideMonitor c ϕ x y θ).Hole w) ↔
    ∀ w, (sideMonitor c ϕ x y θ).Hole w → ¬ w.length ≤ _
  constructor
  · intro h w hw hlen; exact h w hlen hw
  · intro h w hlen hw; exact h w hw hlen

/-- Decide arbitrary-tree entailment through packed Boolean checks and the numerical
length bound. -/
@[instance_reducible] def decideEntailsPacked (c : Fin n → Bool) (ϕ : Constraint n k)
    (x y : V k) : Decidable (Entails c ϕ x y) :=
  decidable_of_iff
    (Checked.packedSatB c ϕ = false ∨
      (noHolesB c ϕ x y .l = true ∧ noHolesB c ϕ x y .r = true)) (by
      rw [Checked.packedSatB_eq, noHolesB_iff, noHolesB_iff]
      exact (entails_iff_of_monitors (sideMonitor c ϕ x y .l) (sideMonitor c ϕ x y .r)).symm)

/-- The packed decider has the same decision value as `decideEntails`; compiled code of
`decideEntails` runs `decideEntailsPacked`. -/
@[csimp] theorem decideEntails_eq_decideEntailsPacked :
    @decideEntails = @decideEntailsPacked := by
  funext n k c ϕ x y
  exact Subsingleton.elim _ _

end DeciNSSE.Solver
