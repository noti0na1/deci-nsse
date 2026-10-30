import DeciNSSE.Solver.Checked
import DeciNSSE.Main

/-! # Complete search without enumerating the reader state space

Only words are enumerated. The state cardinality in the length bound is
computed from its formula, without constructing a finite enumeration of states.
-/

namespace DeciNSSE.Solver
open Monitor Holes
variable {n k : ℕ}

/-- Exhaust the proved word bound using the packed hole checker. -/
def noHolesB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) : Bool :=
  let ψ := Events.sideSystem c ϕ θ
  let q := Events.sideQuery x y θ
  let r := reader ψ q.1 q.2
  let words := Packets.boundedLists (Finset.univ : Finset (Fin n))
    (RejectedTail.holeLengthBound (2 * 4 ^ (2 * k)))
  @decide (∀ w ∈ words, Checked.checkHole r w = false)
    (Finset.decidableDforallFinset (s := words))

theorem noHolesB_iff (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    noHolesB c ϕ x y θ = true ↔ ¬ ∃ w, (sideMonitor c ϕ x y θ).Hole w := by
  have hb := (sideMonitor c ϕ x y θ).hole_iff_bounded
  have hc : @Fintype.card (sideMonitor c ϕ x y θ).Q (sideMonitor c ϕ x y θ).instFintype =
      2 * 4 ^ (2 * k) := card_state (2 * k)
  rw [hc] at hb
  rw [hb]
  have hh (w : List (Fin n)) : Checked.checkHole
      (reader (Events.sideSystem c ϕ θ) (Events.sideQuery x y θ).1
        (Events.sideQuery x y θ).2) w = false ↔ ¬ (sideMonitor c ϕ x y θ).Hole w := by
    rw [Bool.eq_false_iff]
    exact not_congr ((Checked.checkHole_iff _ w).trans (reader_hole _ _ _ w))
  simp only [noHolesB, decide_eq_true_eq, Packets.mem_boundedLists,
    Finset.mem_univ, implies_true, and_true, hh, not_exists, not_and]
  change (∀ w, w.length ≤ _ → ¬ (sideMonitor c ϕ x y θ).Hole w) ↔
    ∀ w, (sideMonitor c ϕ x y θ).Hole w → ¬ w.length ≤ _
  constructor
  · intro h w hw hlen; exact h w hlen hw
  · intro h w hlen hw; exact h w hw hlen

/-- The complete decision expressed through Boolean checks and a numerical bound. -/
def completeDecide (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    Decidable (Entails c ϕ x y) :=
  decidable_of_iff
    (Checked.satB c ϕ = false ∨
      (noHolesB c ϕ x y .l = true ∧ noHolesB c ϕ x y .r = true)) (by
      rw [Checked.satB_eq, noHolesB_iff, noHolesB_iff]
      exact (entails_iff_of_monitors (sideMonitor c ϕ x y .l) (sideMonitor c ϕ x y .r)).symm)

/-- The complete decider has the same proof-relevant decision value. -/
@[csimp] theorem decideEntails_direct : @decideEntails = @completeDecide := by
  funext n k c ϕ x y
  exact Subsingleton.elim _ _

end DeciNSSE.Solver
