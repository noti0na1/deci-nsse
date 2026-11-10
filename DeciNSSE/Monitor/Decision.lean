import DeciNSSE.Monitor.Bridge
import DeciNSSE.RejectedTail.Decision
import DeciNSSE.Transfer.Finite
import DeciNSSE.Transfer.Regular

/-! # Entailment from the side readers

Satisfiability is tested before either hole search. The absence of holes on
both sides decides arbitrary-tree entailment; regular and finite transfer
give the corresponding decisions in the restricted domains.

The deciders take a decider for the existence of holes on each side. The bounded
hole search `Monitor.decideSideHoles` gives the deciders of `DeciNSSE.Main`; the
summary and arity-one deciders pass their own hole searches.

## Main declarations

- `Monitor.entails_iff_sideHoles`: entailment is unsatisfiability or the absence of
  holes on both sides.
- `Monitor.entailsFin_iff_satFinB`: finite entailment is finite unsatisfiability or
  unrestricted entailment.
- `Monitor.decideSideHoles`: the bounded hole search of one side.
- `Monitor.decideEntailsWith`, `Monitor.decideEntailsRegWith`,
  `Monitor.decideEntailsFinWith`: entailment over arbitrary, regular and finite
  trees from a side-hole decider.
-/

namespace DeciNSSE.Monitor

variable {n : ℕ} {c : Fin n → Bool} {k : ℕ} {ϕ : Constraint n k} {x y : V k}

/-- Entailment is unsatisfiability or the absence of holes on both sides. -/
theorem entails_iff_sideHoles :
    Entails c ϕ x y ↔ satB c ϕ = false ∨
      ((¬ ∃ w, SideHole c ϕ x y .l w) ∧ (¬ ∃ w, SideHole c ϕ x y .r w)) := by
  rw [entails_iff_not_sideUnsafe, satB_eq_false_iff]
  by_cases hs : Satisfiable c ϕ
  · simp only [hs, not_true_eq_false, false_or, hole_iff_unsafe hs, not_exists]
    exact ⟨fun h => ⟨h .l, h .r⟩, fun h θ => by cases θ <;> [exact h.1; exact h.2]⟩
  · simp only [hs, not_false_eq_true, true_or, iff_true]
    exact fun θ w => not_unsafe_of_unsat hs w

/-- An unsatisfiable system entails everything. -/
theorem entails_of_satB_false (h : satB c ϕ = false) : Entails c ϕ x y :=
  fun ρ hρ => absurd ⟨ρ, hρ⟩ ((satB_eq_false_iff c ϕ).mp h)

/-- On a satisfiable system, entailment is the absence of holes on both sides. -/
theorem entails_iff_no_holes (h : satB c ϕ = true) :
    Entails c ϕ x y ↔ (¬ ∃ w, SideHole c ϕ x y .l w) ∧ (¬ ∃ w, SideHole c ϕ x y .r w) := by
  rw [entails_iff_sideHoles, h]
  simp

/-- Finite entailment is finite unsatisfiability or unrestricted entailment. -/
theorem entailsFin_iff_satFinB (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :
    EntailsFin c ϕ x y ↔ satFinB c ϕ = false ∨ Entails c ϕ x y := by
  rw [entailsFin_iff, satFinB_eq_false_iff]

/-- The bounded hole search of one side: `RejectedTail.decideHole` enumerates the words of
length at most `RejectedTail.holeLengthBound N` for the state count `N = 2 * 4^(2*k)` of the
side reader. -/
@[instance_reducible] def decideSideHoles (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) : Decidable (∃ w, SideHole c ϕ x y θ w) :=
  RejectedTail.decideHole _ _ _ (card_state (2 * k))

/-- Entailment over arbitrary trees, from a decider `dec` for the existence of holes on
each side. Satisfiability is tested first; the hole searches run only on satisfiable
systems. -/
@[instance_reducible] def decideEntailsWith
    (dec : ∀ θ, Decidable (∃ w, SideHole c ϕ x y θ w)) : Decidable (Entails c ϕ x y) :=
  if h : satB c ϕ = true then
    letI := dec .l
    letI := dec .r
    decidable_of_iff _ (entails_iff_no_holes h).symm
  else
    isTrue (entails_of_satB_false (Bool.eq_false_iff.mpr h))

/-- Entailment over regular trees, from a side-hole decider, by regular transfer. -/
@[instance_reducible] def decideEntailsRegWith
    (dec : ∀ θ, Decidable (∃ w, SideHole c ϕ x y θ w)) : Decidable (EntailsReg c ϕ x y) :=
  letI := decideEntailsWith dec
  decidable_of_iff _ (entailsReg_iff_entails c ϕ x y).symm

/-- Entailment over finite trees, from a side-hole decider. Finite satisfiability is
tested first; the unrestricted decision runs only on finitely satisfiable systems. -/
@[instance_reducible] def decideEntailsFinWith
    (dec : ∀ θ, Decidable (∃ w, SideHole c ϕ x y θ w)) : Decidable (EntailsFin c ϕ x y) :=
  if h : satFinB c ϕ = true then
    letI := decideEntailsWith dec
    decidable_of_iff (Entails c ϕ x y) (by rw [entailsFin_iff_satFinB, h]; simp)
  else
    isTrue (entailsFin_of_not_satFinB (Bool.eq_false_iff.mpr h) x y)

end DeciNSSE.Monitor
