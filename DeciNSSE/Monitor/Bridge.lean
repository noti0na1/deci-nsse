import DeciNSSE.Monitor.Interface
import DeciNSSE.Monitor.Reader
import DeciNSSE.Monitor.Semantics

/-! # Label holes and semantic unsafety

Label-monitor holes are exactly words without events. Under satisfiability
they are precisely unsafe words, so the finite reader supplies the semantic
interface required by the hole decision procedure.
-/

namespace DeciNSSE.Monitor

open Events

open Holes FiniteVariance

variable {n k : ℕ}

section Generic

variable {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

theorem readyAt_take_iff (j : ℕ) : ReadyAt ψ X Y (w.take j) ↔ Events.Ready ψ X Y w j := by
  simp only [ReadyAt, Events.Ready, USet, LSet, mem_botVars, mem_topVars, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem acceptAt_l_iff :
    AcceptAt ψ X Y .l w ↔ (∃ j ≤ w.length, Events.Ready ψ X Y w j) ∨ Events.Child ψ X w := by
  have hr : ((∃ j < w.length, ReadyAt ψ X Y (w.take j)) ∨ ReadyAt ψ X Y w) ↔
      ∃ j ≤ w.length, Events.Ready ψ X Y w j := by
    simp only [← readyAt_take_iff]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, hj.le, h⟩
      · exact ⟨w.length, le_rfl, by rwa [List.take_length]⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_ge j w.length with hlt | hge
      · exact Or.inl ⟨j, hlt, h⟩
      · obtain rfl : j = w.length := le_antisymm hj hge
        rw [List.take_length] at h
        exact Or.inr h
  have hc : ChildAt ψ X Y .l w ↔ Events.Child ψ X w := by
    simp only [ChildAt, Events.Child, USet, List.take_length, Set.mem_ofPred_eq]
    exact ⟨fun ⟨z, b, hz, hl⟩ => ⟨z, hz, b, hl⟩, fun ⟨z, hz, b, hl⟩ => ⟨z, b, hz, hl⟩⟩
  rw [AcceptAt, ← or_assoc, hr, hc]

theorem noWitness_iff {θ : Side} {Rs : ℕ → ℕ → Prop}
    (hR : ∀ s e, admission θ ((reader ψ X Y θ).eval (w.take s))
      ((reader ψ X Y θ).eval (w.take e)) ↔ Rs s e) :
    (∀ p q, WitnessedPair (reader ψ X Y θ) w p q → ¬ admission θ p q) ↔
      ¬ ∃ s e, s < e ∧ e ≤ w.length ∧ w.drop e <+: w.drop s ∧ Rs s e := by
  constructor
  · rintro h ⟨s, e, hse, he, hp, hr⟩
    exact h _ _ ⟨s, e, hse, he, rfl, rfl, hp⟩ ((hR s e).mpr hr)
  · rintro h p q ⟨s, e, hse, he, rfl, rfl, hp⟩ hr
    exact h ⟨s, e, hse, he, hp, (hR s e).mp hr⟩

/-- Left label holes are the words without left events (no hypothesis). -/
theorem hole_left_iff (w : List (Fin n)) :
    IsReaderHole (reader ψ X Y .l) (admission .l) (target ψ .l) w ↔ ¬ Occurs ψ X Y w := by
  have hR : ∀ s e, admission .l ((reader ψ X Y .l).eval (w.take s))
      ((reader ψ X Y .l).eval (w.take e)) ↔ (Events.Cross ψ X Y w s e ∨ Events.Self ψ X w s e) := by
    intro s e
    rw [self_iff]
    simp only [admission, Cross, Self, mem_eval_U, mem_eval_L, Events.Cross, Set.Nonempty,
      Set.mem_inter_iff, USet, LSet, Set.mem_ofPred_eq]
  unfold IsReaderHole runPrefix
  rw [List.take_length, mem_target_iff, noWitness_iff hR, acceptAt_l_iff, occurs_def,
    ← not_or, or_assoc]

theorem self_r_iff (s e : ℕ) :
    Self .r ((reader ψ X Y .r).eval (w.take s)) ((reader ψ X Y .r).eval (w.take e)) ↔
      (LSet ψ Y w s ∩ flipV '' LSet ψ Y w e).Nonempty := by
  simp only [Self, mem_eval_L]
  constructor
  · rintro ⟨z, hz, hz'⟩
    exact ⟨z, hz, flipV z, hz', flipV_flipV z⟩
  · rintro ⟨z, hz, v, hv, rfl⟩
    exact ⟨flipV v, hz, by rw [flipV_flipV]; exact hv⟩

/-- The events of the order dual, written on the original system. -/
theorem occurs_dual_iff :
    Occurs (Constraint.dual ψ) Y X w ↔
      (∃ j ≤ w.length,
        (∃ v ∈ LSet ψ Y w j, Lit.eqTop v ∈ ψ) ∨ (∃ v ∈ USet ψ X w j, Lit.eqBot v ∈ ψ) ∨
        (LSet ψ Y w j ∩ USet ψ X w j).Nonempty) ∨
      (∃ v ∈ LSet ψ Y w w.length, ∃ a, Lit.fLe a v ∈ ψ) ∨
      ∃ s e, s < e ∧ e ≤ w.length ∧ w.drop e <+: w.drop s ∧
        ((USet ψ X w s ∩ LSet ψ Y w e).Nonempty ∨
          (LSet ψ Y w s ∩ flipV '' LSet ψ Y w e).Nonempty) := by
  simp only [Occurs, Events.Ready, Events.Child, Events.Cross, uSet_dual, lSet_dual, eqBot_mem_dual,
    eqTop_mem_dual, leF_mem_dual]

/-- Right label holes are the words without right events (no hypothesis). -/
theorem hole_right_iff (w : List (Fin n)) :
    IsReaderHole (reader ψ X Y .r) (admission .r) (target ψ .r) w ↔
      ¬ Occurs (Constraint.dual ψ) Y X w := by
  have hR : ∀ s e, admission .r ((reader ψ X Y .r).eval (w.take s))
      ((reader ψ X Y .r).eval (w.take e)) ↔
        ((USet ψ X w s ∩ LSet ψ Y w e).Nonempty ∨
          (LSet ψ Y w s ∩ flipV '' LSet ψ Y w e).Nonempty) := by
    intro s e
    rw [admission, self_r_iff]
    simp only [Cross, mem_eval_U, mem_eval_L, Set.Nonempty, Set.mem_inter_iff, USet, LSet,
      Set.mem_ofPred_eq]
  have hready : ((∃ j < w.length, ReadyAt ψ X Y (w.take j)) ∨ ReadyAt ψ X Y w) ↔
      ∃ j ≤ w.length, (∃ v ∈ LSet ψ Y w j, Lit.eqTop v ∈ ψ) ∨
        (∃ v ∈ USet ψ X w j, Lit.eqBot v ∈ ψ) ∨ (LSet ψ Y w j ∩ USet ψ X w j).Nonempty := by
    have e : ∀ j, ReadyAt ψ X Y (w.take j) ↔ ((∃ v ∈ LSet ψ Y w j, Lit.eqTop v ∈ ψ) ∨
        (∃ v ∈ USet ψ X w j, Lit.eqBot v ∈ ψ) ∨ (LSet ψ Y w j ∩ USet ψ X w j).Nonempty) := by
      intro j
      rw [readyAt_take_iff, Events.Ready, Set.inter_comm]
      exact or_left_comm
    simp only [← e]
    constructor
    · rintro (⟨j, hj, h⟩ | h)
      · exact ⟨j, hj.le, h⟩
      · exact ⟨w.length, le_rfl, by rwa [List.take_length]⟩
    · rintro ⟨j, hj, h⟩
      rcases Nat.lt_or_ge j w.length with hlt | hge
      · exact Or.inl ⟨j, hlt, h⟩
      · obtain rfl : j = w.length := le_antisymm hj hge
        rw [List.take_length] at h
        exact Or.inr h
  have hc : ChildAt ψ X Y .r w ↔ ∃ v ∈ LSet ψ Y w w.length, ∃ a, Lit.fLe a v ∈ ψ := by
    simp only [ChildAt, LSet, List.take_length, Set.mem_ofPred_eq]
    exact ⟨fun ⟨a, z, hz, hl⟩ => ⟨z, hz, a, hl⟩, fun ⟨z, hz, a, hl⟩ => ⟨a, z, hz, hl⟩⟩
  unfold IsReaderHole runPrefix
  rw [List.take_length, mem_target_iff, noWitness_iff hR, AcceptAt, ← or_assoc, hready, hc,
    occurs_dual_iff, ← not_or, or_assoc]

end Generic

section Signed

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- Label holes are the event-free words, on either side, for every arity
and variance, with no hypothesis. -/
theorem hole_iff_no_events (θ : Side) (w : List (Fin n)) :
    IsReaderHole (reader (signed c ϕ) (sv x false) (sv y false) θ) (admission θ)
      (target (signed c ϕ) θ) w ↔ ¬ Events.SideOccurs c ϕ x y θ w := by
  cases θ
  · exact hole_left_iff w
  · exact hole_right_iff w

/-- Label-reader holes are the unsafe words of a satisfiable system. -/
theorem hole_iff_unsafe (hs : ∃ ρ, Sat c ρ ϕ) (θ : Side)
    (w : List (Fin n)) :
    IsReaderHole (reader (signed c ϕ) (sv x false) (sv y false) θ) (admission θ)
        (target (signed c ϕ) θ) w ↔
      Unsafe c ϕ x y θ w :=
  (hole_iff_no_events θ w).trans (sideUnsafe_iff_not_events hs θ w).symm

end Signed

/-- Package one side of the label reader with its semantic bridge. -/
def sideMonitor (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    Monitor.SideMonitor n c ϕ x y θ where
  Q := State (2 * k)
  M := reader (signed c ϕ) (sv x false) (sv y false) θ
  R := admission θ
  T := target (signed c ϕ) θ
  bridge hs w := hole_iff_unsafe hs θ w

/-- The label monitor family at every arity, including `n = 0`. -/
def family (c : Fin n → Bool) : Monitor.Family n c :=
  ⟨fun ϕ x y θ => sideMonitor c ϕ x y θ⟩

/-- Unsafe words have a bounded witness at every arity, including zero. -/
theorem unsafe_iff_bounded {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    {θ : Side} (hs : ∃ ρ, Sat c ρ ϕ) :
    (∃ w, Unsafe c ϕ x y θ w) ↔
      ∃ w, Unsafe c ϕ x y θ w ∧
        w.length ≤ RejectedTail.holeLengthBound (2 * 4 ^ (2 * k)) := by
  have h := (sideMonitor c ϕ x y θ).unsafe_iff_bounded hs
  have hc : @Fintype.card (sideMonitor c ϕ x y θ).Q (sideMonitor c ϕ x y θ).instFintype =
      2 * 4 ^ (2 * k) := card_state (2 * k)
  rwa [hc] at h

end DeciNSSE.Monitor
