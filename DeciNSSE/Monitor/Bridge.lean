import DeciNSSE.Monitor.Interface
import DeciNSSE.Monitor.Reader
import DeciNSSE.Monitor.Semantics

/-! # Label holes and semantic unsafety

Label-monitor holes are exactly words without events. Under satisfiability
they are precisely unsafe words, so the finite reader supplies the semantic
interface required by the hole decision procedure. Each side uses the reader
of its covariant system and query; the bottom-prefix side is the top-prefix
side of the order dual.

## Main declarations

- `Monitor.hole_iff_not_occurs`: the label holes are the words without events.
- `Monitor.sideReader`, `Monitor.sideTarget`: the label reader and the target of one side.
- `Monitor.hole_iff_unsafe`: under satisfiability, the holes of a side are its unsafe words.
- `Monitor.sideMonitor`, `Monitor.family`: the packaged side monitors at every arity.
- `Monitor.card_sideMonitor`: a side monitor has `2 * 4^(2*k)` reader states.
- `Monitor.unsafe_iff_bounded`: unsafe words have witnesses within the hole length bound.
-/

namespace DeciNSSE.Monitor

open Events

open Holes

variable {n k : ℕ}

section Generic

variable {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

/-- Readiness of the reader labels at the cut `j` is the readiness event at `j`. -/
theorem readyAt_take_iff (j : ℕ) : ReadyAt ψ X Y (w.take j) ↔ Events.Ready ψ X Y w j := by
  simp only [ReadyAt, Events.Ready, USet, LSet, mem_botVars, mem_topVars, Set.Nonempty,
    Set.mem_inter_iff, Set.mem_ofPred_eq]

/-- Acceptance along `w` is readiness at some cut or the terminal child event. -/
theorem acceptAt_iff :
    AcceptAt ψ X Y w ↔ (∃ j ≤ w.length, Events.Ready ψ X Y w j) ∨ Events.Child ψ X w := by
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
  have hc : ChildAt ψ X w ↔ Events.Child ψ X w := by
    simp only [ChildAt, Events.Child, USet, List.take_length, Set.mem_ofPred_eq]
    exact ⟨fun ⟨z, b, hz, hl⟩ => ⟨z, hz, b, hl⟩, fun ⟨z, hz, b, hl⟩ => ⟨z, b, hz, hl⟩⟩
  rw [AcceptAt, ← or_assoc, hr, hc]

/-- Label holes are the words without events (no hypothesis). -/
theorem hole_iff_not_occurs (w : List (Fin n)) :
    IsReaderHole (reader ψ X Y) admission (target ψ) w ↔ ¬ Occurs ψ X Y w := by
  have hR : ∀ s e, admission ((reader ψ X Y).eval (w.take s))
      ((reader ψ X Y).eval (w.take e)) ↔ (Events.Cross ψ X Y w s e ∨ Events.Self ψ X w s e) := by
    intro s e
    rw [self_iff]
    simp only [admission, mem_eval_U, mem_eval_L, Events.Cross, Set.Nonempty,
      Set.mem_inter_iff, USet, LSet, Set.mem_ofPred_eq]
  rw [isReaderHole_iff, mem_target_iff, acceptAt_iff, occurs_def]
  simp only [hR, not_or, not_exists, not_and, and_assoc]

end Generic

section Signed

/-- The label reader of the side `θ` of the query `ϕ ⊨? x ≤ y`: the reader of the
covariant system and query of that side. Checkers use it directly rather than through
`sideMonitor`: the packaged monitor also carries a `Fintype` instance, and evaluating
that instance would enumerate every reader state. -/
abbrev sideReader (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    DFA (Fin n) (State (2 * k)) :=
  reader (sideSystem c ϕ θ) (sideQuery x y θ).1 (sideQuery x y θ).2

/-- The target of the side `θ`: the rejected label states of its covariant system. -/
abbrev sideTarget (c : Fin n → Bool) (ϕ : Constraint n k) (θ : Side) : Set (State (2 * k)) :=
  target (sideSystem c ϕ θ)

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- Label-reader holes are the unsafe words of a satisfiable system, on either
side, for every arity and variance. -/
theorem hole_iff_unsafe (hs : Satisfiable c ϕ) (θ : Side) (w : List (Fin n)) :
    IsReaderHole (sideReader c ϕ x y θ) admission (sideTarget c ϕ θ) w ↔
      Unsafe c ϕ x y θ w :=
  (hole_iff_not_occurs w).trans (sideUnsafe_iff_not_events hs θ w).symm

end Signed

/-- Package one side of the label reader with its semantic bridge. -/
def sideMonitor (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    Monitor.SideMonitor n c ϕ x y θ where
  Q := State (2 * k)
  M := sideReader c ϕ x y θ
  R := admission
  T := sideTarget c ϕ θ
  bridge hs w := hole_iff_unsafe hs θ w

/-- A side monitor has `2 * 4^(2*k)` reader states: two label sets over the `2 * k`
signed variables and one latch. -/
theorem card_sideMonitor (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    Fintype.card (sideMonitor c ϕ x y θ).Q = 2 * 4 ^ (2 * k) :=
  card_state (2 * k)

/-- The label monitor family at every arity, including `n = 0`. -/
def family (c : Fin n → Bool) : Monitor.Family n c :=
  ⟨fun ϕ x y θ => sideMonitor c ϕ x y θ⟩

/-- Unsafe words have a bounded witness at every arity, including zero. -/
theorem unsafe_iff_bounded {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    {θ : Side} (hs : Satisfiable c ϕ) :
    (∃ w, Unsafe c ϕ x y θ w) ↔
      ∃ w, Unsafe c ϕ x y θ w ∧
        w.length ≤ RejectedTail.holeLengthBound (2 * 4 ^ (2 * k)) := by
  have h := (sideMonitor c ϕ x y θ).unsafe_iff_bounded hs
  rwa [card_sideMonitor] at h

end DeciNSSE.Monitor
