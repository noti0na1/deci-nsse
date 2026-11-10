import DeciNSSE.Monitor.Reader
import DeciNSSE.Monitor.Semantics

/-! # Label holes and semantic unsafety

Label-reader holes are exactly the words without events. Under satisfiability
they are precisely unsafe words, so the finite reader supplies the semantic
bridge required by the hole decision procedure. Both sides use the reader of
the signed translation, started at the query of the side.

## Main declarations

- `Monitor.hole_iff_not_occurs`: the label holes are the words without events.
- `Monitor.sideReader`, `Monitor.sideTarget`, `Monitor.SideHole`: the label reader of one
  side, the common target, and the holes of a side. A side reader has `2 * 4^(2*k)`
  states (`Monitor.card_state`).
- `Monitor.hole_iff_unsafe`: under satisfiability, the holes of a side are its unsafe words.
-/

namespace DeciNSSE.Monitor

open Events

open Holes

variable {n k : ℕ}

section Generic

variable {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

/-- Label holes are the words without events (no hypothesis). -/
theorem hole_iff_not_occurs (w : List (Fin n)) :
    IsReaderHole (reader ψ X Y) admission (target ψ) w ↔ ¬ Occurs ψ X Y w := by
  rw [isReaderHole_iff, mem_target_iff, AcceptAt, Occurs]
  simp only [admission, mem_eval_U, mem_eval_L, not_or, not_exists, not_and, and_assoc]

end Generic

section Signed

/-- The label reader of the side `θ` of the query `ϕ ⊨? x ≤ y`: the reader of the
signed translation at the query of that side. -/
abbrev sideReader (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side) :
    DFA (Fin n) (State (2 * k)) :=
  reader (signed c ϕ) (sideQuery x y θ).1 (sideQuery x y θ).2

/-- The target of both sides: the rejected label states of the signed translation. -/
abbrev sideTarget (c : Fin n → Bool) (ϕ : Constraint n k) : Set (State (2 * k)) :=
  target (signed c ϕ)

/-- The holes of the side `θ` of the query `ϕ ⊨? x ≤ y`: the words that the side reader
rejects without an admitted comparison. -/
abbrev SideHole (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)
    (w : List (Fin n)) : Prop :=
  IsReaderHole (sideReader c ϕ x y θ) admission (sideTarget c ϕ) w

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- Label-reader holes are the unsafe words of a satisfiable system, on either
side, for every arity and variance. -/
theorem hole_iff_unsafe (hs : Satisfiable c ϕ) (θ : Side) (w : List (Fin n)) :
    SideHole c ϕ x y θ w ↔ Unsafe c ϕ x y θ w :=
  (hole_iff_not_occurs w).trans (sideUnsafe_iff_not_events hs θ w).symm

end Signed

end DeciNSSE.Monitor
