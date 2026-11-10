import DeciNSSE.Monitor.Clash
import DeciNSSE.Transfer.Safety

/-! # Events and unsafe words

Both sides of a query read the signed translation. The top-prefix side reads the
query `(x⁺, y⁺)`. A variance solution takes dual values at the two signs of a
variable, so a bottom of `y` that `x` does not share is a top of `y⁻` that `x⁻` does
not share: the bottom-prefix side reads the query `(y⁻, x⁻)`. The unsafe words of a
side are the top-prefix witnesses of its query, hence exactly the words whose
four-spine extension has no label clash. For a satisfiable system these are the
words without events. Satisfiability excludes clashes inherited from the original
constraints; without that hypothesis, the event-free criterion alone need not give a
model.

## Main declarations

- `Events.sideQuery`, `Events.SideOccurs`: the signed query of a side and its events.
- `Events.sideUnsafe_iff_witness`, `Events.sideUnsafe_iff_not_labelClash`,
  `Events.sideUnsafe_iff_not_events`: the three descriptions of the unsafe words.
-/

namespace DeciNSSE.Events

open Spine.Closure

open SignDuality

variable {n k : ℕ}

section Events

variable (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- The query of the signed translation read on side `θ`: `(x⁺, y⁺)` on the
top-prefix side and `(y⁻, x⁻)` on the bottom-prefix side. -/
def sideQuery : Side → V (2 * k) × V (2 * k)
  | .l => (sv x false, sv y false)
  | .r => (sv y true, sv x true)

/-- The events of side `θ`: the events of its query in the signed translation. -/
def SideOccurs (θ : Side) (w : List (Fin n)) : Prop :=
  Occurs (signed c ϕ) (sideQuery x y θ).1 (sideQuery x y θ).2 w

end Events

section Bridge

variable {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}

/-- The signed translation of a satisfiable system has no label clash. -/
theorem signed_not_labelClash (hs : Satisfiable c ϕ) : ¬ LabelClash (signed c ϕ) :=
  fun hc => hc.unsatisfiable (sat_implies_signed_sat c ϕ hs)

/-- An unsafe word of a side is a top-prefix witness of its signed query: a solution
whose normalization has a top of the first root and no top of the second on the prefixes
of the word. -/
theorem sideUnsafe_iff_witness (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ∃ ρ, Sat c ρ ϕ ∧ covPrefTop w (normalized c ρ (sideQuery x y θ).1) ∧
      ¬ covPrefTop w (normalized c ρ (sideQuery x y θ).2) := by
  cases θ <;> simp only [Unsafe, sideQuery, prefTop_iff_normalize, prefBot_iff_normalize,
    normalized_sv, normalize_true, covPrefTop_dual]

/-- A word is unsafe on a side exactly when the four-spine extension of its signed
query has no label clash. No satisfiability hypothesis is needed. -/
theorem sideUnsafe_iff_not_labelClash (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ LabelClash
      (Spine.extension c ϕ (sideQuery x y θ).1 (sideQuery x y θ).2 w) :=
  (sideUnsafe_iff_witness θ w).trans witness_iff_not_labelClash

/-- Under satisfiability, the unsafe words of a side are the words without its events. -/
theorem sideUnsafe_iff_not_events (hs : Satisfiable c ϕ) (θ : Side) (w : List (Fin n)) :
    Unsafe c ϕ x y θ w ↔ ¬ SideOccurs c ϕ x y θ w := by
  rw [sideUnsafe_iff_not_labelClash, labelClash_extension_iff_occurs (signed_not_labelClash hs)]
  rfl

end Bridge

end DeciNSSE.Events
