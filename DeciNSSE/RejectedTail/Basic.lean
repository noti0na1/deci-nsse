import DeciNSSE.Holes.Basic

/-! # Rejected paths and the admission cone

Rejection persists between two rejected prefixes, rather than under arbitrary
extensions. If the first rejected cut is `J`, every witnessed admitted
comparison has `s < e ≤ J`, including comparisons ending at `J`. This admission
cone confines all possible admitted endpoints to the initial segment.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail
open Holes
variable {α Q : Type*}

/-- The first target cut, including cut zero. -/
def IsFirstRejectedPrefix (M : DFA α Q) (T : Set Q) (w : List α) (J : ℕ) : Prop :=
  J ≤ w.length ∧ M.eval (w.take J) ∈ T ∧ ∀ i < J, M.eval (w.take i) ∉ T

/-- Includes terminal comparisons. Only witnessed comparisons need the cone. -/
def AdmissionCone (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) : Prop :=
  ∀ w J, M.eval w ∈ T → IsFirstRejectedPrefix M T w J →
    ∀ s e, s < e → e ≤ w.length → w.drop e <+: w.drop s →
      R (M.eval (w.take s)) (M.eval (w.take e)) → e ≤ J

/-- Rejection holds between rejected prefixes, and admitted comparisons end at or before the first rejection. -/
class RejectedPath (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) : Prop where
  between : ∀ v u w, v <+: u → u <+: w → M.eval v ∈ T → M.eval w ∈ T → M.eval u ∈ T
  cone : AdmissionCone M R T

/-- Existential over holes, not a bound for each fixed rejected prefix. -/
def BoundedRejectedTail (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (B : ℕ) : Prop :=
  (∃ w, IsReaderHole M R T w) →
    ∃ w J, IsReaderHole M R T w ∧ IsFirstRejectedPrefix M T w J ∧ w.length - J ≤ B

theorem exists_firstRejectedPrefix (M : DFA α Q) (T : Set Q) {w : List α}
    (hw : M.eval w ∈ T) : ∃ J, IsFirstRejectedPrefix M T w J := by
  classical
  have hex : ∃ J, J ≤ w.length ∧ M.eval (w.take J) ∈ T :=
    ⟨w.length, le_rfl, by simpa using hw⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi ht
  exact Nat.find_min hex hi ⟨by have := (Nat.find_spec hex).1; omega, ht⟩

/-- A comparison identifies letters at distance `e-s`. -/
theorem comparison_letters {w : List α} {s e k : ℕ}
    (hse : s < e) (he : e ≤ k) (hk : k < w.length)
    (hp : w.drop e <+: w.drop s) : w[k - (e - s)]? = w[k]? := by
  have hlen : k - e < (w.drop e).length := by simp; omega
  obtain ⟨t, ht⟩ := hp
  have hh := congrArg (fun l : List α => l[k - e]?) ht
  rw [List.getElem?_append_left hlen] at hh
  simp only [List.getElem?_drop] at hh
  have h1 : e + (k - e) = k := by omega
  have h2 : s + (k - e) = k - (e - s) := by omega
  simpa only [h1, h2] using hh.symm

end DeciNSSE.RejectedTail
