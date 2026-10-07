import DeciNSSE.RejectedTail.Basic

/-! # Finite prefixes of periodic streams

A finite periodic comparison on a sufficiently long repeated block extends
to equality of infinite suffixes. This connects finite holes with the forced
periodic continuation argument.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail
open Holes
variable {α Q : Type*}

/-- A finite prefix of an infinite spelling. -/
def streamPrefix (W : ℕ → α) (n : ℕ) : List α := List.ofFn (fun i : Fin n => W i)

@[simp] theorem streamPrefix_length (W : ℕ → α) (n : ℕ) :
    (streamPrefix W n).length = n := by simp [streamPrefix]

@[simp] theorem streamPrefix_get (W : ℕ → α) {n i : ℕ} (hi : i < n) :
    (streamPrefix W n)[i]? = some (W i) := by simp [streamPrefix, hi]

theorem streamPrefix_take (W : ℕ → α) {n k : ℕ} (hk : k ≤ n) :
    (streamPrefix W n).take k = streamPrefix W k := by
  apply List.ext_getElem
  · simp [hk]
  · intro i h1 h2
    simp [streamPrefix]

/-- No admitted pair has identical infinite suffixes. -/
def NoInfiniteAdmission (M : DFA α Q) (R : Q → Q → Prop) (W : ℕ → α) : Prop :=
  ∀ s e, s < e → R (M.eval (streamPrefix W s)) (M.eval (streamPrefix W e)) →
    ¬ ∀ k, e ≤ k → W (k-(e-s)) = W k

/-- The full-block argument without Fine--Wilf or a primitive-period
assumption. Backward induction by the eventual period propagates equality. -/
theorem finite_comparison_extends (W : ℕ → α) {n J d s e : ℕ}
    (hd : 0 < d) (hse : s < e) (he : e ≤ J)
    (hper : ∀ k, n ≤ k → W (k+d) = W k)
    (hfin : ∀ k, e ≤ k → k < n+J+d → W (k-(e-s)) = W k) :
    ∀ k, e ≤ k → W (k-(e-s)) = W k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hek
    by_cases hk : k < n+J+d
    · exact hfin k hek hk
    · have hk' : k-d < k := by omega
      have hh := ih (k-d) hk' (by omega)
      have h1 := hper (k-d) (by omega)
      have h2 := hper (k-d-(e-s)) (by omega)
      have h3 : k-d+d = k := by omega
      have h4 : k-d-(e-s)+d = k-(e-s) := by omega
      rw [h3] at h1
      rw [h4] at h2
      exact h2.trans (hh.trans h1.symm)

theorem periodic_truncation (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    (hc : AdmissionCone M R T) (W : ℕ → α) {n J d : ℕ}
    (hd : 0 < d) (hper : ∀ k, n ≤ k → W (k+d) = W k)
    (hclear : NoInfiniteAdmission M R W)
    (ht : M.eval (streamPrefix W (n+J+d)) ∈ T)
    (hJ : IsFirstRejectedPrefix M T (streamPrefix W (n+J+d)) J) :
    IsReaderHole M R T (streamPrefix W (n+J+d)) ∧
      (streamPrefix W (n+J+d)).length-J = n+d := by
  refine ⟨(isReaderHole_iff M R T _).mpr ⟨ht, ?_⟩, by simp; omega⟩
  intro s e hse he hp hr
  have heJ := hc _ J ht hJ s e hse he hp hr
  have heL : e ≤ n+J+d := by simpa using he
  have hsL : s ≤ n+J+d := by omega
  have hrel : R (M.eval (streamPrefix W s)) (M.eval (streamPrefix W e)) := by
    simpa only [streamPrefix_take W hsL, streamPrefix_take W heL] using hr
  apply hclear s e hse hrel
  apply finite_comparison_extends W hd hse heJ hper
  intro k hek hk
  have hh := comparison_letters hse hek (by simpa using hk) hp
  have hk' : k-(e-s) < n+J+d := by omega
  simpa only [streamPrefix_get W hk', streamPrefix_get W hk, Option.some.injEq] using hh
end DeciNSSE.RejectedTail
