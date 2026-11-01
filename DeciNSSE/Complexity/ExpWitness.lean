import DeciNSSE.Complexity.RejectionCertificates
import DeciNSSE.Complexity.CounterBinary
import DeciNSSE.Solver

/-! # Exponentially long witnesses

The counter automaton `Counter.counterNFA k` has `9 k + 27` states, all final,
and accepts exactly the binary words without the prefix `Counter.counterWord k`,
of length `2 (k + 1) 2^k`. Its rejection system `expSystem n k`, for a covariant
constructor of arity `n ≥ 2`, has `9 k + 31` variables and at most `81 k + 247`
literals, and it has finite solutions.

Its unsafe words are exactly the binary words that extend `counterWord k`, all on
the right side. So entailment fails over finite, regular and arbitrary trees,
and every counterexample word has length at least `2 (k + 1) 2^k`: every hole of
a side monitor, every word passing `refutesB`, and the word of every refutation
accepted by the solver's packed checker, in particular of every answer of the
solver. The word `counterWord k` attains the bound. With `K = 9 k + 31`
variables, the shortest holes thus have length at least `2^((K - 22) / 9)`,
exponential in `K`, for every fixed arity `n ≥ 2`
(`two_pow_le_length_counterWord`).

## Main declarations
- `expSystem`, `expSystem_length_le`, `satisfiableFin_expSystem`,
  `two_pow_le_length_counterWord`
- `expSystem_unsafe_iff`, `expSystem_hole_iff`
- `expSystem_hole_length`, `expSystem_shortest_hole`, `expSystem_shortest_refutesB`
- `expSystem_checkRefutationPacked_length`, `expSystem_result`
- `not_entails_expSystem`, `not_entailsReg_expSystem`, `not_entailsFin_expSystem`
-/

namespace DeciNSSE.Complexity

open Rejection Counter Directions

/-- The rejection system of the counter automaton, with `9 k + 31` variables. -/
def expSystem (n k : ℕ) : Constraint n (9 * k + 31) := rejectionSystem n (counterNFA k)

variable {n : ℕ} (hn : 2 ≤ n) (k : ℕ)

/-- The system has at most `81 k + 247` literals. -/
theorem expSystem_length_le : (expSystem n k).length ≤ 81 * k + 247 := by
  have := rejectionSystem_length_le n (counterNFA k)
  have := length_trans_counterNFA_le k
  simp only [expSystem]
  omega

/-- The length `2 (k + 1) 2^k` of the counter word is exponential in the number
`K = 9 k + 31` of variables: it is at least `2^((K - 22) / 9)`. -/
theorem two_pow_le_length_counterWord :
    2 ^ ((9 * k + 31 - 22) / 9) ≤ (counterWord k).length := by
  rw [length_counterWord, show (9 * k + 31 - 22) / 9 = k + 1 by omega, pow_succ]
  calc 2 ^ k * 2 = 2 * 1 * 2 ^ k := by ring
    _ ≤ 2 * (k + 1) * 2 ^ k := by gcongr; omega

/-- The system has a finite solution. -/
theorem satisfiableFin_expSystem : SatisfiableFin (fun _ => false) (expSystem n k) :=
  satisfiableFin_rejectionSystem _

/-- The unsafe words are exactly the binary words that extend the counter word, all on the
right side. -/
theorem expSystem_unsafe_iff (θ : Side) (w : List (Fin n)) :
    Unsafe (fun _ => false) (expSystem n k) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = (counterWord k ++ v).map (embedDir hn) :=
  unsafe_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff θ w

/-- The left monitor has no hole, and the holes of the right monitor are exactly the binary
words that extend the counter word. -/
theorem expSystem_hole_iff (θ : Side) (w : List (Fin n)) :
    (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w ↔
      θ = .r ∧ ∃ v, w = (counterWord k ++ v).map (embedDir hn) :=
  hole_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff θ w

include hn in
/-- Every hole of a side monitor has length at least `2 (k + 1) 2^k`. -/
theorem expSystem_hole_length {θ : Side} {w : List (Fin n)}
    (hw : (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w) :
    2 * (k + 1) * 2 ^ k ≤ w.length := by
  simpa [length_counterWord] using
    (prefix_of_hole hn (fun u => (counterNFA_accepts_iff u).mpr) hw).length_le

include hn in
/-- The shortest holes of the side monitors have length `2 (k + 1) 2^k`. -/
theorem expSystem_shortest_hole :
    IsLeast {ℓ | ∃ θ w,
      (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w ∧
        w.length = ℓ} (2 * (k + 1) * 2 ^ k) := by
  refine ⟨⟨.r, (counterWord k).map (embedDir hn),
    (expSystem_hole_iff hn k _ _).mpr ⟨rfl, [], by simp⟩, by simp [length_counterWord]⟩, ?_⟩
  rintro ℓ ⟨θ, w, hw, rfl⟩
  exact expSystem_hole_length hn k hw

include hn in
/-- The shortest words passing the Boolean certificate check have length `2 (k + 1) 2^k`. -/
theorem expSystem_shortest_refutesB :
    IsLeast {ℓ | ∃ θ w, refutesB (fun _ => false) (expSystem n k) xVar yVar θ w = true ∧
      w.length = ℓ} (2 * (k + 1) * 2 ^ k) := by
  refine ⟨⟨.r, (counterWord k).map (embedDir hn), ?_, by simp [length_counterWord]⟩, ?_⟩
  · exact (refutesB_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff
      _ _).mpr ⟨rfl, [], by simp⟩
  · rintro ℓ ⟨θ, w, hw, rfl⟩
    simpa [length_counterWord] using
      (prefix_of_refutesB hn (fun u => (counterNFA_accepts_iff u).mpr) hw).length_le

include hn in
/-- The word of every refutation accepted by the solver's packed checker has length at
least `2 (k + 1) 2^k`. -/
theorem expSystem_checkRefutationPacked_length {cert : Certificates.Refutation n}
    (h : Solver.Checked.checkRefutationPacked (fun _ => false) (expSystem n k) xVar yVar cert =
      true) :
    2 * (k + 1) * 2 ^ k ≤ cert.word.length := by
  simpa [length_counterWord] using
    (prefix_of_checkRefutationPacked hn (fun u => (counterNFA_accepts_iff u).mpr) h).length_le

include hn in
/-- Entailment fails over finite trees. -/
theorem not_entailsFin_expSystem : ¬ EntailsFin (fun _ => false) (expSystem n k) xVar yVar :=
  not_entailsFin_rejectionSystem hn counterNFA_final (counterWord_ne_nil k)
    counterNFA_accepts_iff

include hn in
/-- Entailment fails over regular trees. -/
theorem not_entailsReg_expSystem : ¬ EntailsReg (fun _ => false) (expSystem n k) xVar yVar :=
  not_entailsReg_rejectionSystem hn counterNFA_final (counterWord_ne_nil k)
    counterNFA_accepts_iff

include hn in
/-- Entailment fails over arbitrary trees. -/
theorem not_entails_expSystem : ¬ Entails (fun _ => false) (expSystem n k) xVar yVar :=
  not_entails_rejectionSystem hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff

include hn in
/-- Every result of the solver, for any search budget, is a refutation, and its word has
length at least `2 (k + 1) 2^k`. -/
theorem expSystem_result (r : Result (fun _ => false) (expSystem n k) xVar yVar) :
    ∃ cert h model, r.evidence = .refuted cert h model ∧
      2 * (k + 1) * 2 ^ k ≤ cert.word.length := by
  rcases r with ⟨e, fallback⟩
  cases e with
  | entailed cert h =>
    exact absurd (Solver.Checked.checkEntailmentPacked_sound _ _ _ _ cert h)
      (not_entails_expSystem hn k)
  | complete h =>
    exact absurd ((decideEntails_correct _ _ _ _).mp h) (not_entails_expSystem hn k)
  | refuted cert h model =>
    exact ⟨cert, h, model, rfl, expSystem_checkRefutationPacked_length hn k h⟩

end DeciNSSE.Complexity
