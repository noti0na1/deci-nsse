import DeciNSSE.Complexity.WitnessSemantics
import DeciNSSE.Complexity.CounterBinary
import DeciNSSE.Solver

/-! # Exponentially long witnesses

The counter automaton `Counter.counterNFA k` has `9 k + 27` states, all final,
and accepts exactly the binary words without the prefix `Counter.counterWord k`,
of length `2 (k + 1) 2^k`. Its witness system `expSystem n k`, for a covariant
constructor of arity `n ≥ 2`, has `9 k + 31` variables and at most `81 k + 247`
literals, and it has finite solutions.

Its unsafe words are exactly the binary words that extend `counterWord k`, all on
the right side. So entailment fails over finite, regular and arbitrary trees,
and every counterexample word has length at least `2 (k + 1) 2^k`: every hole of
a side monitor, every word passing `refutesB`, and the word of every refutation
accepted by the solver's checker, in particular of every answer of the solver.
The word `counterWord k` attains the bound. With `K = 9 k + 31` variables, the
shortest holes thus have length at least `2^((K - 22) / 9)`, exponential in `K`,
for every fixed arity `n ≥ 2` (`two_pow_le_expBound`).

## Main declarations
- `expSystem`, `expSystem_length_le`, `satisfiableFin_expSystem`, `two_pow_le_expBound`
- `expSystem_unsafe_iff`, `expSystem_hole_iff`
- `expSystem_hole_length`, `expSystem_shortest_hole`, `expSystem_shortest`
- `expSystem_checkRefutation`, `expSystem_result`
- `not_entails_expSystem`, `not_entailsReg_expSystem`, `not_entailsFin_expSystem`
-/

set_option autoImplicit false

namespace DeciNSSE.Complexity

open Witness Counter
open Hardness (dir)

namespace Counter

variable (k : ℕ)

/-- The counter word is not empty. -/
theorem counterWord_ne_nil : counterWord k ≠ [] := by
  intro h
  have hlen := length_counterWord (k := k)
  rw [h, List.length_nil] at hlen
  have : 0 < 2 * (k + 1) * 2 ^ k := by positivity
  omega

/-- A list of lists, each of length at most `c`, flattens to at most `c` times its length. -/
theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) {c : ℕ}
    (h : ∀ x ∈ l, (f x).length ≤ c) : (l.flatMap f).length ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h a List.mem_cons_self
    omega

variable {k}

/-- A token state has at most two successors on each token. -/
theorem length_next_le (q : St k) (t : Tok) : (next k q t).length ≤ 2 := by
  cases q <;> cases t <;> simp only [next] <;> (try split_ifs) <;> simp

/-- A binary state has at most two successors on each bit. -/
theorem length_binNext_le (p : BinSt k) (a : Fin 2) : (binNext k p a).length ≤ 2 := by
  obtain ⟨q, _ | b⟩ := p
  · simp [binNext]
  · simpa [binNext] using length_next_le q (tok b a)

variable (k)

/-- The counter automaton has at most `36 k + 108` transitions. -/
theorem length_trans_counterNFA_le : (counterNFA k).trans.length ≤ 36 * k + 108 := by
  have hall : (allStates k).length ≤ 3 * k + 9 := by
    have := length_flatMap_le (List.finRange (k + 1))
      (fun j => [St.wait false j, St.wait true j]) (c := 2) fun _ _ => le_rfl
    simp only [allStates, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_finRange] at this ⊢
    omega
  have hbin : (binStates k).length ≤ 9 * k + 27 :=
    (length_flatMap_le (allStates k) (fun q => [(q, none), (q, some 0), (q, some 1)])
      (c := 3) fun _ _ => le_rfl).trans (by omega)
  show ((binStates k).flatMap fun p => (List.finRange 2).flatMap fun a =>
    (binNext k p a).map fun q => (binIndex k p, a, binIndex k q)).length ≤ _
  refine (length_flatMap_le _ _ (c := 4) fun p _ => ?_).trans (by omega)
  refine (length_flatMap_le _ _ (c := 2) fun a _ => ?_).trans (by simp)
  rw [List.length_map]
  exact length_binNext_le p a

end Counter

/-- The witness system of the counter automaton, with `9 k + 31` variables. -/
def expSystem (n k : ℕ) : Constraint n (9 * k + 31) := witnessSystem n (counterNFA k)

variable {n : ℕ} (hn : 2 ≤ n) (k : ℕ)

/-- The system has at most `81 k + 247` literals. -/
theorem expSystem_length_le : (expSystem n k).length ≤ 81 * k + 247 := by
  have := witnessSystem_length_le n (counterNFA k)
  have := length_trans_counterNFA_le k
  simp only [expSystem]
  omega

/-- The length `2 (k + 1) 2^k` is exponential in the number `K = 9 k + 31` of variables: it
is at least `2^((K - 22) / 9)`. -/
theorem two_pow_le_expBound : 2 ^ ((9 * k + 31 - 22) / 9) ≤ 2 * (k + 1) * 2 ^ k := by
  rw [show (9 * k + 31 - 22) / 9 = k + 1 by omega, pow_succ]
  calc 2 ^ k * 2 = 2 * 1 * 2 ^ k := by ring
    _ ≤ 2 * (k + 1) * 2 ^ k := by gcongr; omega

/-- The system has a finite solution. -/
theorem satisfiableFin_expSystem : SatisfiableFin (fun _ => false) (expSystem n k) :=
  satisfiableFin_witness _

/-- The unsafe words are exactly the binary words that extend the counter word, all on the
right side. -/
theorem expSystem_unsafe_iff (θ : Side) (w : List (Fin n)) :
    Unsafe (fun _ => false) (expSystem n k) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = (counterWord k ++ v).map (dir hn) :=
  unsafe_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff θ w

/-- The left monitor has no hole, and the holes of the right monitor are exactly the binary
words that extend the counter word. -/
theorem expSystem_hole_iff (θ : Side) (w : List (Fin n)) :
    (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w ↔
      θ = .r ∧ ∃ v, w = (counterWord k ++ v).map (dir hn) :=
  hole_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff θ w

include hn in
/-- Every hole of a side monitor has length at least `2 (k + 1) 2^k`. -/
theorem expSystem_hole_length {θ : Side} {w : List (Fin n)}
    (hw : (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w) :
    2 * (k + 1) * 2 ^ k ≤ w.length := by
  simpa [length_counterWord] using
    (hole_prefix hn (fun u => (counterNFA_accepts_iff u).mpr) hw).length_le

include hn in
/-- The shortest holes of the side monitors have length `2 (k + 1) 2^k`. -/
theorem expSystem_shortest_hole :
    IsLeast {ℓ | ∃ θ w,
      (Monitor.sideMonitor (fun _ => false) (expSystem n k) xVar yVar θ).Hole w ∧
        w.length = ℓ} (2 * (k + 1) * 2 ^ k) := by
  refine ⟨⟨.r, (counterWord k).map (dir hn),
    (expSystem_hole_iff hn k _ _).mpr ⟨rfl, [], by simp⟩, by simp [length_counterWord]⟩, ?_⟩
  rintro ℓ ⟨θ, w, hw, rfl⟩
  exact expSystem_hole_length hn k hw

include hn in
/-- The shortest words passing the Boolean certificate check have length `2 (k + 1) 2^k`. -/
theorem expSystem_shortest :
    IsLeast {ℓ | ∃ θ w, refutesB (fun _ => false) (expSystem n k) xVar yVar θ w = true ∧
      w.length = ℓ} (2 * (k + 1) * 2 ^ k) := by
  refine ⟨⟨.r, (counterWord k).map (dir hn), ?_, by simp [length_counterWord]⟩, ?_⟩
  · exact (refutesB_iff hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff
      _ _).mpr ⟨rfl, [], by simp⟩
  · rintro ℓ ⟨θ, w, hw, rfl⟩
    simpa [length_counterWord] using
      (refutesB_prefix hn (fun u => (counterNFA_accepts_iff u).mpr) hw).length_le

include hn in
/-- The word of every refutation accepted by the solver's checker has length at least
`2 (k + 1) 2^k`. -/
theorem expSystem_checkRefutation {cert : Certificates.Refutation n}
    (h : Solver.Checked.checkRefutation (fun _ => false) (expSystem n k) xVar yVar cert = true) :
    2 * (k + 1) * 2 ^ k ≤ cert.word.length := by
  simpa [length_counterWord] using
    (checkRefutation_prefix hn (fun u => (counterNFA_accepts_iff u).mpr) h).length_le

include hn in
/-- Entailment fails over finite trees. -/
theorem not_entailsFin_expSystem : ¬ EntailsFin (fun _ => false) (expSystem n k) xVar yVar :=
  not_entailsFin_witness hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff

include hn in
/-- Entailment fails over regular trees. -/
theorem not_entailsReg_expSystem : ¬ EntailsReg (fun _ => false) (expSystem n k) xVar yVar :=
  not_entailsReg_witness hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff

include hn in
/-- Entailment fails over arbitrary trees. -/
theorem not_entails_expSystem : ¬ Entails (fun _ => false) (expSystem n k) xVar yVar :=
  not_entails_witness hn counterNFA_final (counterWord_ne_nil k) counterNFA_accepts_iff

include hn in
/-- Every result of the solver, for any search budget, is a refutation, and its word has
length at least `2 (k + 1) 2^k`. -/
theorem expSystem_result (r : Result (fun _ => false) (expSystem n k) xVar yVar) :
    ∃ cert h model, r.evidence = .refuted cert h model ∧
      2 * (k + 1) * 2 ^ k ≤ cert.word.length := by
  rcases r with ⟨e, fallback⟩
  cases e with
  | entailed cert h =>
    exact absurd (Solver.Checked.checkEntailment_sound _ _ _ _ cert h) (not_entails_expSystem hn k)
  | complete h =>
    exact absurd ((decideEntails_correct _ _ _ _).mp h) (not_entails_expSystem hn k)
  | refuted cert h model => exact ⟨cert, h, model, rfl, expSystem_checkRefutation hn k h⟩

end DeciNSSE.Complexity
