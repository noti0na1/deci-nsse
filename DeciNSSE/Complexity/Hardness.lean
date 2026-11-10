import DeciNSSE.Complexity.AllFinalCode
import DeciNSSE.Complexity.RejectionCountermodel

/-! # Entailment decides universality of binary automata

For every arity `n ≥ 2` and the covariant constructor, the entailment `x ≤ y`
from `hardnessSystem n M` holds exactly when the binary automaton `M` accepts
every word, over arbitrary, regular and finite trees alike. The system is the
rejection system of `allFinalCode M`: universality rules out unsafe words, and a
rejected word gives a finite countermodel.

For `m` states and `T` transitions the system has `2 m + 7` variables and at most
`6 m + 2 T + 17` literals. It is always satisfiable. Universality of binary
nondeterministic automata therefore reduces to entailment at every fixed arity
at least two, in each domain.

## Main declarations
- `hardnessSystem`, `Hardness.numVars_eq`, `hardnessSystem_length_le`
- `entails_hardnessSystem_iff`, `entailsReg_hardnessSystem_iff`,
  `entailsFin_hardnessSystem_iff`
- `satisfiable_hardnessSystem`
-/

namespace DeciNSSE.Complexity

variable {n m : ℕ}

namespace Hardness

/-- Four rejection-system variables in addition to the `2 m + 3` states of the all-final
encoding. -/
abbrev numVars (_M : BinNFA m) : ℕ := 2 * m + 7

/-- The variable count depends only on the source state count. -/
theorem numVars_eq (M : BinNFA m) : numVars M = 2 * m + 7 := rfl

/-- The left side of the query is the rejection system's variable `x`. -/
abbrev xVar (M : BinNFA m) : V (numVars M) := Rejection.xVar

/-- The right side of the query is the rejection system's variable `y`. -/
abbrev yVar (M : BinNFA m) : V (numVars M) := Rejection.yVar

end Hardness

open Hardness Characterization

/-- The rejection system of the all-final encoding, with the query `x ≤ y`. -/
def hardnessSystem (n : ℕ) (M : BinNFA m) : Constraint n (Hardness.numVars M) :=
  rejectionSystem n (allFinalCode M)

/-- The system has at most `6 m + 2 T + 17` literals for `m` states and `T` transitions. -/
theorem hardnessSystem_length_le (n : ℕ) (M : BinNFA m) :
    (hardnessSystem n M).length ≤ 6 * m + 2 * M.trans.length + 17 := by
  have := rejectionSystem_length_le n (allFinalCode M)
  have := allFinalCode_length_trans_le M
  change (rejectionSystem n (allFinalCode M)).length ≤ _
  omega

/-- Over arbitrary trees, entailment holds exactly for universal automata. -/
theorem entails_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    Entails (fun _ => false) (hardnessSystem n M) (xVar M) (yVar M) ↔
      ∀ w, M.Accepts w := by
  rw [← allFinalCode_universal_iff]
  constructor
  · intro he u
    by_contra hu
    exact Rejection.not_entailsFin_of_not_accepts hn (allFinalCode_final M)
      (allFinalCode_accepts_nil M) hu (fun σ hσ => he _ hσ)
  · intro ha
    rw [entails_iff_not_sideUnsafe]
    intro θ w hw
    obtain ⟨-, u, hu, -⟩ := Rejection.exists_of_unsafe hn hw
    exact hu (ha u)

/-- Over finite trees, entailment holds exactly for universal automata. -/
theorem entailsFin_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    EntailsFin (fun _ => false) (hardnessSystem n M) (xVar M) (yVar M) ↔
      ∀ w, M.Accepts w := by
  constructor
  · intro he
    apply (allFinalCode_universal_iff M).mp
    intro u
    by_contra hu
    exact Rejection.not_entailsFin_of_not_accepts hn (allFinalCode_final M)
      (allFinalCode_accepts_nil M) hu he
  · intro ha σ hσ
    exact (entails_hardnessSystem_iff hn M).mpr ha _ hσ

/-- Over regular trees, entailment holds exactly for universal automata. -/
theorem entailsReg_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    EntailsReg (fun _ => false) (hardnessSystem n M) (xVar M) (yVar M) ↔
      ∀ w, M.Accepts w :=
  ⟨fun he => (entailsFin_hardnessSystem_iff hn M).mp (entailsReg_toFin _ _ _ _ he),
    fun ha => entails_toReg _ _ _ _ ((entails_hardnessSystem_iff hn M).mpr ha)⟩

/-- The system always has a solution, so no entailment holds vacuously. -/
theorem satisfiable_hardnessSystem (M : BinNFA m) :
    Satisfiable (fun _ => false) (hardnessSystem n M) :=
  Rejection.satisfiable_rejectionSystem (allFinalCode M)

section Examples

/-- The one-state automaton with a loop on each letter, accepting every word. -/
private def allWords : BinNFA 1 := ⟨fun _ => true, fun _ => true, [(0, 0, 0), (0, 1, 0)]⟩

/-- The one-state automaton without transitions, accepting only the empty word. -/
private def onlyEmpty : BinNFA 1 := ⟨fun _ => true, fun _ => true, []⟩

private theorem allWords_accepts (w : List (Fin 2)) : allWords.Accepts w := by
  refine ⟨0, rfl, 0, rfl, ?_⟩
  induction w with
  | nil => rfl
  | cons a w ih => exact ⟨0, by fin_cases a <;> simp [allWords], ih⟩

private theorem onlyEmpty_rejects : ¬ onlyEmpty.Accepts [0] := by
  rintro ⟨_, -, _, -, _, h, -⟩
  simp [onlyEmpty] at h

/-- For the universal automaton, entailment holds over arbitrary trees. -/
example : Entails (fun _ => false) (hardnessSystem 2 allWords) (xVar allWords) (yVar allWords) :=
  (entails_hardnessSystem_iff le_rfl allWords).mpr allWords_accepts

/-- For an automaton rejecting `0`, entailment fails already over finite trees. -/
example : ¬ EntailsFin (fun _ => false) (hardnessSystem 3 onlyEmpty)
    (xVar onlyEmpty) (yVar onlyEmpty) :=
  fun h => onlyEmpty_rejects ((entailsFin_hardnessSystem_iff (by norm_num) onlyEmpty).mp h [0])

end Examples

end DeciNSSE.Complexity
