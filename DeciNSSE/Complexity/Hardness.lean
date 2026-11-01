import DeciNSSE.Complexity.HardnessCountermodel

/-! # Entailment decides universality of binary automata

For every arity `n ≥ 2` and the covariant constructor, the entailment `x ≤ r`
from `hardnessSystem n M` holds exactly when the binary automaton `M` accepts
every word, over arbitrary, regular and finite trees alike. A universal `M`
gives entailment over arbitrary trees, hence over the other two domains; a
rejected word gives a finite countermodel, hence one in all three domains.

For `m` states and `T` transitions the system has `m + T + 6` variables and at
most `2 m + 2 T + 4` literals (`hardnessSystem_length_le`), and it is always
satisfiable. Universality of nondeterministic automata is PSPACE-hard, so
entailment is PSPACE-hard for every fixed arity at least two, in each domain.

## Main declarations
- `entails_hardnessSystem_iff`, `entailsReg_hardnessSystem_iff`,
  `entailsFin_hardnessSystem_iff`
- `hardnessSystem_satisfiable`
-/

namespace DeciNSSE.Complexity

open Hardness Characterisation

variable {n m : ℕ}

/-- Over finite trees, entailment holds exactly for universal automata. -/
theorem entailsFin_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    EntailsFin (fun _ => false) (hardnessSystem n M) (xVar M) (rVar M) ↔
      ∀ w, M.Accepts w :=
  ⟨fun h w => Classical.byContradiction fun hw : ¬ M.Accepts w =>
      not_entailsFin_of_not_accepts hn M hw h,
    fun h => entailsReg_toFin _ _ _ _ (entails_toReg _ _ _ _ (entails_of_universal hn h))⟩

/-- Over regular trees, entailment holds exactly for universal automata. -/
theorem entailsReg_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    EntailsReg (fun _ => false) (hardnessSystem n M) (xVar M) (rVar M) ↔
      ∀ w, M.Accepts w :=
  ⟨fun h => (entailsFin_hardnessSystem_iff hn M).mp (entailsReg_toFin _ _ _ _ h),
    fun h => entails_toReg _ _ _ _ (entails_of_universal hn h)⟩

/-- Over arbitrary trees, entailment holds exactly for universal automata. -/
theorem entails_hardnessSystem_iff (hn : 2 ≤ n) (M : BinNFA m) :
    Entails (fun _ => false) (hardnessSystem n M) (xVar M) (rVar M) ↔
      ∀ w, M.Accepts w :=
  ⟨fun h => (entailsReg_hardnessSystem_iff hn M).mp (entails_toReg _ _ _ _ h),
    entails_of_universal hn⟩

/-- The system always has a solution, so no entailment holds vacuously. -/
theorem hardnessSystem_satisfiable (M : BinNFA m) :
    Satisfiable (fun _ => false) (hardnessSystem n M) := by
  refine ⟨valuation M ![Tree.bot, Tree.bot, Tree.bot, Tree.top, Tree.top,
    Tree.node fun _ => Tree.bot] (fun _ => Tree.bot) (fun _ => Tree.bot), ?_⟩
  rw [sat_false, covSat_hardnessSystem_iff]
  simp [comp_kids, kids, xVar, dVar, bVar, rVar, rVar', zVar]

namespace Hardness

/-- The one-state automaton with a loop on each letter, accepting every word. -/
def allWords : BinNFA 1 := ⟨fun _ => true, fun _ => true, [(0, 0, 0), (0, 1, 0)]⟩

/-- The one-state automaton without transitions, accepting only the empty word. -/
def onlyEmpty : BinNFA 1 := ⟨fun _ => true, fun _ => true, []⟩

theorem allWords_accepts (w : List (Fin 2)) : allWords.Accepts w := by
  refine ⟨0, rfl, 0, rfl, ?_⟩
  induction w with
  | nil => rfl
  | cons a w ih => exact ⟨0, by fin_cases a <;> simp [allWords], ih⟩

theorem onlyEmpty_rejects : ¬ onlyEmpty.Accepts [0] := by
  rintro ⟨_, -, _, -, _, h, -⟩
  simp [onlyEmpty] at h

/-- For the universal automaton, entailment holds over arbitrary trees. -/
example : Entails (fun _ => false) (hardnessSystem 2 allWords) (xVar allWords) (rVar allWords) :=
  (entails_hardnessSystem_iff le_rfl allWords).mpr allWords_accepts

/-- For an automaton rejecting `0`, entailment fails already over finite trees. -/
example : ¬ EntailsFin (fun _ => false) (hardnessSystem 3 onlyEmpty)
    (xVar onlyEmpty) (rVar onlyEmpty) :=
  fun h => onlyEmpty_rejects ((entailsFin_hardnessSystem_iff (by norm_num) onlyEmpty).mp h [0])

end Hardness

end DeciNSSE.Complexity
