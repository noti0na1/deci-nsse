import DeciNSSE.Complexity.RejectionSolutions
import DeciNSSE.Complexity.FiniteTrees
import DeciNSSE.Semantics.Characterization

/-! # Finite countermodels of the rejection system

Let all states of the binary automaton `A` be final, and let `A` accept the empty
word but not a prefix `u` of the binary word `w`. A finite solution of
`rejectionSystem n A` of depth `h = |w| + 1` takes for `x` the path tree of `w`,
for `g` the full binary tree of depth `h`, and for `Y_q` and `y` the truncations
at depth `h` of the languages accepted from `q` and by `A` (`FiniteTrees.trunc`).
In it, `x` is a constructor along `w` and `y` is bottom at `u`, so `w` is right
unsafe (`unsafe_of_not_accepts`). One finite countermodel thus refutes entailment
over finite, regular and arbitrary trees.

For the language of the words without the prefix `W`, with `W` nonempty, the
unsafe words are exactly the binary words that extend `W`, all on the right side
(`unsafe_iff`).

## Main declarations
- `Rejection.counterValuation`, `Rejection.sat_counterValuation`
- `Rejection.unsafe_of_not_accepts`, `Rejection.unsafe_iff`
- `Rejection.satisfiableFin_rejectionSystem`, `Rejection.satisfiable_rejectionSystem`
- `Rejection.not_entailsFin_rejectionSystem`, `Rejection.not_entailsReg_rejectionSystem`,
  `Rejection.not_entails_rejectionSystem`
-/

namespace DeciNSSE.Complexity.Rejection

open Safety Directions FiniteTrees

variable {n m : ℕ}

section Countermodel

variable (hn : 2 ≤ n) (A : BinNFA m)

/-- The images of the words accepted from `q`. -/
def stateLang (q : Fin m) (σ : List (Fin n)) : Prop :=
  ∃ u, A.AcceptsFrom q u ∧ σ = u.map (embedDir hn)

/-- The images of the words accepted by `A`. -/
def lang (σ : List (Fin n)) : Prop :=
  ∃ u, A.Accepts u ∧ σ = u.map (embedDir hn)

/-- The finite countermodel for the binary word `w`, of depth `|w| + 1`. -/
noncomputable def counterValuation (w : List (Fin 2)) : V (m + 4) → FTree n :=
  valuation (pathTree (w.map (embedDir hn))) (trunc (lang hn A) (w.length + 1))
    (fullBinary (w.length + 1)) .bot
    (fun q => trunc (stateLang hn A q) (w.length + 1))

/-- If all states are final and `A` accepts the empty word, the countermodel is a
solution. -/
theorem sat_counterValuation (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    (w : List (Fin 2)) :
    Covariant.Sat (FTree.toTree ∘ counterValuation hn A w) (rejectionSystem n A) := by
  rw [covSat_rejectionSystem_iff]
  simp only [Function.comp_apply, node_binaryChildren_toTree, node_letterChildren_toTree,
    FTree.toTree_le_iff]
  simp only [counterValuation, valuation_xVar, valuation_yVar, valuation_gVar,
    valuation_bVar, valuation_stateVar, FTree.toTree_bot, true_and]
  have hstate : ∀ q, stateLang hn A q [] :=
    fun q => ⟨[], (A.acceptsFrom_nil q).mpr (hfin q), rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `g` is the full binary tree
    rw [← fullBinary_succ]
    exact fullBinary_mono (Nat.le_succ _)
  · -- `x` is the path tree of `w`
    rw [← fullBinary_succ]
    refine pathTree_le_fullBinary (by simp only [List.length_map]; omega) ?_
    intro i hi
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hi
    exact a.isLt
  · exact node_bot_le_trunc ⟨[], hnil, rfl⟩ _
  · exact fun q => node_bot_le_trunc (hstate q) _
  · intro q a r ht
    refine node_letterChildren_le_trunc hn (hstate q) a ?_ _
    rintro σ ⟨u, hu, rfl⟩
    exact ⟨a :: u, A.acceptsFrom_cons ht hu, rfl⟩
  · intro q a r ht hq
    refine node_letterChildren_le_trunc hn ⟨[], hnil, rfl⟩ a ?_ _
    rintro σ ⟨u, hu, rfl⟩
    exact ⟨a :: u, ⟨q, hq, A.acceptsFrom_cons ht hu⟩, rfl⟩

variable {A}

/-- In the countermodel, `x` is a constructor along `w`, and `y` is bottom along `w` if `A`
rejects a prefix of `w`. -/
theorem trace_counterValuation {u w : List (Fin 2)} (hu : ¬ A.Accepts u) (huw : u <+: w) :
    trace (counterValuation hn A w xVar).toTree (w.map (embedDir hn)) ≠ Tree.bot ∧
      trace (counterValuation hn A w yVar).toTree (w.map (embedDir hn)) = Tree.bot := by
  simp only [counterValuation, valuation_xVar, valuation_yVar, trace_pathTree]
  refine ⟨by simp, ?_⟩
  obtain ⟨v, rfl⟩ := huw
  rw [List.map_append, trace_append, trace_trunc_of_not_mem (by simp; omega), trace_bot]
  rintro ⟨u', hu', he⟩
  rw [List.map_injective_iff.mpr (embedDir_injective hn) he] at hu
  exact hu hu'

/-- If all states are final and `A` accepts the empty word but not the prefix `u` of `w`,
then `w` is right unsafe. -/
theorem unsafe_of_not_accepts (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    {u w : List (Fin 2)} (hu : ¬ A.Accepts u) (huw : u <+: w) :
    Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar .r (w.map (embedDir hn)) := by
  obtain ⟨hx, hy⟩ := trace_counterValuation hn hu huw
  exact ⟨_, (sat_false _ _).mpr (sat_counterValuation hn A hfin hnil w),
    (prefBot_false_iff _ _).mpr hy, fun h => hx ((prefBot_false_iff _ _).mp h)⟩

include hn in
/-- Under the same conditions, the finite countermodel refutes entailment over finite
trees. -/
theorem not_entailsFin_of_not_accepts (hfin : ∀ q, A.final q = true) (hnil : A.Accepts [])
    {u : List (Fin 2)} (hu : ¬ A.Accepts u) :
    ¬ EntailsFin (fun _ => false) (rejectionSystem n A) xVar yVar := by
  intro h
  have hle := (treeLe_false_iff_le _ _).mp
    (h _ ((sat_false _ _).mpr (sat_counterValuation hn A hfin hnil u)))
  obtain ⟨hx, hy⟩ := trace_counterValuation hn hu (List.prefix_refl u)
  exact hx ((Tree.le_bot_iff _).mp (hy ▸ trace_mono hle _))

end Countermodel

/-- The system always has a finite solution: `x`, `g` and `b` bottom, `y` and all `Y_q`
top. -/
theorem satisfiableFin_rejectionSystem (A : BinNFA m) :
    SatisfiableFin (fun _ => false) (rejectionSystem n A) := by
  refine ⟨valuation .bot .top .bot .bot fun _ => .top, ?_⟩
  rw [sat_false, covSat_rejectionSystem_iff]
  simp

/-- The system always has a solution. -/
theorem satisfiable_rejectionSystem (A : BinNFA m) :
    Satisfiable (fun _ => false) (rejectionSystem n A) :=
  let ⟨_, hσ⟩ := satisfiableFin_rejectionSystem A
  ⟨_, hσ⟩

section Language

variable (hn : 2 ≤ n) {A : BinNFA m} {W : List (Fin 2)} (hfin : ∀ q, A.final q = true)
  (hW : W ≠ []) (hA : ∀ u, A.Accepts u ↔ ¬ W <+: u)
include hn hfin hW hA

/-- Every binary word that extends `W` is right unsafe. -/
theorem unsafe_append (v : List (Fin 2)) :
    Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar .r ((W ++ v).map (embedDir hn)) :=
  unsafe_of_not_accepts hn hfin ((hA []).mpr fun h => hW (List.prefix_nil.mp h))
    (fun h => (hA W).mp h (List.prefix_refl W)) (List.prefix_append W v)

/-- The word `W` is right unsafe. -/
theorem unsafe_word :
    Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar .r (W.map (embedDir hn)) := by
  simpa using unsafe_append hn hfin hW hA []

/-- The unsafe words are exactly the binary words that extend `W`, all on the right
side. -/
theorem unsafe_iff (θ : Side) (w : List (Fin n)) :
    Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (embedDir hn) := by
  constructor
  · intro h
    obtain ⟨rfl, u, hu, rfl⟩ := exists_of_unsafe hn h
    obtain ⟨v, rfl⟩ : W <+: u := by
      by_contra h
      exact hu ((hA u).mpr h)
    exact ⟨rfl, v, rfl⟩
  · rintro ⟨rfl, v, rfl⟩
    exact unsafe_append hn hfin hW hA v

/-- Entailment fails over finite trees. -/
theorem not_entailsFin_rejectionSystem :
    ¬ EntailsFin (fun _ => false) (rejectionSystem n A) xVar yVar :=
  not_entailsFin_of_not_accepts hn hfin ((hA []).mpr fun h => hW (List.prefix_nil.mp h))
    (fun h => (hA W).mp h (List.prefix_refl W))

/-- Entailment fails over regular trees. -/
theorem not_entailsReg_rejectionSystem :
    ¬ EntailsReg (fun _ => false) (rejectionSystem n A) xVar yVar :=
  fun h => not_entailsFin_rejectionSystem hn hfin hW hA
    (Characterization.entailsReg_toFin _ _ _ _ h)

/-- Entailment fails over arbitrary trees. -/
theorem not_entails_rejectionSystem :
    ¬ Entails (fun _ => false) (rejectionSystem n A) xVar yVar :=
  fun h => not_entailsReg_rejectionSystem hn hfin hW hA
    (Characterization.entails_toReg _ _ _ _ h)

end Language

end DeciNSSE.Complexity.Rejection
