import DeciNSSE.Complexity.HardnessSystem
import DeciNSSE.Complexity.FiniteTrees

/-! # A finite countermodel for a rejected word

Let `M` reject `w` and let `c = doublingCode w`. No prefix of `c` is the code of a
word accepted from an initial state, by prefix freeness. The finite solution:

- `x` is the path tree along `c`, with constructor positions the prefixes of `c`;
- `X_p` and `Y_t` are the binary trees of depth `|c| + 1` whose constructor paths
  have no prefix in the language of the corresponding state of the code
  automaton (`avoid`), and `d` is the full binary tree of that depth;
- `r` and `r'` are the approximants `rPair (2 |w| + 1)` of the greatest solution
  of their two literals; `r` is bottom at `c`, where `x` is a constructor.

So `x ≤ r` fails in a finite solution (`not_entailsFin_of_not_accepts`).

## Main declarations
- `Hardness.rPair`, `Hardness.counterValuation`
- `Hardness.not_entailsFin_of_not_accepts`
-/

namespace DeciNSSE.Complexity.Hardness

open Safety Directions FiniteTrees

variable {n m : ℕ}

section Approximants

/-- The approximants of `r` and `r'`: `(⊤, ⊤)`, then `(f(r', ⊥, …), f(r, r, ⊥, …))`. -/
def rPair : ℕ → FTree n × FTree n
  | 0 => (.top, .top)
  | h + 1 =>
    (.node (binaryChildren (rPair h).2 .bot .bot),
      .node (binaryChildren (rPair h).1 (rPair h).1 .bot))

/-- The approximants decrease. -/
theorem rPair_succ_le : ∀ h : ℕ,
    ((rPair (h + 1)).1 : FTree n) ≤ (rPair h).1 ∧ ((rPair (h + 1)).2 : FTree n) ≤ (rPair h).2
  | 0 => ⟨FTree.le_top _, FTree.le_top _⟩
  | h + 1 => by
    obtain ⟨h1, h2⟩ : ((rPair (h + 1)).1 : FTree n) ≤ (rPair h).1 ∧
      ((rPair (h + 1)).2 : FTree n) ≤ (rPair h).2 := rPair_succ_le h
    exact ⟨node_binaryChildren_mono h2 le_rfl le_rfl, node_binaryChildren_mono h1 h1 le_rfl⟩

/-- Along `e(w)`, the approximant of `r` loses two levels per letter. -/
theorem trace_rPair_doubling (hn : 2 ≤ n) : ∀ (w : List (Fin 2)) (h : ℕ),
    trace (rPair (h + 2 * w.length) : FTree n × FTree n).1.toTree (doubling hn w) =
      (rPair h).1.toTree
  | [], _ => rfl
  | a :: w, h => by
    rw [show h + 2 * (a :: w).length = h + 2 * w.length + 1 + 1 by simp; ring, doubling_cons,
      trace_cons, trace_cons]
    simp only [rPair, FTree.descend_toTree_node, binaryChildren_embedDir_zero]
    rw [show (binaryChildren (rPair (h + 2 * w.length)).1 (rPair (h + 2 * w.length)).1 FTree.bot
      (embedDir hn a) : FTree n) = (rPair (h + 2 * w.length)).1 by fin_cases a <;> simp]
    exact trace_rPair_doubling hn w h

end Approximants

section Countermodel

variable (hn : 2 ≤ n) (M : BinNFA m)

/-- The language of the state `X_p` of the code automaton: codes of words accepted from `p`. -/
def stateLang (p : Fin m) (σ : List (Fin n)) : Prop :=
  ∃ v, M.AcceptsFrom p v ∧ σ = doublingCode hn v

/-- The language of the middle state `Y_t` of a transition `p →a q`: the words
`a · doublingCode v` for `v` accepted from `q`. -/
def transLang (j : Fin M.trans.length) (σ : List (Fin n)) : Prop :=
  ∃ v, M.AcceptsFrom M.trans[j].2.2 v ∧ σ = embedDir hn M.trans[j].2.1 :: doublingCode hn v

theorem not_stateLang_nil (p : Fin m) : ¬ stateLang hn M p [] := by
  rintro ⟨v, -, hv⟩; exact doublingCode_ne_nil hn v hv.symm

theorem not_transLang_nil (j : Fin M.trans.length) : ¬ transLang hn M j [] := by
  rintro ⟨v, -, hv⟩; exact List.cons_ne_nil _ _ hv.symm

/-- The length of `doublingCode w`; the countermodel trees have depth `codeLength + 1`. -/
def codeLength (w : List (Fin 2)) : ℕ := (doublingCode hn w).length

/-- The countermodel for a word `w`. -/
noncomputable def counterValuation (w : List (Fin 2)) : V (numVars M) → FTree n :=
  valuation M
    ![pathTree (doublingCode hn w), fullBinary (codeLength hn w + 1), .bot,
      (rPair (1 + 2 * w.length)).1, (rPair (1 + 2 * w.length)).2,
      .node (binaryChildren (pathTree (doublingCode hn w)) .bot .bot)]
    (fun p => avoid (stateLang hn M p) (codeLength hn w + 1))
    (fun j => avoid (transLang hn M j) (codeLength hn w + 1))

/-- A rejected word gives a finite solution. -/
theorem sat_counterValuation {w : List (Fin 2)} (hw : ¬ M.Accepts w) :
    Covariant.Sat (FTree.toTree ∘ counterValuation hn M w) (hardnessSystem n M) := by
  set σ := counterValuation hn M w
  have hx : σ (xVar M) = pathTree (doublingCode hn w) := by simp [σ, counterValuation, xVar]
  have hb : σ (bVar M) = .bot := by simp [σ, counterValuation, bVar]
  have hr : σ (rVar M) = (rPair (1 + 2 * w.length)).1 := by simp [σ, counterValuation, rVar]
  have hr' : σ (rVar' M) = (rPair (1 + 2 * w.length)).2 := by
    simp [σ, counterValuation, rVar']
  have hz : σ (zVar M) = .node (binaryChildren (pathTree (doublingCode hn w)) .bot .bot) := by
    simp [σ, counterValuation, zVar]
  have hd : ∀ (L : List (Fin n) → Prop), avoid L (codeLength hn w) ≤ σ (dVar M) := fun L => by
    have : σ (dVar M) = fullBinary (codeLength hn w + 1) := by
      simp [σ, counterValuation, dVar]
    rw [this]
    exact avoid_le_fullBinary L (by omega)
  have hX : ∀ p, σ (stateVar M p) = avoid (stateLang hn M p) (codeLength hn w + 1) :=
    fun p => by simp [σ, counterValuation]
  have hY : ∀ j, σ (transVar M j) = avoid (transLang hn M j) (codeLength hn w + 1) :=
    fun j => by simp [σ, counterValuation]
  have hval : ∀ (a : Fin n → V (numVars M)),
      Tree.node ((FTree.toTree ∘ σ) ∘ a) = (FTree.node (σ ∘ a)).toTree := fun _ => rfl
  rw [covSat_hardnessSystem_iff]
  simp only [hval]
  simp only [Function.comp_apply, FTree.toTree_le_iff, comp_binaryChildren, hx, hb, hr, hr', hz]
  refine ⟨rfl, (rPair_succ_le _).1, (rPair_succ_le _).2, le_rfl, ?_, ?_, ?_, ?_⟩
  · -- the sandwich: `x` lies below `X_p` for each initial state `p`
    intro p hp
    refine node_binaryChildren_mono ?_ le_rfl le_rfl
    rw [hX]
    refine pathTree_le_avoid _ (by simp [codeLength])
      (fun i hi => val_lt_two_of_mem_doublingCode hn hi) ?_
    rintro τ hτ ⟨v, hv, rfl⟩
    exact hw ⟨p, hp, by rwa [← eq_of_doublingCode_prefix hn hτ]⟩
  · -- a final state closes the code with the letter `1`
    intro p hp
    rw [hX]
    refine avoid_succ_le_node (not_stateLang_nil hn M p) fun i hi => ?_
    simp only [binaryChildren]
    split_ifs with h0 h1
    · exact hd _
    · have hnil : stateLang hn M p [i] := ⟨[], (M.acceptsFrom_nil p).mpr hp, by
        rw [doublingCode_nil, show i = embedDir hn 1 from Fin.ext h1]⟩
      rw [avoid_of_nil (L := fun τ => stateLang hn M p (i :: τ)) hnil]
    · omega
  · -- a state enters the middle state of each outgoing transition by the letter `0`
    intro j
    rw [hX]
    refine avoid_succ_le_node (not_stateLang_nil hn M _) fun i hi => ?_
    simp only [binaryChildren]
    split_ifs with h0
    · rw [hY]
      refine avoid_mono ?_ (by omega)
      rintro τ ⟨v, hv, rfl⟩
      refine ⟨M.trans[j].2.1 :: v, M.acceptsFrom_cons (List.getElem_mem _) hv, ?_⟩
      rw [doublingCode_cons, show i = embedDir hn 0 from Fin.ext h0]
    · exact hd _
    · omega
  · -- the middle state reads the letter of its transition
    intro j
    rw [hY]
    refine avoid_succ_le_node (not_transLang_nil hn M j) fun i hi => ?_
    simp only [Function.comp_apply, readChildren]
    split_ifs with ha
    · rw [hX]
      refine avoid_mono ?_ (by omega)
      rintro τ ⟨v, hv, rfl⟩
      exact ⟨v, hv, by rw [show i = embedDir hn M.trans[j].2.1 from Fin.ext ha]⟩
    · exact hd _

/-- In the countermodel, `x` is a constructor at the code of `w`, where `r` is bottom. -/
theorem not_le_counterValuation (w : List (Fin 2)) :
    ¬ (counterValuation hn M w (xVar M)).toTree ≤ (counterValuation hn M w (rVar M)).toTree := by
  rw [not_le_iff_unsafe]
  refine ⟨doublingCode hn w, Or.inl ⟨?_, ?_⟩⟩
  · simp only [counterValuation, xVar, valuation_auxVar]
    simp [trace_pathTree]
  · simp only [counterValuation, rVar, valuation_auxVar]
    simp only [Matrix.cons_val, doublingCode]
    rw [trace_snoc, trace_rPair_doubling hn w 1]
    simp [rPair]

include hn in
/-- A rejected word refutes entailment over finite trees. -/
theorem not_entailsFin_of_not_accepts {w : List (Fin 2)} (hw : ¬ M.Accepts w) :
    ¬ EntailsFin (fun _ => false) (hardnessSystem n M) (xVar M) (rVar M) := by
  intro h
  have := h (counterValuation hn M w) ((sat_false _ _).mpr (sat_counterValuation hn M hw))
  exact not_le_counterValuation hn M w ((treeLe_false_iff_le _ _).mp this)

end Countermodel

end DeciNSSE.Complexity.Hardness
