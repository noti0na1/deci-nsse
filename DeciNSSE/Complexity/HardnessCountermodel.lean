import DeciNSSE.Complexity.HardnessSolutions

/-! # A finite countermodel for a rejected word

Let `M` reject `w` and let `c = code w`. No prefix of `c` is the code of a word
accepted from an initial state, by prefix freeness. The finite solution:

- `x` is the path tree along `c`, with constructor positions the prefixes of `c`;
- `X_p` and `Y_t` are the binary trees of depth `|c| + 1` whose constructor paths
  have no prefix in the language of the corresponding state of the code
  automaton (`avoid`), and `d` is the full binary tree of that depth;
- `r` and `r'` are the approximants `rPair (2 |w| + 1)` of the greatest solution
  of their two literals; `r` is bottom at `c`, where `x` is a constructor.

So `x ≤ r` fails in a finite solution (`not_entailsFin_of_not_accepts`).

## Main declarations
- `Hardness.avoid`, `Hardness.pathTree`, `Hardness.rPair`
- `Hardness.not_entailsFin_of_not_accepts`
-/

namespace DeciNSSE.Complexity.Hardness

open Safety

variable {n m : ℕ}

/-- The bottom term is least. -/
theorem ftree_bot_le (t : FTree n) : (FTree.bot : FTree n) ≤ t := Tree.bot_le t.toTree

@[simp] theorem descend_toTree_node (a : Fin n → FTree n) (i : Fin n) :
    descend (FTree.node a).toTree i = (a i).toTree := by
  simp

section Avoid

open Classical in
/-- The binary tree of depth `h` whose constructor paths are the binary paths shorter
than `h` with no prefix in `L`. -/
noncomputable def avoid (L : List (Fin n) → Prop) : ℕ → FTree n
  | 0 => .bot
  | h + 1 =>
    if L [] then .bot
    else .node fun i => if i.val < 2 then avoid (fun σ => L (i :: σ)) h else .bot

theorem avoid_of_nil {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) : avoid L h = .bot := by
  cases h <;> simp [avoid, hL]

theorem avoid_succ {L : List (Fin n) → Prop} (hL : ¬ L []) (h : ℕ) :
    avoid L (h + 1) =
      .node fun i => if i.val < 2 then avoid (fun σ => L (i :: σ)) h else .bot := by
  simp [avoid, hL]

/-- A smaller forbidden language and a larger depth give a larger tree. -/
theorem avoid_mono : ∀ {L L' : List (Fin n) → Prop} {h h' : ℕ},
    (∀ σ, L' σ → L σ) → h ≤ h' → avoid L h ≤ avoid L' h'
  | _, _, 0, _, _, _ => ftree_bot_le _
  | L, L', h + 1, h' + 1, hL, hh => by
    by_cases h0 : L []
    · rw [avoid_of_nil h0]; exact ftree_bot_le _
    · rw [avoid_succ h0, avoid_succ (fun h1 => h0 (hL _ h1)), FTree.node_le_node_iff]
      intro i
      split_ifs
      · exact avoid_mono (fun σ => hL (i :: σ)) (by omega)
      · exact le_rfl

/-- Every such tree lies below the full binary tree of at least its depth. -/
theorem avoid_le_full (L : List (Fin n) → Prop) {h h' : ℕ} (hh : h ≤ h') :
    avoid L h ≤ avoid (fun _ => False) h' :=
  avoid_mono (fun _ h => h.elim) hh

/-- The constructor case of `avoid` lies below a node whose binary children dominate. -/
theorem avoid_succ_le_node {L : List (Fin n) → Prop} (hL : ¬ L []) {h : ℕ}
    {a : Fin n → FTree n}
    (ha : ∀ i : Fin n, i.val < 2 → avoid (fun σ => L (i :: σ)) h ≤ a i) :
    avoid L (h + 1) ≤ .node a := by
  rw [avoid_succ hL, FTree.node_le_node_iff]
  intro i
  split_ifs with hi
  · exact ha i hi
  · exact ftree_bot_le _

end Avoid

section PathTree

/-- The finite tree whose constructor positions are the prefixes of the path. -/
def pathTree : List (Fin n) → FTree n
  | [] => .node fun _ => .bot
  | i :: σ => .node fun j => if j = i then pathTree σ else .bot

/-- A binary path avoiding `L` at all its prefixes gives a path tree below `avoid L`. -/
theorem pathTree_le_avoid : ∀ (σ : List (Fin n)) {L : List (Fin n) → Prop} {h : ℕ},
    σ.length < h → (∀ i ∈ σ, i.val < 2) → (∀ τ, τ <+: σ → ¬ L τ) →
      pathTree σ ≤ avoid L h
  | _, _, 0, hσ, _, _ => absurd hσ (by omega)
  | [], L, h + 1, _, _, hL => by
    rw [pathTree, avoid_succ (hL [] List.nil_prefix), FTree.node_le_node_iff]
    exact fun _ => ftree_bot_le _
  | i :: σ, L, h + 1, hσ, hbin, hL => by
    rw [pathTree, avoid_succ (hL [] List.nil_prefix), FTree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [ite_true, hbin j List.mem_cons_self]
      refine pathTree_le_avoid σ (by simpa using hσ) (fun i hi => hbin i (by simp [hi])) ?_
      intro τ hτ
      exact hL (j :: τ) ((List.cons_prefix_cons).mpr ⟨rfl, hτ⟩)
    · simp only [hj, ite_false]
      exact ftree_bot_le _

/-- The path tree is a constructor with bottom children at the end of its path. -/
theorem trace_pathTree : ∀ σ : List (Fin n),
    trace (pathTree σ).toTree σ = (FTree.node fun _ => .bot).toTree
  | [] => rfl
  | i :: σ => by simpa [pathTree] using trace_pathTree σ

end PathTree

section Approximants

/-- The approximants of `r` and `r'`: `(⊤, ⊤)`, then `(f(r', ⊥, …), f(r, r, ⊥, …))`. -/
def rPair : ℕ → FTree n × FTree n
  | 0 => (.top, .top)
  | h + 1 => (.node (kids (rPair h).2 .bot .bot), .node (kids (rPair h).1 (rPair h).1 .bot))

/-- Children `(u, v, w, …)` compare coordinatewise. -/
theorem node_kids_mono {u u' v v' w w' : FTree n} (hu : u ≤ u') (hv : v ≤ v') (hw : w ≤ w') :
    FTree.node (kids u v w) ≤ FTree.node (kids u' v' w') :=
  (FTree.node_le_node_iff _ _).mpr fun i => by
    simp only [kids]
    split_ifs
    exacts [hu, hv, hw]

/-- The approximants decrease. -/
theorem rPair_succ_le : ∀ h : ℕ,
    ((rPair (h + 1)).1 : FTree n) ≤ (rPair h).1 ∧ ((rPair (h + 1)).2 : FTree n) ≤ (rPair h).2
  | 0 => ⟨Tree.le_top _, Tree.le_top _⟩
  | h + 1 => by
    obtain ⟨h1, h2⟩ : ((rPair (h + 1)).1 : FTree n) ≤ (rPair h).1 ∧
      ((rPair (h + 1)).2 : FTree n) ≤ (rPair h).2 := rPair_succ_le h
    exact ⟨node_kids_mono h2 le_rfl le_rfl, node_kids_mono h1 h1 le_rfl⟩

/-- Along `e(w)`, the approximant of `r` loses two levels per letter. -/
theorem trace_rPair_pad (hn : 2 ≤ n) : ∀ (w : List (Fin 2)) (h : ℕ),
    trace (rPair (h + 2 * w.length) : FTree n × FTree n).1.toTree (pad hn w) = (rPair h).1.toTree
  | [], _ => rfl
  | a :: w, h => by
    rw [show h + 2 * (a :: w).length = h + 2 * w.length + 1 + 1 by simp; ring, pad_cons,
      trace_cons, trace_cons]
    simp only [rPair, descend_toTree_node, kids_dir_zero]
    rw [show (kids (rPair (h + 2 * w.length)).1 (rPair (h + 2 * w.length)).1 FTree.bot
      (dir hn a) : FTree n) = (rPair (h + 2 * w.length)).1 by fin_cases a <;> simp]
    exact trace_rPair_pad hn w h

end Approximants

section Countermodel

variable (hn : 2 ≤ n) (M : BinNFA m)

/-- The language of the state `X_p` of the code automaton: codes of words accepted from `p`. -/
def stateLang (p : Fin m) (σ : List (Fin n)) : Prop :=
  ∃ v, M.AcceptsFrom p v ∧ σ = code hn v

/-- The language of the middle state `Y_t` of a transition `p →a q`: the words `a · code v`
for `v` accepted from `q`. -/
def transLang (j : Fin M.trans.length) (σ : List (Fin n)) : Prop :=
  ∃ v, M.AcceptsFrom M.trans[j].2.2 v ∧ σ = dir hn M.trans[j].2.1 :: code hn v

theorem not_stateLang_nil (p : Fin m) : ¬ stateLang hn M p [] := by
  rintro ⟨v, -, hv⟩; exact code_ne_nil hn v hv.symm

theorem not_transLang_nil (j : Fin M.trans.length) : ¬ transLang hn M j [] := by
  rintro ⟨v, -, hv⟩; exact List.cons_ne_nil _ _ hv.symm

/-- The depth of the finite trees in the countermodel. -/
def depth (w : List (Fin 2)) : ℕ := (code hn w).length

/-- The countermodel for a word `w`. -/
noncomputable def counterValuation (w : List (Fin 2)) : V (numVars M) → FTree n :=
  valuation M
    ![pathTree (code hn w), avoid (fun _ => False) (depth hn w + 1), .bot,
      (rPair (1 + 2 * w.length)).1, (rPair (1 + 2 * w.length)).2,
      .node (kids (pathTree (code hn w)) .bot .bot)]
    (fun p => avoid (stateLang hn M p) (depth hn w + 1))
    (fun j => avoid (transLang hn M j) (depth hn w + 1))

/-- A rejected word gives a finite solution. -/
theorem sat_counterValuation {w : List (Fin 2)} (hw : ¬ M.Accepts w) :
    Covariant.Sat (FTree.toTree ∘ counterValuation hn M w) (hardnessSystem n M) := by
  set σ := counterValuation hn M w
  have hx : σ (xVar M) = pathTree (code hn w) := by simp [σ, counterValuation, xVar]
  have hb : σ (bVar M) = .bot := by simp [σ, counterValuation, bVar]
  have hr : σ (rVar M) = (rPair (1 + 2 * w.length)).1 := by simp [σ, counterValuation, rVar]
  have hr' : σ (rVar' M) = (rPair (1 + 2 * w.length)).2 := by
    simp [σ, counterValuation, rVar']
  have hz : σ (zVar M) = .node (kids (pathTree (code hn w)) .bot .bot) := by
    simp [σ, counterValuation, zVar]
  have hd : ∀ (L : List (Fin n) → Prop), avoid L (depth hn w) ≤ σ (dVar M) := fun L => by
    have : σ (dVar M) = avoid (fun _ => False) (depth hn w + 1) := by
      simp [σ, counterValuation, dVar]
    rw [this]
    exact avoid_le_full L (by omega)
  have hX : ∀ p, σ (stateVar M p) = avoid (stateLang hn M p) (depth hn w + 1) := fun p => by
    simp [σ, counterValuation]
  have hY : ∀ j, σ (transVar M j) = avoid (transLang hn M j) (depth hn w + 1) := fun j => by
    simp [σ, counterValuation]
  have hval : ∀ (a : Fin n → V (numVars M)),
      Tree.node ((FTree.toTree ∘ σ) ∘ a) = (FTree.node (σ ∘ a)).toTree := fun _ => rfl
  rw [covSat_hardnessSystem_iff]
  simp only [hval]
  simp only [Function.comp_apply, FTree.toTree_le_iff, comp_kids, hx, hb, hr, hr', hz]
  refine ⟨rfl, (rPair_succ_le _).1, (rPair_succ_le _).2, le_rfl, ?_, ?_, ?_, ?_⟩
  · -- the sandwich: `x` lies below `X_p` for each initial state `p`
    intro p hp
    refine node_kids_mono ?_ le_rfl le_rfl
    rw [hX]
    refine pathTree_le_avoid _ (by simp [depth]) (fun i hi => val_lt_two_of_mem_code hn hi) ?_
    rintro τ hτ ⟨v, hv, rfl⟩
    exact hw ⟨p, hp, by rwa [← eq_of_code_prefix hn hτ]⟩
  · -- a final state closes the code with the letter `1`
    intro p hp
    rw [hX]
    refine avoid_succ_le_node (not_stateLang_nil hn M p) fun i hi => ?_
    simp only [kids]
    split_ifs with h0 h1
    · exact hd _
    · have hnil : stateLang hn M p [i] := ⟨[], (M.acceptsFrom_nil p).mpr hp, by
        rw [code_nil, show i = dir hn 1 from Fin.ext h1]⟩
      rw [avoid_of_nil (L := fun τ => stateLang hn M p (i :: τ)) hnil]
    · omega
  · -- a state enters the middle state of each outgoing transition by the letter `0`
    intro j
    rw [hX]
    refine avoid_succ_le_node (not_stateLang_nil hn M _) fun i hi => ?_
    simp only [kids]
    split_ifs with h0
    · rw [hY]
      refine avoid_mono ?_ (by omega)
      rintro τ ⟨v, hv, rfl⟩
      refine ⟨M.trans[j].2.1 :: v, M.acceptsFrom_cons (List.getElem_mem _) hv, ?_⟩
      rw [code_cons, show i = dir hn 0 from Fin.ext h0]
    · exact hd _
    · omega
  · -- the middle state reads the letter of its transition
    intro j
    rw [hY]
    refine avoid_succ_le_node (not_transLang_nil hn M j) fun i hi => ?_
    simp only [Function.comp_apply, readKids]
    split_ifs with ha
    · rw [hX]
      refine avoid_mono ?_ (by omega)
      rintro τ ⟨v, hv, rfl⟩
      exact ⟨v, hv, by rw [show i = dir hn M.trans[j].2.1 from Fin.ext ha]⟩
    · exact hd _

/-- In the countermodel, `x` is a constructor at the code of `w`, where `r` is bottom. -/
theorem not_le_counterValuation (w : List (Fin 2)) :
    ¬ (counterValuation hn M w (xVar M)).toTree ≤ (counterValuation hn M w (rVar M)).toTree := by
  rw [not_le_iff_unsafe]
  refine ⟨code hn w, Or.inl ⟨?_, ?_⟩⟩
  · simp only [counterValuation, xVar, valuation_auxVar]
    simp [trace_pathTree]
  · simp only [counterValuation, rVar, valuation_auxVar]
    simp only [Matrix.cons_val, code]
    rw [trace_snoc, trace_rPair_pad hn w 1]
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
