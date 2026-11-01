import DeciNSSE.Complexity.Directions
import DeciNSSE.Semantics.Finite

/-! # Finite trees for the countermodels

The countermodels of the complexity results are built from four kinds of finite
trees over a constructor of arity `n`:

- `pathTree σ`, whose constructor positions are the prefixes of the path `σ`;
- `avoid L h`, the binary tree of depth `h` whose constructor paths have no prefix
  in the set `L` of paths;
- `fullBinary h`, the full binary tree of depth `h`, which is `avoid` of the empty
  set;
- `trunc L h`, the truncation of `L` at depth `h`: constructors at the paths shorter
  than `h` all of whose prefixes lie in `L`, top at such paths of length `h`, and
  bottom elsewhere.

They compare with constructors whose children are given by `binaryChildren` and
`letterChildren`.

## Main declarations
- `FiniteTrees.pathTree`, `FiniteTrees.trace_pathTree`, `FiniteTrees.pathTree_le_avoid`,
  `FiniteTrees.pathTree_le_fullBinary`
- `FiniteTrees.avoid`, `FiniteTrees.avoid_mono`, `FiniteTrees.avoid_le_fullBinary`
- `FiniteTrees.fullBinary`, `FiniteTrees.fullBinary_succ`
- `FiniteTrees.trunc`, `FiniteTrees.trunc_mono`, `FiniteTrees.trace_trunc_of_not_mem`,
  `FiniteTrees.node_letterChildren_le_trunc`
-/

namespace DeciNSSE.Complexity.FiniteTrees

open Safety Directions

variable {n : ℕ}

section Children

/-- Children `(u, v, w, …)` compare coordinatewise. -/
theorem node_binaryChildren_mono {u u' v v' w w' : FTree n} (hu : u ≤ u') (hv : v ≤ v')
    (hw : w ≤ w') : FTree.node (binaryChildren u v w) ≤ FTree.node (binaryChildren u' v' w') :=
  (FTree.node_le_node_iff _ _).mpr fun i => by
    simp only [binaryChildren]
    split_ifs
    exacts [hu, hv, hw]

/-- The embedding of finite terms commutes with `f(u, v, w, …)`. -/
theorem node_binaryChildren_toTree (a b c : FTree n) :
    Tree.node (binaryChildren a.toTree b.toTree c.toTree) =
      (FTree.node (binaryChildren a b c)).toTree := by
  rw [FTree.toTree_node, ← comp_binaryChildren]
  rfl

/-- The embedding of finite terms commutes with `f(u @ a, v, …)`. -/
theorem node_letterChildren_toTree (a : Fin 2) (u v : FTree n) :
    Tree.node (letterChildren a u.toTree v.toTree) =
      (FTree.node (letterChildren a u v)).toTree := by
  rw [FTree.toTree_node, ← comp_letterChildren]
  rfl

end Children

section PathTree

/-- The finite tree whose constructor positions are the prefixes of the path. -/
def pathTree : List (Fin n) → FTree n
  | [] => .node fun _ => .bot
  | i :: σ => .node fun j => if j = i then pathTree σ else .bot

/-- The path tree is a constructor with bottom children at the end of its path. -/
theorem trace_pathTree : ∀ σ : List (Fin n),
    trace (pathTree σ).toTree σ = (FTree.node fun _ => .bot).toTree
  | [] => rfl
  | i :: σ => by simpa [pathTree] using trace_pathTree σ

end PathTree

section Avoid

open Classical in
/-- The binary tree of depth `h` whose constructor paths are the binary paths shorter
than `h` with no prefix in `L`. -/
noncomputable def avoid (L : List (Fin n) → Prop) : ℕ → FTree n
  | 0 => .bot
  | h + 1 =>
    if L [] then .bot
    else .node fun i => if i.val < 2 then avoid (fun σ => L (i :: σ)) h else .bot

/-- With the root forbidden, the tree is bottom. -/
theorem avoid_of_nil {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) : avoid L h = .bot := by
  cases h <;> simp [avoid, hL]

/-- Without the root forbidden, the tree at a positive depth is a constructor. -/
theorem avoid_succ {L : List (Fin n) → Prop} (hL : ¬ L []) (h : ℕ) :
    avoid L (h + 1) =
      .node fun i => if i.val < 2 then avoid (fun σ => L (i :: σ)) h else .bot := by
  simp [avoid, hL]

/-- A smaller forbidden language and a larger depth give a larger tree. -/
theorem avoid_mono : ∀ {L L' : List (Fin n) → Prop} {h h' : ℕ},
    (∀ σ, L' σ → L σ) → h ≤ h' → avoid L h ≤ avoid L' h'
  | _, _, 0, _, _, _ => FTree.bot_le _
  | L, L', h + 1, h' + 1, hL, hh => by
    by_cases h0 : L []
    · rw [avoid_of_nil h0]; exact FTree.bot_le _
    · rw [avoid_succ h0, avoid_succ (fun h1 => h0 (hL _ h1)), FTree.node_le_node_iff]
      intro i
      split_ifs
      · exact avoid_mono (fun σ => hL (i :: σ)) (by omega)
      · exact le_rfl

/-- The constructor case of `avoid` lies below a node whose binary children dominate. -/
theorem avoid_succ_le_node {L : List (Fin n) → Prop} (hL : ¬ L []) {h : ℕ}
    {a : Fin n → FTree n}
    (ha : ∀ i : Fin n, i.val < 2 → avoid (fun σ => L (i :: σ)) h ≤ a i) :
    avoid L (h + 1) ≤ .node a := by
  rw [avoid_succ hL, FTree.node_le_node_iff]
  intro i
  split_ifs with hi
  · exact ha i hi
  · exact FTree.bot_le _

/-- A binary path avoiding `L` at all its prefixes gives a path tree below `avoid L`. -/
theorem pathTree_le_avoid : ∀ (σ : List (Fin n)) {L : List (Fin n) → Prop} {h : ℕ},
    σ.length < h → (∀ i ∈ σ, i.val < 2) → (∀ τ, τ <+: σ → ¬ L τ) →
      pathTree σ ≤ avoid L h
  | _, _, 0, hσ, _, _ => absurd hσ (by omega)
  | [], L, h + 1, _, _, hL => by
    rw [pathTree, avoid_succ (hL [] List.nil_prefix), FTree.node_le_node_iff]
    exact fun _ => FTree.bot_le _
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
      exact FTree.bot_le _

end Avoid

section FullBinary

/-- The full binary tree of depth `h`: constructors at the binary paths shorter than `h`,
and bottom elsewhere. -/
noncomputable def fullBinary (h : ℕ) : FTree n := avoid (fun _ => False) h

/-- Every tree `avoid L h` lies below the full binary tree of at least its depth. -/
theorem avoid_le_fullBinary (L : List (Fin n) → Prop) {h h' : ℕ} (hh : h ≤ h') :
    avoid L h ≤ fullBinary h' :=
  avoid_mono (fun _ h => h.elim) hh

/-- Full binary trees grow with the depth. -/
theorem fullBinary_mono {h h' : ℕ} (hh : h ≤ h') : (fullBinary h : FTree n) ≤ fullBinary h' :=
  avoid_le_fullBinary _ hh

/-- The full binary tree of depth `h + 1` is `f(F, F, ⊥, …)` for the full binary tree `F`
of depth `h`. -/
theorem fullBinary_succ (h : ℕ) :
    (fullBinary (h + 1) : FTree n) =
      .node (binaryChildren (fullBinary h) (fullBinary h) .bot) := by
  rw [fullBinary, avoid_succ not_false]
  congr 1
  funext i
  simp only [binaryChildren]
  split_ifs <;> first | rfl | omega

/-- A binary path shorter than `h` gives a path tree below the full binary tree of
depth `h`. -/
theorem pathTree_le_fullBinary {σ : List (Fin n)} {h : ℕ} (hσ : σ.length < h)
    (hbin : ∀ i ∈ σ, i.val < 2) : pathTree σ ≤ fullBinary h :=
  pathTree_le_avoid σ hσ hbin fun _ _ h => h

end FullBinary

section Truncation

open Classical in
/-- The truncation at depth `h` of a set `L` of paths: constructors at the paths shorter
than `h` all of whose prefixes lie in `L`, top at such paths of length `h`, and bottom
elsewhere. -/
noncomputable def trunc (L : List (Fin n) → Prop) : ℕ → FTree n
  | 0 => if L [] then .top else .bot
  | h + 1 => if L [] then .node fun i => trunc (fun σ => L (i :: σ)) h else .bot

/-- Without the root in `L`, the truncation is bottom. -/
theorem trunc_of_not_nil {L : List (Fin n) → Prop} (hL : ¬ L []) (h : ℕ) :
    trunc L h = .bot := by
  cases h <;> simp [trunc, hL]

/-- With the root in `L`, the truncation at a positive depth is a constructor. -/
theorem trunc_succ {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) :
    trunc L (h + 1) = .node fun i => trunc (fun σ => L (i :: σ)) h := by
  simp [trunc, hL]

/-- A larger set of paths and a smaller depth give a larger truncation. -/
theorem trunc_mono : ∀ {L L' : List (Fin n) → Prop} {h h' : ℕ},
    (∀ σ, L σ → L' σ) → h' ≤ h → trunc L h ≤ trunc L' h'
  | L, L', h, 0, hL, _ => by
    by_cases h0 : L []
    · rw [show trunc L' 0 = .top by simp [trunc, hL _ h0]]
      exact FTree.le_top _
    · rw [trunc_of_not_nil h0]
      exact FTree.bot_le _
  | L, L', h + 1, h' + 1, hL, hh => by
    by_cases h0 : L []
    · rw [trunc_succ h0, trunc_succ (hL _ h0), FTree.node_le_node_iff]
      exact fun i => trunc_mono (fun σ => hL (i :: σ)) (by omega)
    · rw [trunc_of_not_nil h0]
      exact FTree.bot_le _
  | _, _, 0, _ + 1, _, hh => absurd hh (by omega)

/-- At a path of length at most `h` outside `L`, the truncation is bottom. -/
theorem trace_trunc_of_not_mem : ∀ {L : List (Fin n) → Prop} {h : ℕ} {σ : List (Fin n)},
    σ.length ≤ h → ¬ L σ → trace (trunc L h).toTree σ = Tree.bot
  | _, h, [], _, hσ => by rw [trunc_of_not_nil hσ]; rfl
  | L, h + 1, i :: σ, hlen, hσ => by
    by_cases h0 : L []
    · rw [trunc_succ h0, trace_cons, FTree.toTree_node, descend_node]
      exact trace_trunc_of_not_mem (by simpa using hlen) hσ
    · rw [trunc_of_not_nil h0]
      simp
  | _, 0, _ :: _, hlen, _ => absurd hlen (by simp)

variable (hn : 2 ≤ n)

/-- If `L` contains the root and `a·L' ⊆ L`, then
`f(trunc L' (h + 1) @ a, ⊥, …) ≤ trunc L (h + 1)`. -/
theorem node_letterChildren_le_trunc {L L' : List (Fin n) → Prop} (hL : L []) (a : Fin 2)
    (hL' : ∀ σ, L' σ → L (embedDir hn a :: σ)) (h : ℕ) :
    FTree.node (letterChildren a (trunc L' (h + 1)) .bot) ≤ trunc L (h + 1) := by
  rw [trunc_succ hL, FTree.node_le_node_iff]
  intro i
  simp only [letterChildren]
  split_ifs with hi
  · obtain rfl : i = embedDir hn a := Fin.ext hi
    exact trunc_mono hL' (Nat.le_succ h)
  · exact FTree.bot_le _

/-- The constructor `f(⊥, …, ⊥)` lies below the truncation of `L` at a positive depth if `L`
contains the root. -/
theorem node_bot_le_trunc {L : List (Fin n) → Prop} (hL : L []) (h : ℕ) :
    FTree.node (binaryChildren .bot .bot .bot) ≤ trunc L (h + 1) := by
  rw [trunc_succ hL, FTree.node_le_node_iff]
  intro i
  simp only [binaryChildren]
  split_ifs <;> exact FTree.bot_le _

end Truncation

end DeciNSSE.Complexity.FiniteTrees
