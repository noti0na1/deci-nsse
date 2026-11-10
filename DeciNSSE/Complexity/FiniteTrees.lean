import DeciNSSE.Complexity.Directions
import DeciNSSE.Semantics.Finite

/-! # Finite trees for the countermodels

The countermodels of the complexity results are built from three kinds of finite
trees over a constructor of arity `n`:

- `pathTree σ`, whose constructor positions are the prefixes of the path `σ`;
- `fullBinary h`, the full binary tree of depth `h`;
- `trunc L h`, the truncation of `L` at depth `h`: constructors at the paths shorter
  than `h` all of whose prefixes lie in `L`, top at such paths of length `h`, and
  bottom elsewhere.

They compare with constructors whose children are given by `binaryChildren` and
`letterChildren`.

## Main declarations
- `FiniteTrees.pathTree`, `FiniteTrees.trace_pathTree`, `FiniteTrees.pathTree_le_fullBinary`
- `FiniteTrees.fullBinary`, `FiniteTrees.fullBinary_succ`, `FiniteTrees.fullBinary_mono`
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

section FullBinary

/-- The full binary tree of depth `h`: constructors at the binary paths shorter than `h`,
and bottom elsewhere. -/
def fullBinary : ℕ → FTree n
  | 0 => .bot
  | h + 1 => .node (binaryChildren (fullBinary h) (fullBinary h) .bot)

/-- The full binary tree of depth `h + 1` is `f(F, F, ⊥, …)` for the full binary tree `F`
of depth `h`. -/
theorem fullBinary_succ (h : ℕ) :
    (fullBinary (h + 1) : FTree n) =
      .node (binaryChildren (fullBinary h) (fullBinary h) .bot) := rfl

/-- Full binary trees grow with the depth. -/
theorem fullBinary_mono {h h' : ℕ} (hh : h ≤ h') : (fullBinary h : FTree n) ≤ fullBinary h' := by
  induction h generalizing h' with
  | zero => exact FTree.bot_le _
  | succ h ih =>
    cases h' with
    | zero => omega
    | succ h' => exact node_binaryChildren_mono (ih (by omega)) (ih (by omega)) le_rfl

/-- A binary path shorter than `h` gives a path tree below the full binary tree of
depth `h`. -/
theorem pathTree_le_fullBinary {σ : List (Fin n)} {h : ℕ} (hσ : σ.length < h)
    (hbin : ∀ i ∈ σ, i.val < 2) : pathTree σ ≤ fullBinary h := by
  induction σ generalizing h with
  | nil =>
    cases h with
    | zero => simp at hσ
    | succ h => exact (FTree.node_le_node_iff _ _).mpr fun _ => FTree.bot_le _
  | cons i σ ih =>
    cases h with
    | zero => simp at hσ
    | succ h =>
      rw [pathTree, fullBinary_succ, FTree.node_le_node_iff]
      intro j
      by_cases hj : j = i
      · subst j
        have hi := hbin i List.mem_cons_self
        have ht := ih (by simpa using hσ) (fun j hj => hbin j (List.mem_cons_of_mem _ hj))
        simp only [ite_true, binaryChildren]
        split_ifs <;> first | exact ht | omega
      · simp only [hj, ite_false]
        exact FTree.bot_le _

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
