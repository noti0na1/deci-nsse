import DeciNSSE.Semantics.Finite

/-! # Regular trees as finite graphs

Finite labelled graphs unfold to possibly infinite trees. Every finite tree
has such a graph, relating the finite, regular and unrestricted solution domains.
-/

namespace DeciNSSE

/-- A rooted finite labelled graph whose unfolding represents a regular tree. -/
structure RGraph where
  /-- The number of graph vertices. -/
  n : ℕ
  /-- The distinguished vertex at which unfolding begins. -/
  root : Fin n
  /-- The bottom, constructor or top label of each vertex. -/
  label : Fin n → Sym
  /-- The two successors of a constructor vertex; successors of leaves are ignored. -/
  child : Fin n → Fin 2 → Fin n

namespace RGraph

/-- Follow a path from a graph vertex, stopping if a leaf is crossed. -/
def walkFrom (g : RGraph) (p : Fin g.n) : List (Fin 2) → Option (Fin g.n)
  | [] => some p
  | i :: π => if g.label p = Sym.f then walkFrom g (g.child p i) π else none

/-- Follow a path from the root of a finite graph. -/
def walk (g : RGraph) (π : List (Fin 2)) : Option (Fin g.n) :=
  g.walkFrom g.root π

theorem walkFrom_append (g : RGraph) (p : Fin g.n) (π ρ : List (Fin 2)) :
    g.walkFrom p (π ++ ρ) = (g.walkFrom p π).bind (fun q => g.walkFrom q ρ) := by
  induction π generalizing p with
  | nil => rfl
  | cons i π ih =>
    simp only [List.cons_append, walkFrom]
    split <;> simp_all

theorem walk_append_singleton (g : RGraph) (π : List (Fin 2)) (i : Fin 2) :
    g.walk (π ++ [i]) = (g.walk π).bind
      (fun p => if g.label p = Sym.f then some (g.child p i) else none) := by
  simp [walk, walkFrom_append, walkFrom]

/-- Unfold a finite labelled graph into its regular tree. -/
def unfold (g : RGraph) : Tree where
  fn π := (g.walk π).map g.label
  wf := by
    constructor
    · simp [walk, walkFrom]
    · intro π i
      rw [walk_append_singleton]
      cases h : g.walk π with
      | none => simp
      | some p => by_cases hf : g.label p = Sym.f <;> simp [hf]

@[simp] theorem unfold_fn (g : RGraph) (π : List (Fin 2)) :
    g.unfold.fn π = (g.walk π).map g.label := rfl

end RGraph

namespace FTree

/-- The list of subtrees of a finite tree, including the tree itself. -/
def subtrees : FTree → List FTree
  | bot => [bot]
  | top => [top]
  | node l r => node l r :: (subtrees l ++ subtrees r)

@[simp] theorem mem_subtrees_self (a : FTree) : a ∈ a.subtrees := by
  cases a <;> simp [subtrees]

theorem children_mem_subtrees {a l r : FTree} (h : node l r ∈ a.subtrees) :
    l ∈ a.subtrees ∧ r ∈ a.subtrees := by
  induction a with
  | bot => simp [subtrees] at h
  | top => simp [subtrees] at h
  | node u v ihu ihv =>
    simp only [subtrees, List.mem_cons, List.mem_append] at h ⊢
    rcases h with h | h | h
    · cases h
      exact ⟨Or.inr (Or.inl (mem_subtrees_self _)),
        Or.inr (Or.inr (mem_subtrees_self _))⟩
    · exact ⟨Or.inr (Or.inl (ihu h).1), Or.inr (Or.inl (ihu h).2)⟩
    · exact ⟨Or.inr (Or.inr (ihv h).1), Or.inr (Or.inr (ihv h).2)⟩

/-- The first index of a subtree in the finite tree's subtree list. -/
def subtreeIndex (a b : FTree) (h : b ∈ a.subtrees) : Fin a.subtrees.length :=
  ⟨a.subtrees.idxOf b, List.idxOf_lt_length_of_mem h⟩

@[simp] theorem get_subtreeIndex (a b : FTree) (h : b ∈ a.subtrees) :
    a.subtrees[(a.subtreeIndex b h).val] = b := List.getElem_idxOf _

/-- The index of a subtree, with the root as the value when it is absent. -/
def subtreeIndexOrRoot (a b : FTree) : Fin a.subtrees.length :=
  if h : b ∈ a.subtrees then a.subtreeIndex b h
  else a.subtreeIndex a (mem_subtrees_self a)

theorem get_subtreeIndexOrRoot (a b : FTree) (h : b ∈ a.subtrees) :
    a.subtrees[(a.subtreeIndexOrRoot b).val] = b := by
  simp [subtreeIndexOrRoot, h]

/-- The label at the root of a finite tree. -/
def rootLabel : FTree → Sym
  | bot => Sym.bot
  | top => Sym.top
  | node _ _ => Sym.f

/-- Represent a finite tree by a graph indexed by its subtree occurrences. -/
def toGraph (a : FTree) : RGraph where
  n := a.subtrees.length
  root := a.subtreeIndex a (mem_subtrees_self a)
  label p := (a.subtrees[p.val]).rootLabel
  child p i :=
    match a.subtrees[p.val] with
    | bot => a.subtreeIndex a (mem_subtrees_self a)
    | top => a.subtreeIndex a (mem_subtrees_self a)
    | node l r =>
      if i = 0 then a.subtreeIndexOrRoot l else a.subtreeIndexOrRoot r

theorem toGraph_walkFrom (a : FTree) (p : Fin a.toGraph.n) (π : List (Fin 2)) :
    (a.toGraph.walkFrom p π).map a.toGraph.label = (a.subtrees[p.val]).toTree.fn π := by
  induction π generalizing p with
  | nil =>
    change some (a.subtrees[p.val].rootLabel) = _
    cases a.subtrees[p.val] <;> rfl
  | cons i π ih =>
    cases h : a.subtrees[p.val] with
    | bot => simp [RGraph.walkFrom, toGraph, h, rootLabel, toTree]
    | top => simp [RGraph.walkFrom, toGraph, h, rootLabel, toTree]
    | node l r =>
      have hf : a.toGraph.label p = Sym.f := by simp [toGraph, h, rootLabel]
      have hm := children_mem_subtrees (h ▸ List.getElem_mem p.isLt)
      rw [RGraph.walkFrom, if_pos hf, ih]
      fin_cases i <;> simp [toGraph, h, toTree,
        get_subtreeIndexOrRoot a l hm.1, get_subtreeIndexOrRoot a r hm.2]

/-- The graph representation of a finite tree unfolds to that same tree. -/
@[simp] theorem unfold_toGraph (a : FTree) : a.toGraph.unfold = a.toTree := by
  apply Tree.ext
  funext π
  change (a.toGraph.walkFrom a.toGraph.root π).map a.toGraph.label = _
  rw [toGraph_walkFrom]
  exact congrArg (fun b : FTree => b.toTree.fn π)
    (get_subtreeIndex a a (mem_subtrees_self a))

end FTree
end DeciNSSE
