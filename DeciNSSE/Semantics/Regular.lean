import DeciNSSE.Semantics.Tree

/-! # Regular trees as finite graphs

Unfolding a finite rooted graph gives a path tree, possibly infinite when the
graph contains cycles. Edges leaving bottom or top labels are ignored.
-/

namespace DeciNSSE

/-- A finite rooted labelled graph presenting a regular tree by unfolding. -/
structure RGraph (n : ℕ) where
  /-- The number of graph states. -/
  size : ℕ
  /-- The distinguished initial state. -/
  root : Fin size
  /-- The symbol emitted at each state. -/
  label : Fin size → Sym
  /-- The successor at each constructor position; leaf successors are ignored. -/
  child : Fin size → Fin n → Fin size

namespace RGraph

variable {n : ℕ}

/-- Follow a path starting at an arbitrary graph node. -/
def walkFrom (g : RGraph n) (p : Fin g.size) : List (Fin n) → Option (Fin g.size)
  | [] => some p
  | i :: π => if g.label p = Sym.f then walkFrom g (g.child p i) π else none

/-- Follow a path from the distinguished root. -/
def walk (g : RGraph n) (π : List (Fin n)) : Option (Fin g.size) :=
  g.walkFrom g.root π

theorem walkFrom_append (g : RGraph n) (p : Fin g.size) (π ρ : List (Fin n)) :
    g.walkFrom p (π ++ ρ) = (g.walkFrom p π).bind (fun q => g.walkFrom q ρ) := by
  induction π generalizing p with
  | nil => rfl
  | cons i π ih =>
    simp only [List.cons_append, walkFrom]
    split <;> simp_all

theorem walk_append_singleton (g : RGraph n) (π : List (Fin n)) (i : Fin n) :
    g.walk (π ++ [i]) = (g.walk π).bind
      (fun p => if g.label p = Sym.f then some (g.child p i) else none) := by
  simp [walk, walkFrom_append, walkFrom]

/-- Unfolding gives a path tree, including for graphs with cycles. -/
def unfold (g : RGraph n) : Tree n where
  fn π := (g.walk π).map g.label
  wf := by
    constructor
    · simp [walk, walkFrom]
    · intro π i
      rw [walk_append_singleton]
      cases h : g.walk π with
      | none => simp
      | some p => by_cases hf : g.label p = Sym.f <;> simp [hf]

@[simp] theorem unfold_fn (g : RGraph n) (π : List (Fin n)) :
    g.unfold.fn π = (g.walk π).map g.label := rfl

/-- Use the selected graph node as the distinguished root. -/
def reroot (g : RGraph n) (p : Fin g.size) : RGraph n := { g with root := p }

@[simp] theorem unfold_root (g : RGraph n) :
    g.unfold.fn [] = some (g.label g.root) := rfl

theorem unfold_bot (g : RGraph n) (h : g.label g.root = Sym.bot) :
    g.unfold = Tree.bot := (Tree.root_eq_bot_iff _).mp (congrArg some h)

theorem unfold_top (g : RGraph n) (h : g.label g.root = Sym.top) :
    g.unfold = Tree.top := (Tree.root_eq_top_iff _).mp (congrArg some h)

theorem walkFrom_reroot (g : RGraph n) (p q : Fin g.size) (w : List (Fin n)) :
    (g.reroot p).walkFrom q w = g.walkFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons i w ih =>
    change (if g.label q = Sym.f then (g.reroot p).walkFrom (g.child q i) w else none) =
      (if g.label q = Sym.f then g.walkFrom (g.child q i) w else none)
    split
    · exact ih _
    · rfl

theorem unfold_node (g : RGraph n) (h : g.label g.root = Sym.f) :
    g.unfold = Tree.node (fun i => (g.reroot (g.child g.root i)).unfold) := by
  apply Tree.ext
  funext w
  cases w with
  | nil => exact congrArg some h
  | cons i w =>
    change (g.walkFrom g.root (i :: w)).map g.label =
      ((g.reroot (g.child g.root i)).walkFrom (g.child g.root i) w).map g.label
    rw [walkFrom, ite_eq_left h, walkFrom_reroot]

/-- One state with every edge returning to itself. -/
def allF (n : ℕ) : RGraph n where
  size := 1
  root := 0
  label := fun _ => Sym.f
  child := fun _ _ => 0

@[simp] theorem allF_walkFrom (p : Fin 1) (w : List (Fin n)) :
    (allF n).walkFrom p w = some (0 : Fin 1) := by
  induction w generalizing p with
  | nil => exact congrArg some (Subsingleton.elim p 0)
  | cons i w ih => simpa [walkFrom, allF] using ih 0

@[simp] theorem allF_unfold_fn (w : List (Fin n)) :
    (allF n).unfold.fn w = some Sym.f := by
  change ((allF n).walkFrom (0 : Fin 1) w).map _ = _
  rw [allF_walkFrom]
  rfl

/-- The one-state constructor graph unfolds to a node with identical subtrees. -/
theorem allF_unfold_node :
    (allF n).unfold = Tree.node (fun _ => (allF n).unfold) := by
  apply Tree.ext
  funext w
  cases w <;> simp only [Tree.node_fn_nil, Tree.node_fn_cons, allF_unfold_fn]

end RGraph
end DeciNSSE
