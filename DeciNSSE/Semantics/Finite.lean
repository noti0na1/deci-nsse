import DeciNSSE.Semantics.Normalisation

/-! # Finite tree terms

Inductive terms embed injectively into path trees. Their covariant order is
the order inherited from this embedding.
-/

namespace DeciNSSE

/-- Finite terms over bottom, top and one constructor of arity `n`. -/
inductive FTree (n : ℕ) where
  | bot
  | top
  | node (children : Fin n → FTree n)

namespace FTree
variable {n : ℕ}

/-- Embed a finite term as a well-formed partial labelling of paths. -/
def toTree : FTree n → Tree n
  | bot => Tree.bot
  | top => Tree.top
  | node a => Tree.node (fun i => toTree (a i))

@[simp] theorem toTree_bot : toTree (bot : FTree n) = Tree.bot := rfl
@[simp] theorem toTree_top : toTree (top : FTree n) = Tree.top := rfl
@[simp] theorem toTree_node (a : Fin n → FTree n) :
    toTree (node a) = Tree.node (fun i => toTree (a i)) := rfl

/-- Distinct finite terms represent distinct path trees. -/
theorem toTree_injective : Function.Injective (@toTree n) := by
  intro a b h
  induction a generalizing b with
  | bot => cases b <;> simp_all [toTree]
  | top => cases b <;> simp_all [toTree]
  | node a ih =>
    cases b with
    | bot => simp [toTree] at h
    | top => simp [toTree] at h
    | node b =>
      apply congrArg node
      funext i
      exact ih i (congrFun ((Tree.node_eq_node_iff ..).mp h) i)

instance : PartialOrder (FTree n) :=
  PartialOrder.lift toTree toTree_injective

@[simp] theorem toTree_le_iff (a b : FTree n) : a.toTree ≤ b.toTree ↔ a ≤ b := Iff.rfl

@[simp] theorem node_le_node_iff (a b : Fin n → FTree n) :
    node a ≤ node b ↔ ∀ i, a i ≤ b i := Tree.node_le_node_iff _ _

/-- Flip each leaf by its polarity `p ⊕ pol(π)` along the finite tree. -/
def normalize (c : Fin n → Bool) (p : Bool) : FTree n → FTree n
  | .bot => if p then .top else .bot
  | .top => if p then .bot else .top
  | .node a => .node fun i => normalize c (Bool.xor p (c i)) (a i)

@[simp] theorem normalize_toTree (c : Fin n → Bool) (p : Bool) (t : FTree n) :
    (normalize c p t).toTree = Tree.normalize c p t.toTree := by
  induction t generalizing p with
  | bot => cases p <;> simp [normalize]
  | top => cases p <;> simp [normalize]
  | node a ih => simp [normalize, ih]

end FTree
end DeciNSSE
