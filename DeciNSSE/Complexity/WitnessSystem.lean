import DeciNSSE.Complexity.HardnessCountermodel

/-! # The witness system of a binary automaton

From a binary automaton `A` with states `Fin m`, the system `witnessSystem n A`
over one covariant constructor of arity `n ≥ 2` reads binary words along the
first two directions. Its right-unsafe words for the query `x ≤ y` are the
words that extend a word rejected by `A`. The variables are

- `x` and `y`, the queried pair;
- `g`, confined to the binary directions by `g ≤ f(g, g, b, …)`, and `b`,
  equal to bottom;
- `Y_q` for each state `q` of `A`.

The literals are

- `b = ⊥`, `g ≤ f(g, g, b, …)` and `x ≤ f(g, g, b, …)`, which keep `x` free of
  top and bottom off the binary paths;
- `f(b, …, b) ≤ y`, and `f(b, …, b) ≤ Y_q` for every state `q`;
- `f(Y_r @ a, b, …) ≤ Y_q` for every transition `q →a r`, with `Y_r` in the
  direction `a` and `b` in every other direction;
- `f(Y_r @ a, b, …) ≤ y` for every transition `q →a r` from an initial state
  `q`, so that `y` receives the lower literals of the initial states directly.

There is no literal between two variables. For `m` states and `T` transitions
the system has `m + 4` variables and at most `m + 2 T + 4` literals.

## Main declarations
- `witnessSystem`, with the variables `Witness.xVar`, `Witness.yVar`,
  `Witness.gVar`, `Witness.bVar` and `Witness.stateVar`
- `witnessSystem_length_le`, the size bound
- `covSat_witnessSystem_iff`, the solutions literal by literal
-/

namespace DeciNSSE.Complexity

namespace Witness

open Hardness (kids comp_kids)

variable {n m : ℕ}

/-- The variable `Y_q` of a state. -/
def stateVar (q : Fin m) : V (m + 4) := Fin.castAdd 4 q

/-- The auxiliary variable with the given index. -/
def auxVar (i : Fin 4) : V (m + 4) := Fin.natAdd m i

/-- The left side `x` of the query. -/
def xVar : V (m + 4) := auxVar 0
/-- The right side `y` of the query. -/
def yVar : V (m + 4) := auxVar 1
/-- The variable `g`, which confines `x` to the binary directions. -/
def gVar : V (m + 4) := auxVar 2
/-- The variable `b`, equal to bottom. -/
def bVar : V (m + 4) := auxVar 3

/-- The children `(u @ a, v, …, v)` of a constructor, variables in a flat literal or their
values: `u` in the direction of the binary letter `a`, and `v` in every other direction. -/
def letterKids {α : Type*} (a : Fin 2) (u v : α) : Fin n → α :=
  fun i => if i.val = a.val then u else v

/-- Applying a map to the children of `letterKids`. -/
theorem comp_letterKids {α β : Type*} (g : α → β) (a : Fin 2) (u v : α) :
    g ∘ (letterKids a u v : Fin n → α) = letterKids a (g u) (g v) := by
  funext i
  simp only [Function.comp_apply, letterKids]
  split_ifs <;> rfl

/-- A valuation from the values of `x`, `y`, `g` and `b` and of the state variables. -/
def valuation {α : Type*} (x y g b : α) (Y : Fin m → α) : V (m + 4) → α :=
  Fin.append Y ![x, y, g, b]

section Valuation
variable {α : Type*} (x y g b : α) (Y : Fin m → α)

@[simp] theorem valuation_xVar : valuation x y g b Y xVar = x := by
  simp [valuation, xVar, auxVar]

@[simp] theorem valuation_yVar : valuation x y g b Y yVar = y := by
  simp [valuation, yVar, auxVar]

@[simp] theorem valuation_gVar : valuation x y g b Y gVar = g := by
  simp [valuation, gVar, auxVar]

@[simp] theorem valuation_bVar : valuation x y g b Y bVar = b := by
  simp [valuation, bVar, auxVar]

@[simp] theorem valuation_stateVar (q : Fin m) : valuation x y g b Y (stateVar q) = Y q := by
  simp [valuation, stateVar]

end Valuation

end Witness

open Witness
open Hardness (kids comp_kids)

/-- The witness system of a binary automaton `A`, with the query `x ≤ y`. -/
def witnessSystem (n : ℕ) {m : ℕ} (A : BinNFA m) : Constraint n (m + 4) :=
  [.eqBot bVar, .leF gVar (kids gVar gVar bVar), .leF xVar (kids gVar gVar bVar),
    .fLe (kids bVar bVar bVar) yVar] ++
  (List.finRange m).map (fun q => .fLe (kids bVar bVar bVar) (stateVar q)) ++
  A.trans.map (fun t => .fLe (letterKids t.2.1 (stateVar t.2.2) bVar) (stateVar t.1)) ++
  (A.trans.filter fun t => A.init t.1).map
    (fun t => .fLe (letterKids t.2.1 (stateVar t.2.2) bVar) yVar)

/-- The literal count: four, one per state, one per transition, and one per transition
from an initial state. -/
theorem witnessSystem_length (n : ℕ) {m : ℕ} (A : BinNFA m) :
    (witnessSystem n A).length =
      m + A.trans.length + (A.trans.filter fun t => A.init t.1).length + 4 := by
  simp only [witnessSystem, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]
  omega

/-- The system has at most `m + 2 T + 4` literals for `m` states and `T` transitions. -/
theorem witnessSystem_length_le (n : ℕ) {m : ℕ} (A : BinNFA m) :
    (witnessSystem n A).length ≤ m + 2 * A.trans.length + 4 := by
  have := List.length_filter_le (fun t => A.init t.1) A.trans
  rw [witnessSystem_length]
  omega

/-- The solutions of the system, literal by literal. -/
theorem covSat_witnessSystem_iff {n m : ℕ} (A : BinNFA m) (ρ : V (m + 4) → Tree n) :
    Covariant.Sat ρ (witnessSystem n A) ↔
      ρ bVar = Tree.bot ∧
      ρ gVar ≤ Tree.node (kids (ρ gVar) (ρ gVar) (ρ bVar)) ∧
      ρ xVar ≤ Tree.node (kids (ρ gVar) (ρ gVar) (ρ bVar)) ∧
      Tree.node (kids (ρ bVar) (ρ bVar) (ρ bVar)) ≤ ρ yVar ∧
      (∀ q, Tree.node (kids (ρ bVar) (ρ bVar) (ρ bVar)) ≤ ρ (stateVar q)) ∧
      (∀ q a r, (q, a, r) ∈ A.trans →
        Tree.node (letterKids a (ρ (stateVar r)) (ρ bVar)) ≤ ρ (stateVar q)) ∧
      (∀ q a r, (q, a, r) ∈ A.trans → A.init q = true →
        Tree.node (letterKids a (ρ (stateVar r)) (ρ bVar)) ≤ ρ yVar) := by
  simp only [Covariant.Sat, witnessSystem, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_map, List.mem_filter, List.mem_finRange, true_implies, Covariant.holds,
    comp_kids, comp_letterKids, Prod.forall, and_imp, List.not_mem_nil, false_implies,
    implies_true, and_true, and_assoc]

end DeciNSSE.Complexity
