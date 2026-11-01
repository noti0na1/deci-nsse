import DeciNSSE.Complexity.BinNFA
import DeciNSSE.Complexity.Directions
import DeciNSSE.Constraints.Basic

/-! # The rejection system of a binary automaton

From a binary automaton `A` with states `Fin m`, the system `rejectionSystem n A`
over one covariant constructor of arity `n ≥ 2` reads binary words along the
first two directions, with the query `x ≤ y`. Every unsafe word is right unsafe
and is the image of a binary word rejected by `A` (`Rejection.exists_of_unsafe`).
When all states of `A` are final and `A` accepts the empty word, the unsafe words
are exactly the images of the binary words that extend a word rejected by `A`
(`Rejection.unsafe_of_not_accepts`). The variables are

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

The final states of `A` do not occur in the system. There is no literal between
two variables. For `m` states and `T` transitions the system has `m + 4`
variables and at most `m + 2 T + 4` literals.

## Main declarations
- `rejectionSystem`, with the variables `Rejection.xVar`, `Rejection.yVar`,
  `Rejection.gVar`, `Rejection.bVar` and `Rejection.stateVar`
- `rejectionSystem_length_le`, the size bound
- `covSat_rejectionSystem_iff`, the solutions literal by literal
-/

namespace DeciNSSE.Complexity

namespace Rejection

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

end Rejection

open Rejection Directions

/-- The rejection system of a binary automaton `A`, with the query `x ≤ y`. -/
def rejectionSystem (n : ℕ) {m : ℕ} (A : BinNFA m) : Constraint n (m + 4) :=
  [.eqBot bVar, .leF gVar (binaryChildren gVar gVar bVar),
    .leF xVar (binaryChildren gVar gVar bVar), .fLe (binaryChildren bVar bVar bVar) yVar] ++
  (List.finRange m).map (fun q => .fLe (binaryChildren bVar bVar bVar) (stateVar q)) ++
  A.trans.map (fun t => .fLe (letterChildren t.2.1 (stateVar t.2.2) bVar) (stateVar t.1)) ++
  (A.trans.filter fun t => A.init t.1).map
    (fun t => .fLe (letterChildren t.2.1 (stateVar t.2.2) bVar) yVar)

/-- The literal count: four, one per state, one per transition, and one per transition
from an initial state. -/
theorem rejectionSystem_length (n : ℕ) {m : ℕ} (A : BinNFA m) :
    (rejectionSystem n A).length =
      m + A.trans.length + (A.trans.filter fun t => A.init t.1).length + 4 := by
  simp only [rejectionSystem, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]
  omega

/-- The system has at most `m + 2 T + 4` literals for `m` states and `T` transitions. -/
theorem rejectionSystem_length_le (n : ℕ) {m : ℕ} (A : BinNFA m) :
    (rejectionSystem n A).length ≤ m + 2 * A.trans.length + 4 := by
  have := List.length_filter_le (fun t => A.init t.1) A.trans
  rw [rejectionSystem_length]
  omega

/-- The solutions of the system, literal by literal. -/
theorem covSat_rejectionSystem_iff {n m : ℕ} (A : BinNFA m) (ρ : V (m + 4) → Tree n) :
    Covariant.Sat ρ (rejectionSystem n A) ↔
      ρ bVar = Tree.bot ∧
      ρ gVar ≤ Tree.node (binaryChildren (ρ gVar) (ρ gVar) (ρ bVar)) ∧
      ρ xVar ≤ Tree.node (binaryChildren (ρ gVar) (ρ gVar) (ρ bVar)) ∧
      Tree.node (binaryChildren (ρ bVar) (ρ bVar) (ρ bVar)) ≤ ρ yVar ∧
      (∀ q, Tree.node (binaryChildren (ρ bVar) (ρ bVar) (ρ bVar)) ≤ ρ (stateVar q)) ∧
      (∀ q a r, (q, a, r) ∈ A.trans →
        Tree.node (letterChildren a (ρ (stateVar r)) (ρ bVar)) ≤ ρ (stateVar q)) ∧
      (∀ q a r, (q, a, r) ∈ A.trans → A.init q = true →
        Tree.node (letterChildren a (ρ (stateVar r)) (ρ bVar)) ≤ ρ yVar) := by
  simp only [rejectionSystem, Covariant.sat_append, Covariant.sat_cons, Covariant.sat_map,
    Covariant.sat_nil, Covariant.holds, comp_binaryChildren, comp_letterChildren,
    List.mem_finRange, List.mem_filter, true_implies, Prod.forall, and_imp, and_true,
    and_assoc]

end DeciNSSE.Complexity
