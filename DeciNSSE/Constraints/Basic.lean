import DeciNSSE.Semantics.Finite
import DeciNSSE.Semantics.Regular
import DeciNSSE.Semantics.Safety

/-! # Flat constraints and entailment

A constraint system is a finite list of constructor inequalities and equations
to bottom or top. `Sat c ρ ϕ` means satisfaction by the specified valuation;
`Satisfiable c ϕ` existentially quantifies it. Entailment quantifies over all
solutions in the chosen tree domain.

## Main declarations
- `Lit`, `Constraint`, `Sat`, `Satisfiable`, `SatisfiableFin`
- `Entails`, `EntailsReg`, `EntailsFin`
- `Covariant.Sat`, with `sat_false` and the list lemmas `Covariant.sat_cons`,
  `Covariant.sat_append` and `Covariant.sat_map`
- `entails_iff_safe`: entailment as preservation of top and bottom prefixes
-/

namespace DeciNSSE
/-- The finite set of variables of a constraint system. -/
abbrev V (k : ℕ) := Fin k

/-- Flat constructor inequalities and equations to bottom or top. -/
inductive Lit (n k : ℕ) where
  /-- `leF x a` is the inequality `x ≤ f(a)`. -/
  | leF (x : V k) (children : Fin n → V k)
  /-- `fLe a x` is the inequality `f(a) ≤ x`. -/
  | fLe (children : Fin n → V k) (x : V k)
  /-- `eqBot x` is the equation `x = ⊥`. -/
  | eqBot (x : V k)
  /-- `eqTop x` is the equation `x = ⊤`. -/
  | eqTop (x : V k)

/-- A finite conjunction of flat literals, represented as a list. -/
abbrev Constraint (n k : ℕ) := List (Lit n k)

/-- Interpret a literal under the given variance and tree valuation. -/
def Lit.holds {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Tree n) : Lit n k → Prop
  | .leF x a => Tree.Le c (ρ x) (Tree.node (ρ ∘ a))
  | .fLe a x => Tree.Le c (Tree.node (ρ ∘ a)) (ρ x)
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- An assignment satisfies every literal under the given variance. -/
def Sat {n k : ℕ} (c : Fin n → Bool)
    (ρ : V k → Tree n) (ϕ : Constraint n k) : Prop :=
  ∀ l ∈ ϕ, Lit.holds c ρ l

/-- The constraint system has a solution by arbitrary trees. -/
abbrev Satisfiable {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) : Prop :=
  ∃ ρ, Sat c ρ ϕ

/-- The constraint system has a solution by finite trees. -/
abbrev SatisfiableFin {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) : Prop :=
  ∃ σ : V k → FTree n, Sat c (FTree.toTree ∘ σ) ϕ

/-- Every arbitrary-tree solution satisfies the queried variable inequality. -/
def Entails {n : ℕ} {k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Prop :=
  ∀ ρ, Sat c ρ ϕ → Tree.Le c (ρ x) (ρ y)

/-- Every solution represented by finite rooted graphs satisfies the query. -/
def EntailsReg {n : ℕ} {k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Prop :=
  ∀ σ : V k → RGraph n,
    Sat c (RGraph.unfold ∘ σ) ϕ →
      Tree.Le c (σ x).unfold (σ y).unfold

/-- Every solution by finite tree terms satisfies the query. -/
def EntailsFin {n : ℕ} {k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) : Prop :=
  ∀ σ : V k → FTree n,
    Sat c (FTree.toTree ∘ σ) ϕ →
      Tree.Le c (σ x).toTree (σ y).toTree

/-- Covariant satisfaction for the target of signed translation. -/
def Covariant.holds {n k : ℕ} (ρ : V k → Tree n) : Lit n k → Prop
  | .leF x a => ρ x ≤ Tree.node (ρ ∘ a)
  | .fLe a x => Tree.node (ρ ∘ a) ≤ ρ x
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- An assignment satisfies every literal in the covariant order. -/
def Covariant.Sat {n k : ℕ} (ρ : V k → Tree n) (ϕ : Constraint n k) : Prop :=
  ∀ l ∈ ϕ, Covariant.holds ρ l

namespace Covariant

variable {n k : ℕ} (ρ : V k → Tree n)

/-- The empty system is satisfied by every valuation. -/
theorem sat_nil : Covariant.Sat ρ ([] : Constraint n k) := fun _ h => absurd h List.not_mem_nil

/-- A system with a first literal is satisfied when the literal and the rest are. -/
theorem sat_cons (l : Lit n k) (ϕ : Constraint n k) :
    Covariant.Sat ρ (l :: ϕ) ↔ Covariant.holds ρ l ∧ Covariant.Sat ρ ϕ :=
  List.forall_mem_cons

/-- A concatenation is satisfied when both parts are. -/
theorem sat_append (ϕ ψ : Constraint n k) :
    Covariant.Sat ρ (ϕ ++ ψ) ↔ Covariant.Sat ρ ϕ ∧ Covariant.Sat ρ ψ :=
  List.forall_mem_append

/-- A system of the literals `f b` for `b ∈ l` is satisfied when each literal holds. -/
theorem sat_map {β : Type*} (f : β → Lit n k) (l : List β) :
    Covariant.Sat ρ (l.map f) ↔ ∀ b ∈ l, Covariant.holds ρ (f b) :=
  List.forall_mem_map

end Covariant

@[simp] theorem holds_false {n k : ℕ} (ρ : V k → Tree n) (l : Lit n k) :
    Lit.holds (fun _ => false) ρ l ↔ Covariant.holds ρ l := by
  cases l <;> simp [Lit.holds, Covariant.holds]

@[simp] theorem sat_false {n k : ℕ} (ρ : V k → Tree n) (ϕ : Constraint n k) :
    Sat (fun _ => false) ρ ϕ ↔ Covariant.Sat ρ ϕ := by simp [Sat, Covariant.Sat]

/-- Entailment is preservation of top and bottom prefixes in every solution. -/
theorem entails_iff_safe {n k : ℕ} (c : Fin n → Bool)
    (ϕ : Constraint n k) (x y : V k) :
    Entails c ϕ x y ↔ ∀ w ρ, Sat c ρ ϕ →
      (prefTop c w (ρ x) → prefTop c w (ρ y)) ∧
      (prefBot c w (ρ y) → prefBot c w (ρ x)) := by
  simp only [Entails, treeLe_iff_safe]
  constructor
  · intro h w ρ hs; exact h ρ hs w
  · intro h ρ hs w; exact h w ρ hs

end DeciNSSE
