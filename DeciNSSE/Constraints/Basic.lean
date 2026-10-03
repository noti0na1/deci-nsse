import DeciNSSE.Semantics.Regular

/-! # Flat constraints and entailment

A constraint system is a finite list of constructor inequalities and equations
to bottom or top. Entailment requires an inequality to hold in every solution,
over unrestricted trees, regular trees or finite trees.
-/

namespace DeciNSSE

/-- The finite set of variables of a constraint system. -/
abbrev V (k : ℕ) := Fin k

/-- Flat constructor inequalities and equations to bottom or top. -/
inductive Lit (k : ℕ) where
  | leF (x y₁ y₂ : V k)
  | fLe (y₁ y₂ x : V k)
  | eqBot (x : V k)
  | eqTop (x : V k)
  deriving DecidableEq, Repr

/-- A finite conjunction of flat literals, represented as a list. -/
abbrev Constraint (k : ℕ) := List (Lit k)

/-- Interpret a literal under an assignment of trees to variables. -/
def Lit.holds {k : ℕ} (ρ : V k → Tree) : Lit k → Prop
  | .leF x y₁ y₂ => ρ x ≤ Tree.node (ρ y₁) (ρ y₂)
  | .fLe y₁ y₂ x => Tree.node (ρ y₁) (ρ y₂) ≤ ρ x
  | .eqBot x => ρ x = Tree.bot
  | .eqTop x => ρ x = Tree.top

/-- An assignment satisfies every literal in the constraint system. -/
def Sat {k : ℕ} (ρ : V k → Tree) (ϕ : Constraint k) : Prop :=
  ∀ l ∈ ϕ, l.holds ρ

/-- Every solution by finite or infinite trees satisfies the indicated inequality. -/
def Entails {k : ℕ} (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ ρ, Sat ρ ϕ → ρ x ≤ ρ y

/-- Every finite-tree solution satisfies the indicated inequality. -/
def EntailsFin {k : ℕ} (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ → (σ x).toTree ≤ (σ y).toTree

/-- Every regular-tree solution satisfies the indicated inequality. -/
def EntailsReg {k : ℕ} (ϕ : Constraint k) (x y : V k) : Prop :=
  ∀ σ : V k → RGraph, Sat (RGraph.unfold ∘ σ) ϕ → (σ x).unfold ≤ (σ y).unfold

/-- Unrestricted entailment implies regular-tree entailment. -/
theorem Entails.toReg {k : ℕ} {ϕ : Constraint k} {x y : V k}
    (h : Entails ϕ x y) : EntailsReg ϕ x y := by
  intro σ hσ
  exact h (RGraph.unfold ∘ σ) hσ

/-- Regular-tree entailment implies finite-tree entailment. -/
theorem EntailsReg.toFin {k : ℕ} {ϕ : Constraint k} {x y : V k}
    (h : EntailsReg ϕ x y) : EntailsFin ϕ x y := by
  intro σ hσ
  have hemb : RGraph.unfold ∘ (FTree.toGraph ∘ σ) = FTree.toTree ∘ σ := by
    funext x
    exact FTree.unfold_toGraph (σ x)
  have hsat : Sat (RGraph.unfold ∘ (FTree.toGraph ∘ σ)) ϕ := by
    rw [hemb]
    exact hσ
  simpa only [Function.comp_apply, FTree.unfold_toGraph] using h (FTree.toGraph ∘ σ) hsat

/-- Unrestricted entailment implies finite-tree entailment. -/
theorem Entails.toFin {k : ℕ} {ϕ : Constraint k} {x y : V k}
    (h : Entails ϕ x y) : EntailsFin ϕ x y := h.toReg.toFin

end DeciNSSE
