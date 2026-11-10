import DeciNSSE.Satisfiability.Finite

/-! # Finite searches for satisfiability

The finite closure decides label clashes, and reachability in a finite graph on
pairs of variables decides cycle clashes; together they decide finite-tree covariant
satisfiability. Path judgments are computed by recursion over the
path with a precomputed closure.

## Main declarations

- `PathDecision.lower`, `PathDecision.upper`, `lowerAtB`, `upperAtB`, `lowerAtB_iff`,
  `upperAtB_iff`: executable lower and upper path judgments.
- `cycleClashB`, `cycleClashB_iff`: the cycle-clash test.
- `Covariant.satFinB`, `Covariant.satFinB_iff`: covariant satisfiability over finite trees.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace PathDecision

/-- The lower path judgment over a precomputed closure `pairs`. The closure is passed as
data, so the recursion does not recompute it. -/
def lower (ϕ : Constraint n k) (pairs : Finset (V k × V k)) :
    List (Fin n) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => (lowerLits ϕ).any fun l =>
      decide ((l.2, y) ∈ pairs) && lower ϕ pairs π x (l.1 i)

/-- The upper path judgment over a precomputed closure `pairs`, by the symmetric
recursion. -/
def upper (ϕ : Constraint n k) (pairs : Finset (V k × V k)) :
    List (Fin n) → V k → V k → Bool
  | [], x, y => decide ((x, y) ∈ pairs)
  | i :: π, x, y => (upperLits ϕ).any fun m =>
      decide ((x, m.1) ∈ pairs) && upper ϕ pairs π (m.2 i) y

end PathDecision

/-- Read a lower path judgment from the root, searching the finite literal list. -/
def lowerAtB (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) : Bool :=
  PathDecision.lower ϕ (derivedPairs ϕ) π x y

/-- The symmetric executable upper path judgment. -/
def upperAtB (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) : Bool :=
  PathDecision.upper ϕ (derivedPairs ϕ) π x y

/-- The Boolean lower-path test agrees with the inductive path judgment. -/
theorem lowerAtB_iff (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) :
    lowerAtB ϕ π x y = true ↔ LowerAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [lowerAtB, PathDecision.lower, mem_derivedPairs]
  | cons i π ih =>
    change ((lowerLits ϕ).any fun l =>
      derivesB ϕ l.2 y && lowerAtB ϕ π x (l.1 i)) = true ↔ _
    simp only [List.any_eq_true, Bool.and_eq_true, derivesB_iff, ih]
    constructor
    · rintro ⟨⟨a, u⟩, hl, hd, hp⟩
      exact .cons ((mem_lowerLits ϕ a u).mp hl) hd hp
    · intro h
      cases h with
      | @cons a u _ _ _ _ hl hd hp =>
        exact ⟨(a, u), (mem_lowerLits ϕ a u).mpr hl, hd, hp⟩

/-- The Boolean upper-path test agrees with the inductive path judgment. -/
theorem upperAtB_iff (ϕ : Constraint n k) (π : List (Fin n)) (x y : V k) :
    upperAtB ϕ π x y = true ↔ UpperAt ϕ π x y := by
  induction π generalizing x y with
  | nil => simp [upperAtB, PathDecision.upper, mem_derivedPairs]
  | cons i π ih =>
    change ((upperLits ϕ).any fun m =>
      derivesB ϕ x m.1 && upperAtB ϕ π (m.2 i) y) = true ↔ _
    simp only [List.any_eq_true, Bool.and_eq_true, derivesB_iff, ih]
    constructor
    · rintro ⟨⟨v, b⟩, hm, hd, hp⟩
      exact .cons hd ((mem_upperLits ϕ v b).mp hm) hp
    · intro h
      cases h with
      | @cons _ v b _ _ _ hd hm hp =>
        exact ⟨(v, b), (mem_upperLits ϕ v b).mpr hm, hd, hp⟩

/-- The successors of a pair of variables in the cycle graph, over a precomputed
closure. -/
def cycleNext (ϕ : Constraint n k) (pairs : Finset (V k × V k)) (p : V k × V k) :
    Finset (V k × V k) :=
  Finset.univ.filter fun q => ∃ i : Fin n,
    PathDecision.lower ϕ pairs [i] q.1 p.1 = true ∧ PathDecision.upper ϕ pairs [i] p.2 q.2 = true

theorem mem_cycleNext (ϕ : Constraint n k) (p q : V k × V k) :
    q ∈ cycleNext ϕ (derivedPairs ϕ) p ↔ CycleStep ϕ p q := by
  simp only [cycleNext, Finset.mem_filter, Finset.mem_univ, true_and, CycleStep]
  exact exists_congr fun i => and_congr (lowerAtB_iff ϕ [i] q.1 p.1) (upperAtB_iff ϕ [i] p.2 q.2)

/-- Search for a derived pair of variables that is reachable from one of its successors
in the cycle graph. -/
def cycleClashB (ϕ : Constraint n k) : Bool :=
  let pairs := derivedPairs ϕ
  let next := cycleNext ϕ pairs
  decide (∃ p ∈ pairs, ∃ q ∈ next p, p ∈ Saturation.reachSet next q)

/-- The cycle-clash test decides whether the system has a cycle clash. -/
theorem cycleClashB_iff (ϕ : Constraint n k) : cycleClashB ϕ = true ↔ CycleClash ϕ := by
  simp only [cycleClashB, decide_eq_true_eq, cycleClash_iff_transGen, Prod.exists,
    mem_derivedPairs, Saturation.mem_reachSet, mem_cycleNext, Relation.TransGen.head'_iff]

/-- Satisfiability over finite trees. -/
def Covariant.satFinB (ϕ : Constraint n k) : Bool := !labelClashB ϕ && !cycleClashB ϕ

/-- The finite test succeeds exactly without label and cycle clashes. -/
theorem Covariant.satFinB_iff_not_clash (ϕ : Constraint n k) :
    Covariant.satFinB ϕ = true ↔ ¬ LabelClash ϕ ∧ ¬ CycleClash ϕ := by
  simp only [Covariant.satFinB, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    labelClashB_iff, cycleClashB_iff]

/-- The covariant finite satisfiability test succeeds exactly when a finite solution exists. -/
theorem Covariant.satFinB_iff (ϕ : Constraint n k) :
    Covariant.satFinB ϕ = true ↔ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  rw [satFin_iff, Covariant.satFinB_iff_not_clash]

end DeciNSSE
