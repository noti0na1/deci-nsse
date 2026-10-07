import DeciNSSE.Satisfiability.Least

/-! # A finite graph for the least solution

Sets of reachable lower bounds form the states of a finite graph whose
unfolding is the least solution. Every satisfiable covariant system therefore
has a regular solution.
-/

namespace DeciNSSE

variable {n k : ℕ}

/-- Compute lower bounds by reading the path from the root. -/
def lowerSet (ϕ : Constraint n k) (z : V k) : List (Fin n) → Finset (V k)
  | [] => Finset.univ.filter (fun y => derivesB ϕ y z = true)
  | i :: π => Finset.univ.filter (fun x => ∃ l ∈ lowerLits ϕ,
      derivesB ϕ l.2 z = true ∧ x ∈ lowerSet ϕ (l.1 i) π)

theorem mem_lowerSet (ϕ : Constraint n k) (z y : V k) (π : List (Fin n)) :
    y ∈ lowerSet ϕ z π ↔ LowerAt ϕ π y z := by
  induction π generalizing z with
  | nil => simp [lowerSet, derivesB_iff]
  | cons i π ih =>
    simp only [lowerSet, Finset.mem_filter, Finset.mem_univ, true_and,
      derivesB_iff, ih]
    constructor
    · rintro ⟨⟨a, u⟩, hl, hd, hp⟩
      exact .cons ((mem_lowerLits ϕ a u).mp hl) hd hp
    · intro h
      cases h with
      | @cons a u _ _ _ _ hl hd hp =>
        exact ⟨(a, u), (mem_lowerLits ϕ a u).mpr hl, hd, hp⟩

/-- The paper's end-append rule follows from the root-first path rules. -/
theorem lowerAt_append_singleton_iff (ϕ : Constraint n k) (π : List (Fin n))
    (i : Fin n) (x y : V k) :
    LowerAt ϕ (π ++ [i]) x y ↔ ∃ z a,
      LowerAt ϕ π z y ∧ Lit.fLe a z ∈ ϕ ∧ Derives ϕ x (a i) := by
  induction π generalizing y with
  | nil =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp => exact ⟨_, _, .nil hd, hl, lowerAt_nil_iff.mp hp⟩
    · rintro ⟨z, a, hp, hl, hd⟩
      exact .cons hl (lowerAt_nil_iff.mp hp) (.nil hd)
  | cons j π ih =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp =>
        obtain ⟨z, a, hp, hfl, hdx⟩ := (ih _).mp hp
        exact ⟨z, a, .cons hl hd hp, hfl, hdx⟩
    · rintro ⟨z, a, hp, hfl, hdx⟩
      cases hp with
      | cons hl hd hp =>
        exact .cons hl hd ((ih _).mpr ⟨z, a, hp, hfl, hdx⟩)

/-- A transition on lower sets, including the closure below the chosen child. -/
def step (ϕ : Constraint n k) (S : Finset (V k)) (i : Fin n) : Finset (V k) :=
  Finset.univ.filter (fun x => ∃ l ∈ lowerLits ϕ, l.2 ∈ S ∧ derivesB ϕ x (l.1 i) = true)

theorem mem_step (ϕ : Constraint n k) (S : Finset (V k)) (i : Fin n) (x : V k) :
    x ∈ step ϕ S i ↔ ∃ z ∈ S, ∃ a, Lit.fLe a z ∈ ϕ ∧ Derives ϕ x (a i) := by
  simp only [step, Finset.mem_filter, Finset.mem_univ, true_and, derivesB_iff]
  constructor
  · rintro ⟨⟨a, z⟩, hl, hz, hd⟩
    exact ⟨z, hz, a, (mem_lowerLits ϕ a z).mp hl, hd⟩
  · rintro ⟨z, hz, a, hl, hd⟩
    exact ⟨(a, z), (mem_lowerLits ϕ a z).mpr hl, hz, hd⟩

theorem lowerSet_append (ϕ : Constraint n k) (z : V k) (π : List (Fin n))
    (i : Fin n) : lowerSet ϕ z (π ++ [i]) = step ϕ (lowerSet ϕ z π) i := by
  ext x
  simp only [mem_lowerSet, mem_step, lowerAt_append_singleton_iff]
  constructor
  · rintro ⟨w, a, hp, hl, hd⟩
    exact ⟨w, hp, a, hl, hd⟩
  · rintro ⟨w, hp, a, hl, hd⟩
    exact ⟨w, a, hp, hl, hd⟩

/-- The greatest label supported by a finite set of lower bounds. -/
def labelOf (ϕ : Constraint n k) (S : Finset (V k)) : Sym :=
  if ∃ y ∈ S, y ∈ topVars ϕ then .top
  else if ∃ y ∈ S, ∃ l ∈ lowerLits ϕ, l.2 = y then .f else .bot

theorem labelOf_lowerSet (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    labelOf ϕ (lowerSet ϕ z π) = lowSup ϕ z π := by
  classical
  have ht : (∃ y ∈ lowerSet ϕ z π, y ∈ topVars ϕ) ↔ LowerLabel ϕ π .top z := by
    simp only [mem_lowerSet, mem_topVars, LowerLabel]
    constructor
    · rintro ⟨y, hp, ht⟩; exact ⟨y, ht, hp⟩
    · rintro ⟨y, ht, hp⟩; exact ⟨y, hp, ht⟩
  have hf : (∃ y ∈ lowerSet ϕ z π, ∃ l ∈ lowerLits ϕ, l.2 = y) ↔
      LowerLabel ϕ π .f z := by
    simp only [mem_lowerSet, LowerLabel]
    constructor
    · rintro ⟨y, hp, ⟨a, u⟩, hl, rfl⟩
      exact ⟨a, u, (mem_lowerLits ϕ a u).mp hl, hp⟩
    · rintro ⟨a, y, hl, hp⟩
      exact ⟨y, hp, (a, y), (mem_lowerLits ϕ a y).mpr hl, rfl⟩
  unfold labelOf lowSup
  simp only [ht, hf]

namespace LeastGraph

/-- Enumerate all finite subsets using their computable `Encodable` instance. -/
def stateEquiv (k : ℕ) : Finset (V k) ≃ Fin (Fintype.card (Finset (V k))) :=
  Encodable.fintypeEquivFin

end LeastGraph

/-- All lower sets are states; only states reached through `f` are unfolded. -/
def leastGraph (ϕ : Constraint n k) (z : V k) : RGraph n where
  size := Fintype.card (Finset (V k))
  root := LeastGraph.stateEquiv k (lowerSet ϕ z [])
  label p := labelOf ϕ ((LeastGraph.stateEquiv k).symm p)
  child p i := LeastGraph.stateEquiv k (step ϕ ((LeastGraph.stateEquiv k).symm p) i)

theorem leastGraph_label (ϕ : Constraint n k) (z : V k) (S : Finset (V k)) :
    (leastGraph ϕ z).label (LeastGraph.stateEquiv k S) = labelOf ϕ S := by
  simp [leastGraph]

theorem leastGraph_child (ϕ : Constraint n k) (z : V k) (S : Finset (V k))
    (i : Fin n) :
    (leastGraph ϕ z).child (LeastGraph.stateEquiv k S) i =
      LeastGraph.stateEquiv k (step ϕ S i) := by
  simp [leastGraph]

open Classical in

/-- A walk reaches the lower set exactly when all proper prefixes have label `f`. -/
theorem leastGraph_walk (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    (leastGraph ϕ z).walk π =
      if Active (lowSup ϕ z) π then
        some (LeastGraph.stateEquiv k (lowerSet ϕ z π)) else none := by
  classical
  induction π using List.reverseRecOn with
  | nil => simp [RGraph.walk, RGraph.walkFrom, leastGraph]
  | append_singleton π i ih =>
    rw [RGraph.walk_append_singleton, ih, active_append_singleton]
    by_cases ha : Active (lowSup ϕ z) π
    · simp [ha, Option.bind, leastGraph_label, leastGraph_child,
        labelOf_lowerSet, lowerSet_append]
      rfl
    · simp [ha, Option.bind]
      rfl

/-- The executable graph presents the semantic least tree, even for clashing constraints. -/
theorem unfold_leastGraph (ϕ : Constraint n k) (z : V k) :
    (leastGraph ϕ z).unfold = least ϕ z := by
  classical
  apply Tree.ext
  funext π
  rw [RGraph.unfold_fn, leastGraph_walk, least_fn]
  by_cases ha : Active (lowSup ϕ z) π
  · simp [ha, Option.map, leastGraph_label, labelOf_lowerSet]
  · simp [ha, Option.map]

theorem unfold_comp_leastGraph (ϕ : Constraint n k) :
    RGraph.unfold ∘ leastGraph ϕ = least ϕ :=
  funext (unfold_leastGraph ϕ)

/-- The least graph is a regular solution whenever there is no label clash. -/
theorem leastGraph_sat {ϕ : Constraint n k} (hn : ¬ LabelClash ϕ) :
    Covariant.Sat (RGraph.unfold ∘ leastGraph ϕ) ϕ := by
  rw [unfold_comp_leastGraph]
  exact least_sat hn

end DeciNSSE
