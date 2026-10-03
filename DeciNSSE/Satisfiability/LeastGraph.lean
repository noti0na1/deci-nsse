import Mathlib.Data.Fintype.Powerset
import Mathlib.Logic.Equiv.Finset
import DeciNSSE.Satisfiability.Least

/-! # Finite graphs for least solutions

Sets of reachable lower variables give finitely many states for the least
solution. Unfolding the resulting graph proves that satisfiable constraints
always have regular-tree solutions.
-/

namespace DeciNSSE

variable {k : ℕ}

def lowerSet (ϕ : Constraint k) (z : V k) : List (Fin 2) → Finset (V k)
  | [] => Finset.univ.filter (fun y => derivesB ϕ y z = true)
  | i :: π => Finset.univ.filter (fun x => ∃ u z₁ z₂,
      Lit.fLe z₁ z₂ u ∈ ϕ ∧ derivesB ϕ u z = true ∧
        x ∈ lowerSet ϕ (if i = 0 then z₁ else z₂) π)

theorem mem_lowerSet (ϕ : Constraint k) (z y : V k) (π : List (Fin 2)) :
    y ∈ lowerSet ϕ z π ↔ LowerAt ϕ π y z := by
  induction π generalizing z with
  | nil => simp [lowerSet, derivesB_iff]
  | cons i π ih =>
    simp only [lowerSet, Finset.mem_filter, Finset.mem_univ, true_and,
      derivesB_iff, ih]
    constructor
    · rintro ⟨u, z₁, z₂, hl, hd, hp⟩
      exact .cons hl hd hp
    · intro h
      cases h with
      | cons hl hd hp => exact ⟨_, _, _, hl, hd, hp⟩

theorem lowerAt_append_singleton_iff (ϕ : Constraint k) (π : List (Fin 2))
    (i : Fin 2) (x y : V k) :
    LowerAt ϕ (π ++ [i]) x y ↔ ∃ z z₁ z₂,
      LowerAt ϕ π z y ∧ Lit.fLe z₁ z₂ z ∈ ϕ ∧
        Derives ϕ x (if i = 0 then z₁ else z₂) := by
  induction π generalizing y with
  | nil =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp => exact ⟨_, _, _, .nil hd, hl, lowerAt_nil_iff.mp hp⟩
    · rintro ⟨z, z₁, z₂, hp, hl, hd⟩
      exact .cons hl (lowerAt_nil_iff.mp hp) (.nil hd)
  | cons j π ih =>
    constructor
    · intro h
      cases h with
      | cons hl hd hp =>
        obtain ⟨z, z₁, z₂, hp, hfl, hdx⟩ := (ih _).mp hp
        exact ⟨z, z₁, z₂, .cons hl hd hp, hfl, hdx⟩
    · rintro ⟨z, z₁, z₂, hp, hfl, hdx⟩
      cases hp with
      | cons hl hd hp =>
        exact .cons hl hd ((ih _).mpr ⟨z, z₁, z₂, hp, hfl, hdx⟩)

def step (ϕ : Constraint k) (S : Finset (V k)) (i : Fin 2) : Finset (V k) :=
  Finset.univ.filter (fun x => ∃ z ∈ S, ∃ z₁ z₂,
    Lit.fLe z₁ z₂ z ∈ ϕ ∧ derivesB ϕ x (if i = 0 then z₁ else z₂) = true)

theorem mem_step (ϕ : Constraint k) (S : Finset (V k)) (i : Fin 2) (x : V k) :
    x ∈ step ϕ S i ↔ ∃ z ∈ S, ∃ z₁ z₂,
      Lit.fLe z₁ z₂ z ∈ ϕ ∧ Derives ϕ x (if i = 0 then z₁ else z₂) := by
  simp [step, derivesB_iff]

theorem lowerSet_append (ϕ : Constraint k) (z : V k) (π : List (Fin 2))
    (i : Fin 2) : lowerSet ϕ z (π ++ [i]) = step ϕ (lowerSet ϕ z π) i := by
  ext x
  simp only [mem_lowerSet, mem_step, lowerAt_append_singleton_iff]
  aesop

def labelOf (ϕ : Constraint k) (S : Finset (V k)) : Sym :=
  if ∃ y ∈ S, Lit.eqTop y ∈ ϕ then .top
  else if ∃ y ∈ S, ∃ y₁ y₂, Lit.fLe y₁ y₂ y ∈ ϕ then .f else .bot

theorem labelOf_lowerSet (ϕ : Constraint k) (z : V k) (π : List (Fin 2)) :
    labelOf ϕ (lowerSet ϕ z π) = lowSup ϕ z π := by
  classical
  have ht : (∃ y ∈ lowerSet ϕ z π, Lit.eqTop y ∈ ϕ) ↔
      LowerLabel ϕ π .top z := by
    simp [mem_lowerSet, LowerLabel, and_comm]
  have hf : (∃ y ∈ lowerSet ϕ z π, ∃ y₁ y₂, Lit.fLe y₁ y₂ y ∈ ϕ) ↔
      LowerLabel ϕ π .f z := by
    simp only [mem_lowerSet, LowerLabel]
    aesop
  simp only [labelOf, lowSup, ht, hf]

namespace LeastGraph

def stateEquiv (k : ℕ) : Finset (V k) ≃ Fin (Fintype.card (Finset (V k))) :=
  Encodable.fintypeEquivFin

end LeastGraph

def leastGraph (ϕ : Constraint k) (z : V k) : RGraph where
  n := Fintype.card (Finset (V k))
  root := LeastGraph.stateEquiv k (lowerSet ϕ z [])
  label p := labelOf ϕ ((LeastGraph.stateEquiv k).symm p)
  child p i := LeastGraph.stateEquiv k (step ϕ ((LeastGraph.stateEquiv k).symm p) i)

theorem leastGraph_label (ϕ : Constraint k) (z : V k) (S : Finset (V k)) :
    (leastGraph ϕ z).label (LeastGraph.stateEquiv k S) = labelOf ϕ S := by
  simp [leastGraph]

theorem leastGraph_child (ϕ : Constraint k) (z : V k) (S : Finset (V k))
    (i : Fin 2) :
    (leastGraph ϕ z).child (LeastGraph.stateEquiv k S) i =
      LeastGraph.stateEquiv k (step ϕ S i) := by
  simp [leastGraph]

open Classical in

theorem leastGraph_walk (ϕ : Constraint k) (z : V k) (π : List (Fin 2)) :
    (leastGraph ϕ z).walk π =
      if LeastConstruction.Active (lowSup ϕ z) π then
        some (LeastGraph.stateEquiv k (lowerSet ϕ z π)) else none := by
  classical
  induction π using List.reverseRecOn with
  | nil => simp [RGraph.walk, RGraph.walkFrom, leastGraph]
  | append_singleton π i ih =>
    rw [RGraph.walk_append_singleton, ih, LeastConstruction.active_append_singleton]
    by_cases ha : LeastConstruction.Active (lowSup ϕ z) π
    · simp [ha, Option.bind, leastGraph_label, leastGraph_child,
        labelOf_lowerSet, lowerSet_append]
      rfl
    · simp [ha, Option.bind]
      rfl

theorem unfold_leastGraph (ϕ : Constraint k) (z : V k) :
    (leastGraph ϕ z).unfold = least ϕ z := by
  classical
  apply Tree.ext
  funext π
  rw [RGraph.unfold_fn, leastGraph_walk, least_fn]
  by_cases ha : LeastConstruction.Active (lowSup ϕ z) π
  · simp [ha, Option.map, leastGraph_label, labelOf_lowerSet]
  · simp [ha, Option.map]

theorem sat_regular_of_sat {ϕ : Constraint k} (h : ∃ ρ, Sat ρ ϕ) :
    ∃ σ : V k → RGraph, Sat (RGraph.unfold ∘ σ) ϕ := by
  refine ⟨leastGraph ϕ, ?_⟩
  have he : RGraph.unfold ∘ leastGraph ϕ = least ϕ :=
    funext (unfold_leastGraph ϕ)
  rw [he]
  exact least_sat (satisfiable_iff_not_labelClash.mp h)

end DeciNSSE
