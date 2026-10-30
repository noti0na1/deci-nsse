import Mathlib.Data.BitVec
import DeciNSSE.Solver.Reader
import DeciNSSE.Solver.Graph

/-! # Reachable regular countermodels

Packed bound sets present the same least shape. Restricting the selected,
decoded graphs to reachable states preserves their unfolding.
-/

namespace DeciNSSE.Solver
open Mask
attribute [-simp] BitVec.getLsbD_eq_getElem
variable {n m k : ℕ}

/-- Extend lower labels by one literal and its closure row. -/
def shapeStep (ψ : Constraint n m) (d : Rows m) (s : BitVec m) (i : Fin n) : BitVec m :=
  union (lowerLits ψ) fun p => if s.getLsbD p.2 then d (p.1 i) else BitVec.zero _

theorem shapeStep_spec (ψ : Constraint n m) (s : BitVec m) (i : Fin n) :
    decode (shapeStep ψ (inverseRows (derivedRows ψ)) s i) = DeciNSSE.step ψ (decode s) i := by
  ext x
  simp only [mem_decode, shapeStep, bit_union, DeciNSSE.step, Finset.mem_filter,
    Finset.mem_univ, true_and, derivesB_iff, mem_decode]
  apply exists_congr; intro p
  apply and_congr_right; intro _
  split <;> rename_i h
  · simp [h]
  · simp [h]

/-- Cached predicates and transitions for the least-shape graph. -/
structure ShapeReader (n m : ℕ) where
  initial : V m → BitVec m × BitVec m
  next : (BitVec m × BitVec m) → Fin n → BitVec m × BitVec m
  label : (BitVec m × BitVec m) → Sym

def shapeReader (ψ : Constraint n m) : ShapeReader n m :=
  let dl := inverseRows (derivedRows ψ)
  let du := inverseRows (derivedRows (Constraint.dual ψ))
  let lo := ofList ((lowerLits ψ).map Prod.snd)
  let up := ofList ((lowerLits (Constraint.dual ψ)).map Prod.snd)
  let bot := ofList (topVars (Constraint.dual ψ))
  ⟨fun z => (dl z, du z),
    fun s i => (shapeStep ψ dl s.1 i, shapeStep (Constraint.dual ψ) du s.2 i),
    fun s => if meets s.1 lo && meets s.2 up then .f
      else if !(meets s.1 lo) && (meets s.2 bot || meets s.2 up) then .bot else .top⟩

private def decodePair (s : BitVec m × BitVec m) : Finset (V m) × Finset (V m) :=
  (decode s.1, decode s.2)

theorem shapeReader_initial (ψ : Constraint n m) (z : V m) :
    decodePair ((shapeReader ψ).initial z) = boundSets ψ z [] := by
  apply Prod.ext <;> ext x <;>
    simp [decodePair, shapeReader, boundSets, lowerSet, derivesB_iff]

theorem shapeReader_next (ψ : Constraint n m) (s : BitVec m × BitVec m) (i : Fin n) :
    decodePair ((shapeReader ψ).next s i) =
      (DeciNSSE.step ψ (decodePair s).1 i,
       DeciNSSE.step (Constraint.dual ψ) (decodePair s).2 i) := by
  exact Prod.ext (shapeStep_spec ψ s.1 i) (shapeStep_spec (Constraint.dual ψ) s.2 i)

theorem shapeReader_label (ψ : Constraint n m) (s : BitVec m × BitVec m) :
    (shapeReader ψ).label s = shapeLabelOf ψ (decodePair s) := by
  have hf (φ : Constraint n m) (v : BitVec m) :
      meets v (ofList ((lowerLits φ).map Prod.snd)) = true ↔ SupportsF φ (decode v) := by
    simp only [meets_iff, bit_ofList, List.mem_map, SupportsF, mem_decode]
  have ht (φ : Constraint n m) (v : BitVec m) :
      meets v (ofList (topVars φ)) = true ↔ SupportsTop φ (decode v) := by
    simp [SupportsTop]
  simp only [shapeReader, shapeLabelOf, decodePair, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hf, ht]
  rfl

/-- Changing the state representation preserves a graph's unfolding. -/
theorem unfold_ofEquiv_map {S T : Type} {a b : ℕ} (e : S ≃ Fin a) (e' : T ≃ Fin b)
    (f : S → T) (root : S) (label : S → Sym) (child : S → Fin n → S)
    (label' : T → Sym) (child' : T → Fin n → T)
    (hl : ∀ s, label s = label' (f s))
    (hc : ∀ s i, f (child s i) = child' (f s) i) :
    (RGraph.ofEquiv e root label child).unfold =
      (RGraph.ofEquiv e' (f root) label' child').unfold := by
  let g := RGraph.ofEquiv e root label child
  let g' := RGraph.ofEquiv e' (f root) label' child'
  have hw (w : List (Fin n)) (s : S) :
      (g.walkFrom (e s) w).map g.label = (g'.walkFrom (e' (f s)) w).map g'.label := by
    induction w generalizing s with
    | nil => simp [g, g', RGraph.walkFrom, RGraph.ofEquiv, hl]
    | cons i w ih =>
      simp only [RGraph.walkFrom, g, g', RGraph.ofEquiv, Equiv.symm_apply_apply, hl]
      split
      · simpa only [g, g', RGraph.ofEquiv, hc, hl] using ih (child s i)
      · rfl
  exact Tree.ext (funext fun w => hw w root)

/-- A binary numbering of packed bound pairs. -/
def pairEquiv (m : ℕ) : (BitVec m × BitVec m) ≃ Fin (2 ^ m * 2 ^ m) :=
  (Equiv.prodCongr BitVec.equivFin.toEquiv BitVec.equivFin.toEquiv).trans finProdFinEquiv

/-- A finite array of rooted graphs. -/
abbrev GraphFamily (n m : ℕ) := Table m (RGraph n)

/-- A shared family of packed least-shape graphs. -/
def packedShapes (ψ : Constraint n m) : GraphFamily n m :=
  let r := shapeReader (ψ.map cacheLiteral)
  table fun z => RGraph.ofEquiv (pairEquiv m) (r.initial z) r.label r.next

theorem unfold_packedShapes (ψ : Constraint n m) (z : V m) :
    (packedShapes ψ z).unfold = (shapeGraph ψ z).unfold := by
  simp only [packedShapes, map_cacheLiteral, table_eq]
  unfold shapeGraph
  rw [← shapeReader_initial]
  exact unfold_ofEquiv_map _ _ decodePair _ _ _ _ _ (shapeReader_label ψ) (shapeReader_next ψ)

/-- Selection and decoding of the packed least shape of the spine extension. -/
def packedRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : GraphFamily n k :=
  let ψ := Events.sideSystem c ϕ θ
  let q := Events.sideQuery x y θ
  let graphs := selectGraph c (packedShapes (Spine.extension c ψ q.1 q.2 w))
  let witness := fun z => graphs (Spine.Closure.lift z)
  match θ with
  | .l => table (decodedGraph c witness)
  | .r => table (decodedGraph c (witness ∘ FiniteVariance.flipV))

theorem unfold_packedRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) :
    (packedRegular c ϕ x y θ w z).unfold = (extractRegular c ϕ x y θ w z).unfold := by
  have hm {j : ℕ} (ψ : Constraint n (2 * j)) (hf : FiniteVariance.FlipClosed ψ)
      (u : V (2 * j)) :
      (selectGraph c (packedShapes ψ) u).unfold =
        (selectGraph c (shapeGraph ψ) u).unfold := by
    have hg : RGraph.unfold ∘ packedShapes ψ = leastShape ψ :=
      funext fun v => (unfold_packedShapes ψ v).trans (unfold_shapeGraph ψ v)
    exact congrFun ((unfold_selectGraph c hg (FiniteVariance.leastShape_sameShape_dual hf)).trans
      (unfold_selectGraph_shapeGraph c hf).symm) u
  have hf := Spine.Closure.extension_flipClosed (c := c) (X := (Events.sideQuery x y θ).1)
    (Y := (Events.sideQuery x y θ).2) (w := w) (Events.sideSystem_flipClosed (c := c) (ϕ := ϕ) θ)
  cases θ <;> simp only [packedRegular, table_eq, extractRegular, RegularTransfer.countermodel,
    RegularTransfer.witnessGraph, Events.sideSystem, Events.sideQuery, decodedGraph,
    RGraph.unfold_normalize, Function.comp_apply] at *
  all_goals congr 1; exact hm _ hf _

/-- Extract only the reachable part of each regular countermodel graph. -/
def extractReachable (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : GraphFamily n k :=
  let gs := packedRegular c ϕ x y θ w
  table fun z => (gs z).compact

theorem extractReachable_unfold (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) :
    (extractReachable c ϕ x y θ w z).unfold = (extractRegular c ϕ x y θ w z).unfold := by
  simp only [extractReachable, table_eq, RGraph.unfold_compact, unfold_packedRegular]

end DeciNSSE.Solver
