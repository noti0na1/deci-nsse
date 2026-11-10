import Mathlib.Data.BitVec
import DeciNSSE.Solver.Reader
import DeciNSSE.Solver.Graph

/-! # Reachable regular countermodels

Packed bound sets present the same least shape. Restricting the variance
graphs to reachable states preserves their unfolding.

## Main declarations

- `Solver.shapeReader`: the packed bound-set automaton of a covariant system.
- `Solver.packedShapes`, `Solver.unfold_packedShapes`: packed graphs of the least shapes.
- `Solver.packedRegular`, `Solver.unfold_packedRegular`: the packed graphs of the regular
  countermodel `extractRegular`.
- `Solver.extractReachable`, `Solver.extractReachable_unfold`: their reachable parts, with
  the unfolding of `extractRegular`.
-/

namespace DeciNSSE.Solver
open Mask
attribute [-simp] BitVec.getLsbD_eq_getElem
variable {n m k : ℕ}

/-- Cached predicates and transitions for the least-shape graph. -/
structure ShapeReader (n m : ℕ) where
  initial : V m → BitVec m × BitVec m
  next : (BitVec m × BitVec m) → Fin n → BitVec m × BitVec m
  label : (BitVec m × BitVec m) → Sym

/-- The packed bound-set automaton of `ψ`, with the transition matrices of the packed
label reader. -/
def shapeReader (ψ : Constraint n m) : ShapeReader n m :=
  let d := derivedRows ψ
  let di := inverseRows d
  let lower := lowerRows ψ d
  let upper := upperRows ψ d
  let lo := ofList ((lowerLits ψ).map Prod.snd)
  let up := ofList ((upperLits ψ).map Prod.fst)
  let bot := ofList (botVars ψ)
  ⟨fun z => (di z, d z),
    fun s i => (image (lower i) s.1, image (upper i) s.2),
    fun s => if meets s.1 lo && meets s.2 up then .f
      else if !(meets s.1 lo) && (meets s.2 bot || meets s.2 up) then .bot else .top⟩

private def decodePair (s : BitVec m × BitVec m) : Finset (V m) × Finset (V m) :=
  (decode s.1, decode s.2)

theorem shapeReader_initial (ψ : Constraint n m) (z : V m) :
    decodePair ((shapeReader ψ).initial z) = boundSets ψ z [] := by
  apply Prod.ext <;> ext x <;> simp [decodePair, shapeReader, boundSets]

theorem shapeReader_next (ψ : Constraint n m) (s : BitVec m × BitVec m) (i : Fin n) :
    decodePair ((shapeReader ψ).next s i) = boundStep ψ (decodePair s) i := by
  apply Prod.ext <;> ext x
  · simp only [shapeReader, decodePair, boundStep, mem_decode, bit_image, lowerStep,
      Finset.mem_filter, Finset.mem_univ, true_and, lowerRows_spec]
  · simp only [shapeReader, decodePair, boundStep, mem_decode, bit_image, upperStep,
      Finset.mem_filter, Finset.mem_univ, true_and, upperRows_spec]

theorem shapeReader_label (ψ : Constraint n m) (s : BitVec m × BitVec m) :
    (shapeReader ψ).label s = shapeLabelOf ψ (decodePair s) := by
  have hl (v : BitVec m) :
      meets v (ofList ((lowerLits ψ).map Prod.snd)) = true ↔ SupportsF ψ (decode v) := by
    simp only [meets_iff, bit_ofList, List.mem_map, SupportsF, mem_decode]
  have hu (v : BitVec m) :
      meets v (ofList ((upperLits ψ).map Prod.fst)) = true ↔ LimitsF ψ (decode v) := by
    simp only [meets_iff, bit_ofList, List.mem_map, LimitsF, mem_decode]
  have hb (v : BitVec m) :
      meets v (ofList (botVars ψ)) = true ↔ LimitsBot ψ (decode v) := by
    simp [LimitsBot]
  simp only [shapeReader, shapeLabelOf, decodePair, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, hl, hu, hb]
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

/-- The variance graphs of the packed least shapes of the four-spine extension of a side
and a word. -/
def packedRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : GraphFamily n k :=
  let q := Events.sideQuery x y θ
  let graphs := packedShapes (Spine.extension c ϕ q.1 q.2 w)
  table fun z => varianceGraph c graphs (Fin.castAdd _ z)

theorem unfold_packedRegular (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) :
    (packedRegular c ϕ x y θ w z).unfold = (extractRegular c ϕ x y θ w z).unfold := by
  simp only [packedRegular, table_eq, extractRegular, RegularTransfer.countermodel]
  exact (unfold_varianceGraph c
    (fun v => (unfold_packedShapes _ v).trans (unfold_shapeGraph _ v)) _).trans
    (unfold_varianceGraph c (unfold_shapeGraph _) _).symm

/-- Extract only the reachable part of each regular countermodel graph. -/
def extractReachable (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) : GraphFamily n k :=
  let gs := packedRegular c ϕ x y θ w
  table fun z => Graph.compact (gs z)

theorem extractReachable_unfold (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)
    (θ : Side) (w : List (Fin n)) (z : V k) :
    (extractReachable c ϕ x y θ w z).unfold = (extractRegular c ϕ x y θ w z).unfold := by
  simp only [extractReachable, table_eq, Graph.unfold_compact, unfold_packedRegular]

end DeciNSSE.Solver
