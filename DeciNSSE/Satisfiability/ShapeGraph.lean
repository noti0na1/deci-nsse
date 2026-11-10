import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import DeciNSSE.Satisfiability.BoundSets
import DeciNSSE.Satisfiability.VarianceShape

/-! # A finite graph for the least shape

The least-shape label of a variable at a path depends only on its sets of lower
and upper bounds at that path, and both sets are updated letter by letter.
Pairs of such sets are the states of a finite graph whose unfolding is the
least shape. Pairing the graphs of the two signs of a variable with a polarity
bit gives a finite graph whose unfolding is the variance shape.

## Main declarations

- `RGraph.ofEquiv`, `RGraph.unfold_ofEquiv_fn`: graphs presented on a numbered state
  type, and their unfolding along a run.
- `shapeGraph`, `unfold_shapeGraph`: the least shape of every system is regular.
- `varianceGraph`, `unfold_varianceGraph`: the variance shape is regular.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace RGraph

/-- Present a transition system using an explicit numbering of its states. -/
def ofEquiv {S : Type} {m : ℕ} (e : S ≃ Fin m) (root : S) (label : S → Sym)
    (child : S → Fin n → S) : RGraph n where
  size := m
  root := e root
  label p := label (e.symm p)
  child p i := e (child (e.symm p) i)

/-- A run that starts at the root and leaves exactly the constructor states gives the
labels of the unfolding. -/
theorem unfold_ofEquiv_fn {S : Type} {m : ℕ} (e : S ≃ Fin m) {root : S}
    {label : S → Sym} {child : S → Fin n → S} (run : List (Fin n) → Option S)
    (hnil : run [] = some root)
    (hsnoc : ∀ π i, run (π ++ [i]) =
      (run π).bind fun s => if label s = .f then some (child s i) else none)
    (π : List (Fin n)) : (ofEquiv e root label child).unfold.fn π = (run π).map label := by
  have hwalk : ∀ π, (ofEquiv e root label child).walk π = (run π).map e := by
    intro π
    induction π using List.reverseRecOn with
    | nil => simp [hnil, walk, walkFrom, ofEquiv]
    | append_singleton π i ih =>
      rw [walk_append_singleton, ih, hsnoc]
      cases run π with
      | none => rfl
      | some s => by_cases hs : label s = .f <;> simp [hs, ofEquiv]
  rw [unfold_fn, hwalk]
  cases run π <;> simp [ofEquiv]

end RGraph

section ShapeGraph

variable {ϕ : Constraint n k}

/-- A set of lower bounds supports a constructor label. -/
def SupportsF (ϕ : Constraint n k) (S : Finset (V k)) : Prop :=
  ∃ y ∈ S, ∃ l ∈ lowerLits ϕ, l.2 = y

/-- A set of upper bounds supports a constructor label. -/
def LimitsF (ϕ : Constraint n k) (S : Finset (V k)) : Prop :=
  ∃ y ∈ S, ∃ m ∈ upperLits ϕ, m.1 = y

/-- A set of upper bounds supports a bottom label. -/
def LimitsBot (ϕ : Constraint n k) (S : Finset (V k)) : Prop :=
  ∃ y ∈ S, y ∈ botVars ϕ

instance (ϕ : Constraint n k) (S : Finset (V k)) : Decidable (SupportsF ϕ S) := by
  unfold SupportsF; infer_instance

instance (ϕ : Constraint n k) (S : Finset (V k)) : Decidable (LimitsF ϕ S) := by
  unfold LimitsF; infer_instance

instance (ϕ : Constraint n k) (S : Finset (V k)) : Decidable (LimitsBot ϕ S) := by
  unfold LimitsBot; infer_instance

theorem supportsF_lowerSet (z : V k) (π : List (Fin n)) :
    SupportsF ϕ (lowerSet ϕ z π) ↔ LowerLabel ϕ π .f z := by
  simp only [SupportsF, mem_lowerSet, LowerLabel]
  constructor
  · rintro ⟨y, hp, ⟨a, u⟩, hl, rfl⟩
    exact ⟨a, u, (mem_lowerLits ϕ a u).mp hl, hp⟩
  · rintro ⟨a, y, hl, hp⟩
    exact ⟨y, hp, (a, y), (mem_lowerLits ϕ a y).mpr hl, rfl⟩

theorem limitsF_upperSet (z : V k) (π : List (Fin n)) :
    LimitsF ϕ (upperSet ϕ z π) ↔ UpperLabel ϕ π .f z := by
  simp only [LimitsF, mem_upperSet, UpperLabel]
  constructor
  · rintro ⟨y, hp, ⟨u, b⟩, hl, rfl⟩
    exact ⟨u, b, (mem_upperLits ϕ u b).mp hl, hp⟩
  · rintro ⟨y, b, hl, hp⟩
    exact ⟨y, hp, (y, b), (mem_upperLits ϕ y b).mpr hl, rfl⟩

theorem limitsBot_upperSet (z : V k) (π : List (Fin n)) :
    LimitsBot ϕ (upperSet ϕ z π) ↔ UpperLabel ϕ π .bot z := by
  simp only [LimitsBot, mem_upperSet, mem_botVars, UpperLabel]
  constructor
  · rintro ⟨y, hp, ht⟩; exact ⟨y, ht, hp⟩
  · rintro ⟨y, ht, hp⟩; exact ⟨y, hp, ht⟩

/-- The lower and the upper bounds of `z` at `π`. -/
def boundSets (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    Finset (V k) × Finset (V k) :=
  (lowerSet ϕ z π, upperSet ϕ z π)

/-- One letter of the bound-set automaton. -/
def boundStep (ϕ : Constraint n k) (s : Finset (V k) × Finset (V k)) (i : Fin n) :
    Finset (V k) × Finset (V k) :=
  (lowerStep ϕ (derivedPairs ϕ) i s.1, upperStep ϕ (derivedPairs ϕ) i s.2)

theorem boundSets_append (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) (i : Fin n) :
    boundSets ϕ z (π ++ [i]) = boundStep ϕ (boundSets ϕ z π) i := by
  simp only [boundSets, boundStep, lowerSet_append, upperSet_append]

/-- The least-shape label read from a pair of lower and upper bound sets. -/
def shapeLabelOf (ϕ : Constraint n k) (s : Finset (V k) × Finset (V k)) : Sym :=
  if SupportsF ϕ s.1 ∧ LimitsF ϕ s.2 then .f
  else if ¬ SupportsF ϕ s.1 ∧ (LimitsBot ϕ s.2 ∨ LimitsF ϕ s.2) then .bot
  else .top

theorem shapeLabelOf_boundSets (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    shapeLabelOf ϕ (boundSets ϕ z π) = shapeLabel ϕ z π := by
  classical
  unfold shapeLabelOf shapeLabel boundSets
  simp only [supportsF_lowerSet, limitsF_upperSet, limitsBot_upperSet]

/-- Number a bound set by its binary membership vector. -/
private def boundSetEquiv (k : ℕ) : Finset (V k) ≃ Fin (2 ^ k) :=
  let e : Finset (V k) ≃ (Fin k → Fin 2) :=
    { toFun := fun s i => finTwoEquiv.symm (decide (i ∈ s))
      invFun := fun f => Finset.univ.filter fun i => finTwoEquiv (f i) = true
      left_inv := by intro s; ext i; simp
      right_inv := by intro f; funext i; simp }
  e.trans finFunctionFinEquiv

/-- States are pairs of bound sets, numbered by their binary membership vectors. -/
def shapeGraph (ϕ : Constraint n k) (z : V k) : RGraph n :=
  RGraph.ofEquiv ((Equiv.prodCongr (boundSetEquiv k) (boundSetEquiv k)).trans
    finProdFinEquiv) (boundSets ϕ z []) (shapeLabelOf ϕ) (boundStep ϕ)

/-- The least shape of every system is regular: the shape graph unfolds to it. -/
theorem unfold_shapeGraph (ϕ : Constraint n k) (z : V k) :
    (shapeGraph ϕ z).unfold = leastShape ϕ z := by
  classical
  apply Tree.ext
  funext π
  rw [shapeGraph, RGraph.unfold_ofEquiv_fn _
    (fun π => if Active (shapeLabel ϕ z) π then some (boundSets ϕ z π) else none)
    (by simp) ?_ π, leastShape_fn]
  · split_ifs <;> simp [shapeLabelOf_boundSets]
  · intro π i
    simp only [active_append_singleton]
    by_cases ha : Active (shapeLabel ϕ z) π
    · by_cases hf : shapeLabel ϕ z π = .f
      · simp [ha, hf, shapeLabelOf_boundSets, boundSets_append]
      · simp [ha, hf, shapeLabelOf_boundSets]
    · simp [ha]

end ShapeGraph

open SignDuality

/-- The variance graph of a family of graphs on signed variables: a state pairs a state
of the graph of `u⁺` and a state of the graph of `u⁻` with the polarity bit, which
selects the graph whose label is read. -/
def varianceGraph (c : Fin n → Bool) (g : V (2 * k) → RGraph n) (u : V k) : RGraph n :=
  RGraph.ofEquiv ((Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _)
    finTwoEquiv.symm).trans finProdFinEquiv)).trans finProdFinEquiv)
    ((g (sv u false)).root, (g (sv u true)).root, false)
    (fun s => if s.2.2 then (g (sv u true)).label s.2.1 else (g (sv u false)).label s.1)
    (fun s i => ((g (sv u false)).child s.1 i, (g (sv u true)).child s.2.1 i,
      Bool.xor s.2.2 (c i)))

/-- If the graph of each signed variable unfolds to its least shape in the signed
translation, the variance graph unfolds to the variance shape. -/
theorem unfold_varianceGraph (c : Fin n → Bool) {ϕ : Constraint n k} {g : V (2 * k) → RGraph n}
    (hg : ∀ z, (g z).unfold = leastShape (signed c ϕ) z) (u : V k) :
    (varianceGraph c g u).unfold = varianceShape c ϕ u := by
  have hf (π : List (Fin n)) : (g (sv u false)).unfold.fn π = some .f ↔
      (g (sv u true)).unfold.fn π = some .f := by
    simpa [hg] using leastShape_flip_f (signed_flipClosed c ϕ) (sv u false) π
  have hd (π : List (Fin n)) :
      ((g (sv u false)).walk π).isSome = ((g (sv u true)).walk π).isSome := by
    have h : ((g (sv u false)).unfold.fn π).isSome = ((g (sv u true)).unfold.fn π).isSome := by
      apply Bool.eq_iff_iff.mpr
      induction π using List.reverseRecOn with
      | nil => exact iff_of_true (Tree.root_isSome _) (Tree.root_isSome _)
      | append_singleton π i => simp only [Tree.child_isSome_iff, hf π]
    simpa using h
  apply Tree.ext
  funext π
  rw [varianceGraph, RGraph.unfold_ofEquiv_fn _ (fun π => ((g (sv u false)).walk π).bind
      fun q₁ => ((g (sv u true)).walk π).map fun q₂ => (q₁, q₂, polarity c π))
    (by simp [RGraph.walk, RGraph.walkFrom]) ?_ π]
  · have hπ := hd π
    rw [varianceShape_fn, ← hg]
    cases polarity c π <;> rw [RGraph.unfold_fn] <;>
      cases h₁ : (g (sv u false)).walk π <;> cases h₂ : (g (sv u true)).walk π <;>
      simp [h₁, h₂] at hπ ⊢
  · intro π i
    have hπ := hd π
    have hq := hf π
    simp only [RGraph.unfold_fn] at hq
    simp only [RGraph.walk_append_singleton, polarity_append_singleton]
    cases h₁ : (g (sv u false)).walk π <;> cases h₂ : (g (sv u true)).walk π <;>
      simp only [h₁, h₂] at hπ hq ⊢
    · rfl
    · simp at hπ
    · simp at hπ
    · rename_i q₁ q₂
      simp only [Option.map_some, Option.some.injEq] at hq
      by_cases hq₁ : (g (sv u false)).label q₁ = .f
      · simp [hq₁, hq.mp hq₁]
      · cases polarity c π <;> simp [hq₁, mt hq.mpr hq₁]

end DeciNSSE
