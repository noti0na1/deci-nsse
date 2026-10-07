import DeciNSSE.Constraints.Dual
import DeciNSSE.Semantics.Selector

/-! # A finite graph for the least shape

The least-shape label of a variable at a path depends only on its sets of lower
and upper bounds at that path, and both sets are updated letter by letter.
Pairs of such sets are the states of a finite graph whose unfolding is the
least shape. A polarity bit realises selection and normalisation on graphs.
Hence the selected least shape of a flip-closed, sign-coherent system without
label clash is a regular solution fixed by sign duality, and decoding a regular
solution fixed by sign duality gives a regular variance solution.
-/

namespace DeciNSSE

variable {n k : ℕ}

namespace RGraph

/-- The graph of a transition system on an encodable finite type of states. -/
def ofStates {S : Type} [Fintype S] [Encodable S] (root : S) (label : S → Sym)
    (child : S → Fin n → S) : RGraph n where
  size := Fintype.card S
  root := Encodable.fintypeEquivFin root
  label p := label (Encodable.fintypeEquivFin.symm p)
  child p i := Encodable.fintypeEquivFin (child (Encodable.fintypeEquivFin.symm p) i)

/-- A run that starts at the root and leaves exactly the constructor states gives the
labels of the unfolding. -/
theorem unfold_ofStates_fn {S : Type} [Fintype S] [Encodable S] {root : S}
    {label : S → Sym} {child : S → Fin n → S} (run : List (Fin n) → Option S)
    (hnil : run [] = some root)
    (hsnoc : ∀ π i, run (π ++ [i]) =
      (run π).bind fun s => if label s = .f then some (child s i) else none)
    (π : List (Fin n)) : (ofStates root label child).unfold.fn π = (run π).map label := by
  have hwalk : ∀ π, (ofStates root label child).walk π =
      (run π).map Encodable.fintypeEquivFin := by
    intro π
    induction π using List.reverseRecOn with
    | nil => simp [hnil, walk, walkFrom, ofStates]
    | append_singleton π i ih =>
      rw [walk_append_singleton, ih, hsnoc]
      cases run π with
      | none => rfl
      | some s => by_cases hs : label s = .f <;> simp [hs, ofStates]
  rw [unfold_fn, hwalk]
  cases run π <;> simp [ofStates]

/-- The polarity product of two graphs: a state pairs a state of each graph with the
polarity bit, and the second graph is read, with leaves exchanged, where the bit is set. -/
def mix (c : Fin n → Bool) (p : Bool) (g₁ g₂ : RGraph n) : RGraph n :=
  ofStates (g₁.root, g₂.root, p)
    (fun s => if s.2.2 then Sym.flip true (g₂.label s.2.1) else g₁.label s.1)
    (fun s i => (g₁.child s.1 i, g₂.child s.2.1 i, Bool.xor s.2.2 (c i)))

theorem mix_unfold_fn (c : Fin n → Bool) (p : Bool) {g₁ g₂ : RGraph n}
    (h : FiniteVariance.SameShape g₁.unfold g₂.unfold) (π : List (Fin n)) :
    (mix c p g₁ g₂).unfold.fn π =
      if Bool.xor p (polarity c π) then (g₂.unfold.fn π).map (Sym.flip true)
      else g₁.unfold.fn π := by
  have hd (π) : (g₁.walk π).isSome = (g₂.walk π).isSome := by simpa using h.domain π
  have hf (π) {q₁ q₂} (h₁ : g₁.walk π = some q₁) (h₂ : g₂.walk π = some q₂) :
      g₁.label q₁ = .f ↔ g₂.label q₂ = .f := by simpa [h₁, h₂] using h π
  rw [mix, unfold_ofStates_fn (fun π => (g₁.walk π).bind fun q₁ =>
      (g₂.walk π).map fun q₂ => (q₁, q₂, Bool.xor p (polarity c π)))
    (by simp [walk, walkFrom]) ?_ π]
  · rw [unfold_fn, unfold_fn]
    have hπ := hd π
    revert hπ
    cases g₁.walk π <;> cases g₂.walk π <;> cases Bool.xor p (polarity c π) <;> simp
  · intro π i
    have hπ := hd π
    simp only [walk_append_singleton, polarity_append_singleton]
    cases h₁ : g₁.walk π <;> cases h₂ : g₂.walk π <;> simp only [h₁, h₂] at hπ ⊢
    · rfl
    · simp at hπ
    · simp at hπ
    · rename_i q₁ q₂
      have hq := hf π h₁ h₂
      by_cases hq₁ : g₁.label q₁ = .f
      · simp [hq₁, hq.mp hq₁]
      · cases Bool.xor p (polarity c π) <;> simp [hq₁, mt hq.mpr hq₁]

/-- The polarity product presents the polarity mix of the first tree with the dual of the
second. -/
theorem unfold_mix (c : Fin n → Bool) (p : Bool) {g₁ g₂ : RGraph n} {a b : Tree n}
    (h : FiniteVariance.SameShape a b) (ha : g₁.unfold = a) (hb : Tree.dual g₂.unfold = b) :
    (mix c p g₁ g₂).unfold = FiniteVariance.mix c p a b h := by
  subst ha hb
  apply Tree.ext
  funext π
  rw [mix_unfold_fn c p (fun π => (h π).trans (normalize_constructor _ _ _ π)),
    FiniteVariance.mix_fn, dual_fn]

/-- Normalisation reads a graph and its dual according to the polarity bit. -/
def normalize (c : Fin n → Bool) (p : Bool) (g : RGraph n) : RGraph n := mix c p g g

theorem unfold_normalize (c : Fin n → Bool) (p : Bool) (g : RGraph n) :
    (normalize c p g).unfold = Tree.normalize c p g.unfold := by
  apply Tree.ext
  funext π
  rw [normalize, mix_unfold_fn c p (fun _ => Iff.rfl), normalize_fn]
  cases Bool.xor p (polarity c π) <;> cases g.unfold.fn π <;> simp

end RGraph

section ShapeGraph

variable {ϕ : Constraint n k}

/-- The lower bounds of `z` at a path, computed by reading the path from the root. -/
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

/-- A lower path ending in a letter factors through the lower bounds before it. -/
theorem lowerAt_append_singleton_iff (π : List (Fin n)) (i : Fin n) (x y : V k) :
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

/-- One letter of lower bounds: the variables below the chosen child of a lower
constructor bound of the set. -/
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

/-- A set of lower bounds supports a constructor label. -/
def SupportsF (ϕ : Constraint n k) (S : Finset (V k)) : Prop :=
  ∃ y ∈ S, ∃ l ∈ lowerLits ϕ, l.2 = y

/-- A set of lower bounds supports a top label. -/
def SupportsTop (ϕ : Constraint n k) (S : Finset (V k)) : Prop :=
  ∃ y ∈ S, y ∈ topVars ϕ

instance (ϕ : Constraint n k) (S : Finset (V k)) : Decidable (SupportsF ϕ S) := by
  unfold SupportsF; infer_instance

instance (ϕ : Constraint n k) (S : Finset (V k)) : Decidable (SupportsTop ϕ S) := by
  unfold SupportsTop; infer_instance

theorem supportsF_lowerSet (z : V k) (π : List (Fin n)) :
    SupportsF ϕ (lowerSet ϕ z π) ↔ LowerLabel ϕ π .f z := by
  simp only [SupportsF, mem_lowerSet, LowerLabel]
  constructor
  · rintro ⟨y, hp, ⟨a, u⟩, hl, rfl⟩
    exact ⟨a, u, (mem_lowerLits ϕ a u).mp hl, hp⟩
  · rintro ⟨a, y, hl, hp⟩
    exact ⟨y, hp, (a, y), (mem_lowerLits ϕ a y).mpr hl, rfl⟩

theorem supportsTop_lowerSet (z : V k) (π : List (Fin n)) :
    SupportsTop ϕ (lowerSet ϕ z π) ↔ LowerLabel ϕ π .top z := by
  simp only [SupportsTop, mem_lowerSet, mem_topVars, LowerLabel]
  constructor
  · rintro ⟨y, hp, ht⟩; exact ⟨y, ht, hp⟩
  · rintro ⟨y, ht, hp⟩; exact ⟨y, hp, ht⟩

/-- Upper constructor bounds are lower constructor bounds in the dual system. -/
theorem upperLabel_f_iff_dual {π : List (Fin n)} {z : V k} :
    UpperLabel ϕ π .f z ↔ LowerLabel (Constraint.dual ϕ) π .f z := by
  simp only [UpperLabel, LowerLabel, ConstraintDual.lower_iff]
  constructor
  · rintro ⟨y, b, hl, hp⟩
    exact ⟨b, y, (ConstraintDual.lit_mem (Lit.leF y b)).mpr hl, hp⟩
  · rintro ⟨a, y, hl, hp⟩
    exact ⟨y, a, (ConstraintDual.lit_mem (Lit.leF y a)).mp hl, hp⟩

/-- Upper bottom bounds are lower top bounds in the dual system. -/
theorem upperLabel_bot_iff_dual {π : List (Fin n)} {z : V k} :
    UpperLabel ϕ π .bot z ↔ LowerLabel (Constraint.dual ϕ) π .top z := by
  simp only [UpperLabel, LowerLabel, ConstraintDual.lower_iff]
  constructor
  · rintro ⟨y, hl, hp⟩
    exact ⟨y, (ConstraintDual.lit_mem (Lit.eqBot y)).mpr hl, hp⟩
  · rintro ⟨y, hl, hp⟩
    exact ⟨y, (ConstraintDual.lit_mem (Lit.eqBot y)).mp hl, hp⟩

/-- The lower and the upper bounds of `z` at `π`; upper bounds are computed as lower
bounds in the dual system. -/
def boundSets (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    Finset (V k) × Finset (V k) :=
  (lowerSet ϕ z π, lowerSet (Constraint.dual ϕ) z π)

theorem boundSets_append (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) (i : Fin n) :
    boundSets ϕ z (π ++ [i]) =
      (step ϕ (boundSets ϕ z π).1 i, step (Constraint.dual ϕ) (boundSets ϕ z π).2 i) := by
  simp only [boundSets, lowerSet_append]

/-- The least-shape label read from a pair of lower and upper bound sets. -/
def shapeLabelOf (ϕ : Constraint n k) (s : Finset (V k) × Finset (V k)) : Sym :=
  if SupportsF ϕ s.1 ∧ SupportsF (Constraint.dual ϕ) s.2 then .f
  else if ¬ SupportsF ϕ s.1 ∧
    (SupportsTop (Constraint.dual ϕ) s.2 ∨ SupportsF (Constraint.dual ϕ) s.2) then .bot
  else .top

theorem shapeLabelOf_boundSets (ϕ : Constraint n k) (z : V k) (π : List (Fin n)) :
    shapeLabelOf ϕ (boundSets ϕ z π) = shapeLabel ϕ z π := by
  classical
  unfold shapeLabelOf shapeLabel boundSets
  simp only [supportsF_lowerSet, supportsTop_lowerSet, upperLabel_f_iff_dual,
    upperLabel_bot_iff_dual]

/-- States are pairs of bound sets; each letter updates both sets. -/
def shapeGraph (ϕ : Constraint n k) (z : V k) : RGraph n :=
  RGraph.ofStates (boundSets ϕ z []) (shapeLabelOf ϕ)
    (fun s i => (step ϕ s.1 i, step (Constraint.dual ϕ) s.2 i))

/-- The least shape of every system is regular: the shape graph unfolds to it. -/
theorem unfold_shapeGraph (ϕ : Constraint n k) (z : V k) :
    (shapeGraph ϕ z).unfold = leastShape ϕ z := by
  classical
  apply Tree.ext
  funext π
  rw [shapeGraph, RGraph.unfold_ofStates_fn
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

open FiniteVariance

/-- Selection on graph families: the polarity product of the graphs at `z` and at its
sign flip. -/
def selectGraph (c : Fin n → Bool) (g : V (2 * k) → RGraph n) (z : V (2 * k)) : RGraph n :=
  RGraph.mix c (sign z) (g z) (g (flipV z))

/-- Selection preserves regularity. -/
theorem unfold_selectGraph (c : Fin n → Bool) {g : V (2 * k) → RGraph n}
    {B : V (2 * k) → Tree n} (hg : RGraph.unfold ∘ g = B)
    (h : ∀ z, SameShape (B z) (Signed.dual B z)) :
    RGraph.unfold ∘ selectGraph c g = select c B h := by
  subst hg
  funext z
  exact RGraph.unfold_mix c (sign z) (h z) rfl rfl

/-- The selected least shape of a flip-closed system is regular. -/
theorem unfold_selectGraph_shapeGraph (c : Fin n → Bool) {ψ : Constraint n (2 * k)}
    (hc : FlipClosed ψ) :
    RGraph.unfold ∘ selectGraph c (shapeGraph ψ) =
      select c (leastShape ψ) (leastShape_sameShape_dual hc) :=
  unfold_selectGraph c (funext (unfold_shapeGraph ψ)) _

/-- Decoding on graph families: normalise the graph of the positive coordinate. -/
def decodedGraph (c : Fin n → Bool) (g : V (2 * k) → RGraph n) (u : V k) : RGraph n :=
  RGraph.normalize c false (g (sv u false))

/-- Decoding preserves regularity. -/
theorem unfold_decodedGraph (c : Fin n → Bool) {g : V (2 * k) → RGraph n}
    {A : V (2 * k) → Tree n} (hg : RGraph.unfold ∘ g = A) :
    RGraph.unfold ∘ decodedGraph c g = decoded c A := by
  subst hg
  funext u
  exact RGraph.unfold_normalize c false (g (sv u false))

/-- A flip-closed, sign-coherent system without label clash has a regular solution fixed by
sign duality: the selected least shape, presented by `selectGraph c (shapeGraph ψ)`. -/
theorem regular_fixed_solution (c : Fin n → Bool) {ψ : Constraint n (2 * k)}
    (hc : FlipClosed ψ) (hs : SignCoherent c ψ) (hn : ¬ LabelClash ψ) :
    Covariant.Sat (RGraph.unfold ∘ selectGraph c (shapeGraph ψ)) ψ ∧
      Signed.dual (RGraph.unfold ∘ selectGraph c (shapeGraph ψ)) =
        RGraph.unfold ∘ selectGraph c (shapeGraph ψ) := by
  rw [unfold_selectGraph_shapeGraph c hc]
  exact ⟨select_sat_of_coherent hs (leastShape_sat hn)
      (sat_signedDual_of_flipClosed hc (leastShape_sat hn)) (leastShape_sameShape_dual hc),
    select_fixed c (leastShape ψ) (leastShape_sameShape_dual hc)⟩

/-- A signed solution fixed by sign duality and presented by graphs decodes to a regular
variance solution. -/
theorem sat_decodedGraph (c : Fin n → Bool) {ϕ : Constraint n k} {g : V (2 * k) → RGraph n}
    (hs : Covariant.Sat (RGraph.unfold ∘ g) (signed c ϕ))
    (hfix : Signed.dual (RGraph.unfold ∘ g) = RGraph.unfold ∘ g) :
    Sat c (RGraph.unfold ∘ decodedGraph c g) ϕ := by
  rw [sat_iff_signed, unfold_decodedGraph c rfl, normalized_decoded c hfix]
  exact hs

end DeciNSSE
