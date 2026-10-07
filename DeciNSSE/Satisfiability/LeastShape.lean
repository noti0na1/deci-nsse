import DeciNSSE.Satisfiability.Least

/-! # The least-shape solution

A constructor is retained only where both lower and upper constructor support
require it. Pruning the resulting labels gives a solution with bounded depth
whenever there is no cycle clash.
-/

namespace DeciNSSE

variable {n k : ℕ} {ϕ : Constraint n k}

/-- Syntactically supported upper bounds on the label of `x` at the path `π`. -/
def UpperLabel (ϕ : Constraint n k) (π : List (Fin n)) : Sym → V k → Prop
  | .bot, x => ∃ y, Lit.eqBot y ∈ ϕ ∧ UpperAt ϕ π x y
  | .f, x => ∃ y b, Lit.leF y b ∈ ϕ ∧ UpperAt ϕ π x y
  | .top, _ => True

/-- Cancel a lower path from an upper-supported label. -/
theorem UpperLabel.decompose {π π' : List (Fin n)} {g : Sym} {x y : V k}
    (h : UpperLabel ϕ (π ++ π') g x) (hl : LowerAt ϕ π y x) :
    UpperLabel ϕ π' g y := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hl.decompose_upper hp⟩
  | f =>
    obtain ⟨z, b, hz, hp⟩ := h
    exact ⟨z, b, hz, hl.decompose_upper hp⟩

theorem UpperLabel.cons_leF {π : List (Fin n)} {g : Sym} {x : V k} {b : Fin n → V k}
    (hl : Lit.leF x b ∈ ϕ) (i : Fin n) (h : UpperLabel ϕ π g (b i)) :
    UpperLabel ϕ (i :: π) g x := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons (.refl x) hl hp⟩
  | f =>
    obtain ⟨y, c, hy, hp⟩ := h
    exact ⟨y, c, hy, .cons (.refl x) hl hp⟩

@[simp] theorem upperLabel_nil_bot {x : V k} :
    UpperLabel ϕ [] .bot x ↔ UpperBot ϕ x := by
  simp [UpperLabel, UpperBot]

@[simp] theorem upperLabel_nil_f {x : V k} :
    UpperLabel ϕ [] .f x ↔ UpperF ϕ x := by
  simp [UpperLabel, UpperF]

/-- The three clauses of the paper's least-shape label assignment. -/
noncomputable def shapeLabel (ϕ : Constraint n k) (x : V k) (π : List (Fin n)) : Sym := by
  classical
  exact if LowerLabel ϕ π .f x ∧ UpperLabel ϕ π .f x then .f
    else if ¬ LowerLabel ϕ π .f x ∧
      (UpperLabel ϕ π .bot x ∨ UpperLabel ϕ π .f x) then .bot else .top

theorem shapeLabel_eq_f_iff {π : List (Fin n)} {x : V k} :
    shapeLabel ϕ x π = .f ↔ LowerLabel ϕ π .f x ∧ UpperLabel ϕ π .f x := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem shapeLabel_eq_bot_iff {π : List (Fin n)} {x : V k} :
    shapeLabel ϕ x π = .bot ↔ ¬ LowerLabel ϕ π .f x ∧
      (UpperLabel ϕ π .bot x ∨ UpperLabel ϕ π .f x) := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem f_le_shapeLabel {π : List (Fin n)} {x : V k}
    (h : LowerLabel ϕ π .f x) : Sym.f ≤ shapeLabel ϕ x π := by
  cases he : shapeLabel ϕ x π with
  | bot => exact False.elim ((shapeLabel_eq_bot_iff.mp he).1 h)
  | f => exact le_rfl
  | top => exact Sym.le_top _

theorem shapeLabel_le_f {π : List (Fin n)} {x : V k}
    (h : UpperLabel ϕ π .f x) : shapeLabel ϕ x π ≤ Sym.f := by
  classical
  by_cases hl : LowerLabel ϕ π .f x
  · rw [shapeLabel_eq_f_iff.mpr ⟨hl, h⟩]
  · rw [shapeLabel_eq_bot_iff.mpr ⟨hl, Or.inr h⟩]
    exact Sym.bot_le _

/-- Lower bounds transport forward and upper bounds backward along a comparison. -/
theorem shapeLabel_mono {π τ : List (Fin n)} {x y : V k}
    (hl : LowerLabel ϕ π .f x → LowerLabel ϕ τ .f y)
    (hu : ∀ g, UpperLabel ϕ τ g y → UpperLabel ϕ π g x) :
    shapeLabel ϕ x π ≤ shapeLabel ϕ y τ := by
  cases he : shapeLabel ϕ y τ with
  | top => exact Sym.le_top _
  | f => exact shapeLabel_le_f (hu .f (shapeLabel_eq_f_iff.mp he).2)
  | bot =>
    obtain ⟨hn, hb | hf⟩ := shapeLabel_eq_bot_iff.mp he
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inl (hu .bot hb)⟩]
    · rw [shapeLabel_eq_bot_iff.mpr ⟨fun hx => hn (hl hx), Or.inr (hu .f hf)⟩]

/-- Gate the labels by the same proper-prefix predicate used for `least`. -/
noncomputable def leastShape (ϕ : Constraint n k) (x : V k) : Tree n := by
  classical
  exact {
    fn := fun π => if Active (shapeLabel ϕ x) π then some (shapeLabel ϕ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [active_append_singleton]
        by_cases ha : Active (shapeLabel ϕ x) π <;> simp [ha]
  }

open Classical in
theorem leastShape_fn (ϕ : Constraint n k) (x : V k) (π : List (Fin n)) :
    (leastShape ϕ x).fn π =
      if Active (shapeLabel ϕ x) π then some (shapeLabel ϕ x π) else none := by
  classical
  rfl

@[simp] theorem leastShape_fn_nil (ϕ : Constraint n k) (x : V k) :
    (leastShape ϕ x).fn [] = some (shapeLabel ϕ x []) := by
  simp [leastShape_fn]

theorem leastShape_label_eq {π : List (Fin n)} {x : V k} {a : Sym}
    (h : (leastShape ϕ x).fn π = some a) : a = shapeLabel ϕ x π := by
  classical
  rw [leastShape_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

/-- A prescribed bottom is realised by the least-shape solution when there is no label clash. -/
theorem leastShape_eq_bot (hn : ¬ LabelClash ϕ) {x : V k}
    (hl : Lit.eqBot x ∈ ϕ) : leastShape ϕ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [leastShape_fn_nil]
  congr 1
  apply shapeLabel_eq_bot_iff.mpr
  have hu : UpperBot ϕ x := ⟨x, hl, .refl x⟩
  exact ⟨fun hf => hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hf, hu⟩)⟩,
    Or.inl (upperLabel_nil_bot.mpr hu)⟩

/-- A prescribed top is realised by the least-shape solution when there is no label clash. -/
theorem leastShape_eq_top (hn : ¬ LabelClash ϕ) {x : V k}
    (hl : Lit.eqTop x ∈ ϕ) : leastShape ϕ x = Tree.top := by
  classical
  have htop : LowerTop ϕ x := ⟨x, hl, .refl x⟩
  have hub : ¬ UpperLabel ϕ [] .bot x :=
    fun h => hn ⟨x, Or.inl ⟨htop, upperLabel_nil_bot.mp h⟩⟩
  have huf : ¬ UpperLabel ϕ [] .f x :=
    fun h => hn ⟨x, Or.inr (Or.inl ⟨htop, upperLabel_nil_f.mp h⟩)⟩
  apply (Tree.root_eq_top_iff _).mp
  simp [leastShape_fn_nil, shapeLabel, hub, huf]

/-- The least-shape assignment satisfies each lower constructor literal. -/
theorem node_le_leastShape {a : Fin n → V k} {x : V k} (hl : Lit.fLe a x ∈ ϕ) :
    Tree.node (leastShape ϕ ∘ a) ≤ leastShape ϕ x := by
  intro π c Tree.dual hc hd
  rw [leastShape_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact f_le_shapeLabel ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (leastShape ϕ (a i)).fn π = some c := hc
    rw [leastShape_label_eq hc']
    have hp : LowerAt ϕ [i] (a i) x := .cons hl (.refl x) (.nil (.refl _))
    exact shapeLabel_mono (fun h => h.cons_fLe hl i)
      (fun _ h => UpperLabel.decompose (π := [i]) h hp)

/-- The least-shape assignment satisfies each upper constructor literal. -/
theorem leastShape_le_node {x : V k} {b : Fin n → V k} (hl : Lit.leF x b ∈ ϕ) :
    leastShape ϕ x ≤ Tree.node (leastShape ϕ ∘ b) := by
  intro π c Tree.dual hc hd
  rw [leastShape_label_eq hc]
  cases π with
  | nil =>
    have he : Tree.dual = .f := (Option.some.inj hd).symm
    subst Tree.dual
    exact shapeLabel_le_f ⟨x, b, hl, .nil (.refl x)⟩
  | cons i π =>
    have hd' : (leastShape ϕ (b i)).fn π = some Tree.dual := hd
    rw [leastShape_label_eq hd']
    have hp : UpperAt ϕ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact shapeLabel_mono (fun h => LowerLabel.decompose (π := [i]) h hp)
      (fun _ h => h.cons_leF hl i)

/-- The least-shape assignment satisfies every label-clash-free system. -/
theorem leastShape_sat (hn : ¬ LabelClash ϕ) : Covariant.Sat (leastShape ϕ) ϕ := by
  intro l hl
  cases l with
  | leF x b => exact leastShape_le_node hl
  | fLe a x => exact node_le_leastShape hl
  | eqBot x => exact leastShape_eq_bot hn hl
  | eqTop x => exact leastShape_eq_top hn hl

end DeciNSSE
