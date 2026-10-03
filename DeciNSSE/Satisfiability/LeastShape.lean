import DeciNSSE.Satisfiability.Least

/-! # Solutions of least shape

Lower and upper label requirements determine a solution with minimal branching.
Bounds on its active paths are used to obtain finite-tree solutions.
-/

namespace DeciNSSE

variable {k : ℕ} {ϕ : Constraint k}

def UpperLabel (ϕ : Constraint k) (π : List (Fin 2)) : Sym → V k → Prop
  | .bot, x => ∃ y, Lit.eqBot y ∈ ϕ ∧ UpperAt ϕ π x y
  | .f, x => ∃ y y₁ y₂, Lit.leF y y₁ y₂ ∈ ϕ ∧ UpperAt ϕ π x y
  | .top, _ => True

theorem UpperLabel.decompose {π π' : List (Fin 2)} {g : Sym} {x y : V k}
    (h : UpperLabel ϕ (π ++ π') g x) (hl : LowerAt ϕ π y x) :
    UpperLabel ϕ π' g y := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hl.decompose_upper hp⟩
  | f =>
    obtain ⟨z, z₁, z₂, hz, hp⟩ := h
    exact ⟨z, z₁, z₂, hz, hl.decompose_upper hp⟩

theorem UpperLabel.cons_leF {π : List (Fin 2)} {g : Sym} {x x₁ x₂ : V k}
    (hl : Lit.leF x x₁ x₂ ∈ ϕ) (i : Fin 2)
    (h : UpperLabel ϕ π g (if i = 0 then x₁ else x₂)) :
    UpperLabel ϕ (i :: π) g x := by
  cases g with
  | top => trivial
  | bot =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons (.refl x) hl hp⟩
  | f =>
    obtain ⟨y, y₁, y₂, hy, hp⟩ := h
    exact ⟨y, y₁, y₂, hy, .cons (.refl x) hl hp⟩

@[simp] theorem upperLabel_nil_bot {x : V k} :
    UpperLabel ϕ [] .bot x ↔ UpperBot ϕ x := by
  simp [UpperLabel, UpperBot]

@[simp] theorem upperLabel_nil_f {x : V k} :
    UpperLabel ϕ [] .f x ↔ UpperF ϕ x := by
  simp [UpperLabel, UpperF]

noncomputable def shapeLabel (ϕ : Constraint k) (x : V k) (π : List (Fin 2)) : Sym := by
  classical
  exact if LowerLabel ϕ π .f x ∧ UpperLabel ϕ π .f x then .f
    else if ¬ LowerLabel ϕ π .f x ∧
      (UpperLabel ϕ π .bot x ∨ UpperLabel ϕ π .f x) then .bot else .top

theorem shapeLabel_eq_f_iff {π : List (Fin 2)} {x : V k} :
    shapeLabel ϕ x π = .f ↔ LowerLabel ϕ π .f x ∧ UpperLabel ϕ π .f x := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem shapeLabel_eq_bot_iff {π : List (Fin 2)} {x : V k} :
    shapeLabel ϕ x π = .bot ↔ ¬ LowerLabel ϕ π .f x ∧
      (UpperLabel ϕ π .bot x ∨ UpperLabel ϕ π .f x) := by
  classical
  unfold shapeLabel
  split_ifs <;> simp_all

theorem f_le_shapeLabel {π : List (Fin 2)} {x : V k}
    (h : LowerLabel ϕ π .f x) : Sym.f ≤ shapeLabel ϕ x π := by
  cases he : shapeLabel ϕ x π with
  | bot => exact False.elim ((shapeLabel_eq_bot_iff.mp he).1 h)
  | f => exact le_rfl
  | top => exact Sym.le_top _

theorem shapeLabel_le_f {π : List (Fin 2)} {x : V k}
    (h : UpperLabel ϕ π .f x) : shapeLabel ϕ x π ≤ Sym.f := by
  classical
  by_cases hl : LowerLabel ϕ π .f x
  · rw [shapeLabel_eq_f_iff.mpr ⟨hl, h⟩]
  · rw [shapeLabel_eq_bot_iff.mpr ⟨hl, Or.inr h⟩]
    exact Sym.bot_le _

theorem shapeLabel_mono {π τ : List (Fin 2)} {x y : V k}
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

noncomputable def leastShape (ϕ : Constraint k) (x : V k) : Tree := by
  classical
  exact {
    fn := fun π => if LeastConstruction.Active (shapeLabel ϕ x) π then
      some (shapeLabel ϕ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [LeastConstruction.active_append_singleton]
        by_cases ha : LeastConstruction.Active (shapeLabel ϕ x) π <;> simp [ha]
  }

open Classical in
theorem leastShape_fn (ϕ : Constraint k) (x : V k) (π : List (Fin 2)) :
    (leastShape ϕ x).fn π =
      if LeastConstruction.Active (shapeLabel ϕ x) π then some (shapeLabel ϕ x π)
      else none := rfl

@[simp] theorem leastShape_fn_nil (ϕ : Constraint k) (x : V k) :
    (leastShape ϕ x).fn [] = some (shapeLabel ϕ x []) := by
  simp [leastShape_fn]

theorem leastShape_label_eq {π : List (Fin 2)} {x : V k} {a : Sym}
    (h : (leastShape ϕ x).fn π = some a) : a = shapeLabel ϕ x π := by
  classical
  rw [leastShape_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem leastShape_eq_bot (hn : ¬ LabelClash ϕ) {x : V k}
    (hl : Lit.eqBot x ∈ ϕ) : leastShape ϕ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [leastShape_fn_nil]
  congr 1
  apply shapeLabel_eq_bot_iff.mpr
  have hu : UpperBot ϕ x := ⟨x, hl, .refl x⟩
  exact ⟨fun hf => hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hf, hu⟩)⟩,
    Or.inl (upperLabel_nil_bot.mpr hu)⟩

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

theorem node_le_leastShape {x x₁ x₂ : V k} (hl : Lit.fLe x₁ x₂ x ∈ ϕ) :
    Tree.node (leastShape ϕ x₁) (leastShape ϕ x₂) ≤ leastShape ϕ x := by
  intro π a b ha hb
  rw [leastShape_label_eq hb]
  cases π with
  | nil =>
    have he : a = .f := (Option.some.inj ha).symm
    subst a
    exact f_le_shapeLabel ⟨x, x₁, x₂, hl, .nil (.refl x)⟩
  | cons i π =>
    have ha' : (leastShape ϕ (if i = 0 then x₁ else x₂)).fn π = some a := by
      fin_cases i <;> simpa using ha
    rw [leastShape_label_eq ha']
    have hp : LowerAt ϕ [i] (if i = 0 then x₁ else x₂) x :=
      .cons hl (.refl x) (.nil (.refl _))
    exact shapeLabel_mono (fun h => h.cons_fLe hl i)
      (fun _ h => UpperLabel.decompose (π := [i]) h hp)

theorem leastShape_le_node {x x₁ x₂ : V k} (hl : Lit.leF x x₁ x₂ ∈ ϕ) :
    leastShape ϕ x ≤ Tree.node (leastShape ϕ x₁) (leastShape ϕ x₂) := by
  intro π a b ha hb
  rw [leastShape_label_eq ha]
  cases π with
  | nil =>
    have he : b = .f := (Option.some.inj hb).symm
    subst b
    exact shapeLabel_le_f ⟨x, x₁, x₂, hl, .nil (.refl x)⟩
  | cons i π =>
    have hb' : (leastShape ϕ (if i = 0 then x₁ else x₂)).fn π = some b := by
      fin_cases i <;> simpa using hb
    rw [leastShape_label_eq hb']
    have hp : UpperAt ϕ [i] x (if i = 0 then x₁ else x₂) :=
      .cons (.refl x) hl (.nil (.refl _))
    exact shapeLabel_mono (fun h => LowerLabel.decompose (π := [i]) h hp)
      (fun _ h => h.cons_leF hl i)

theorem leastShape_sat (hn : ¬ LabelClash ϕ) : Sat (leastShape ϕ) ϕ := by
  intro l hl
  cases l with
  | leF x x₁ x₂ => exact leastShape_le_node hl
  | fLe x₁ x₂ x => exact node_le_leastShape hl
  | eqBot x => exact leastShape_eq_bot hn hl
  | eqTop x => exact leastShape_eq_top hn hl

end DeciNSSE
