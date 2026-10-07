import DeciNSSE.Constraints.PathBounds

/-! # The least covariant solution

Lower-supported labels define a least assignment after pruning. A label clash
is exactly the obstruction to this assignment satisfying the constraints.
-/

namespace DeciNSSE

variable {n k : ℕ} {ϕ : Constraint n k}

/-- Syntactically supported lower bounds on the label of `x` at the path `π`. -/
def LowerLabel (ϕ : Constraint n k) (π : List (Fin n)) : Sym → V k → Prop
  | .top, x => ∃ y, Lit.eqTop y ∈ ϕ ∧ LowerAt ϕ π y x
  | .f, x => ∃ a y, Lit.fLe a y ∈ ϕ ∧ LowerAt ϕ π y x
  | .bot, _ => True

/-- The maximum supported symbol; this is a semantic, classical definition. -/
noncomputable def lowSup (ϕ : Constraint n k) (x : V k) (π : List (Fin n)) : Sym := by
  classical
  exact if LowerLabel ϕ π .top x then .top else if LowerLabel ϕ π .f x then .f else .bot

theorem lowerLabel_le_lowSup {π : List (Fin n)} {g : Sym} {x : V k}
    (h : LowerLabel ϕ π g x) : g ≤ lowSup ϕ x π := by
  classical
  unfold lowSup
  cases g <;> split_ifs <;> simp_all

theorem lowerLabel_lowSup (ϕ : Constraint n k) (x : V k) (π : List (Fin n)) :
    LowerLabel ϕ π (lowSup ϕ x π) x := by
  classical
  unfold lowSup
  split_ifs <;> simp_all [LowerLabel]

theorem lowSup_le {π : List (Fin n)} {x : V k} {b : Sym}
    (h : ∀ g, LowerLabel ϕ π g x → g ≤ b) : lowSup ϕ x π ≤ b :=
  h _ (lowerLabel_lowSup ϕ x π)

theorem lowSup_mono {π τ : List (Fin n)} {x y : V k}
    (h : ∀ g, LowerLabel ϕ π g x → LowerLabel ϕ τ g y) :
    lowSup ϕ x π ≤ lowSup ϕ y τ :=
  lowSup_le (fun g hg => lowerLabel_le_lowSup (h g hg))

/-- `lowSup` is characterised by the two positive label judgments. -/
theorem lowSup_eq_top {π : List (Fin n)} {x : V k} (h : LowerLabel ϕ π .top x) :
    lowSup ϕ x π = .top :=
  (Sym.top_le_iff _).mp (lowerLabel_le_lowSup h)

@[simp] theorem lowerLabel_nil_top {x : V k} :
    LowerLabel ϕ [] .top x ↔ LowerTop ϕ x := by
  simp [LowerLabel, LowerTop]

@[simp] theorem lowerLabel_nil_f {x : V k} :
    LowerLabel ϕ [] .f x ↔ LowerF ϕ x := by
  simp [LowerLabel, LowerF]

/-- A path survives precisely when its proper prefixes carry the constructor. -/
def Active (labels : List (Fin n) → Sym) (π : List (Fin n)) : Prop :=
  ∀ τ, τ <+: π → τ ≠ π → labels τ = .f

@[simp] theorem active_nil (labels : List (Fin n) → Sym) : Active labels [] := by
  intro τ hp hn
  exact False.elim (hn (List.prefix_nil.mp hp))

theorem active_append_singleton (labels : List (Fin n) → Sym)
    (π : List (Fin n)) (i : Fin n) :
    Active labels (π ++ [i]) ↔ Active labels π ∧ labels π = .f := by
  constructor
  · intro h
    have hlen : π ≠ π ++ [i] := by intro he; have := congrArg List.length he; simp at this
    refine ⟨?_, h π (List.prefix_append _ _) hlen⟩
    intro τ hp hn
    apply h τ (hp.trans (List.prefix_append _ _))
    intro he
    have := hp.length_le
    simp [he] at this
  · rintro ⟨h, hf⟩ τ hp hn
    have hlen : τ.length ≤ π.length := by
      have hle := hp.length_le
      have hneq : τ.length ≠ (π ++ [i]).length := fun he => hn (hp.eq_of_length he)
      simp only [List.length_append, List.length_singleton] at hle hneq
      omega
    have hprefix : τ <+: π :=
      List.prefix_of_prefix_length_le hp (List.prefix_append _ _) hlen
    by_cases he : τ = π
    · simpa [he] using hf
    · exact h τ hprefix he

/-- Prune the supported labels below every nullary label. -/
noncomputable def least (ϕ : Constraint n k) (x : V k) : Tree n := by
  classical
  exact {
    fn := fun π => if Active (lowSup ϕ x) π then some (lowSup ϕ x π) else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [active_append_singleton]
        by_cases ha : Active (lowSup ϕ x) π <;> simp [ha]
  }

open Classical in
theorem least_fn (ϕ : Constraint n k) (x : V k) (π : List (Fin n)) :
    (least ϕ x).fn π =
      if Active (lowSup ϕ x) π then some (lowSup ϕ x π) else none := by
  classical
  rfl

@[simp] theorem least_fn_nil (ϕ : Constraint n k) (x : V k) :
    (least ϕ x).fn [] = some (lowSup ϕ x []) := by
  simp [least_fn]

theorem least_label_eq {π : List (Fin n)} {x : V k} {a : Sym}
    (h : (least ϕ x).fn π = some a) : a = lowSup ϕ x π := by
  classical
  rw [least_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem LowerLabel.cons_fLe {π : List (Fin n)} {g : Sym} {a : Fin n → V k} {x : V k}
    (hl : Lit.fLe a x ∈ ϕ) (i : Fin n) (h : LowerLabel ϕ π g (a i)) :
    LowerLabel ϕ (i :: π) g x := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨b, y, hy, hp⟩ := h
    exact ⟨b, y, hy, .cons hl (.refl x) hp⟩
  | top =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons hl (.refl x) hp⟩

theorem LowerLabel.decompose {π π' : List (Fin n)} {g : Sym} {x y : V k}
    (h : LowerLabel ϕ (π ++ π') g x) (hu : UpperAt ϕ π x y) :
    LowerLabel ϕ π' g y := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨a, z, hz, hp⟩ := h
    exact ⟨a, z, hz, hp.decompose_lower hu⟩
  | top =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hp.decompose_lower hu⟩

/-- An explicit bottom excludes both positive lower bounds. -/
theorem least_eq_bot (hn : ¬ LabelClash ϕ) {x : V k} (hl : Lit.eqBot x ∈ ϕ) :
    least ϕ x = Tree.bot := by
  apply (Tree.root_eq_bot_iff _).mp
  rw [least_fn_nil]
  congr 1
  apply (Sym.le_bot_iff _).mp
  apply lowSup_le
  intro g hg
  have hu : UpperBot ϕ x := ⟨x, hl, .refl x⟩
  cases g with
  | bot => exact le_rfl
  | f => exact False.elim (hn ⟨x, Or.inr (Or.inr ⟨lowerLabel_nil_f.mp hg, hu⟩)⟩)
  | top => exact False.elim (hn ⟨x, Or.inl ⟨lowerLabel_nil_top.mp hg, hu⟩⟩)

/-- A prescribed top is realised by the least assignment. -/
theorem least_eq_top {x : V k} (hl : Lit.eqTop x ∈ ϕ) : least ϕ x = Tree.top := by
  apply (Tree.root_eq_top_iff _).mp
  rw [least_fn_nil]
  congr 1
  exact lowSup_eq_top (π := []) ⟨x, hl, .nil (.refl x)⟩

/-- Lower constructor bounds propagate down the path. -/
theorem node_le_least {a : Fin n → V k} {x : V k} (hl : Lit.fLe a x ∈ ϕ) :
    Tree.node (least ϕ ∘ a) ≤ least ϕ x := by
  intro π c Tree.dual hc hd
  rw [least_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact lowerLabel_le_lowSup ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (least ϕ (a i)).fn π = some c := hc
    rw [least_label_eq hc']
    exact lowSup_mono (fun _ hg => hg.cons_fLe hl i)

/-- Without label clashes, the least assignment satisfies each upper constructor literal. -/
theorem least_le_node (hn : ¬ LabelClash ϕ) {x : V k} {b : Fin n → V k}
    (hl : Lit.leF x b ∈ ϕ) :
    least ϕ x ≤ Tree.node (least ϕ ∘ b) := by
  intro π c Tree.dual hc hd
  rw [least_label_eq hc]
  cases π with
  | nil =>
    have he : Tree.dual = .f := (Option.some.inj hd).symm
    subst Tree.dual
    apply lowSup_le
    intro g hg
    cases g with
    | bot => exact Sym.bot_le _
    | f => exact le_rfl
    | top =>
      exact False.elim (hn ⟨x, Or.inr (Or.inl
        ⟨lowerLabel_nil_top.mp hg, ⟨x, b, hl, .refl x⟩⟩)⟩)
  | cons i π =>
    have hd' : (least ϕ (b i)).fn π = some Tree.dual := hd
    rw [least_label_eq hd']
    have hu : UpperAt ϕ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact lowSup_mono (fun _ hg => LowerLabel.decompose (π := [i]) hg hu)

/-- Absence of a label clash suffices for the explicitly constructed solution. -/
theorem least_sat (hn : ¬ LabelClash ϕ) : Covariant.Sat (least ϕ) ϕ := by
  intro l hl
  cases l with
  | leF x b => exact least_le_node hn hl
  | fLe a x => exact node_le_least hl
  | eqBot x => exact least_eq_bot hn hl
  | eqTop x => exact least_eq_top hl

/-- A covariant system is satisfiable exactly when it has no label clash. -/
theorem satisfiable_iff_not_labelClash : (∃ ρ, Covariant.Sat ρ ϕ) ↔ ¬ LabelClash ϕ :=
  ⟨fun hs hc => hc.unsatisfiable hs, fun hn => ⟨least ϕ, least_sat hn⟩⟩

end DeciNSSE
