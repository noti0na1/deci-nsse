import DeciNSSE.Constraints.Closure

/-! # Least solutions

Path-indexed lower and upper bounds determine a least tree assignment.
Absence of a label clash ensures that this assignment satisfies every constraint.
-/

namespace DeciNSSE

variable {k : ℕ} {ϕ : Constraint k}

inductive LowerAt (ϕ : Constraint k) : List (Fin 2) → V k → V k → Prop where
  | nil {x y : V k} : Derives ϕ x y → LowerAt ϕ [] x y
  | cons {z₁ z₂ z y x : V k} {π : List (Fin 2)} {i : Fin 2} :
      Lit.fLe z₁ z₂ z ∈ ϕ → Derives ϕ z y →
      LowerAt ϕ π x (if i = 0 then z₁ else z₂) → LowerAt ϕ (i :: π) x y

inductive UpperAt (ϕ : Constraint k) : List (Fin 2) → V k → V k → Prop where
  | nil {x y : V k} : Derives ϕ x y → UpperAt ϕ [] x y
  | cons {x z z₁ z₂ y : V k} {π : List (Fin 2)} {i : Fin 2} :
      Derives ϕ x z → Lit.leF z z₁ z₂ ∈ ϕ →
      UpperAt ϕ π (if i = 0 then z₁ else z₂) y → UpperAt ϕ (i :: π) x y

@[simp] theorem lowerAt_nil_iff {x y : V k} : LowerAt ϕ [] x y ↔ Derives ϕ x y :=
  ⟨fun h => by cases h with | nil h => exact h, LowerAt.nil⟩

@[simp] theorem upperAt_nil_iff {x y : V k} : UpperAt ϕ [] x y ↔ Derives ϕ x y :=
  ⟨fun h => by cases h with | nil h => exact h, UpperAt.nil⟩

theorem LowerAt.trans_right {π : List (Fin 2)} {x y z : V k}
    (h : LowerAt ϕ π x y) (hyz : Derives ϕ y z) : LowerAt ϕ π x z := by
  cases h with
  | nil h => exact .nil (.trans h hyz)
  | cons hl hd hp => exact .cons hl (.trans hd hyz) hp

theorem UpperAt.trans_left {π : List (Fin 2)} {x y z : V k}
    (hxy : Derives ϕ x y) (h : UpperAt ϕ π y z) : UpperAt ϕ π x z := by
  cases h with
  | nil h => exact .nil (.trans hxy h)
  | cons hd hl hp => exact .cons (.trans hxy hd) hl hp

private theorem derives_children {a₁ a₂ a b b₁ b₂ : V k} (i : Fin 2)
    (hl : Lit.fLe a₁ a₂ a ∈ ϕ) (hd : Derives ϕ a b)
    (hu : Lit.leF b b₁ b₂ ∈ ϕ) :
    Derives ϕ (if i = 0 then a₁ else a₂) (if i = 0 then b₁ else b₂) := by
  split
  · exact .decomp_left hl hd hu
  · exact .decomp_right hl hd hu

theorem LowerAt.decompose_upper {π π' : List (Fin 2)} {w u v : V k}
    (hl : LowerAt ϕ π w u) (hu : UpperAt ϕ (π ++ π') u v) :
    UpperAt ϕ π' w v := by
  induction π generalizing w u with
  | nil => exact UpperAt.trans_left (lowerAt_nil_iff.mp hl) hu
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (derives_children i hfl (.trans hd₁ hd₂) hfu)) hu

theorem LowerAt.decompose_lower {π π' : List (Fin 2)} {v u w : V k}
    (hl : LowerAt ϕ (π ++ π') v u) (hu : UpperAt ϕ π u w) :
    LowerAt ϕ π' v w := by
  induction π generalizing u with
  | nil => exact hl.trans_right (upperAt_nil_iff.mp hu)
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (derives_children i hfl (.trans hd₁ hd₂) hfu)) hu

namespace PathBounds

def embed (filler : Tree) : List (Fin 2) → Tree → Tree
  | [], t => t
  | i :: π, t => if i = 0 then Tree.node (embed filler π t) filler
      else Tree.node filler (embed filler π t)

theorem embed_fn_append (filler t : Tree) (π τ : List (Fin 2)) :
    (embed filler π t).fn (π ++ τ) = t.fn τ := by
  induction π with
  | nil => rfl
  | cons i π ih => fin_cases i <;> simpa [embed] using ih

theorem embed_subtree (filler t : Tree) (π : List (Fin 2)) :
    (embed filler π t).subtree π = some t := by
  have hd : ((embed filler π t).fn π).isSome := by
    have he := embed_fn_append filler t π []
    simp only [List.append_nil] at he
    rw [he]
    exact t.root_isSome
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp
    ((Tree.subtree_isSome_iff _ _).mpr hd)
  have hut : u = t := by
    apply Tree.ext
    funext τ
    rw [Tree.subtree_fn hu, embed_fn_append]
  simpa [hut] using hu

end PathBounds

theorem LowerAt.embed_le {π : List (Fin 2)} {x y : V k}
    (h : LowerAt ϕ π x y) {ρ : V k → Tree} (hρ : Sat ρ ϕ) :
    PathBounds.embed Tree.bot π (ρ x) ≤ ρ y := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons z₁ z₂ z y x π i hl hd hp ih =>
    apply le_trans ?_ (le_trans (hρ _ hl) (hd.sound ρ hρ))
    fin_cases i <;> simp_all [PathBounds.embed, Tree.node_le_node_iff]

theorem UpperAt.le_embed {π : List (Fin 2)} {x y : V k}
    (h : UpperAt ϕ π x y) {ρ : V k → Tree} (hρ : Sat ρ ϕ) :
    ρ x ≤ PathBounds.embed Tree.top π (ρ y) := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons x z z₁ z₂ y π i hd hl hp ih =>
    apply le_trans (le_trans (hd.sound ρ hρ) (hρ _ hl))
    fin_cases i <;> simp_all [PathBounds.embed, Tree.node_le_node_iff]

theorem UpperAt.sound {π : List (Fin 2)} {x y : V k}
    (h : UpperAt ϕ π x y) {ρ : V k → Tree} (hρ : Sat ρ ϕ) :
    ∃ t : Tree, ρ x ≤ t ∧ t.subtree π = some (ρ y) :=
  ⟨_, h.le_embed hρ, PathBounds.embed_subtree _ _ _⟩

def LowerLabel (ϕ : Constraint k) (π : List (Fin 2)) : Sym → V k → Prop
  | .top, x => ∃ y, Lit.eqTop y ∈ ϕ ∧ LowerAt ϕ π y x
  | .f, x => ∃ y y₁ y₂, Lit.fLe y₁ y₂ y ∈ ϕ ∧ LowerAt ϕ π y x
  | .bot, _ => True

noncomputable def lowSup (ϕ : Constraint k) (x : V k) (π : List (Fin 2)) : Sym := by
  classical
  exact if LowerLabel ϕ π .top x then .top else if LowerLabel ϕ π .f x then .f else .bot

theorem lowerLabel_le_lowSup {π : List (Fin 2)} {g : Sym} {x : V k}
    (h : LowerLabel ϕ π g x) : g ≤ lowSup ϕ x π := by
  classical
  unfold lowSup
  cases g <;> split_ifs <;> simp_all

theorem lowerLabel_lowSup (ϕ : Constraint k) (x : V k) (π : List (Fin 2)) :
    LowerLabel ϕ π (lowSup ϕ x π) x := by
  classical
  unfold lowSup
  split_ifs <;> simp_all [LowerLabel]

theorem lowSup_le {π : List (Fin 2)} {x : V k} {b : Sym}
    (h : ∀ g, LowerLabel ϕ π g x → g ≤ b) : lowSup ϕ x π ≤ b :=
  h _ (lowerLabel_lowSup ϕ x π)

theorem lowSup_mono {π τ : List (Fin 2)} {x y : V k}
    (h : ∀ g, LowerLabel ϕ π g x → LowerLabel ϕ τ g y) :
    lowSup ϕ x π ≤ lowSup ϕ y τ :=
  lowSup_le (fun g hg => lowerLabel_le_lowSup (h g hg))

@[simp] theorem lowerLabel_nil_top {x : V k} :
    LowerLabel ϕ [] .top x ↔ LowerTop ϕ x := by
  simp [LowerLabel, LowerTop]

@[simp] theorem lowerLabel_nil_f {x : V k} :
    LowerLabel ϕ [] .f x ↔ LowerF ϕ x := by
  simp only [LowerLabel, LowerF, lowerAt_nil_iff]
  constructor
  · rintro ⟨y, y₁, y₂, hl, hd⟩; exact ⟨y₁, y₂, y, hl, hd⟩
  · rintro ⟨y₁, y₂, y, hl, hd⟩; exact ⟨y, y₁, y₂, hl, hd⟩

namespace LeastConstruction

def Active (labels : List (Fin 2) → Sym) (π : List (Fin 2)) : Prop :=
  ∀ τ, τ <+: π → τ ≠ π → labels τ = .f

@[simp] theorem active_nil (labels : List (Fin 2) → Sym) : Active labels [] := by
  intro τ hp hn
  exact False.elim (hn (List.prefix_nil.mp hp))

theorem active_append_singleton (labels : List (Fin 2) → Sym)
    (π : List (Fin 2)) (i : Fin 2) :
    Active labels (π ++ [i]) ↔ Active labels π ∧ labels π = .f := by
  constructor
  · intro h
    have hlen : π ≠ π ++ [i] := by intro he; have := congrArg List.length he; simp at this
    refine ⟨?_, h π (List.prefix_append _ _) hlen⟩
    intro τ hp hn
    apply h τ (hp.trans (List.prefix_append _ _))
    intro he
    have := hp.length_le
    simp only [he, List.length_append, List.length_singleton] at this
    omega
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

end LeastConstruction

noncomputable def least (ϕ : Constraint k) (x : V k) : Tree := by
  classical
  exact {
    fn := fun π => if LeastConstruction.Active (lowSup ϕ x) π then some (lowSup ϕ x π)
      else none
    wf := by
      constructor
      · simp
      · intro π i
        simp only [LeastConstruction.active_append_singleton]
        by_cases ha : LeastConstruction.Active (lowSup ϕ x) π <;> simp [ha]
  }

open Classical in
theorem least_fn (ϕ : Constraint k) (x : V k) (π : List (Fin 2)) :
    (least ϕ x).fn π =
      if LeastConstruction.Active (lowSup ϕ x) π then some (lowSup ϕ x π) else none := by
  classical
  rfl

@[simp] theorem least_fn_nil (ϕ : Constraint k) (x : V k) :
    (least ϕ x).fn [] = some (lowSup ϕ x []) := by
  simp [least_fn]

theorem least_label_eq {π : List (Fin 2)} {x : V k} {a : Sym}
    (h : (least ϕ x).fn π = some a) : a = lowSup ϕ x π := by
  classical
  rw [least_fn] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

theorem LowerLabel.cons_fLe {π : List (Fin 2)} {g : Sym} {x x₁ x₂ : V k}
    (hl : Lit.fLe x₁ x₂ x ∈ ϕ) (i : Fin 2)
    (h : LowerLabel ϕ π g (if i = 0 then x₁ else x₂)) :
    LowerLabel ϕ (i :: π) g x := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨y, y₁, y₂, hy, hp⟩ := h
    exact ⟨y, y₁, y₂, hy, .cons hl (.refl x) hp⟩
  | top =>
    obtain ⟨y, hy, hp⟩ := h
    exact ⟨y, hy, .cons hl (.refl x) hp⟩

theorem LowerLabel.decompose {π π' : List (Fin 2)} {g : Sym} {x y : V k}
    (h : LowerLabel ϕ (π ++ π') g x) (hu : UpperAt ϕ π x y) :
    LowerLabel ϕ π' g y := by
  cases g with
  | bot => trivial
  | f =>
    obtain ⟨z, z₁, z₂, hz, hp⟩ := h
    exact ⟨z, z₁, z₂, hz, hp.decompose_lower hu⟩
  | top =>
    obtain ⟨z, hz, hp⟩ := h
    exact ⟨z, hz, hp.decompose_lower hu⟩

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

theorem least_eq_top {x : V k} (hl : Lit.eqTop x ∈ ϕ) : least ϕ x = Tree.top := by
  apply (Tree.root_eq_top_iff _).mp
  rw [least_fn_nil]
  congr 1
  exact (Sym.top_le_iff _).mp
    (lowerLabel_le_lowSup (g := .top) (π := []) ⟨x, hl, .nil (.refl x)⟩)

theorem node_le_least {x x₁ x₂ : V k} (hl : Lit.fLe x₁ x₂ x ∈ ϕ) :
    Tree.node (least ϕ x₁) (least ϕ x₂) ≤ least ϕ x := by
  intro π a b ha hb
  rw [least_label_eq hb]
  cases π with
  | nil =>
    have he : a = .f := (Option.some.inj ha).symm
    subst a
    exact lowerLabel_le_lowSup ⟨x, x₁, x₂, hl, .nil (.refl x)⟩
  | cons i π =>
    have ha' : (least ϕ (if i = 0 then x₁ else x₂)).fn π = some a := by
      fin_cases i <;> simpa using ha
    rw [least_label_eq ha']
    exact lowSup_mono (fun _ hg => hg.cons_fLe hl i)

theorem least_le_node (hn : ¬ LabelClash ϕ) {x x₁ x₂ : V k}
    (hl : Lit.leF x x₁ x₂ ∈ ϕ) :
    least ϕ x ≤ Tree.node (least ϕ x₁) (least ϕ x₂) := by
  intro π a b ha hb
  rw [least_label_eq ha]
  cases π with
  | nil =>
    have he : b = .f := (Option.some.inj hb).symm
    subst b
    apply lowSup_le
    intro g hg
    cases g with
    | bot => exact Sym.bot_le _
    | f => exact le_rfl
    | top =>
      exact False.elim (hn ⟨x, Or.inr (Or.inl
        ⟨lowerLabel_nil_top.mp hg, ⟨x, x₁, x₂, hl, .refl x⟩⟩)⟩)
  | cons i π =>
    have hb' : (least ϕ (if i = 0 then x₁ else x₂)).fn π = some b := by
      fin_cases i <;> simpa using hb
    rw [least_label_eq hb']
    have hu : UpperAt ϕ [i] x (if i = 0 then x₁ else x₂) :=
      .cons (.refl x) hl (.nil (.refl _))
    exact lowSup_mono (fun _ hg => LowerLabel.decompose (π := [i]) hg hu)

theorem least_sat (hn : ¬ LabelClash ϕ) : Sat (least ϕ) ϕ := by
  intro l hl
  cases l with
  | leF x x₁ x₂ => exact least_le_node hn hl
  | fLe x₁ x₂ x => exact node_le_least hl
  | eqBot x => exact least_eq_bot hn hl
  | eqTop x => exact least_eq_top hl

theorem satisfiable_iff_not_labelClash : (∃ ρ, Sat ρ ϕ) ↔ ¬ LabelClash ϕ :=
  ⟨fun hs hc => hc.unsatisfiable hs, fun hn => ⟨least ϕ, least_sat hn⟩⟩

end DeciNSSE
