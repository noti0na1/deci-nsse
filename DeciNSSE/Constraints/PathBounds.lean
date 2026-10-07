import DeciNSSE.Constraints.Closure

/-! # Bounds along constructor paths

Upper and lower path judgements propagate constructor bounds through the
closure. Their composition, factorisation and cancellation laws connect
constraint derivations with labels at finite tree paths.
-/

namespace DeciNSSE

variable {n k : ℕ} {ϕ : Constraint n k}

/-- `LowerAt ϕ π x y`: the subtree of `y` at `π` is bounded below by `x`. -/
inductive LowerAt (ϕ : Constraint n k) : List (Fin n) → V k → V k → Prop where
  | nil {x y : V k} : Derives ϕ x y → LowerAt ϕ [] x y
  | cons {a : Fin n → V k} {z y x : V k} {π : List (Fin n)} {i : Fin n} :
      Lit.fLe a z ∈ ϕ → Derives ϕ z y → LowerAt ϕ π x (a i) →
      LowerAt ϕ (i :: π) x y

/-- `UpperAt ϕ π x y`: the subtree of `x` at `π` is bounded above by `y`. -/
inductive UpperAt (ϕ : Constraint n k) : List (Fin n) → V k → V k → Prop where
  | nil {x y : V k} : Derives ϕ x y → UpperAt ϕ [] x y
  | cons {x z : V k} {b : Fin n → V k} {y : V k} {π : List (Fin n)} {i : Fin n} :
      Derives ϕ x z → Lit.leF z b ∈ ϕ → UpperAt ϕ π (b i) y →
      UpperAt ϕ (i :: π) x y

@[simp] theorem lowerAt_nil_iff {x y : V k} : LowerAt ϕ [] x y ↔ Derives ϕ x y :=
  ⟨fun h => by cases h with | nil h => exact h, LowerAt.nil⟩

@[simp] theorem upperAt_nil_iff {x y : V k} : UpperAt ϕ [] x y ↔ Derives ϕ x y :=
  ⟨fun h => by cases h with | nil h => exact h, UpperAt.nil⟩

theorem LowerAt.trans_right {π : List (Fin n)} {x y z : V k}
    (h : LowerAt ϕ π x y) (hyz : Derives ϕ y z) : LowerAt ϕ π x z := by
  cases h with
  | nil h => exact .nil (.trans h hyz)
  | cons hl hd hp => exact .cons hl (.trans hd hyz) hp

theorem UpperAt.trans_left {π : List (Fin n)} {x y z : V k}
    (hxy : Derives ϕ x y) (h : UpperAt ϕ π y z) : UpperAt ϕ π x z := by
  cases h with
  | nil h => exact .nil (.trans hxy h)
  | cons hd hl hp => exact .cons (.trans hxy hd) hl hp

/-- Cancel a lower path from an upper path. -/
theorem LowerAt.decompose_upper {π π' : List (Fin n)} {w u v : V k}
    (hl : LowerAt ϕ π w u) (hu : UpperAt ϕ (π ++ π') u v) :
    UpperAt ϕ π' w v := by
  induction π generalizing w u with
  | nil => exact UpperAt.trans_left (lowerAt_nil_iff.mp hl) hu
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (Derives.decomp i hfl (.trans hd₁ hd₂) hfu)) hu

/-- Cancel an upper path from a lower path. -/
theorem LowerAt.decompose_lower {π π' : List (Fin n)} {v u w : V k}
    (hl : LowerAt ϕ (π ++ π') v u) (hu : UpperAt ϕ π u w) :
    LowerAt ϕ π' v w := by
  induction π generalizing u with
  | nil => exact hl.trans_right (upperAt_nil_iff.mp hu)
  | cons i π ih =>
    cases hl with
    | cons hfl hd₁ hl =>
      cases hu with
      | cons hd₂ hfu hu =>
        exact ih (hl.trans_right (Derives.decomp i hfl (.trans hd₁ hd₂) hfu)) hu

theorem LowerAt.comp {π π' : List (Fin n)} {x w z : V k}
    (h' : LowerAt ϕ π' x w) (h : LowerAt ϕ π w z) :
    LowerAt ϕ (π ++ π') x z := by
  induction h with
  | nil hd => exact h'.trans_right hd
  | cons hl hd _ ih => exact .cons hl hd (ih h')

theorem UpperAt.comp {π π' : List (Fin n)} {z w y : V k}
    (h : UpperAt ϕ π z w) (h' : UpperAt ϕ π' w y) :
    UpperAt ϕ (π ++ π') z y := by
  induction h with
  | nil hd => exact UpperAt.trans_left hd h'
  | cons hd hl _ ih => exact .cons hd hl (ih h')

theorem LowerAt.factor {π π' : List (Fin n)} {x z : V k}
    (h : LowerAt ϕ (π ++ π') x z) :
    ∃ w, LowerAt ϕ π w z ∧ LowerAt ϕ π' x w := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hl hd hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hl hd hw, hw'⟩

theorem UpperAt.factor {π π' : List (Fin n)} {z y : V k}
    (h : UpperAt ϕ (π ++ π') z y) :
    ∃ w, UpperAt ϕ π z w ∧ UpperAt ϕ π' w y := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hd hl hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hd hl hw, hw'⟩

theorem LowerAt.map {m : ℕ} {ψ : Constraint n m} (r : V k → V m)
    (hr : ∀ l ∈ ϕ, l.rename r ∈ ψ) {π : List (Fin n)} {a b : V k}
    (h : LowerAt ϕ π a b) : LowerAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons c z y x π i hl hd _ ih =>
    exact LowerAt.cons (a := r ∘ c) (hr _ hl) (hd.map r hr) ih

theorem UpperAt.map {m : ℕ} {ψ : Constraint n m} (r : V k → V m)
    (hr : ∀ l ∈ ϕ, l.rename r ∈ ψ) {π : List (Fin n)} {a b : V k}
    (h : UpperAt ϕ π a b) : UpperAt ψ π (r a) (r b) := by
  induction h with
  | nil hd => exact .nil (hd.map r hr)
  | @cons x z c y π i hd hl _ ih =>
    exact UpperAt.cons (b := r ∘ c) (hd.map r hr) (hr _ hl) ih

namespace PathBounds

/-- Embed a tree at a path; every off-path child on the spine is `filler`. -/
def embed (filler : Tree n) : List (Fin n) → Tree n → Tree n
  | [], t => t
  | i :: π, t => Tree.node (fun j => if j = i then embed filler π t else filler)

@[simp] theorem embed_nil (filler t : Tree n) : embed filler [] t = t := rfl

theorem embed_cons (filler t : Tree n) (i : Fin n) (π : List (Fin n)) :
    embed filler (i :: π) t =
      Tree.node (fun j => if j = i then embed filler π t else filler) := rfl

theorem embed_fn_append (filler t : Tree n) (π τ : List (Fin n)) :
    (embed filler π t).fn (π ++ τ) = t.fn τ := by
  induction π with
  | nil => rfl
  | cons i π ih => simpa [embed_cons] using ih

end PathBounds

theorem LowerAt.embed_le {π : List (Fin n)} {x y : V k}
    (h : LowerAt ϕ π x y) {ρ : V k → Tree n} (hρ : Covariant.Sat ρ ϕ) :
    PathBounds.embed Tree.bot π (ρ x) ≤ ρ y := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons a z y x π i hl hd hp ih =>
    have hz : Tree.node (ρ ∘ a) ≤ ρ y := le_trans (hρ _ hl) (hd.sound ρ hρ)
    refine le_trans ?_ hz
    rw [PathBounds.embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using ih
    · simp [hj]

theorem UpperAt.le_embed {π : List (Fin n)} {x y : V k}
    (h : UpperAt ϕ π x y) {ρ : V k → Tree n} (hρ : Covariant.Sat ρ ϕ) :
    ρ x ≤ PathBounds.embed Tree.top π (ρ y) := by
  induction h with
  | nil hd => exact hd.sound ρ hρ
  | @cons x z b y π i hd hl hp ih =>
    have hz : ρ x ≤ Tree.node (ρ ∘ b) := le_trans (hd.sound ρ hρ) (hρ _ hl)
    refine le_trans hz ?_
    rw [PathBounds.embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using ih
    · simp [hj]

end DeciNSSE
