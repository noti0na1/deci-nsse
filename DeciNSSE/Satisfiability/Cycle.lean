import DeciNSSE.Constraints.PathBounds

/-! # Cycle clashes force infinite depth

Matching nonempty lower and upper self-paths, joined by closure, force paths
of unbounded length in every solution. Such a cycle clash excludes finite
solutions.
-/

namespace DeciNSSE

variable {n k : ℕ} {ϕ : Constraint n k}

/-- A nonempty lower self-path lies below a matching upper self-path. -/
def CycleClash (ϕ : Constraint n k) : Prop :=
  ∃ π x y, π ≠ [] ∧ LowerAt ϕ π x x ∧ Derives ϕ x y ∧ UpperAt ϕ π y y

namespace PathBounds

theorem embed_mono (filler : Tree n) (π : List (Fin n)) {t u : Tree n}
    (h : t ≤ u) : embed filler π t ≤ embed filler π u := by
  induction π with
  | nil => exact h
  | cons i π ih =>
    rw [embed_cons, embed_cons, Tree.node_le_node_iff]
    intro j
    by_cases hj : j = i
    · simpa [hj] using ih
    · simp [hj]

theorem embed_append (filler t : Tree n) (π τ : List (Fin n)) :
    embed filler (π ++ τ) t = embed filler π (embed filler τ t) := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [embed_cons, ih]

/-- Iterating a lower self-bound preserves the bound. -/
theorem embed_repeat_le {t : Tree n} {π : List (Fin n)}
    (h : embed Tree.bot π t ≤ t) (m : ℕ) :
    embed Tree.bot (List.replicate m π).flatten t ≤ t := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans (embed_mono Tree.bot π ih) h

/-- Iterating an upper self-bound preserves the bound. -/
theorem le_embed_repeat {t : Tree n} {π : List (Fin n)}
    (h : t ≤ embed Tree.top π t) (m : ℕ) :
    t ≤ embed Tree.top (List.replicate m π).flatten t := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans h (embed_mono Tree.top π ih)

/-- Matching lower and upper cycles force every power of the path to exist. -/
theorem repeat_isSome {t u : Tree n} {π : List (Fin n)}
    (hl : embed Tree.bot π t ≤ t) (htu : t ≤ u)
    (hu : u ≤ embed Tree.top π u) (m : ℕ) :
    (t.fn (List.replicate m π).flatten).isSome := by
  apply Tree.middle_isSome (embed_repeat_le hl m)
    (le_trans htu (le_embed_repeat hu m))
  · have he := embed_fn_append Tree.bot t (List.replicate m π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact t.root_isSome
  · have he := embed_fn_append Tree.top u (List.replicate m π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact u.root_isSome

end PathBounds

namespace FTree

/-- Maximum edge depth of a finite tree. -/
def height : FTree n → ℕ
  | .bot | .top => 0
  | .node a => (Finset.univ.sup fun i => (a i).height) + 1

@[simp] theorem height_bot : (bot : FTree n).height = 0 := rfl
@[simp] theorem height_top : (top : FTree n).height = 0 := rfl

theorem height_node (a : Fin n → FTree n) :
    (node a).height = (Finset.univ.sup fun i => (a i).height) + 1 := rfl

theorem height_child_lt (a : Fin n → FTree n) (i : Fin n) :
    (a i).height < (node a).height := by
  rw [height_node]
  have := Finset.le_sup (f := fun i => (a i).height) (Finset.mem_univ i)
  omega

theorem length_le_height {t : FTree n} {π : List (Fin n)}
    (h : (t.toTree.fn π).isSome) : π.length ≤ t.height := by
  induction t generalizing π with
  | bot => cases π <;> simp_all [toTree]
  | top => cases π <;> simp_all [toTree]
  | node a ih =>
    cases π with
    | nil => simp
    | cons i π =>
      have hp := ih i (π := π) (by simpa [toTree] using h)
      have hlt := height_child_lt a i
      simp only [List.length_cons]
      omega

end FTree

/-- No valuation into finite trees can satisfy a cycle clash. -/
theorem CycleClash.no_finite_solution (hc : CycleClash ϕ) :
    ¬ ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  rintro ⟨σ, hσ⟩
  obtain ⟨π, x, y, hπ, hl, hd, hu⟩ := hc
  have hdom := PathBounds.repeat_isSome (hl.embed_le hσ) (hd.sound _ hσ)
    (hu.le_embed hσ) ((σ x).height + 1)
  have hlen := FTree.length_le_height hdom
  have hpos : 0 < π.length := List.length_pos_iff.mpr hπ
  simp only [List.length_flatten, List.map_replicate, List.sum_replicate,
    smul_eq_mul] at hlen
  nlinarith

end DeciNSSE
