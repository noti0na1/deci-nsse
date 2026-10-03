import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
import DeciNSSE.Satisfiability.Least

/-! # Cyclic obstructions to finite solutions

A nonempty path bounding a variable from both sides yields a cycle clash.
Repeated embeddings along this path are incompatible with finite tree height.
-/

namespace DeciNSSE

variable {k : ℕ} {ϕ : Constraint k}

def CycleClash (ϕ : Constraint k) : Prop :=
  ∃ π x y, π ≠ [] ∧ LowerAt ϕ π x x ∧ Derives ϕ x y ∧ UpperAt ϕ π y y

namespace PathBounds

theorem embed_mono (filler : Tree) (π : List (Fin 2)) {t u : Tree}
    (h : t ≤ u) : embed filler π t ≤ embed filler π u := by
  induction π with
  | nil => exact h
  | cons i π ih =>
    fin_cases i <;> simp [embed, Tree.node_le_node_iff, ih]

theorem embed_append (filler t : Tree) (π τ : List (Fin 2)) :
    embed filler (π ++ τ) t = embed filler π (embed filler τ t) := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [embed, ih]

theorem embed_repeat_le {t : Tree} {π : List (Fin 2)}
    (h : embed Tree.bot π t ≤ t) (n : ℕ) :
    embed Tree.bot (List.replicate n π).flatten t ≤ t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans (embed_mono Tree.bot π ih) h

theorem le_embed_repeat {t : Tree} {π : List (Fin 2)}
    (h : t ≤ embed Tree.top π t) (n : ℕ) :
    t ≤ embed Tree.top (List.replicate n π).flatten t := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simpa [List.replicate_succ, embed_append] using
      le_trans h (embed_mono Tree.top π ih)

theorem repeat_isSome {t u : Tree} {π : List (Fin 2)}
    (hl : embed Tree.bot π t ≤ t) (htu : t ≤ u)
    (hu : u ≤ embed Tree.top π u) (n : ℕ) :
    (t.fn (List.replicate n π).flatten).isSome := by
  apply Tree.middle_isSome (embed_repeat_le hl n)
    (le_trans htu (le_embed_repeat hu n))
  · have he := embed_fn_append Tree.bot t (List.replicate n π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact t.root_isSome
  · have he := embed_fn_append Tree.top u (List.replicate n π).flatten []
    simp only [List.append_nil] at he
    rw [he]
    exact u.root_isSome

end PathBounds

namespace FTree

def height : FTree → ℕ
  | .bot | .top => 0
  | .node l r => max l.height r.height + 1

theorem length_le_height {t : FTree} {π : List (Fin 2)}
    (h : (t.toTree.fn π).isSome) : π.length ≤ t.height := by
  induction t generalizing π with
  | bot => cases π <;> simp_all [toTree, height]
  | top => cases π <;> simp_all [toTree, height]
  | node l r ihl ihr =>
    cases π with
    | nil => simp
    | cons i π =>
      fin_cases i
      · have hp := ihl (by simpa [toTree] using h)
        simp only [List.length_cons, height]
        omega
      · have hp := ihr (by simpa [toTree] using h)
        simp only [List.length_cons, height]
        omega

end FTree

theorem CycleClash.no_finite_solution (hc : CycleClash ϕ) :
    ¬ ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ := by
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
