import DeciNSSE.Shortening.Paths
import DeciNSSE.Monitor.Reader
import DeciNSSE.Holes.Hierarchy.Reader

/-! # Transformations of label-reader states

## Main declarations

- `reader_actionBound` counts the two image relations, the individual bottom
  and top flags, and the relation witnessing a meeting at a common prefix.
-/

namespace DeciNSSE.Shortening
open Monitor LetteredHierarchy CoAlignment
variable {n m : ℕ}

private def walk {α β : Type*} (edge : α → β → β → Prop) : List α → β → β → Prop
  | [], x, y => x = y
  | a :: w, x, y => ∃ z, edge a x z ∧ walk edge w z y

private abbrev upper (ψ : Constraint n m) := walk fun i x y => UpperAt ψ [i] x y
private abbrev lower (ψ : Constraint n m) := walk fun i x y => LowerAt ψ [i] y x

private theorem images (ψ : Constraint n m) (X Y : V m) (s : State m) (w : List (Fin n)) :
    (∀ y, y ∈ ((reader ψ X Y).evalFrom s w).U ↔ ∃ x ∈ s.U, upper ψ w x y) ∧
    (∀ y, y ∈ ((reader ψ X Y).evalFrom s w).L ↔ ∃ x ∈ s.L, lower ψ w x y) := by
  induction w generalizing s with
  | nil => simp [upper, lower, walk]
  | cons a w ih =>
    obtain ⟨hu, hl⟩ := ih ((reader ψ X Y).step s a)
    constructor
    · intro y
      rw [DFA.evalFrom_cons, hu, reader_step]
      simp only [mem_upperStep, upper, walk]
      exact ⟨fun ⟨z, ⟨x, hx, hxz⟩, hzy⟩ => ⟨x, hx, z, hxz, hzy⟩,
        fun ⟨x, hx, z, hxz, hzy⟩ => ⟨z, ⟨x, hx, hxz⟩, hzy⟩⟩
    · intro y
      rw [DFA.evalFrom_cons, hl, reader_step]
      simp only [mem_lowerStep, lower, walk]
      exact ⟨fun ⟨z, ⟨x, hx, hxz⟩, hzy⟩ => ⟨x, hx, z, hxz, hzy⟩,
        fun ⟨x, hx, z, hxz, hzy⟩ => ⟨z, ⟨x, hx, hxz⟩, hzy⟩⟩

private theorem latch (ψ : Constraint n m) (X Y : V m) (s : State m) (w : List (Fin n)) :
    ((reader ψ X Y).evalFrom s w).b = true ↔ s.b = true ∨ ∃ i < w.length,
      Ready ψ ((reader ψ X Y).evalFrom s (w.take i)).U
        ((reader ψ X Y).evalFrom s (w.take i)).L := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w a ih =>
    rw [DFA.evalFrom_append_singleton, reader_step, Bool.or_eq_true, decide_eq_true_eq, ih]
    simp only [List.length_append, List.length_singleton]
    constructor
    · rintro ((h | ⟨i, hi, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨i, by omega, by rwa [List.take_append_of_le_length hi.le]⟩
      · exact Or.inr ⟨w.length, by omega, by simpa⟩
    · rintro (h | ⟨i, hi, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_or_ge i w.length with ht | ht
        · exact Or.inl (Or.inr ⟨i, ht, by rwa [List.take_append_of_le_length ht.le] at h⟩)
        · obtain rfl : i = w.length := by omega
          exact Or.inr (by simpa using h)

private abbrev Signature (m : ℕ) :=
  Finset (V m × V m) × Finset (V m × V m) × Finset (V m) × Finset (V m) × Finset (V m × V m)

private noncomputable def signature (ψ : Constraint n m) (w : List (Fin n)) : Signature m := by
  classical
  exact (Finset.univ.filter (fun (x, y) => upper ψ w x y),
    Finset.univ.filter (fun (x, y) => lower ψ w x y),
    Finset.univ.filter (fun x => ∃ i < w.length, ∃ y ∈ botVars ψ, upper ψ (w.take i) x y),
    Finset.univ.filter (fun x => ∃ i < w.length, ∃ y ∈ topVars ψ, lower ψ (w.take i) x y),
    Finset.univ.filter (fun (x, z) =>
      ∃ i < w.length, ∃ y, upper ψ (w.take i) x y ∧ lower ψ (w.take i) z y))

private def applySignature : Signature m → State m → State m
  | (u, l, b, t, r), s =>
    ⟨Finset.univ.filter (fun y => ∃ x ∈ s.U, (x, y) ∈ u),
     Finset.univ.filter (fun y => ∃ x ∈ s.L, (x, y) ∈ l),
     s.b || decide ((∃ x ∈ s.U, x ∈ b) ∨
       (∃ x ∈ s.L, x ∈ t) ∨ ∃ x ∈ s.U, ∃ y ∈ s.L, (x, y) ∈ r)⟩

private theorem signature_eval (ψ : Constraint n m) (X Y : V m) (w : List (Fin n)) (s : State m) :
    applySignature (signature ψ w) s = (reader ψ X Y).evalFrom s w := by
  classical
  have imgs := images ψ X Y s
  have eqU : (applySignature (signature ψ w) s).U = ((reader ψ X Y).evalFrom s w).U := by
    ext y; simp [applySignature, signature, (imgs w).1]
  have eqL : (applySignature (signature ψ w) s).L = ((reader ψ X Y).evalFrom s w).L := by
    ext y; simp [applySignature, signature, (imgs w).2]
  have eqB : (applySignature (signature ψ w) s).b = ((reader ψ X Y).evalFrom s w).b := by
    apply Bool.eq_iff_iff.mpr
    rw [latch]
    simp only [applySignature, signature, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, Ready]
    simp_rw [(imgs _).1, (imgs _).2]
    apply or_congr Iff.rfl
    constructor
    · rintro (⟨x, hx, i, hi, y, hy, hw⟩ | ⟨x, hx, i, hi, y, hy, hw⟩ |
        ⟨x, hx, z, hz, i, hi, y, hu, hl⟩)
      · exact ⟨i, hi, Or.inl ⟨y, ⟨x, hx, hw⟩, hy⟩⟩
      · exact ⟨i, hi, Or.inr (Or.inl ⟨y, ⟨x, hx, hw⟩, hy⟩)⟩
      · exact ⟨i, hi, Or.inr (Or.inr ⟨y, ⟨x, hx, hu⟩, z, hz, hl⟩)⟩
    · rintro ⟨i, hi, h⟩
      rcases h with ⟨y, ⟨x, hx, hw⟩, hy⟩ | ⟨y, ⟨x, hx, hw⟩, hy⟩ |
        ⟨y, ⟨x, hx, hu⟩, z, hz, hl⟩
      · exact Or.inl ⟨x, hx, i, hi, y, hy, hw⟩
      · exact Or.inr (Or.inl ⟨x, hx, i, hi, y, hy, hw⟩)
      · exact Or.inr (Or.inr ⟨x, hx, z, hz, i, hi, y, hu, hl⟩)
  exact (State.equiv m).injective (Prod.ext eqU (Prod.ext eqL eqB))

/-- The label reader on `m` variables induces at most `2 ^ (3 * m ^ 2 + 2 * m)` word actions on
all input masks and both latch values. -/
theorem reader_actionBound (ψ : Constraint n m) (X Y : V m) (R : State m → State m → Prop)
    (T : Set (State m)) : ActionBound (ofReader (reader ψ X Y) R T) (2 ^ (3 * m ^ 2 + 2 * m)) := by
  classical
  refine ⟨(Finset.univ : Finset (Signature m)).image applySignature,
    Finset.card_image_le.trans ?_, ?_⟩
  · simp only [Signature, Finset.card_univ, Fintype.card_prod,
      Fintype.card_finset, Fintype.card_fin]
    simp only [← pow_add]
    exact le_of_eq (congrArg (2 ^ ·) (by ring))
  · intro w
    exact Finset.mem_image.mpr
      ⟨signature ψ w, Finset.mem_univ _, funext (signature_eval ψ X Y w)⟩

end DeciNSSE.Shortening
