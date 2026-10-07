import DeciNSSE.Semantics.Safety

/-! # Median of trees

Pointwise median of extended labels, pruned below extreme labels, defines a
monotone tree operation that commutes with duality.
-/

namespace DeciNSSE

open DeciNSSE.Tree

variable {n : ℕ}

/-- Read the root of the leaf-freezing trace: the label at `w`, or the first leaf
above `w` when `w` leaves the domain. -/
def Tree.trace (t : Tree n) (w : List (Fin n)) : Sym :=
  ((Safety.trace t w).fn []).getD .f

@[simp] theorem trace_bot (w : List (Fin n)) : Tree.trace Tree.bot w = .bot := by simp [Tree.trace]
@[simp] theorem trace_top (w : List (Fin n)) : Tree.trace Tree.top w = .top := by simp [Tree.trace]
@[simp] theorem trace_node_nil (a : Fin n → Tree n) : Tree.trace (Tree.node a) [] = .f := rfl
@[simp] theorem trace_node_cons (a : Fin n → Tree n) (i : Fin n) (w : List (Fin n)) :
    Tree.trace (Tree.node a) (i :: w) = Tree.trace (a i) w := by
  simp [Tree.trace]

theorem trace_step (t : Tree n) (w : List (Fin n)) (i : Fin n) :
    Tree.trace t (w ++ [i]) = (t.fn (w ++ [i])).getD (Tree.trace t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simp [Tree.trace]
  | cons j w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp
    · simp
    · simpa using ih (t := a j)

@[simp] theorem covPrefTop_iff_trace (w : List (Fin n)) (t : Tree n) :
    covPrefTop w t ↔ Tree.trace t w = .top := by
  change Safety.HasLabel t w .top ↔ _
  rw [← Safety.trace_eq_top_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [Tree.trace, h]

@[simp] theorem covPrefBot_iff_trace (w : List (Fin n)) (t : Tree n) :
    covPrefBot w t ↔ Tree.trace t w = .bot := by
  change Safety.HasLabel t w .bot ↔ _
  rw [← Safety.trace_eq_bot_iff]
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with h | h | ⟨a, h⟩ <;>
    simp [Tree.trace, h]

/-- The covariant order is the pointwise order of constant leaf extensions. -/
theorem le_iff_trace (t u : Tree n) : t ≤ u ↔ ∀ w, Tree.trace t w ≤ Tree.trace u w := by
  rw [cov_le_iff_safe]
  simp only [covPrefTop_iff_trace, covPrefBot_iff_trace]
  have hs (a b : Sym) : ((a = .top → b = .top) ∧ (b = .bot → a = .bot)) ↔ a ≤ b := by
    cases a <;> cases b <;> decide
  simp only [hs]

theorem trace_injective : Function.Injective (@Tree.trace n) := by
  intro a b h
  apply _root_.le_antisymm <;> apply (le_iff_trace _ _).mpr <;> intro w <;> rw [h]

/-- Extreme labels remain constant on every descendant. -/
theorem trace_absorb (t : Tree n) (w v : List (Fin n)) (h : Tree.trace t w ≠ .f) :
    Tree.trace t (w ++ v) = Tree.trace t w := by
  rcases (Safety.trace t w).eq_bot_or_eq_top_or_node with ht | ht | ⟨a, ht⟩
  · simp [Tree.trace, Safety.trace_append, ht]
  · simp [Tree.trace, Safety.trace_append, ht]
  · simp [Tree.trace, ht] at h

@[simp] theorem trace_dual (t : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.dual t) w = Sym.flip true (Tree.trace t w) := by
  induction w generalizing t with
  | nil =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩ <;> simp [Sym.flip]
  | cons i w ih =>
    rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
    · simp [Sym.flip]
    · simp [Sym.flip]
    · simp [ih]

/-- The median in the three-element linear order. -/
def medianSym (a b c : Sym) : Sym := max (min a b) (min (max a b) c)

theorem medianSym_mono {a a' b b' c c' : Sym}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    medianSym a b c ≤ medianSym a' b' c' :=
  max_le_max (min_le_min ha hb) (min_le_min (max_le_max ha hb) hc)

@[simp] theorem medianSym_self (a c : Sym) : medianSym a a c = a := by
  cases a <;> cases c <;> decide

theorem medianSym_swap (a b c : Sym) : medianSym a b c = medianSym b a c := by
  simp [medianSym, min_comm, max_comm]

theorem medianSym_flip (a b c : Sym) :
    Sym.flip true (medianSym a b c) =
      medianSym (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- An extreme median needs two equal extreme inputs, so absorption is preserved. -/
theorem medianSym_absorb (a b c a' b' c' : Sym)
    (ha : a ≠ .f → a' = a) (hb : b ≠ .f → b' = b) (hc : c ≠ .f → c' = c)
    (h : medianSym a b c ≠ .f) : medianSym a' b' c' = medianSym a b c := by
  cases a <;> cases b <;> cases c <;> simp_all [medianSym]

/-- A path survives pruning when every proper prefix carries the constructor. -/
def PruneLive (labels : List (Fin n) → Sym) (π : List (Fin n)) : Prop :=
  ∀ τ, τ <+: π → τ ≠ π → labels τ = .f

@[simp] theorem pruneLive_nil (labels : List (Fin n) → Sym) : PruneLive labels [] := by
  intro τ hp hn
  exact False.elim (hn (List.prefix_nil.mp hp))

theorem pruneLive_append_singleton (labels : List (Fin n) → Sym)
    (π : List (Fin n)) (i : Fin n) :
    PruneLive labels (π ++ [i]) ↔ PruneLive labels π ∧ labels π = .f := by
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

/-- Prune at the first extreme label. -/
noncomputable def prune (labels : List (Fin n) → Sym) : Tree n := by
  classical
  exact {
    fn := fun w => if PruneLive labels w then some (labels w) else none
    wf := by
      constructor
      · simp
      · intro w i
        simp only [pruneLive_append_singleton]
        by_cases h : PruneLive labels w <;> simp [h]
  }

/-- Pruning is a right inverse of constant extension on absorbing label maps. -/
theorem trace_prune (labels : List (Fin n) → Sym)
    (h : ∀ w v, labels w ≠ .f → labels (w ++ v) = labels w) :
    Tree.trace (prune labels) = labels := by
  classical
  funext w
  induction w using List.reverseRecOn with
  | nil => simp [Tree.trace, prune]
  | append_singleton w i ih =>
    rw [trace_step, ih]
    by_cases ha : PruneLive labels (w ++ [i])
    · simp [prune, ha]
    · simp only [prune, ite_eq_right ha, Option.getD_none]
      by_cases hw : labels w = .f
      · obtain ⟨v, hp, hn, hv⟩ := by
          simpa only [PruneLive, not_forall, Classical.not_imp] using ha
        have hvw : v.IsPrefix w := List.prefix_of_prefix_length_le hp
          (List.prefix_append _ _) (by
            have hle := hp.length_le
            have hne : v.length ≠ (w ++ [i]).length := fun he => hn (hp.eq_of_length he)
            simp only [List.length_append, List.length_singleton] at hle hne
            omega)
        obtain ⟨s, rfl⟩ := hvw
        exact False.elim (hv ((h v s hv).symm.trans hw))
      · exact (h w [i] hw).symm

/-- The label is the pointwise median; its domain consists of constructor prefixes. -/
noncomputable def Tree.median (a b c : Tree n) : Tree n :=
  prune (fun w => medianSym (Tree.trace a w) (Tree.trace b w) (Tree.trace c w))

/-- The median is pointwise on constant extensions. -/
@[simp] theorem trace_median (a b c : Tree n) (w : List (Fin n)) :
    Tree.trace (Tree.median a b c) w = medianSym (Tree.trace a w) (Tree.trace b w) (Tree.trace c w) := by
  apply congrFun (trace_prune _ _) w
  intro v s h
  exact medianSym_absorb _ _ _ _ _ _ (trace_absorb a v s) (trace_absorb b v s)
    (trace_absorb c v s) h

theorem median_mono {a a' b b' c c' : Tree n} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    Tree.median a b c ≤ Tree.median a' b' c' := by
  apply (le_iff_trace _ _).mpr
  intro w
  simp only [trace_median]
  exact medianSym_mono ((le_iff_trace _ _).mp ha w) ((le_iff_trace _ _).mp hb w)
    ((le_iff_trace _ _).mp hc w)

@[simp] theorem median_self (a c : Tree n) : Tree.median a a c = a := by
  apply trace_injective; funext w; simp

theorem median_swap (a b c : Tree n) : Tree.median a b c = Tree.median b a c := by
  apply trace_injective; funext w; simp [medianSym_swap]

/-- The median commutes with the n-ary constructor, child by child. -/
theorem median_node (a b c : Fin n → Tree n) :
    Tree.median (Tree.node a) (Tree.node b) (Tree.node c) =
      Tree.node (fun i => Tree.median (a i) (b i) (c i)) := by
  apply trace_injective; funext w
  cases w with
  | nil => simp
  | cons i w => simp

theorem dual_median (a b c : Tree n) : Tree.dual (Tree.median a b c) = Tree.median (Tree.dual a) (Tree.dual b) (Tree.dual c) := by
  apply trace_injective; funext w; simp [medianSym_flip]

end DeciNSSE
