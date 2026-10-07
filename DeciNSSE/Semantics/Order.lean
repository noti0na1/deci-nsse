import DeciNSSE.Semantics.Normalisation

/-! # The variance order

Labels at shared paths are compared in the direction of accumulated polarity.
Constructor comparison reverses precisely the contravariant child inequalities;
the covariant order remains the default order instance.
-/

namespace DeciNSSE
open DeciNSSE.Tree
variable {n : ℕ}

/-- Compare symbols on shared paths with their accumulated variance. -/
def Tree.Le (c : Fin n → Bool) (t u : Tree n) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → if polarity c π then b ≤ a else a ≤ b

/-- Variance order agrees with covariant order after normalisation. -/
theorem treeLe_iff_normalize (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ Tree.normalize c false t ≤ Tree.normalize c false u := by
  constructor
  · intro h π a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    simpa using (Sym.leP_iff_flip (polarity c π) a' b').mp (h π a' b' ha' hb')
  · intro h π a b ha hb
    apply (Sym.leP_iff_flip (polarity c π) a b).mpr
    exact h π _ _ (by simp [ha]) (by simp [hb])

@[simp] theorem treeLe_false_iff_le (t u : Tree n) :
    Tree.Le (fun _ => false) t u ↔ t ≤ u := by rw [treeLe_iff_normalize]; simp

/-- Every tree is below itself for every variance. -/
theorem treeLe_refl (c : Fin n → Bool) (t : Tree n) : Tree.Le c t t :=
  (treeLe_iff_normalize c t t).mpr le_rfl

/-- Mutual variance subtyping identifies trees. -/
theorem treeLe_antisymm {c : Fin n → Bool} {t u : Tree n}
    (htu : Tree.Le c t u) (hut : Tree.Le c u t) : t = u :=
  normalize_injective c false (_root_.le_antisymm ((treeLe_iff_normalize c t u).mp htu)
    ((treeLe_iff_normalize c u t).mp hut))

theorem normalize_le_normalize_iff (c : Fin n → Bool) (p : Bool) (t u : Tree n) :
    Tree.normalize c p t ≤ Tree.normalize c p u ↔ if p then Tree.Le c u t else Tree.Le c t u := by
  cases p <;> simp [treeLe_iff_normalize]

@[simp] theorem bot_treeLe (c : Fin n → Bool) (t : Tree n) : Tree.Le c bot t := by
  rw [treeLe_iff_normalize]; simp
@[simp] theorem treeLe_top (c : Fin n → Bool) (t : Tree n) : Tree.Le c t top := by
  rw [treeLe_iff_normalize]; simp
@[simp] theorem treeLe_bot_iff (c : Fin n → Bool) (t : Tree n) : Tree.Le c t bot ↔ t = bot :=
  ⟨fun h => treeLe_antisymm h (bot_treeLe c t), fun h => h ▸ treeLe_refl c bot⟩
@[simp] theorem top_treeLe_iff (c : Fin n → Bool) (t : Tree n) : Tree.Le c top t ↔ t = top :=
  ⟨fun h => treeLe_antisymm (treeLe_top c t) h, fun h => h ▸ treeLe_refl c top⟩

@[simp] theorem node_treeLe_node_iff (c : Fin n → Bool) (a b : Fin n → Tree n) :
    Tree.Le c (node a) (node b) ↔ ∀ i, if c i then Tree.Le c (b i) (a i) else Tree.Le c (a i) (b i) := by
  rw [treeLe_iff_normalize]
  simp only [normalize_node, Bool.false_xor, node_le_node_iff, normalize_le_normalize_iff]

/-- The variance order is transitive. -/
theorem treeLe_trans {c : Fin n → Bool} {t u v : Tree n}
    (htu : Tree.Le c t u) (huv : Tree.Le c u v) : Tree.Le c t v :=
  (treeLe_iff_normalize c t v).mpr (_root_.le_trans ((treeLe_iff_normalize c t u).mp htu)
    ((treeLe_iff_normalize c u v).mp huv))

/-- A partial order value, deliberately not an instance. -/
@[instance_reducible] def variancePartialOrder (c : Fin n → Bool) : PartialOrder (Tree n) where
  le := Tree.Le c
  lt t u := Tree.Le c t u ∧ ¬ Tree.Le c u t
  lt_iff_le_not_ge := fun _ _ => Iff.rfl
  le_refl := treeLe_refl c
  le_trans := fun _ _ _ => treeLe_trans
  le_antisymm := fun _ _ => treeLe_antisymm

/-- Variance subtyping unfolds into bottom, top and oriented child comparisons. -/
theorem treeLe_iff_root_cases (c : Fin n → Bool) (t u : Tree n) :
    Tree.Le c t u ↔ t = bot ∨ u = top ∨
      ∃ a b, t = node a ∧ u = node b ∧
        ∀ i, if c i then Tree.Le c (b i) (a i) else Tree.Le c (a i) (b i) := by
  constructor
  · intro h
    rcases t.eq_bot_or_eq_top_or_node with ht | ht | ⟨a, rfl⟩
    · exact Or.inl ht
    · subst t; exact Or.inr (Or.inl ((top_treeLe_iff c u).mp h))
    · rcases u.eq_bot_or_eq_top_or_node with hu | hu | ⟨b, rfl⟩
      · subst u; exact False.elim (node_ne_bot a ((treeLe_bot_iff c _).mp h))
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, (node_treeLe_node_iff ..).mp h⟩)
  · rintro (rfl | rfl | ⟨a, b, rfl, rfl, h⟩)
    · exact bot_treeLe c u
    · exact treeLe_top c t
    · exact (node_treeLe_node_iff ..).mpr h

end DeciNSSE
