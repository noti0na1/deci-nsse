import DeciNSSE.Holes.Supports

/-! # Boundary pairs through hierarchy expansion

Ordered nonterminal boundary pairs descend from upper boundary pairs or endpoint
pairs. Endpoint pairs have a fixed final letter, giving a linear counting bound.
-/

set_option autoImplicit false

namespace DeciNSSE.BoundaryPairs
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy DeciNSSE.Supports
open scoped List

section Mismatch
variable {Γ : Type*} [DecidableEq Γ]

/-- The letter of the first list at the first mismatch of two lists (read from the left);
`none` if the first list is a prefix of the second. -/
def fmis : List Γ → List Γ → Option Γ
  | [], _ => none
  | a :: _, [] => some a
  | a :: A, b :: B => if a = b then fmis A B else some a

theorem fmis_append_left : ∀ (Y A B : List Γ), fmis (Y ++ A) (Y ++ B) = fmis A B
  | [], _, _ => rfl
  | y :: Y, A, B => by simp [fmis, fmis_append_left Y A B]

theorem fmis_self (A : List Γ) : fmis A A = none := by
  have := fmis_append_left A [] []
  simp only [List.append_nil] at this
  rw [this]; rfl

theorem fmis_getD_of_ne (ℓ : Γ) : ∀ (A B : List Γ), A.head?.getD ℓ ≠ B.head?.getD ℓ →
    (fmis A B).getD ℓ = A.head?.getD ℓ
  | [], _, _ => rfl
  | a :: _, [], _ => rfl
  | a :: _, b :: _, h => by
      have hab : a ≠ b := by simpa using h
      simp [fmis, hab]

/-- The right-aligned mismatch of two packet bodies, using the marker for a missing letter. -/
def mu (ℓ : Γ) (X Y : List Γ) : Γ × Γ :=
  ((fmis X.reverse Y.reverse).getD ℓ, (fmis Y.reverse X.reverse).getD ℓ)

theorem mu_self (ℓ : Γ) (X : List Γ) : mu ℓ X X = (ℓ, ℓ) := by
  simp [mu, fmis_self]

theorem mu_nil_left (ℓ : Γ) (Y : List Γ) : (mu ℓ [] Y).1 = ℓ := by
  simp [mu, fmis]

theorem mu_nil_right (ℓ : Γ) (X : List Γ) : (mu ℓ X []).2 = ℓ := by
  simp [mu, fmis]

end Mismatch

section BP
variable {β : Type*}

/-- `(x, y)` is a **boundary pair** of `u`: the ordered boundary letters `(u[s-1], u[e-1])` of a
nonterminal left-maximal comparison `(s, e)`. -/
def IsBP (u : List β) (x y : β) : Prop :=
  ∃ s e, IsLeftMax u s e ∧ e < u.length ∧ u[s - 1]? = some x ∧ u[e - 1]? = some y

end BP

section ExpandLetters
variable {Γ : Type*}

/-- The letter before the cut `P_k + |x|` (with `v[k] = x y`, the cut `≥ 1`) is the last letter
of `x`, or the marker `ℓ` if `x = ε`. -/
theorem getElem?_expand_before (ℓ : Γ) (v : List (List Γ)) {k : ℕ} (hk : k < v.length)
    {x y : List Γ} (hxy : v[k] = x ++ y) (h1 : 1 ≤ cutP ℓ v k + x.length) :
    (expand ℓ v)[cutP ℓ v k + x.length - 1]? = some (x.reverse.head?.getD ℓ) := by
  rcases List.eq_nil_or_concat x with rfl | ⟨x', a, rfl⟩
  · -- the cut is a block start: the previous letter is the marker ending block `k - 1`
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
      rcases k with _ | k'
      · simp [cutP] at h1
      · exact ⟨k', rfl⟩
    have hc := cutP_succ ℓ v k' (by omega)
    simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.head?_nil,
      Option.getD_none]
    rw [show cutP ℓ v (k' + 1) - 1 = cutP ℓ v k' + v[k'].length by omega]
    exact getElem?_expand_marker ℓ v (by omega)
  · simp only [List.concat_eq_append] at hxy h1 ⊢
    have hp : x'.length < v[k].length := by rw [hxy]; simp
    rw [show cutP ℓ v k + (x' ++ [a]).length - 1 = cutP ℓ v k + x'.length by simp,
      getElem?_expand_cutP ℓ v hk hp, hxy]
    simp

end ExpandLetters

section BPExpand
variable {Γ : Type*} [DecidableEq Γ]

/-- Every nonterminal lower boundary pair is the mismatch of two distinct upper
letters whose following cuts form a comparison, possibly at the endpoint. -/
theorem bp_expand {ℓ : Γ} {v : List (List Γ)} (hv : ∀ X ∈ v, ℓ ∉ X) {x y : Γ}
    (h : IsBP (expand ℓ v) x y) :
    ∃ ks ke, ∃ (hks : ks < v.length) (hke : ke < v.length), ks < ke ∧ v[ks] ≠ v[ke] ∧
      IsComp v (ks + 1) (ke + 1) ∧ mu ℓ v[ks] v[ke] = (x, y) := by
  obtain ⟨s, e, ⟨⟨hse, -, hc⟩, hs1, hne⟩, he, hx, hy⟩ := h
  obtain ⟨ks, ke, hks, hke, hlt, xs, xe, z, h1, h2, rfl, rfl, hcv⟩ :=
    (alignment ℓ v hv hse he).mp hc
  have lx := getElem?_expand_before ℓ v hks h1 hs1
  have ly := getElem?_expand_before ℓ v hke h2 (by omega)
  rw [hx, Option.some.injEq] at lx
  rw [hy, Option.some.injEq] at ly
  have hxy : x ≠ y := by
    intro h'; apply hne; rw [hx, hy, h']
  have hmu : mu ℓ v[ks] v[ke] = (x, y) := by
    simp only [mu, h1, h2, List.reverse_append, fmis_append_left]
    rw [fmis_getD_of_ne ℓ _ _ (by rw [← lx, ← ly]; exact hxy),
      fmis_getD_of_ne ℓ _ _ (by rw [← lx, ← ly]; exact hxy.symm), lx, ly]
  refine ⟨ks, ke, hks, hke, hlt, ?_, ⟨by omega, by omega, hcv⟩, hmu⟩
  intro heq
  rw [heq, mu_self, Prod.mk.injEq] at hmu
  exact hxy (hmu.1.symm.trans hmu.2)

end BPExpand

section FinitePairs
variable {Γ : Type*}

/-- The ordered nonterminal boundary pairs of a word. -/
noncomputable def boundaryPairs (v : List Γ) : Finset (Γ × Γ) := by
  classical
  exact (v.toFinset ×ˢ v.toFinset).filter (fun p => IsBP v p.1 p.2)

/-- The ordered boundary pairs of comparisons ending at the final cut. -/
noncomputable def endpointPairs (v : List Γ) : Finset (Γ × Γ) := by
  classical
  exact (v.toFinset ×ˢ v.toFinset).filter (fun p =>
    p.1 ≠ p.2 ∧ ∃ s, IsLeftMax v s v.length ∧
      v[s - 1]? = some p.1 ∧ v[v.length - 1]? = some p.2)

theorem IsBP.mem {v : List Γ} {x y : Γ} (h : IsBP v x y) : x ∈ v ∧ y ∈ v := by
  obtain ⟨s, e, _, _, hx, hy⟩ := h
  exact ⟨List.mem_of_getElem? hx, List.mem_of_getElem? hy⟩

theorem IsBP.ne {v : List Γ} {x y : Γ} (h : IsBP v x y) : x ≠ y := by
  obtain ⟨s, e, hlm, _, hx, hy⟩ := h
  intro heq
  exact hlm.2.2 (by rw [hx, hy, heq])

@[simp] theorem mem_boundaryPairs {v : List Γ} {p : Γ × Γ} :
    p ∈ boundaryPairs v ↔ IsBP v p.1 p.2 := by
  classical
  simp only [boundaryPairs, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
  exact ⟨And.right, fun h => ⟨h.mem, h⟩⟩

@[simp] theorem mem_endpointPairs {v : List Γ} {p : Γ × Γ} :
    p ∈ endpointPairs v ↔ p.1 ≠ p.2 ∧ ∃ s, IsLeftMax v s v.length ∧
      v[s - 1]? = some p.1 ∧ v[v.length - 1]? = some p.2 := by
  classical
  simp only [endpointPairs, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨_, s, _, hx, hy⟩ := h
  exact ⟨List.mem_of_getElem? hx, List.mem_of_getElem? hy⟩

/-- Each nonterminal co-alignment is represented by an ordered boundary pair. -/
theorem coAlignedNT_iff {v : List Γ} {x y : Γ} :
    CoAlignedNT v x y ↔ (x, y) ∈ boundaryPairs v ∨ (y, x) ∈ boundaryPairs v := by
  simp only [mem_boundaryPairs]
  constructor
  · rintro ⟨_, s, e, hlm, he, h | h⟩
    · exact Or.inl ⟨s, e, hlm, he, h⟩
    · exact Or.inr ⟨s, e, hlm, he, h⟩
  · rintro (h | h)
    · have hne := h.ne
      obtain ⟨s, e, hlm, he, hx, hy⟩ := h
      exact ⟨hne, s, e, hlm, he, Or.inl ⟨hx, hy⟩⟩
    · have hne := h.ne.symm
      obtain ⟨s, e, hlm, he, hx, hy⟩ := h
      exact ⟨hne, s, e, hlm, he, Or.inr ⟨hx, hy⟩⟩

/-- Expansion propagates every boundary pair, including pairs involving the marker. -/
theorem boundaryPairs_expand_subset [DecidableEq Γ] {ℓ : Γ} {v : List (List Γ)}
    (hv : ∀ X ∈ v, ℓ ∉ X) :
    boundaryPairs (expand ℓ v) ⊆
      (boundaryPairs v ∪ endpointPairs v).image (fun p => mu ℓ p.1 p.2) := by
  classical
  rintro ⟨x, y⟩ h
  obtain ⟨ks, ke, hks, hke, hlt, hne, hcomp, hmu⟩ := bp_expand hv (mem_boundaryPairs.mp h)
  have hlm : IsLeftMax v (ks + 1) (ke + 1) := by
    refine ⟨hcomp, by omega, ?_⟩
    simpa only [Nat.add_sub_cancel, List.getElem?_eq_getElem hks,
      List.getElem?_eq_getElem hke, ne_eq, Option.some.injEq] using hne
  refine Finset.mem_image.mpr ⟨(v[ks], v[ke]), Finset.mem_union.mpr ?_, hmu⟩
  rcases Nat.lt_or_ge (ke + 1) v.length with he | he
  · left
    exact mem_boundaryPairs.mpr ⟨ks + 1, ke + 1, hlm, he, by simp, by simp⟩
  · right
    have heq : ke + 1 = v.length := by omega
    apply mem_endpointPairs.mpr
    refine ⟨hne, ks + 1, heq ▸ hlm, by simp, ?_⟩
    rw [← heq]
    simp

/-- Endpoint pairs inject into the alphabet with its final letter removed. -/
theorem card_endpointPairs_le [DecidableEq Γ] {v : List Γ} (hv : v ≠ []) :
    (endpointPairs v).card ≤ v.toFinset.card - 1 := by
  classical
  let z := v.getLast hv
  have hz : v[v.length - 1]? = some z := by
    rw [← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast hv]
  have hsub : endpointPairs v ⊆ (v.toFinset.erase z).image (fun x => (x, z)) := by
    intro p hp
    obtain ⟨hne, s, _, hx, hy⟩ := mem_endpointPairs.mp hp
    have heq : p.2 = z := Option.some.inj (hy.symm.trans hz)
    refine Finset.mem_image.mpr ⟨p.1, Finset.mem_erase.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa only [heq] using hne
    · exact List.mem_toFinset.mpr (List.mem_of_getElem? hx)
    · exact Prod.ext rfl heq.symm
  calc
    (endpointPairs v).card ≤ ((v.toFinset.erase z).image (fun x => (x, z))).card :=
      Finset.card_le_card hsub
    _ ≤ (v.toFinset.erase z).card := Finset.card_image_le
    _ = v.toFinset.card - 1 := Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.getLast_mem hv))

/-- A unary word has no nonterminal boundary pair. -/
theorem boundaryPairs_eq_empty_of_isUnary {v : List Γ} (hu : IsUnary v) :
    boundaryPairs v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := mem_boundaryPairs.mp hp
  exact h.ne (hu _ h.mem.1 _ h.mem.2)

end FinitePairs

section Hierarchy
variable {α : Type*} [DecidableEq α] [Inhabited α]

/-- One step of boundary propagation, in subtraction-free form. -/
theorem boundaryCount_step_add_one {w : List α} (hw : w ≠ []) (i : ℕ) :
    (boundaryPairs (hierOf w i)).card + 1 ≤
      (boundaryPairs (hierOf w (i + 1))).card + (hierOf w (i + 1)).toFinset.card := by
  classical
  have hsub := boundaryPairs_expand_subset (avoid_hierOf (w := w) i)
  rw [expand_hierOf hw i] at hsub
  have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
  have hu := Finset.card_union_le (boundaryPairs (hierOf w (i + 1)))
    (endpointPairs (hierOf w (i + 1)))
  have he := card_endpointPairs_le (hierOf_ne_nil hw (i + 1))
  have hp : 0 < (hierOf w (i + 1)).toFinset.card := by
    apply Finset.card_pos.mpr
    exact ⟨markOf w (i + 1), List.mem_toFinset.mpr (markOf_mem hw _)⟩
  omega

/-- The linear one-step boundary-count bound. -/
theorem boundaryCount_step {w : List α} (hw : w ≠ []) (i : ℕ) :
    (boundaryPairs (hierOf w i)).card ≤
      (boundaryPairs (hierOf w (i + 1))).card + (hierOf w (i + 1)).toFinset.card - 1 := by
  have := boundaryCount_step_add_one hw i
  omega

end Hierarchy
end DeciNSSE.BoundaryPairs
