import DeciNSSE.Holes.Basic

/-! # Expansion of block words

A word over the alphabet `List Γ` of blocks expands to a word over `Γ` by
terminating every block with a marker `ℓ`. The cuts `P_k` are the positions
after the first `k` blocks. Every position of an expansion lies in one block,
and its comparisons are aligned at block ends.

## Main declarations

- `expand`: `σ_ℓ(X_0 ⋯ X_{k-1}) = X_0 ℓ ⋯ X_{k-1} ℓ`, and `cutP`, its cuts.
- `pos_decomp`, `pos_lt`: the positions of an expansion, by block.
- `mark_prefix_iff`, `expand_prefix_iff`: prefix comparisons through markers.
- `alignment`: the comparisons of an expansion, by block.
- `mem_expand`, `map_inj_on`: list facts about maps and expansions.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open scoped List

section Expand
variable {Γ : Type*}

/-- `σ_ℓ(X_0 ⋯ X_{k-1}) = X_0 ℓ X_1 ℓ ⋯ X_{k-1} ℓ`. -/
def expand (ℓ : Γ) (v : List (List Γ)) : List Γ := v.flatMap (· ++ [ℓ])

/-- Expanding the empty block word gives the empty word. -/
@[simp] theorem expand_nil (ℓ : Γ) : expand ℓ [] = [] := rfl

/-- `σ_ℓ(X v) = X ℓ σ_ℓ(v)`. -/
@[simp] theorem expand_cons (ℓ : Γ) (X : List Γ) (v : List (List Γ)) :
    expand ℓ (X :: v) = X ++ ℓ :: expand ℓ v := by
  simp [expand]

/-- Expansion is a word morphism. -/
@[simp] theorem expand_append (ℓ : Γ) (v w : List (List Γ)) :
    expand ℓ (v ++ w) = expand ℓ v ++ expand ℓ w := by
  simp [expand]

/-- `σ_ℓ(v X) = σ_ℓ(v) X ℓ`. -/
theorem expand_snoc (ℓ : Γ) (v : List (List Γ)) (X : List Γ) :
    expand ℓ (v ++ [X]) = expand ℓ v ++ X ++ [ℓ] := by
  simp

/-- An expansion is empty only for the empty block word. -/
theorem expand_eq_nil {ℓ : Γ} {v : List (List Γ)} : expand ℓ v = [] ↔ v = [] := by
  cases v <;> simp

/-- The cut `P_k = |σ_ℓ(v[:k])|`. -/
def cutP (ℓ : Γ) (v : List (List Γ)) (k : ℕ) : ℕ := (expand ℓ (v.take k)).length

/-- Splitting an expansion at block `k`: `σ_ℓ(v) = σ_ℓ(v[:k]) X_k ℓ σ_ℓ(v[k+1:])`. -/
theorem expand_split (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    expand ℓ v = expand ℓ (v.take k) ++ (v[k] ++ ℓ :: expand ℓ (v.drop (k + 1))) := by
  have h := List.take_append_drop k v
  rw [List.drop_eq_getElem_cons hk] at h
  conv_lhs => rw [← h]
  rw [expand_append, expand_cons]

/-- `σ_ℓ(v[:k+1]) = σ_ℓ(v[:k]) X_k ℓ`. -/
theorem expand_take_succ (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    expand ℓ (v.take (k + 1)) = expand ℓ (v.take k) ++ v[k] ++ [ℓ] := by
  rw [List.take_succ_eq_append_getElem hk, expand_snoc]

/-- `P_{k+1} = P_k + |X_k| + 1`. -/
theorem cutP_succ (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    cutP ℓ v (k + 1) = cutP ℓ v k + v[k].length + 1 := by
  simp only [cutP, expand_take_succ ℓ v k hk, List.length_append, List.length_singleton]

/-- The length of an expansion is its last cut. -/
theorem length_expand (ℓ : Γ) (v : List (List Γ)) :
    (expand ℓ v).length = cutP ℓ v v.length := by
  simp [cutP]

/-- The cuts are monotone. -/
theorem cutP_mono (ℓ : Γ) (v : List (List Γ)) {i j : ℕ} (hij : i ≤ j) :
    cutP ℓ v i ≤ cutP ℓ v j := by
  obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := v) hij
  simp only [cutP, ← ht, expand_append, List.length_append]
  omega

/-- Every cut lies within the expansion. -/
theorem cutP_le_length (ℓ : Γ) (v : List (List Γ)) (k : ℕ) :
    cutP ℓ v k ≤ (expand ℓ v).length := by
  rw [length_expand]
  rcases Nat.lt_or_ge k v.length with h | h
  · exact cutP_mono ℓ v h.le
  · simp [cutP, List.take_of_length_le h]

/-- Words `y ++ a :: X` and `y' ++ a :: Y` with `a` in neither `y` nor `y'` compare
through their first `a`: `y = y'` and `X` is a prefix of `Y`. -/
theorem mark_prefix_iff {a : Γ} {X Y : List Γ} : ∀ {y y' : List Γ}, a ∉ y → a ∉ y' →
    (y ++ a :: X <+: y' ++ a :: Y ↔ y = y' ∧ X <+: Y)
  | [], [], _, _ => by simp
  | [], b :: y', _, hy' => by
      simp only [List.nil_append, List.cons_append, List.cons_prefix_cons, List.nil_eq,
        reduceCtorEq, false_and, iff_false, not_and]
      rintro rfl
      exact absurd (List.mem_cons_self) hy'
  | b :: y, [], hy, _ => by
      simp only [List.nil_append, List.cons_append, List.cons_prefix_cons, reduceCtorEq,
        false_and, iff_false, not_and]
      rintro rfl
      exact absurd (List.mem_cons_self) hy
  | b :: y, b' :: y', hy, hy' => by
      simp only [List.cons_append, List.cons_prefix_cons, List.cons.injEq]
      rw [mark_prefix_iff (fun h => hy (List.mem_cons_of_mem _ h))
        (fun h => hy' (List.mem_cons_of_mem _ h))]
      tauto

/-- Marker-terminated expansion preserves and reflects prefixes. -/
theorem expand_prefix_iff {ℓ : Γ} : ∀ {a b : List (List Γ)},
    (∀ X ∈ a, ℓ ∉ X) → (∀ X ∈ b, ℓ ∉ X) →
    (expand ℓ a <+: expand ℓ b ↔ a <+: b)
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | X :: a, Y :: b, ha, hb => by
      rw [expand_cons, expand_cons, mark_prefix_iff (ha X List.mem_cons_self)
        (hb Y List.mem_cons_self), List.cons_prefix_cons,
        expand_prefix_iff (fun Z hZ => ha Z (List.mem_cons_of_mem _ hZ))
          (fun Z hZ => hb Z (List.mem_cons_of_mem _ hZ))]

/-- The suffix at a position inside a block. -/
theorem drop_expand_at (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length)
    (x y : List Γ) (hxy : v[k] = x ++ y) :
    (expand ℓ v).drop (cutP ℓ v k + x.length) = y ++ ℓ :: expand ℓ (v.drop (k + 1)) := by
  have h : expand ℓ v = (expand ℓ (v.take k) ++ x) ++
      (y ++ ℓ :: expand ℓ (v.drop (k + 1))) := by
    rw [expand_split ℓ v k hk, hxy]
    simp
  rw [h]
  exact List.drop_left' (by simp [cutP])

/-- Every position `s < |σ_ℓ(v)|` lies in a block: `s = P_k + p` with `p ≤ |X_k|`. -/
theorem pos_decomp (ℓ : Γ) (v : List (List Γ)) {s : ℕ} (hs : s < (expand ℓ v).length) :
    ∃ k, ∃ hk : k < v.length, ∃ p, p ≤ v[k].length ∧ s = cutP ℓ v k + p := by
  induction v generalizing s with
  | nil => simp at hs
  | cons X v ih =>
    by_cases hsX : s ≤ X.length
    · exact ⟨0, by simp, s, by simpa using hsX, by simp [cutP]⟩
    · have hs' : s - (X.length + 1) < (expand ℓ v).length := by
        simp only [expand_cons, List.length_append, List.length_cons] at hs
        omega
      obtain ⟨k, hk, p, hp, hk'⟩ := ih hs'
      refine ⟨k + 1, by simp; omega, p, by simpa using hp, ?_⟩
      simp only [cutP, List.take_succ_cons, expand_cons, List.length_append,
        List.length_cons] at hk' ⊢
      omega

/-- The position `P_k + p` with `p ≤ |X_k|` lies inside the expansion. -/
theorem pos_lt (ℓ : Γ) (v : List (List Γ)) {k : ℕ} (hk : k < v.length) {p : ℕ}
    (hp : p ≤ v[k].length) : cutP ℓ v k + p < (expand ℓ v).length := by
  have h1 := cutP_succ ℓ v k hk
  have h2 := cutP_le_length ℓ v (k + 1)
  omega

/-- Alignment. For `s < e < |σ_ℓ(v)|` and letters
of `v` avoiding `ℓ`: `(s,e)` is a comparison of `σ_ℓ(v)` iff `s = P_{ks} + |xs|`,
`e = P_{ke} + |xe|` with `X_{ks} = xs y`, `X_{ke} = xe y` (a common suffix: equal distance
to the block ends) and `(ks+1, ke+1)` a comparison of `v`, `ks < ke`. -/
theorem alignment (ℓ : Γ) (v : List (List Γ)) (hv : ∀ X ∈ v, ℓ ∉ X) {s e : ℕ} (hse : s < e)
    (he : e < (expand ℓ v).length) :
    (expand ℓ v).drop e <+: (expand ℓ v).drop s ↔
      ∃ ks ke, ∃ (hks : ks < v.length) (hke : ke < v.length), ks < ke ∧
        ∃ xs xe y, v[ks] = xs ++ y ∧ v[ke] = xe ++ y ∧
          s = cutP ℓ v ks + xs.length ∧ e = cutP ℓ v ke + xe.length ∧
          v.drop (ke + 1) <+: v.drop (ks + 1) := by
  constructor
  · intro hc
    obtain ⟨ks, hks, ps, hps, rfl⟩ := pos_decomp ℓ v (by omega : s < (expand ℓ v).length)
    obtain ⟨ke, hke, pe, hpe, rfl⟩ := pos_decomp ℓ v he
    obtain ⟨xs, ys, hs, hxs⟩ : ∃ xs ys, v[ks] = xs ++ ys ∧ xs.length = ps :=
      ⟨v[ks].take ps, v[ks].drop ps, (List.take_append_drop _ _).symm, by simp [hps]⟩
    obtain ⟨xe, ye, hee, hxe⟩ : ∃ xe ye, v[ke] = xe ++ ye ∧ xe.length = pe :=
      ⟨v[ke].take pe, v[ke].drop pe, (List.take_append_drop _ _).symm, by simp [hpe]⟩
    rw [← hxs, ← hxe, drop_expand_at ℓ v ke hke xe ye hee,
      drop_expand_at ℓ v ks hks xs ys hs,
      mark_prefix_iff (fun h => hv _ (List.getElem_mem _) (hee ▸ List.mem_append_right _ h))
        (fun h => hv _ (List.getElem_mem _) (hs ▸ List.mem_append_right _ h)),
      expand_prefix_iff (fun X hX => hv X (List.mem_of_mem_drop hX))
        (fun X hX => hv X (List.mem_of_mem_drop hX))] at hc
    obtain ⟨rfl, hc⟩ := hc
    refine ⟨ks, ke, hks, hke, ?_, xs, xe, ye, hs, hee, by rw [hxs], by rw [hxe], hc⟩
    by_contra hlt
    have hm := cutP_mono ℓ v (show ke + 1 ≤ ks + 1 by omega)
    rw [cutP_succ ℓ v ke hke, cutP_succ ℓ v ks hks, hs, hee] at hm
    simp only [List.length_append] at hm
    omega
  · rintro ⟨ks, ke, hks, hke, -, xs, xe, y, hs, hee, rfl, rfl, hc⟩
    rw [drop_expand_at ℓ v ke hke xe y hee, drop_expand_at ℓ v ks hks xs y hs,
      List.prefix_append_right_inj, List.cons_prefix_cons]
    exact ⟨rfl, (expand_prefix_iff (fun X hX => hv X (List.mem_of_mem_drop hX))
      (fun X hX => hv X (List.mem_of_mem_drop hX))).mpr hc⟩

/-- The letters of `σ_ℓ(v)` are the letters of its blocks and the marker. -/
theorem mem_expand {ℓ a : Γ} {v : List (List Γ)} :
    a ∈ expand ℓ v ↔ ∃ X ∈ v, a ∈ X ++ [ℓ] := by
  simp [expand, List.mem_flatMap]

/-- A map injective on the letters of `S` is injective on the lists over `S`. -/
theorem map_inj_on {β γ : Type*} {f : β → γ} {S : List β}
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) :
    ∀ {X Y : List β}, (∀ a ∈ X, a ∈ S) → (∀ a ∈ Y, a ∈ S) → X.map f = Y.map f → X = Y
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: X, b :: Y, hX, hY, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf a (hX a List.mem_cons_self) b (hY b List.mem_cons_self) h.1,
        map_inj_on hf (fun c hc => hX c (List.mem_cons_of_mem _ hc))
          (fun c hc => hY c (List.mem_cons_of_mem _ hc)) h.2]

end Expand

end DeciNSSE.LetteredHierarchy
