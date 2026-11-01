import DeciNSSE.Holes.Desubstitution

/-! # Expansion of block words

A word over the alphabet `List Γ` of blocks expands to a word over `Γ` by
terminating every block with a marker `ℓ`. The cuts `P_k` are the positions
after the first `k` blocks. Every position of an expansion lies in one block,
and its comparisons are aligned at block ends.

## Main declarations

- `expand`: `σ_ℓ(X_0 ⋯ X_{k-1}) = X_0 ℓ ⋯ X_{k-1} ℓ`, and `cutP`, its cuts.
- `pos_decomp`, `pos_lt`: the positions of an expansion, by block.
- `alignment`: the comparisons of an expansion, by block.
- `mem_expand`, `prefix_map_inj`, `map_inj_on`: list facts about maps and
  expansions.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.Desubstitution
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

/-- The marker code whose bodies avoid the selected marker. -/
def mcode (ℓ : Γ) : MarkerCode Γ {X : List Γ // ℓ ∉ X} where
  mark := ℓ
  body := Subtype.val
  mark_not_mem c := c.2
  body_injective := Subtype.val_injective

/-- The marker code of `ℓ` encodes by expansion. -/
theorem mcode_enc (ℓ : Γ) (x : List {X : List Γ // ℓ ∉ X}) :
    (mcode ℓ).enc x = expand ℓ (x.map Subtype.val) := by
  induction x with
  | nil => rfl
  | cons X x ih =>
    rw [MarkerCode.enc_cons, ih, List.map_cons, expand_cons]
    simp [MarkerCode.code, mcode]

/-- The cuts of the marker code of `ℓ` are the cuts `P_k`. -/
theorem mcode_cut (ℓ : Γ) (x : List {X : List Γ // ℓ ∉ X}) (k : ℕ) :
    (mcode ℓ).cut x k = cutP ℓ (x.map Subtype.val) k := by
  simp [MarkerCode.cut, cutP, mcode_enc, List.map_take]

/-- A block word avoiding `ℓ` lifts to the alphabet of the marker code of `ℓ`. -/
theorem lift_avoid {ℓ : Γ} {v : List (List Γ)} (h : ∀ X ∈ v, ℓ ∉ X) :
    ∃ x : List {X : List Γ // ℓ ∉ X}, x.map Subtype.val = v :=
  ⟨v.attach.map fun X => ⟨X.1, h X.1 X.2⟩, by simp⟩

/-- An injective letter map preserves and reflects prefixes. -/
theorem prefix_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) {l₁ l₂ : List α} :
    l₁.map f <+: l₂.map f ↔ l₁ <+: l₂ := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  obtain ⟨l, hl, he⟩ := List.prefix_map_iff.mp h
  rw [List.map_inj_right (fun a b h => hf h)] at he
  exact he ▸ hl

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
  obtain ⟨x, rfl⟩ := lift_avoid hv
  rw [← mcode_enc] at he ⊢
  rw [(mcode ℓ).alignment x hse he]
  simp only [List.length_map, List.getElem_map, mcode_cut, ← List.map_drop,
    prefix_map_inj Subtype.val_injective]
  rfl

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
