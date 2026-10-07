import DeciNSSE.Holes.Basic

/-! # Marker codes and desubstitution

Marker-terminated blocks form a prefix code. Comparisons of expanded words
align at markers, allowing a hole to be described by block and endpoint
conditions in a derived reader.
-/

set_option autoImplicit false

namespace DeciNSSE.Desubstitution
open DeciNSSE.Holes
open scoped List

variable {α γ Q : Type*}

/-- A marker code `σ(c) = β_c #`: the marker `#` occurs in no body `β_c`, and the
bodies are pairwise distinct. -/
structure MarkerCode (α γ : Type*) where

  mark : α

  body : γ → List α
  mark_not_mem : ∀ c, mark ∉ body c
  body_injective : Function.Injective body

/-- Words of the form `y # X` with `# ∉ y` compare through their first marker. -/
theorem mark_prefix_iff {a : α} {X Y : List α} : ∀ {y y' : List α}, a ∉ y → a ∉ y' →
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

namespace MarkerCode
variable (C : MarkerCode α γ)

/-- The codeword `σ(c) = β_c #`. -/
def code (c : γ) : List α := C.body c ++ [C.mark]

/-- `σ(v)`. -/
def enc (v : List γ) : List α := v.flatMap C.code

/-- The cut `P_k = |σ(v[:k])|`. -/
def cut (v : List γ) (k : ℕ) : ℕ := (C.enc (v.take k)).length

@[simp] theorem enc_nil : C.enc [] = [] := rfl
@[simp] theorem enc_cons (c : γ) (v : List γ) : C.enc (c :: v) = C.code c ++ C.enc v := by
  simp [enc]
@[simp] theorem enc_append (v w : List γ) : C.enc (v ++ w) = C.enc v ++ C.enc w := by
  simp [enc]
@[simp] theorem enc_singleton (c : γ) : C.enc [c] = C.code c := by simp [enc]

theorem length_code (c : γ) : (C.code c).length = (C.body c).length + 1 := by simp [code]

theorem mark_not_mem_of_append {c : γ} {x y : List α} (h : C.body c = x ++ y) :
    C.mark ∉ y := fun hm => C.mark_not_mem c (h ▸ List.mem_append_right x hm)

/-- `σ` is a prefix code: prefix comparisons are preserved and reflected. -/
theorem enc_prefix_iff : ∀ (v w : List γ), C.enc v <+: C.enc w ↔ v <+: w
  | [], w => by simp
  | c :: v, [] => by simp [code]
  | c :: v, d :: w => by
      rw [enc_cons, enc_cons, code, code, List.append_assoc, List.append_assoc,
        List.singleton_append, List.singleton_append,
        mark_prefix_iff (C.mark_not_mem c) (C.mark_not_mem d), List.cons_prefix_cons,
        enc_prefix_iff v w]
      constructor
      · rintro ⟨h, h'⟩; exact ⟨C.body_injective h, h'⟩
      · rintro ⟨rfl, h'⟩; exact ⟨rfl, h'⟩

/-- `σ(v) = σ(v[:k]) · β_{v[k]} · # · σ(v[k+1:])`. -/
theorem enc_split (v : List γ) (k : ℕ) (hk : k < v.length) :
    C.enc v = C.enc (v.take k) ++ (C.body v[k] ++ C.mark :: C.enc (v.drop (k + 1))) := by
  conv_lhs => rw [← List.take_append_drop k v, List.drop_eq_getElem_cons hk]
  rw [enc_append, enc_cons, code, List.append_assoc, List.singleton_append]

theorem enc_split_xy (v : List γ) (k : ℕ) (hk : k < v.length) (x y : List α)
    (hxy : C.body v[k] = x ++ y) :
    C.enc v = (C.enc (v.take k) ++ x) ++ (y ++ C.mark :: C.enc (v.drop (k + 1))) := by
  rw [C.enc_split v k hk, hxy]
  simp

/-- The suffix of `σ(v)` from a position inside block `k+1`. -/
theorem drop_at (v : List γ) (k : ℕ) (hk : k < v.length) (x y : List α)
    (hxy : C.body v[k] = x ++ y) :
    (C.enc v).drop (C.cut v k + x.length) = y ++ C.mark :: C.enc (v.drop (k + 1)) := by
  rw [C.enc_split_xy v k hk x y hxy]
  exact List.drop_left' (by simp [cut])

theorem cut_succ (v : List γ) (k : ℕ) (hk : k < v.length) :
    C.cut v (k + 1) = C.cut v k + (C.body v[k]).length + 1 := by
  simp only [cut, List.take_succ_eq_append_getElem hk, enc_append, enc_singleton,
    List.length_append, length_code]
  omega

theorem cut_mono (v : List γ) {i j : ℕ} (hij : i ≤ j) : C.cut v i ≤ C.cut v j := by
  obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := v) hij
  simp only [cut, ← ht, enc_append, List.length_append]
  omega

/-- Every position `s < |σ(v)|` lies in a block: `s = P_k + |x|` with `β_{v[k]} = x y`. -/
theorem pos_decomp : ∀ (v : List γ) (s : ℕ), s < (C.enc v).length →
    ∃ k, ∃ hk : k < v.length, ∃ x y, C.body v[k] = x ++ y ∧ s = C.cut v k + x.length
  | [], s, hs => by simp at hs
  | c :: v, s, hs => by
      by_cases hsc : s ≤ (C.body c).length
      · refine ⟨0, by simp, (C.body c).take s, (C.body c).drop s, by simp, ?_⟩
        simp [cut, Nat.min_eq_left hsc]
      · have hs' : s - ((C.body c).length + 1) < (C.enc v).length := by
          simp only [enc_cons, List.length_append, length_code] at hs
          omega
        obtain ⟨k, hk, x, y, hxy, hk'⟩ := pos_decomp v _ hs'
        refine ⟨k + 1, by simp; omega, x, y, by simpa using hxy, ?_⟩
        simp only [cut, List.take_succ_cons, enc_cons, List.length_append, length_code] at hk' ⊢
        omega

/-- Let `s < e < |σ(v)|`. Then `(s,e)` is a comparison of
`σ(v)` iff it is marker-aligned: `s = P_{ks} + |xs|` and `e = P_{ke} + |xe|` with
`β_{v[ks]} = xs y`, `β_{v[ke]} = xe y` (the same distance `|y| + 1` from the ends of
blocks `ks+1`, `ke+1`, which share their suffix `y #`), and `(ks+1, ke+1)` is a
comparison of `v`; moreover `ks < ke`. -/
theorem alignment (v : List γ) {s e : ℕ} (hse : s < e) (he : e < (C.enc v).length) :
    (C.enc v).drop e <+: (C.enc v).drop s ↔
      ∃ ks ke, ∃ (hks : ks < v.length) (hke : ke < v.length), ks < ke ∧
        ∃ xs xe y, C.body v[ks] = xs ++ y ∧ C.body v[ke] = xe ++ y ∧
          s = C.cut v ks + xs.length ∧ e = C.cut v ke + xe.length ∧
          v.drop (ke + 1) <+: v.drop (ks + 1) := by
  constructor
  · intro hc
    obtain ⟨ks, hks, xs, ys, hs, rfl⟩ := C.pos_decomp v s (by omega)
    obtain ⟨ke, hke, xe, ye, hee, rfl⟩ := C.pos_decomp v e he
    rw [C.drop_at v ke hke xe ye hee, C.drop_at v ks hks xs ys hs,
      mark_prefix_iff (C.mark_not_mem_of_append hee) (C.mark_not_mem_of_append hs),
      C.enc_prefix_iff] at hc
    obtain ⟨rfl, hc⟩ := hc
    refine ⟨ks, ke, hks, hke, ?_, xs, xe, ye, hs, hee, rfl, rfl, hc⟩
    by_contra hlt
    have hm := C.cut_mono v (show ke + 1 ≤ ks + 1 by omega)
    rw [C.cut_succ v ke hke, C.cut_succ v ks hks, hs, hee] at hm
    simp only [List.length_append] at hm
    omega
  · rintro ⟨ks, ke, hks, hke, -, xs, xe, y, hs, hee, rfl, rfl, hc⟩
    rw [C.drop_at v ke hke xe y hee, C.drop_at v ks hks xs y hs, List.prefix_append_right_inj,
      List.cons_prefix_cons]
    exact ⟨rfl, (C.enc_prefix_iff _ _).mpr hc⟩

end MarkerCode

/-- `Vis(r,x) = {δ*(r, x[:i]) : 0 ≤ i < |x|}`. -/
def vis (M : DFA α Q) (r : Q) (x : List α) : Set Q :=
  {q | ∃ i < x.length, M.evalFrom r (x.take i) = q}

/-- `R[S] = {q : ∃ s ∈ S, (s,q) ∈ R}`. -/
def rimg (R : Q → Q → Prop) (S : Set Q) : Set Q := {q | ∃ p ∈ S, R p q}

variable (C : MarkerCode α γ) (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)

variable {M R}

@[simp] theorem vis_nil (r : Q) : vis M r [] = ∅ := by
  ext q; simp [vis]

@[simp] theorem rimg_empty : rimg R (∅ : Set Q) = ∅ := by
  ext q; simp [rimg]

/-- A hole condition split into: target, endpoint pairs `(x, n)`, interior pairs
`(s, e)` with `e < n`. -/
theorem isReaderHole_iff_split (u : List α) :
    IsReaderHole M R T u ↔
      runPrefix M u u.length ∈ T ∧ runPrefix M u u.length ∉ rimg R (vis M M.start u) ∧
        ∀ s e, s < e → e < u.length → u.drop e <+: u.drop s →
          ¬ R (runPrefix M u s) (runPrefix M u e) := by
  constructor
  · rintro ⟨hT, hW⟩
    refine ⟨hT, ?_, fun s e hse he hc => hW _ _ ⟨s, e, hse, he.le, rfl, rfl, hc⟩⟩
    rintro ⟨p, ⟨i, hi, rfl⟩, hr⟩
    exact hW _ _ ⟨i, u.length, hi, le_rfl, rfl, rfl, by simp⟩ hr
  · rintro ⟨hT, hE, hI⟩
    refine ⟨hT, ?_⟩
    rintro p q ⟨s, e, hse, he, rfl, rfl, hc⟩ hr
    rcases Nat.lt_or_ge e u.length with he' | he'
    · exact hI s e hse he' hc hr
    · have hn : e = u.length := le_antisymm he he'
      subst hn
      exact hE ⟨_, ⟨s, hse, rfl⟩, hr⟩

end DeciNSSE.Desubstitution
