import DeciNSSE.Holes.CoAlignment
import DeciNSSE.Holes.Hierarchy.Expansion

/-! # Derived monitors

Fix a lettered monitor `D` and a marker `ℓ`. The derived monitor `Der(D, ℓ)`
reads words over the alphabet of blocks: a block `X` stands for the factor
`X ℓ` of the expansion. Its cores are those of `D` and one new start core; its
interior admission is the right-aligned ladder `Λ'` and its terminal admission
adds the terminal admissions of the blocks. A nonempty block word avoiding
`ℓ` is a hole of `Der(D, ℓ)` exactly when its expansion is a hole of `D`.

## Main declarations

- `kst`, `labFrom`: the core reached after a word, and the labels read from a
  core.
- `fcore`, `zlab`: the exit core and the labels of a shifted block.
- `derΛ`, `derΛf`, `derTf`, `der`: the derived monitor `Der(D, ℓ)`.
- `label_expand`, `label_expand_length`: the labels of an expansion, by block.
- `terminal_admissions_expand_iff`, `internal_admissions_expand_iff`: the
  terminal and interior admissions of an expansion, by block.
- `isHole_der_iff`: holes of `Der(D, ℓ)` are the block words whose expansions
  are holes of `D`.
- `mapLab`: renaming of labels.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment
open scoped List

/-- Matching a letter label `some (b, d)` against the pattern `some (c, a)`. -/
theorem exists_some_eq_iff {β δ : Type*} (P : β → δ → Prop) (b : β) (d : δ) :
    (∃ c a, some (b, d) = some (c, a) ∧ P c a) ↔ P b d := by
  constructor
  · rintro ⟨c, a, h, hp⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp
  · intro h; exact ⟨b, d, rfl, h⟩

section Rename
variable {Γ C Γ' C' : Type*}

/-- Renaming labels: `S ↦ S`, `(c, a) ↦ (ψ c, φ a)`. -/
def mapLab (φ : Γ' → Γ) (ψ : C' → C) (L : Lab Γ' C') : Lab Γ C := L.map (Prod.map ψ φ)

end Rename

section Der
variable {Γ C : Type*}

/-- `κ*`: the core reached from `c` after reading `w`. -/
def kst (D : Lettered Γ C) (c : C) (w : List Γ) : C := D.coreDFA.evalFrom c w

/-- `κ*` along the empty word. -/
@[simp] theorem kst_nil (D : Lettered Γ C) (c : C) : kst D c [] = c := rfl

/-- `κ*` reads the first letter first. -/
@[simp] theorem kst_cons (D : Lettered Γ C) (c : C) (a : Γ) (w : List Γ) :
    kst D c (a :: w) = kst D (D.κ a c) w := rfl

/-- `κ*` along a concatenation. -/
theorem kst_append (D : Lettered Γ C) (c : C) (w w' : List Γ) :
    kst D c (w ++ w') = kst D (kst D c w) w' := DFA.evalFrom_of_append _ _ _ _

/-- The core run is `κ*` from the start core along a prefix. -/
theorem core_eq_kst (D : Lettered Γ C) (v : List Γ) (x : ℕ) :
    D.core v x = kst D D.start (v.take x) := rfl

/-- The label of cut `x` of `w` read from core `c`. -/
def labFrom (D : Lettered Γ C) (c : C) (w : List Γ) : ℕ → Lab Γ C
  | 0 => none
  | x + 1 => (w[x]?).map fun a => (kst D c (w.take x), a)

/-- The labels of a word are its labels read from the start core. -/
theorem label_eq_labFrom (D : Lettered Γ C) (w : List Γ) (x : ℕ) :
    D.label w x = labFrom D D.start w x := by
  cases x <;> rfl

/-- The labels of the cuts of `A` do not depend on what follows `A`. -/
theorem labFrom_append_le (D : Lettered Γ C) (c : C) (A B : List Γ) {p : ℕ}
    (hp : p ≤ A.length) : labFrom D c (A ++ B) p = labFrom D c A p := by
  rcases p with _ | x
  · rfl
  · simp only [labFrom]
    rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]

/-- The labels after a prefix `A` are read from the core reached after `A`. -/
theorem labFrom_append_add (D : Lettered Γ C) (c : C) (A B : List Γ) (q : ℕ) :
    labFrom D c (A ++ B) (A.length + (q + 1)) = labFrom D (kst D c A) B (q + 1) := by
  rw [show A.length + (q + 1) = (A.length + q) + 1 by omega]
  simp only [labFrom]
  rw [List.getElem?_append_right (by omega : A.length ≤ A.length + q), Nat.add_sub_cancel_left,
    List.take_length_add_append, kst_append]

variable (D : Lettered Γ C) (ℓ : Γ)

/-- The core after the shifted block: `fc(c, X)` reads `ℓ·X` from `c ∈ C`, and `X` from `⋆`
for the new start core `⋆' = none`. -/
def fcore : Option C → List Γ → C
  | none, X => kst D D.start X
  | some c, X => kst D c (ℓ :: X)

/-- `lab_p(c, X)`: the `𝔇`-label of position `p` of the shifted block `Ẑ(c, X)` (`ℓ·X` read
from `c`, or `⊢·X` read from `⋆`, position `0` of `⊢` carrying `S`). -/
def zlab : Option C → List Γ → ℕ → Lab Γ C
  | none, X, p => labFrom D D.start X p
  | some c, X, p => labFrom D c (ℓ :: X) (p + 1)

/-- `Λ'`: the right-aligned ladder. Some common suffix `y` of `X = x y`, `X' = x' y`
(the last `t - 1 = |y|` letters agree) has `Λ` at the labels of positions `|x|`, `|x'|`
(the first mismatch, or the marker/`⊢` column). `S` is in no pair. -/
def derΛ : Lab (List Γ) (Option C) → Lab (List Γ) (Option C) → Prop
  | some (c, X), some (c', X') => ∃ x x' y, X = x ++ y ∧ X' = x' ++ y ∧
      D.Λ (zlab D ℓ c X x.length) (zlab D ℓ c' X' x'.length)
  | _, _ => False

/-- `Λ'^f`: `Λ'`, or some label of the block is `Λ^f`-related to the final label
`(fc(c', X'), ℓ)` (the marker after `X'`). -/
def derΛf : Lab (List Γ) (Option C) → Lab (List Γ) (Option C) → Prop
  | some (c, X), some (c', X') => derΛ D ℓ (some (c, X)) (some (c', X')) ∨
      ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (fcore D ℓ c' X', ℓ))
  | _, _ => False

/-- `Tf'(c, X) = Tf(fc(c,X), ℓ) ∧ ¬∃ p, Λ^f(lab_p(c,X), (fc(c,X), ℓ))`. -/
def derTf (c : Option C) (X : List Γ) : Prop :=
  D.Tf (fcore D ℓ c X) ℓ ∧ ¬ ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (fcore D ℓ c X, ℓ))

/-- The monitor induced by replacing each marker-terminated block with a letter. -/
def der : Lettered (List Γ) (Option C) where
  start := none
  κ X c := some (fcore D ℓ c X)
  Λ := derΛ D ℓ
  Λf := derΛf D ℓ
  Tf := derTf D ℓ

/-- The derived run starts at the new start core. -/
theorem der_core_zero (v : List (List Γ)) : (der D ℓ).core v 0 = none := rfl

/-- The derived run moves to the exit core of each block. -/
theorem der_core_succ (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (der D ℓ).core v (k + 1) = some (fcore D ℓ ((der D ℓ).core v k) v[k]) := by
  rw [core_eq_kst, core_eq_kst, List.take_succ_eq_append_getElem hk, kst_append]
  rfl

/-- The core after block `k` is the `𝔇`-core before the
marker that ends block `k`: `fc(c'_k, X_k) = κ*(⋆, σ_ℓ(v[:k]) X_k)`. -/
theorem fcore_core (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    fcore D ℓ ((der D ℓ).core v k) v[k] = kst D D.start (expand ℓ (v.take k) ++ v[k]) := by
  induction k with
  | zero => simp [der_core_zero, fcore]
  | succ k ih =>
    rw [der_core_succ D ℓ v k (by omega), fcore, ih (by omega), ← kst_append,
      expand_take_succ ℓ v k (by omega)]
    simp

/-- The cut `P_k + p` (`p ≤ |X_k|`) of `σ_ℓ(v)` carries the
label `lab_p(c'_k, X_k)` of position `p` of the shifted block of `X_k`. -/
theorem label_expand (v : List (List Γ)) (k : ℕ) (hk : k < v.length) {p : ℕ}
    (hp : p ≤ v[k].length) :
    D.label (expand ℓ v) (cutP ℓ v k + p) = zlab D ℓ ((der D ℓ).core v k) v[k] p := by
  rw [label_eq_labFrom]
  rcases k with _ | k
  · rw [der_core_zero]
    simp only [cutP, List.take_zero, expand_nil, List.length_nil, Nat.zero_add, zlab]
    rw [expand_split ℓ v 0 hk]
    simp only [List.take_zero, expand_nil, List.nil_append]
    exact labFrom_append_le D _ _ _ hp
  · rw [der_core_succ D ℓ v k (by omega), fcore_core D ℓ v k (by omega)]
    simp only [zlab]
    rw [expand_split ℓ v (k + 1) hk, expand_take_succ ℓ v k (by omega)]
    have hc : cutP ℓ v (k + 1) + p =
        (expand ℓ (v.take k) ++ v[k]).length + (p + 1) := by
      rw [cutP_succ ℓ v k (by omega)]; simp [cutP]; omega
    rw [hc, show expand ℓ (List.take k v) ++ v[k] ++ [ℓ] ++
        (v[k + 1] ++ ℓ :: expand ℓ (List.drop (k + 1 + 1) v)) =
        (expand ℓ (List.take k v) ++ v[k]) ++
          ((ℓ :: v[k + 1]) ++ ℓ :: expand ℓ (List.drop (k + 1 + 1) v)) by simp,
      labFrom_append_add, labFrom_append_le D _ _ _ (by simpa using hp)]

/-- The final label of `σ_ℓ(v)` is `(fc(c'_{k-1}, X_{k-1}), ℓ)`. -/
theorem label_expand_length (v : List (List Γ)) (j : ℕ) (hj : v.length = j + 1) :
    D.label (expand ℓ v) (expand ℓ v).length =
      some (fcore D ℓ ((der D ℓ).core v j) v[j], ℓ) := by
  have hjv : j < v.length := by omega
  have hsplit : expand ℓ v = (expand ℓ (v.take j) ++ v[j]) ++ [ℓ] := by
    rw [expand_split ℓ v j hjv, List.drop_eq_nil_of_le (by omega)]
    simp
  rw [label_eq_labFrom, fcore_core D ℓ v j hjv, hsplit]
  simp only [List.length_append, List.length_singleton, labFrom]
  rw [List.getElem?_append_right (by simp), List.take_left' (by simp)]
  simp

/-- The start core of `Der(D, ℓ)` is the new start core. -/
@[simp] theorem der_start : (der D ℓ).start = none := rfl
/-- The interior admission of `Der(D, ℓ)` is the ladder `Λ'`. -/
@[simp] theorem der_Λ : (der D ℓ).Λ = derΛ D ℓ := rfl
/-- The terminal admission of `Der(D, ℓ)` is `Λ'^f`. -/
@[simp] theorem der_Λf : (der D ℓ).Λf = derΛf D ℓ := rfl
/-- The target condition of `Der(D, ℓ)` is `Tf'`. -/
@[simp] theorem der_Tf : (der D ℓ).Tf = derTf D ℓ := rfl
/-- A block moves the derived run to its exit core. -/
@[simp] theorem der_κ (X : List Γ) (c : Option C) : (der D ℓ).κ X c = some (fcore D ℓ c X) := rfl

/-- The start label `S` is in no ladder pair. -/
@[simp] theorem derΛ_none_left (L : Lab (List Γ) (Option C)) : ¬ derΛ D ℓ none L := by
  simp [derΛ]

/-- The start label `S` is in no terminal ladder pair. -/
@[simp] theorem derΛf_none_left (L : Lab (List Γ) (Option C)) : ¬ derΛf D ℓ none L := by
  simp [derΛf]

/-- Terminal admissions of an expansion, by block: no cut of `σ_ℓ(v)` before its end has
a label `Λ^f`-related to `L` iff no position of a shifted block has one. -/
theorem terminal_admissions_expand_iff (v : List (List Γ)) (L : Lab Γ C) :
    (∀ s, s < (expand ℓ v).length → ¬ D.Λf (D.label (expand ℓ v) s) L) ↔
      ∀ a (ha : a < v.length), ∀ p ≤ v[a].length,
        ¬ D.Λf (zlab D ℓ ((der D ℓ).core v a) v[a] p) L := by
  constructor
  · intro h a ha p hp
    have := h _ (pos_lt ℓ v ha hp)
    rwa [label_expand D ℓ v a ha hp] at this
  · intro h s hs
    obtain ⟨a, ha, p, hp, rfl⟩ := pos_decomp ℓ v hs
    rw [label_expand D ℓ v a ha hp]
    exact h a ha p hp

/-- Interior admissions of an expansion, by block. For blocks avoiding `ℓ`, no comparison
of `σ_ℓ(v)` ending before its end is `Λ`-admitted iff no pair of blocks `a < b` with
`v[b+1:] ⪯ v[a+1:]` is related by the ladder `Λ'`. -/
theorem internal_admissions_expand_iff (v : List (List Γ)) (hℓ : ∀ X ∈ v, ℓ ∉ X) :
    (∀ s e, IsComp (expand ℓ v) s e → e < (expand ℓ v).length →
        ¬ D.Λ (D.label (expand ℓ v) s) (D.label (expand ℓ v) e)) ↔
      ∀ a b (ha : a < v.length) (hb : b < v.length), a < b →
        v.drop (b + 1) <+: v.drop (a + 1) →
        ¬ derΛ D ℓ (some ((der D ℓ).core v a, v[a])) (some ((der D ℓ).core v b, v[b])) := by
  constructor
  · rintro h a b ha hb hab hc ⟨xs, xe, y, hxs, hxe, hΛ⟩
    have hpa : xs.length ≤ v[a].length := by rw [hxs]; simp
    have hpb : xe.length ≤ v[b].length := by rw [hxe]; simp
    have he := pos_lt ℓ v hb hpb
    have hlt : cutP ℓ v a + xs.length < cutP ℓ v b + xe.length := by
      have h1 := cutP_succ ℓ v a ha
      have h2 := cutP_mono ℓ v (show a + 1 ≤ b by omega)
      omega
    refine h _ _ ⟨hlt, he.le, (alignment ℓ v hℓ hlt he).mpr
      ⟨a, b, ha, hb, hab, xs, xe, y, hxs, hxe, rfl, rfl, hc⟩⟩ he ?_
    rw [label_expand D ℓ v a ha hpa, label_expand D ℓ v b hb hpb]
    exact hΛ
  · rintro h s e ⟨hse, -, hc⟩ he hΛ
    obtain ⟨a, b, ha, hb, hab, xs, xe, y, hxs, hxe, rfl, rfl, hc'⟩ :=
      (alignment ℓ v hℓ hse he).mp hc
    rw [label_expand D ℓ v a ha (by rw [hxs]; simp),
      label_expand D ℓ v b hb (by rw [hxe]; simp)] at hΛ
    exact h a b ha hb hab hc' ⟨xs, xe, y, hxs, hxe, hΛ⟩

/-- Desubstitution. A nonempty block word `v` avoiding `ℓ` is a hole of `Der(D, ℓ)` iff its
expansion `σ_ℓ(v)` is a hole of `D`. -/
theorem isHole_der_iff (v : List (List Γ)) (hv : v ≠ []) (hℓ : ∀ X ∈ v, ℓ ∉ X) :
    (der D ℓ).IsHole v ↔ D.IsHole (expand ℓ v) := by
  obtain ⟨j, hlen⟩ : ∃ j, v.length = j + 1 :=
    ⟨v.length - 1, by have := List.length_pos_iff.mpr hv; omega⟩
  have hj : j < v.length := by omega
  set F := fcore D ℓ ((der D ℓ).core v j) v[j] with hF
  have hfin : D.label (expand ℓ v) (expand ℓ v).length = some (F, ℓ) :=
    label_expand_length D ℓ v j hlen
  have hfin' : (der D ℓ).label v v.length = some ((der D ℓ).core v j, v[j]) := by
    simp only [hlen]; exact Lettered.label_succ _ v hj
  unfold Lettered.IsHole
  rw [terminal_admissions_expand_iff D ℓ v, internal_admissions_expand_iff D ℓ v hℓ, hfin,
    hfin', exists_some_eq_iff, exists_some_eq_iff]
  simp only [der_Tf, der_Λf, der_Λ]
  constructor
  · rintro ⟨⟨hT1, hT2⟩, hE', hI'⟩
    refine ⟨hT1, ?_, ?_⟩
    · intro a ha p hp hr
      rcases Nat.lt_or_ge a j with haj | haj
      · have := hE' (a + 1) (by omega)
        rw [Lettered.label_succ _ v ha] at this
        exact this (Or.inr ⟨p, hp, hr⟩)
      · obtain rfl : a = j := by omega
        exact hT2 ⟨p, hp, hr⟩
    · intro a b ha hb hab hc hr
      rcases Nat.lt_or_ge b j with hbj | hbj
      · have := hI' (a + 1) (b + 1) ⟨by omega, by omega, hc⟩ (by omega)
        rw [Lettered.label_succ _ v ha, Lettered.label_succ _ v hb] at this
        exact this hr
      · obtain rfl : b = j := by omega
        have := hE' (a + 1) (by omega)
        rw [Lettered.label_succ _ v ha] at this
        exact this (Or.inl hr)
  · rintro ⟨hT1, hE', hI'⟩
    refine ⟨⟨hT1, fun ⟨p, hp, hr⟩ => hE' j hj p hp hr⟩, ?_, ?_⟩
    · intro s hs
      rcases s with _ | a
      · exact derΛf_none_left D ℓ _
      · have ha : a < v.length := by omega
        rw [Lettered.label_succ _ v ha]
        rintro (hr | ⟨p, hp, hr⟩)
        · exact hI' a j ha hj (by omega) (by rw [List.drop_eq_nil_of_le (by omega)]; simp) hr
        · exact hE' a ha p hp hr
    · intro s e hc he
      rcases s with _ | a
      · exact derΛ_none_left D ℓ _
      · obtain ⟨b, rfl⟩ : ∃ b, e = b + 1 := ⟨e - 1, by have := hc.1; omega⟩
        have ha : a < v.length := by have := hc.1; omega
        have hb : b < v.length := by omega
        rw [Lettered.label_succ _ v ha, Lettered.label_succ _ v hb]
        exact hI' a b ha hb (by have := hc.1; omega) hc.2.2

end Der

end DeciNSSE.LetteredHierarchy
