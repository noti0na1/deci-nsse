import DeciNSSE.Holes.Desubstitution
import DeciNSSE.Holes.CoAlignment

/-! # The canonical desubstitution hierarchy

Cutting at the last letter repeatedly produces a hierarchy of block words.
Derived lettered monitors preserve holes under expansion. Canonical markers,
start cores and bounded horizons relate this hierarchy to finite readers.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment DeciNSSE.Desubstitution DeciNSSE.Holes

section Expand
variable {Γ : Type*}

/-- Expand a block word by appending the marker to each block and concatenating. -/
def expand (ℓ : Γ) (v : List (List Γ)) : List Γ := v.flatMap (· ++ [ℓ])

@[simp] theorem expand_nil (ℓ : Γ) : expand ℓ [] = [] := rfl

@[simp] theorem expand_cons (ℓ : Γ) (X : List Γ) (v : List (List Γ)) :
    expand ℓ (X :: v) = X ++ ℓ :: expand ℓ v := by
  simp [expand]

@[simp] theorem expand_append (ℓ : Γ) (v w : List (List Γ)) :
    expand ℓ (v ++ w) = expand ℓ v ++ expand ℓ w := by
  simp [expand]

theorem expand_snoc (ℓ : Γ) (v : List (List Γ)) (X : List Γ) :
    expand ℓ (v ++ [X]) = expand ℓ v ++ X ++ [ℓ] := by
  simp

theorem expand_eq_nil {ℓ : Γ} {v : List (List Γ)} : expand ℓ v = [] ↔ v = [] := by
  cases v <;> simp

/-- The position reached after expanding the first `k` blocks. -/
def cutP (ℓ : Γ) (v : List (List Γ)) (k : ℕ) : ℕ := (expand ℓ (v.take k)).length

theorem expand_split (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    expand ℓ v = expand ℓ (v.take k) ++ (v[k] ++ ℓ :: expand ℓ (v.drop (k + 1))) := by
  have h := List.take_append_drop k v
  rw [List.drop_eq_getElem_cons hk] at h
  conv_lhs => rw [← h]
  rw [expand_append, expand_cons]

theorem expand_take_succ (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    expand ℓ (v.take (k + 1)) = expand ℓ (v.take k) ++ v[k] ++ [ℓ] := by
  rw [List.take_succ_eq_append_getElem hk, expand_snoc]

theorem cutP_succ (ℓ : Γ) (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    cutP ℓ v (k + 1) = cutP ℓ v k + v[k].length + 1 := by
  simp only [cutP, expand_take_succ ℓ v k hk, List.length_append, List.length_singleton]

theorem length_expand (ℓ : Γ) (v : List (List Γ)) :
    (expand ℓ v).length = cutP ℓ v v.length := by
  simp [cutP]

theorem cutP_mono (ℓ : Γ) (v : List (List Γ)) {i j : ℕ} (hij : i ≤ j) :
    cutP ℓ v i ≤ cutP ℓ v j := by
  obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := v) hij
  simp only [cutP, ← ht, expand_append, List.length_append]
  omega

theorem cutP_le_length (ℓ : Γ) (v : List (List Γ)) (k : ℕ) :
    cutP ℓ v k ≤ (expand ℓ v).length := by
  rw [length_expand]
  rcases Nat.lt_or_ge k v.length with h | h
  · exact cutP_mono ℓ v h.le
  · simp [cutP, List.take_of_length_le h]

/-- The marker code whose bodies are precisely the words avoiding the marker. -/
def mcode (ℓ : Γ) : MarkerCode Γ {X : List Γ // ℓ ∉ X} where
  mark := ℓ
  body := Subtype.val
  mark_not_mem c := c.2
  body_injective := Subtype.val_injective

theorem mcode_enc (ℓ : Γ) (x : List {X : List Γ // ℓ ∉ X}) :
    (mcode ℓ).enc x = expand ℓ (x.map Subtype.val) := by
  induction x with
  | nil => rfl
  | cons X x ih =>
    rw [MarkerCode.enc_cons, ih, List.map_cons, expand_cons]
    simp [MarkerCode.code, mcode]

theorem mcode_cut (ℓ : Γ) (x : List {X : List Γ // ℓ ∉ X}) (k : ℕ) :
    (mcode ℓ).cut x k = cutP ℓ (x.map Subtype.val) k := by
  simp [MarkerCode.cut, cutP, mcode_enc, List.map_take]

theorem lift_avoid {ℓ : Γ} {v : List (List Γ)} (h : ∀ X ∈ v, ℓ ∉ X) :
    ∃ x : List {X : List Γ // ℓ ∉ X}, x.map Subtype.val = v :=
  ⟨v.attach.map fun X => ⟨X.1, h X.1 X.2⟩, by simp⟩

theorem prefix_map_inj {α β : Type*} {f : α → β} (hf : Function.Injective f) {l₁ l₂ : List α} :
    l₁.map f <+: l₂.map f ↔ l₁ <+: l₂ := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  obtain ⟨l, hl, he⟩ := List.prefix_map_iff.mp h
  rw [List.map_inj_right (fun a b h => hf h)] at he
  exact he ▸ hl

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

theorem pos_lt (ℓ : Γ) (v : List (List Γ)) {k : ℕ} (hk : k < v.length) {p : ℕ}
    (hp : p ≤ v[k].length) : cutP ℓ v k + p < (expand ℓ v).length := by
  have h1 := cutP_succ ℓ v k hk
  have h2 := cutP_le_length ℓ v (k + 1)
  omega

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

end Expand

theorem exists_some_eq_iff {β δ : Type*} (P : β → δ → Prop) (b : β) (d : δ) :
    (∃ c a, some (b, d) = some (c, a) ∧ P c a) ↔ P b d := by
  constructor
  · rintro ⟨c, a, h, hp⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hp
  · intro h; exact ⟨b, d, rfl, h⟩

section Der
variable {Γ C : Type*}

/-- Evaluate a word in the core automaton from a specified core. -/
def kst (D : Lettered Γ C) (c : C) (w : List Γ) : C := D.coreDFA.evalFrom c w

@[simp] theorem kst_nil (D : Lettered Γ C) (c : C) : kst D c [] = c := rfl

@[simp] theorem kst_cons (D : Lettered Γ C) (c : C) (a : Γ) (w : List Γ) :
    kst D c (a :: w) = kst D (D.κ a c) w := rfl

theorem kst_append (D : Lettered Γ C) (c : C) (w w' : List Γ) :
    kst D c (w ++ w') = kst D (kst D c w) w' := DFA.evalFrom_of_append _ _ _ _

theorem core_eq_kst (D : Lettered Γ C) (v : List Γ) (x : ℕ) :
    D.core v x = kst D D.start (v.take x) := rfl

/-- The core-and-letter labels along a word from a specified initial core. -/
def labFrom (D : Lettered Γ C) (c : C) (w : List Γ) : ℕ → Lab Γ C
  | 0 => none
  | x + 1 => (w[x]?).map fun a => (kst D c (w.take x), a)

theorem label_eq_labFrom (D : Lettered Γ C) (w : List Γ) (x : ℕ) :
    D.label w x = labFrom D D.start w x := by
  cases x <;> rfl

theorem labFrom_append_le (D : Lettered Γ C) (c : C) (A B : List Γ) {p : ℕ}
    (hp : p ≤ A.length) : labFrom D c (A ++ B) p = labFrom D c A p := by
  rcases p with _ | x
  · rfl
  · simp only [labFrom]
    rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]

theorem labFrom_append_add (D : Lettered Γ C) (c : C) (A B : List Γ) (q : ℕ) :
    labFrom D c (A ++ B) (A.length + (q + 1)) = labFrom D (kst D c A) B (q + 1) := by
  rw [show A.length + (q + 1) = (A.length + q) + 1 by omega]
  simp only [labFrom]
  rw [List.getElem?_append_right (by omega : A.length ≤ A.length + q), Nat.add_sub_cancel_left,
    List.take_length_add_append, kst_append]

variable (D : Lettered Γ C) (ℓ : Γ)

/-- The final core of a block, including its preceding marker when present. -/
def fcore : Option C → List Γ → C
  | none, X => kst D D.start X
  | some c, X => kst D c (ℓ :: X)

/-- The label at a position within a block, accounting for its preceding marker. -/
def zlab : Option C → List Γ → ℕ → Lab Γ C
  | none, X, p => labFrom D D.start X p
  | some c, X, p => labFrom D c (ℓ :: X) (p + 1)

/-- Admission between blocks witnessed before a common suffix of their bodies. -/
def derΛ : Lab (List Γ) (Option C) → Lab (List Γ) (Option C) → Prop
  | some (c, X), some (c', X') => ∃ x x' y, X = x ++ y ∧ X' = x' ++ y ∧
      D.Λ (zlab D ℓ c X x.length) (zlab D ℓ c' X' x'.length)
  | _, _ => False

/-- Admission between blocks allowing an endpoint at the final marker. -/
def derΛf : Lab (List Γ) (Option C) → Lab (List Γ) (Option C) → Prop
  | some (c, X), some (c', X') => derΛ D ℓ (some (c, X)) (some (c', X')) ∨
      ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (fcore D ℓ c' X', ℓ))
  | _, _ => False

/-- A block ends in a target label and contains no admitted comparison to its final marker. -/
def derTf (c : Option C) (X : List Γ) : Prop :=
  D.Tf (fcore D ℓ c X) ℓ ∧ ¬ ∃ p ≤ X.length, D.Λf (zlab D ℓ c X p) (some (fcore D ℓ c X, ℓ))

/-- The lettered monitor induced by cutting at a fixed marker. -/
def der : Lettered (List Γ) (Option C) where
  start := none
  κ X c := some (fcore D ℓ c X)
  Λ := derΛ D ℓ
  Λf := derΛf D ℓ
  Tf := derTf D ℓ

theorem der_core_zero (v : List (List Γ)) : (der D ℓ).core v 0 = none := rfl

theorem der_core_succ (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (der D ℓ).core v (k + 1) = some (fcore D ℓ ((der D ℓ).core v k) v[k]) := by
  rw [core_eq_kst, core_eq_kst, List.take_succ_eq_append_getElem hk, kst_append]
  rfl

theorem fcore_core (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    fcore D ℓ ((der D ℓ).core v k) v[k] = kst D D.start (expand ℓ (v.take k) ++ v[k]) := by
  induction k with
  | zero => simp [der_core_zero, fcore]
  | succ k ih =>
    rw [der_core_succ D ℓ v k (by omega), fcore, ih (by omega), ← kst_append,
      expand_take_succ ℓ v k (by omega)]
    simp

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

@[simp] theorem der_start : (der D ℓ).start = none := rfl
@[simp] theorem der_Λ : (der D ℓ).Λ = derΛ D ℓ := rfl
@[simp] theorem der_Λf : (der D ℓ).Λf = derΛf D ℓ := rfl
@[simp] theorem der_Tf : (der D ℓ).Tf = derTf D ℓ := rfl
@[simp] theorem der_κ (X : List Γ) (c : Option C) : (der D ℓ).κ X c = some (fcore D ℓ c X) := rfl

@[simp] theorem derΛ_none_left (L : Lab (List Γ) (Option C)) : ¬ derΛ D ℓ none L := by
  simp [derΛ]

@[simp] theorem derΛf_none_left (L : Lab (List Γ) (Option C)) : ¬ derΛf D ℓ none L := by
  simp [derΛf]

/-- Desubstitution at a marker preserves holes for nonempty marker-free block words. -/
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

  have hE : (∀ s, s < (expand ℓ v).length →
        ¬ D.Λf (D.label (expand ℓ v) s) (D.label (expand ℓ v) (expand ℓ v).length)) ↔
      ∀ a (ha : a < v.length), ∀ p ≤ v[a].length,
        ¬ D.Λf (zlab D ℓ ((der D ℓ).core v a) v[a] p) (some (F, ℓ)) := by
    rw [hfin]
    constructor
    · intro h a ha p hp
      have := h _ (pos_lt ℓ v ha hp)
      rwa [label_expand D ℓ v a ha hp] at this
    · intro h s hs
      obtain ⟨a, ha, p, hp, rfl⟩ := pos_decomp ℓ v hs
      rw [label_expand D ℓ v a ha hp]
      exact h a ha p hp

  have hI : (∀ s e, IsComp (expand ℓ v) s e → e < (expand ℓ v).length →
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
  unfold Lettered.IsHole
  rw [hE, hI, hfin, hfin', exists_some_eq_iff, exists_some_eq_iff]
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

section Cut
variable {Γ : Type*} [DecidableEq Γ]

/-- Cut a word into marker-free blocks ending just before each occurrence of the marker. -/
def cutAt (ℓ : Γ) : List Γ → List (List Γ)
  | [] => []
  | a :: u => if a = ℓ then [] :: cutAt ℓ u else
      match cutAt ℓ u with
      | [] => []
      | X :: rest => (a :: X) :: rest

theorem cutAt_of_not_mem {ℓ : Γ} : ∀ {t : List Γ}, ℓ ∉ t → cutAt ℓ t = []
  | [], _ => rfl
  | a :: t, h => by
      have ha : a ≠ ℓ := fun h' => h (h' ▸ List.mem_cons_self)
      have ht : ℓ ∉ t := fun h' => h (List.mem_cons_of_mem _ h')
      simp [cutAt, ha, cutAt_of_not_mem ht]

theorem cutAt_block {ℓ : Γ} (w : List Γ) : ∀ {X : List Γ}, ℓ ∉ X →
    cutAt ℓ (X ++ ℓ :: w) = X :: cutAt ℓ w
  | [], _ => by simp [cutAt]
  | a :: X, h => by
      have ha : a ≠ ℓ := fun h' => h (h' ▸ List.mem_cons_self)
      have hX : ℓ ∉ X := fun h' => h (List.mem_cons_of_mem _ h')
      simp [cutAt, ha, cutAt_block w hX]

theorem cutAt_expand_append {ℓ : Γ} {t : List Γ} (ht : ℓ ∉ t) :
    ∀ {v : List (List Γ)}, (∀ X ∈ v, ℓ ∉ X) → cutAt ℓ (expand ℓ v ++ t) = v
  | [], _ => by simpa using cutAt_of_not_mem ht
  | X :: v, h => by
      rw [expand_cons, List.append_assoc, List.cons_append,
        cutAt_block _ (h X List.mem_cons_self),
        cutAt_expand_append ht (fun Y hY => h Y (List.mem_cons_of_mem _ hY))]

theorem cutAt_expand {ℓ : Γ} {v : List (List Γ)} (h : ∀ X ∈ v, ℓ ∉ X) :
    cutAt ℓ (expand ℓ v) = v := by
  simpa using cutAt_expand_append (t := []) (by simp) h

theorem exists_expand_append (ℓ : Γ) : ∀ u : List Γ,
    ∃ v t, u = expand ℓ v ++ t ∧ ℓ ∉ t ∧ ∀ X ∈ v, ℓ ∉ X
  | [] => ⟨[], [], rfl, by simp, by simp⟩
  | a :: u => by
      obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
      by_cases ha : a = ℓ
      · subst ha
        refine ⟨[] :: v, t, by simp, ht, ?_⟩
        intro X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · simp
        · exact hv X hX
      · rcases v with _ | ⟨X, v⟩
        · refine ⟨[], a :: t, by simp, ?_, by simp⟩
          simp only [List.mem_cons, not_or]
          exact ⟨Ne.symm ha, ht⟩
        · refine ⟨(a :: X) :: v, t, by simp, ht, ?_⟩
          intro Y hY
          rcases List.mem_cons.mp hY with rfl | hY
          · simp only [List.mem_cons, not_or]
            exact ⟨Ne.symm ha, hv X List.mem_cons_self⟩
          · exact hv Y (List.mem_cons_of_mem _ hY)

theorem avoid_cutAt (ℓ : Γ) (u : List Γ) : ∀ X ∈ cutAt ℓ u, ℓ ∉ X := by
  obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
  rw [cutAt_expand_append ht hv]
  exact hv

theorem expand_cutAt {ℓ : Γ} {u : List Γ} (hu : u.getLast? = some ℓ) :
    expand ℓ (cutAt ℓ u) = u := by
  obtain ⟨v, t, rfl, ht, hv⟩ := exists_expand_append ℓ u
  rw [cutAt_expand_append ht hv]
  rcases List.eq_nil_or_concat t with rfl | ⟨t', b, rfl⟩
  · simp
  · rw [List.concat_eq_append, ← List.append_assoc, List.getLast?_append_of_ne_nil _
      (by simp), List.getLast?_singleton, Option.some.injEq] at hu
    exact absurd (by simp [hu]) ht

theorem cutAt_ne_nil {ℓ : Γ} {u : List Γ} (hu : u.getLast? = some ℓ) : cutAt ℓ u ≠ [] := by
  intro h
  have := expand_cutAt hu
  rw [h, expand_nil] at this
  subst this
  simp at hu

omit [DecidableEq Γ] in
theorem getLast?_expand {ℓ : Γ} {v : List (List Γ)} (hv : v ≠ []) :
    (expand ℓ v).getLast? = some ℓ := by
  rcases List.eq_nil_or_concat v with rfl | ⟨v', X, rfl⟩
  · exact absurd rfl hv
  · rw [List.concat_eq_append, expand_snoc, List.getLast?_append_of_ne_nil _ (by simp)]
    simp

end Cut

section Hierarchy
universe u v

/-- The alphabet at a hierarchy level, obtained by iterating the list construction. -/
@[reducible] def Alph (α : Type u) : ℕ → Type u
  | 0 => α
  | i + 1 => List (Alph α i)

/-- The core type at a hierarchy level, with one new start core per derivation. -/
@[reducible] def Cores (Q : Type v) : ℕ → Type v
  | 0 => Q
  | i + 1 => Option (Cores Q i)

instance instDecEqAlph {α : Type u} [DecidableEq α] : ∀ i, DecidableEq (Alph α i)
  | 0 => (inferInstance : DecidableEq α)
  | i + 1 => @instDecidableEqList (Alph α i) (instDecEqAlph i)

instance instInhabitedAlph {α : Type u} [Inhabited α] : ∀ i, Inhabited (Alph α i)
  | 0 => (inferInstance : Inhabited α)
  | _ + 1 => ⟨[]⟩

variable {α : Type u} {Q : Type v}

/-- Iterate the derived-monitor construction along a sequence of markers. -/
def tower (D0 : Lettered α Q) (ℓ : (i : ℕ) → Alph α i) :
    (i : ℕ) → Lettered (Alph α i) (Cores Q i)
  | 0 => D0
  | i + 1 => der (tower D0 ℓ i) (ℓ i)

/-- Expand a word at a hierarchy level back to the base alphabet. -/
def expandTo (ℓ : (i : ℕ) → Alph α i) : (j : ℕ) → List (Alph α j) → List α
  | 0, v => v
  | j + 1, v => expandTo ℓ j (expand (ℓ j) v)

/-- Every block avoids its level's marker throughout expansion to the base alphabet. -/
def Admissible (ℓ : (i : ℕ) → Alph α i) : (j : ℕ) → List (Alph α j) → Prop
  | 0, _ => True
  | j + 1, v => (∀ X ∈ v, ℓ j ∉ X) ∧ Admissible ℓ j (expand (ℓ j) v)

theorem expandTo_ne_nil (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (v : List (Alph α j)), v ≠ [] → expandTo ℓ j v ≠ []
  | 0, _, h => h
  | j + 1, v, h => expandTo_ne_nil ℓ j _ (by simpa [expand_eq_nil] using h)

/-- Admissible expansion through any number of levels preserves holes. -/
theorem isHole_tower_iff (D0 : Lettered α Q) (ℓ : (i : ℕ) → Alph α i) :
    ∀ (j : ℕ) (v : List (Alph α j)), Admissible ℓ j v → v ≠ [] →
      ((tower D0 ℓ j).IsHole v ↔ D0.IsHole (expandTo ℓ j v))
  | 0, _, _, _ => Iff.rfl
  | j + 1, v, ⟨hav, had⟩, hv => by
      rw [show tower D0 ℓ (j + 1) = der (tower D0 ℓ j) (ℓ j) from rfl,
        isHole_der_iff _ _ v hv hav,
        isHole_tower_iff D0 ℓ j _ had (by simpa [expand_eq_nil] using hv)]
      rfl

variable [DecidableEq α] [Inhabited α]

/-- The canonical hierarchy, obtained by repeatedly cutting at the last letter. -/
def hierOf (w : List α) : (i : ℕ) → List (Alph α i)
  | 0 => w
  | i + 1 => cutAt ((hierOf w i).getLastD default) (hierOf w i)

/-- The last letter of the canonical word at a given level, or the default if empty. -/
def markOf (w : List α) (i : ℕ) : Alph α i := (hierOf w i).getLastD default

theorem hierOf_succ (w : List α) (i : ℕ) :
    hierOf w (i + 1) = cutAt (markOf w i) (hierOf w i) := rfl

section Canonical
variable {w : List α} (hw : w ≠ [])
include hw

theorem hierOf_ne_nil : ∀ i, hierOf w i ≠ []
  | 0 => hw
  | i + 1 => by
      rw [hierOf_succ]
      refine cutAt_ne_nil ?_
      rw [markOf, List.getLastD_eq_getLast?]
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
        (by simpa using hierOf_ne_nil i : (hierOf w i).getLast? ≠ none)
      simp [ha]

theorem getLast?_hierOf (i : ℕ) : (hierOf w i).getLast? = some (markOf w i) := by
  rw [markOf, List.getLastD_eq_getLast?]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
    (by simpa using hierOf_ne_nil hw i : (hierOf w i).getLast? ≠ none)
  simp [ha]

theorem expand_hierOf (i : ℕ) : expand (markOf w i) (hierOf w (i + 1)) = hierOf w i := by
  rw [hierOf_succ, expand_cutAt (getLast?_hierOf hw i)]

omit hw in
theorem avoid_hierOf (i : ℕ) : ∀ X ∈ hierOf w (i + 1), markOf w i ∉ X := by
  rw [hierOf_succ]; exact avoid_cutAt _ _

theorem markOf_mem (i : ℕ) : markOf w i ∈ hierOf w i :=
  List.mem_of_getLast? (getLast?_hierOf hw i)

theorem admissible_hierOf : ∀ i, Admissible (markOf w) i (hierOf w i)
  | 0 => trivial
  | i + 1 => ⟨avoid_hierOf i, by rw [expand_hierOf hw i]; exact admissible_hierOf i⟩

/-- Expanding a canonical hierarchy level recovers the original word. -/
theorem expandTo_hierOf : ∀ i, expandTo (markOf w) i (hierOf w i) = w
  | 0 => rfl
  | i + 1 => by
      rw [expandTo, expand_hierOf hw i]; exact expandTo_hierOf i

/-- Every canonical hierarchy level represents a hole exactly when the base word does. -/
theorem isHole_hierOf_iff (D0 : Lettered α Q) (i : ℕ) :
    (tower D0 (markOf w) i).IsHole (hierOf w i) ↔ D0.IsHole w := by
  rw [isHole_tower_iff D0 (markOf w) i _ (admissible_hierOf hw i) (hierOf_ne_nil hw i),
    expandTo_hierOf hw i]

end Canonical

theorem hierOf_expandTo (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (v : List (Alph α j)),
    Admissible ℓ j v → v ≠ [] →
      hierOf (expandTo ℓ j v) j = v ∧ ∀ i < j, markOf (expandTo ℓ j v) i = ℓ i
  | 0, _, _, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, v, ⟨hav, had⟩, hv => by
      have hv' : expand (ℓ j) v ≠ [] := by simpa [expand_eq_nil] using hv
      obtain ⟨h1, h2⟩ := hierOf_expandTo ℓ j _ had hv'
      have hm : markOf (expandTo ℓ (j + 1) v) j = ℓ j := by
        rw [markOf, expandTo, h1, List.getLastD_eq_getLast?, getLast?_expand hv]
        rfl
      refine ⟨?_, fun i hi => ?_⟩
      · rw [hierOf_succ, hm, expandTo, h1, cutAt_expand hav]
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact hm

end Hierarchy

section StartOne
variable {Γ C : Type*} (D : Lettered Γ C) (ℓ : Γ)

theorem take_expand_cutP (v : List (List Γ)) (k : ℕ) :
    (expand ℓ v).take (cutP ℓ v k) = expand ℓ (v.take k) := by
  have h : expand ℓ v = expand ℓ (v.take k) ++ expand ℓ (v.drop k) := by
    rw [← expand_append, List.take_append_drop]
  rw [h]; exact List.take_left' rfl

theorem take_expand_pre (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (expand ℓ v).take (cutP ℓ v (k + 1) - 1) = expand ℓ (v.take k) ++ v[k] := by
  rw [expand_split ℓ v k hk, ← List.append_assoc]
  refine List.take_left' ?_
  rw [cutP_succ ℓ v k hk]; simp [cutP]

theorem cutP_succ_pos (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    1 ≤ cutP ℓ v (k + 1) := by
  rw [cutP_succ ℓ v k hk]; omega

theorem cutP_succ_strictMono (v : List (List Γ)) {k m : ℕ} (hkm : k < m) (hm : m < v.length) :
    cutP ℓ v (k + 1) < cutP ℓ v (m + 1) := by
  have h1 := cutP_succ ℓ v m hm
  have h2 := cutP_mono ℓ v (show k + 1 ≤ m by omega)
  omega

theorem der_core_succ_eq (v : List (List Γ)) (k : ℕ) (hk : k < v.length) :
    (der D ℓ).core v (k + 1) = some (D.core (expand ℓ v) (cutP ℓ v (k + 1) - 1)) := by
  rw [der_core_succ D ℓ v k hk, fcore_core D ℓ v k hk, core_eq_kst, take_expand_pre ℓ v k hk]

/-- Lift the start-core predicate, marking the new initial core as a start core. -/
def stLift (st : C → Bool) : Option C → Bool
  | none => true
  | some c => st c

theorem stLift_closed (st : C → Bool) (hcl : ∀ c a, st c = false → st (D.κ a c) = false) :
    ∀ (c : Option C) (X : List Γ), stLift st c = false → stLift st ((der D ℓ).κ X c) = false
  | none, _, h => absurd h (by simp [stLift])
  | some c, X, h => by
      simp only [der_κ, fcore, stLift] at h ⊢
      have key : ∀ (w : List Γ) (c : C), st c = false → st (kst D c w) = false := by
        intro w
        induction w with
        | nil => exact fun _ h => h
        | cons a w ih => exact fun c h => ih _ (hcl c a h)
      exact key _ _ h

variable [DecidableEq Γ]

theorem count_expand {v : List (List Γ)} (hv : ∀ X ∈ v, ℓ ∉ X) :
    (expand ℓ v).count ℓ = v.length := by
  induction v with
  | nil => simp
  | cons X v ih =>
    rw [expand_cons, List.count_append, List.count_cons_self,
      List.count_eq_zero.mpr (hv X List.mem_cons_self),
      ih (fun Y hY => hv Y (List.mem_cons_of_mem _ hY))]
    simp

theorem count_take_expand {v : List (List Γ)} (hv : ∀ X ∈ v, ℓ ∉ X) {k : ℕ} (hk : k < v.length)
    (s : ℕ) : k + 1 ≤ ((expand ℓ v).take s).count ℓ ↔ cutP ℓ v (k + 1) ≤ s := by
  have hvt : ∀ m, ∀ X ∈ v.take m, ℓ ∉ X := fun m X hX => hv X (List.mem_of_mem_take hX)
  constructor
  · intro h
    by_contra hlt
    have hle : s ≤ cutP ℓ v (k + 1) - 1 := by omega
    obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := expand ℓ v) hle
    have h1 : ((expand ℓ v).take s).count ℓ ≤
        ((expand ℓ v).take (cutP ℓ v (k + 1) - 1)).count ℓ := by
      rw [← ht, List.count_append]; omega
    rw [take_expand_pre ℓ v k hk, List.count_append, count_expand ℓ (hvt k),
      List.count_eq_zero.mpr (hv _ (List.getElem_mem hk)), List.length_take,
      Nat.min_eq_left (by omega)] at h1
    omega
  · intro h
    obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := expand ℓ v) h
    rw [← ht, List.count_append, take_expand_cutP, count_expand ℓ (hvt _), List.length_take,
      Nat.min_eq_left (by omega)]
    omega

theorem startCores_der (st : C → Bool) (v : List (List Γ)) (hℓ : ∀ X ∈ v, ℓ ∉ X) (s : ℕ)
    (hpre : ∀ x < (expand ℓ v).length, st (D.core (expand ℓ v) x) = true ↔ x < s) :
    ∀ x < v.length, stLift st ((der D ℓ).core v x) = true ↔
      x < min v.length (1 + ((expand ℓ v).take s).count ℓ) := by
  intro x hx
  rcases x with _ | k
  · simp [der_core_zero, stLift]; omega
  · rw [der_core_succ_eq D ℓ v k (by omega)]
    simp only [stLift]
    have hlt : cutP ℓ v (k + 1) - 1 < (expand ℓ v).length := by
      have := cutP_le_length ℓ v (k + 1)
      have := cutP_succ_pos ℓ v k (by omega)
      omega
    rw [hpre _ hlt]
    have := count_take_expand ℓ hℓ (k := k) (by omega) s
    have := cutP_succ_pos ℓ v k (by omega)
    constructor
    · intro h; exact lt_min hx (by omega)
    · intro h; have := lt_of_lt_of_le h (min_le_right _ _); omega

omit [DecidableEq Γ] in

theorem startCores_der_distinct (st : C → Bool) (v : List (List Γ))
    (hdist : ∀ x y, x < (expand ℓ v).length → y < (expand ℓ v).length →
      st (D.core (expand ℓ v) x) = true → st (D.core (expand ℓ v) y) = true → x ≠ y →
      D.core (expand ℓ v) x ≠ D.core (expand ℓ v) y) :
    ∀ x y, x < v.length → y < v.length → stLift st ((der D ℓ).core v x) = true →
      stLift st ((der D ℓ).core v y) = true → x ≠ y →
      (der D ℓ).core v x ≠ (der D ℓ).core v y := by
  have hlt : ∀ k, k < v.length → cutP ℓ v (k + 1) - 1 < (expand ℓ v).length := by
    intro k hk
    have := cutP_le_length ℓ v (k + 1)
    have := cutP_succ_pos ℓ v k hk
    omega
  intro x y hx hy hsx hsy hxy
  rcases x with _ | k <;> rcases y with _ | m
  · exact absurd rfl hxy
  · rw [der_core_zero, der_core_succ_eq D ℓ v m (by omega)]; simp
  · rw [der_core_zero, der_core_succ_eq D ℓ v k (by omega)]; simp
  · rw [der_core_succ_eq D ℓ v k (by omega)] at hsx ⊢
    rw [der_core_succ_eq D ℓ v m (by omega)] at hsy ⊢
    simp only [stLift] at hsx hsy
    simp only [ne_eq, Option.some.injEq]
    refine hdist _ _ (hlt k (by omega)) (hlt m (by omega)) hsx hsy ?_
    have h1 := cutP_succ_pos ℓ v k (by omega)
    have h2 := cutP_succ_pos ℓ v m (by omega)
    rcases Nat.lt_or_gt_of_ne (show k ≠ m by omega) with h | h
    · have := cutP_succ_strictMono ℓ v h (by omega); omega
    · have := cutP_succ_strictMono ℓ v h (by omega); omega

end StartOne

section StartTower
universe u v
variable {α : Type u} {Q : Type v}

/-- Recognise the start cores introduced by repeated derivation. -/
def isStart : (i : ℕ) → Cores Q i → Bool
  | 0, _ => false
  | i + 1, c => stLift (isStart i) c

theorem countP_range_lt (n s : ℕ) :
    (List.range n).countP (fun x => decide (x < s)) = min s n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : n < s <;> simp [h] <;> omega

theorem countP_range_of_prefix {n s : ℕ} {p : ℕ → Bool} (hs : s ≤ n)
    (hp : ∀ x < n, p x = true ↔ x < s) : (List.range n).countP p = s := by
  rw [List.countP_congr (q := fun x => decide (x < s)) (fun x hx => by
    rw [List.mem_range] at hx; simp [hp x hx]), countP_range_lt, Nat.min_eq_left hs]

variable [DecidableEq α] [Inhabited α]

/-- The number of start-core positions in a canonical hierarchy level. -/
def sCount (D0 : Lettered α Q) (w : List α) (j : ℕ) : ℕ :=
  (List.range (hierOf w j).length).countP
    (fun x => isStart j ((tower D0 (markOf w) j).core (hierOf w j) x))

/--
Start cores occupy an initial segment of distinct cores, and transitions from ordinary cores
remain ordinary.
-/
theorem lemma41 (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) : ∀ j,
    (∀ x < (hierOf w j).length,
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) x) = true ↔ x < sCount D0 w j) ∧
    sCount D0 w j ≤ (hierOf w j).length ∧
    (∀ x y, x < (hierOf w j).length → y < (hierOf w j).length →
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) x) = true →
      isStart j ((tower D0 (markOf w) j).core (hierOf w j) y) = true → x ≠ y →
      (tower D0 (markOf w) j).core (hierOf w j) x ≠
        (tower D0 (markOf w) j).core (hierOf w j) y) ∧
    (∀ c a, isStart j c = false → isStart j ((tower D0 (markOf w) j).κ a c) = false)
  | 0 => by
      have h0 : sCount D0 w 0 = 0 := by simp [sCount, isStart]
      refine ⟨fun x _ => by simp [h0, isStart], by omega, fun x y _ _ hx => by
        simp [isStart] at hx, fun _ _ _ => rfl⟩
  | j + 1 => by
      obtain ⟨hpre, hsle, hdist, hcl⟩ := lemma41 D0 hw j
      have hu := expand_hierOf hw j
      set s' := min (hierOf w (j + 1)).length
        (1 + ((hierOf w j).take (sCount D0 w j)).count (markOf w j)) with hs'
      have hpre' : ∀ x < (hierOf w (j + 1)).length,
          isStart (j + 1) ((tower D0 (markOf w) (j + 1)).core (hierOf w (j + 1)) x) = true ↔
            x < s' := by
        have := startCores_der (tower D0 (markOf w) j) (markOf w j) (isStart j)
          (hierOf w (j + 1)) (avoid_hierOf j) (sCount D0 w j) (by rw [hu]; exact hpre)
        rw [hu] at this
        exact this
      have hseq : sCount D0 w (j + 1) = s' :=
        countP_range_of_prefix (min_le_left _ _) hpre'
      refine ⟨by rw [hseq]; exact hpre', by rw [hseq]; exact min_le_left _ _, ?_, ?_⟩
      · have := startCores_der_distinct (tower D0 (markOf w) j) (markOf w j) (isStart j)
          (hierOf w (j + 1)) (by rw [hu]; exact hdist)
        exact this
      · exact stLift_closed (tower D0 (markOf w) j) (markOf w j) (isStart j) hcl

theorem sCount_zero (D0 : Lettered α Q) (w : List α) : sCount D0 w 0 = 0 := by
  simp [sCount, isStart]

theorem sCount_succ (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) = min (hierOf w (j + 1)).length
      (1 + ((hierOf w j).take (sCount D0 w j)).count (markOf w j)) := by
  have hu := expand_hierOf hw j
  obtain ⟨hpre, -, -, -⟩ := lemma41 D0 hw j
  refine countP_range_of_prefix (min_le_left _ _) ?_
  have := startCores_der (tower D0 (markOf w) j) (markOf w j) (isStart j)
    (hierOf w (j + 1)) (avoid_hierOf j) (sCount D0 w j) (by rw [hu]; exact hpre)
  rw [hu] at this
  exact this

end StartTower

section Transfer
variable {Γ C Γ' C' : Type*}

/-- A core occurs before the end of the given word. -/
def UsedCore (D : Lettered Γ C) (v : List Γ) (c : C) : Prop := ∃ x < v.length, D.core v x = c

/-- A label is initial or consists of a used core and an occurring letter. -/
def UsedLab (D : Lettered Γ C) (v : List Γ) : Lab Γ C → Prop
  | none => True
  | some (c, a) => UsedCore D v c ∧ a ∈ v

/-- Map both the letter and core components of a label. -/
def mapLab (φ : Γ' → Γ) (ψ : C' → C) (L : Lab Γ' C') : Lab Γ C := L.map (Prod.map ψ φ)

/-- A correspondence preserving letters, used cores, admission and targets along two words. -/
structure ConfIso (E : Lettered Γ' C') (v' : List Γ') (D : Lettered Γ C) (v : List Γ) where

  φ : Γ' → Γ

  ψ : C' → C
  letters_inj : ∀ a ∈ v', ∀ b ∈ v', φ a = φ b → a = b
  letters_onto : ∀ a, a ∈ v ↔ ∃ b ∈ v', φ b = a
  cores_inj : ∀ c d, UsedCore E v' c → UsedCore E v' d → ψ c = ψ d → c = d
  cores_onto : ∀ c, UsedCore D v c ↔ ∃ d, UsedCore E v' d ∧ ψ d = c
  start : ψ E.start = D.start
  κ_comm : ∀ c a, UsedCore E v' c → a ∈ v' → UsedCore E v' (E.κ a c) →
    ψ (E.κ a c) = D.κ (φ a) (ψ c)
  tf : ∀ c a, UsedCore E v' c → a ∈ v' → (E.Tf c a ↔ D.Tf (ψ c) (φ a))
  Λ : ∀ L L', UsedLab E v' L → UsedLab E v' L' →
    (E.Λ L L' ↔ D.Λ (mapLab φ ψ L) (mapLab φ ψ L'))
  Λf : ∀ L L', UsedLab E v' L → UsedLab E v' L' →
    (E.Λf L L' ↔ D.Λf (mapLab φ ψ L) (mapLab φ ψ L'))

end Transfer

section Pumping
universe u v
variable {α : Type u} {Q : Type v}

theorem mem_expand {Γ : Type*} {ℓ a : Γ} {v : List (List Γ)} :
    a ∈ expand ℓ v ↔ ∃ X ∈ v, a ∈ X ++ [ℓ] := by
  simp [expand, List.mem_flatMap]

theorem admissible_of_subset (ℓ : (i : ℕ) → Alph α i) : ∀ (j : ℕ) (v v₀ : List (Alph α j)),
    Admissible ℓ j v₀ → v₀ ≠ [] → (∀ a ∈ v, a ∈ v₀) → Admissible ℓ j v
  | 0, _, _, _, _, _ => trivial
  | j + 1, v, v₀, ⟨hav, had⟩, hv₀, hsub => by
      refine ⟨fun X hX => hav X (hsub X hX), admissible_of_subset ℓ j _ _ had
        (by simpa [expand_eq_nil] using hv₀) ?_⟩
      intro a ha
      obtain ⟨X, hX, haX⟩ := mem_expand.mp ha
      rw [List.mem_append, List.mem_singleton] at haX
      rcases haX with haX | rfl
      · exact mem_expand.mpr ⟨X, hsub X hX, List.mem_append_left _ haX⟩
      · obtain ⟨Y, hY⟩ := List.exists_mem_of_ne_nil v₀ hv₀
        exact mem_expand.mpr ⟨Y, hY, by simp⟩

/-- Lift a map of hierarchy alphabets through further list levels. -/
def liftMap {j j' : ℕ} (φ : Alph α j' → Alph α j) : (r : ℕ) → Alph α (j' + r) → Alph α (j + r)
  | 0 => φ
  | r + 1 => List.map (liftMap φ r)

variable [DecidableEq α] [Inhabited α]

theorem map_inj_on {β γ : Type*} {f : β → γ} {S : List β} (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b) :
    ∀ {X Y : List β}, (∀ a ∈ X, a ∈ S) → (∀ a ∈ Y, a ∈ S) → X.map f = Y.map f → X = Y
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: X, b :: Y, hX, hY, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      rw [hf a (hX a List.mem_cons_self) b (hY b List.mem_cons_self) h.1,
        map_inj_on hf (fun c hc => hX c (List.mem_cons_of_mem _ hc))
          (fun c hc => hY c (List.mem_cons_of_mem _ hc)) h.2]

omit [DecidableEq α] [Inhabited α] in
theorem tower_congr (D0 : Lettered α Q) {ℓ ℓ' : (i : ℕ) → Alph α i} :
    ∀ i, (∀ k < i, ℓ k = ℓ' k) → tower D0 ℓ i = tower D0 ℓ' i
  | 0, _ => rfl
  | i + 1, h => by
      show der (tower D0 ℓ i) (ℓ i) = der (tower D0 ℓ' i) (ℓ' i)
      rw [tower_congr D0 i (fun k hk => h k (by omega)), h i (by omega)]

end Pumping

section Bounded
universe u v
variable {α : Type u}

/-- All letters occurring in the word are equal. -/
def IsUnary {β : Type*} (u : List β) : Prop := ∀ a ∈ u, ∀ b ∈ u, a = b

/-- Every comparison ending before the last position leaves a suffix of length at most `h`. -/
def HorizonLE {β : Type*} (u : List β) (h : ℕ) : Prop :=
  ∀ s e, IsComp u s e → e < u.length → u.length - e ≤ h

variable [DecidableEq α] [Inhabited α]

/-- Some level at depth at most `d` is unary or has comparison horizon at most `h`. -/
def InL (d h : ℕ) (w : List α) : Prop :=
  ∃ i ≤ d, IsUnary (hierOf w i) ∨ HorizonLE (hierOf w i) h

theorem core_replicate {Γ C : Type*} (D : Lettered Γ C) (x : Γ) (m : ℕ) :
    ∀ k ≤ m, D.core (List.replicate m x) k = (D.κ x)^[k] D.start := by
  intro k hk
  rw [core_eq_kst, List.take_replicate, Nat.min_eq_left hk]
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', kst_append, ih m (by omega), Function.iterate_succ_apply']
    rfl

theorem iterate_small {C : Type*} [Fintype C] (f : C → C) (c : C) :
    ∀ n, ∃ t, t ≤ n ∧ t < Fintype.card C ∧ f^[t] c = f^[n] c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < Fintype.card C
    · exact ⟨n, le_rfl, hn, rfl⟩
    · obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun i : Fin (Fintype.card C + 1) => f^[i.1] c) (by simp)
      have key : ∀ a b : Fin (Fintype.card C + 1), a.1 < b.1 → f^[a.1] c = f^[b.1] c →
          ∃ t, t ≤ n ∧ t < Fintype.card C ∧ f^[t] c = f^[n] c := by
        intro a b hlt he
        have hb := b.2
        obtain ⟨t, ht, htC, hte⟩ := ih (n - (b.1 - a.1)) (by omega)
        refine ⟨t, by omega, htC, ?_⟩
        rw [hte]
        have h1 : n = (n - b.1) + b.1 := by omega
        have h2 : n - (b.1 - a.1) = (n - b.1) + a.1 := by omega
        rw [h2, h1, Function.iterate_add_apply, Function.iterate_add_apply, he]
        congr 1
        omega
      rcases Nat.lt_or_gt_of_ne (fun h => hab (Fin.ext h)) with h | h
      · exact key a b h he
      · exact key b a h he.symm

/-- A unary hole exists exactly when one exists below the finite core-cardinality bound. -/
theorem exists_unary_hole_iff {Γ C : Type*} [Fintype C] (D : Lettered Γ C) (x : Γ) :
    (∃ m, D.IsHole (List.replicate m x)) ↔
      ∃ m, 1 ≤ m ∧ m ≤ Fintype.card C ∧ D.IsHole (List.replicate m x) := by
  refine ⟨fun ⟨m, hm⟩ => ?_, fun ⟨m, _, _, hm⟩ => ⟨m, hm⟩⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exact absurd rfl hm.ne_nil
    · exact ⟨m', rfl⟩
  obtain ⟨t, ht, htC, hte⟩ := iterate_small (D.κ x) D.start m'
  refine ⟨t + 1, by omega, by omega, ?_⟩

  have hsplit : List.replicate (m' + 1) x =
      List.replicate (t + 1) x ++ List.replicate (m' + 1 - (t + 1)) x := by
    rw [← List.replicate_add]; congr 1; omega
  have hlab : ∀ k ≤ t + 1,
      D.label (List.replicate (t + 1) x) k = D.label (List.replicate (m' + 1) x) k := by
    intro k hk
    rw [label_eq_labFrom, label_eq_labFrom, hsplit,
      labFrom_append_le D _ _ _ (by simpa using hk)]
  have hfin : D.label (List.replicate (t + 1) x) (t + 1) =
      D.label (List.replicate (m' + 1) x) (m' + 1) := by
    rw [Lettered.label_succ _ _ (by simp), Lettered.label_succ _ _ (by simp),
      core_replicate D x _ t (by omega), core_replicate D x _ m' (by omega), hte]
    simp
  obtain ⟨⟨c, a, hl, hT⟩, hE, hI⟩ := hm
  simp only [List.length_replicate] at hl hE hI
  refine ⟨⟨c, a, ?_, hT⟩, fun s hs => ?_, fun s e hc he => ?_⟩
  · rw [List.length_replicate, hfin, hl]
  · rw [List.length_replicate] at hs ⊢
    rw [hfin, hlab s hs.le]
    exact hE s (by omega)
  · rw [List.length_replicate] at he
    have he1 : e ≤ t + 1 := by simpa using hc.2.1
    have hc' : IsComp (List.replicate (m' + 1) x) s e := by
      refine ⟨hc.1, by simp; omega, ?_⟩
      rw [List.drop_replicate, List.drop_replicate,
        show m' + 1 - s = (m' + 1 - e) + (e - s) by have := hc.1; omega, List.replicate_add]
      exact List.prefix_append _ _
    rw [hlab s (by have := hc.1; omega), hlab e he.le]
    exact hI s e hc' (by omega)

end Bounded

section Reader
universe u v
variable {α : Type u} {Q : Type v}

/-- Recover the reader state from an initial or core-and-letter label. -/
def stOf (M : DFA α Q) : Lab α Q → Q
  | none => M.start
  | some (c, a) => M.step c a

/-- The reader's admission relation expressed on core-and-letter labels. -/
def readerΛ (M : DFA α Q) (R : Q → Q → Prop) : Lab α Q → Lab α Q → Prop
  | _, none => False
  | L, some p => R (stOf M L) (stOf M (some p))

/-- View an ordinary finite reader as a lettered monitor. -/
def ofReader (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) : Lettered α Q where
  start := M.start
  κ a c := M.step c a
  Λ := readerΛ M R
  Λf := readerΛ M R
  Tf c a := M.step c a ∈ T

@[simp] theorem ofReader_Λ (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) :
    (ofReader M R T).Λ = readerΛ M R := rfl
@[simp] theorem ofReader_Λf (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) :
    (ofReader M R T).Λf = readerΛ M R := rfl
@[simp] theorem ofReader_Tf (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (c : Q) (a : α) :
    (ofReader M R T).Tf c a = (M.step c a ∈ T) := rfl

theorem core_ofReader (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) (x : ℕ) :
    (ofReader M R T).core w x = runG M w x := rfl

theorem stOf_label (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (w : List α) :
    ∀ x ≤ w.length, stOf M ((ofReader M R T).label w x) = runG M w x
  | 0, _ => rfl
  | x + 1, hx => by
      rw [Lettered.label_succ _ _ (by omega), stOf, core_ofReader, runG, runG,
        List.take_succ_eq_append_getElem (by omega), DFA.eval_append_singleton]

/-- For nonempty words, lettered-reader holes and ordinary reader holes coincide. -/
theorem isHole_ofReader_iff (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) {w : List α}
    (hw : w ≠ []) : (ofReader M R T).IsHole w ↔ AbsHoleG M R T w := by
  obtain ⟨j, hlen⟩ : ∃ j, w.length = j + 1 :=
    ⟨w.length - 1, by have := List.length_pos_iff.mpr hw; omega⟩
  have hst := stOf_label M R T w
  have hlab : (ofReader M R T).label w w.length = some (runG M w j, w[j]) := by
    rw [← core_ofReader M R T]; simp only [hlen]; exact Lettered.label_succ _ w (by omega)
  have hfin : M.step (runG M w j) w[j] = runG M w w.length := by
    have := hst _ le_rfl
    rw [hlab] at this
    exact this
  have hfin' : stOf M (some (runG M w j, w[j])) = runG M w w.length := hfin
  rw [absHoleG_iff_split]
  unfold Lettered.IsHole
  rw [hlab, exists_some_eq_iff]
  refine and_congr (by rw [ofReader_Tf, hfin]) (and_congr ?_ ?_)
  · constructor
    · rintro h ⟨p, ⟨i, hi, hp⟩, hr⟩
      refine h i hi ?_
      rw [ofReader_Λf]
      show R (stOf M ((ofReader M R T).label w i)) (stOf M (some (runG M w j, w[j])))
      rw [hst i hi.le, hfin']
      have : runG M w i = p := hp
      rw [this]; exact hr
    · intro h s hs hr
      rw [ofReader_Λf] at hr
      change R (stOf M ((ofReader M R T).label w s)) (stOf M (some (runG M w j, w[j]))) at hr
      rw [hst s hs.le, hfin'] at hr
      exact h ⟨_, ⟨s, hs, rfl⟩, hr⟩
  · constructor
    · intro h s e hse he hc hr
      refine h s e ⟨hse, he.le, hc⟩ he ?_
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rw [ofReader_Λ, Lettered.label_succ _ _ (by omega)]
      show R (stOf M ((ofReader M R T).label w s)) (stOf M (some ((ofReader M R T).core w e', w[e'])))
      rw [← Lettered.label_succ _ _ (by omega), hst s (by omega), hst _ (by omega)]
      exact hr
    · intro h s e hc he hr
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by have := hc.1; omega⟩
      rw [ofReader_Λ, Lettered.label_succ _ _ (by omega)] at hr
      change R (stOf M ((ofReader M R T).label w s))
        (stOf M (some ((ofReader M R T).core w e', w[e']))) at hr
      rw [← Lettered.label_succ _ _ (by omega), hst s (by have := hc.1; omega),
        hst _ (by omega)] at hr
      exact h s (e' + 1) hc.1 he hc.2.2 hr

end Reader

end DeciNSSE.LetteredHierarchy
