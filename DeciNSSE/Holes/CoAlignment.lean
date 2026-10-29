import DeciNSSE.Holes.Basic

/-! # Lettered monitors and comparison alignment

Lettered monitors distinguish current cores and letters. A letter map that
introduces no new boundary comparison preserves the hole condition.
-/

set_option autoImplicit false

namespace DeciNSSE.CoAlignment
open DeciNSSE.Holes
open scoped List

section Comparisons
variable {α β : Type*}

/-- A comparison `(s,e)` of `u`: `s < e ≤ |u|` and `u[e:] ⪯ u[s:]`. -/
def IsComp (u : List α) (s e : ℕ) : Prop := s < e ∧ e ≤ u.length ∧ u.drop e <+: u.drop s

/-- One step to the left: for `a < b < |u|`, `u[b:] ⪯ u[a:]` iff the letters agree and
`u[b+1:] ⪯ u[a+1:]`. -/
theorem drop_prefix_iff_succ (u : List α) {a b : ℕ} (hab : a < b) (hb : b < u.length) :
    u.drop b <+: u.drop a ↔ u[b] = u[a] ∧ u.drop (b + 1) <+: u.drop (a + 1) := by
  rw [List.drop_eq_getElem_cons hb, List.drop_eq_getElem_cons (by omega : a < u.length),
    List.cons_prefix_cons]

/-- Letter maps preserve comparisons. -/
theorem IsComp.map (f : α → β) {u : List α} {s e : ℕ} (h : IsComp u s e) :
    IsComp (u.map f) s e := by
  obtain ⟨hse, he, hc⟩ := h
  refine ⟨hse, by simpa using he, ?_⟩
  rw [← List.map_drop, ← List.map_drop]
  exact hc.map f

/-- Collapse. A comparison of `f(u)` that is not a comparison of `u` extends to a
left-maximal comparison `(s+1, e+1)` of `u` whose boundary letters are distinct with
equal `f`-images (the rightmost mismatch). -/
theorem exists_collapse (f : α → β) (u : List α) :
    ∀ k a b, u.length - b = k → a < b → b ≤ u.length →
      (u.map f).drop b <+: (u.map f).drop a → ¬ u.drop b <+: u.drop a →
      ∃ s e, ∃ (hs : s < u.length) (he : e < u.length), s < e ∧
        IsComp u (s + 1) (e + 1) ∧ u[s] ≠ u[e] ∧ f u[s] = f u[e] := by
  intro k
  induction k with
  | zero =>
    intro a b hk hab hb _ hn
    exact absurd (by rw [show b = u.length by omega]; simp) hn
  | succ k ih =>
    intro a b hk hab hb hm hn
    have hb' : b < u.length := by omega
    have hmb : b < (u.map f).length := by simpa using hb'
    rw [drop_prefix_iff_succ (u.map f) hab hmb] at hm
    simp only [List.getElem_map] at hm
    obtain ⟨hfe, hm⟩ := hm
    by_cases hc : u.drop (b + 1) <+: u.drop (a + 1)
    · refine ⟨a, b, by omega, hb', hab, ⟨by omega, by omega, hc⟩, ?_, hfe.symm⟩
      intro hab'
      exact hn ((drop_prefix_iff_succ u hab hb').mpr ⟨hab'.symm, hc⟩)
    · exact ih (a + 1) (b + 1) (by omega) (by omega) (by omega) hm hc

/-- General identification lemma. If a letter map `f` collapses no boundary pair of a
left-maximal comparison of `u`, then `f(u)` has exactly the comparisons of `u`. -/
theorem isComp_map_iff (f : α → β) (u : List α)
    (hf : ∀ s e (hs : s < u.length) (he : e < u.length), s < e →
      IsComp u (s + 1) (e + 1) → f u[s] = f u[e] → u[s] = u[e])
    (s e : ℕ) : IsComp (u.map f) s e ↔ IsComp u s e := by
  refine ⟨fun h => ?_, IsComp.map f⟩
  obtain ⟨hse, he, hc⟩ := h
  have he' : e ≤ u.length := by simpa using he
  refine ⟨hse, he', ?_⟩
  by_contra hn
  obtain ⟨s', e', hs', he'', hlt, hcomp, hne, hfe⟩ :=
    exists_collapse f u _ s e rfl hse he' hc hn
  exact hne (hf s' e' hs' he'' hlt hcomp hfe)

variable [DecidableEq α]

end Comparisons

/-- Labels: `none` is the label `S` of cut 0; `some (c, a)` is the letter `a` read from
core `c`. -/
abbrev Lab (Γ C : Type*) := Option (C × Γ)

/-- A monitor with core transitions, interior and terminal admissions, and a final target. -/
structure Lettered (Γ C : Type*) where
  /-- The initial core. -/
  start : C
  /-- The core transition on a letter. -/
  κ : Γ → C → C
  /-- Admission for comparisons ending before the terminal cut. -/
  Λ : Lab Γ C → Lab Γ C → Prop
  /-- Admission for comparisons ending at the terminal cut. -/
  Λf : Lab Γ C → Lab Γ C → Prop
  /-- The target condition on the final core and letter. -/
  Tf : C → Γ → Prop

namespace Lettered
variable {Γ C : Type*} (D : Lettered Γ C)

/-- The core reader. -/
def coreDFA : DFA Γ C where
  step c a := D.κ a c
  start := D.start
  accept := ∅

/-- The core run: `c_0 = ⋆`, `c_{x+1} = κ(v_x, c_x)`. -/
def core (v : List Γ) (x : ℕ) : C := runPrefix D.coreDFA v x

/-- The label of cut `x`: `L_0 = S`, `L_{x+1} = (c_x, v_x)`. -/
def label (v : List Γ) : ℕ → Lab Γ C
  | 0 => none
  | x + 1 => (v[x]?).map fun a => (D.core v x, a)

theorem label_succ (v : List Γ) {x : ℕ} (hx : x < v.length) :
    D.label v (x + 1) = some (D.core v x, v[x]) := by
  simp [label, List.getElem?_eq_getElem hx]

/-- The final label is a target and no interior or terminal comparison is admitted. -/
def IsHole (v : List Γ) : Prop :=
  (∃ c a, D.label v v.length = some (c, a) ∧ D.Tf c a) ∧
    (∀ s, s < v.length → ¬ D.Λf (D.label v s) (D.label v v.length)) ∧
    (∀ s e, IsComp v s e → e < v.length → ¬ D.Λ (D.label v s) (D.label v e))

theorem IsHole.ne_nil {D : Lettered Γ C} {v : List Γ} (h : D.IsHole v) : v ≠ [] := by
  rintro rfl
  obtain ⟨⟨c, a, hl, -⟩, -⟩ := h
  simp [label] at hl

variable [DecidableEq Γ]

end Lettered

end DeciNSSE.CoAlignment

namespace DeciNSSE.CoAlignment
open DeciNSSE.Holes
open scoped List
section
variable {α β : Type*}
/-- A comparison whose unequal predecessor letters prevent extending it to the left. -/
def IsLeftMax (u : List α) (s e : ℕ) : Prop :=
  IsComp u s e ∧ 1 ≤ s ∧ u[s - 1]? ≠ u[e - 1]?

/-- Distinct letters bounding a left-maximal comparison, including terminal comparisons. -/
def CoAligned (u : List α) (x y : α) : Prop :=
  x ≠ y ∧ ∃ s e, IsLeftMax u s e ∧
    ((u[s - 1]? = some x ∧ u[e - 1]? = some y) ∨ (u[s - 1]? = some y ∧ u[e - 1]? = some x))

/-- Distinct letters bounding a nonterminal left-maximal comparison. -/
def CoAlignedNT (u : List α) (x y : α) : Prop :=
  x ≠ y ∧ ∃ s e, IsLeftMax u s e ∧ e < u.length ∧
    ((u[s - 1]? = some x ∧ u[e - 1]? = some y) ∨ (u[s - 1]? = some y ∧ u[e - 1]? = some x))

theorem CoAligned.symm {u : List α} {x y : α} (h : CoAligned u x y) : CoAligned u y x := by
  obtain ⟨hxy, s, e, hl, h⟩ := h
  exact ⟨fun h' => hxy h'.symm, s, e, hl, h.symm⟩

theorem coAligned_comm {u : List α} {x y : α} : CoAligned u x y ↔ CoAligned u y x :=
  ⟨CoAligned.symm, CoAligned.symm⟩

/-- A co-alignment avoiding the final letter must be nonterminal. -/
theorem coAlignedNT_of_coAligned {u : List α} {x y : α} (h : CoAligned u x y)
    (hx : u.getLast? ≠ some x) (hy : u.getLast? ≠ some y) : CoAlignedNT u x y := by
  obtain ⟨hxy, s, e, ⟨⟨hse, he, hc⟩, hs1, hne⟩, hb⟩ := h
  refine ⟨hxy, s, e, ⟨⟨hse, he, hc⟩, hs1, hne⟩, ?_, hb⟩
  rcases Nat.lt_or_ge e u.length with h' | h'
  · exact h'
  · have hn : e = u.length := le_antisymm he h'
    subst hn
    rw [List.getLast?_eq_getElem?] at hx hy
    rcases hb with ⟨-, hb⟩ | ⟨-, hb⟩
    · exact absurd hb hy
    · exact absurd hb hx

/-- Protecting the final letter excludes terminal co-alignments between unprotected letters. -/
theorem not_coAligned_of_not_NT {u : List α} {Z : Set α}
    (hlast : ∀ c, u.getLast? = some c → c ∈ Z) {a b : α} (ha : a ∉ Z) (hb : b ∉ Z)
    (h : ¬ CoAlignedNT u a b) : ¬ CoAligned u a b := fun hco =>
  h (coAlignedNT_of_coAligned hco (fun h' => ha (hlast a h')) (fun h' => hb (hlast b h')))

theorem isComp_end (u : List α) {s : ℕ} (hs : s < u.length) : IsComp u s u.length :=
  ⟨hs, le_rfl, by simp⟩

/-- Unequal predecessor letters of a comparison are co-aligned. -/
theorem coAligned_of_comp {u : List α} {s e : ℕ} (hs : s < u.length) (he : e < u.length)
    (hc : IsComp u (s + 1) (e + 1)) (hne : u[s] ≠ u[e]) : CoAligned u u[s] u[e] := by
  refine ⟨hne, s + 1, e + 1, ⟨hc, by omega, ?_⟩, Or.inl ⟨?_, ?_⟩⟩
  · simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem he,
      ne_eq, Option.some.injEq]
    exact hne
  · simp [List.getElem?_eq_getElem hs]
  · simp [List.getElem?_eq_getElem he]

variable [DecidableEq α]

/-- Replace every occurrence of the first letter by the second. -/
def identify (a b : α) (z : α) : α := if z = a then b else z

@[simp] theorem identify_self_left (a b : α) : identify a b a = b := by simp [identify]

theorem identify_of_ne {a b z : α} (h : z ≠ a) : identify a b z = z := by
  simp [identify, h]

/-- Distinct letters identified by this map must be its source and target. -/
theorem identify_collapse {a b p q : α} (hpq : p ≠ q) (h : identify a b p = identify a b q) :
    (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
  unfold identify at h
  by_cases hp : p = a <;> by_cases hq : q = a <;> simp only [hp, hq, ite_true, ite_false] at h
  · exact absurd (hp.trans hq.symm) hpq
  · exact Or.inl ⟨hp, h.symm⟩
  · exact Or.inr ⟨h, hq⟩
  · exact absurd h hpq

/-- Identifying non-co-aligned letters preserves exactly the comparisons. -/
theorem isComp_identify_iff {u : List α} {x y : α} (h : ¬ CoAligned u x y) (s e : ℕ) :
    IsComp (u.map (identify y x)) s e ↔ IsComp u s e := by
  refine isComp_map_iff _ u (fun s e hs he _ hc hfe => ?_) s e
  by_contra hne
  rcases identify_collapse hne hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h (h1 ▸ h2 ▸ (coAligned_of_comp hs he hc hne).symm)
  · exact h (h1 ▸ h2 ▸ coAligned_of_comp hs he hc hne)

theorem isComp_identify_of_isComp {u : List α} {x y : α} {s e : ℕ} (h : IsComp u s e) :
    IsComp (u.map (identify y x)) s e :=
  h.map _

end
section
variable {α Q : Type*} [DecidableEq α]
/-- Equal transitions at the changed occurrences preserve every prefix state. -/
theorem runPrefix_identify (M : DFA α Q) (u : List α) (a b : α)
    (h : ∀ i (hi : i < u.length), u[i] = a → M.step (runPrefix M u i) a = M.step (runPrefix M u i) b) :
    ∀ i, runPrefix M (u.map (identify a b)) i = runPrefix M u i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [runPrefix] at ih ⊢
    rw [List.take_add_one, List.take_add_one, List.getElem?_map]
    rcases hi : u[i]? with _ | c
    · simpa using ih
    · obtain ⟨hlt, hci⟩ := List.getElem?_eq_some_iff.mp hi
      simp only [Option.map_some, Option.toList_some, DFA.eval_append_singleton, ih]
      by_cases hca : c = a
      · subst hca
        rw [identify_self_left]
        exact (h i hlt hci).symm
      · rw [identify_of_ne hca]

end
end DeciNSSE.CoAlignment

namespace DeciNSSE.CoAlignment
/-- Both endpoints of a nonterminal co-alignment occur in the word. -/
theorem coAlignedNT_mem {β : Type*} {u : List β} {a b : β} (h : CoAlignedNT u a b) :
    a ∈ u ∧ b ∈ u := by
  obtain ⟨-, s, e, -, -, hb⟩ := h
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨List.mem_of_getElem? h1, List.mem_of_getElem? h2⟩
  · exact ⟨List.mem_of_getElem? h2, List.mem_of_getElem? h1⟩
end DeciNSSE.CoAlignment
