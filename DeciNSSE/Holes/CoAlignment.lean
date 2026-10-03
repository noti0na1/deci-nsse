import DeciNSSE.Holes.Basic

/-! # Lettered monitors and comparison alignment

Comparisons are suffix-prefix relations between distinct positions. Lettered
monitors record a core together with the preceding letter; their
admission and target predicates support desubstitution of holes.
-/

namespace DeciNSSE.CoAlignment
open DeciNSSE.Holes

section Comparisons
variable {α β : Type*}

/-- A suffix-prefix comparison between two distinct positions of a word. -/
def IsComp (u : List α) (s e : ℕ) : Prop := s < e ∧ e ≤ u.length ∧ u.drop e <+: u.drop s

theorem drop_prefix_iff_succ (u : List α) {a b : ℕ} (hab : a < b) (hb : b < u.length) :
    u.drop b <+: u.drop a ↔ u[b] = u[a] ∧ u.drop (b + 1) <+: u.drop (a + 1) := by
  rw [List.drop_eq_getElem_cons hb, List.drop_eq_getElem_cons (by omega : a < u.length),
    List.cons_prefix_cons]

theorem IsComp.map (f : α → β) {u : List α} {s e : ℕ} (h : IsComp u s e) :
    IsComp (u.map f) s e := by
  obtain ⟨hse, he, hc⟩ := h
  refine ⟨hse, by simpa using he, ?_⟩
  rw [← List.map_drop, ← List.map_drop]
  exact hc.map f

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

/-- Identify one letter with another, leaving every other letter fixed. -/
def identify (a b : α) (z : α) : α := if z = a then b else z

@[simp] theorem identify_self_left (a b : α) : identify a b a = b := by simp [identify]

end Comparisons

/-- An initial label or a pair consisting of a core and the preceding letter. -/
abbrev Lab (Γ C : Type*) := Option (C × Γ)

/-- A core reader with separate admission relations for internal and final comparisons. -/
structure Lettered (Γ C : Type*) where

  /-- The initial core. -/
  start : C

  /-- The core transition associated with a letter. -/
  κ : Γ → C → C

  /-- Admission for comparisons ending before the final position. -/
  Λ : Lab Γ C → Lab Γ C → Prop

  /-- Admission for comparisons ending at the final position. -/
  Λf : Lab Γ C → Lab Γ C → Prop

  /-- The target predicate on the final core and letter. -/
  Tf : C → Γ → Prop

namespace Lettered
variable {Γ C : Type*} (D : Lettered Γ C)

/-- The deterministic automaton of core transitions, with no accepting states. -/
def coreDFA : DFA Γ C where
  step c a := D.κ a c
  start := D.start
  accept := ∅

/-- The core reached after the prefix ending at a given position. -/
def core (v : List Γ) (x : ℕ) : C := runG D.coreDFA v x

/-- The initial label at zero, or the preceding core and letter at a positive position. -/
def label (v : List Γ) : ℕ → Lab Γ C
  | 0 => none
  | x + 1 => (v[x]?).map fun a => (D.core v x, a)

theorem label_succ (v : List Γ) {x : ℕ} (hx : x < v.length) :
    D.label v (x + 1) = some (D.core v x, v[x]) := by
  simp [label, List.getElem?_eq_getElem hx]

/-- A nonempty target word without admitted internal or final comparisons. -/
def IsHole (v : List Γ) : Prop :=
  (∃ c a, D.label v v.length = some (c, a) ∧ D.Tf c a) ∧
    (∀ s, s < v.length → ¬ D.Λf (D.label v s) (D.label v v.length)) ∧
    (∀ s e, IsComp v s e → e < v.length → ¬ D.Λ (D.label v s) (D.label v e))

theorem IsHole.ne_nil {D : Lettered Γ C} {v : List Γ} (h : D.IsHole v) : v ≠ [] := by
  rintro rfl
  obtain ⟨⟨c, a, hl, -⟩, -⟩ := h
  simp [label] at hl

/--
Two letters have identical admission rows and columns on the specified sets of cores and
letters.
-/
structure PairRows (P : Lab Γ C → Lab Γ C → Prop) (Qo U : Set C) (Z : Set Γ) (x y : Γ) :
    Prop where
  self : ∀ q ∈ Qo, ∀ q' ∈ Qo, P (some (q, x)) (some (q', x)) ↔ P (some (q, y)) (some (q', y))
  left : ∀ q ∈ Qo, ∀ c ∈ U, ∀ z ∈ Z, P (some (q, x)) (some (c, z)) ↔ P (some (q, y)) (some (c, z))
  right : ∀ q ∈ Qo, ∀ c ∈ U, ∀ z ∈ Z,
    P (some (c, z)) (some (q, x)) ↔ P (some (c, z)) (some (q, y))
  /-- The initial core. -/
  start : ∀ q ∈ Qo, P none (some (q, x)) ↔ P none (some (q, y))

end Lettered

end DeciNSSE.CoAlignment
