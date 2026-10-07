import DeciNSSE.Satisfiability.Decide
import DeciNSSE.Semantics.Selector

/-! # Readiness and periodic admission events

Readiness is tested at every cut, including zero and the terminal cut. The
child test is letter-free and remains meaningful at the terminal cut and at
arity zero. Self-admission allows both orientations of sign-flipped labels;
sign coherence relates these events to the spine clash formulas.
-/

namespace DeciNSSE.Events

open FiniteVariance

variable {n K k : ℕ}

section Defs

variable (ψ : Constraint n K) (X Y : V K) (w : List (Fin n))

/-- `U_j = {v | UpperAt ψ (w.take j) X v}`. -/
def USet (j : ℕ) : Set (V K) := {v | UpperAt ψ (w.take j) X v}

/-- `L_j = {v | LowerAt ψ (w.take j) v Y}`. -/
def LSet (j : ℕ) : Set (V K) := {v | LowerAt ψ (w.take j) v Y}

/-- Readiness at cut `j` (letter-free): bot, top or reflexivity. -/
def Ready (j : ℕ) : Prop :=
  (∃ v ∈ USet ψ X w j, Lit.eqBot v ∈ ψ) ∨ (∃ v ∈ LSet ψ Y w j, Lit.eqTop v ∈ ψ) ∨
    (USet ψ X w j ∩ LSet ψ Y w j).Nonempty

/-- The letter-free child test at the end of the word. -/
def Child : Prop := ∃ v ∈ USet ψ X w w.length, ∃ b, Lit.leF v b ∈ ψ

/-- Cross admission at `(s, e)`: `L_s ∩ U_e ≠ ∅`. -/
def Cross (s e : ℕ) : Prop := (LSet ψ Y w s ∩ USet ψ X w e).Nonempty

/-- A readiness, terminal child, cross or self event occurs along the word. -/
def Occurs (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) : Prop :=
  (∃ j ≤ w.length, Ready ψ X Y w j) ∨ Child ψ X w ∨
    ∃ s e, s < e ∧ e ≤ w.length ∧ w.drop e <+: w.drop s ∧
      (Cross ψ X Y w s e ∨ (USet ψ X w s ∩ flipV '' USet ψ X w e).Nonempty)

end Defs

/-- Self admission at `(s, e)`: `U_s ∩ σ(U_e) ≠ ∅`. -/
def Self (ψ : Constraint n (2 * k)) (X : V (2 * k)) (w : List (Fin n)) (s e : ℕ) : Prop :=
  (USet ψ X w s ∩ flipV '' USet ψ X w e).Nonempty

theorem occurs_def (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) :
    Occurs ψ X Y w ↔ (∃ j ≤ w.length, Ready ψ X Y w j) ∨ Child ψ X w ∨
      ∃ s e, s < e ∧ e ≤ w.length ∧ w.drop e <+: w.drop s ∧
        (Cross ψ X Y w s e ∨ Self ψ X w s e) := Iff.rfl

theorem self_iff {ψ : Constraint n (2 * k)} {X : V (2 * k)} {w : List (Fin n)}
    {s e : ℕ} : Self ψ X w s e ↔ ∃ v, v ∈ USet ψ X w s ∧ flipV v ∈ USet ψ X w e := by
  constructor
  · rintro ⟨z, hz, v, hv, rfl⟩
    exact ⟨flipV v, hz, by simpa using hv⟩
  · rintro ⟨v, h₁, h₂⟩
    exact ⟨v, h₁, flipV v, h₂, flipV_flipV v⟩

section Words

variable {w : List (Fin n)}

theorem prefix_of_take_eq {a b d : ℕ} (ha : a + d = w.length)
    (h : (w.drop a).take d = (w.drop b).take d) : w.drop a <+: w.drop b := by
  have hl : (w.drop a).take d = w.drop a := List.take_of_length_le (by simp; omega)
  rw [← hl, h]
  exact List.take_prefix _ _

theorem take_eq_of_prefix {s e : ℕ} (h : w.drop e <+: w.drop s) :
    (w.drop e).take (w.length - e) = (w.drop s).take (w.length - e) := by
  have h1 : (w.drop e).take (w.length - e) = w.drop e := List.take_of_length_le (by simp)
  rw [h1]
  have h2 := List.prefix_iff_eq_take.mp h
  rw [List.length_drop] at h2
  exact h2

end Words

section Bool

variable (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n))

/-- Readiness at cut `j`, computably. -/
def readyB (j : ℕ) : Bool :=
  (List.finRange (2 * k)).any fun v =>
    (upperAtB ψ (w.take j) X v && decide (v ∈ botVars ψ)) ||
    (lowerAtB ψ (w.take j) v Y && decide (v ∈ topVars ψ)) ||
    (upperAtB ψ (w.take j) X v && lowerAtB ψ (w.take j) v Y)

/-- The child test, computably. -/
def childB : Bool :=
  (List.finRange (2 * k)).any fun v =>
    upperAtB ψ (w.take w.length) X v && (upperLits ψ).any fun p => decide (p.1 = v)

/-- Cross admission, computably. -/
def crossB (s e : ℕ) : Bool :=
  (List.finRange (2 * k)).any fun v => lowerAtB ψ (w.take s) v Y && upperAtB ψ (w.take e) X v

/-- Self admission, computably. -/
def selfB (s e : ℕ) : Bool :=
  (List.finRange (2 * k)).any fun v =>
    upperAtB ψ (w.take s) X v && upperAtB ψ (w.take e) X (flipV v)

/-- The events, computably. -/
def occursB : Bool :=
  (List.range (w.length + 1)).any (fun j => readyB ψ X Y w j) || childB ψ X w ||
    (List.range (w.length + 1)).any fun e => (List.range e).any fun s =>
      decide (w.drop e <+: w.drop s) && (crossB ψ X Y w s e || selfB ψ X w s e)

variable {ψ X Y w}

theorem readyB_iff (j : ℕ) : readyB ψ X Y w j = true ↔ Ready ψ X Y w j := by
  simp only [readyB, List.any_eq_true, List.mem_finRange, true_and, Bool.or_eq_true,
    Bool.and_eq_true, upperAtB_iff, lowerAtB_iff, decide_eq_true_eq, mem_botVars,
    mem_topVars, Ready, USet, LSet, Set.Nonempty, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) | ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨v, h₁, h₂⟩
    · exact Or.inr (Or.inl ⟨v, h₁, h₂⟩)
    · exact Or.inr (Or.inr ⟨v, h₁, h₂⟩)
  · rintro (⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩)
    · exact ⟨v, Or.inl (Or.inl ⟨h₁, h₂⟩)⟩
    · exact ⟨v, Or.inl (Or.inr ⟨h₁, h₂⟩)⟩
    · exact ⟨v, Or.inr ⟨h₁, h₂⟩⟩

theorem childB_iff : childB ψ X w = true ↔ Child ψ X w := by
  simp only [childB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    upperAtB_iff, decide_eq_true_eq, Child, USet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨v, h₁, ⟨⟨v', b⟩, hp, rfl⟩⟩
    exact ⟨v', h₁, b, (mem_upperLits ψ v' b).mp hp⟩
  · rintro ⟨v, h₁, b, hb⟩
    exact ⟨v, h₁, ⟨(v, b), (mem_upperLits ψ v b).mpr hb, rfl⟩⟩

theorem crossB_iff (s e : ℕ) : crossB ψ X Y w s e = true ↔ Cross ψ X Y w s e := by
  simp only [crossB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    upperAtB_iff, lowerAtB_iff, Cross, USet, LSet, Set.Nonempty, Set.mem_inter_iff,
    Set.mem_ofPred_eq]

theorem selfB_iff (s e : ℕ) : selfB ψ X w s e = true ↔ Self ψ X w s e := by
  rw [self_iff]
  simp only [selfB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    upperAtB_iff, USet, Set.mem_ofPred_eq]

/-- The Boolean event test decides whether any readiness, child, cross or self event occurs. -/
theorem occursB_iff : occursB ψ X Y w = true ↔ Occurs ψ X Y w := by
  rw [occurs_def]
  simp only [occursB, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, readyB_iff, childB_iff, crossB_iff, selfB_iff, Nat.lt_succ_iff]
  constructor
  · rintro ((⟨j, hj, h⟩ | h) | ⟨e, he, s, hs, hp, h⟩)
    · exact Or.inl ⟨j, hj, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨s, e, hs, he, hp, h⟩)
  · rintro (⟨j, hj, h⟩ | h | ⟨s, e, hs, he, hp, h⟩)
    · exact Or.inl (Or.inl ⟨j, hj, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, he, s, hs, hp, h⟩

instance (ψ : Constraint n (2 * k)) (X Y : V (2 * k)) (w : List (Fin n)) :
    Decidable (Occurs ψ X Y w) :=
  decidable_of_iff _ occursB_iff

end Bool

end DeciNSSE.Events
