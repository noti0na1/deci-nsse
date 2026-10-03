import DeciNSSE.Automata.Inclusion
import DeciNSSE.Coverage.FullCoverage

/-! # Transition relations and coverage

The transition relations of a finite automaton form a finite monoid.
Ordinary and periodic acceptance become full coverage under its word morphism.
-/

namespace DeciNSSE.EndToEnd

open Words CapAutomaton CapInflation FullCoverage
open scoped TerminalCopy

structure Rel (Q : Type) where
  pairs : Finset (Q × Q)
  deriving DecidableEq, Fintype

namespace Rel

variable {Q : Type}

instance : Membership (Q × Q) (Rel Q) := ⟨fun R p => p ∈ R.pairs⟩

instance [DecidableEq Q] (p : Q × Q) (R : Rel Q) : Decidable (p ∈ R) :=
  inferInstanceAs (Decidable (p ∈ R.pairs))

@[ext] theorem ext {R S : Rel Q} (h : ∀ p q, (p, q) ∈ R ↔ (p, q) ∈ S) : R = S := by
  cases R with
  | mk R =>
    cases S with
    | mk S =>
      congr 1
      exact Finset.ext (fun ⟨p, q⟩ => h p q)

variable [Fintype Q] [DecidableEq Q]

instance : One (Rel Q) := ⟨⟨Finset.univ.filter (fun p => p.1 = p.2)⟩⟩

instance : Mul (Rel Q) := ⟨fun R S =>
  ⟨Finset.univ.filter (fun p => ∃ q, (p.1, q) ∈ R ∧ (q, p.2) ∈ S)⟩⟩

@[simp] theorem mem_one (p q : Q) : (p, q) ∈ (1 : Rel Q) ↔ p = q := by
  change (p, q) ∈ Finset.univ.filter _ ↔ _
  simp

@[simp] theorem mem_mul (R S : Rel Q) (p q : Q) :
    (p, q) ∈ R * S ↔ ∃ r, (p, r) ∈ R ∧ (r, q) ∈ S := by
  change (p, q) ∈ Finset.univ.filter _ ↔ _
  simp

instance : Monoid (Rel Q) where
  mul_assoc R S T := by
    ext p q
    simp only [mem_mul]
    constructor
    · rintro ⟨s, ⟨r, hr, hs⟩, ht⟩
      exact ⟨r, hr, s, hs, ht⟩
    · rintro ⟨r, hr, s, hs, ht⟩
      exact ⟨s, ⟨r, hr, hs⟩, ht⟩
  one_mul R := by ext p q; simp
  mul_one R := by ext p q; simp

end Rel

section Automaton

variable {Q : Type} [Fintype Q] [DecidableEq Q] (P : CapAutomaton Q)

theorem runs_append_iff (p q : Q) (u v : Word) :
    P.Runs p (u ++ v) q ↔ ∃ r, P.Runs p u r ∧ P.Runs r v q := by
  induction u generalizing p with
  | nil => simp
  | cons a u ih =>
    simp only [List.cons_append, runs_cons_iff, ih]
    constructor
    · rintro ⟨s, hs, r, hu, hv⟩
      exact ⟨r, ⟨s, hs, hu⟩, hv⟩
    · rintro ⟨r, ⟨s, hs, hu⟩, hv⟩
      exact ⟨s, hs, r, hu, hv⟩

def transition (w : Word) : Rel Q :=
  ⟨Finset.univ.filter (fun p => p.2 ∈ P.reach p.1 w)⟩

theorem mem_transition_iff (p q : Q) (w : Word) :
    (p, q) ∈ transition P w ↔ P.Runs p w q := by
  change (p, q) ∈ Finset.univ.filter _ ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_reach_iff]

def transRel : Word →* Rel Q where
  toFun := transition P
  map_one' := by
    change transition P [] = 1
    apply Rel.ext
    intro p q
    rw [mem_transition_iff, Rel.mem_one, runs_nil_iff]
  map_mul' u v := by
    change transition P (u ++ v) = transition P u * transition P v
    apply Rel.ext
    intro p q
    simp only [Rel.mem_mul, mem_transition_iff]
    exact runs_append_iff P p q u v

@[simp] theorem mem_transRel_iff (p q : Q) (w : Word) :
    (p, q) ∈ transRel P w ↔ P.Runs p w q := by
  exact mem_transition_iff P p q w

def VA : Set (Rel Q) := {R | ∃ q, (P.init, q) ∈ R ∧ P.final q = true}

abbrev Edge := {e : Q × Q // P.pedge e.1 e.2 = true}

def V (e : Edge P) : Set (Rel Q) := {R | (P.init, e.val.2) ∈ R}
def U (e : Edge P) : Set (Rel Q) := {R | (e.val.2, e.val.1) ∈ R}

instance : DecidablePred (· ∈ VA P) := fun R =>
  inferInstanceAs (Decidable (∃ q, (P.init, q) ∈ R ∧ P.final q = true))

theorem loop_eq_preimage (q₁ q₂ : Q) :
    P.Loop q₁ q₂ = transRel P ⁻¹' {R | (q₁, q₂) ∈ R} := by
  ext w
  exact (mem_transRel_iff P q₁ q₂ w).symm

theorem langA_eq_preimage : P.LangA = transRel P ⁻¹' VA P := by
  ext w
  simp [LangA, VA]

theorem mem_lang_iff_fullCovered (w : Word) :
    w ∈ P.Lang ↔ FullCovered (transRel P) (VA P) (V P) (U P) w := by
  change (w ∈ P.LangA ∨ w ∈ P.LangP) ↔ _
  rw [langA_eq_preimage, P.langP_eq]
  simp only [FullCovered, Set.mem_preimage, Set.mem_iUnion]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨q₁, q₂, he, π, hπ, v, hv, hw⟩
    refine ⟨⟨(q₂, q₁), he⟩, π, v, hw.symm, ?_, ?_⟩
    · exact (mem_transRel_iff P P.init q₁ π).mpr hπ
    · rw [capCovered_iff]
      simpa only [U, ← loop_eq_preimage] using hv
  · rintro ⟨⟨⟨q₂, q₁⟩, he⟩, π, v, hw, hπ, hv⟩
    refine ⟨q₁, q₂, he, π, ?_, v, ?_, hw.symm⟩
    · exact (mem_transRel_iff P P.init q₁ π).mp hπ
    · rw [capCovered_iff] at hv
      simpa only [U, ← loop_eq_preimage] using hv

end Automaton

end DeciNSSE.EndToEnd
