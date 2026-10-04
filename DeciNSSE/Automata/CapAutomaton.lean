import DeciNSSE.Words
import DeciNSSE.Transfer.Safety

/-! # Automata with periodic caps

An automaton accepts ordinary finite runs together with prefixes of powers
of designated loop words. Two path-safety predicates connect these languages
to non-structural subtype entailment.
-/

namespace DeciNSSE

/-- A finite nondeterministic automaton with additional edges closing admitted cap roots. -/
structure CapAutomaton (Q : Type) [Fintype Q] [DecidableEq Q] where
  init : Q
  final : Q → Bool
  step : Q → Fin 2 → Finset Q
  pedge : Q → Q → Bool

namespace CapAutomaton

variable {Q : Type} [Fintype Q] [DecidableEq Q] (P : CapAutomaton Q)

inductive Runs : Q → List (Fin 2) → Q → Prop where
  | nil (q : Q) : Runs q [] q
  | cons {q r s : Q} {i : Fin 2} {π : List (Fin 2)} :
      r ∈ P.step q i → Runs r π s → Runs q (i :: π) s

@[simp] theorem runs_nil_iff {q r : Q} : P.Runs q [] r ↔ q = r := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

@[simp] theorem runs_cons_iff {q s : Q} {i : Fin 2} {π : List (Fin 2)} :
    P.Runs q (i :: π) s ↔ ∃ r, r ∈ P.step q i ∧ P.Runs r π s := by
  constructor
  · intro h; cases h with | cons hs hr => exact ⟨_, hs, hr⟩
  · rintro ⟨r, hs, hr⟩; exact .cons hs hr

theorem Runs.append {q r s : Q} {π τ : List (Fin 2)}
    (h : P.Runs q π r) (h' : P.Runs r τ s) : P.Runs q (π ++ τ) s := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

def reach (q : Q) : List (Fin 2) → Finset Q
  | [] => {q}
  | i :: π => (P.step q i).biUnion (fun r => reach r π)

theorem mem_reach_iff (q r : Q) (π : List (Fin 2)) :
    r ∈ P.reach q π ↔ P.Runs q π r := by
  induction π generalizing q with
  | nil => simp [reach, eq_comm]
  | cons i π ih => simp [reach, ih]

/-- Ordinary acceptance by a finite run from the initial state to a final state. -/
def LangA : Set (List (Fin 2)) :=
  {π | ∃ q, P.Runs P.init π q ∧ P.final q = true}

/-- Acceptance by an initial run followed by a prefix of a power of an admitted cap root. -/
def LangP : Set (List (Fin 2)) :=
  {ν | ∃ π μ' q₁ q₂ μ, ν = π ++ μ' ∧ P.Runs P.init π q₁ ∧
    P.Runs q₁ μ q₂ ∧ P.pedge q₂ q₁ = true ∧ Words.IsPrefixOfPower μ μ'}

/-- The union of ordinary acceptance and acceptance by periodic caps. -/
def Lang : Set (List (Fin 2)) := P.LangA ∪ P.LangP

end CapAutomaton

variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {ν : List (Fin 2)}

def LSafe (ϕ : Constraint k) (x y : V k) (π : List (Fin 2)) : Prop :=
  ∀ ρ, Sat ρ ϕ → Safety.HasLabel (ρ x) π Sym.top → Safety.HasLabel (ρ y) π Sym.top

def RSafe (ϕ : Constraint k) (x y : V k) (π : List (Fin 2)) : Prop :=
  ∀ ρ, Sat ρ ϕ → Safety.HasLabel (ρ y) π Sym.bot → Safety.HasLabel (ρ x) π Sym.bot

theorem not_lSafe_iff : ¬ LSafe ϕ x y ν ↔ ∃ ρ', Sat ρ' (lUnsafe ϕ x y ν) := by
  classical
  constructor
  · intro h
    simp only [LSafe, ← Safety.trace_eq_top_iff, not_forall] at h
    obtain ⟨ρ, hs, hx, hy⟩ := h
    exact ⟨_, Safety.lUnsafe_extend ρ hs hx hy⟩
  · rintro ⟨ρ', hs⟩ h
    obtain ⟨hs, hx, hy⟩ := (Safety.sat_lUnsafe_iff _).mp hs
    exact Safety.noTopChain_sound hy ((Safety.trace_eq_top_iff _ _).mpr
      (h _ hs ((Safety.trace_eq_top_iff _ _).mp (Safety.topChain_sound hx))))

theorem not_rSafe_iff : ¬ RSafe ϕ x y ν ↔ ∃ ρ', Sat ρ' (rUnsafe ϕ x y ν) := by
  classical
  constructor
  · intro h
    simp only [RSafe, ← Safety.trace_eq_bot_iff, not_forall] at h
    obtain ⟨ρ, hs, hy, hx⟩ := h
    exact ⟨_, Safety.rUnsafe_extend ρ hs hx hy⟩
  · rintro ⟨ρ', hs⟩ h
    obtain ⟨hs, hx, hy⟩ := (Safety.sat_rUnsafe_iff _).mp hs
    exact Safety.noBotChain_sound hx ((Safety.trace_eq_bot_iff _ _).mpr
      (h _ hs ((Safety.trace_eq_bot_iff _ _).mp (Safety.botChain_sound hy))))

theorem entails_iff_safe : Entails ϕ x y ↔ ∀ π, LSafe ϕ x y π ∧ RSafe ϕ x y π := by
  classical
  rw [← not_iff_not]
  simp only [not_entails_iff, not_forall, not_and_or, not_lSafe_iff, not_rSafe_iff,
    or_comm]

end DeciNSSE
