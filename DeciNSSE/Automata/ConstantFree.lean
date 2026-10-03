import DeciNSSE.Automata.Language

/-! # Loop coordinates without constants

The selected state coordinate characterises loop words independently of
constant transitions. These characterisations identify admitted periodic roots.
-/

namespace DeciNSSE

namespace ConstantFree

open Words CState Construction

variable {k : ℕ} {ϕ : Constraint k} {x y : V k}
  {q r : CState k} {i : Fin 2} {u v w : Word}

def G : Side → CState k → Prop
  | .l, q => q = all ∨ ∃ u s, q = pair (some u) s
  | .r, q => q = all ∨ ∃ v s, q = pair s (some v)

theorem left_root_iff {a b : V k} {μ : Word} (hn : μ ≠ []) :
    (construct ϕ x y .l).Runs (pair (some a) (some b)) μ (pair (some b) none) ↔
      UpperAt ϕ μ a b := by
  constructor
  · intro h
    obtain ⟨u, hu, hp⟩ := runs_upper h rfl
    cases Option.some.inj hu
    exact hp
  · intro h
    exact Language.upperAt_run_from hn h (some b)

theorem left_pair_root_iff {a b c : V k} {μ : Word} (hn : μ ≠ []) :
    (construct ϕ x y .l).Runs (pair (some a) (some b)) μ (pair (some b) (some c)) ↔
      UpperAt ϕ μ a b ∧ LowerAt ϕ μ c b := by
  constructor
  · intro h
    obtain ⟨u, hu, hp⟩ := runs_upper h rfl
    obtain ⟨v, hv, hq⟩ := runs_lower h rfl
    cases Option.some.inj hu
    cases Option.some.inj hv
    exact ⟨hp, hq⟩
  · rintro ⟨hu, hl⟩
    exact Language.pair_run hn hu hl

theorem right_root_iff {a b : V k} {μ : Word} (hn : μ ≠ []) :
    (construct ϕ x y .r).Runs (pair (some a) (some b)) μ (pair none (some a)) ↔
      LowerAt ϕ μ a b := by
  constructor
  · intro h
    obtain ⟨v, hv, hp⟩ := runs_lower h rfl
    cases Option.some.inj hv
    exact hp
  · intro h
    exact Language.lowerAt_run_from hn h (some a)

theorem right_pair_root_iff {a b c : V k} {μ : Word} (hn : μ ≠ []) :
    (construct ϕ x y .r).Runs (pair (some a) (some b)) μ (pair (some c) (some a)) ↔
      UpperAt ϕ μ a c ∧ LowerAt ϕ μ a b := by
  constructor
  · intro h
    obtain ⟨u, hu, hp⟩ := runs_upper h rfl
    obtain ⟨v, hv, hq⟩ := runs_lower h rfl
    cases Option.some.inj hu
    cases Option.some.inj hv
    exact ⟨hp, hq⟩
  · rintro ⟨hu, hl⟩
    exact Language.pair_run hn hu hl

end ConstantFree
end DeciNSSE
