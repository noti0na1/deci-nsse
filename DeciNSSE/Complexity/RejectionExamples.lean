import DeciNSSE.Complexity.RejectionCountermodel

/-! # An example of the rejection system

The automaton `noZeroZero` accepts the binary words without the prefix `00`,
and all its states are final. At arity three, the unsafe words of its rejection
system are the binary words that extend `00`; at arity two, entailment fails
already over finite trees. These checks exercise `Rejection.unsafe_iff` and
`Rejection.not_entailsFin_rejectionSystem` on a concrete automaton.
-/

namespace DeciNSSE.Complexity.Rejection

open Directions

/-- The binary words without the prefix `00`: the initial state `0` reads `0` to `1` and `1`
to `2`, the state `1` reads `1` to `2`, and the state `2` loops; all states are final. -/
private def noZeroZero : BinNFA 3 :=
  ⟨fun q => q = 0, fun _ => true, [(0, 0, 1), (0, 1, 2), (1, 1, 2), (2, 0, 2), (2, 1, 2)]⟩

/-- The looping state accepts every word. -/
private theorem noZeroZero_acceptsFrom_two (u : List (Fin 2)) : noZeroZero.AcceptsFrom 2 u := by
  refine ⟨2, rfl, ?_⟩
  induction u with
  | nil => rfl
  | cons a u ih => exact ⟨2, by fin_cases a <;> simp [noZeroZero], ih⟩

/-- The automaton accepts exactly the words without the prefix `00`. -/
private theorem noZeroZero_accepts_iff (u : List (Fin 2)) :
    noZeroZero.Accepts u ↔ ¬ [0, 0] <+: u := by
  constructor
  · rintro ⟨p, hp, r, -, hpath⟩ ⟨v, rfl⟩
    obtain rfl : p = 0 := by simpa [noZeroZero] using hp
    obtain ⟨p₁, h₁, p₂, h₂, -⟩ := hpath
    obtain rfl : p₁ = 1 := by simpa [noZeroZero] using h₁
    simp [noZeroZero] at h₂
  · intro h
    have two := noZeroZero_acceptsFrom_two
    refine ⟨0, rfl, ?_⟩
    rcases u with _ | ⟨a, _ | ⟨b, v⟩⟩
    · exact ⟨0, rfl, rfl⟩
    · fin_cases a
      · exact ⟨1, rfl, 1, by simp [noZeroZero], rfl⟩
      · exact noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two [])
    · fin_cases a
      · fin_cases b
        · exact absurd ⟨v, rfl⟩ h
        · exact noZeroZero.acceptsFrom_cons (q := 1) (by simp [noZeroZero])
            (noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two v))
      · exact noZeroZero.acceptsFrom_cons (by simp [noZeroZero]) (two (b :: v))

/-- For `W = 00` at arity three, the unsafe words are the binary words that extend `00`. -/
example (θ : Side) (w : List (Fin 3)) :
    Unsafe (fun _ => false) (rejectionSystem 3 noZeroZero) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = ([0, 0] ++ v).map (embedDir (by norm_num)) :=
  unsafe_iff _ (fun _ => rfl) (List.cons_ne_nil _ _) noZeroZero_accepts_iff θ w

/-- For `W = 00`, entailment fails already over finite trees. -/
example : ¬ EntailsFin (fun _ => false) (rejectionSystem 2 noZeroZero) xVar yVar :=
  not_entailsFin_rejectionSystem le_rfl (fun _ => rfl) (List.cons_ne_nil _ _)
    noZeroZero_accepts_iff

end DeciNSSE.Complexity.Rejection
