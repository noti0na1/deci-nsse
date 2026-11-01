import DeciNSSE.Complexity.HardnessSystem

/-! # Solutions of the hardness system for a universal automaton

Let `M` be universal and `ρ` a solution of `hardnessSystem n M` by arbitrary
trees. Call `P` the proper prefixes of doubling codes, the paths `e(w)` and
`e(w) 0`.

- Along a run of `M` on `w`, the subtree of `x` at `e(w)` lies below `X_q`
  (`trace_le_stateVar`). Every code is accepted, so `x` is bottom at codes and
  at the directions `2, …, n - 1`, never top, and differs from bottom only on `P`.
- The literals on `r` and `r'` keep a constructor above `r` at every path of
  `P`, so `r` is never bottom there.

Hence `ρ x ≤ ρ r` (`le_of_universal`).

## Main declarations
- `Hardness.le_of_universal`
- `Hardness.entails_of_universal`
-/

namespace DeciNSSE.Complexity.Hardness

open Safety Directions

variable {n m : ℕ}

section Solution

variable (hn : 2 ≤ n) {M : BinNFA m} {ρ : V (numVars M) → Tree n}
  (hρ : Covariant.Sat ρ (hardnessSystem n M))
include hn hρ

/-- Along a run on `w`, the subtree of `x` below `X_p` moves along `e(w)` below `X_q`. -/
theorem trace_le_stateVar {p q : Fin m} {w : List (Fin 2)} (hw : M.Path p w q)
    (π : List (Fin n)) (hπ : trace (ρ (xVar M)) π ≤ ρ (stateVar M p)) :
    trace (ρ (xVar M)) (π ++ doubling hn w) ≤ ρ (stateVar M q) := by
  obtain ⟨-, -, -, -, -, -, henter, hread⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  induction w generalizing p π with
  | nil => simp only [BinNFA.path_nil] at hw; subst hw; simpa using hπ
  | cons a w ih =>
    obtain ⟨p', ht, hw⟩ := hw
    obtain ⟨i, hi, hj⟩ := List.mem_iff_getElem.mp ht
    have h0 : trace (ρ (xVar M)) (π ++ [embedDir hn 0]) ≤ ρ (transVar M ⟨i, hi⟩) := by
      have := descend_mono (le_trans hπ (by simpa [hj] using henter ⟨i, hi⟩)) (embedDir hn 0)
      simpa [trace_snoc] using this
    have h1 : trace (ρ (xVar M)) (π ++ [embedDir hn 0] ++ [embedDir hn a]) ≤
        ρ (stateVar M p') := by
      have := descend_mono (le_trans h0 (hread ⟨i, hi⟩)) (embedDir hn a)
      rw [← trace_snoc] at this
      refine le_of_le_of_eq this ?_
      simp [readChildren, hj]
    simpa using ih hw _ h1

/-- At `e(w)`, the subtree of `x` lies below the variable of a final state. -/
theorem trace_doubling_le (huniv : ∀ w, M.Accepts w) (w : List (Fin 2)) :
    ∃ q, M.final q = true ∧ trace (ρ (xVar M)) (doubling hn w) ≤ ρ (stateVar M q) := by
  obtain ⟨-, -, -, hz, hinit, -⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  obtain ⟨p, hp, q, hq, hpath⟩ := huniv w
  have hx : ρ (xVar M) ≤ ρ (stateVar M p) := by
    simpa using (Tree.node_le_node_iff _ _).mp (le_trans hz (hinit p hp)) (embedDir hn 0)
  exact ⟨q, hq, by simpa using trace_le_stateVar hn hρ hpath [] (by simpa using hx)⟩

/-- At `e(w) 0`, the subtree of `x` lies below the middle variable of a transition. -/
theorem trace_doubling_zero_le (huniv : ∀ w, M.Accepts w) (w : List (Fin 2)) :
    ∃ j, trace (ρ (xVar M)) (doubling hn w ++ [embedDir hn 0]) ≤ ρ (transVar M j) := by
  obtain ⟨-, -, -, hz, hinit, -, henter, -⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  obtain ⟨p, hp, q, -, hpath⟩ := huniv (w ++ [0])
  obtain ⟨s, hs, p', ht, -⟩ := (M.path_append p q w [0]).mp hpath
  obtain ⟨i, hi, hj⟩ := List.mem_iff_getElem.mp ht
  have hx : ρ (xVar M) ≤ ρ (stateVar M p) := by
    simpa using (Tree.node_le_node_iff _ _).mp (le_trans hz (hinit p hp)) (embedDir hn 0)
  have hw := trace_le_stateVar hn hρ hs [] (by simpa using hx)
  have := descend_mono (le_trans hw (by simpa [hj] using henter ⟨i, hi⟩)) (embedDir hn 0)
  exact ⟨⟨i, hi⟩, by simpa [trace_snoc] using this⟩

/-- Off the proper prefixes of codes, `x` is bottom. -/
theorem trace_eq_bot_or_mem (huniv : ∀ w, M.Accepts w) (ν : List (Fin n)) :
    trace (ρ (xVar M)) ν = Tree.bot ∨
      ∃ w, ν = doubling hn w ∨ ν = doubling hn w ++ [embedDir hn 0] := by
  obtain ⟨hb, -, -, -, -, hfinal, -, hread⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  induction ν using List.reverseRecOn with
  | nil => exact Or.inr ⟨[], Or.inl rfl⟩
  | append_singleton ν i ih =>
    rcases ih with h | ⟨w, rfl | rfl⟩
    · exact Or.inl (by rw [trace_snoc, h, descend_bot])
    · by_cases hi : i.val = 0
      · exact Or.inr ⟨w, Or.inr (by rw [show i = embedDir hn 0 from Fin.ext hi])⟩
      · obtain ⟨q, hq, hle⟩ := trace_doubling_le hn hρ huniv w
        refine Or.inl ?_
        rw [trace_snoc]
        exact descend_eq_bot_of_le (le_trans hle (hfinal q hq))
          (by simp [binaryChildren, hi, hb])
    · by_cases hi : i.val < 2
      · refine Or.inr ⟨w ++ [⟨i.val, hi⟩], Or.inl ?_⟩
        rw [doubling_snoc]
        rfl
      · obtain ⟨j, hle⟩ := trace_doubling_zero_le hn hρ huniv w
        refine Or.inl ?_
        rw [trace_snoc]
        refine descend_eq_bot_of_le (le_trans hle (hread j)) ?_
        have hne : i.val ≠ M.trans[j].2.1.val := by have := M.trans[j].2.1.isLt; omega
        simp only [Function.comp_apply, readChildren, hne, hi, ↓reduceIte, hb]

/-- The tree `x` is top at no path. -/
theorem trace_ne_top (huniv : ∀ w, M.Accepts w) (ν : List (Fin n)) :
    trace (ρ (xVar M)) ν ≠ Tree.top := by
  obtain ⟨-, -, -, -, -, hfinal, -, hread⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  rcases trace_eq_bot_or_mem hn hρ huniv ν with h | ⟨w, rfl | rfl⟩
  · rw [h]; exact Tree.bot_ne_top
  · obtain ⟨q, hq, hle⟩ := trace_doubling_le hn hρ huniv w
    exact ne_top_of_le_node (le_trans hle (hfinal q hq))
  · obtain ⟨j, hle⟩ := trace_doubling_zero_le hn hρ huniv w
    exact ne_top_of_le_node (le_trans hle (hread j))

omit hρ in
/-- The value of `r` lies below its subtrees at `e(w)`, and that of `r'` below its
subtrees at `e(w) 0`. -/
theorem le_trace_rVar (hρ : Covariant.Sat ρ (hardnessSystem n M)) (w : List (Fin 2)) :
    ρ (rVar M) ≤ trace (ρ (rVar M)) (doubling hn w) ∧
      ρ (rVar' M) ≤ trace (ρ (rVar M)) (doubling hn w ++ [embedDir hn 0]) := by
  obtain ⟨-, hr, hr', -⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  have step : ∀ ν, ρ (rVar M) ≤ trace (ρ (rVar M)) ν →
      ρ (rVar' M) ≤ trace (ρ (rVar M)) (ν ++ [embedDir hn 0]) := by
    intro ν h
    simpa [trace_snoc] using descend_mono (le_trans hr h) (embedDir hn 0)
  refine ⟨?_, step _ ?_⟩ <;>
  · induction w using List.reverseRecOn with
    | nil => exact le_rfl
    | append_singleton w a ih =>
      have := descend_mono (le_trans hr' (step _ ih)) (embedDir hn a)
      rw [← trace_snoc, ← doubling_snoc] at this
      refine le_of_eq_of_le ?_ this
      fin_cases a <;> simp [binaryChildren, embedDir]

/-- For a universal automaton, every solution satisfies `x ≤ r`. -/
theorem le_of_universal (huniv : ∀ w, M.Accepts w) : ρ (xVar M) ≤ ρ (rVar M) := by
  obtain ⟨-, hr, hr', -⟩ := (covSat_hardnessSystem_iff M ρ).mp hρ
  by_contra h
  obtain ⟨ν, ⟨hx, hν⟩ | ⟨hx, -⟩⟩ := (not_le_iff_unsafe _ _).mp h
  · rcases trace_eq_bot_or_mem hn hρ huniv ν with h' | ⟨w, rfl | rfl⟩
    · exact hx h'
    · exact ne_bot_of_node_le (le_trans hr (le_trace_rVar hn hρ w).1) hν
    · exact ne_bot_of_node_le (le_trans hr' (le_trace_rVar hn hρ w).2) hν
  · exact trace_ne_top hn hρ huniv ν hx

end Solution

/-- Universality gives entailment over arbitrary trees. -/
theorem entails_of_universal (hn : 2 ≤ n) {M : BinNFA m} (huniv : ∀ w, M.Accepts w) :
    Entails (fun _ => false) (hardnessSystem n M) (xVar M) (rVar M) := by
  intro ρ hρ
  rw [treeLe_false_iff_le]
  exact le_of_universal hn ((sat_false ρ _).mp hρ) huniv

end DeciNSSE.Complexity.Hardness
