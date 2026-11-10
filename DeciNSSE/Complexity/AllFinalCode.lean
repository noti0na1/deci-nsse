import DeciNSSE.Complexity.BinNFA
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Induction

/-! # An all-final encoding of binary automata

Each source letter `a` is encoded as `0 a`. Boundary states `B q` and pending states
`P q` simulate the source automaton. Guards `g` and `h` accept every complete code and
every complete code followed by `0`. A `1` at a code boundary reaches the absorbing sink
exactly when the source word is accepted. Every state is final.

For a source automaton with `m` states and `T` transitions, the encoding has `2 m + 3`
states and at most `T + 2 m + 5` transitions. It accepts the empty word and preserves
universality, including for automata with no states.

## Main declarations
- `allFinalCode`, `allFinalCode_length_trans_le`
- `AllFinal.reached_enc`, `AllFinal.reached_enc_zero`, `AllFinal.reached_enc_one`
- `AllFinal.accepts_enc`, `AllFinal.accepts_enc_zero`, `AllFinal.accepts_enc_one`
- `allFinalCode_universal_iff`
-/

namespace DeciNSSE.Complexity

namespace AllFinal

variable {m : ℕ}

/-- Boundary and pending copies of each source state, two guards, and an absorbing sink. -/
inductive State (m : ℕ)
  | B : Fin m → State m
  | P : Fin m → State m
  | g | h | sink

open State

private theorem exists_state (p : State m → Prop) :
    (∃ s, p s) ↔ (∃ q, p (B q)) ∨ (∃ q, p (P q)) ∨ p g ∨ p h ∨ p sink := by
  constructor
  · rintro ⟨s, hs⟩
    cases s with
    | B q => exact Or.inl ⟨q, hs⟩
    | P q => exact Or.inr (Or.inl ⟨q, hs⟩)
    | g => exact Or.inr (Or.inr (Or.inl hs))
    | h => exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    | sink => exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
  · rintro (⟨q, hq⟩ | ⟨q, hq⟩ | hg | hh | hs) <;> exact ⟨_, ‹p _›⟩

/-- Index the structured states in the `2 m + 3` states of the binary automaton. -/
def idx : State m → Fin (2 * m + 3)
  | B q => ⟨q, by omega⟩
  | P q => ⟨m + q, by omega⟩
  | g => ⟨2 * m, by omega⟩
  | h => ⟨2 * m + 1, by omega⟩
  | sink => ⟨2 * m + 2, by omega⟩

theorem idx_injective : Function.Injective (idx (m := m)) := by
  intro s t he
  have he := congrArg Fin.val he
  cases s <;> cases t <;> simp_all [idx, Fin.ext_iff] <;> omega

theorem idx_surjective : Function.Surjective (idx (m := m)) := by
  intro i
  by_cases hb : i.val < m
  · exact ⟨B ⟨i, hb⟩, Fin.ext rfl⟩
  by_cases hp : i.val < 2 * m
  · exact ⟨P ⟨i - m, by omega⟩, Fin.ext (by simp [idx]; omega)⟩
  rcases show i.val = 2 * m ∨ i.val = 2 * m + 1 ∨ i.val = 2 * m + 2 by omega with h | h | h
  · exact ⟨g, Fin.ext h.symm⟩
  · exact ⟨State.h, Fin.ext h.symm⟩
  · exact ⟨sink, Fin.ext h.symm⟩

/-- The boundary guard and the boundary copies of the source initial states. -/
def starts (M : BinNFA m) : List (State m) :=
  g :: ((List.finRange m).filter M.init).map B

/-- Simulation edges, final-state exits, guard edges, and sink loops. -/
def edges (M : BinNFA m) : List (State m × Fin 2 × State m) :=
  (List.finRange m).map (fun q => (B q, 0, P q)) ++
  M.trans.map (fun t => (P t.1, t.2.1, B t.2.2)) ++
  ((List.finRange m).filter M.final).map (fun q => (B q, 1, sink)) ++
  [(g, 0, h), (h, 0, g), (h, 1, g), (sink, 0, sink), (sink, 1, sink)]

/-- The transition relation on structured states. -/
def step (M : BinNFA m) : State m → Fin 2 → State m → Prop
  | B q, a, P r => a = 0 ∧ q = r
  | P q, a, B r => (q, a, r) ∈ M.trans
  | B q, a, sink => a = 1 ∧ M.final q = true
  | g, a, h => a = 0
  | h, _, g => True
  | sink, _, sink => True
  | _, _, _ => False

@[simp] theorem mem_edges (M : BinNFA m) (s t : State m) (a : Fin 2) :
    (s, a, t) ∈ edges M ↔ step M s a t := by
  cases s <;> cases t <;> fin_cases a <;>
    simp [edges, step, List.mem_map, Prod.mk.injEq]

end AllFinal

open AllFinal AllFinal.State

/-- Encode binary universality by an automaton whose states are all final. -/
def allFinalCode {m : ℕ} (M : BinNFA m) : BinNFA (2 * m + 3) where
  init i := (starts M).any (fun s => idx s == i)
  final _ := true
  trans := (edges M).map (fun t => (idx t.1, t.2.1, idx t.2.2))

namespace AllFinal

variable {m : ℕ} (M : BinNFA m)

@[simp] theorem init_idx (s : State m) :
    (allFinalCode M).init (idx s) = true ↔ s ∈ starts M := by
  simp [allFinalCode, idx_injective.eq_iff]

@[simp] theorem trans_idx (s t : State m) (a : Fin 2) :
    (idx s, a, idx t) ∈ (allFinalCode M).trans ↔ step M s a t := by
  simp [allFinalCode, List.mem_map, Prod.exists, Prod.mk.injEq, idx_injective.eq_iff]

/-- States reached after reading a word from some initial state. -/
def Reached {k : ℕ} (A : BinNFA k) (w : List (Fin 2)) (q : Fin k) : Prop :=
  ∃ p, A.init p = true ∧ A.Path p w q

@[simp] theorem reached_nil {k : ℕ} (A : BinNFA k) (q : Fin k) :
    Reached A [] q ↔ A.init q = true := by simp [Reached]

theorem reached_snoc {k : ℕ} (A : BinNFA k) (w : List (Fin 2)) (a : Fin 2) (q : Fin k) :
    Reached A (w ++ [a]) q ↔ ∃ p, Reached A w p ∧ (p, a, q) ∈ A.trans := by
  simp only [Reached, BinNFA.path_append, BinNFA.path_cons, BinNFA.path_nil,
    exists_eq_right]
  exact ⟨fun ⟨p, hp, r, hr, ht⟩ => ⟨r, ⟨p, hp, hr⟩, ht⟩,
    fun ⟨r, ⟨p, hp, hr⟩, ht⟩ => ⟨p, hp, r, hr, ht⟩⟩

theorem reached_idx_snoc (w : List (Fin 2)) (a : Fin 2) (t : State m) :
    Reached (allFinalCode M) (w ++ [a]) (idx t) ↔
      ∃ s, Reached (allFinalCode M) w (idx s) ∧ step M s a t := by
  rw [reached_snoc, idx_surjective.exists]
  simp

/-- Encode each binary letter `a` as `0 a`. -/
def enc (w : List (Fin 2)) : List (Fin 2) := w.flatMap (fun a => [0, a])

/-- At a code boundary, the guard and the reached source states are present. -/
def boundary (w : List (Fin 2)) : State m → Prop
  | B q => Reached M w q
  | g => True
  | _ => False

/-- After a boundary `0`, the pending guard and pending source states are present. -/
def pending (w : List (Fin 2)) : State m → Prop
  | P q => Reached M w q
  | h => True
  | _ => False

private theorem reached_zero {u w : List (Fin 2)}
    (hu : ∀ s, Reached (allFinalCode M) u (idx s) ↔ boundary M w s) (t : State m) :
    Reached (allFinalCode M) (u ++ [0]) (idx t) ↔ pending M w t := by
  rw [reached_idx_snoc]
  simp only [hu]
  cases t <;> simp [exists_state, boundary, pending, step]

/-- A complete code reaches exactly the boundary guard and the source reachable states. -/
theorem reached_enc (w : List (Fin 2)) (t : State m) :
    Reached (allFinalCode M) (enc w) (idx t) ↔ boundary M w t := by
  induction w using List.reverseRecOn generalizing t with
  | nil => cases t <;> simp [enc, boundary, starts]
  | append_singleton w a ih =>
    have he : enc (w ++ [a]) = (enc w ++ [0]) ++ [a] := by simp [enc, List.append_assoc]
    rw [he, reached_idx_snoc]
    simp only [reached_zero M ih]
    cases t <;> simp [exists_state, pending, boundary, step, reached_snoc]

/-- A code followed by `0` reaches exactly the pending copies of its boundary states. -/
theorem reached_enc_zero (w : List (Fin 2)) (t : State m) :
    Reached (allFinalCode M) (enc w ++ [0]) (idx t) ↔ pending M w t :=
  reached_zero M (reached_enc M w) t

theorem accepts_iff_reached {k : ℕ} (A : BinNFA k) (w : List (Fin 2)) :
    A.Accepts w ↔ ∃ q, Reached A w q ∧ A.final q = true := by
  unfold BinNFA.Accepts BinNFA.AcceptsFrom Reached
  exact ⟨fun ⟨p, hp, q, hq, hpq⟩ => ⟨q, ⟨p, hp, hpq⟩, hq⟩,
    fun ⟨q, ⟨p, hp, hpq⟩, hq⟩ => ⟨p, hp, q, hq, hpq⟩⟩

/-- After a boundary `1` and any suffix, only the sink can remain, iff the source accepts. -/
theorem reached_enc_one (w v : List (Fin 2)) (t : State m) :
    Reached (allFinalCode M) (enc w ++ [1] ++ v) (idx t) ↔
      t = sink ∧ M.Accepts w := by
  induction v using List.reverseRecOn generalizing t with
  | nil =>
    simp only [List.append_nil, reached_idx_snoc, reached_enc]
    cases t <;> simp [exists_state, boundary, step, accepts_iff_reached]
  | append_singleton v a ih =>
    rw [← List.append_assoc, reached_idx_snoc]
    simp only [ih]
    cases t <;> simp [step]

/-- The boundary guard accepts every complete code. -/
theorem accepts_enc (w : List (Fin 2)) : (allFinalCode M).Accepts (enc w) := by
  rw [accepts_iff_reached]
  exact ⟨idx g, (reached_enc M w g).mpr trivial, rfl⟩

/-- The pending guard accepts every code followed by `0`. -/
theorem accepts_enc_zero (w : List (Fin 2)) : (allFinalCode M).Accepts (enc w ++ [0]) := by
  rw [accepts_iff_reached]
  exact ⟨idx h, (reached_enc_zero M w h).mpr trivial, rfl⟩

/-- A code terminated by `1`, with any suffix, is accepted iff the source word is accepted. -/
theorem accepts_enc_one (w v : List (Fin 2)) :
    (allFinalCode M).Accepts (enc w ++ [1] ++ v) ↔ M.Accepts w := by
  rw [accepts_iff_reached, idx_surjective.exists]
  simp only [reached_enc_one]
  simp [allFinalCode]

/-- Every binary word is a complete code, a pending code, or a terminated code with a suffix. -/
theorem word_cases (u : List (Fin 2)) :
    (∃ w, u = enc w) ∨ (∃ w, u = enc w ++ [0]) ∨
      (∃ w v, u = enc w ++ [1] ++ v) := by
  induction u using List.twoStepInduction with
  | nil => exact Or.inl ⟨[], rfl⟩
  | singleton a =>
    fin_cases a
    · exact Or.inr (Or.inl ⟨[], rfl⟩)
    · exact Or.inr (Or.inr ⟨[], [], rfl⟩)
  | cons_cons a b u ih _ =>
    fin_cases a
    · rcases ih with ⟨w, rfl⟩ | ⟨w, rfl⟩ | ⟨w, v, rfl⟩
      · exact Or.inl ⟨b :: w, rfl⟩
      · exact Or.inr (Or.inl ⟨b :: w, rfl⟩)
      · exact Or.inr (Or.inr ⟨b :: w, v, rfl⟩)
    · exact Or.inr (Or.inr ⟨[], b :: u, rfl⟩)

end AllFinal

/-- The all-final encoding preserves universality for every source state count. -/
theorem allFinalCode_universal_iff {m : ℕ} (M : BinNFA m) :
    (∀ u, (allFinalCode M).Accepts u) ↔ ∀ w, M.Accepts w := by
  constructor
  · intro h w
    exact (accepts_enc_one M w []).mp (h _)
  · intro h u
    rcases word_cases u with ⟨w, rfl⟩ | ⟨w, rfl⟩ | ⟨w, v, rfl⟩
    · exact accepts_enc M w
    · exact accepts_enc_zero M w
    · exact (accepts_enc_one M w v).mpr (h w)

/-- Every state of the encoding is final. -/
@[simp] theorem allFinalCode_final {m : ℕ} (M : BinNFA m) (q : Fin (2 * m + 3)) :
    (allFinalCode M).final q = true := rfl

/-- The boundary guard accepts the empty word, even with no source initial states. -/
theorem allFinalCode_accepts_nil {m : ℕ} (M : BinNFA m) : (allFinalCode M).Accepts [] :=
  accepts_enc M []

/-- There is one edge per source state, transition, and final state, plus five fixed edges. -/
theorem allFinalCode_length_trans {m : ℕ} (M : BinNFA m) :
    (allFinalCode M).trans.length =
      m + M.trans.length + ((List.finRange m).filter M.final).length + 5 := by
  simp [allFinalCode, edges, Nat.add_assoc]

/-- The encoding has at most `T + 2 m + 5` transitions. -/
theorem allFinalCode_length_trans_le {m : ℕ} (M : BinNFA m) :
    (allFinalCode M).trans.length ≤ M.trans.length + 2 * m + 5 := by
  have hf := List.length_filter_le M.final (List.finRange m)
  rw [List.length_finRange] at hf
  rw [allFinalCode_length_trans]
  omega

end DeciNSSE.Complexity
