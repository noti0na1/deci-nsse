import DeciNSSE.Monitor.Events
import DeciNSSE.RejectedTail.Basic
import DeciNSSE.Satisfiability.BoundSets

/-! # The finite label reader

A state records upper labels, lower labels and a latch for earlier readiness.
Acceptance also tests current readiness and the terminal child condition.
Cross and self admissions detect periodic comparisons. There are `2 * 4^m`
states for `m` variables, hence `2 * 4^(2*k)` after signed translation.
The label sets are the bound sets `upperSet ψ X` and `lowerSet ψ Y` along the
word read so far.

## Main declarations

- `Monitor.State`, `Monitor.card_state`: label states, `2 * 4^m` of them.
- `Monitor.reader`: the label DFA of `ψ ⊨? X ≤ Y`, with `Monitor.target` its rejected
  states and `Monitor.admission` its admissions.
- `Monitor.eval_U`, `Monitor.eval_L`, `Monitor.accept_eval_iff`: after reading a word,
  the labels are its upper and lower bound sets, and acceptance is acceptance along the
  path.
- `Monitor.rejectedPath`: the reader has the rejected-path property, so the generic hole
  bounds apply to it.
-/

namespace DeciNSSE.Monitor

open SignDuality RejectedTail Events

/-- A label state: upper labels `U`, lower labels `L`, acceptance latch `b`. -/
structure State (m : ℕ) where
  /-- The upper path bounds of the first root along the word read so far. -/
  U : Finset (V m)
  /-- The lower path bounds of the second root along the word read so far. -/
  L : Finset (V m)
  /-- Whether readiness occurred at a strictly earlier cut. -/
  b : Bool
  deriving DecidableEq

/-- Label states are triples. -/
def State.equiv (m : ℕ) : State m ≃ Finset (V m) × Finset (V m) × Bool where
  toFun S := (S.U, S.L, S.b)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Label states are finite. -/
instance instFintypeState (m : ℕ) : Fintype (State m) :=
  Fintype.ofEquiv _ (State.equiv m).symm

/-- The label reader has exactly two label sets and one Boolean latch. -/
theorem card_state (m : ℕ) : Fintype.card (State m) = 2 * 4 ^ m := by
  rw [Fintype.card_congr (State.equiv m)]
  simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, Fintype.card_bool]
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  ring

variable {n m k : ℕ}

/-- The label sets witness a bottom, top or common-variable clash. -/
def Ready (ψ : Constraint n m) (U L : Finset (V m)) : Prop :=
  (∃ u ∈ U, u ∈ botVars ψ) ∨ (∃ v ∈ L, v ∈ topVars ψ) ∨ (∃ u ∈ U, u ∈ L)

/-- Readiness of label sets is decidable. -/
instance instDecidableReady (ψ : Constraint n m) (U L : Finset (V m)) :
    Decidable (Ready ψ U L) :=
  inferInstanceAs (Decidable ((∃ u ∈ U, u ∈ botVars ψ) ∨ (∃ v ∈ L, v ∈ topVars ψ) ∨
    (∃ u ∈ U, u ∈ L)))

/-- Acceptance of a label state: latch, readiness, or a child (an upper label
carrying an upper constructor literal). -/
def Accept (ψ : Constraint n m) (S : State m) : Prop :=
  S.b = true ∨ Ready ψ S.U S.L ∨ ∃ p ∈ upperLits ψ, p.1 ∈ S.U

/-- Acceptance of a label state is decidable. -/
instance instDecidableAccept (ψ : Constraint n m) (S : State m) : Decidable (Accept ψ S) :=
  inferInstanceAs (Decidable (S.b = true ∨ Ready ψ S.U S.L ∨ ∃ p ∈ upperLits ψ, p.1 ∈ S.U))

/-- The label DFA over a given closure `pairs`. -/
def readerOf (ψ : Constraint n m) (pairs : Finset (V m × V m)) (X Y : V m) :
    DFA (Fin n) (State m) where
  step S i := ⟨upperStep ψ pairs i S.U, lowerStep ψ pairs i S.L,
    S.b || decide (Ready ψ S.U S.L)⟩
  start := ⟨Finset.univ.filter (fun v => (X, v) ∈ pairs),
    Finset.univ.filter (fun v => (v, Y) ∈ pairs), false⟩
  accept := {S | Accept ψ S}

/-- The label DFA of `ψ ⊨? X ≤ Y`. -/
def reader (ψ : Constraint n m) (X Y : V m) : DFA (Fin n) (State m) :=
  readerOf ψ (derivedPairs ψ) X Y

/-- The target: the rejected label states. -/
def target (ψ : Constraint n m) : Set (State m) := {S | ¬ Accept ψ S}

/-- Membership in the target is decidable. -/
instance instDecidableMemTarget (ψ : Constraint n m) : DecidablePred (· ∈ target ψ) :=
  fun S => inferInstanceAs (Decidable (¬ Accept ψ S))

/-- The admission relation of the label reader over signed variables: cross admission
`L_s ∩ U_e ≠ ∅` or self admission `U_s ∩ flipV U_e ≠ ∅`. -/
def admission (S S' : State (2 * k)) : Prop :=
  (∃ v ∈ S.L, v ∈ S'.U) ∨ ∃ z ∈ S.U, flipV z ∈ S'.U

/-- Admission is decidable. -/
instance instDecidableRelAdmission : DecidableRel (admission (k := k)) :=
  fun S S' => inferInstanceAs (Decidable ((∃ v ∈ S.L, v ∈ S'.U) ∨ ∃ z ∈ S.U, flipV z ∈ S'.U))

/-- Every admission needs an upper label at its second cut. -/
theorem admission_upper {S S' : State (2 * k)} (h : admission S S') : ∃ v, v ∈ S'.U := by
  rcases h with ⟨v, -, hv⟩ | ⟨z, -, hz⟩
  exacts [⟨v, hv⟩, ⟨_, hz⟩]

section Semantics

variable {ψ : Constraint n m} {X Y : V m}

/-- One transition extends both label sets and records readiness in the latch. -/
@[simp] theorem reader_step (S : State m) (i : Fin n) :
    (reader ψ X Y).step S i =
      ⟨upperStep ψ (derivedPairs ψ) i S.U, lowerStep ψ (derivedPairs ψ) i S.L,
        S.b || decide (Ready ψ S.U S.L)⟩ := rfl

/-- The start state holds the closure bounds of `X` and `Y`. -/
theorem reader_start :
    (reader ψ X Y).start = ⟨Finset.univ.filter (fun v => (X, v) ∈ derivedPairs ψ),
      Finset.univ.filter (fun v => (v, Y) ∈ derivedPairs ψ), false⟩ := rfl

/-- Upper labels. After reading `w`, `U` is the set of upper path bounds of `X`
along `w`. -/
theorem eval_U (w : List (Fin n)) : ((reader ψ X Y).eval w).U = upperSet ψ X w := by
  induction w using List.reverseRecOn with
  | nil => ext v; simp [reader_start, mem_derivedPairs]
  | append_singleton w i ih => rw [DFA.eval_append_singleton, reader_step, ih, upperSet_append]

/-- Lower labels. After reading `w`, `L` is the set of lower path bounds of `Y`
along `w`. -/
theorem eval_L (w : List (Fin n)) : ((reader ψ X Y).eval w).L = lowerSet ψ Y w := by
  induction w using List.reverseRecOn with
  | nil => ext v; simp [reader_start, mem_derivedPairs]
  | append_singleton w i ih => rw [DFA.eval_append_singleton, reader_step, ih, lowerSet_append]

@[simp] theorem mem_eval_U (w : List (Fin n)) (v : V m) :
    v ∈ ((reader ψ X Y).eval w).U ↔ UpperAt ψ w X v := by
  rw [eval_U, mem_upperSet]

@[simp] theorem mem_eval_L (w : List (Fin n)) (v : V m) :
    v ∈ ((reader ψ X Y).eval w).L ↔ LowerAt ψ w v Y := by
  rw [eval_L, mem_lowerSet]

/-- Acceptance along a path: readiness at some cut, or the child condition at the end. -/
def AcceptAt (ψ : Constraint n m) (X Y : V m) (π : List (Fin n)) : Prop :=
  (∃ j ≤ π.length, ReadyAt ψ X Y (π.take j)) ∨ ChildAt ψ X π

/-- Readiness of the labels after `π` is readiness along `π`. -/
theorem ready_eval_iff (π : List (Fin n)) :
    Ready ψ ((reader ψ X Y).eval π).U ((reader ψ X Y).eval π).L ↔ ReadyAt ψ X Y π := by
  simp only [Ready, ReadyAt, mem_eval_U, mem_eval_L, mem_botVars, mem_topVars]

/-- The child condition of the labels after `π` is the child condition along `π`. -/
theorem child_eval_iff (π : List (Fin n)) :
    (∃ p ∈ upperLits ψ, p.1 ∈ ((reader ψ X Y).eval π).U) ↔ ChildAt ψ X π := by
  simp only [ChildAt, mem_eval_U, Prod.exists, mem_upperLits]
  exact ⟨fun ⟨z, b, hl, hz⟩ => ⟨z, hz, b, hl⟩, fun ⟨z, hz, b, hl⟩ => ⟨z, b, hl, hz⟩⟩

/-- The latch records readiness at a strictly earlier cut. -/
theorem eval_b_iff (w : List (Fin n)) :
    ((reader ψ X Y).eval w).b = true ↔ ∃ j < w.length, ReadyAt ψ X Y (w.take j) := by
  induction w using List.reverseRecOn with
  | nil => simp [reader_start]
  | append_singleton w i ih =>
    simp only [DFA.eval_append_singleton, reader_step, Bool.or_eq_true, decide_eq_true_eq, ih,
      ready_eval_iff, List.length_append, List.length_singleton]
    constructor
    · rintro (⟨j, hj, hr⟩ | hr)
      · refine ⟨j, by omega, ?_⟩
        rwa [List.take_append_of_le_length (show j ≤ w.length by omega)]
      · refine ⟨w.length, by omega, ?_⟩
        rwa [List.take_append_of_le_length le_rfl, List.take_length]
    · rintro ⟨j, hj, hr⟩
      rw [List.take_append_of_le_length (show j ≤ w.length by omega)] at hr
      by_cases hjw : j < w.length
      · exact Or.inl ⟨j, hjw, hr⟩
      · obtain rfl : j = w.length := by omega
        rw [List.take_length] at hr
        exact Or.inr hr

/-- Acceptance after reading `w` is acceptance along `w`. -/
theorem accept_eval_iff (w : List (Fin n)) :
    Accept ψ ((reader ψ X Y).eval w) ↔ AcceptAt ψ X Y w := by
  simp only [Accept, AcceptAt, eval_b_iff, ready_eval_iff, child_eval_iff, ← or_assoc]
  refine or_congr_left ⟨?_, ?_⟩
  · rintro (⟨j, hj, h⟩ | h)
    · exact ⟨j, hj.le, h⟩
    · exact ⟨w.length, le_rfl, by rwa [List.take_length]⟩
  · rintro ⟨j, hj, h⟩
    rcases hj.lt_or_eq with hlt | rfl
    · exact Or.inl ⟨j, hlt, h⟩
    · exact Or.inr (by rwa [List.take_length] at h)

/-- The reader ends in the target exactly when `w` is not accepted along its path. -/
theorem mem_target_iff (w : List (Fin n)) :
    (reader ψ X Y).eval w ∈ target ψ ↔ ¬ AcceptAt ψ X Y w :=
  not_congr (accept_eval_iff w)

/-- An upper label strictly after the cut `π` needs a child at `π`. -/
theorem childAt_of_upper {π τ : List (Fin n)} {v : V m} (hτ : τ ≠ [])
    (h : v ∈ ((reader ψ X Y).eval (π ++ τ)).U) : ChildAt ψ X π := by
  obtain ⟨a, ha, ht⟩ := UpperAt.factor ((mem_eval_U _ v).mp h)
  cases τ with
  | nil => exact (hτ rfl).elim
  | cons i τ =>
    cases ht with
    | cons hd hl _ =>
      exact ⟨_, by simpa using ha.comp (UpperAt.nil hd), _, hl⟩

/-- The latch is monotone along prefixes. -/
theorem eval_b_append {u τ : List (Fin n)} (h : ((reader ψ X Y).eval u).b = true) :
    ((reader ψ X Y).eval (u ++ τ)).b = true := by
  obtain ⟨j, hj, hr⟩ := (eval_b_iff u).mp h
  refine (eval_b_iff _).mpr ⟨j, by simp only [List.length_append]; omega, ?_⟩
  rwa [List.take_append_of_le_length (show j ≤ u.length by omega)]

/-- Readiness at a cut sets the latch at every strictly later cut. -/
theorem eval_b_of_ready {u τ : List (Fin n)} (hτ : τ ≠ []) (h : ReadyAt ψ X Y u) :
    ((reader ψ X Y).eval (u ++ τ)).b = true := by
  refine (eval_b_iff _).mpr ⟨u.length, ?_, ?_⟩
  · have := List.length_pos_iff.mpr hτ
    simp only [List.length_append]; omega
  · rwa [List.take_append_of_le_length le_rfl, List.take_length]

end Semantics

section Interface

variable {ψ : Constraint n (2 * k)} {X Y : V (2 * k)}

/-- The label reader has the rejected-path property: a prefix between two rejected
prefixes is rejected, and on a rejected word every admitted comparison ends at or before
the first rejected prefix. -/
instance rejectedPath : RejectedPath (reader ψ X Y) admission (target ψ) where
  between := by
    intro v u w hvu huw hv hw
    rw [mem_target_iff] at hv hw ⊢
    obtain ⟨τ₂, rfl⟩ := huw
    intro hacc
    rcases (accept_eval_iff u).mpr hacc with hb | hr | ⟨p, -, hp⟩
    · exact hw ((accept_eval_iff _).mp (Or.inl (eval_b_append hb)))
    · by_cases hτ : τ₂ = []
      · subst τ₂; rw [List.append_nil] at hw; exact hw hacc
      · rw [ready_eval_iff] at hr
        exact hw ((accept_eval_iff _).mp (Or.inl (eval_b_of_ready hτ hr)))
    · obtain ⟨τ₁, rfl⟩ := hvu
      by_cases hτ : τ₁ = []
      · subst τ₁; rw [List.append_nil] at hacc; exact hv hacc
      · exact hv (Or.inr (childAt_of_upper hτ hp))
  cone := by
    intro w J _ hJ s e hse he _ hr
    by_contra hlt
    rw [not_le] at hlt
    have hc : ¬ ChildAt ψ X (w.take J) := by
      have h := hJ.2.1
      rw [mem_target_iff] at h
      exact fun hc => h (Or.inr hc)
    have hτ : (w.drop J).take (e - J) ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · rw [List.drop_eq_nil_iff] at h; omega
    have hcut : w.take e = w.take J ++ (w.drop J).take (e - J) := by
      rw [← List.take_add]; congr 1; omega
    obtain ⟨z, hz⟩ := admission_upper hr
    rw [hcut] at hz
    exact hc (childAt_of_upper hτ hz)

end Interface

end DeciNSSE.Monitor
