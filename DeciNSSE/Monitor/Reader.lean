import DeciNSSE.RejectedTail.Basic
import DeciNSSE.Satisfiability.Decide
import DeciNSSE.Semantics.Selector
import DeciNSSE.Transfer.Safety

/-! # The finite label reader

A state records upper labels, lower labels and a latch for earlier readiness.
Acceptance also tests current readiness and the terminal child condition.
Cross and self admissions detect periodic comparisons. There are `2 * 4^m`
states for `m` variables, hence `2 * 4^(2*k)` after signed translation.
-/

set_option autoImplicit false

namespace DeciNSSE.Monitor

open FiniteVariance RejectedTail

/-- A label state: upper labels `U`, lower labels `L`, acceptance latch `b`. -/
structure State (m : ℕ) where
  /-- Variables with an upper bound along the path read so far. -/
  U : Finset (V m)
  /-- Variables with a lower bound along the path read so far. -/
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

instance instFintypeState (m : ℕ) : Fintype (State m) :=
  Fintype.ofEquiv _ (State.equiv m).symm

/-- The label reader has exactly two label sets and one Boolean latch. -/
theorem card_state (m : ℕ) : Fintype.card (State m) = 2 * 4 ^ m := by
  rw [Fintype.card_congr (State.equiv m)]
  simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin, Fintype.card_bool]
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  ring

variable {n m k : ℕ}

section Executable

variable (ψ : Constraint n m) (pairs : Finset (V m × V m))

/-- `E_i U`: the one-letter upper extension, over a precomputed closure. -/
def upperStep (i : Fin n) (U : Finset (V m)) : Finset (V m) :=
  Finset.univ.filter fun v => ∃ u ∈ U, PathDecision.upper ψ pairs [i] u v = true

/-- `F_i L`: the one-letter lower extension, over a precomputed closure. -/
def lowerStep (i : Fin n) (L : Finset (V m)) : Finset (V m) :=
  Finset.univ.filter fun v => ∃ u ∈ L, PathDecision.lower ψ pairs [i] v u = true

end Executable

/-- The label sets witness a bottom, top or common-variable clash. -/
def Ready (ψ : Constraint n m) (U L : Finset (V m)) : Prop :=
  (∃ u ∈ U, u ∈ botVars ψ) ∨ (∃ v ∈ L, v ∈ topVars ψ) ∨ (∃ u ∈ U, u ∈ L)

instance instDecidableReady (ψ : Constraint n m) (U L : Finset (V m)) :
    Decidable (Ready ψ U L) :=
  inferInstanceAs (Decidable ((∃ u ∈ U, u ∈ botVars ψ) ∨ (∃ v ∈ L, v ∈ topVars ψ) ∨
    (∃ u ∈ U, u ∈ L)))

/-- The letter-free child condition of side `θ`: some upper (lower) label
carries an upper (lower) constructor literal. -/
def Child (ψ : Constraint n m) : Side → Finset (V m) → Finset (V m) → Prop
  | .l, U, _ => ∃ p ∈ upperLits ψ, p.1 ∈ U
  | .r, _, L => ∃ p ∈ lowerLits ψ, p.2 ∈ L

instance instDecidableChild (ψ : Constraint n m) :
    (θ : Side) → (U L : Finset (V m)) → Decidable (Child ψ θ U L)
  | .l, U, _ => inferInstanceAs (Decidable (∃ p ∈ upperLits ψ, p.1 ∈ U))
  | .r, _, L => inferInstanceAs (Decidable (∃ p ∈ lowerLits ψ, p.2 ∈ L))

/-- Acceptance of a label state on side `θ`: latch, readiness or child. -/
def Accept (ψ : Constraint n m) (θ : Side) (S : State m) : Prop :=
  S.b = true ∨ Ready ψ S.U S.L ∨ Child ψ θ S.U S.L

instance instDecidableAccept (ψ : Constraint n m) (θ : Side) (S : State m) :
    Decidable (Accept ψ θ S) :=
  inferInstanceAs (Decidable (S.b = true ∨ Ready ψ S.U S.L ∨ Child ψ θ S.U S.L))

/-- The label DFA over a given closure `pairs`. -/
def readerOf (ψ : Constraint n m) (pairs : Finset (V m × V m)) (X Y : V m) (θ : Side) :
    DFA (Fin n) (State m) where
  step S i := ⟨upperStep ψ pairs i S.U, lowerStep ψ pairs i S.L,
    S.b || decide (Ready ψ S.U S.L)⟩
  start := ⟨Finset.univ.filter (fun v => (X, v) ∈ pairs),
    Finset.univ.filter (fun v => (v, Y) ∈ pairs), false⟩
  accept := {S | Accept ψ θ S}

/-- The label DFA of `ψ ⊨? X ≤ Y` on side `θ` (the side only matters for
its accepting states). -/
def reader (ψ : Constraint n m) (X Y : V m) (θ : Side) : DFA (Fin n) (State m) :=
  readerOf ψ (derivedPairs ψ) X Y θ

/-- The target: the rejected label states. -/
def target (ψ : Constraint n m) (θ : Side) : Set (State m) := {S | ¬ Accept ψ θ S}

instance instDecidableMemTarget (ψ : Constraint n m) (θ : Side) :
    DecidablePred (· ∈ target ψ θ) :=
  fun S => inferInstanceAs (Decidable (¬ Accept ψ θ S))

/-- Opposite label sets intersect in the orientation selected by the side. -/
def Cross : Side → State m → State m → Prop
  | .l, S, S' => ∃ v ∈ S.L, v ∈ S'.U
  | .r, S, S' => ∃ u ∈ S.U, u ∈ S'.L

instance instDecidableCross : (θ : Side) → (S S' : State m) → Decidable (Cross θ S S')
  | .l, S, S' => inferInstanceAs (Decidable (∃ v ∈ S.L, v ∈ S'.U))
  | .r, S, S' => inferInstanceAs (Decidable (∃ u ∈ S.U, u ∈ S'.L))

/-- Self admission over doubled variables: left `U_s ∩ flipV U_e ≠ ∅`,
right `L_s ∩ flipV L_e ≠ ∅`. -/
def Self : Side → State (2 * k) → State (2 * k) → Prop
  | .l, S, S' => ∃ z ∈ S.U, flipV z ∈ S'.U
  | .r, S, S' => ∃ z ∈ S.L, flipV z ∈ S'.L

instance instDecidableSelf :
    (θ : Side) → (S S' : State (2 * k)) → Decidable (Self θ S S')
  | .l, S, S' => inferInstanceAs (Decidable (∃ z ∈ S.U, flipV z ∈ S'.U))
  | .r, S, S' => inferInstanceAs (Decidable (∃ z ∈ S.L, flipV z ∈ S'.L))

/-- The relation of the label monitor: cross or self admission. -/
def admission (θ : Side) (S S' : State (2 * k)) : Prop := Cross θ S S' ∨ Self θ S S'

instance instDecidableRelAdmission (θ : Side) : DecidableRel (admission (k := k) θ) :=
  fun S S' => inferInstanceAs (Decidable (Cross θ S S' ∨ Self θ S S'))

/-- The labels of side `θ`: upper on the left, lower on the right. -/
def sideLabels : Side → State m → Finset (V m)
  | .l, S => S.U
  | .r, S => S.L

/-- Every admission needs a label of its side at its second cut. -/
theorem admission_sideLabels {θ : Side} {S S' : State (2 * k)} (h : admission θ S S') :
    ∃ v, v ∈ sideLabels θ S' := by
  cases θ
  · rcases h with ⟨v, -, hv⟩ | ⟨z, -, hz⟩
    · exact ⟨v, hv⟩
    · exact ⟨_, hz⟩
  · rcases h with ⟨v, -, hv⟩ | ⟨z, -, hz⟩
    · exact ⟨v, hv⟩
    · exact ⟨_, hz⟩

/-- The child condition needs a label of its side. -/
theorem child_sideLabels {ψ : Constraint n m} {θ : Side} {S : State m}
    (h : Child ψ θ S.U S.L) : ∃ v, v ∈ sideLabels θ S := by
  cases θ
  · obtain ⟨p, -, hp⟩ := h; exact ⟨_, hp⟩
  · obtain ⟨p, -, hp⟩ := h; exact ⟨_, hp⟩

section Semantics

variable {ψ : Constraint n m} {X Y : V m} {θ : Side}

@[simp] theorem reader_step (S : State m) (i : Fin n) :
    (reader ψ X Y θ).step S i =
      ⟨upperStep ψ (derivedPairs ψ) i S.U, lowerStep ψ (derivedPairs ψ) i S.L,
        S.b || decide (Ready ψ S.U S.L)⟩ := rfl

theorem reader_start :
    (reader ψ X Y θ).start = ⟨Finset.univ.filter (fun v => (X, v) ∈ derivedPairs ψ),
      Finset.univ.filter (fun v => (v, Y) ∈ derivedPairs ψ), false⟩ := rfl

theorem mem_upperStep_iff {i : Fin n} {U : Finset (V m)} {v : V m} :
    v ∈ upperStep ψ (derivedPairs ψ) i U ↔ ∃ u ∈ U, UpperAt ψ [i] u v := by
  simp only [upperStep, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun u => and_congr_right fun _ => upperAtB_iff ψ [i] u v

theorem mem_lowerStep_iff {i : Fin n} {L : Finset (V m)} {v : V m} :
    v ∈ lowerStep ψ (derivedPairs ψ) i L ↔ ∃ u ∈ L, LowerAt ψ [i] v u := by
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and]
  exact exists_congr fun u => and_congr_right fun _ => lowerAtB_iff ψ [i] v u

/-- Upper labels. After reading `w`, `U` holds exactly the upper path
bounds of `X` along `w`. -/
theorem mem_eval_U (w : List (Fin n)) (v : V m) :
    v ∈ ((reader ψ X Y θ).eval w).U ↔ UpperAt ψ w X v := by
  induction w using List.reverseRecOn generalizing v with
  | nil =>
    simp [reader_start, mem_derivedPairs]
  | append_singleton w i ih =>
    simp only [DFA.eval_append_singleton, reader_step, mem_upperStep_iff]
    constructor
    · rintro ⟨u, hu, hi⟩
      exact ((ih u).mp hu).comp hi
    · intro h
      obtain ⟨u, hu, hi⟩ := UpperAt.factor h
      exact ⟨u, (ih u).mpr hu, hi⟩

/-- Lower labels. After reading `w`, `L` holds exactly the lower path
bounds of `Y` along `w`. -/
theorem mem_eval_L (w : List (Fin n)) (v : V m) :
    v ∈ ((reader ψ X Y θ).eval w).L ↔ LowerAt ψ w v Y := by
  induction w using List.reverseRecOn generalizing v with
  | nil =>
    simp [reader_start, mem_derivedPairs]
  | append_singleton w i ih =>
    simp only [DFA.eval_append_singleton, reader_step, mem_lowerStep_iff]
    constructor
    · rintro ⟨u, hu, hi⟩
      exact hi.comp ((ih u).mp hu)
    · intro h
      obtain ⟨u, hu, hi⟩ := LowerAt.factor (π := w) (π' := [i]) h
      exact ⟨u, (ih u).mpr hu, hi⟩

/-- Readiness along a path. -/
def ReadyAt (ψ : Constraint n m) (X Y : V m) (π : List (Fin n)) : Prop :=
  (∃ u, UpperAt ψ π X u ∧ u ∈ botVars ψ) ∨ (∃ v, LowerAt ψ π v Y ∧ v ∈ topVars ψ) ∨
    (∃ u, UpperAt ψ π X u ∧ LowerAt ψ π u Y)

/-- The letter-free child condition along a path. -/
def ChildAt (ψ : Constraint n m) (X Y : V m) : Side → List (Fin n) → Prop
  | .l, π => ∃ z b, UpperAt ψ π X z ∧ Lit.leF z b ∈ ψ
  | .r, π => ∃ a z, LowerAt ψ π z Y ∧ Lit.fLe a z ∈ ψ

/-- Acceptance along a path: readiness at a strictly earlier cut, readiness, or a child. -/
def AcceptAt (ψ : Constraint n m) (X Y : V m) (θ : Side) (π : List (Fin n)) : Prop :=
  (∃ j < π.length, ReadyAt ψ X Y (π.take j)) ∨ ReadyAt ψ X Y π ∨ ChildAt ψ X Y θ π

theorem ready_eval_iff (π : List (Fin n)) :
    Ready ψ ((reader ψ X Y θ).eval π).U ((reader ψ X Y θ).eval π).L ↔ ReadyAt ψ X Y π := by
  simp only [Ready, ReadyAt, mem_eval_U, mem_eval_L]

theorem child_eval_iff (π : List (Fin n)) :
    Child ψ θ ((reader ψ X Y θ).eval π).U ((reader ψ X Y θ).eval π).L ↔
      ChildAt ψ X Y θ π := by
  cases θ
  · simp only [Child, ChildAt, mem_eval_U, Prod.exists, mem_upperLits]
    exact ⟨fun ⟨z, b, hl, hz⟩ => ⟨z, b, hz, hl⟩, fun ⟨z, b, hz, hl⟩ => ⟨z, b, hl, hz⟩⟩
  · simp only [Child, ChildAt, mem_eval_L, Prod.exists, mem_lowerLits]
    exact ⟨fun ⟨a, z, hl, hz⟩ => ⟨a, z, hz, hl⟩, fun ⟨a, z, hz, hl⟩ => ⟨a, z, hl, hz⟩⟩

/-- The latch records readiness at a strictly earlier cut. -/
theorem eval_b_iff (w : List (Fin n)) :
    ((reader ψ X Y θ).eval w).b = true ↔ ∃ j < w.length, ReadyAt ψ X Y (w.take j) := by
  induction w using List.reverseRecOn with
  | nil => simp [reader_start]
  | append_singleton w i ih =>
    simp only [DFA.eval_append_singleton, reader_step, Bool.or_eq_true, decide_eq_true_eq, ih, ready_eval_iff, List.length_append,
      List.length_singleton]
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

theorem accept_eval_iff (w : List (Fin n)) :
    Accept ψ θ ((reader ψ X Y θ).eval w) ↔ AcceptAt ψ X Y θ w := by
  simp only [Accept, AcceptAt, eval_b_iff, ready_eval_iff, child_eval_iff]

theorem mem_target_iff (w : List (Fin n)) :
    (reader ψ X Y θ).eval w ∈ target ψ θ ↔ ¬ AcceptAt ψ X Y θ w :=
  not_congr (accept_eval_iff w)

/-- An upper label strictly after the cut `π` needs a left child at `π`. -/
theorem childAt_of_upper {π τ : List (Fin n)} {v : V m} (hτ : τ ≠ [])
    (h : UpperAt ψ (π ++ τ) X v) : ChildAt ψ X Y .l π := by
  obtain ⟨a, ha, ht⟩ := UpperAt.factor h
  cases τ with
  | nil => exact (hτ rfl).elim
  | cons i τ =>
    cases ht with
    | cons hd hl _ =>
      exact ⟨_, _, by simpa using ha.comp (UpperAt.nil hd), hl⟩

/-- A lower label strictly after the cut `π` needs a right child at `π`. -/
theorem childAt_of_lower {π τ : List (Fin n)} {v : V m} (hτ : τ ≠ [])
    (h : LowerAt ψ (π ++ τ) v Y) : ChildAt ψ X Y .r π := by
  obtain ⟨a, ha, ht⟩ := LowerAt.factor (π := π) (π' := τ) h
  cases τ with
  | nil => exact (hτ rfl).elim
  | cons i τ =>
    cases ht with
    | cons hl hd _ =>
      exact ⟨_, _, by simpa using (LowerAt.nil hd).comp ha, hl⟩

/-- Without a child of side `θ` at `π`, side `θ` has no label at any later cut. -/
theorem sideLabels_dead {π τ : List (Fin n)} (hτ : τ ≠ []) (hc : ¬ ChildAt ψ X Y θ π)
    (v : V m) : v ∉ sideLabels θ ((reader ψ X Y θ).eval (π ++ τ)) := by
  cases θ
  · intro h
    exact hc (childAt_of_upper hτ ((mem_eval_U _ v).mp h))
  · intro h
    exact hc (childAt_of_lower hτ ((mem_eval_L _ v).mp h))

/-- The latch is monotone along prefixes. -/
theorem eval_b_append {u τ : List (Fin n)} (h : ((reader ψ X Y θ).eval u).b = true) :
    ((reader ψ X Y θ).eval (u ++ τ)).b = true := by
  obtain ⟨j, hj, hr⟩ := (eval_b_iff u).mp h
  refine (eval_b_iff _).mpr ⟨j, by simp only [List.length_append]; omega, ?_⟩
  rwa [List.take_append_of_le_length (show j ≤ u.length by omega)]

/-- Readiness at a cut sets the latch at every strictly later cut. -/
theorem eval_b_of_ready {u τ : List (Fin n)} (hτ : τ ≠ []) (h : ReadyAt ψ X Y u) :
    ((reader ψ X Y θ).eval (u ++ τ)).b = true := by
  refine (eval_b_iff _).mpr ⟨u.length, ?_, ?_⟩
  · have := List.length_pos_iff.mpr hτ
    simp only [List.length_append]; omega
  · rwa [List.take_append_of_le_length le_rfl, List.take_length]

end Semantics

section Interface

variable {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {θ : Side}

instance rejectedPath :
    RejectedPath (reader ψ X Y θ) (admission θ) (target ψ θ) where
  between := by
    intro v u w hvu huw hv hw
    rw [mem_target_iff] at hv hw ⊢
    obtain ⟨τ₂, rfl⟩ := huw
    intro hacc
    rcases (accept_eval_iff (θ := θ) u).mpr hacc with hb | hr | hch
    · exact hw ((accept_eval_iff _).mp (Or.inl (eval_b_append hb)))
    · by_cases hτ : τ₂ = []
      · subst τ₂; rw [List.append_nil] at hw; exact hw hacc
      · rw [ready_eval_iff] at hr
        exact hw ((accept_eval_iff _).mp (Or.inl (eval_b_of_ready hτ hr)))
    · obtain ⟨τ₁, rfl⟩ := hvu
      by_cases hτ : τ₁ = []
      · subst τ₁; rw [List.append_nil] at hacc; exact hv hacc
      · have hc : ¬ ChildAt ψ X Y θ v := fun h => hv (Or.inr (Or.inr h))
        obtain ⟨z, hz⟩ := child_sideLabels hch
        exact sideLabels_dead hτ hc z hz
  cone := by
    intro w J _ hJ s e hse he _ hr
    by_contra hlt
    rw [not_le] at hlt
    have hc : ¬ ChildAt ψ X Y θ (w.take J) := by
      have h := hJ.2.1
      rw [mem_target_iff] at h
      exact fun hc => h (Or.inr (Or.inr hc))
    have hτ : (w.drop J).take (e - J) ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · rw [List.drop_eq_nil_iff] at h; omega
    have hcut : w.take e = w.take J ++ (w.drop J).take (e - J) := by
      rw [← List.take_add]; congr 1; omega
    obtain ⟨z, hz⟩ := admission_sideLabels hr
    rw [hcut] at hz
    exact sideLabels_dead hτ hc z hz

end Interface

end DeciNSSE.Monitor
