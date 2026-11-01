import DeciNSSE.Main

/-! # Holes and entailment at arity one

Over a one-letter alphabet, words of equal length are equal, so every pair of
cuts `s < e ≤ |w|` is a comparison: `w.drop e` is a prefix of `w.drop s`.
Let `J` be the first rejected cut of a hole `w`, the first cut whose state is in
the target. The prefix of length `J` reaches the target, and its comparisons,
terminal ones included, are comparisons of `w` with the same states; so it is a
hole. The states at the cuts `0, …, J` are pairwise distinct: a repeated state
makes the run periodic, which moves the rejected state at `J` to an earlier cut.
Hence a reader with `N` states that has a hole has one of length at most `N - 1`.
The rejected-path property is not needed.

The hole search reads the single letter for fewer than `N` steps to the first
rejected cut `J`, and tests the one word `a^J`. With this hole decision for the
side monitors, the deciders of `Monitor.Decision` give decision procedures at
arity one in each tree domain, whose hole searches stop below the state count
`2 * 4^(2*k)` of the label monitors.

## Main declarations

- `Unary.exists_hole_length_le`: a hole of a reader with `N` states over a
  one-letter alphabet yields a hole of length at most `N - 1`.
- `Unary.hole_iff_length_le_card_sub_one`: hole existence within that bound.
- `Unary.firstRejectedCut`, `Unary.hole_iff_firstRejectedCut`: hole existence as a
  test of the word up to the first rejected cut, which lies below `N`.
- `Unary.decideHole`, `Unary.decideSideHoles`: the resulting computable hole
  decisions.
- `Unary.unsafe_iff_bounded`: at arity one, unsafe words of a satisfiable
  system have a witness of length at most `2 * 4^(2*k) - 1`.
- `decideEntailsUnary`, `decideEntailsRegUnary`, `decideEntailsFinUnary`:
  entailment at arity one over arbitrary, regular and finite trees, with the
  correctness theorems `decideEntailsUnary_correct`,
  `decideEntailsRegUnary_correct` and `decideEntailsFinUnary_correct`.

All declarations except the top-level deciders are in `DeciNSSE.Complexity.Unary`.
-/

namespace DeciNSSE

namespace Complexity.Unary

open Holes RejectedTail

section Bound

variable {α Q : Type*} [Subsingleton α]

/-- Over a one-letter alphabet, words of equal length are equal. -/
theorem eq_of_length_eq {u v : List α} (h : u.length = v.length) : u = v :=
  List.ext_getElem h fun _ _ _ => Subsingleton.elim _ _

/-- Over a one-letter alphabet, a word is a prefix of every word at least as long. -/
theorem prefix_of_length_le {u v : List α} (h : u.length ≤ v.length) : u <+: v :=
  List.prefix_iff_eq_take.mpr (eq_of_length_eq (by simp only [List.length_take]; omega))

variable (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)

/-- Cutting a hole back to a cut whose state is in the target gives a hole. -/
theorem isReaderHole_take {w : List α} (hw : IsReaderHole M R T w) {J : ℕ}
    (hJ : J ≤ w.length) (hT : M.eval (w.take J) ∈ T) :
    IsReaderHole M R T (w.take J) := by
  rw [isReaderHole_iff] at hw ⊢
  refine ⟨hT, fun s e hse he _ => ?_⟩
  rw [List.length_take_of_le hJ] at he
  rw [List.take_take, List.take_take, min_eq_left (by omega), min_eq_left he]
  exact hw.2 s e hse (by omega) (prefix_of_length_le (by simp only [List.length_drop]; omega))

/-- Equal states at two cuts stay equal after the same number of further letters. -/
theorem eval_take_add {w : List α} {i j t : ℕ} (hij : i ≤ j) (hjt : j + t ≤ w.length)
    (h : M.eval (w.take i) = M.eval (w.take j)) :
    M.eval (w.take (i + t)) = M.eval (w.take (j + t)) := by
  have happ (u v : List α) : M.eval (u ++ v) = M.evalFrom (M.eval u) v :=
    M.evalFrom_of_append M.start u v
  rw [List.take_add, List.take_add, happ, happ, h,
    eq_of_length_eq (u := (w.drop i).take t) (v := (w.drop j).take t)
      (by simp only [List.length_take, List.length_drop]; omega)]

/-- The states at the cuts up to the first rejected cut are pairwise distinct. -/
theorem eval_take_ne {w : List α} {J : ℕ} (hJ : IsFirstRejectedPrefix M T w J) {i j : ℕ}
    (hij : i < j) (hj : j ≤ J) : M.eval (w.take i) ≠ M.eval (w.take j) := by
  intro h
  have hp := eval_take_add M (t := J - j) hij.le (by have := hJ.1; omega) h
  rw [show j + (J - j) = J by omega] at hp
  exact hJ.2.2 (i + (J - j)) (by omega) (hp ▸ hJ.2.1)

/-- The first rejected cut lies below the number of states. -/
theorem firstRejected_lt_card [Fintype Q] {w : List α} {J : ℕ}
    (hJ : IsFirstRejectedPrefix M T w J) : J < Fintype.card Q := by
  have hinj : Function.Injective fun i : Fin (J + 1) => M.eval (w.take i) := by
    intro i j h
    rcases lt_trichotomy (i : ℕ) j with hlt | heq | hgt
    · exact absurd h (eval_take_ne M T hJ hlt (by omega))
    · exact Fin.ext heq
    · exact absurd h.symm (eval_take_ne M T hJ hgt (by omega))
  have := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_fin] at this
  omega

/-- A reader over a one-letter alphabet with `N` states that has a hole has one
of length at most `N - 1`, namely its prefix up to the first rejected cut. -/
theorem exists_hole_length_le [Fintype Q] {w : List α} (hw : IsReaderHole M R T w) :
    ∃ v, IsReaderHole M R T v ∧ v.length ≤ Fintype.card Q - 1 := by
  obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T ((isReaderHole_iff M R T w).mp hw).1
  refine ⟨w.take J, isReaderHole_take M R T hw hJ.1 hJ.2.1, ?_⟩
  have := firstRejected_lt_card M T hJ
  rw [List.length_take_of_le hJ.1]
  omega

/-- Hole existence is witnessed within the length bound `N - 1`. -/
theorem hole_iff_length_le_card_sub_one [Fintype Q] :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ Fintype.card Q - 1 :=
  ⟨fun ⟨_, hw⟩ => exists_hole_length_le M R T hw, fun ⟨w, hw, _⟩ => ⟨w, hw⟩⟩

end Bound

section Scan

variable {α Q : Type*} (M : DFA α Q) (T : Set Q) [DecidablePred (· ∈ T)] (a : α)

/-- Read the letter `a` from the state `q` until a rejected state, one in the target, for
fewer than `fuel` letters; the result is the number of letters read. -/
def firstRejectedCut : ℕ → Q → Option ℕ
  | 0, _ => none
  | fuel + 1, q => if q ∈ T then some 0 else (firstRejectedCut fuel (M.step q a)).map (· + 1)

/-- The scan finds the first rejected cut of the run of `a`: the first cut whose state is in
the target. -/
theorem firstRejectedCut_eq_some_iff {fuel : ℕ} {q : Q} {J : ℕ} :
    firstRejectedCut M T a fuel q = some J ↔
      J < fuel ∧ M.evalFrom q (List.replicate J a) ∈ T ∧
        ∀ i < J, M.evalFrom q (List.replicate i a) ∉ T := by
  induction fuel generalizing q J with
  | zero => simp [firstRejectedCut]
  | succ fuel ih =>
    by_cases hq : q ∈ T
    · simp only [firstRejectedCut, hq, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨by omega, by simpa using hq, fun i hi => absurd hi (by omega)⟩
      · rintro ⟨-, -, hi⟩
        by_contra hJ
        exact hi 0 (by omega) (by simpa using hq)
    · simp only [firstRejectedCut, hq, ↓reduceIte, Option.map_eq_some_iff, ih]
      constructor
      · rintro ⟨J, ⟨hJ, hT, hi⟩, rfl⟩
        refine ⟨by omega, by simpa [List.replicate_succ] using hT, fun i hi' => ?_⟩
        cases i with
        | zero => simpa using hq
        | succ i => simpa [List.replicate_succ] using hi i (by omega)
      · rintro ⟨hJ, hT, hi⟩
        cases J with
        | zero => exact absurd (by simpa using hT) hq
        | succ J =>
          refine ⟨J, ⟨by omega, by simpa [List.replicate_succ] using hT, fun i hi' => ?_⟩, rfl⟩
          simpa [List.replicate_succ] using hi (i + 1) (by omega)

end Scan

section Search

variable {α Q : Type*} [Unique α] [Fintype Q] (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
  [DecidablePred (· ∈ T)]

/-- A hole exists exactly when the run of the single letter reaches the target
within `N` letters and the word up to the first rejected cut is a hole. -/
theorem hole_iff_firstRejectedCut :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ J ∈ (firstRejectedCut M T default (Fintype.card Q) M.start).toList,
        IsReaderHole M R T (List.replicate J default) := by
  simp only [Option.mem_toList, firstRejectedCut_eq_some_iff]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T ((isReaderHole_iff M R T w).mp hw).1
    have hrep (i : ℕ) (hi : i ≤ J) : w.take i = List.replicate i default :=
      eq_of_length_eq (by simp only [List.length_take, List.length_replicate]; have := hJ.1; omega)
    refine ⟨J, ⟨firstRejected_lt_card M T hJ, ?_, fun i hi => ?_⟩, ?_⟩
    · rw [← hrep J le_rfl]; exact hJ.2.1
    · rw [← hrep i hi.le]; exact hJ.2.2 i hi
    · rw [← hrep J le_rfl]; exact isReaderHole_take M R T hw hJ.1 hJ.2.1
  · rintro ⟨J, -, hJ⟩
    exact ⟨_, hJ⟩

/-- The hole decision over a one-letter alphabet. It reads fewer than `N`
letters to the first rejected cut and tests the single word up to that cut. -/
@[instance_reducible] def decideHole [DecidableEq α] [DecidableRel R] :
    Decidable (∃ w, IsReaderHole M R T w) :=
  decidable_of_iff _ (hole_iff_firstRejectedCut M R T).symm

end Search

section Monitors

open Monitor

variable {c : Fin 1 → Bool} {k : ℕ} {ϕ : Constraint 1 k} {x y : V k}

/-- The hole decision of a side monitor at arity one. -/
@[instance_reducible] def decideSideHoles {θ : Side} (P : SideMonitor 1 c ϕ x y θ) :
    Decidable (∃ w, P.Hole w) :=
  Unary.decideHole P.M P.R P.T

/-- At arity one, unsafe words of a satisfiable system have a witness of length
at most `2 * 4^(2*k) - 1`, the label state count minus one. -/
theorem unsafe_iff_bounded {θ : Side} (hs : Satisfiable c ϕ) :
    (∃ w, Unsafe c ϕ x y θ w) ↔
      ∃ w, Unsafe c ϕ x y θ w ∧ w.length ≤ 2 * 4 ^ (2 * k) - 1 := by
  let P := Monitor.sideMonitor c ϕ x y θ
  have h := hole_iff_length_le_card_sub_one P.M P.R P.T
  have hc : Fintype.card P.Q = 2 * 4 ^ (2 * k) := card_sideMonitor c ϕ x y θ
  simp only [hc] at h
  exact (exists_congr fun w => (P.hole_iff_unsafe hs w).symm).trans
    (h.trans (exists_congr fun w => and_congr_left' (P.hole_iff_unsafe hs w)))

end Monitors

end Complexity.Unary

section Deciders

variable {k : ℕ}

/-- Decide entailment at arity one over arbitrary trees for the given variance,
searching the label monitors for holes of length below their state count.
Satisfiability is tested first; the hole searches run only on satisfiable systems. -/
@[instance_reducible] def decideEntailsUnary (c : Fin 1 → Bool) (ϕ : Constraint 1 k)
    (x y : V k) : Decidable (Entails c ϕ x y) :=
  Monitor.decideEntailsOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r) Complexity.Unary.decideSideHoles

/-- Decide entailment at arity one over regular trees for the given variance. -/
@[instance_reducible] def decideEntailsRegUnary (c : Fin 1 → Bool) (ϕ : Constraint 1 k)
    (x y : V k) : Decidable (EntailsReg c ϕ x y) :=
  Monitor.decideEntailsRegOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r) Complexity.Unary.decideSideHoles

/-- Decide entailment at arity one over finite trees for the given variance. -/
@[instance_reducible] def decideEntailsFinUnary (c : Fin 1 → Bool) (ϕ : Constraint 1 k)
    (x y : V k) : Decidable (EntailsFin c ϕ x y) :=
  Monitor.decideEntailsFinOfMonitors ((Monitor.family c).monitor ϕ x y .l)
    ((Monitor.family c).monitor ϕ x y .r) Complexity.Unary.decideSideHoles

/-- The arity-one decision returns true exactly when unrestricted entailment holds. -/
theorem decideEntailsUnary_correct (c : Fin 1 → Bool) (ϕ : Constraint 1 k) (x y : V k) :
    @decide _ (decideEntailsUnary c ϕ x y) = true ↔ Entails c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsUnary c ϕ x y)

/-- The arity-one decision returns true exactly when regular-tree entailment holds. -/
theorem decideEntailsRegUnary_correct (c : Fin 1 → Bool) (ϕ : Constraint 1 k) (x y : V k) :
    @decide _ (decideEntailsRegUnary c ϕ x y) = true ↔ EntailsReg c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsRegUnary c ϕ x y)

/-- The arity-one decision returns true exactly when finite-tree entailment holds. -/
theorem decideEntailsFinUnary_correct (c : Fin 1 → Bool) (ϕ : Constraint 1 k) (x y : V k) :
    @decide _ (decideEntailsFinUnary c ϕ x y) = true ↔ EntailsFin c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsFinUnary c ϕ x y)

end Deciders

end DeciNSSE
