import DeciNSSE.Shortening.Side

/-! # Checks on block shortening and bounded decisions

The block examples test what happens to a hole when blocks are shortened independently
or loop erasure tests only the initial core. The decision examples reach the empty-word,
empty-alphabet or unsatisfiability branches before enumerating words.

## Main declarations

- `compareBlocks` tests the hole predicate before and after independent shortening.
- `singleEntry` compares erasure on one and on both entry cores.
- `answers` evaluates the three bounded entailment decisions.
-/

namespace DeciNSSE.Shortening.Examples

open LetteredHierarchy CoAlignment
open scoped List

private def holeB {α Q : Type*} [DecidableEq α] (D : Lettered α Q)
    [DecidableRel D.Λ] [DecidableRel D.Λf] [∀ q a, Decidable (D.Tf q a)] (w : List α) : Bool :=
  let cuts := List.range (w.length + 1)
  let last := D.label w w.length
  (match last with | none => false | some (c, a) => decide (D.Tf c a)) &&
    cuts.all (fun s => decide (s < w.length → ¬ D.Λf (D.label w s) last)) &&
    cuts.all (fun s => cuts.all (fun e =>
      decide (s < e → e < w.length → w.drop e <+: w.drop s →
        ¬ D.Λ (D.label w s) (D.label w e))))

private theorem holeB_iff {α Q : Type*} [DecidableEq α] (D : Lettered α Q)
    [DecidableRel D.Λ] [DecidableRel D.Λf] [∀ q a, Decidable (D.Tf q a)] (w : List α) :
    holeB D w = true ↔ D.IsHole w := by
  unfold holeB Lettered.IsHole
  cases he : D.label w w.length with
  | none => simp
  | some p =>
    rcases p with ⟨q,a⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq, exists_some_eq_iff, List.all_eq_true,
      List.mem_range, IsComp]
    grind

private def pinLast {Q : Type} [DecidableEq Q] (D : Lettered Nat Q)
    (entries : List Q) (w : List Nat) :=
  let seen := w.dropLast.foldl (fun (stack : List (List Q × List Nat)) a =>
    let (before, word) := stack.getLastD (entries, [])
    let after := before.map (D.κ a)
    let i := stack.findIdx (fun p => p.1 == after)
    if i < stack.length then stack.take (i + 1) else stack ++ [(after, word ++ [a])])
    [(entries, [])]
  (seen.getLastD (entries, [])).2 ++ w.getLast?.toList

private def independent {Q : Type} (start : Q) (testLetter : Nat)
    (step : Nat → Q → Q) : Lettered Nat Q where
  start := start
  κ := step
  Λ l r := l = none ∧ r = some (start, testLetter)
  Λf _ _ := False
  Tf _ _ := True

private def compareBlocks {Q : Type} [DecidableEq Q] (start : Q) (entries : List Q)
    (testLetter : Nat) (step : Nat → Q → Q)
    (blocks : List (List Nat)) :=
  let D := independent start testLetter step
  letI : DecidableRel D.Λ := fun l r =>
    inferInstanceAs (Decidable (l = none ∧ r = some (start, testLetter)))
  letI : DecidableRel D.Λf := fun _ _ => isFalse id
  letI : ∀ c a, Decidable (D.Tf c a) := fun _ _ => isTrue trivial
  let image := blocks.map (pinLast D entries)
  (image, holeB D (expand 2 blocks), holeB D (expand 2 image))

-- Independent erasure can identify two block names.
#guard compareBlocks () [()] 2 (fun _ _ => ()) [[0, 1], [1, 1]] == ([[1], [1]], true, false)

-- Even distinct shortened names can acquire an interior admission.
#guard compareBlocks false [false, true] 0 (fun a q => q && a == 2) [[0], [0, 1, 0]] ==
  ([[0], [0, 0]], true, false)

private def targetMonitor : Lettered Nat Bool where
  start := false
  κ a q := if a = 0 then false else q
  Λ _ _ := False
  Λf _ _ := False
  Tf q _ := q = false

private def targetAtOne (x : List Nat) : Bool :=
  letI : Decidable (derTf targetMonitor 2 (some true) x) :=
    decidable_of_iff (fcore targetMonitor 2 (some true) x = false) (by simp [derTf, targetMonitor])
  decide (derTf targetMonitor 2 (some true) x)

private def singleEntry :=
  let x := [0, 1]
  let y := pinLast targetMonitor [false] x
  let z := pinLast targetMonitor [false, true] x
  (y, z, targetAtOne x, targetAtOne y, targetAtOne z)

#guard singleEntry == ([1], [0, 1], true, false, true)

-- There is a single possible word over the empty alphabet.
private def emptyTarget (b : Bool) : Set Unit := Set.ofPred fun _ => b = true

private def emptyDecision (b : Bool) : Bool :=
  let M : DFA (Fin 0) Unit := ⟨fun q _ => q, (), ∅⟩
  let R (_ _ : Unit) : Prop := False
  letI : DecidableRel R := fun _ _ => isFalse id
  letI : DecidablePred (· ∈ emptyTarget b) := fun _ =>
    inferInstanceAs (Decidable (b = true))
  letI : RejectedTail.RejectedPath M R (emptyTarget b) :=
    ⟨fun _ _ _ _ _ h _ => h, fun _ _ _ _ _ _ _ _ _ h => h.elim⟩
  @decide _ (Shortening.decideHoleExp M R (emptyTarget b) (N := 1) (by decide))

#guard (emptyDecision true, emptyDecision false) == (true, false)

private def answers {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) :=
  (@decide _ (decideEntailsExp c ϕ x y), @decide _ (decideEntailsRegExp c ϕ x y),
    @decide _ (decideEntailsFinExp c ϕ x y))

-- At arity zero the empty address suffices for either answer.
#guard answers (n := 0) (fun _ => false) [] (0 : V 2) 1 == (false, false, false)
#guard answers (n := 0) (fun _ => false) [] (0 : V 1) 0 == (true, true, true)

private def covariant : Fin 2 → Bool := fun _ => false

-- The empty system has a hole at the empty address for a query on distinct roots.
#guard answers covariant [] (0 : V 2) 1 == (false, false, false)
#guard sideSearchExp covariant [] (0 : V 2) 1 .l

private def binaryReaderAnswer : Bool :=
  let M := Monitor.sideReader covariant [] (0 : V 2) 1 .l
  @decide _ (decideHoleExp M Monitor.admission (Monitor.sideTarget covariant ([] : Constraint 2 2))
    (N := 2 * 4 ^ 4) (Monitor.card_state 4))

#guard binaryReaderAnswer

-- Assigning both extreme leaves to one root makes every query vacuous.
private def conflict : Constraint 2 1 := [.eqBot 0, .eqTop 0]

#guard answers covariant conflict 0 0 == (true, true, true)

-- A root equal to its own binary constructor has no finite solution.
private def cycle : Constraint 2 1 := [.leF 0 ![0, 0], .fLe ![0, 0] 0]

#guard @decide _ (decideEntailsFinExp covariant cycle 0 0)

end DeciNSSE.Shortening.Examples
