import DeciNSSE.Shortening.DeadEndDepth
import DeciNSSE.Shortening.LabelActions
import DeciNSSE.Shortening.Readers
import DeciNSSE.Monitor.Decision

/-! # Short counterexample words for subtype entailment

## Main declarations

- `depth_le_of_deadEnd`, `side_actionBound`, `tower_actionBound` give the
  depth and action estimates for the signed label reader.
- `sideHole_iff_bounded` bounds witnesses uniformly in arity and variance.
- `not_entails_iff_bounded` and its domain variants characterize non-entailment.
- `decideEntailsExp`, `decideEntailsRegExp`, `decideEntailsFinExp` search the
  quartic-exponent witness bound.
-/

namespace DeciNSSE
namespace Shortening
open Monitor LetteredHierarchy HierarchyDepth CoAlignment

/-- Number of bit patterns for the two image relations and readiness flags. -/
def labelActions (b : ℕ) := 2 ^ (3 * b ^ 2 + 2 * b)

/-- For a query on `k` variables, the allowance `2 ^ (512 * (k + 1) ^ 4)` covers both dead-end
holes and finite witnesses from periodic continuations. -/
def sideBound (k : ℕ) := 2 ^ (512 * (k + 1) ^ 4)

/-- Every nonempty continuation of a reachable rejected state has empty upper image. -/
theorem upper_eq_empty_of_rejected {n m : ℕ} (ψ : Constraint n m) (X Y : V m)
    {w v : List (Fin n)} (hw : (reader ψ X Y).eval w ∈ target ψ) (hv : v ≠ []) :
    ((reader ψ X Y).eval (w ++ v)).U = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (mem_target_iff w).mp hw (Or.inr (childAt_of_upper hv ha))

variable {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k) (θ : Side)

/-- Every nonempty word ending at a dead end of a side reader has canonical depth at most
`4 * k + 1` for `k` variables. -/
theorem depth_le_of_deadEnd {w : List (Fin n)} (hw : w ≠ [])
    (h : DeadEnd (sideReader c ϕ x y θ) (sideTarget c ϕ) ((sideReader c ϕ x y θ).eval w)) :
    letI : Inhabited (Fin n) := ⟨w.head hw⟩
    depth w ≤ 4 * k + 1 := by
  let : Inhabited (Fin n) := ⟨w.head hw⟩
  have hd := reader_deadEnd_depth hw h
    (fun a => upper_eq_empty_of_rejected _ _ _ h.1 (v := [a]) (by simp))
  omega

/-- The signed side reader on `k` variables has at most `labelActions (2 * k)` distinct word
actions on its cores. -/
theorem side_actionBound : ActionBound
    (ofReader (sideReader c ϕ x y θ) admission (sideTarget c ϕ)) (labelActions (2 * k)) := by
  exact reader_actionBound (signed c ϕ) (Events.sideQuery x y θ).1 (Events.sideQuery x y θ).2 _ _

private theorem actionBound_der {Γ C : Type*} [Fintype C] (D : Lettered Γ C)
    (ℓ : Γ) {A : ℕ} (hA : ActionBound D A) :
    ActionBound (der D ℓ) (A * (Fintype.card C + 1)) := by
  classical
  obtain ⟨F, hcard, hmem⟩ := hA
  let extend (p : (C → C) × Option C) (q : Option C) := q.elim p.2 (fun c => some (p.1 c))
  refine ⟨(F ×ˢ (Finset.univ : Finset (Option C))).image extend, ?_, ?_⟩
  · apply Finset.card_image_le.trans
    simpa using Nat.mul_le_mul_right (Fintype.card C + 1) hcard
  · intro w
    let old (w : List (List Γ)) := w.flatMap (ℓ :: ·)
    have ordinary (c : C) : kst (der D ℓ) (some c) w = some (kst D c (old w)) := by
      induction w generalizing c with
      | nil => rfl
      | cons x w ih =>
        change kst (der D ℓ) (some (kst D c (ℓ :: x))) w = some (kst D c ((ℓ :: x) ++ old w))
        rw [kst_append, ih]
    refine Finset.mem_image.mpr ⟨⟨fun c => kst D c (old w), kst (der D ℓ) none w⟩,
      Finset.mem_product.mpr ⟨hmem _, Finset.mem_univ _⟩, ?_⟩
    funext q
    cases q with
    | none => rfl
    | some c => exact (ordinary c).symm

/-- At level `j`, at most `A * (N + j) ^ j` word actions arise from a base monitor with `N`
cores and at most `A` actions. -/
theorem tower_actionBound {Γ C : Type*} [Fintype C] (D : Lettered Γ C)
    (ℓ : (i : ℕ) → Alph Γ i) {A : ℕ} (hA : ActionBound D A) (j : ℕ) :
    ActionBound (tower D ℓ j) (A * (Fintype.card C + j) ^ j) := by
  induction j with
  | zero => simpa [tower] using hA
  | succ j ih =>
    obtain ⟨F, hF, hw⟩ := actionBound_der (tower D ℓ j) (ℓ j) ih
    refine ⟨F, hF.trans ?_, hw⟩
    rw [BoundedDepth.card_cores, pow_succ, ← Nat.mul_assoc]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) (by omega)


private theorem card_signed (k : ℕ) : Fintype.card (State (2 * k)) = 2 ^ (4 * k + 1) := by
  rw [card_state, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, pow_succ]
  ring_nf

private theorem deadEnd_length_estimate (k d : ℕ) (hd : d ≤ 4 * k + 1) :
    let N := 2 ^ (4 * k + 1)
    descentBound N d (labelActions (2 * k) * (N + d) ^ d) ≤ sideBound k := by
  dsimp only
  let N := 2 ^ (4 * k + 1)
  let e := 4 * k + 2
  let a := 3 * (2 * k) ^ 2 + 2 * (2 * k) + e * (4 * k + 1)
  have hdN : d ≤ N := hd.trans Nat.lt_two_pow_self.le
  have hN : N + d ≤ 2 ^ e := by
    change N + d ≤ 2 ^ ((4 * k + 1) + 1)
    rw [pow_succ]; change N + d ≤ N * 2; omega
  have hK : labelActions (2 * k) * (N + d) ^ d ≤ 2 ^ a := by
    dsimp [a, labelActions]
    rw [pow_add 2 (3 * (2 * k) ^ 2 + 2 * (2 * k)), pow_mul 2 e]
    exact Nat.mul_le_mul_left _
      ((Nat.pow_le_pow_left hN _).trans (Nat.pow_le_pow_right (by positivity) hd))
  have hbase : 1 + 2 * (labelActions (2 * k) * (N + d) ^ d) ≤ 2 ^ (a + 2) := by
    rw [pow_add 2 a]; have := Nat.one_le_pow a 2 (by decide); omega
  have ht : d * (d + 1) / 2 ≤ (4 * k + 1) * (4 * k + 2) :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul hd (by omega))
  calc
    descentBound N d _ ≤ 2 ^ e * (2 ^ (a + 2)) ^ ((4 * k + 1) * (4 * k + 2)) :=
      Nat.mul_le_mul hN
        ((Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) ht))
    _ = 2 ^ (e + (a + 2) * ((4 * k + 1) * (4 * k + 2))) := by rw [pow_add 2 e, pow_mul 2 (a + 2)]
    _ ≤ sideBound k := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [a, e]
      ring_nf; omega

/-- The full dead-end depth and action estimates fit in the quartic exponent. -/
theorem deadEnd_descent_le (k : ℕ) :
    let N := 2 * 4 ^ (2 * k)
    let d := 4 * k + 1
    descentBound N d (labelActions (2 * k) * (N + d) ^ d) ≤ sideBound k := by
  dsimp only
  rw [← card_state, card_signed]
  exact deadEnd_length_estimate _ _ le_rfl

/-- The quadratic lasso bound on label-reader states fits in the same allowance. -/
theorem omega_le_sideBound (k : ℕ) :
    (2 * 4 ^ (2 * k)) ^ 2 + 3 * (2 * 4 ^ (2 * k)) ≤ sideBound k := by
  rw [← card_state, card_signed]
  let N := 2 ^ (4 * k + 1)
  have pos : 0 < N := by dsimp [N]; positivity
  calc
    N ^ 2 + 3 * N ≤ N ^ 2 * 4 := by nlinarith [Nat.mul_le_mul_left N pos]
    _ = 2 ^ ((4 * k + 1) * 2 + 2) := by rw [pow_add, pow_mul]; rfl
    _ ≤ sideBound k := by
      apply Nat.pow_le_pow_right (by decide)
      ring_nf; omega

/-- Any side hole ending at a dead end yields one of length at most `sideBound k` that also ends
at a dead end. -/
theorem short_deadEnd_sideHole {w : List (Fin n)} (hw : SideHole c ϕ x y θ w)
    (h : DeadEnd (sideReader c ϕ x y θ) (sideTarget c ϕ) ((sideReader c ϕ x y θ).eval w)) :
    ∃ v, SideHole c ϕ x y θ v ∧
      DeadEnd (sideReader c ϕ x y θ) (sideTarget c ϕ) ((sideReader c ϕ x y θ).eval v) ∧
      v.length ≤ sideBound k := by
  by_cases hn : w = []
  · exact ⟨w, hw, h, by simp [hn]⟩
  let : Inhabited (Fin n) := ⟨w.head hn⟩
  let M := sideReader c ϕ x y θ
  let T := sideTarget c ϕ
  let E : Set (State (2 * k)) := DeadEnd M T
  let D := ofReader M admission E
  have refined (u : List (Fin n)) : Holes.IsReaderHole M admission E u ↔
      SideHole c ϕ x y θ u ∧ DeadEnd M T (M.eval u) := by
    rw [SideHole, Holes.isReaderHole_iff, Holes.isReaderHole_iff]
    exact ⟨fun ⟨he, ha⟩ => ⟨⟨he.1, ha⟩, he⟩,
      fun ⟨⟨_, ha⟩, he⟩ => ⟨he, ha⟩⟩
  have base : ActionBound D (labelActions (2 * k)) := side_actionBound c ϕ x y θ
  let N := Fintype.card (State (2 * k))
  have hpos : 0 < N := Fintype.card_pos_iff.mpr ⟨M.start⟩
  have actions (j : ℕ) (hj : j < depth w) :
      ActionBound (tower D (markOf w) j) (labelActions (2 * k) * (N + depth w) ^ depth w) := by
    obtain ⟨A, ha, hA⟩ := tower_actionBound D (markOf w) base j
    refine ⟨A, ha.trans (Nat.mul_le_mul_left _ ?_), hA⟩
    exact (Nat.pow_le_pow_left (Nat.add_le_add_left hj.le N) _).trans
      (Nat.pow_le_pow_right (by omega) hj.le)
  have hletter : D.IsHole w :=
    (isHole_ofReader_iff M admission E hn).mpr ((refined w).mpr ⟨hw,h⟩)
  obtain ⟨u, hu, hl⟩ := exists_short_hole D hletter actions
  have ⟨hs, he⟩ := (refined u).mp ((isHole_ofReader_iff M admission E hu.ne_nil).mp hu)
  refine ⟨u, hs, he, hl.trans ?_⟩
  dsimp only [N]
  rw [card_signed]
  exact deadEnd_length_estimate _ _ (depth_le_of_deadEnd c ϕ x y θ hn h)

/-- A side reader has a hole exactly when it has one of length at most `sideBound k`, uniformly
in arity and variance. -/
theorem sideHole_iff_bounded :
    (∃ w, SideHole c ϕ x y θ w) ↔
      ∃ w, SideHole c ϕ x y θ w ∧ w.length ≤ sideBound k := by
  constructor
  · intro hh
    let M := sideReader c ϕ x y θ
    let T := sideTarget c ϕ
    rcases (hole_dichotomy M admission T).mp hh with ⟨W, _, _, hW, _⟩ | ⟨w, hw, hd⟩
    · obtain ⟨w, hw, hl⟩ := short_hole_of_omega M admission T hW
      refine ⟨w, hw, hl.trans ?_⟩
      rw [card_state]
      exact omega_le_sideBound k
    · obtain ⟨u, hu, _, hl⟩ := short_deadEnd_sideHole c ϕ x y θ hw hd
      exact ⟨u, hu, hl⟩
  · rintro ⟨w, hw, _⟩; exact ⟨w, hw⟩

/-- There is no well-formed query root over zero variables. -/
theorem no_query_zero (x : V 0) : False := Fin.elim0 x

/-- At arity zero the empty word is the entire search space. -/
theorem nullary_sideHole_iff (c : Fin 0 → Bool) (ϕ : Constraint 0 k) (x y : V k) (θ : Side) :
    (∃ w, SideHole c ϕ x y θ w) ↔ SideHole c ϕ x y θ [] := by
  constructor
  · rintro ⟨w, hw⟩
    cases w with
    | nil => exact hw
    | cons a _ => exact Fin.elim0 a
  · exact fun h => ⟨[], h⟩

/-- The empty address is a hole precisely when the initial state is rejected. -/
theorem empty_sideHole_iff :
    SideHole c ϕ x y θ [] ↔ (sideReader c ϕ x y θ).start ∈ sideTarget c ϕ := by
  rw [SideHole, Holes.isReaderHole_iff]
  simp; omega

/-- Some side of the query has a hole of length at most `sideBound k`. -/
def BoundedSideHole : Prop := ∃ θ w, SideHole c ϕ x y θ w ∧ w.length ≤ sideBound k

/-- A query fails over arbitrary trees exactly when its system is satisfiable and some side has
a bounded hole. -/
theorem not_entails_iff_bounded :
    ¬ Entails c ϕ x y ↔ Satisfiable c ϕ ∧ BoundedSideHole c ϕ x y := by
  classical
  rw [entails_iff_sideHoles, satB_eq_false_iff, not_or, not_not]
  apply and_congr_right
  intro _
  rw [not_and_or, not_not, not_not, sideHole_iff_bounded, sideHole_iff_bounded]
  exact ⟨fun h => h.elim (fun hw => ⟨.l, hw⟩) (fun hw => ⟨.r, hw⟩),
    fun ⟨θ, hw⟩ => by cases θ <;> [exact Or.inl hw; exact Or.inr hw]⟩

/-- A query fails over regular trees exactly when its system is satisfiable and some side has a
bounded hole. -/
theorem not_entailsReg_iff_bounded :
    ¬ EntailsReg c ϕ x y ↔ Satisfiable c ϕ ∧ BoundedSideHole c ϕ x y := by
  rw [entailsReg_iff_entails, not_entails_iff_bounded]

/-- A query fails over finite trees exactly when its system has a finite solution and some side
has a bounded hole. -/
theorem not_entailsFin_iff_bounded :
    ¬ EntailsFin c ϕ x y ↔ SatisfiableFin c ϕ ∧ BoundedSideHole c ϕ x y := by
  classical
  rw [entailsFin_iff, not_or, not_not, not_entails_iff_bounded]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun ⟨hs, hb⟩ =>
    ⟨hs, (by obtain ⟨σ, hσ⟩ := hs; exact ⟨FTree.toTree ∘ σ, hσ⟩), hb⟩⟩

/-- Enumerating all direction words of length at most `sideBound k` suffices to detect a hole on
the given side. -/
theorem decideSideHolesExp_iff :
    (∃ w, SideHole c ϕ x y θ w) ↔
      ∃ w ∈ Packets.boundedLists (Finset.univ : Finset (Fin n)) (sideBound k),
        SideHole c ϕ x y θ w := by
  rw [sideHole_iff_bounded]
  simp [Packets.mem_boundedLists, and_comm]

/-- Boolean side search with immediate answers for the empty address and nullary arity. -/
def sideSearchExp : Bool :=
  letI : ∀ w, Decidable (SideHole c ϕ x y θ w) :=
    Packets.decHole (sideReader c ϕ x y θ) admission (sideTarget c ϕ)
  if SideHole c ϕ x y θ [] then true else if n = 0 then false else
    decide (∃ w ∈ Packets.boundedLists (Finset.univ : Finset (Fin n)) (sideBound k),
      SideHole c ϕ x y θ w)

/-- The bounded Boolean search returns true exactly when the side reader has a hole. -/
theorem sideSearchExp_correct :
    sideSearchExp c ϕ x y θ = true ↔ ∃ w, SideHole c ϕ x y θ w := by
  unfold sideSearchExp
  split_ifs with he hn
  · exact ⟨fun _ => ⟨[], he⟩, fun _ => rfl⟩
  · subst n; simp [nullary_sideHole_iff, he]
  · exact decide_eq_true_iff.trans (decideSideHolesExp_iff ..).symm

/-- Bounded enumeration of a single side, including the empty address. -/
def decideSideHolesExp : Decidable (∃ w, SideHole c ϕ x y θ w) :=
  decidable_of_iff (sideSearchExp c ϕ x y θ = true) (sideSearchExp_correct ..)

end Shortening

variable {n k : ℕ} (c : Fin n → Bool) (ϕ : Constraint n k) (x y : V k)

/-- Decide arbitrary-tree entailment by testing satisfiability and, after the early exits,
enumerating every word up to `sideBound k` in a side search. The exhaustive search serves as a
specification, and the README's “Lean solver” section describes the practical solver `nsse`. -/
@[instance_reducible] def decideEntailsExp : Decidable (Entails c ϕ x y) :=
  Monitor.decideEntailsWith (Shortening.decideSideHolesExp c ϕ x y)

/-- Decide regular entailment by regular transfer, enumerating every word up to `sideBound k` in
a side search after the early exits. The exhaustive search serves as a specification, and `nsse`
checks the equivalent arbitrary-tree query in practice (see “Lean solver” in the README). -/
@[instance_reducible] def decideEntailsRegExp : Decidable (EntailsReg c ϕ x y) :=
  Monitor.decideEntailsRegWith (Shortening.decideSideHolesExp c ϕ x y)

/-- Decide finite entailment by testing finite satisfiability and, after the early exits,
enumerating every word up to `sideBound k` in a side search. The exhaustive search serves as a
specification, and the README's “Lean solver” section describes `nsse` for practical
arbitrary-tree queries. -/
@[instance_reducible] def decideEntailsFinExp : Decidable (EntailsFin c ϕ x y) :=
  Monitor.decideEntailsFinWith (Shortening.decideSideHolesExp c ϕ x y)

/-- The decision returns true exactly when the query holds over arbitrary trees. -/
theorem decideEntailsExp_correct :
    @decide _ (decideEntailsExp c ϕ x y) = true ↔ Entails c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsExp c ϕ x y)

/-- The decision returns true exactly when the query holds over regular trees. -/
theorem decideEntailsRegExp_correct :
    @decide _ (decideEntailsRegExp c ϕ x y) = true ↔ EntailsReg c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsRegExp c ϕ x y)

/-- The decision returns true exactly when the query holds over finite trees. -/
theorem decideEntailsFinExp_correct :
    @decide _ (decideEntailsFinExp c ϕ x y) = true ↔ EntailsFin c ϕ x y :=
  @decide_eq_true_iff _ (decideEntailsFinExp c ϕ x y)

private theorem decide_transport {p q : Prop} (h : p ↔ q) (d : Decidable p) :
    @decide q (@decidable_of_iff q p h d) = @decide p d := by
  cases d <;> rfl

private theorem decide_bool {p : Prop} (b : Bool) (h : b = true ↔ p) :
    @decide p (decidable_of_iff (b = true) h) = b := by
  cases b <;> rfl

private theorem decide_conjunction {p q : Prop} (dp : Decidable p) (dq : Decidable q) :
    @decide (p ∧ q) (@instDecidableAnd p q dp dq) = (@decide p dp && @decide q dq) := by
  cases dp <;> cases dq <;> rfl

private theorem decide_negation {p : Prop} (dp : Decidable p) :
    @decide (¬ p) (@instDecidableNot p dp) = !(@decide p dp) := by
  cases dp <;> rfl

private theorem decide_side (θ : Side) :
    @decide _ (Shortening.decideSideHolesExp c ϕ x y θ) =
      Shortening.sideSearchExp c ϕ x y θ :=
  decide_bool _ (Shortening.sideSearchExp_correct ..)

/-- Correctness alone gives this Boolean equation for any decision procedure for arbitrary-tree
entailment. The definitions of `decideEntailsExp`, `Monitor.decideEntailsWith` and
`Shortening.sideSearchExp` fix the bounded search used here. -/
theorem decideEntailsExp_eq :
    @decide _ (decideEntailsExp c ϕ x y) =
      (!satB c ϕ || !(Shortening.sideSearchExp c ϕ x y .l ||
        Shortening.sideSearchExp c ϕ x y .r)) := by
  unfold decideEntailsExp Monitor.decideEntailsWith
  by_cases hs : satB c ϕ = true
  · rw [dite_eq_left_of_eq_true (eq_true hs), decide_transport, decide_conjunction,
      decide_negation, decide_negation, decide_side, decide_side, hs]
    cases Shortening.sideSearchExp c ϕ x y .l <;>
      cases Shortening.sideSearchExp c ϕ x y .r <;> rfl
  · rw [dite_eq_right_of_eq_false (eq_false hs)]
    show true = _
    rw [Bool.eq_false_iff.mpr hs]
    rfl

/-- Correctness and regular transfer give this equation for any decision procedure for regular
entailment. By definition `decideEntailsRegExp` uses the same `Monitor.decideEntailsWith` and
`Shortening.sideSearchExp` computation as `decideEntailsExp`. -/
theorem decideEntailsRegExp_eq :
    @decide _ (decideEntailsRegExp c ϕ x y) = @decide _ (decideEntailsExp c ϕ x y) := by
  unfold decideEntailsRegExp Monitor.decideEntailsRegWith decideEntailsExp
  exact decide_transport ..

/-- Correctness and finite transfer give this Boolean equation for any decision procedure for
finite entailment. The definitions of `decideEntailsFinExp` and `Monitor.decideEntailsFinWith`
test finite satisfiability before the `decideEntailsExp` computation through
`Monitor.decideEntailsWith` and `Shortening.sideSearchExp`. -/
theorem decideEntailsFinExp_eq :
    @decide _ (decideEntailsFinExp c ϕ x y) =
      (!satFinB c ϕ || @decide _ (decideEntailsExp c ϕ x y)) := by
  unfold decideEntailsFinExp Monitor.decideEntailsFinWith
  by_cases hs : satFinB c ϕ = true
  · rw [dite_eq_left_of_eq_true (eq_true hs), decide_transport, hs]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false hs)]
    show true = _
    rw [Bool.eq_false_iff.mpr hs]
    rfl

end DeciNSSE
