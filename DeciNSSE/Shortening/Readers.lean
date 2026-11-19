import DeciNSSE.Shortening.Descent
import DeciNSSE.RejectedTail.Decision

/-! # Singly exponential bounds for explicit readers

## Main declarations

- `rpBound`, `stoppingBound` specialize the descent bound to finite readers.
- `hole_iff_rpBound`, `hole_iff_stoppingBound` include the empty word.
- `decideHoleExp` searches the singly exponential allowance.
-/

namespace DeciNSSE.Shortening
open Holes RejectedTail

/-- Bound every transformation by counting all functions on the largest core set. -/
def readerBound (N d : ℕ) := descentBound N d ((N + d) ^ (N + d))

/-- The length allowance for an `N`-state rejected-path reader uses its selected depth bound. -/
def rpBound (N : ℕ) := readerBound N (holeDepthBound N)

/-- The length allowance for an `N`-state stopping reader uses depth at most `2 * N - 1`. -/
def stoppingBound (N : ℕ) := readerBound N (2 * N - 1)

private theorem readerBound_le_pow (N d e : ℕ) (ha : N + d ≤ 2 ^ e) :
    readerBound N d ≤ 2 ^ (e + (2 + e * (N + d)) * (d + 1) ^ 2) := by
  have hK : (N + d) ^ (N + d) ≤ 2 ^ (e * (N + d)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left ha _
  have hbase : 1 + 2 * (N + d) ^ (N + d) ≤ 2 ^ (2 + e * (N + d)) := by
    rw [pow_add 2 2]
    have := Nat.one_le_pow (e * (N + d)) 2 (by decide)
    omega
  have hexp : d * (d + 1) / 2 ≤ (d + 1) ^ 2 := by
    apply (Nat.div_le_self _ _).trans; nlinarith
  unfold readerBound descentBound
  rw [pow_add 2 e, pow_mul]
  exact Nat.mul_le_mul ha
    ((Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hexp))

/-- The rejected-path length allowance is singly exponential with exponent of order
`N⁶ log(N+1)`. -/
theorem rpBound_le (N : ℕ) :
    rpBound N ≤ 2 ^ (10000 * (N + 1) ^ 6 * (Nat.log2 (N + 1) + 1)) := by
  let L := Nat.log2 (N + 1) + 1
  let X := N + 1
  let d := holeDepthBound N
  have hx : X ≤ 2 ^ L :=
    ((Nat.log2_lt (by dsimp [X]; omega : X ≠ 0)).mp (Nat.lt_succ_self X.log2)).le
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have hd : d ≤ 8 * N ^ 2 := holeDepthBound_le N
  have ha : N + d ≤ 9 * X ^ 2 := by dsimp [X]; nlinarith
  have hb : d + 1 ≤ 8 * X ^ 2 := by dsimp [X]; nlinarith
  have he : N + d ≤ 2 ^ (4 + L * 2) := by
    rw [pow_add, pow_mul]
    exact ha.trans (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hx 2))
  apply (readerBound_le_pow N d _ he).trans
  apply Nat.pow_le_pow_right (by decide)
  have hlog : 4 + L * 2 ≤ 6 * L := by omega
  calc
    _ ≤ 6 * L + (2 + 6 * L * (9 * X ^ 2)) * (8 * X ^ 2) ^ 2 := by gcongr
    _ ≤ 10000 * X ^ 6 * L := by
      dsimp [X, L]
      ring_nf
      omega

/-- The stopping length allowance is singly exponential with exponent of order `N³ log(N+1)`. -/
theorem stoppingBound_le (N : ℕ) :
    stoppingBound N ≤ 2 ^ (64 * (N + 1) ^ 3 * (Nat.log2 (N + 1) + 1)) := by
  let L := Nat.log2 (N + 1) + 1
  let X := N + 1
  let d := 2 * N - 1
  have hx : X ≤ 2 ^ L :=
    ((Nat.log2_lt (by dsimp [X]; omega : X ≠ 0)).mp (Nat.lt_succ_self X.log2)).le
  have ha : N + d ≤ 3 * X := by dsimp [X, d]; omega
  have hb : d + 1 ≤ 2 * X := by dsimp [X, d]; omega
  have he : N + d ≤ 2 ^ (2 + L) := by
    rw [pow_add]; exact ha.trans (Nat.mul_le_mul (by decide) hx)
  apply (readerBound_le_pow N d _ he).trans
  apply Nat.pow_le_pow_right (by decide)
  have hlog : 2 + L ≤ 3 * L := by dsimp [L]; omega
  calc
    _ ≤ 3 * L + (2 + 3 * L * (3 * X)) * (2 * X) ^ 2 := by gcongr
    _ ≤ 64 * X ^ 3 * L := by
      dsimp [X, L]
      ring_nf
      omega

/-- The rejected-path length allowance is at most `2 ^ (10000 * (N + 1) ^ 7)`. -/
theorem rpBound_le_pow_seven (N : ℕ) : rpBound N ≤ 2 ^ (10000 * (N + 1) ^ 7) := by
  apply (rpBound_le N).trans
  apply Nat.pow_le_pow_right (by decide)
  have h := (Nat.log2_lt (by omega : N + 1 ≠ 0)).mpr (Nat.lt_two_pow_self (n := N + 1))
  calc
    _ ≤ 10000 * (N + 1) ^ 6 * (N + 1) := Nat.mul_le_mul_left _ h
    _ = _ := by ring

variable {α Q : Type*} (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)

/-- From every target state, reachable or unreachable, every nonempty word ends outside the
target set. -/
def Stopping : Prop := ∀ q ∈ T, ∀ w : List α, w ≠ [] → M.evalFrom q w ∉ T

variable [Fintype Q]
variable [DecidableEq α] [DecidableEq Q]

open CoAlignment LetteredHierarchy HierarchyDepth BoundedDepth

private theorem bounded_of_depth [Inhabited α] {w : List α} (hn : w ≠ [])
    (hw : IsReaderHole M R T w) {d : ℕ} (hd : depth w ≤ d) :
    ∃ u, IsReaderHole M R T u ∧ u.length ≤ readerBound (Fintype.card Q) d := by
  classical
  let N := Fintype.card Q
  let A := N + d
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨M.start⟩
  have hK (j : ℕ) (hj : j < depth w) :
      ActionBound (tower (ofReader M R T) (markOf w) j) (A ^ A) := by
    refine ⟨Finset.univ, ?_, fun _ => Finset.mem_univ _⟩
    rw [Finset.card_univ, Fintype.card_fun, card_cores]
    have h : Fintype.card Q + j ≤ A := by dsimp [A, N]; omega
    exact (Nat.pow_le_pow_left h _).trans (Nat.pow_le_pow_right (by dsimp [A]; omega) h)
  obtain ⟨u, hu, hlen⟩ := exists_short_hole (ofReader M R T)
    ((isHole_ofReader_iff M R T hn).mpr hw) hK
  refine ⟨u, (isHole_ofReader_iff M R T hu.ne_nil).mp hu, hlen.trans ?_⟩
  unfold descentBound readerBound
  dsimp [descentBound, A, N]
  gcongr

/-- A finite-state rejected-path reader has a hole exactly when it has one of length at most
`rpBound` of its state count. -/
theorem hole_iff_rpBound [RejectedPath M R T] :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ rpBound (Fintype.card Q) := by
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | nil => exact ⟨[], hv, Nat.zero_le _⟩
    | cons a v =>
      let : Inhabited α := ⟨a⟩
      rcases (hole_iff_bounded_depth M R T).mp ⟨_, hv⟩ with hh | ⟨w, hn, hw, i, hi, hu⟩
      · exact ⟨[], hh, Nat.zero_le _⟩
      · exact bounded_of_depth M R T hn hw ((depth_le_of_isUnary hu).trans hi)
  · rintro ⟨w, hw, _⟩; exact ⟨w, hw⟩

/-- A finite-state stopping reader has a hole exactly when it has one within its stopping length
bound. -/
theorem hole_iff_stoppingBound (h : Stopping M T) :
    (∃ w, IsReaderHole M R T w) ↔
      ∃ w, IsReaderHole M R T w ∧ w.length ≤ stoppingBound (Fintype.card Q) := by
  constructor
  · rintro ⟨w, hw⟩
    by_cases hn : w = []
    · subst w; exact ⟨[], hw, Nat.zero_le _⟩
    let : Inhabited α := ⟨w.head hn⟩
    have ht := ((isReaderHole_iff M R T w).mp hw).1
    have first : IsFirstRejectedPrefix M T w w.length := by
      refine ⟨le_rfl, by simpa using ht, ?_⟩
      intro i hi hr
      apply h _ hr (w.drop i) (by simpa using hi)
      change M.evalFrom (M.evalFrom M.start (w.take i)) (w.drop i) ∈ T
      rwa [← DFA.evalFrom_of_append, List.take_append_drop]
    apply bounded_of_depth M R T hn hw
    simpa using rejected_depth M T hn ht first
  · rintro ⟨w, hw, _⟩; exact ⟨w, hw⟩

/-- This decision procedure checks the empty word and empty alphabet first, then enumerates
every word up to `rpBound N`. The bound makes exhaustive search a specification for general
inputs, and the README's “Lean solver” section describes the practical entailment tool
`nsse`. -/
def decideHoleExp [Fintype α] [RejectedPath M R T] [DecidableRel R] [DecidablePred (· ∈ T)]
    {N : ℕ} (hN : Fintype.card Q = N) : Decidable (∃ w, IsReaderHole M R T w) :=
  letI : ∀ w, Decidable (IsReaderHole M R T w) := Packets.decHole M R T
  if he : IsReaderHole M R T [] then isTrue ⟨[], he⟩
  else if ha : (Finset.univ : Finset α).Nonempty then
    decidable_of_iff (∃ w ∈ Packets.boundedLists (Finset.univ : Finset α) (rpBound N),
        IsReaderHole M R T w)
      (by rw [hole_iff_rpBound M R T, hN]; simp [Packets.mem_boundedLists, and_comm])
  else isFalse (fun ⟨w, hw⟩ => by
    cases w with
    | nil => exact he hw
    | cons a _ => exact ha ⟨a, Finset.mem_univ _⟩)

end DeciNSSE.Shortening
