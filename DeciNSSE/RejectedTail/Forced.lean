import DeciNSSE.Holes.Packets
import DeciNSSE.RejectedTail.Periodic

/-! # Forced periodic continuations

If every rejected state on a cycle has at most one rejected outgoing letter,
a long rejected path has a forced periodic continuation. Shortening its
transient part while tracking phase preserves the absence of admissions.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail
open Holes
variable {α Q : Type*}

/-- Periodicity from a specified cut. -/
def PeriodicFrom (W : ℕ → α) (A d : ℕ) : Prop :=
  ∀ k, A ≤ k → W (k+d) = W k

/-- Equality of two infinite suffixes. -/
def EqualSuffix (W : ℕ → α) (s e : ℕ) : Prop :=
  ∀ k, W (s+k) = W (e+k)

theorem equalSuffix_iff (W : ℕ → α) {s e : ℕ} (h : s ≤ e) :
    EqualSuffix W s e ↔ ∀ k, e ≤ k → W (k-(e-s)) = W k := by
  constructor
  · intro he k hk
    have hh := he (k-e)
    convert hh using 1 <;> congr 1 <;> omega
  · intro he k
    have hh := he (e+k) (by omega)
    convert hh using 1; congr 1; omega

theorem periodicFrom_mul {W : ℕ → α} {A d : ℕ}
    (h : PeriodicFrom W A d) {k : ℕ} (hk : A ≤ k) (m : ℕ) :
    W (k+m*d) = W k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h _ (by omega), ih]

/-- An equal suffix pair propagates any eventual period backwards. -/
theorem equalSuffix_periodicFrom {W : ℕ → α} {n d s e : ℕ}
    (hper : PeriodicFrom W n d) (hse : s < e) (heq : EqualSuffix W s e) :
    PeriodicFrom W s d := by
  have hp : PeriodicFrom W s (e-s) := by
    intro k hk
    have hh := heq (k-s)
    convert hh.symm using 1 <;> congr 1 <;> omega
  intro k hk
  have hb : n ≤ k + (n+1)*(e-s) := by
    have : 1 ≤ e-s := by omega
    nlinarith
  calc
    W (k+d) = W (k+d+(n+1)*(e-s)) := (periodicFrom_mul hp (by omega) _).symm
    _ = W (k+(n+1)*(e-s)+d) := by congr 1; omega
    _ = W (k+(n+1)*(e-s)) := hper _ hb
    _ = W k := periodicFrom_mul hp hk _

/-- Earliest onset and the preceding mismatch. -/
theorem exists_periodicOnset {W : ℕ → α} {n d : ℕ}
    (h : PeriodicFrom W n d) :
    ∃ A, A ≤ n ∧ PeriodicFrom W A d ∧
      (∀ s e, s < e → EqualSuffix W s e → A ≤ s) ∧
      (A ≠ 0 → W (A-1+d) ≠ W (A-1)) := by
  classical
  let hex : ∃ A, PeriodicFrom W A d := ⟨n,h⟩
  let A := Nat.find hex
  have hp : PeriodicFrom W A d := Nat.find_spec hex
  refine ⟨A, Nat.find_min' hex h, hp, ?_, ?_⟩
  · intro s e hse heq
    exact Nat.find_min' hex (equalSuffix_periodicFrom hp hse heq)
  · intro hA heq
    apply Nat.find_min hex (show A-1 < A by omega)
    intro k hk
    by_cases hAk : A ≤ k
    · exact hp k hAk
    · have : k = A-1 := by omega
      simpa only [this] using heq

/-- A preceding mismatch excludes earlier equal infinite suffixes. -/
theorem mismatch_excludes_equalSuffix {W : ℕ → α} {A d s e : ℕ}
    (hper : PeriodicFrom W A d) (hm : A ≠ 0 → W (A-1+d) ≠ W (A-1))
    (hse : s < e) (heq : EqualSuffix W s e) : A ≤ s := by
  by_contra hn
  exact hm (by omega) (equalSuffix_periodicFrom hper hse heq (A-1) (by omega))

/-- Restrict a comparison to a shorter prefix. -/
theorem comparison_take {w : List α} {s e n : ℕ}
    (hse : s ≤ e) (hen : e ≤ n) (_hn : n ≤ w.length)
    (hp : w.drop e <+: w.drop s) :
    (w.take n).drop e <+: (w.take n).drop s := by
  rw [List.drop_take, List.drop_take]
  exact (hp.take (n-e)).trans (List.take_prefix_take_left (by omega))

/-- Extension to another rejected endpoint preserves holehood. -/
theorem rejected_extension (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] {v w : List α}
    (hv : IsReaderHole M R T v) (hvw : v <+: w) (hw : M.eval w ∈ T) :
    IsReaderHole M R T w := by
  obtain ⟨J,hJ⟩ := exists_firstRejectedPrefix M T hw
  have hvT := ((isReaderHole_iff M R T v).mp hv).1
  have hjv : J ≤ v.length := by
    by_contra hn
    apply hJ.2.2 v.length (by omega)
    simpa only [← List.prefix_iff_eq_take.mp hvw] using hvT
  apply (isReaderHole_iff M R T w).mpr
  refine ⟨hw, ?_⟩
  intro s e hse he hp hr
  have heJ := h.cone w J hw hJ s e hse he hp hr
  have hev : e ≤ v.length := heJ.trans hjv
  have htake : w.take v.length = v := (List.prefix_iff_eq_take.mp hvw).symm
  have hc := comparison_take hse.le hev hvw.length_le hp
  rw [htake] at hc
  apply ((isReaderHole_iff M R T v).mp hv).2 s e hse hev hc
  have hs : (w.take v.length).take s = w.take s := by simp only [List.take_take, min_eq_left (show s ≤ v.length by omega)]
  have heq : (w.take v.length).take e = w.take e := by simp only [List.take_take, min_eq_left hev]
  rw [htake] at hs heq
  simpa only [hs, heq] using hr

/-- A rejected infinite extension of a hole has no infinite admission. -/
theorem extension_noInfiniteAdmission (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [RejectedPath M R T] (W : ℕ → α) {v : List α}
    (hv : IsReaderHole M R T v) (hp : v = streamPrefix W v.length)
    (ht : ∀ n, v.length ≤ n → M.eval (streamPrefix W n) ∈ T) :
    NoInfiniteAdmission M R W := by
  intro s e hse hr heq
  let n := max v.length e
  have hn : v.length ≤ n := le_max_left _ _
  have he : e ≤ n := le_max_right _ _
  have hvp : v <+: streamPrefix W n := by
    rw [hp, ← streamPrefix_take W hn]
    exact List.take_prefix _ _
  have hh := rejected_extension M R T hv hvp (ht n hn)
  apply ((isReaderHole_iff M R T _).mp hh).2 s e hse (by simpa using he) ?_ ?_
  · apply List.prefix_iff_eq_take.mpr
    apply List.ext_getElem
    · simp only [List.length_drop, streamPrefix_length, List.length_take]
      omega
    · intro i hi hi'
      have hiN : e+i < n := by
        simp only [List.length_drop, streamPrefix_length] at hi
        omega
      have hsN : s+i < n := by omega
      have hletter := heq (e+i) (by omega)
      have hid : e+i-(e-s) = s+i := by omega
      simp only [hid] at hletter
      simp [streamPrefix, hletter]
  · simpa only [streamPrefix_take W (show s ≤ n by omega), streamPrefix_take W he] using hr

/-- Replace the prefix, retaining the entire infinite suffix. -/
def spliceStream (u : List α) (W : ℕ → α) (A : ℕ) (k : ℕ) : α :=
  if h : k < u.length then u[k] else W (A + (k-u.length))

@[simp] theorem spliceStream_after (u : List α) (W : ℕ → α) (A k : ℕ) :
    spliceStream u W A (u.length+k) = W (A+k) := by simp [spliceStream]

@[simp] theorem streamPrefix_succ (W : ℕ → α) (n : ℕ) :
    streamPrefix W (n+1) = streamPrefix W n ++ [W n] := by
  unfold streamPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem streamPrefix_add (W : ℕ → α) (A k : ℕ) :
    streamPrefix W (A+k) = streamPrefix W A ++ streamPrefix (fun i => W (A+i)) k := by
  induction k with
  | zero => simp [streamPrefix]
  | succ k ih =>
    rw [show A+(k+1) = A+k+1 by omega, streamPrefix_succ, ih, streamPrefix_succ]
    simp [List.append_assoc]

theorem spliceStream_prefix (u : List α) (W : ℕ → α) (A : ℕ) :
    streamPrefix (spliceStream u W A) u.length = u := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [streamPrefix, spliceStream]

theorem spliceStream_eval (M : DFA α Q) {u : List α} {W : ℕ → α} {A : ℕ}
    (hu : M.eval u = M.eval (streamPrefix W A)) (k : ℕ) :
    M.eval (streamPrefix (spliceStream u W A) (u.length+k)) =
      M.eval (streamPrefix W (A+k)) := by
  rw [streamPrefix_add, streamPrefix_add, spliceStream_prefix]
  simp only [spliceStream_after, DFA.eval, DFA.evalFrom_of_append]
  change M.evalFrom (M.eval u) _ = M.evalFrom (M.eval (streamPrefix W A)) _
  rw [hu]

theorem spliceStream_periodic {u : List α} {W : ℕ → α} {A d : ℕ}
    (hp : PeriodicFrom W A d) : PeriodicFrom (spliceStream u W A) u.length d := by
  intro k hk
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_assoc, spliceStream_after, spliceStream_after]
  simpa only [Nat.add_assoc] using hp (A+i) (by omega)

/-- State preservation at the seam and its preceding mismatch are
sufficient to preserve absence of infinite admissions. -/
theorem spliceStream_noInfiniteAdmission (M : DFA α Q) (R : Q → Q → Prop)
    {u : List α} {W : ℕ → α} {A d : ℕ}
    (hp : PeriodicFrom W A d) (hc : NoInfiniteAdmission M R W)
    (hu : M.eval u = M.eval (streamPrefix W A))
    (hm : u.length ≠ 0 →
      spliceStream u W A (u.length-1+d) ≠ spliceStream u W A (u.length-1)) :
    NoInfiniteAdmission M R (spliceStream u W A) := by
  intro s e hse hr heq
  have hsuf := (equalSuffix_iff _ hse.le).mpr heq
  have hs := mismatch_excludes_equalSuffix (spliceStream_periodic hp) hm hse hsuf
  have he : u.length ≤ e := by omega
  obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le he
  have hA : A+i < A+j := by omega
  apply hc (A+i) (A+j) hA
  · simpa only [spliceStream_eval M hu] using hr
  · apply (equalSuffix_iff W hA.le).mp
    intro k
    have hh := hsuf k
    simpa only [Nat.add_assoc, spliceStream_after] using hh

/-- Shortest-prefix replacement keeps the onset mismatch and the
absence of infinite admissions, with prefix length at most the state count. -/
theorem compress_periodic_prefix [Fintype Q] (M : DFA α Q) (R : Q → Q → Prop)
    {W : ℕ → α} {A d : ℕ} (hd : 0 < d)
    (hp : PeriodicFrom W A d) (hc : NoInfiniteAdmission M R W)
    (hm : A ≠ 0 → W (A-1+d) ≠ W (A-1)) :
    ∃ u : List α, u.length ≤ Fintype.card Q ∧
      M.eval u = M.eval (streamPrefix W A) ∧
      PeriodicFrom (spliceStream u W A) u.length d ∧
      NoInfiniteAdmission M R (spliceStream u W A) := by
  by_cases hA : A = 0
  · subst A
    refine ⟨[],by simp, rfl, spliceStream_periodic hp, ?_⟩
    exact spliceStream_noInfiniteAdmission M R hp hc rfl (by simp)
  · obtain ⟨v,_,hv,hve⟩ := Packets.exists_short_evalFrom M M.start
      (streamPrefix W (A-1))
    let u := v ++ [W (A-1)]
    have he : M.eval u = M.eval (streamPrefix W A) := by
      have hAA : A = A-1+1 := by omega
      rw [hAA, streamPrefix_succ]
      simp only [u, DFA.eval_append_singleton]
      change M.step (M.eval v) (W (A-1)) = _
      simpa only [DFA.eval, show A-1+1-1 = A-1 by omega] using
        congrArg (fun q => M.step q (W (A-1))) hve
    have hmm : u.length ≠ 0 →
        spliceStream u W A (u.length-1+d) ≠ spliceStream u W A (u.length-1) := by
      intro _
      have hlen : u.length = v.length+1 := by simp [u]
      have hidx : u.length-1+d = u.length+(d-1) := by omega
      rw [hidx, spliceStream_after]
      have hlast : spliceStream u W A (u.length-1) = W (A-1) := by
        simp [spliceStream, hlen, u]
      rw [hlast, show A+(d-1) = A-1+d by omega]
      exact hm hA
    exact ⟨u, by simp [u]; omega, he, spliceStream_periodic hp,
      spliceStream_noInfiniteAdmission M R hp hc he hmm⟩

/-- A deterministic finite trajectory has a short first visit. -/
theorem trajectory_short_visit {S : Type*} [Fintype S] (f : S → S)
    (q : ℕ → S) (hq : ∀ i, q (i+1) = f (q i)) (t : ℕ) :
    ∃ i, i < Fintype.card S ∧ q i = q t := by
  let D : DFA Unit S := ⟨fun s _ => f s, q 0, ∅⟩
  have he (w : List Unit) : D.eval w = q w.length := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a ih =>
      rw [DFA.eval_append_singleton, List.length_append, List.length_singleton, hq]
      exact congrArg f ih
  obtain ⟨u,_,hu,heq⟩ := Packets.exists_short_evalFrom D D.start
    (List.replicate t ())
  change D.eval u = D.eval (List.replicate t ()) at heq
  rw [he, he, List.length_replicate] at heq
  exact ⟨u.length,hu,heq⟩

theorem periodicFrom_mod {W : ℕ → α} {A d : ℕ} (hp : PeriodicFrom W A d)
    (k : ℕ) : W (A+k) = W (A+k%d) := by
  have hh := periodicFrom_mul hp (k := A+k%d) (by omega) (k/d)
  rw [Nat.add_assoc, Nat.mul_comm (k/d) d, Nat.mod_add_div] at hh
  exact hh

/-- State and spelling phase form a finite deterministic trajectory.
A state at a prescribed phase is reached in fewer than |Q|*d letters. -/
theorem periodic_short_visit [Fintype Q] (M : DFA α Q) {W : ℕ → α} {A d : ℕ}
    (hd : 0 < d) (hp : PeriodicFrom W A d) (t : ℕ) :
    ∃ i, i < Fintype.card Q*d ∧
      M.eval (streamPrefix W (A+i)) = M.eval (streamPrefix W (A+t)) ∧ i%d = t%d := by
  let q : ℕ → Q × Fin d := fun i =>
    (M.eval (streamPrefix W (A+i)), ⟨i%d, Nat.mod_lt _ hd⟩)
  let f : Q × Fin d → Q × Fin d := fun s =>
    (M.step s.1 (W (A+s.2)), ⟨(s.2.val+1)%d, Nat.mod_lt _ hd⟩)
  have hq : ∀ i, q (i+1) = f (q i) := by
    intro i
    apply Prod.ext
    · change M.eval (streamPrefix W (A+(i+1))) =
        M.step (M.eval (streamPrefix W (A+i))) (W (A+i%d))
      rw [show A+(i+1) = A+i+1 by omega, streamPrefix_succ, DFA.eval_append_singleton,
        periodicFrom_mod hp i]
    · apply Fin.ext
      change (i+1)%d = (i%d+1)%d
      simp [Nat.add_mod]
  obtain ⟨i,hi,he⟩ := trajectory_short_visit f q hq t
  refine ⟨i, by simpa using hi, congrArg Prod.fst he, ?_⟩
  exact congrArg (fun s : Q × Fin d => s.2.val) he

/-- Equal state and phase give identical future state trajectories. -/
theorem periodic_visit_future (M : DFA α Q) {W : ℕ → α} {A d i t : ℕ}
    (hp : PeriodicFrom W A d)
    (he : M.eval (streamPrefix W (A+i)) = M.eval (streamPrefix W (A+t)))
    (hm : i%d = t%d) (k : ℕ) :
    M.eval (streamPrefix W (A+i+k)) = M.eval (streamPrefix W (A+t+k)) := by
  induction k with
  | zero => simpa using he
  | succ k ih =>
    rw [show A+i+(k+1) = (A+i+k)+1 by omega,
      show A+t+(k+1) = (A+t+k)+1 by omega,
      streamPrefix_succ, streamPrefix_succ, DFA.eval_append_singleton,
      DFA.eval_append_singleton, ih]
    congr 1
    simp only [Nat.add_assoc]
    rw [periodicFrom_mod hp (i+k), periodicFrom_mod hp (t+k)]
    have hm' : (i+k)%d = (t+k)%d := by rw [Nat.add_mod i k d, Nat.add_mod t k d, hm]
    rw [hm']

/-- Any eventually periodic rejected extension without infinite
admissions can be compressed to a quadratic rejected-tail bound. -/
theorem periodic_witness_brt [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    {W : ℕ → α} {n d : ℕ} (hd : 0 < d) (hdN : d ≤ Fintype.card Q)
    (hp : PeriodicFrom W n d) (hc : NoInfiniteAdmission M R W)
    (ht : ∀ k, n ≤ k → M.eval (streamPrefix W k) ∈ T) :
    ∃ w J, IsReaderHole M R T w ∧ IsFirstRejectedPrefix M T w J ∧
      w.length-J ≤ (Fintype.card Q)^2 + 2*Fintype.card Q := by
  obtain ⟨A,hAn,hper,_,hmis⟩ := exists_periodicOnset hp
  obtain ⟨u,hu,hue,hup,huc⟩ := compress_periodic_prefix M R hd hper hc hmis
  let U := spliceStream u W A
  have htar (k : ℕ) : M.eval (streamPrefix U (u.length+(n-A)+k)) ∈ T := by
    rw [Nat.add_assoc, spliceStream_eval M hue]
    apply ht
    omega
  obtain ⟨i,hi,hie,him⟩ := periodic_short_visit M hd hup (n-A)
  have hafter (k : ℕ) : M.eval (streamPrefix U (u.length+i+k)) ∈ T := by
    rw [periodic_visit_future M hup hie him k]
    exact htar k
  obtain ⟨J,hJ⟩ := exists_firstRejectedPrefix M T (by simpa using hafter 0)
  let L := u.length+i+J+d
  have hL : M.eval (streamPrefix U L) ∈ T := by
    simpa [L, Nat.add_assoc] using hafter (J+d)
  have hJL : IsFirstRejectedPrefix M T (streamPrefix U L) J := by
    have hj : J ≤ u.length+i := by simpa using hJ.1
    refine ⟨by simp [L]; omega, ?_, ?_⟩
    · rw [streamPrefix_take U (by dsimp [L]; omega)]
      simpa only [streamPrefix_take U hj] using hJ.2.1
    · intro j hjJ
      rw [streamPrefix_take U (by dsimp [L]; omega)]
      simpa only [streamPrefix_take U (show j ≤ u.length+i by omega)] using hJ.2.2 j hjJ
  obtain ⟨hh,hlen⟩ := periodic_truncation M R T h.cone U hd
    (fun k hk => hup k (by omega)) huc hL hJL
  refine ⟨_,J,hh,hJL, ?_⟩
  rw [hlen]
  have hm := Nat.mul_le_mul_left (Fintype.card Q) hdN
  nlinarith

/-- Reachable rejected states with a nonempty return. -/
def RejectedCycle (M : DFA α Q) (T : Set Q) (q : Q) : Prop :=
  (∃ v, M.eval v = q) ∧ q ∈ T ∧ ∃ c : List α, c ≠ [] ∧ M.evalFrom q c = q

/-- No branching means uniqueness of safe LETTERS, not successors. -/
def ForcedCycles (M : DFA α Q) (T : Set Q) : Prop :=
  ∀ q, RejectedCycle M T q → ∀ a b, M.step q a ∈ T → M.step q b ∈ T → a = b

theorem cycle_safe_letter (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] {q : Q} (hq : RejectedCycle M T q) :
    ∃ a, M.step q a ∈ T := by
  obtain ⟨⟨v,hv⟩,hqt,⟨c,hc,hr⟩⟩ := hq
  cases c with
  | nil => exact (hc rfl).elim
  | cons a c =>
    refine ⟨a, ?_⟩
    have ht : M.eval (v ++ a::c) ∈ T := by
      simpa only [DFA.eval, DFA.evalFrom_of_append, show M.evalFrom M.start v = q from hv,
        hr] using hqt
    have hh := h.between v (v++[a]) (v++a::c) (List.prefix_append _ _)
      (by exact ⟨c,by simp⟩) (hv ▸ hqt) ht
    simpa only [DFA.eval_append_singleton, hv] using hh

theorem forced_cycle_step (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] (hf : ForcedCycles M T)
    {q : Q} (hq : RejectedCycle M T q) {a : α} (ha : M.step q a ∈ T) :
    RejectedCycle M T (M.step q a) := by
  obtain ⟨⟨v,hv⟩,hqt,⟨c,hc,hr⟩⟩ := hq
  cases c with
  | nil => exact (hc rfl).elim
  | cons b c =>
    have hb : M.step q b ∈ T := by
      have ht : M.eval (v ++ b::c) ∈ T := by
        simpa only [DFA.eval, DFA.evalFrom_of_append, show M.evalFrom M.start v = q from hv,
          hr] using hqt
      have hh := h.between v (v++[b]) (v++b::c) (List.prefix_append _ _)
        (by exact ⟨c,by simp⟩) (hv ▸ hqt) ht
      simpa only [DFA.eval_append_singleton, hv] using hh
    have hab := hf q ⟨⟨v,hv⟩,hqt,⟨b::c,hc,hr⟩⟩ a b ha hb
    subst b
    refine ⟨⟨v++[a],by simp [hv]⟩,ha,c++[a],by simp, ?_⟩
    rw [DFA.evalFrom_append_singleton]
    exact congrArg (fun q => M.step q a) hr

/-- Equal states on a deterministic trajectory have equal futures. -/
theorem trajectory_eq_future {S : Type*} (f : S → S) (q : ℕ → S)
    (hq : ∀ i, q (i+1) = f (q i)) {i j : ℕ} (he : q i = q j) (k : ℕ) :
    q (i+k) = q (j+k) := by
  induction k with
  | zero => simpa using he
  | succ k ih => simpa only [← Nat.add_assoc, hq] using congrArg f ih

/-- A finite deterministic trajectory is eventually periodic with
positive period at most its state count. -/
theorem trajectory_period [Fintype Q] (f : Q → Q) (q : ℕ → Q)
    (hq : ∀ i, q (i+1) = f (q i)) :
    ∃ m d, 0 < d ∧ d ≤ Fintype.card Q ∧ ∀ k, q (m+k+d) = q (m+k) := by
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card Q+1) => q i) (by simp)
  have hij : i.val ≠ j.val := fun hh => hne (Fin.ext hh)
  wlog hlt : i.val < j.val generalizing i j
  · exact this j i hne.symm he.symm (Ne.symm hij) (by omega)
  refine ⟨i.val,j.val-i.val,by omega,by omega, ?_⟩
  intro k
  have hh := trajectory_eq_future f q hq he k
  convert hh.symm using 1; congr 1; omega

/-- Safe continuations at cyclic rejected states follow the unique
safe-letter trajectory. -/
theorem forced_path_tracks (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] (hf : ForcedCycles M T)
    (q : ℕ → Q) (a : ℕ → α) (hq : ∀ i, RejectedCycle M T (q i))
    (hs : ∀ i, M.step (q i) (a i) ∈ T) (hstep : ∀ i, q (i+1) = M.step (q i) (a i))
    {v z : List α} (hv : M.eval v = q 0) (hc : M.eval (v++z) ∈ T) :
    z = streamPrefix a z.length := by
  have hprefix (k : ℕ) : M.eval (v++z.take k) ∈ T := by
    apply h.between v (v++z.take k) (v++z) (List.prefix_append _ _)
      ((List.prefix_append_right_inj v).mpr (List.take_prefix _ _)) (hv ▸ (hq 0).2.1) hc
  have hrun : ∀ k, k ≤ z.length → M.eval (v++z.take k) = q k := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      intro hk
      have hk' : k < z.length := by omega
      have he := ih (by omega)
      have hsafe : M.step (q k) z[k] ∈ T := by
        have hh := hprefix (k+1)
        simpa only [List.take_succ_eq_append_getElem hk', ← List.append_assoc,
          DFA.eval_append_singleton, he] using hh
      have ha := hf (q k) (hq k) z[k] (a k) hsafe (hs k)
      rw [List.take_succ_eq_append_getElem hk', ← List.append_assoc,
        DFA.eval_append_singleton, he, ha, ← hstep]
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    have he := hrun k (by omega)
    have hsafe : M.step (q k) z[k] ∈ T := by
      have hh := hprefix (k+1)
      simpa only [List.take_succ_eq_append_getElem hk, ← List.append_assoc,
        DFA.eval_append_singleton, he] using hh
    simpa [streamPrefix] using hf (q k) (hq k) z[k] (a k) hsafe (hs k)

end DeciNSSE.RejectedTail
