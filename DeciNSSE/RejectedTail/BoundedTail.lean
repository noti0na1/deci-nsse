import DeciNSSE.RejectedTail.Periodic
import DeciNSSE.RejectedTail.Decision

/-! # A bound on rejected-tail length

For a binary finite reader, assume rejection persists between rejected prefixes
and comparisons satisfy the admission cone. Existence of a hole then implies
existence of one with rejected tail at most |Q|² + 4|Q|.
A rejected cyclic state with two safe letters admits a word v c^K b that
breaks every admitted period. If all rejected cycles are forced, an infinite
periodic extension is moved to its earliest periodic onset, its prefix is
compressed, and a finite hole is obtained by truncation.
-/

namespace DeciNSSE.RejectedTail
open Words Holes
variable {α Q : Type*}

/-- The infinite word repeats with period `d` from position `A` onward. -/
def PeriodicFrom (W : ℕ → α) (A d : ℕ) : Prop :=
  ∀ k, A ≤ k → W (k + d) = W k

/-- The infinite suffixes beginning at two positions agree letter for letter. -/
def EqualSuffix (W : ℕ → α) (s e : ℕ) : Prop :=
  ∀ k, W (s + k) = W (e + k)

theorem equalSuffix_iff (W : ℕ → α) {s e : ℕ} (h : s ≤ e) :
    EqualSuffix W s e ↔ ∀ k, e ≤ k → W (k - (e - s)) = W k := by
  constructor
  · intro he k hk
    have hh := he (k - e)
    convert hh using 1 <;> congr 1 <;> omega
  · intro he k
    have hh := he (e + k) (by omega)
    convert hh using 1; congr 1; omega

theorem periodicFrom_mul {W : ℕ → α} {A d : ℕ}
    (h : PeriodicFrom W A d) {k : ℕ} (hk : A ≤ k) (m : ℕ) :
    W (k + m * d) = W k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, h _ (by omega), ih]

theorem equalSuffix_periodicFrom {W : ℕ → α} {n d s e : ℕ}
    (hper : PeriodicFrom W n d) (hse : s < e) (heq : EqualSuffix W s e) :
    PeriodicFrom W s d := by
  have hp : PeriodicFrom W s (e - s) := by
    intro k hk
    have hh := heq (k - s)
    convert hh.symm using 1 <;> congr 1 <;> omega
  intro k hk
  have hb : n ≤ k + (n + 1) * (e - s) := by
    have : 1 ≤ e - s := by omega
    nlinarith
  calc
    W (k + d) = W (k + d + (n + 1) * (e - s)) := (periodicFrom_mul hp (by omega) _).symm
    _ = W (k + (n + 1) * (e - s) + d) := by congr 1; omega
    _ = W (k + (n + 1) * (e - s)) := hper _ hb
    _ = W k := periodicFrom_mul hp hk _

/-- An eventually periodic stream has a least position where its given period begins. -/
theorem exists_periodicOnset {W : ℕ → α} {n d : ℕ}
    (h : PeriodicFrom W n d) :
    ∃ A, A ≤ n ∧ PeriodicFrom W A d ∧
      (∀ s e, s < e → EqualSuffix W s e → A ≤ s) ∧
      (A ≠ 0 → W (A - 1 + d) ≠ W (A - 1)) := by
  classical
  let hex : ∃ A, PeriodicFrom W A d := ⟨n, h⟩
  let A := Nat.find hex
  have hp : PeriodicFrom W A d := Nat.find_spec hex
  refine ⟨A, Nat.find_min' hex h, hp, ?_, ?_⟩
  · intro s e hse heq
    exact Nat.find_min' hex (equalSuffix_periodicFrom hp hse heq)
  · intro hA heq
    apply Nat.find_min hex (show A - 1 < A by omega)
    intro k hk
    by_cases hAk : A ≤ k
    · exact hp k hAk
    · have : k = A - 1 := by omega
      simpa only [this] using heq

theorem mismatch_excludes_equalSuffix {W : ℕ → α} {A d s e : ℕ}
    (hper : PeriodicFrom W A d) (hm : A ≠ 0 → W (A - 1 + d) ≠ W (A - 1))
    (hse : s < e) (heq : EqualSuffix W s e) : A ≤ s := by
  by_contra hn
  exact hm (by omega) (equalSuffix_periodicFrom hper hse heq (A - 1) (by omega))

theorem comparison_take {w : List α} {s e n : ℕ}
    (hse : s ≤ e) (hen : e ≤ n) (_hn : n ≤ w.length)
    (hp : w.drop e <+: w.drop s) :
    (w.take n).drop e <+: (w.take n).drop s := by
  rw [List.drop_take, List.drop_take]
  exact (hp.take (n - e)).trans (List.take_prefix_take_left (by omega))

/--
Extending a rejected hole along rejected states preserves absence of admissions ending in its
prefix.
-/
theorem rejected_extension (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] {v w : List α}
    (hv : IsReaderHole M R T v) (hvw : v <+: w) (hw : M.eval w ∈ T) :
    IsReaderHole M R T w := by
  obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T hw
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

/-- An infinite rejected extension of a hole has no admitted equal suffixes. -/
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
      have hiN : e + i < n := by
        simp only [List.length_drop, streamPrefix_length] at hi
        omega
      have hsN : s + i < n := by omega
      have hletter := heq (e + i) (by omega)
      have hid : e + i - (e - s) = s + i := by omega
      simp only [hid] at hletter
      simp [streamPrefix, hletter]
  · simpa only [streamPrefix_take W (show s ≤ n by omega), streamPrefix_take W he] using hr

/-- Replace the prefix before position `A` of an infinite word by a finite word. -/
def spliceStream (u : List α) (W : ℕ → α) (A : ℕ) (k : ℕ) : α :=
  if h : k < u.length then u[k] else W (A + (k - u.length))

@[simp] theorem spliceStream_after (u : List α) (W : ℕ → α) (A k : ℕ) :
    spliceStream u W A (u.length + k) = W (A + k) := by simp [spliceStream]

@[simp] theorem streamPrefix_succ (W : ℕ → α) (n : ℕ) :
    streamPrefix W (n + 1) = streamPrefix W n ++ [W n] := by
  unfold streamPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem streamPrefix_add (W : ℕ → α) (A k : ℕ) :
    streamPrefix W (A + k) = streamPrefix W A ++ streamPrefix (fun i => W (A + i)) k := by
  induction k with
  | zero => simp [streamPrefix]
  | succ k ih =>
    rw [show A + (k + 1) = A + k + 1 by omega, streamPrefix_succ, ih, streamPrefix_succ]
    simp [List.append_assoc]

theorem spliceStream_prefix (u : List α) (W : ℕ → α) (A : ℕ) :
    streamPrefix (spliceStream u W A) u.length = u := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [streamPrefix, spliceStream]

theorem spliceStream_eval (M : DFA α Q) {u : List α} {W : ℕ → α} {A : ℕ}
    (hu : M.eval u = M.eval (streamPrefix W A)) (k : ℕ) :
    M.eval (streamPrefix (spliceStream u W A) (u.length + k)) =
      M.eval (streamPrefix W (A + k)) := by
  rw [streamPrefix_add, streamPrefix_add, spliceStream_prefix]
  simp only [spliceStream_after, DFA.eval, DFA.evalFrom_of_append]
  change M.evalFrom (M.eval u) _ = M.evalFrom (M.eval (streamPrefix W A)) _
  rw [hu]

theorem spliceStream_periodic {u : List α} {W : ℕ → α} {A d : ℕ}
    (hp : PeriodicFrom W A d) : PeriodicFrom (spliceStream u W A) u.length d := by
  intro k hk
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_assoc, spliceStream_after, spliceStream_after]
  simpa only [Nat.add_assoc] using hp (A + i) (by omega)

theorem spliceStream_noInfiniteAdmission (M : DFA α Q) (R : Q → Q → Prop)
    {u : List α} {W : ℕ → α} {A d : ℕ}
    (hp : PeriodicFrom W A d) (hc : NoInfiniteAdmission M R W)
    (hu : M.eval u = M.eval (streamPrefix W A))
    (hm : u.length ≠ 0 →
      spliceStream u W A (u.length - 1 + d) ≠ spliceStream u W A (u.length - 1)) :
    NoInfiniteAdmission M R (spliceStream u W A) := by
  intro s e hse hr heq
  have hsuf := (equalSuffix_iff _ hse.le).mpr heq
  have hs := mismatch_excludes_equalSuffix (spliceStream_periodic hp) hm hse hsuf
  have he : u.length ≤ e := by omega
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hs
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le he
  have hA : A + i < A + j := by omega
  apply hc (A + i) (A + j) hA
  · simpa only [spliceStream_eval M hu] using hr
  · apply (equalSuffix_iff W hA.le).mp
    intro k
    have hh := hsuf k
    simpa only [Nat.add_assoc, spliceStream_after] using hh

/--
The prefix before the earliest periodic onset can be shortened while preserving non-admission.
-/
theorem compress_periodic_prefix [Fintype Q] (M : DFA α Q) (R : Q → Q → Prop)
    {W : ℕ → α} {A d : ℕ} (hd : 0 < d)
    (hp : PeriodicFrom W A d) (hc : NoInfiniteAdmission M R W)
    (hm : A ≠ 0 → W (A - 1 + d) ≠ W (A - 1)) :
    ∃ u : List α, u.length ≤ Fintype.card Q ∧
      M.eval u = M.eval (streamPrefix W A) ∧
      PeriodicFrom (spliceStream u W A) u.length d ∧
      NoInfiniteAdmission M R (spliceStream u W A) := by
  by_cases hA : A = 0
  · subst A
    refine ⟨[], by simp, rfl, spliceStream_periodic hp, ?_⟩
    exact spliceStream_noInfiniteAdmission M R hp hc rfl (by simp)
  · obtain ⟨v, _, hv, hve⟩ := Packets.exists_short_evalFrom M M.start
      (streamPrefix W (A - 1))
    let u := v ++ [W (A - 1)]
    have he : M.eval u = M.eval (streamPrefix W A) := by
      have hAA : A = A - 1 + 1 := by omega
      rw [hAA, streamPrefix_succ]
      simp only [u, DFA.eval_append_singleton]
      change M.step (M.eval v) (W (A - 1)) = _
      simpa only [DFA.eval, show A - 1 + 1 - 1 = A - 1 by omega] using
        congrArg (fun q => M.step q (W (A - 1))) hve
    have hmm : u.length ≠ 0 →
        spliceStream u W A (u.length - 1 + d) ≠ spliceStream u W A (u.length - 1) := by
      intro _
      have hlen : u.length = v.length + 1 := by simp [u]
      have hidx : u.length - 1 + d = u.length + (d - 1) := by omega
      rw [hidx, spliceStream_after]
      have hlast : spliceStream u W A (u.length - 1) = W (A - 1) := by
        simp [spliceStream, hlen, u]
      rw [hlast, show A + (d - 1) = A - 1 + d by omega]
      exact hm hA
    exact ⟨u, by simp [u]; omega, he, spliceStream_periodic hp,
      spliceStream_noInfiniteAdmission M R hp hc he hmm⟩

theorem trajectory_short_visit {S : Type*} [Fintype S] (f : S → S)
    (q : ℕ → S) (hq : ∀ i, q (i + 1) = f (q i)) (t : ℕ) :
    ∃ i, i < Fintype.card S ∧ q i = q t := by
  let D : DFA Unit S := ⟨fun s _ => f s, q 0, ∅⟩
  have he (w : List Unit) : D.eval w = q w.length := by
    induction w using List.reverseRecOn with
    | nil => rfl
    | append_singleton w a ih =>
      rw [DFA.eval_append_singleton, List.length_append, List.length_singleton, hq]
      exact congrArg f ih
  obtain ⟨u, _, hu, heq⟩ := Packets.exists_short_evalFrom D D.start
    (List.replicate t ())
  change D.eval u = D.eval (List.replicate t ()) at heq
  rw [he, he, List.length_replicate] at heq
  exact ⟨u.length, hu, heq⟩

theorem periodicFrom_mod {W : ℕ → α} {A d : ℕ} (hp : PeriodicFrom W A d)
    (k : ℕ) : W (A + k) = W (A + k % d) := by
  have hh := periodicFrom_mul hp (k := A + k % d) (by omega) (k/d)
  rw [Nat.add_assoc, Nat.mul_comm (k/d) d, Nat.mod_add_div] at hh
  exact hh

theorem periodic_short_visit [Fintype Q] (M : DFA α Q) {W : ℕ → α} {A d : ℕ}
    (hd : 0 < d) (hp : PeriodicFrom W A d) (t : ℕ) :
    ∃ i, i < Fintype.card Q * d ∧
      M.eval (streamPrefix W (A + i)) = M.eval (streamPrefix W (A + t)) ∧ i % d = t % d := by
  let q : ℕ → Q × Fin d := fun i =>
    (M.eval (streamPrefix W (A + i)), ⟨i % d, Nat.mod_lt _ hd⟩)
  let f : Q × Fin d → Q × Fin d := fun s =>
    (M.step s.1 (W (A + s.2)), ⟨(s.2.val + 1) % d, Nat.mod_lt _ hd⟩)
  have hq : ∀ i, q (i + 1) = f (q i) := by
    intro i
    apply Prod.ext
    · change M.eval (streamPrefix W (A + (i + 1))) =
        M.step (M.eval (streamPrefix W (A + i))) (W (A + i % d))
      rw [show A + (i + 1) = A + i + 1 by omega, streamPrefix_succ, DFA.eval_append_singleton,
        periodicFrom_mod hp i]
    · apply Fin.ext
      change (i + 1) % d = (i % d + 1) % d
      simp [Nat.add_mod]
  obtain ⟨i, hi, he⟩ := trajectory_short_visit f q hq t
  refine ⟨i, by simpa using hi, congrArg Prod.fst he, ?_⟩
  exact congrArg (fun s : Q × Fin d => s.2.val) he

theorem periodic_visit_future (M : DFA α Q) {W : ℕ → α} {A d i t : ℕ}
    (hp : PeriodicFrom W A d)
    (he : M.eval (streamPrefix W (A + i)) = M.eval (streamPrefix W (A + t)))
    (hm : i % d = t % d) (k : ℕ) :
    M.eval (streamPrefix W (A + i + k)) = M.eval (streamPrefix W (A + t + k)) := by
  induction k with
  | zero => simpa using he
  | succ k ih =>
    rw [show A + i + (k + 1) = (A + i + k) + 1 by omega,
      show A + t + (k + 1) = (A + t + k) + 1 by omega,
      streamPrefix_succ, streamPrefix_succ, DFA.eval_append_singleton,
      DFA.eval_append_singleton, ih]
    congr 1
    simp only [Nat.add_assoc]
    rw [periodicFrom_mod hp (i + k), periodicFrom_mod hp (t + k)]
    have hm' : (i + k) % d = (t + k) % d := by rw [Nat.add_mod i k d, Nat.add_mod t k d, hm]
    rw [hm']

/-- An eventually periodic witness yields a hole with a quadratically bounded rejected tail. -/
theorem exists_bounded_tail_of_periodic_witness [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    {W : ℕ → α} {n d : ℕ} (hd : 0 < d) (hdN : d ≤ Fintype.card Q)
    (hp : PeriodicFrom W n d) (hc : NoInfiniteAdmission M R W)
    (ht : ∀ k, n ≤ k → M.eval (streamPrefix W k) ∈ T) :
    ∃ w J, IsReaderHole M R T w ∧ IsFirstRejectedPrefix M T w J ∧
      w.length - J ≤ (Fintype.card Q) ^ 2 + 2 * Fintype.card Q := by
  obtain ⟨A, hAn, hper, _, hmis⟩ := exists_periodicOnset hp
  obtain ⟨u, hu, hue, hup, huc⟩ := compress_periodic_prefix M R hd hper hc hmis
  let U := spliceStream u W A
  have htar (k : ℕ) : M.eval (streamPrefix U (u.length + (n - A) + k)) ∈ T := by
    rw [Nat.add_assoc, spliceStream_eval M hue]
    apply ht
    omega
  obtain ⟨i, hi, hie, him⟩ := periodic_short_visit M hd hup (n - A)
  have hafter (k : ℕ) : M.eval (streamPrefix U (u.length + i + k)) ∈ T := by
    rw [periodic_visit_future M hup hie him k]
    exact htar k
  obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T (by simpa using hafter 0)
  let L := u.length + i + J + d
  have hL : M.eval (streamPrefix U L) ∈ T := by
    simpa [L, Nat.add_assoc] using hafter (J + d)
  have hJL : IsFirstRejectedPrefix M T (streamPrefix U L) J := by
    have hj : J ≤ u.length + i := by simpa using hJ.1
    refine ⟨by simp [L]; omega, ?_, ?_⟩
    · rw [streamPrefix_take U (by dsimp [L]; omega)]
      simpa only [streamPrefix_take U hj] using hJ.2.1
    · intro j hjJ
      rw [streamPrefix_take U (by dsimp [L]; omega)]
      simpa only [streamPrefix_take U (show j ≤ u.length + i by omega)] using hJ.2.2 j hjJ
  obtain ⟨hh, hlen⟩ := periodic_truncation M R T h.cone U hd
    (fun k hk => hup k (by omega)) huc hL hJL
  refine ⟨_, J, hh, hJL, ?_⟩
  rw [hlen]
  have hm := Nat.mul_le_mul_left (Fintype.card Q) hdN
  nlinarith

/-- A reachable rejected state admits a nonempty return word. -/
def RejectedCycle (M : DFA α Q) (T : Set Q) (q : Q) : Prop :=
  (∃ v, M.eval v = q) ∧ q ∈ T ∧ ∃ c : List α, c ≠ [] ∧ M.evalFrom q c = q

/--
Two safe letters at a rejected cyclic state yield a bounded tail by breaking every admitted
period.
-/
theorem exists_bounded_tail_of_branching_cycle [Fintype Q] (M : DFA (Fin 2) Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    {q : Q} (hq : RejectedCycle M T q) (hn : ∀ a, M.step q a ∈ T) :
    ∃ w J, IsReaderHole M R T w ∧ IsFirstRejectedPrefix M T w J ∧
      w.length - J ≤ 4 * Fintype.card Q := by
  obtain ⟨⟨v, hv⟩, hqt, ⟨c, hc, hret⟩⟩ := hq
  obtain ⟨u, _, hu, hue⟩ := Packets.exists_short_evalFrom M M.start v
  have huq : M.eval u = q := hue.trans hv
  obtain ⟨c, hc, hret, hcl⟩ : ∃ c : Word, c ≠ [] ∧ M.evalFrom q c = q ∧
      c.length ≤ Fintype.card Q := by
    cases c with
    | nil => exact (hc rfl).elim
    | cons a c =>
      obtain ⟨z, _, hz, hze⟩ := Packets.exists_short_evalFrom M (M.step q a) c
      exact ⟨a::z, by simp, hze.trans hret, by simp; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, c.head? ≠ some b := by
    by_cases hh : c.head? = some 0
    · exact ⟨1, by rw [hh]; decide⟩
    · exact ⟨0, hh⟩
  let K := DerivedClass.cycleCopies u c
  have hK := DerivedClass.cycleCopies_bounds u c hc
  have hpow (k : ℕ) : M.evalFrom q (pow c k) = q := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, DFA.evalFrom_of_append, hret, ih]
  let w := u ++ pow c K ++ [b]
  have hwt : M.eval w ∈ T := by
    simpa only [w, DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton,
      show M.evalFrom M.start u = q from huq, hpow] using hn b
  obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T hwt
  have hJu : J ≤ u.length := by
    by_contra hh
    apply hJ.2.2 u.length (by omega)
    simpa [w, huq] using hqt
  have hh : IsReaderHole M R T w := by
    apply (isReaderHole_iff M R T w).mpr
    refine ⟨hwt, ?_⟩
    intro s e hse he hp hr
    have heJ := h.cone w J hwt hJ s e hse he hp hr
    have hsu : s ≤ u.length := by omega
    have hper := comparison_period hse.le hp
    have hdrop : w.drop s = u.drop s ++ (pow c K ++ [b]) := by
      simp only [w, List.append_assoc, List.drop_append_of_le_length hsu]
    have htail : HasPeriod (pow c K ++ [b]) (e - s) :=
      hper.infix (by rw [hdrop]; exact (List.suffix_append _ _).isInfix)
    exact DerivedClass.fine_wilf_escape hc (by omega) (by dsimp [K]; omega) hb htail
  refine ⟨w, J, hh, hJ, ?_⟩
  have hlen : w.length = u.length + K * c.length + 1 := by simp [w, length_pow, Nat.add_assoc]
  dsimp [K] at hlen
  omega

/-- Every rejected cyclic state has at most one letter leading to another rejected state. -/
def ForcedCycles (M : DFA α Q) (T : Set Q) : Prop :=
  ∀ q, RejectedCycle M T q → ∀ a b, M.step q a ∈ T → M.step q b ∈ T → a = b

theorem cycle_safe_letter (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] {q : Q} (hq : RejectedCycle M T q) :
    ∃ a, M.step q a ∈ T := by
  obtain ⟨⟨v, hv⟩, hqt, ⟨c, hc, hr⟩⟩ := hq
  cases c with
  | nil => exact (hc rfl).elim
  | cons a c =>
    refine ⟨a, ?_⟩
    have ht : M.eval (v ++ a::c) ∈ T := by
      simpa only [DFA.eval, DFA.evalFrom_of_append, show M.evalFrom M.start v = q from hv,
        hr] using hqt
    have hh := h.between v (v++[a]) (v++a::c) (List.prefix_append _ _)
      (by exact ⟨c, by simp⟩) (hv ▸ hqt) ht
    simpa only [DFA.eval_append_singleton, hv] using hh

theorem forced_cycle_step (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] (hf : ForcedCycles M T)
    {q : Q} (hq : RejectedCycle M T q) {a : α} (ha : M.step q a ∈ T) :
    RejectedCycle M T (M.step q a) := by
  obtain ⟨⟨v, hv⟩, hqt, ⟨c, hc, hr⟩⟩ := hq
  cases c with
  | nil => exact (hc rfl).elim
  | cons b c =>
    have hb : M.step q b ∈ T := by
      have ht : M.eval (v ++ b::c) ∈ T := by
        simpa only [DFA.eval, DFA.evalFrom_of_append, show M.evalFrom M.start v = q from hv,
          hr] using hqt
      have hh := h.between v (v++[b]) (v++b::c) (List.prefix_append _ _)
        (by exact ⟨c, by simp⟩) (hv ▸ hqt) ht
      simpa only [DFA.eval_append_singleton, hv] using hh
    have hab := hf q ⟨⟨v, hv⟩, hqt, ⟨b::c, hc, hr⟩⟩ a b ha hb
    subst b
    refine ⟨⟨v++[a], by simp [hv]⟩, ha, c++[a], by simp, ?_⟩
    rw [DFA.evalFrom_append_singleton]
    exact congrArg (fun q => M.step q a) hr

theorem trajectory_eq_future {S : Type*} (f : S → S) (q : ℕ → S)
    (hq : ∀ i, q (i + 1) = f (q i)) {i j : ℕ} (he : q i = q j) (k : ℕ) :
    q (i + k) = q (j + k) := by
  induction k with
  | zero => simpa using he
  | succ k ih => simpa only [← Nat.add_assoc, hq] using congrArg f ih

theorem trajectory_period [Fintype Q] (f : Q → Q) (q : ℕ → Q)
    (hq : ∀ i, q (i + 1) = f (q i)) :
    ∃ m d, 0 < d ∧ d ≤ Fintype.card Q ∧ ∀ k, q (m + k + d) = q (m + k) := by
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card Q + 1) => q i) (by simp)
  have hij : i.val ≠ j.val := fun hh => hne (Fin.ext hh)
  wlog hlt : i.val < j.val generalizing i j
  · exact this j i hne.symm he.symm (Ne.symm hij) (by omega)
  refine ⟨i.val, j.val - i.val, by omega, by omega, ?_⟩
  intro k
  have hh := trajectory_eq_future f q hq he k
  convert hh.symm using 1; congr 1; omega

theorem forced_path_tracks (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    [h : RejectedPath M R T] (hf : ForcedCycles M T)
    (q : ℕ → Q) (a : ℕ → α) (hq : ∀ i, RejectedCycle M T (q i))
    (hs : ∀ i, M.step (q i) (a i) ∈ T) (hstep : ∀ i, q (i + 1) = M.step (q i) (a i))
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
        have hh := hprefix (k + 1)
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
      have hh := hprefix (k + 1)
      simpa only [List.take_succ_eq_append_getElem hk, ← List.append_assoc,
        DFA.eval_append_singleton, he] using hh
    simpa [streamPrefix] using hf (q k) (hq k) z[k] (a k) hsafe (hs k)

/-- When rejected cycles are forced, a long rejected path has a periodic infinite extension. -/
theorem forced_infinite_extension [Fintype Q] (M : DFA (Fin 2) Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    (hf : ForcedCycles M T) {v c : Word} (hv : RejectedCycle M T (M.eval v))
    (hw : IsReaderHole M R T (v++c)) :
    ∃ W n d, 0 < d ∧ d ≤ Fintype.card Q ∧ PeriodicFrom W n d ∧
      NoInfiniteAdmission M R W ∧ ∀ k, n ≤ k → M.eval (streamPrefix W k) ∈ T := by
  classical
  let a : Q → Fin 2 := fun q => if hs : ∃ a, M.step q a ∈ T then hs.choose else 0
  have ha (q : Q) (hq : RejectedCycle M T q) : M.step q (a q) ∈ T := by
    have hs := cycle_safe_letter M R T hq
    dsimp [a]
    rw [dite_eq_left hs]
    exact hs.choose_spec
  let f : Q → Q := fun q => M.step q (a q)
  let q : ℕ → Q := fun k => f^[k] (M.eval v)
  have hqstep (i : ℕ) : q (i + 1) = f (q i) := Function.iterate_succ_apply' _ _ _
  have hq (i : ℕ) : RejectedCycle M T (q i) := by
    induction i with
    | zero => exact hv
    | succ i ih =>
      rw [hqstep]
      exact forced_cycle_step M R T hf ih (ha _ ih)
  let Z : ℕ → Fin 2 := fun k => a (q k)
  let W := spliceStream v Z 0
  have hrun (k : ℕ) : M.eval (streamPrefix W (v.length + k)) = q k := by
    induction k with
    | zero =>
      change M.eval (streamPrefix (spliceStream v Z 0) v.length) = M.eval v
      rw [spliceStream_prefix]
    | succ k ih =>
      rw [show v.length + (k + 1) = v.length + k + 1 by omega,
        streamPrefix_succ, DFA.eval_append_singleton, ih, hqstep]
      congr 1
      simpa only [Nat.zero_add] using spliceStream_after v Z 0 k
  have htar (k : ℕ) (hk : v.length ≤ k) : M.eval (streamPrefix W k) ∈ T := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [hrun]
    exact (hq i).2.1
  have hc : c = streamPrefix Z c.length := forced_path_tracks M R T hf q Z hq
    (fun i => ha _ (hq i)) hqstep rfl ((isReaderHole_iff _ _ _ _).mp hw).1
  have hpre : v++c = streamPrefix W (v++c).length := by
    rw [List.length_append, streamPrefix_add, spliceStream_prefix]
    simp only [W, spliceStream_after, Nat.zero_add]
    rw [← hc]
  have hclear := extension_noInfiniteAdmission M R T W hw hpre
    (fun k hk => htar k (by simp only [List.length_append] at hk; omega))
  obtain ⟨m, d, hd, hdN, hper⟩ := trajectory_period f q hqstep
  refine ⟨W, v.length + m, d, hd, hdN, ?_, hclear, ?_⟩
  · intro k hk
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hh := congrArg a (hper i)
    simpa only [W, Nat.add_assoc, spliceStream_after, Nat.zero_add, Z] using hh
  · intro k hk
    exact htar k (by omega)

/-- Forced rejected cycles yield a hole with a quadratically bounded rejected tail. -/
theorem boundedRejectedTail_of_forcedCycles [Fintype Q] (M : DFA (Fin 2) Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    (hf : ForcedCycles M T) :
    BoundedRejectedTail M R T ((Fintype.card Q) ^ 2 + 2 * Fintype.card Q) := by
  rintro ⟨w, hw⟩
  have hwt := ((isReaderHole_iff M R T w).mp hw).1
  obtain ⟨J, hJ⟩ := exists_firstRejectedPrefix M T hwt
  by_cases hshort : w.length - J < Fintype.card Q
  · exact ⟨w, J, hw, hJ, by nlinarith⟩
  · obtain ⟨q, a, b, z, hsplit, _, hb, hqa, hloop, _⟩ := M.evalFrom_split
      (s := M.eval (w.take J)) (x := w.drop J) (by simp; omega) rfl
    let v := w.take J ++ a
    have hvq : M.eval v = q := by
      simpa only [v, DFA.eval, DFA.evalFrom_of_append] using hqa
    have hwfac : w = v ++ (b++z) := by
      calc
        w = w.take J ++ w.drop J := (List.take_append_drop J w).symm
        _ = v ++ (b++z) := by rw [hsplit]; simp only [v, List.append_assoc]
    have hqT : q ∈ T := by
      rw [← hvq]
      apply h.between (w.take J) v w (List.prefix_append _ _)
        (by rw [hwfac]; exact List.prefix_append _ _) hJ.2.1 hwt
    have hvcycle : RejectedCycle M T (M.eval v) := by
      rw [hvq]
      exact ⟨⟨v, hvq⟩, hqT, b, hb, hloop⟩
    obtain ⟨W, n, d, hd, hdN, hper, hclear, htar⟩ := forced_infinite_extension M R T hf
      hvcycle (hwfac ▸ hw)
    exact exists_bounded_tail_of_periodic_witness M R T hd hdN hper hclear htar

/--
Every binary finite reader satisfying the rejected-path conditions has tail bound `|Q|² + 4|Q|`.
-/
theorem boundedRejectedTail_of_rejectedPath [Fintype Q] (M : DFA (Fin 2) Q)
    (R : Q → Q → Prop) (T : Set Q) [RejectedPath M R T] :
    BoundedRejectedTail M R T ((Fintype.card Q) ^ 2 + 4 * Fintype.card Q) := by
  classical
  by_cases hb : ∃ q, RejectedCycle M T q ∧ ∀ a, M.step q a ∈ T
  · obtain ⟨q, hq, hn⟩ := hb
    intro _
    obtain ⟨w, J, hw, hJ, hl⟩ := exists_bounded_tail_of_branching_cycle M R T hq hn
    exact ⟨w, J, hw, hJ, by nlinarith⟩
  · have hf : ForcedCycles M T := by
      intro q hq a b ha hb'
      by_contra hab
      apply hb
      refine ⟨q, hq, ?_⟩
      intro x
      fin_cases a <;> fin_cases b <;> fin_cases x <;> simp_all
    intro hh
    obtain ⟨w, J, hw, hJ, hl⟩ := boundedRejectedTail_of_forcedCycles M R T hf hh
    exact ⟨w, J, hw, hJ, by nlinarith⟩

open ConstructedAxioms

/--
The transition-image reader of a constraint system has a quadratically bounded rejected tail.
-/
theorem nsse_boundedRejectedTail {k : ℕ} (ϕ : Constraint k) (x y : V k) (side : Side) :
    BoundedRejectedTail (imageReader (imageμ ϕ x y side))
      (endpointRelation (imageD ϕ x y side)) (imageVA ϕ x y side)ᶜ
      ((Fintype.card (Image ϕ x y side)) ^ 2 + 4 * Fintype.card (Image ϕ x y side)) := by
  let := nsse_rejectedPath (ϕ := ϕ) (x := x) (y := y) (d := side)
  exact boundedRejectedTail_of_rejectedPath _ _ _

end DeciNSSE.RejectedTail
namespace DeciNSSE.Bridge
open RejectedTail ConstructedAxioms

/-- The quadratic bound `N² + 4N` for the number of letters in a rejected tail. -/
def rejectedTailBound {k : ℕ} (ϕ : Constraint k) (x y : V k) (side : Side) : ℕ :=
  (Fintype.card (Image ϕ x y side)) ^ 2 + 4 * Fintype.card (Image ϕ x y side)

/-- Decide entailment using the quadratic tail bound and corresponding bounds on depth. -/
def decideEntailsOfRejectedTailDepth {k : ℕ} (ϕ : Constraint k) (x y : V k)
    (depth : Side → ℕ)
    (hdepth : ∀ side, RejectedTailDepth ϕ x y side
      (rejectedTailBound ϕ x y side) (depth side)) : Decidable (Entails ϕ x y) :=
  decideEntailsOfRejectedTail ϕ x y (rejectedTailBound ϕ x y) depth
    (nsse_boundedRejectedTail ϕ x y) hdepth
end DeciNSSE.Bridge
