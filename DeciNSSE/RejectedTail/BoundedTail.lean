import DeciNSSE.RejectedTail.Forced
import DeciNSSE.Words

/-! # A quadratic bound on rejected tails

For a finite-alphabet reader satisfying the rejected-path invariant, a hole
can be chosen with rejected tail at most `N^2 + 4*N`. A branching rejected
cycle breaks periods; otherwise a forced periodic continuation gives the bound.
-/

set_option autoImplicit false
namespace DeciNSSE.RejectedTail

open Holes Words
variable {α Q : Type*}

theorem branching_boundedRejectedTail [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    {q : Q} (hq : RejectedCycle M T q) (hn : ∃ a b, a ≠ b ∧ M.step q a ∈ T ∧ M.step q b ∈ T) :
    ∃ w J, IsReaderHole M R T w ∧ IsFirstRejectedPrefix M T w J ∧
      w.length-J ≤ 4*Fintype.card Q := by
  obtain ⟨⟨v,hv⟩,hqt,⟨c,hc,hret⟩⟩ := hq
  obtain ⟨u,_,hu,hue⟩ := Packets.exists_short_evalFrom M M.start v
  have huq : M.eval u = q := hue.trans hv
  obtain ⟨c,hc,hret,hcl⟩ : ∃ c : List α, c ≠ [] ∧ M.evalFrom q c = q ∧
      c.length ≤ Fintype.card Q := by
    cases c with
    | nil => exact (hc rfl).elim
    | cons a c =>
      obtain ⟨z,_,hz,hze⟩ := Packets.exists_short_evalFrom M (M.step q a) c
      exact ⟨a::z,by simp,hze.trans hret,by simp; omega⟩
  obtain ⟨a,b,hab,ha,hb⟩ := hn
  obtain ⟨b,hb,hbs⟩ : ∃ b : α, c.head? ≠ some b ∧ M.step q b ∈ T := by
    by_cases hh : c.head? = some a
    · exact ⟨b, fun he => hab (Option.some.inj (hh.symm.trans he)), hb⟩
    · exact ⟨a, hh, ha⟩
  let K := cycleCopies u c
  have hK := cycleCopies_bounds u c hc
  have hpow (k : ℕ) : M.evalFrom q (pow c k) = q := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, DFA.evalFrom_of_append, hret, ih]
  let w := u ++ pow c K ++ [b]
  have hwt : M.eval w ∈ T := by
    simpa only [w, DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton,
      show M.evalFrom M.start u = q from huq, hpow] using hbs
  obtain ⟨J,hJ⟩ := exists_firstRejectedPrefix M T hwt
  have hJu : J ≤ u.length := by
    by_contra hh
    apply hJ.2.2 u.length (by omega)
    simpa [w, huq] using hqt
  have hh : IsReaderHole M R T w := by
    apply (Holes.isReaderHole_iff M R T w).mpr
    refine ⟨hwt, ?_⟩
    intro s e hse he hp hr
    have heJ := h.cone w J hwt hJ s e hse he hp hr
    have hsu : s ≤ u.length := by omega
    have hper := comparison_period hse.le hp
    have hdrop : w.drop s = u.drop s ++ (pow c K ++ [b]) := by
      simp only [w, List.append_assoc, List.drop_append_of_le_length hsu]
    have htail : HasPeriod (pow c K ++ [b]) (e-s) :=
      hper.infix (by rw [hdrop]; exact (List.suffix_append _ _).isInfix)
    exact fine_wilf_escape hc (by omega) (by dsimp [K]; omega) hb htail
  refine ⟨w,J,hh,hJ, ?_⟩
  have hlen : w.length = u.length + K*c.length+1 := by simp [w, length_pow, Nat.add_assoc]
  dsimp [K] at hlen
  omega

theorem forced_infinite_extension [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    (hf : ForcedCycles M T) {v c : List α} (hv : RejectedCycle M T (M.eval v))
    (hw : IsReaderHole M R T (v++c)) :
    ∃ W n d, 0 < d ∧ d ≤ Fintype.card Q ∧ PeriodicFrom W n d ∧
      NoInfiniteAdmission M R W ∧ ∀ k, n ≤ k → M.eval (streamPrefix W k) ∈ T := by
  classical
  let a : Q → α := fun q => if hs : ∃ a, M.step q a ∈ T then hs.choose else (cycle_safe_letter M R T hv).choose
  have ha (q : Q) (hq : RejectedCycle M T q) : M.step q (a q) ∈ T := by
    have hs := cycle_safe_letter M R T hq
    dsimp [a]
    rw [dite_eq_left hs]
    exact hs.choose_spec
  let f : Q → Q := fun q => M.step q (a q)
  let q : ℕ → Q := fun k => f^[k] (M.eval v)
  have hqstep (i : ℕ) : q (i+1) = f (q i) := Function.iterate_succ_apply' _ _ _
  have hq (i : ℕ) : RejectedCycle M T (q i) := by
    induction i with
    | zero => exact hv
    | succ i ih =>
      rw [hqstep]
      exact forced_cycle_step M R T hf ih (ha _ ih)
  let Z : ℕ → α := fun k => a (q k)
  let W := spliceStream v Z 0
  have hrun (k : ℕ) : M.eval (streamPrefix W (v.length+k)) = q k := by
    induction k with
    | zero =>
      change M.eval (streamPrefix (spliceStream v Z 0) v.length) = M.eval v
      rw [spliceStream_prefix]
    | succ k ih =>
      rw [show v.length+(k+1) = v.length+k+1 by omega,
        streamPrefix_succ, DFA.eval_append_singleton, ih, hqstep]
      congr 1
      simpa only [Nat.zero_add] using spliceStream_after v Z 0 k
  have htar (k : ℕ) (hk : v.length ≤ k) : M.eval (streamPrefix W k) ∈ T := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [hrun]
    exact (hq i).2.1
  have hc : c = streamPrefix Z c.length := forced_path_tracks M R T hf q Z hq
    (fun i => ha _ (hq i)) hqstep rfl ((Holes.isReaderHole_iff _ _ _ _).mp hw).1
  have hpre : v++c = streamPrefix W (v++c).length := by
    rw [List.length_append, streamPrefix_add, spliceStream_prefix]
    simp only [W, spliceStream_after, Nat.zero_add]
    rw [← hc]
  have hclear := extension_noInfiniteAdmission M R T W hw hpre
    (fun k hk => htar k (by simp only [List.length_append] at hk; omega))
  obtain ⟨m,d,hd,hdN,hper⟩ := trajectory_period f q hqstep
  refine ⟨W,v.length+m,d,hd,hdN, ?_,hclear, ?_⟩
  · intro k hk
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le hk
    have hh := congrArg a (hper i)
    simpa only [W, Nat.add_assoc, spliceStream_after, Nat.zero_add, Z] using hh
  · intro k hk
    exact htar k (by omega)

/-- The forced-cycle case, including holes whose tail is already short. -/
theorem forced_boundedRejectedTail [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [h : RejectedPath M R T]
    (hf : ForcedCycles M T) :
    BoundedRejectedTail M R T ((Fintype.card Q)^2 + 2*Fintype.card Q) := by
  rintro ⟨w,hw⟩
  have hwt := ((Holes.isReaderHole_iff M R T w).mp hw).1
  obtain ⟨J,hJ⟩ := exists_firstRejectedPrefix M T hwt
  by_cases hshort : w.length-J < Fintype.card Q
  · exact ⟨w,J,hw,hJ,by nlinarith⟩
  · obtain ⟨q,a,b,z,hsplit,_,hb,hqa,hloop,_⟩ := M.evalFrom_split
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
      exact ⟨⟨v,hvq⟩,hqT,b,hb,hloop⟩
    obtain ⟨W,n,d,hd,hdN,hper,hclear,htar⟩ := forced_infinite_extension M R T hf
      hvcycle (hwfac ▸ hw)
    exact periodic_witness_brt M R T hd hdN hper hclear htar

/-- The same state-only bound works over every alphabet, including the empty one. -/
theorem boundedRejectedTail_of_rejectedPath [Fintype Q] (M : DFA α Q)
    (R : Q → Q → Prop) (T : Set Q) [RejectedPath M R T] :
    BoundedRejectedTail M R T ((Fintype.card Q)^2 + 4*Fintype.card Q) := by
  classical
  by_cases hb : ∃ q, RejectedCycle M T q ∧
      ∃ a b, a ≠ b ∧ M.step q a ∈ T ∧ M.step q b ∈ T
  · obtain ⟨q,hq,hn⟩ := hb
    intro _
    obtain ⟨w,J,hw,hJ,hl⟩ := branching_boundedRejectedTail M R T hq hn
    exact ⟨w,J,hw,hJ,by nlinarith⟩
  · have hf : ForcedCycles M T := by
      intro q hq a b ha hb'
      by_contra hab
      exact hb ⟨q,hq,a,b,hab,ha,hb'⟩
    intro hh
    obtain ⟨w,J,hw,hJ,hl⟩ := forced_boundedRejectedTail M R T hf hh
    exact ⟨w,J,hw,hJ,by nlinarith⟩

end DeciNSSE.RejectedTail
