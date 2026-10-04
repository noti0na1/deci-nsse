import Mathlib.Data.List.GetD
import Mathlib.Data.List.ReduceOption
import DeciNSSE.Holes.Basic

/-! # Finite enumeration and simultaneous word compression

Tuples of words are encoded by padded columns. Finite automata compress
these encodings, while bounded lists and bounded comparisons provide
the finite searches used to decide existence of shallow holes.
-/

namespace DeciNSSE.Packets

section Horizon
variable {β : Type*}

theorem drop_prefix_drop_iff (Y : List β) {a b : ℕ} :
    Y.drop b <+: Y.drop a ↔ ∀ k, b + k < Y.length → Y[a + k]? = Y[b + k]? := by
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h k hk
    have := congrArg (·[k]?) h
    simp only [List.getElem?_drop, List.getElem?_take, List.length_drop] at this
    rw [ite_eq_left (by omega)] at this
    exact this.symm
  · intro h
    apply List.ext_getElem?
    intro k
    simp only [List.getElem?_drop, List.getElem?_take, List.length_drop]
    split_ifs with hk
    · exact (h k (by omega)).symm
    · rw [List.getElem?_eq_none (by omega)]

end Horizon

section ShortWords
variable {α S : Type*}

theorem exists_short_evalFrom [Fintype S] (A : DFA α S) (s : S) (x : List α) :
    ∃ y, y.Sublist x ∧ y.length < Fintype.card S ∧ A.evalFrom s y = A.evalFrom s x := by
  induction hn : x.length using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  subst hn
  by_cases hx : x.length < Fintype.card S
  · exact ⟨x, List.Sublist.refl x, hx, rfl⟩
  · obtain ⟨q, a, b, c, rfl, -, hb, ha, -, hc⟩ :=
      A.evalFrom_split (s := s) (t := A.evalFrom s x) (by omega) rfl
    have hb' : b.length ≠ 0 := fun h0 => hb (List.eq_nil_of_length_eq_zero h0)
    have hlt : (a ++ c).length < (a ++ b ++ c).length := by
      simp only [List.length_append]
      omega
    obtain ⟨y, hy1, hy2, hy3⟩ := ih _ hlt (a ++ c) rfl
    refine ⟨y, hy1.trans (List.Sublist.append (List.sublist_append_left a b)
      (List.Sublist.refl c)), hy2, ?_⟩
    rw [hy3, ← hc, A.evalFrom_of_append s a c, ha]

open Classical in

noncomputable def congrDFA (f : List α → S) : DFA α S where
  step s a := if h : ∃ x, f x = s then f (h.choose ++ [a]) else s
  start := f []
  accept := ∅

theorem congrDFA_evalFrom (f : List α → S)
    (hf : ∀ x y a, f x = f y → f (x ++ [a]) = f (y ++ [a])) (x : List α) :
    (congrDFA f).evalFrom (f []) x = f x := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x a ih =>
    rw [DFA.evalFrom_append_singleton, ih]
    have h : ∃ y, f y = f x := ⟨x, rfl⟩
    simp only [congrDFA]
    rw [dite_eq_left h]
    exact hf _ _ _ h.choose_spec

theorem exists_short_of_congr [Fintype S] (f : List α → S)
    (hf : ∀ x y a, f x = f y → f (x ++ [a]) = f (y ++ [a])) (x : List α) :
    ∃ y, y.Sublist x ∧ y.length < Fintype.card S ∧ f y = f x := by
  obtain ⟨y, h1, h2, h3⟩ := exists_short_evalFrom (congrDFA f) (f []) x
  rw [congrDFA_evalFrom f hf, congrDFA_evalFrom f hf] at h3
  exact ⟨y, h1, h2, h3⟩

end ShortWords

open DeciNSSE.Holes
open scoped List

section ColumnEncoding
variable {σ : Type*} {r : ℕ}

def tr (w : List (Fin r → Option σ)) (k : Fin r) : List (Option σ) := w.map (· k)

def dec (w : List (Fin r → Option σ)) (k : Fin r) : List σ := (tr w k).reduceOption

def PadPre (l : List (Option σ)) : Prop := ∃ (a : ℕ) (P : List σ), l = List.replicate a none ++ P.map some

def Valid (w : List (Fin r → Option σ)) : Prop := ∀ k, PadPre (tr w k)

def padL (L : ℕ) (W : List σ) : List (Option σ) := List.replicate (L - W.length) none ++ W.map some

def clen (Ws : Fin r → List σ) : ℕ := Finset.univ.sup fun k => (Ws k).length

def conv (Ws : Fin r → List σ) : List (Fin r → Option σ) :=
  List.ofFn fun p : Fin (clen Ws) => fun k => (padL (clen Ws) (Ws k)).getD p none

theorem reduceOption_map_some (P : List σ) : (P.map some).reduceOption = P := by
  induction P with
  | nil => rfl
  | cons a P ih => rw [List.map_cons, List.reduceOption_cons_of_some, ih]

theorem reduceOption_pad (a : ℕ) (P : List σ) :
    (List.replicate a none ++ P.map some).reduceOption = P := by
  rw [List.reduceOption_append, List.reduceOption_replicate_none, List.nil_append,
    reduceOption_map_some]

theorem PadPre.eq {l : List (Option σ)} (h : PadPre l) :
    l = List.replicate (l.length - l.reduceOption.length) none ++ l.reduceOption.map some := by
  obtain ⟨a, P, rfl⟩ := h
  rw [reduceOption_pad]
  simp

theorem PadPre.sublist {l l' : List (Option σ)} (h : PadPre l) (hs : l' <+ l) : PadPre l' := by
  obtain ⟨a, P, rfl⟩ := h
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.sublist_append_iff.mp hs
  obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.mp h1
  obtain ⟨P', -, rfl⟩ := List.sublist_map_iff.mp h2
  exact ⟨n, P', rfl⟩

theorem tr_length (w : List (Fin r → Option σ)) (k : Fin r) : (tr w k).length = w.length :=
  List.length_map _

theorem dec_snoc (w : List (Fin r → Option σ)) (c : Fin r → Option σ) (k : Fin r) :
    dec (w ++ [c]) k = dec w k ++ (c k).toList := by
  simp only [dec, tr, List.map_append, List.map_singleton, List.reduceOption_append,
    List.reduceOption_singleton]

theorem Valid.sublist {w w' : List (Fin r → Option σ)} (hw : Valid w) (hs : w' <+ w) :
    Valid w' := fun k => (hw k).sublist (hs.map _)

theorem dec_sublist {w w' : List (Fin r → Option σ)} (hs : w' <+ w) (k : Fin r) :
    (dec w' k).Sublist (dec w k) := (hs.map _).filterMap _

theorem length_dec_le (w : List (Fin r → Option σ)) (k : Fin r) : (dec w k).length ≤ w.length :=
  (List.reduceOption_length_le _).trans (tr_length w k).le

theorem le_clen (Ws : Fin r → List σ) (k : Fin r) : (Ws k).length ≤ clen Ws :=
  Finset.le_sup (f := fun k => (Ws k).length) (Finset.mem_univ k)

theorem padL_length {L : ℕ} {W : List σ} (h : W.length ≤ L) : (padL L W).length = L := by
  simp only [padL, List.length_append, List.length_replicate, List.length_map]
  omega

theorem length_conv (Ws : Fin r → List σ) : (conv Ws).length = clen Ws := List.length_ofFn

theorem tr_conv (Ws : Fin r → List σ) (k : Fin r) : tr (conv Ws) k = padL (clen Ws) (Ws k) := by
  have hl := padL_length (le_clen Ws k)
  apply List.ext_getElem (by rw [tr_length, length_conv, hl])
  intro p h1 h2
  simp only [tr, conv, List.getElem_map, List.getElem_ofFn]
  rw [List.getD_eq_getElem _ _ h2]

theorem dec_conv (Ws : Fin r → List σ) : dec (conv Ws) = Ws := by
  funext k
  rw [dec, tr_conv, padL, reduceOption_pad]

theorem valid_conv (Ws : Fin r → List σ) : Valid (conv Ws) := fun k => ⟨_, _, tr_conv Ws k⟩

theorem eq_of_tr {w w' : List (Fin r → Option σ)} (hl : w.length = w'.length)
    (h : ∀ k, tr w k = tr w' k) : w = w' := by
  apply List.ext_getElem hl
  intro p h1 h2
  funext k
  have := congrArg (fun l => l[p]?) (h k)
  simp only [tr, List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
    Option.map_some, Option.some_inj] at this
  exact this

theorem conv_noPad (Ws : Fin r → List σ) : ∀ c ∈ conv Ws, ∃ k, c k ≠ none := by
  intro c hc
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hc
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have hp := p.2
    simp only [clen, hcon, Finset.sup_empty] at hp
    exact absurd hp (Nat.not_lt_zero _)
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup _ hne fun k => (Ws k).length
  refine ⟨k, ?_⟩
  have hp := p.2
  have e : padL (clen Ws) (Ws k) = (Ws k).map some := by
    rw [padL, show clen Ws - (Ws k).length = 0 by rw [clen, hk]; omega, List.replicate_zero,
      List.nil_append]
  simp only [e]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, clen] at hp ⊢; rw [← hk]; exact hp)]
  simp

theorem conv_dec {w : List (Fin r → Option σ)} (hv : Valid w) (hna : ∀ c ∈ w, ∃ k, c k ≠ none) :
    conv (dec w) = w := by
  have hL : clen (dec w) = w.length := by
    apply le_antisymm (Finset.sup_le fun k _ => length_dec_le w k)
    cases hw : w with
    | nil => exact Nat.zero_le _
    | cons c w0 =>
      obtain ⟨k, hk⟩ := hna c (by rw [hw]; exact List.mem_cons_self)
      have he := (hv k).eq
      have hlen : (dec w k).length = w.length := by
        by_contra hcon
        have hlt : 0 < (tr w k).length - (tr w k).reduceOption.length := by
          have := length_dec_le w k
          rw [tr_length]
          simp only [dec] at hcon this
          omega
        have h0 := congrArg (fun l => l[0]?) he
        rw [List.getElem?_append_left (by simp only [List.length_replicate]; exact hlt),
          List.getElem?_replicate, ite_eq_left hlt] at h0
        simp only [tr, hw, List.map_cons, List.getElem?_cons_zero, Option.some_inj] at h0
        exact hk h0
      rw [← hw, ← hlen]
      exact le_clen (dec w) k
  apply eq_of_tr (by rw [length_conv, hL])
  intro k
  rw [tr_conv, hL, padL, (hv k).eq, tr_length]
  rfl

theorem exists_short_conv {S : Type*} [Fintype S] (f : List (Fin r → Option σ) → S)
    (hf : ∀ x y a, f x = f y → f (x ++ [a]) = f (y ++ [a])) (Ws : Fin r → List σ) :
    ∃ Ws' : Fin r → List σ, (∀ k, (Ws' k).Sublist (Ws k)) ∧
      (∀ k, (Ws' k).length < Fintype.card S) ∧ f (conv Ws') = f (conv Ws) := by
  obtain ⟨w', hs, hl, he⟩ := exists_short_of_congr f hf (conv Ws)
  have hv : Valid w' := (valid_conv Ws).sublist hs
  have hna : ∀ c ∈ w', ∃ k, c k ≠ none := fun c hc => conv_noPad Ws c (hs.subset hc)
  refine ⟨dec w', fun k => ?_, fun k => (length_dec_le w' k).trans_lt hl, ?_⟩
  · have := dec_sublist hs k
    rwa [dec_conv] at this
  · rw [conv_dec hv hna, he]

end ColumnEncoding

section Summary
variable {σ : Type*} {r : ℕ}

theorem dec_eq_nil_of_pad {w : List (Fin r → Option σ)} {c : Fin r → Option σ}
    (hv : Valid (w ++ [c])) (k : Fin r) (hk : c k = none) : dec w k = [] := by
  obtain ⟨a, P, hP⟩ := hv k
  have htr : tr (w ++ [c]) k = tr w k ++ [none] := by
    simp only [tr, List.map_append, List.map_singleton, hk]
  rw [htr] at hP
  rcases List.eq_nil_or_concat' P with rfl | ⟨P0, z, rfl⟩
  · have hd := congrArg List.reduceOption hP
    rw [reduceOption_pad, List.reduceOption_append, List.reduceOption_singleton,
      Option.toList_none, List.append_nil] at hd
    exact hd
  · rw [List.map_append, ← List.append_assoc] at hP
    obtain ⟨-, e⟩ := List.append_inj' hP rfl
    simp at e

end Summary

section Decide
variable {Q : Type*}

/-- Enumerate words of length at most n whose letters lie in the given finite set. -/
def boundedLists {α : Type*} [DecidableEq α] (S : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n + 1 => insert [] ((S ×ˢ boundedLists S n).image fun p => p.1 :: p.2)

theorem mem_boundedLists {α : Type*} [DecidableEq α] (S : Finset α) (n : ℕ) (l : List α) :
    l ∈ boundedLists S n ↔ l.length ≤ n ∧ ∀ x ∈ l, x ∈ S := by
  induction n generalizing l with
  | zero =>
    simp only [boundedLists, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]
    constructor
    · rintro rfl; simp
    · exact fun h => h.1
  | succ n ih =>
    cases l with
    | nil => simp [boundedLists]
    | cons a l =>
      simp only [boundedLists, Finset.mem_insert, reduceCtorEq, false_or, Finset.mem_image,
        Finset.mem_product, Prod.exists, List.cons.injEq, List.length_cons, List.mem_cons,
        forall_eq_or_imp]
      constructor
      · rintro ⟨b, l', ⟨hb, hl'⟩, rfl, rfl⟩
        have := (ih l').mp hl'
        exact ⟨by omega, hb, this.2⟩
      · rintro ⟨hlen, ha, hl⟩
        exact ⟨a, l, ⟨ha, (ih l).mpr ⟨by omega, hl⟩⟩, rfl, rfl⟩

theorem absHoleG_iff_bounded {α : Type*} (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q)
    (w : List α) :
    IsReaderHole M R T w ↔ runPrefix M w w.length ∈ T ∧
      ∀ s ∈ Finset.range (w.length + 1), ∀ e ∈ Finset.range (w.length + 1), s < e →
        w.drop e <+: w.drop s → ¬ R (runPrefix M w s) (runPrefix M w e) := by
  unfold IsReaderHole WitnessedPair
  constructor
  · rintro ⟨hT, hW⟩
    refine ⟨hT, fun s _ e he hse hc => hW _ _ ⟨s, e, hse, ?_, rfl, rfl, hc⟩⟩
    rw [Finset.mem_range] at he
    omega
  · rintro ⟨hT, hB⟩
    refine ⟨hT, ?_⟩
    rintro p q ⟨s, e, hse, hel, rfl, rfl, hc⟩
    exact hB s (Finset.mem_range.mpr (by omega)) e (Finset.mem_range.mpr (by omega)) hse hc

instance decHole {α : Type*} [DecidableEq α] (M : DFA α Q) (R : Q → Q → Prop) [DecidableRel R]
    (T : Set Q) [DecidablePred (· ∈ T)] (w : List α) : Decidable (IsReaderHole M R T w) :=
  decidable_of_iff _ (absHoleG_iff_bounded M R T w).symm

end Decide

end DeciNSSE.Packets
