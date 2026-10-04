import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.IntervalCases
import DeciNSSE.Satisfiability.LeastShape
import DeciNSSE.Satisfiability.Cycle

/-! # Characterisation of finite satisfiability

Long paths yield bounded cycle clashes. Without label or cycle clashes the
least-shape solution has bounded depth and can be represented by finite trees.
-/

namespace DeciNSSE

variable {k : ℕ} {ϕ : Constraint k}

theorem LowerAt.comp {π π' : List (Fin 2)} {x w z : V k}
    (h' : LowerAt ϕ π' x w) (h : LowerAt ϕ π w z) :
    LowerAt ϕ (π ++ π') x z := by
  induction h with
  | nil hd => exact h'.trans_right hd
  | cons hl hd _ ih => exact .cons hl hd (ih h')

theorem UpperAt.comp {π π' : List (Fin 2)} {z w y : V k}
    (h : UpperAt ϕ π z w) (h' : UpperAt ϕ π' w y) :
    UpperAt ϕ (π ++ π') z y := by
  induction h with
  | nil hd => exact UpperAt.trans_left hd h'
  | cons hd hl _ ih => exact .cons hd hl (ih h')

theorem LowerAt.factor {π π' : List (Fin 2)} {x z : V k}
    (h : LowerAt ϕ (π ++ π') x z) :
    ∃ w, LowerAt ϕ π w z ∧ LowerAt ϕ π' x w := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hl hd hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hl hd hw, hw'⟩

theorem UpperAt.factor {π π' : List (Fin 2)} {z y : V k}
    (h : UpperAt ϕ (π ++ π') z y) :
    ∃ w, UpperAt ϕ π z w ∧ UpperAt ϕ π' w y := by
  induction π generalizing z with
  | nil => exact ⟨z, .nil (.refl z), h⟩
  | cons i π ih =>
    cases h with
    | cons hd hl hp =>
      obtain ⟨w, hw, hw'⟩ := ih hp
      exact ⟨w, .cons hd hl hw, hw'⟩

namespace FiniteSat

def PathChain {α : Type*} (R : List (Fin 2) → α → α → Prop)
    (π : List (Fin 2)) (z x : α) : Prop :=
  ∃ w : ℕ → α, w 0 = z ∧ w π.length = x ∧
    ∀ i j, i ≤ j → j ≤ π.length → R ((π.take j).drop i) (w i) (w j)

theorem pathChain_of_nonempty {α : Type*} (R : List (Fin 2) → α → α → Prop)
    (hrefl : ∀ x, R [] x x)
    (hcomp : ∀ {π τ x y z}, R π x y → R τ y z → R (π ++ τ) x z)
    (hfactor : ∀ {π τ x z}, R (π ++ τ) x z → ∃ y, R π x y ∧ R τ y z)
    {π : List (Fin 2)} {z x : α} (hπ : π ≠ []) (h : R π z x) :
    PathChain R π z x := by
  induction π generalizing z with
  | nil => exact False.elim (hπ rfl)
  | cons a π ih =>
    cases π with
    | nil =>
      refine ⟨fun n => if n = 0 then z else x, by simp, by simp, ?_⟩
      intro i j hij hj
      have hj' : j ≤ 1 := by simpa using hj
      interval_cases j
      · have hi : i = 0 := by omega
        simpa [hi] using hrefl z
      · interval_cases i
        · simpa using h
        · simpa using hrefl x
    | cons b π =>
      obtain ⟨q, hq, ht⟩ := hfactor (π := [a]) (τ := b :: π) h
      obtain ⟨w, hw0, hwn, hw⟩ := ih (by simp) ht
      refine ⟨fun n => match n with | 0 => z | n + 1 => w n,
        rfl, hwn, ?_⟩
      intro i j hij hj
      cases j with
      | zero =>
        have hi : i = 0 := by omega
        simpa [hi] using hrefl z
      | succ j =>
        have hj' : j ≤ (b :: π).length := by simpa using hj
        cases i with
        | zero =>
          have hp := hw 0 j (Nat.zero_le j) hj'
          simp only [List.drop_zero, hw0] at hp
          simpa using hcomp hq hp
        | succ i =>
          simpa using hw i j (by omega) hj'

end FiniteSat

theorem LowerAt.chain {π : List (Fin 2)} {x z : V k}
    (h : LowerAt ϕ π x z) (hπ : π ≠ []) :
    FiniteSat.PathChain (fun τ u v => LowerAt ϕ τ v u) π z x :=
  FiniteSat.pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₂.comp h₁) (fun hp => hp.factor) hπ h

theorem UpperAt.chain {π : List (Fin 2)} {z y : V k}
    (h : UpperAt ϕ π z y) (hπ : π ≠ []) :
    FiniteSat.PathChain (UpperAt ϕ) π z y :=
  FiniteSat.pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₁.comp h₂) (fun hp => hp.factor) hπ h

theorem cycleClash_bounded_of_long_path (π : List (Fin 2)) (x y z : V k)
    (hl : LowerAt ϕ π x z) (hu : UpperAt ϕ π z y) (hlen : k * k < π.length) :
    ∃ ρ x' y', 0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x' x' ∧ Derives ϕ x' y' ∧ UpperAt ϕ ρ y' y' := by
  have hπ : π ≠ [] := by intro he; simp [he] at hlen
  obtain ⟨w, hw0, _, hw⟩ := hl.chain hπ
  obtain ⟨v, hv0, _, hv⟩ := hu.chain hπ
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun n : Fin (k * k + 1) => (w n.val, v n.val)) (by simp [V])
  have hpair : ∃ i j : Fin (k * k + 1), i < j ∧
      (w i.val, v i.val) = (w j.val, v j.val) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ⟨i, j, hij, he⟩
    · exact ⟨j, i, hji, he.symm⟩
  obtain ⟨i, j, hij, he⟩ := hpair
  have hij' : i.val < j.val := hij
  have hj : j.val ≤ π.length := by omega
  have hi : i.val ≤ π.length := by omega
  have hw_eq : w i.val = w j.val := congrArg Prod.fst he
  have hv_eq : v i.val = v j.val := congrArg Prod.snd he
  let ρ := (π.take j.val).drop i.val
  have hρ : ρ.length = j.val - i.val := by
    simp [ρ, List.length_take, Nat.min_eq_left hj]
  have hlp : LowerAt ϕ (π.take i.val) (w i.val) z := by
    simpa [hw0] using hw 0 i.val (Nat.zero_le _) hi
  have hup : UpperAt ϕ (π.take i.val) z (v i.val) := by
    simpa [hv0] using hv 0 i.val (Nat.zero_le _) hi
  refine ⟨ρ, w i.val, v i.val, by omega, by omega, ?_, ?_, ?_⟩
  · simpa only [← hw_eq] using hw i.val j.val (by omega) hj
  · exact upperAt_nil_iff.mp (hlp.decompose_upper (π' := []) (by simpa using hup))
  · simpa only [← hv_eq] using hv i.val j.val (by omega) hj

theorem leastShape_bounded_cycle_of_long_path {z : V k} {π : List (Fin 2)}
    (hdom : ((leastShape ϕ z).fn π).isSome) (hlen : k * k + 1 < π.length) :
    ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x x ∧ Derives ϕ x y ∧ UpperAt ϕ ρ y y := by
  let τ := π.take (k * k + 1)
  have hτ : τ.length = k * k + 1 := by
    simp [τ, Nat.min_eq_left (show k * k + 1 ≤ π.length by omega)]
  have hprefix : τ <+: π := ⟨π.drop (k * k + 1), List.take_append_drop _ _⟩
  have hne : τ ≠ π := by intro he; have := congrArg List.length he; omega
  have hf := (leastShape ϕ z).label_eq_f_of_proper_prefix hprefix hne hdom
  obtain ⟨hl, hu⟩ := shapeLabel_eq_f_iff.mp (leastShape_label_eq hf).symm
  obtain ⟨x, x₁, x₂, _, hx⟩ := hl
  obtain ⟨y, y₁, y₂, _, hy⟩ := hu
  exact cycleClash_bounded_of_long_path τ x y z hx hy (by omega)

theorem leastShape_depth (hn : ¬ CycleClash ϕ) (z : V k) (π : List (Fin 2))
    (hdom : ((leastShape ϕ z).fn π).isSome) : π.length ≤ k * k + 1 := by
  by_contra hlen
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ :=
    leastShape_bounded_cycle_of_long_path hdom (by omega)
  exact hn ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩

namespace FTree

def ofTree : ℕ → Tree → FTree
  | 0, t => match t.fn [] with
    | some .bot => .bot
    | _ => .top
  | d + 1, t =>
    if h : t.fn [] = some .f then
      .node (ofTree d (t.branch 0 h)) (ofTree d (t.branch 1 h))
    else match t.fn [] with
      | some .bot => .bot
      | _ => .top

theorem toTree_ofTree {d : ℕ} {t : Tree}
    (hdepth : ∀ π, (t.fn π).isSome → π.length ≤ d) : (ofTree d t).toTree = t := by
  induction d generalizing t with
  | zero =>
    cases hr : t.fn [] with
    | none => exact False.elim (t.wf.1 hr)
    | some a =>
      cases a with
      | bot =>
        simpa [ofTree, hr, toTree] using ((Tree.root_eq_bot_iff t).mp hr).symm
      | top =>
        simpa [ofTree, hr, toTree] using ((Tree.root_eq_top_iff t).mp hr).symm
      | f =>
        have hd := hdepth [0] ((t.child_isSome_iff [] 0).mpr hr)
        simp at hd
  | succ d ih =>
    cases hr : t.fn [] with
    | none => exact False.elim (t.wf.1 hr)
    | some a =>
      cases a with
      | bot =>
        simpa [ofTree, hr, toTree] using ((Tree.root_eq_bot_iff t).mp hr).symm
      | top =>
        simpa [ofTree, hr, toTree] using ((Tree.root_eq_top_iff t).mp hr).symm
      | f =>
        have hb (i : Fin 2) : ∀ π, ((t.branch i hr).fn π).isSome → π.length ≤ d := by
          intro π hp
          have hd := hdepth (i :: π) hp
          simp only [List.length_cons] at hd
          omega
        simp only [ofTree, dite_eq_left hr, toTree]
        rw [ih (hb 0), ih (hb 1)]
        exact (t.eq_node_of_root_eq_f hr).symm

end FTree

theorem satFin_of_leastShape_depth (hn : ¬ LabelClash ϕ)
    (hd : ∀ z π, ((leastShape ϕ z).fn π).isSome → π.length ≤ k * k + 1) :
    ∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ := by
  let σ := fun z => FTree.ofTree (k * k + 1) (leastShape ϕ z)
  have hσ : FTree.toTree ∘ σ = leastShape ϕ := by
    funext z
    exact FTree.toTree_ofTree (hd z)
  exact ⟨σ, hσ.symm ▸ leastShape_sat hn⟩

theorem satFin_iff : (∃ σ : V k → FTree, Sat (FTree.toTree ∘ σ) ϕ) ↔
    ¬ LabelClash ϕ ∧ ¬ CycleClash ϕ := by
  constructor
  · intro hfin
    obtain ⟨σ, hσ⟩ := hfin
    exact ⟨fun hl => hl.unsatisfiable ⟨FTree.toTree ∘ σ, hσ⟩,
      fun hc => hc.no_finite_solution ⟨σ, hσ⟩⟩
  · rintro ⟨hl, hc⟩
    exact satFin_of_leastShape_depth hl (leastShape_depth hc)

theorem cycleClash_iff_bounded (hn : ¬ LabelClash ϕ) :
    CycleClash ϕ ↔ ∃ ρ x y, 0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x x ∧ Derives ϕ x y ∧ UpperAt ϕ ρ y y := by
  constructor
  · intro hc
    by_contra hbounded
    apply hc.no_finite_solution
    apply satFin_of_leastShape_depth hn
    intro z π hdom
    by_contra hlen
    exact hbounded (leastShape_bounded_cycle_of_long_path hdom (by omega))
  · rintro ⟨ρ, x, y, hp, _, hl, hd, hu⟩
    exact ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩

end DeciNSSE
