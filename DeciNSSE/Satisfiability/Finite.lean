import DeciNSSE.Satisfiability.Cycle
import DeciNSSE.Satisfiability.LeastShape

/-! # Finite covariant satisfiability

Finite solutions exist exactly when there are neither label nor cycle clashes.
Repeated pairs of path endpoints bound the depth of the least-shape solution.
-/

namespace DeciNSSE

variable {n k : ℕ} {ϕ : Constraint n k}

namespace FiniteSat

/-- Chains include every interval, so singleton steps and prefix judgments
are immediate instances. Only indices through `π.length` are used. -/
def PathChain {α : Type*} (R : List (Fin n) → α → α → Prop)
    (π : List (Fin n)) (z x : α) : Prop :=
  ∃ w : ℕ → α, w 0 = z ∧ w π.length = x ∧
    ∀ i j, i ≤ j → j ≤ π.length → R ((π.take j).drop i) (w i) (w j)

/-- At length zero a path judgment need not equate its endpoints; exact
endpoint chains therefore require a nonempty path. -/
theorem pathChain_of_nonempty {α : Type*} (R : List (Fin n) → α → α → Prop)
    (hrefl : ∀ x, R [] x x)
    (hcomp : ∀ {π τ x y z}, R π x y → R τ y z → R (π ++ τ) x z)
    (hfactor : ∀ {π τ x z}, R (π ++ τ) x z → ∃ y, R π x y ∧ R τ y z)
    {π : List (Fin n)} {z x : α} (hπ : π ≠ []) (h : R π z x) :
    PathChain R π z x := by
  induction π generalizing z with
  | nil => exact False.elim (hπ rfl)
  | cons a π ih =>
    cases π with
    | nil =>
      refine ⟨fun m => if m = 0 then z else x, by simp, by simp, ?_⟩
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
      refine ⟨fun m => match m with | 0 => z | m + 1 => w m,
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

theorem LowerAt.chain {π : List (Fin n)} {x z : V k}
    (h : LowerAt ϕ π x z) (hπ : π ≠ []) :
    FiniteSat.PathChain (fun τ u v => LowerAt ϕ τ v u) π z x :=
  FiniteSat.pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₂.comp h₁) (fun hp => hp.factor) hπ h

theorem UpperAt.chain {π : List (Fin n)} {z y : V k}
    (h : UpperAt ϕ π z y) (hπ : π ≠ []) :
    FiniteSat.PathChain (UpperAt ϕ) π z y :=
  FiniteSat.pathChain_of_nonempty _ (fun u => .nil (.refl u))
    (fun h₁ h₂ => h₁.comp h₂) (fun hp => hp.factor) hπ h

/-- Use just the first `k*k+1` positions, ensuring that the repeated
pair encloses a nonempty path of length at most `k*k`. -/
theorem cycleClash_bounded_of_long_path (π : List (Fin n)) (x y z : V k)
    (hl : LowerAt ϕ π x z) (hu : UpperAt ϕ π z y) (hlen : k * k < π.length) :
    ∃ ρ x' y', 0 < ρ.length ∧ ρ.length ≤ k * k ∧
      LowerAt ϕ ρ x' x' ∧ Derives ϕ x' y' ∧ UpperAt ϕ ρ y' y' := by
  have hπ : π ≠ [] := by intro he; simp [he] at hlen
  obtain ⟨w, hw0, _, hw⟩ := hl.chain hπ
  obtain ⟨v, hv0, _, hv⟩ := hu.chain hπ
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun m : Fin (k * k + 1) => (w m.val, v m.val)) (by simp [V])
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

/-- A domain path beyond the proposed depth bound already supplies a
bounded cycle witness; no label-clash assumption is needed. -/
theorem leastShape_bounded_cycle_of_long_path {z : V k} {π : List (Fin n)}
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
  obtain ⟨a, x, _, hx⟩ := hl
  obtain ⟨y, b, _, hy⟩ := hu
  exact cycleClash_bounded_of_long_path τ x y z hx hy (by omega)

/-- Without cycle clashes, every least-shape domain path has bounded length. -/
theorem leastShape_depth (hn : ¬ CycleClash ϕ) (z : V k) (π : List (Fin n))
    (hdom : ((leastShape ϕ z).fn π).isSome) : π.length ≤ k * k + 1 := by
  by_contra hlen
  obtain ⟨ρ, x, y, hp, _, hl, hd, hu⟩ :=
    leastShape_bounded_cycle_of_long_path hdom (by omega)
  exact hn ⟨ρ, x, y, List.length_pos_iff.mp hp, hl, hd, hu⟩

namespace FTree

/-- Read at most `d` edges of a tree. A constructor root at depth zero becomes
`f(top, …, top)`: exact at arity zero, and never used at positive arity under
the depth hypothesis of `toTree_ofTree`. -/
def ofTree : ℕ → Tree n → FTree n
  | 0, t => match t.fn [] with
    | some .bot => .bot
    | some .f => .node fun _ => .top
    | _ => .top
  | d + 1, t =>
    if h : t.fn [] = some .f then
      .node fun i => ofTree d (t.branch i h)
    else match t.fn [] with
      | some .bot => .bot
      | _ => .top

/-- Bounded-depth path trees are exactly represented by finite trees. -/
theorem toTree_ofTree {d : ℕ} {t : Tree n}
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
        have hc : ∀ i, (Tree.top : Tree n) = t.branch i hr := fun i => by
          have hd := hdepth [i] ((t.child_isSome_iff [] i).mpr hr)
          simp at hd
        calc (ofTree 0 t).toTree = Tree.node fun _ => Tree.top := by
                simp [ofTree, hr]
          _ = Tree.node fun i => t.branch i hr := by
                congr 1
                funext i
                exact hc i
          _ = t := (t.eq_node_of_root_eq_f hr).symm
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
        have hb (i : Fin n) : ∀ π, ((t.branch i hr).fn π).isSome → π.length ≤ d := by
          intro π hp
          have hd := hdepth (i :: π) hp
          simp only [List.length_cons] at hd
          omega
        have hc : ∀ i, (ofTree d (t.branch i hr)).toTree = t.branch i hr :=
          fun i => ih (hb i)
        simp only [ofTree, dite_eq_left hr, toTree_node, hc]
        exact (t.eq_node_of_root_eq_f hr).symm

end FTree

/-- A uniform depth bound turns the least-shape assignment into a finite solution. -/
theorem satFin_of_leastShape_depth (hn : ¬ LabelClash ϕ)
    (hd : ∀ z π, ((leastShape ϕ z).fn π).isSome → π.length ≤ k * k + 1) :
    ∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ := by
  let σ := fun z => FTree.ofTree (k * k + 1) (leastShape ϕ z)
  have hσ : FTree.toTree ∘ σ = leastShape ϕ := by
    funext z
    exact FTree.toTree_ofTree (hd z)
  exact ⟨σ, hσ.symm ▸ leastShape_sat hn⟩

/-- Finite satisfiability is equivalent to the absence of label and cycle clashes. -/
theorem satFin_iff : (∃ σ : V k → FTree n, Covariant.Sat (FTree.toTree ∘ σ) ϕ) ↔
    ¬ LabelClash ϕ ∧ ¬ CycleClash ϕ := by
  constructor
  · intro hfin
    obtain ⟨σ, hσ⟩ := hfin
    exact ⟨fun hl => hl.unsatisfiable ⟨FTree.toTree ∘ σ, hσ⟩,
      fun hc => hc.no_finite_solution ⟨σ, hσ⟩⟩
  · rintro ⟨hl, hc⟩
    exact satFin_of_leastShape_depth hl (leastShape_depth hc)

/-- Without a label clash, every cycle clash has a witness of length
between one and the number of variable pairs. -/
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
