import DeciNSSE.Complexity.Tiling.Backbones

/-! # Holes of the backbone construction

## Main declarations

- `Emitter.left_hole` computes the left-hole language with a copy compatibility test.
- `Emitter.right_clear` excludes right holes for each copy.
- `Emitter.polarized` provides a finite solution, including after signing.
-/

namespace DeciNSSE.Complexity.Tiling.Emitter
open Monitor Events Holes CoAlignment SignDuality
open scoped List
variable {n m : ℕ} (M : StoppingTable (Fin n)) {ψ : Constraint n (2*m)} {c : Fin n → Bool}

/-- In the emitted system each variable has bounds in at most one orientation. -/
theorem polarized : Polarized (system M) := by
  intro x hb ht
  rcases hb with ⟨a,ha⟩ | hb
  · rcases ht with ⟨b,hb⟩ | ht
    · exact separated M x b a hb ha
    · obtain ⟨_,rfl⟩ := (leaf_iff M ..).mp ht
      obtain ⟨q,he,_,_⟩ := (mem_leF M _ _).mp ha
      have := congrArg Fin.val he
      simp [u,top] at this; omega
  · exact Bool.noConfusion ((leaf_iff M ..).mp hb).1

private theorem imageU {d} (F : Track (system M) ψ c d) (sep : Separated ψ) (x z w) :
    UpperAt ψ w (F.var false x) z ↔
      ∃ y, Trace (system M) d w x y ∧ z = F.var (polarity c w) y := by
  rw [upper_trace sep, F.path_iff]; simp

private theorem imageL {d} (F : Track (system M) ψ c d) (sep : Separated ψ) (x z w) :
    LowerAt ψ w z (F.var false x) ↔
      ∃ y, Trace (system M) (!d) w x y ∧ z = F.var (polarity c w) y := by
  rw [lower_trace sep, F.path_iff]; simp

private theorem left_images (F : Track (system M) ψ c false) (sep : Separated ψ)
    {w} (hw : ProperFree M w) :
    (∀ z, UpperAt ψ w (F.var false (u M M.start)) z ↔
      ∃ y ∈ upperMask M w, z = F.var (polarity c w) y) ∧
    (∀ z, LowerAt ψ w z (F.var false (l M M.start)) ↔
      ∃ y ∈ lower M (M.dfa.eval w), z = F.var (polarity c w) y) := by
  obtain ⟨hu,hl⟩ := masks M w hw
  simp only [imageU M F sep, imageL M F sep, Bool.not_false, hu, hl, implies_true, and_self]

private theorem no_ready (F : Track (system M) ψ c false) (sep : Separated ψ)
    {w} (hw : ProperFree M w) :
    ¬ ReadyAt ψ (F.var false (u M M.start)) (F.var false (l M M.start)) w := by
  obtain ⟨hu,hl⟩ := left_images M F sep hw
  rintro (⟨z,hz,hb⟩ | ⟨z,hz,ht⟩ | ⟨z,h₁,h₂⟩)
  · obtain ⟨v,_,rfl⟩ := (hu z).mp hz
    exact Bool.noConfusion ((leaf_iff M ..).mp ((F.leaf false _ v).mp hb)).1
  · obtain ⟨v,hv,rfl⟩ := (hl z).mp hz
    obtain ⟨_,rfl⟩ := (leaf_iff M ..).mp ((F.leaf true _ v).mp ht)
    exact top_not_lower M _ hv
  · obtain ⟨a,ha,rfl⟩ := (hu _).mp h₁
    obtain ⟨b,hb,he⟩ := (hl _).mp h₂
    obtain ⟨_,rfl⟩ := (F.eq ..).mp he
    cases w with
    | nil =>
      have hq : a = u M M.start := by simpa [upperMask] using ha
      subst a; simp [lower,marker,StoppingTable.dfa,Ne.symm (l_ne_u M M.start M.start)] at hb
    | cons i w =>
      apply M.irrefl (M.dfa.eval (i :: w))
      exact (meet_iff M ..).mp ⟨a,hb,by simpa [upperMask] using ha⟩

private theorem child_iff (hn : 0 < n) (F : Track (system M) ψ c false) (sep : Separated ψ)
    {w} (hw : ProperFree M w) :
    ChildAt ψ (F.var false (u M M.start)) w ↔ M.dfa.eval w ∉ M.target := by
  have hcrit (z) :
      (∃ b, Lit.leF (F.var (polarity c w) z) b ∈ ψ) ↔ ∃ q, z = u M q ∧ q ∉ M.target :=
    (F.has_node false _ z).trans (upper_node M hn z)
  constructor
  · rintro ⟨z,hz,child⟩
    obtain ⟨v,hv,rfl⟩ := ((left_images M F sep hw).1 _).mp hz
    obtain ⟨q,rfl,_⟩ := (hcrit _).mp child
    exact ((active_upper M w q).mp hv).2
  · intro ht
    exact ⟨_,((left_images M F sep hw).1 _).mpr ⟨_,(active_upper M w _).mpr ⟨rfl,ht⟩,rfl⟩,
      (hcrit _).mpr ⟨_,rfl,ht⟩⟩

private theorem admission_iff (F : Track (system M) ψ c false) (sep : Separated ψ)
    {a b} (ha : ProperFree M a) (hb : ProperFree M b) (hne : b ≠ []) :
    ((∃ z, LowerAt ψ a z (F.var false (l M M.start)) ∧
        UpperAt ψ b (F.var false (u M M.start)) z) ∨
      ∃ z, UpperAt ψ a (F.var false (u M M.start)) z ∧
        UpperAt ψ b (F.var false (u M M.start)) (flipV z)) ↔
      F.compatible (polarity c a) (polarity c b) ∧ (M.dfa.eval a,M.dfa.eval b) ∈ M.pairs := by
  obtain ⟨ua,la⟩ := left_images M F sep ha
  obtain ⟨ub,_⟩ := left_images M F sep hb
  simp only [upperMask, ite_eq_right hne] at ub
  constructor
  · rintro (⟨z,h₁,h₂⟩ | ⟨z,h₁,h₂⟩)
    · obtain ⟨x,hx,rfl⟩ := (la _).mp h₁
      obtain ⟨y,hy,he⟩ := (ub _).mp h₂
      obtain ⟨hc,rfl⟩ := (F.eq ..).mp he
      exact ⟨hc,(meet_iff M ..).mp ⟨x,hx,hy⟩⟩
    · obtain ⟨x,_,rfl⟩ := (ua _).mp h₁
      obtain ⟨y,_,he⟩ := (ub _).mp h₂
      exact (F.noFlip _ _ _ _ he).elim
  · rintro ⟨hc,hm⟩
    obtain ⟨x,hx,hy⟩ := (meet_iff M ..).mpr hm
    exact Or.inl ⟨_,(la _).mpr ⟨x,hx,rfl⟩,(ub _).mpr ⟨x,hy,(F.eq ..).mpr ⟨hc,rfl⟩⟩⟩

private theorem occurs_after_target {d} (F : Track (system M) ψ c d) (sep : Separated ψ)
    {w} (bad : ¬ ProperFree M w) :
    Occurs ψ (F.var false (if d then l M M.start else u M M.start))
      (F.var false (if d then u M M.start else l M M.start)) w := by
  obtain ⟨p,a,hp,ht,pref⟩ := first_target M bad
  have trace := reaches_top M hp ht a
  let z := F.var (polarity c (p ++ [a])) (top M)
  refine Or.inl ⟨_,pref.length_le,?_⟩
  rw [← List.prefix_iff_eq_take.mp pref]
  cases d with
  | false =>
    exact Or.inr (Or.inl ⟨z,(imageL M F sep ..).mpr ⟨_,trace,rfl⟩,
      (F.leaf true _ _).mpr ((leaf_iff M ..).mpr ⟨rfl,rfl⟩)⟩)
  | true =>
    exact Or.inl ⟨z,(imageU M F sep ..).mpr ⟨_,trace,rfl⟩,
      (F.leaf false _ _).mpr ((leaf_iff M ..).mpr ⟨rfl,rfl⟩)⟩

/-- A left hole reaches a table target and avoids every admitted comparison whose cuts have
compatible copy signs. -/
theorem left_hole (hn : 0 < n) (F : Track (system M) ψ c false) (sep : Separated ψ)
    (w : List (Fin n)) :
    IsReaderHole (reader ψ (F.var false (u M M.start)) (F.var false (l M M.start)))
      admission (target ψ) w ↔
      M.dfa.eval w ∈ M.target ∧ ∀ s e, IsComp w s e →
        F.compatible (polarity c (w.take s)) (polarity c (w.take e)) →
        (M.dfa.eval (w.take s),M.dfa.eval (w.take e)) ∉ M.pairs := by
  classical
  rw [Monitor.hole_iff_not_occurs]
  by_cases free : ProperFree M w
  · have ready := fun i => no_ready M F sep (free_take M free i)
    have child := child_iff M hn F sep free
    have pair (s e : ℕ) (h : IsComp w s e) := admission_iff M F sep
      (free_take M free s) (free_take M free e) (by simp [List.take_eq_nil_iff]; have := h.1
                                                    have := h.2.1; grind)
    constructor
    · intro h
      refine ⟨Classical.not_not.mp (fun nt => h (Or.inr (Or.inl (child.mpr nt)))),?_⟩
      exact fun s e hc compat rel =>
        h (Or.inr (Or.inr ⟨s,e,hc.1,hc.2.1,hc.2.2,(pair _ _ hc).mpr ⟨compat,rel⟩⟩))
    · rintro ⟨ht,clear⟩ (⟨i,_,hr⟩ | hc | ⟨s,e,hs,he,hp,hr⟩)
      · exact ready i hr
      · exact child.mp hc ht
      · have comp : IsComp w s e := ⟨hs,he,hp⟩
        obtain ⟨compat,rel⟩ := (pair s e comp).mp hr
        exact clear _ _ comp compat rel
  · have occ := occurs_after_target M F sep free
    exact ⟨fun h => (h occ).elim, fun h => (free (free_of_target M h.1)).elim⟩

/-- At positive arity the right track of the emitted system has no reader hole. -/
theorem right_clear (hn : 0 < n) (F : Track (system M) ψ c true) (sep : Separated ψ)
    (w : List (Fin n)) : ¬ IsReaderHole
      (reader ψ (F.var false (l M M.start)) (F.var false (u M M.start)))
      admission (target ψ) w := by
  rw [Monitor.hole_iff_not_occurs]
  apply not_not_intro
  by_cases free : ProperFree M w
  · apply Or.inr (Or.inl _)
    refine ⟨F.var (polarity c w) (l M (M.dfa.eval w)),
      (imageU M F sep ..).mpr ⟨_,?_,rfl⟩,?_⟩
    · exact ((masks M w free).2 _).mpr ((l_mem_lower M ..).mpr rfl)
    · exact (F.has_node false _ _).mpr (lower_node M hn _)
  · exact occurs_after_target M F sep free

end DeciNSSE.Complexity.Tiling.Emitter
