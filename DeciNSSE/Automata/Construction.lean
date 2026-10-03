import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import DeciNSSE.Automata.CapAutomaton

/-! # The two constraint automata

Pairs of variables track upper and lower path bounds. The two choices of
final states and periodic edges recognise the left and right safety conditions.
-/

namespace DeciNSSE

inductive Side | l | r
  deriving DecidableEq, Repr

inductive CState (k : ℕ) where
  | pair (s s' : Option (V k))
  | all
  deriving DecidableEq, Repr, Fintype

namespace Construction

open CState

variable {k : ℕ} {ϕ : Constraint k}

theorem upperAt_singleton_iff (i : Fin 2) (u v : V k) :
    UpperAt ϕ [i] u v ↔ ∃ z a b, Derives ϕ u z ∧ Lit.leF z a b ∈ ϕ ∧
      Derives ϕ (if i = 0 then a else b) v := by
  constructor
  · intro h; cases h with | cons hd hl hp => exact ⟨_, _, _, hd, hl, upperAt_nil_iff.mp hp⟩
  · rintro ⟨z, a, b, hd, hl, hp⟩; exact .cons hd hl (.nil hp)

theorem lowerAt_singleton_iff (i : Fin 2) (v u : V k) :
    LowerAt ϕ [i] v u ↔ ∃ z a b, Lit.fLe a b z ∈ ϕ ∧ Derives ϕ z u ∧
      Derives ϕ v (if i = 0 then a else b) := by
  constructor
  · intro h; cases h with | cons hl hd hp => exact ⟨_, _, _, hl, hd, lowerAt_nil_iff.mp hp⟩
  · rintro ⟨z, a, b, hl, hd, hp⟩; exact .cons hl hd (.nil hp)

inductive Move (ϕ : Constraint k) (i : Fin 2) : CState k → CState k → Prop where

  | descend_left {u u' : V k} {s : Option (V k)} : UpperAt ϕ [i] u u' →
      Move ϕ i (pair (some u) s) (pair (some u') none)

  | descend_right {v v' : V k} {s : Option (V k)} : LowerAt ϕ [i] v' v →
      Move ϕ i (pair s (some v)) (pair none (some v'))

  | descend_both {u u' v v' : V k} : UpperAt ϕ [i] u u' → LowerAt ϕ [i] v' v →
      Move ϕ i (pair (some u) (some v)) (pair (some u') (some v'))

  | bot {u w : V k} {s : Option (V k)} : Derives ϕ u w → Lit.eqBot w ∈ ϕ →
      Move ϕ i (pair (some u) s) all

  | top {v w : V k} {s : Option (V k)} : Derives ϕ w v → Lit.eqTop w ∈ ϕ →
      Move ϕ i (pair s (some v)) all

  | reflexivity {u v : V k} : Derives ϕ u v →
      Move ϕ i (pair (some u) (some v)) all

  | all : Move ϕ i all all

def moveB (ϕ : Constraint k) (i : Fin 2) : CState k → CState k → Bool
  | pair (some u) _, pair (some u') none => upperAtB ϕ [i] u u'
  | pair _ (some v), pair none (some v') => lowerAtB ϕ [i] v' v
  | pair (some u) (some v), pair (some u') (some v') =>
      upperAtB ϕ [i] u u' && lowerAtB ϕ [i] v' v
  | pair a b, all =>
      (match a with
       | some u => decide (∃ w, derivesB ϕ u w = true ∧ Lit.eqBot w ∈ ϕ)
       | none => false) ||
      (match b with
       | some v => decide (∃ w, derivesB ϕ w v = true ∧ Lit.eqTop w ∈ ϕ)
       | none => false) ||
      (match a, b with
       | some u, some v => derivesB ϕ u v
       | _, _ => false)
  | all, all => true
  | _, _ => false

theorem moveB_iff (ϕ : Constraint k) (i : Fin 2) (q r : CState k) :
    moveB ϕ i q r = true ↔ Move ϕ i q r := by
  constructor
  · cases q with
    | all => cases r <;> simp [moveB]; exact Move.all
    | pair a b =>
      cases r with
      | all =>
        cases a <;> cases b <;>
          simp only [moveB, Bool.or_eq_true, decide_eq_true_eq, derivesB_iff,
            Bool.false_eq_true, false_or, or_false] <;>
          first
          | exact False.elim
          | exact fun ⟨w, hd, hl⟩ => Move.bot hd hl
          | exact fun ⟨w, hd, hl⟩ => Move.top hd hl
          | exact fun h => by
              rcases h with ((⟨w, hd, hl⟩ | ⟨w, hd, hl⟩) | hd)
              · exact .bot hd hl
              · exact .top hd hl
              · exact .reflexivity hd
      | pair c d =>
        cases a <;> cases b <;> cases c <;> cases d <;>
          simp only [moveB, Bool.false_eq_true, Bool.and_eq_true, upperAtB_iff,
            lowerAtB_iff] <;>
          first | exact False.elim | exact Move.descend_left | exact Move.descend_right |
            exact fun ⟨hu, hl⟩ => Move.descend_both hu hl
  · intro h
    cases h with
    | descend_left h => simp [moveB, upperAtB_iff, h]
    | descend_right h => simp [moveB, lowerAtB_iff, h]
    | descend_both hu hl => simp [moveB, upperAtB_iff, lowerAtB_iff, hu, hl]
    | @bot u w s hd hl => cases s <;> simp [moveB, derivesB_iff] <;> aesop
    | @top v w s hd hl => cases s <;> simp [moveB, derivesB_iff] <;> aesop
    | reflexivity h => simp [moveB, derivesB_iff, h]
    | all => rfl

def childFinalB (ϕ : Constraint k) : Side → CState k → Bool
  | _, all => true
  | .l, pair (some u) _ => decide (∃ i v, upperAtB ϕ [i] u v = true)
  | .r, pair _ (some v) => decide (∃ i u, lowerAtB ϕ [i] u v = true)
  | _, _ => false

def finalB (ϕ : Constraint k) (θ : Side) (q : CState k) : Bool :=
  childFinalB ϕ θ q || moveB ϕ 0 q all

def pedgeB : Side → CState k → CState k → Bool
  | .l, pair (some u) _, pair (some _) (some u') => decide (u = u')
  | .r, pair _ (some v), pair (some v') (some _) => decide (v = v')
  | _, _, _ => false

end Construction

def construct {k : ℕ} (ϕ : Constraint k) (x y : V k) (θ : Side) :
    CapAutomaton (CState k) where

  init := .pair (some x) (some y)
  final := Construction.finalB ϕ θ
  step q i := Finset.univ.filter (fun r => Construction.moveB ϕ i q r = true)
  pedge := Construction.pedgeB θ

namespace Construction

open CState CapAutomaton Safety

variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {θ : Side}

@[simp] theorem mem_step_iff {q r : CState k} {i : Fin 2} :
    r ∈ (construct ϕ x y θ).step q i ↔ Move ϕ i q r := by
  simp [construct, moveB_iff]

def left : CState k → Option (V k)
  | pair a _ => a
  | all => none

def right : CState k → Option (V k)
  | pair _ b => b
  | all => none

theorem move_upper {q r : CState k} {i : Fin 2} {v : V k}
    (h : Move ϕ i q r) (hv : left r = some v) :
    ∃ u, left q = some u ∧ UpperAt ϕ [i] u v := by
  cases h <;> simp_all [left]

theorem move_lower {q r : CState k} {i : Fin 2} {v : V k}
    (h : Move ϕ i q r) (hv : right r = some v) :
    ∃ u, right q = some u ∧ LowerAt ϕ [i] v u := by
  cases h <;> simp_all [right]

theorem runs_upper {q r : CState k} {π : List (Fin 2)} {v : V k}
    (h : Runs (construct ϕ x y θ) q π r) (hv : left r = some v) :
    ∃ u, left q = some u ∧ UpperAt ϕ π u v := by
  induction h with
  | nil => exact ⟨v, hv, .nil (.refl _)⟩
  | cons hs _ ih =>
    obtain ⟨w, hw, hp⟩ := ih hv
    obtain ⟨u, hu, hi⟩ := move_upper (mem_step_iff.mp hs) hw
    exact ⟨u, hu, hi.comp hp⟩

theorem runs_lower {q r : CState k} {π : List (Fin 2)} {v : V k}
    (h : Runs (construct ϕ x y θ) q π r) (hv : right r = some v) :
    ∃ u, right q = some u ∧ LowerAt ϕ π v u := by
  induction h with
  | nil => exact ⟨v, hv, .nil (.refl _)⟩
  | cons hs _ ih =>
    obtain ⟨w, hw, hp⟩ := ih hv
    obtain ⟨u, hu, hi⟩ := move_lower (mem_step_iff.mp hs) hw
    exact ⟨u, hu, hp.comp hi⟩

theorem upperAt_run {π : List (Fin 2)} {u v : V k} (hn : π ≠ [])
    (h : UpperAt ϕ π u v) :
    Runs (construct ϕ x y θ) (pair (some u) none) π (pair (some v) none) := by
  induction π generalizing u with
  | nil => exact (hn rfl).elim
  | cons i π ih =>
    cases π with
    | nil => exact .cons (mem_step_iff.mpr (.descend_left h)) (.nil _)
    | cons j π =>
      obtain ⟨w, hw, hp⟩ := UpperAt.factor (π := [i]) h
      exact .cons (mem_step_iff.mpr (.descend_left hw)) (ih (by simp) hp)

theorem lowerAt_run {π : List (Fin 2)} {u v : V k} (hn : π ≠ [])
    (h : LowerAt ϕ π v u) :
    Runs (construct ϕ x y θ) (pair none (some u)) π (pair none (some v)) := by
  induction π generalizing u with
  | nil => exact (hn rfl).elim
  | cons i π ih =>
    cases π with
    | nil => exact .cons (mem_step_iff.mpr (.descend_right h)) (.nil _)
    | cons j π =>
      obtain ⟨w, hw, hp⟩ := LowerAt.factor (π := [i]) h
      exact .cons (mem_step_iff.mpr (.descend_right hw)) (ih (by simp) hp)

theorem runs_pair_iff_upperAt {π : List (Fin 2)} {u v : V k} (hn : π ≠ []) :
    (∃ s s', Runs (construct ϕ x y θ) (pair (some u) s) π (pair (some v) s')) ↔
      UpperAt ϕ π u v := by
  constructor
  · rintro ⟨s, s', h⟩
    obtain ⟨w, hw, hp⟩ := runs_upper h rfl
    have he : u = w := Option.some.inj hw
    exact he.symm ▸ hp
  · intro h; exact ⟨none, none, upperAt_run hn h⟩

theorem runs_pair_iff_lowerAt {π : List (Fin 2)} {u v : V k} (hn : π ≠ []) :
    (∃ s s', Runs (construct ϕ x y θ) (pair s (some u)) π (pair s' (some v))) ↔
      LowerAt ϕ π v u := by
  constructor
  · rintro ⟨s, s', h⟩
    obtain ⟨w, hw, hp⟩ := runs_lower h rfl
    have he : u = w := Option.some.inj hw
    exact he.symm ▸ hp
  · intro h; exact ⟨none, none, lowerAt_run hn h⟩

theorem all_run (π : List (Fin 2)) : Runs (construct ϕ x y θ) all π all := by
  induction π with
  | nil => exact .nil _
  | cons i π ih => exact .cons (mem_step_iff.mpr .all) ih

theorem trace_embed (filler t : Tree) (π : List (Fin 2)) :
    trace (PathBounds.embed filler π t) π = t := by
  induction π with
  | nil => rfl
  | cons i π ih => fin_cases i <;> simpa [PathBounds.embed] using ih

theorem upper_trace_le {π : List (Fin 2)} {u v : V k} {ρ : V k → Tree}
    (h : UpperAt ϕ π u v) (hs : Sat ρ ϕ) : trace (ρ u) π ≤ ρ v := by
  simpa only [trace_embed] using trace_mono (h.le_embed hs) π

theorem lower_le_trace {π : List (Fin 2)} {u v : V k} {ρ : V k → Tree}
    (h : LowerAt ϕ π v u) (hs : Sat ρ ϕ) : ρ v ≤ trace (ρ u) π := by
  simpa only [trace_embed] using trace_mono (h.embed_le hs) π

theorem upper_bound_proper_prefix {X Y U : Tree} {π τ : List (Fin 2)}
    (h : ∃ T : Tree, X ≤ T ∧ T.subtree π = some U)
    (hp : τ <+: π) (hne : τ ≠ π) :
    HasLabel X τ Sym.top → HasLabel Y τ Sym.top := by
  intro hx
  obtain ⟨T, hXT, hT⟩ := h
  have ht : trace T τ = Tree.top := (Tree.top_le_iff _).mp
    (by simpa [(trace_eq_top_iff _ _).mpr hx] using trace_mono hXT τ)
  obtain ⟨σ, hσ, hs⟩ := (trace_eq_top_iff _ _).mp ht
  have hσπ := hσ.trans hp
  have hne' : σ ≠ π := by
    intro he
    subst σ
    exact hne (hp.eq_of_length_le hσ.length_le)
  have hd := (Tree.subtree_isSome_iff T π).mp (by simp [hT])
  have hf := T.label_eq_f_of_proper_prefix hσπ hne' hd
  simp [hs] at hf

def Bounds (ρ : V k → Tree) (X Y : Tree) : CState k → Prop
  | pair a b => (∀ u, a = some u → X ≤ ρ u) ∧ (∀ v, b = some v → ρ v ≤ Y)
  | all => X ≤ Y

theorem move_to_all_bounds {ρ : V k → Tree} (hs : Sat ρ ϕ)
    {q : CState k} {i : Fin 2} (h : Move ϕ i q all) {X Y : Tree}
    (hb : Bounds ρ X Y q) : X ≤ Y := by
  cases h with
  | bot hd hl =>
    have he : X = Tree.bot := (Tree.le_bot_iff _).mp
      (le_trans (hb.1 _ rfl) (le_trans (hd.sound ρ hs) (le_of_eq (hs _ hl))))
    simp [he]
  | top hd hl =>
    have he : Y = Tree.top := (Tree.top_le_iff _).mp
      (le_trans (le_of_eq (hs _ hl).symm) (le_trans (hd.sound ρ hs) (hb.2 _ rfl)))
    simp [he]
  | reflexivity hd =>
    exact le_trans (hb.1 _ rfl) (le_trans (hd.sound ρ hs) (hb.2 _ rfl))
  | all => exact hb

theorem move_bounds {ρ : V k → Tree} (hs : Sat ρ ϕ)
    {q r : CState k} {i : Fin 2} (h : Move ϕ i q r) {X Y : Tree}
    (hb : Bounds ρ X Y q) : Bounds ρ (descend X i) (descend Y i) r := by
  cases h with
  | descend_left hu =>
    have hm := le_trans (descend_mono (hb.1 _ rfl) i) (upper_trace_le hu hs)
    simpa [Bounds] using hm
  | descend_right hl =>
    have hm := le_trans (lower_le_trace hl hs) (descend_mono (hb.2 _ rfl) i)
    simpa [Bounds] using hm
  | descend_both hu hl =>
    have hm₁ := le_trans (descend_mono (hb.1 _ rfl) i) (upper_trace_le hu hs)
    have hm₂ := le_trans (lower_le_trace hl hs) (descend_mono (hb.2 _ rfl) i)
    simpa [Bounds] using And.intro hm₁ hm₂
  | bot hd hl =>
    have he : X = Tree.bot := (Tree.le_bot_iff _).mp
      (le_trans (hb.1 _ rfl) (le_trans (hd.sound ρ hs) (le_of_eq (hs _ hl))))
    simp [Bounds, he]
  | top hd hl =>
    have he : Y = Tree.top := (Tree.top_le_iff _).mp
      (le_trans (le_of_eq (hs _ hl).symm) (le_trans (hd.sound ρ hs) (hb.2 _ rfl)))
    simp [Bounds, he]
  | reflexivity hd =>
    exact descend_mono (le_trans (hb.1 _ rfl) (le_trans (hd.sound ρ hs) (hb.2 _ rfl))) i
  | all => exact descend_mono hb i

theorem runs_bounds {ρ : V k → Tree} (hs : Sat ρ ϕ)
    {q r : CState k} {π : List (Fin 2)} (h : Runs (construct ϕ x y θ) q π r)
    {X Y : Tree} (hb : Bounds ρ X Y q) : Bounds ρ (trace X π) (trace Y π) r := by
  induction h generalizing X Y with
  | nil => exact hb
  | cons hm _ ih => exact ih (move_bounds hs (mem_step_iff.mp hm) hb)

theorem upper_singleton_ne_top {ρ : V k → Tree} (hs : Sat ρ ϕ)
    {u v : V k} {i : Fin 2} (h : UpperAt ϕ [i] u v) : ρ u ≠ Tree.top := by
  intro he
  have hh := upper_bound_proper_prefix (Y := Tree.bot) (h.sound hs)
    (τ := []) List.nil_prefix (by simp)
  simpa [he] using hh (by simp [he])

theorem lower_singleton_ne_bot {ρ : V k → Tree} (hs : Sat ρ ϕ)
    {u v : V k} {i : Fin 2} (h : LowerAt ϕ [i] v u) : ρ u ≠ Tree.bot := by
  intro he
  have hb := h.embed_le hs
  rw [he] at hb
  have he' := (Tree.le_bot_iff _).mp hb
  fin_cases i <;> have := congrArg (fun t : Tree => t.fn []) he' <;>
    simp [PathBounds.embed] at this

end Construction

open CapAutomaton Safety Construction

variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {π : List (Fin 2)}

theorem soundA_l (h : π ∈ LangA (construct ϕ x y .l)) : LSafe ϕ x y π := by
  rintro ρ hs hx
  obtain ⟨q, hr, hf⟩ := h
  have hb := runs_bounds hs hr (X := ρ x) (Y := ρ y) (by simp [construct, Bounds])
  simp only [construct, finalB, Bool.or_eq_true] at hf
  rcases hf with hf | hf
  ·
    cases q with
    | all =>
      change trace (ρ x) π ≤ trace (ρ y) π at hb
      apply (trace_eq_top_iff _ _).mp
      exact (Tree.top_le_iff _).mp (by simpa [(trace_eq_top_iff _ _).mpr hx] using hb)
    | pair a b =>
      cases a with
      | none => simp [childFinalB] at hf
      | some u =>
        obtain ⟨i, v, hu⟩ : ∃ i v, UpperAt ϕ [i] u v := by
          simpa [childFinalB, upperAtB_iff] using hf
        have he : ρ u = Tree.top := (Tree.top_le_iff _).mp
          (by simpa [(trace_eq_top_iff _ _).mpr hx] using hb.1 u rfl)
        exact (upper_singleton_ne_top hs hu he).elim

  · have hm := move_to_all_bounds hs ((moveB_iff _ _ _ _).mp hf) hb
    apply (trace_eq_top_iff _ _).mp
    exact (Tree.top_le_iff _).mp (by simpa [(trace_eq_top_iff _ _).mpr hx] using hm)

theorem soundA_r (h : π ∈ LangA (construct ϕ x y .r)) : RSafe ϕ x y π := by
  rintro ρ hs hy
  obtain ⟨q, hr, hf⟩ := h
  have hb := runs_bounds hs hr (X := ρ x) (Y := ρ y) (by simp [construct, Bounds])
  simp only [construct, finalB, Bool.or_eq_true] at hf
  rcases hf with hf | hf
  ·
    cases q with
    | all =>
      change trace (ρ x) π ≤ trace (ρ y) π at hb
      apply (trace_eq_bot_iff _ _).mp
      exact (Tree.le_bot_iff _).mp (by simpa [(trace_eq_bot_iff _ _).mpr hy] using hb)
    | pair a b =>
      cases b with
      | none => simp [childFinalB] at hf
      | some v =>
        obtain ⟨i, u, hl⟩ : ∃ i u, LowerAt ϕ [i] u v := by
          simpa [childFinalB, lowerAtB_iff] using hf
        have he : ρ v = Tree.bot := (Tree.le_bot_iff _).mp
          (by simpa [(trace_eq_bot_iff _ _).mpr hy] using hb.2 v rfl)
        exact (lower_singleton_ne_bot hs hl he).elim

  · have hm := move_to_all_bounds hs ((moveB_iff _ _ _ _).mp hf) hb
    apply (trace_eq_bot_iff _ _).mp
    exact (Tree.le_bot_iff _).mp (by simpa [(trace_eq_bot_iff _ _).mpr hy] using hm)

end DeciNSSE
