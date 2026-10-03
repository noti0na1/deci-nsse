import DeciNSSE.Automata.Soundness
import DeciNSSE.Automata.Completeness

/-! # Entailment as language universality

Rejected words give satisfiable path-witness systems. Order duality transfers
the right-side argument to the left, proving that entailment is equivalent
to unsatisfiability or universality of both constraint automata.
-/

namespace DeciNSSE.Language

open Safety Words CapAutomaton CState Construction Completeness

variable {k : ℕ} {ϕ : Constraint k} {x y u v : V k} {θ : Side}
  {ν π τ : Word}

theorem upperAt_run_from (hn : π ≠ []) (h : UpperAt ϕ π u v)
    (s : Option (V k)) :
    Runs (construct ϕ x y θ) (pair (some u) s) π (pair (some v) none) := by
  cases π with
  | nil => exact (hn rfl).elim
  | cons i π =>
    cases π with
    | nil => exact .cons (mem_step_iff.mpr (.descend_left h)) (.nil _)
    | cons j π =>
      obtain ⟨w, hw, hp⟩ := UpperAt.factor (π := [i]) h
      exact .cons (mem_step_iff.mpr (.descend_left hw)) (upperAt_run (by simp) hp)

theorem lowerAt_run_from (hn : π ≠ []) (h : LowerAt ϕ π v u)
    (s : Option (V k)) :
    Runs (construct ϕ x y θ) (pair s (some u)) π (pair none (some v)) := by
  cases π with
  | nil => exact (hn rfl).elim
  | cons i π =>
    cases π with
    | nil => exact .cons (mem_step_iff.mpr (.descend_right h)) (.nil _)
    | cons j π =>
      obtain ⟨w, hw, hp⟩ := LowerAt.factor (π := [i]) h
      exact .cons (mem_step_iff.mpr (.descend_right hw)) (lowerAt_run (by simp) hp)

theorem pair_run (hn : π ≠ []) {u' v' : V k}
    (hu : UpperAt ϕ π u u') (hl : LowerAt ϕ π v' v) :
    Runs (construct ϕ x y θ) (pair (some u) (some v)) π
      (pair (some u') (some v')) := by
  induction π generalizing u v with
  | nil => exact (hn rfl).elim
  | cons i π ih =>
    cases π with
    | nil => exact .cons (mem_step_iff.mpr (.descend_both hu hl)) (.nil _)
    | cons j π =>
      obtain ⟨a, ha, hu⟩ := UpperAt.factor (π := [i]) hu
      obtain ⟨b, hb, hl⟩ := LowerAt.factor (π := [i]) hl
      exact .cons (mem_step_iff.mpr (.descend_both ha hb)) (ih (by simp) hu hl)

theorem move_all_letter {q : CState k} (h : Move ϕ 0 q all) (i : Fin 2) :
    Move ϕ i q all := by
  cases h with
  | bot hd hl => exact .bot hd hl
  | top hd hl => exact .top hd hl
  | reflexivity hd => exact .reflexivity hd
  | all => exact .all

theorem memA_of_run_move_all {q : CState k}
    (hr : Runs (construct ϕ x y θ) (construct ϕ x y θ).init π q)
    (hm : Move ϕ 0 q all) (τ : Word) : π ++ τ ∈ LangA (construct ϕ x y θ) := by
  cases τ with
  | nil =>
    refine ⟨q, by simpa using hr, ?_⟩
    simp only [construct, finalB, Bool.or_eq_true]
    exact Or.inr ((moveB_iff ..).mpr hm)
  | cons i τ =>
    exact ⟨all, Runs.append _ hr (.cons (mem_step_iff.mpr (move_all_letter hm i))
      (all_run τ)), rfl⟩

theorem memA_of_upper_bot (h : UpperAt ϕ π x v) (hb : Lit.eqBot v ∈ ϕ)
    (hp : π <+: ν) : ν ∈ LangA (construct ϕ x y θ) := by
  obtain ⟨τ, rfl⟩ := hp
  by_cases hn : π = []
  · subst π
    exact memA_of_run_move_all (.nil _) (.bot (upperAt_nil_iff.mp h) hb) τ
  · exact memA_of_run_move_all (upperAt_run_from hn h (some y))
      (.bot (.refl _) hb) τ

theorem memA_of_lower_top (h : LowerAt ϕ π v y) (ht : Lit.eqTop v ∈ ϕ)
    (hp : π <+: ν) : ν ∈ LangA (construct ϕ x y θ) := by
  obtain ⟨τ, rfl⟩ := hp
  by_cases hn : π = []
  · subst π
    exact memA_of_run_move_all (.nil _) (.top (lowerAt_nil_iff.mp h) ht) τ
  · exact memA_of_run_move_all (lowerAt_run_from hn h (some x))
      (.top (.refl _) ht) τ

theorem memA_of_lowerLabel_f (h : LowerLabel ϕ ν .f y) :
    ν ∈ LangA (construct ϕ x y .r) := by
  obtain ⟨z, a, b, hf, hl⟩ := h
  have final {w : V k} (hd : Derives ϕ z w) (s : Option (V k)) :
      (construct ϕ x y .r).final (pair s (some w)) = true := by
    simp only [construct, finalB, Bool.or_eq_true]
    apply Or.inl
    simp only [childFinalB, decide_eq_true_eq, lowerAtB_iff]
    exact ⟨0, a, .cons hf hd (.nil (.refl _))⟩
  by_cases hn : ν = []
  · subst ν
    exact ⟨_, .nil _, final (lowerAt_nil_iff.mp hl) (some x)⟩
  · exact ⟨_, lowerAt_run_from hn hl (some x), final (.refl _) none⟩

theorem memA_of_derives (hd : Derives ϕ x y) (ν : Word) :
    ν ∈ LangA (construct ϕ x y θ) :=
  memA_of_run_move_all (.nil _) (.reflexivity hd) ν

theorem memA_of_common (hn : π ≠ []) (hu : UpperAt ϕ π x v)
    (hl : LowerAt ϕ π v y) (hp : π <+: ν) :
    ν ∈ LangA (construct ϕ x y θ) := by
  obtain ⟨τ, rfl⟩ := hp
  exact memA_of_run_move_all (pair_run hn hu hl) (.reflexivity (.refl _)) τ

theorem memP_of_factor (hπ : π ≠ []) (hτ : τ ≠ [])
    (hu : UpperAt ϕ π x v) (hl : LowerAt ϕ (π ++ τ) v y)
    (hp : ∃ μ, ν = π ++ μ ∧ IsPrefixOfPower τ μ) :
    ν ∈ LangP (construct ϕ x y .r) := by
  obtain ⟨s, hs, ht⟩ := LowerAt.factor hl
  obtain ⟨μ, rfl, hp⟩ := hp
  exact ⟨π, μ, pair (some v) (some s), pair none (some v), τ, rfl,
    pair_run hπ hu hs, lowerAt_run_from hτ ht (some v),
    Soundness.pedge_r_iff.mpr ⟨v, s, none, rfl, rfl⟩, hp⟩

theorem memP_of_initial_factor (hτ : τ ≠ []) (hu : Derives ϕ x v)
    (hl : LowerAt ϕ τ v y) (hp : IsPrefixOfPower τ ν) :
    ν ∈ LangP (construct ϕ x y .r) := by
  have hx : LowerAt ϕ τ x y := by simpa using (LowerAt.nil hu).comp hl
  exact ⟨[], ν, pair (some x) (some y), pair none (some x), τ, rfl,
    .nil _, lowerAt_run_from hτ hx (some x),
    Soundness.pedge_r_iff.mpr ⟨x, y, none, rfl, rfl⟩, hp⟩

theorem mem_of_lowerLabel_f_chain
    (h : LowerLabel (chainConstraint ϕ x ν) ν .f (Fin.castAdd _ y)) :
    ν ∈ Lang (construct ϕ x y .r) := by
  rcases (lowerLabel_f_chain_iff y).mp h with h | ⟨z, π₁, π₂, hpre, hl, hu, hp⟩
  · exact Or.inl (memA_of_lowerLabel_f h)
  · by_cases h₂ : π₂ = []
    · subst π₂
      simp only [List.append_nil] at hl
      by_cases h₁ : π₁ = []
      · subst π₁
        exact Or.inl (memA_of_derives
          ((upperAt_nil_iff.mp hu).trans (lowerAt_nil_iff.mp hl)) ν)
      · exact Or.inl (memA_of_common h₁ hu hl hpre)
    · by_cases h₁ : π₁ = []
      · subst π₁
        obtain ⟨μ, he, hp⟩ := hp h₂
        simp only [List.nil_append] at he hl
        subst μ
        exact Or.inr (memP_of_initial_factor h₂ (upperAt_nil_iff.mp hu) hl hp)
      · exact Or.inr (memP_of_factor h₁ h₂ hu hl (hp h₂))

theorem not_labelClash_chain (hn : ν ∉ Lang (construct ϕ x y .r))
    (hs : ∃ ρ, Sat ρ ϕ) : ¬ LabelClash (chainConstraint ϕ x ν) := by
  have hc := satisfiable_iff_not_labelClash.mp hs
  rintro ⟨w, h | h | h⟩
  · obtain ⟨⟨a, ha, hd⟩, b, hb, he⟩ := h
    have hab := hd.trans he
    obtain ⟨a', ha', rfl⟩ := eqTop_original ha
    rcases eqBot_original_or_bv hb with ⟨b', hb', rfl⟩ | rfl
    · exact hc ⟨b', Or.inl ⟨⟨a', ha', (Completeness.derives_original _ _).mp hab⟩,
        b', hb', .refl _⟩⟩
    · exact not_lowerLabel_top_bv [] ⟨_, ha, .nil hab⟩
  · obtain ⟨⟨a, ha, hd⟩, b, b₁, b₂, hb, he⟩ := h
    obtain ⟨a', ha', rfl⟩ := eqTop_original ha
    obtain ⟨b', b₁', b₂', hb', rfl, _, _⟩ := leF_original hb
    exact hc ⟨b', Or.inr (Or.inl ⟨⟨a', ha',
      (Completeness.derives_original _ _).mp (hd.trans he)⟩, b', b₁', b₂', hb', .refl _⟩)⟩
  · obtain ⟨⟨a₁, a₂, a, ha, hd⟩, b, hb, he⟩ := h
    have hab := hd.trans he
    rcases eqBot_original_or_bv hb with ⟨b', hb', rfl⟩ | rfl
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨a₁', a₂', a', ha', rfl, rfl, rfl⟩ := TransferFin.fLe_mem_lift ha
        exact hc ⟨b', Or.inr (Or.inr ⟨⟨a₁', a₂', a', ha',
          (Completeness.derives_original _ _).mp hab⟩, b', hb', .refl _⟩)⟩
      · obtain ⟨j, hj, rfl⟩ := fLe_chain_root ha
        exact hn (Or.inl (memA_of_upper_bot ((derives_chain_iff hj b').mp hab)
          hb' (List.take_prefix j ν)))
    · exact not_lowerLabel_f_bv [] ⟨a, a₁, a₂, ha, .nil hab⟩

theorem least_no_bot_bounds {m : ℕ} {ψ : Constraint m} {z : V m}
    (h : ¬ HasLabel (least ψ z) ν .bot) :
    (∃ π, π <+: ν ∧ LowerLabel ψ π .top z) ∨ LowerLabel ψ ν .f z := by
  have top {π : Word} (hp : π <+: ν) (he : (least ψ z).fn π = some Sym.top) :
      ∃ π, π <+: ν ∧ LowerLabel ψ π .top z := by
    exact ⟨π, hp, (least_label_eq he).symm ▸ lowerLabel_lowSup ψ z π⟩
  cases he : (least ψ z).fn ν with
  | none =>
    obtain ⟨π, hp, hb | ht⟩ := Soundness.leaf_prefix_of_missing he
    · exact (h ⟨π, hp, hb⟩).elim
    · exact Or.inl (top hp ht)
  | some a =>
    cases a with
    | bot => exact (h ⟨ν, List.prefix_rfl, he⟩).elim
    | top => exact Or.inl (top List.prefix_rfl he)
    | f => exact Or.inr ((least_label_eq he).symm ▸ lowerLabel_lowSup ψ z ν)

theorem least_bot_prefix (hn : ν ∉ Lang (construct ϕ x y .r))
    (_hs : ∃ ρ, Sat ρ ϕ) :
    ∃ τ, τ <+: ν ∧ (least (chainConstraint ϕ x ν) (Fin.castAdd _ y)).fn τ =
      some Sym.bot := by
  classical
  by_contra hb
  rcases least_no_bot_bounds hb with ⟨π, hp, ht⟩ | hf
  · obtain ⟨z, hz, hl⟩ := lowerLabel_top_original hp ht
    exact hn (Or.inl (memA_of_lower_top hl hz hp))
  · exact hn (mem_of_lowerLabel_f_chain hf)

theorem sat_rUnsafe_of_rejected (hn : ν ∉ Lang (construct ϕ x y .r))
    (hs : ∃ ρ, Sat ρ ϕ) : ∃ ρ', Sat ρ' (rUnsafe ϕ x y ν) := by
  have hleast := least_sat (not_labelClash_chain hn hs)
  have hparts : Sat ((least (chainConstraint ϕ x ν)) ∘ Fin.castAdd _) ϕ ∧
      Sat (least (chainConstraint ϕ x ν)) (noBotChain x ν) := by
    simpa only [chainConstraint, sat_append, sat_lift] using hleast
  exact ⟨_, rUnsafe_extend _ hparts.1 (noBotChain_sound hparts.2)
    ((trace_eq_bot_iff _ _).mpr (least_bot_prefix hn hs))⟩

namespace Dual

def sym : Sym → Sym
  | .bot => .top
  | .f => .f
  | .top => .bot

@[simp] theorem sym_sym (a : Sym) : sym (sym a) = a := by cases a <;> rfl

@[simp] theorem sym_le (a b : Sym) : sym a ≤ sym b ↔ b ≤ a := by
  cases a <;> cases b <;> decide

def tree (t : Tree) : Tree where
  fn π := (t.fn π).map sym
  wf := by
    constructor
    · simpa using t.wf.1
    · intro π i
      rw [Option.isSome_map, t.child_isSome_iff]
      cases h : t.fn π with
      | none => simp
      | some a => cases a <;> simp [sym]

@[simp] theorem tree_fn (t : Tree) (π : Word) : (tree t).fn π = (t.fn π).map sym := rfl

@[simp] theorem tree_tree (t : Tree) : tree (tree t) = t := by
  apply Tree.ext
  funext π
  simp only [tree_fn, Option.map_map]
  cases t.fn π <;> simp

@[simp] theorem tree_bot : tree Tree.bot = Tree.top := by
  apply Tree.ext
  funext π
  cases π <;> rfl

@[simp] theorem tree_top : tree Tree.top = Tree.bot := by
  apply Tree.ext
  funext π
  cases π <;> rfl

@[simp] theorem tree_node (a b : Tree) :
    tree (Tree.node a b) = Tree.node (tree a) (tree b) := by
  apply Tree.ext
  funext π
  cases π with
  | nil => rfl
  | cons i π => fin_cases i <;> rfl

theorem tree_le_of {a b : Tree} (h : a ≤ b) : tree b ≤ tree a := by
  intro π s t hs ht
  obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
  exact (sym_le _ _).mpr (h π _ _ ht' hs')

@[simp] theorem tree_le (a b : Tree) : tree a ≤ tree b ↔ b ≤ a := by
  constructor
  · intro h; simpa using tree_le_of h
  · exact tree_le_of

@[simp] theorem tree_eq_bot (t : Tree) : tree t = Tree.bot ↔ t = Tree.top := by
  constructor
  · intro h; simpa using congrArg tree h
  · rintro rfl; exact tree_top

@[simp] theorem tree_eq_top (t : Tree) : tree t = Tree.top ↔ t = Tree.bot := by
  constructor
  · intro h; simpa using congrArg tree h
  · rintro rfl; exact tree_bot

theorem hasLabel (t : Tree) (π : Word) (a : Sym) :
    HasLabel (tree t) π (sym a) ↔ HasLabel t π a := by
  have hinj : Function.Injective sym := Function.LeftInverse.injective sym_sym
  simp only [HasLabel, tree_fn, Option.map_eq_some_iff]
  constructor
  · rintro ⟨τ, hp, b, hb, he⟩
    exact ⟨τ, hp, hinj he ▸ hb⟩
  · rintro ⟨τ, hp, ht⟩; exact ⟨τ, hp, a, ht, rfl⟩

def lit : Lit k → Lit k
  | .leF x a b => .fLe a b x
  | .fLe a b x => .leF x a b
  | .eqBot x => .eqTop x
  | .eqTop x => .eqBot x

@[simp] theorem lit_lit (l : Lit k) : lit (lit l) = l := by cases l <;> rfl

def constraint (ϕ : Constraint k) : Constraint k := ϕ.map lit

@[simp] theorem constraint_constraint (ϕ : Constraint k) :
    constraint (constraint ϕ) = ϕ := by
  simp only [constraint, List.map_map]
  have h : (lit (k := k)) ∘ lit = id := funext lit_lit
  rw [h, List.map_id]

@[simp] theorem lit_mem (l : Lit k) : lit l ∈ constraint ϕ ↔ l ∈ ϕ := by
  have hinj : Function.Injective (lit (k := k)) := Function.LeftInverse.injective lit_lit
  exact List.mem_map_of_injective hinj

@[simp] theorem holds (ρ : V k → Tree) (l : Lit k) :
    (lit l).holds (tree ∘ ρ) ↔ l.holds ρ := by
  cases l <;> simp only [lit, Lit.holds, Function.comp_apply, ← tree_node,
    tree_le, tree_eq_bot, tree_eq_top]

@[simp] theorem sat (ρ : V k → Tree) : Sat (tree ∘ ρ) (constraint ϕ) ↔ Sat ρ ϕ := by
  simp only [Sat, constraint, List.forall_mem_map, holds]

theorem sat_of_dual {ρ : V k → Tree} (h : Sat ρ (constraint ϕ)) :
    Sat (tree ∘ ρ) ϕ := by
  simpa only [constraint_constraint] using (sat ρ).mpr h

theorem satisfiable (h : ∃ ρ, Sat ρ ϕ) : ∃ ρ, Sat ρ (constraint ϕ) := by
  obtain ⟨ρ, hs⟩ := h
  exact ⟨_, (sat ρ).mpr hs⟩

theorem derives {a b : V k} (h : Derives ϕ a b) : Derives (constraint ϕ) b a := by
  induction h with
  | refl => exact .refl _
  | trans _ _ ih ih' => exact ih'.trans ih
  | decomp_left hl _ hu ih => exact .decomp_left ((lit_mem _).mpr hu) ih ((lit_mem _).mpr hl)
  | decomp_right hl _ hu ih => exact .decomp_right ((lit_mem _).mpr hu) ih ((lit_mem _).mpr hl)

@[simp] theorem derives_iff {a b : V k} : Derives (constraint ϕ) a b ↔ Derives ϕ b a := by
  constructor
  · intro h; simpa using derives h
  · exact derives

theorem upper {a b : V k} (h : UpperAt ϕ π a b) : LowerAt (constraint ϕ) π b a := by
  induction h with
  | nil hd => exact .nil (derives hd)
  | cons hd hl _ ih => exact .cons ((lit_mem _).mpr hl) (derives hd) ih

theorem lower {a b : V k} (h : LowerAt ϕ π a b) : UpperAt (constraint ϕ) π b a := by
  induction h with
  | nil hd => exact .nil (derives hd)
  | cons hl hd _ ih => exact .cons (derives hd) ((lit_mem _).mpr hl) ih

@[simp] theorem lower_iff {a b : V k} :
    LowerAt (constraint ϕ) π a b ↔ UpperAt ϕ π b a := by
  constructor
  · intro h; simpa using lower h
  · exact upper

@[simp] theorem upper_iff {a b : V k} :
    UpperAt (constraint ϕ) π a b ↔ LowerAt ϕ π b a := by
  constructor
  · intro h; simpa using upper h
  · exact lower

def state : CState k → CState k
  | pair a b => pair b a
  | all => all

@[simp] theorem state_state (q : CState k) : state (state q) = q := by cases q <;> rfl

theorem move {q r : CState k} {i : Fin 2} (h : Move ϕ i q r) :
    Move (constraint ϕ) i (state q) (state r) := by
  cases h with
  | descend_left h => exact .descend_right (upper h)
  | descend_right h => exact .descend_left (lower h)
  | descend_both hu hl => exact .descend_both (lower hl) (upper hu)
  | bot hd hl => exact .top (derives hd) ((lit_mem _).mpr hl)
  | top hd hl => exact .bot (derives hd) ((lit_mem _).mpr hl)
  | reflexivity hd => exact .reflexivity (derives hd)
  | all => exact .all

@[simp] theorem move_iff {q r : CState k} {i : Fin 2} :
    Move (constraint ϕ) i (state q) (state r) ↔ Move ϕ i q r := by
  constructor
  · intro h; simpa using move h
  · exact move

theorem runs {θ' : Side} {q r : CState k}
    (h : Runs (construct ϕ x y θ) q π r) :
    Runs (construct (constraint ϕ) y x θ') (state q) π (state r) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (mem_step_iff.mpr (move (mem_step_iff.mp hs))) ih

@[simp] theorem final_r (q : CState k) :
    (construct (constraint ϕ) y x .r).final (state q) = true ↔
      (construct ϕ x y .l).final q = true := by
  simp only [construct, finalB, Bool.or_eq_true, moveB_iff]
  have hm : Move (constraint ϕ) 0 (state q) all ↔ Move ϕ 0 q all :=
    move_iff (r := all)
  rw [hm]
  cases q with
  | all => rfl
  | pair a b => cases a <;> simp [state, childFinalB, lowerAtB_iff, upperAtB_iff]

@[simp] theorem pedge_r (q r : CState k) :
    (construct (constraint ϕ) y x .r).pedge (state q) (state r) = true ↔
      (construct ϕ x y .l).pedge q r = true := by
  cases q with
  | all => simp [state, construct, pedgeB]
  | pair a b =>
    cases r with
    | all => simp [state, construct, pedgeB]
    | pair c d => cases a <;> cases c <;> cases d <;> simp [state, construct, pedgeB]

theorem lang_r : ν ∈ Lang (construct (constraint ϕ) y x .r) ↔
    ν ∈ Lang (construct ϕ x y .l) := by
  constructor
  · rintro (⟨q, hr, hf⟩ | ⟨π, μ, q, r, τ, he, hr, ht, hp, hw⟩)
    · apply Or.inl
      refine ⟨state q, ?_, ?_⟩
      · simpa only [constraint_constraint, state, construct] using (runs (θ' := .l) hr)
      · exact (final_r (state q)).mp (by simpa using hf)
    · apply Or.inr
      refine ⟨π, μ, state q, state r, τ, he, ?_, ?_, ?_, hw⟩
      · simpa only [constraint_constraint, state, construct] using (runs (θ' := .l) hr)
      · simpa only [constraint_constraint] using (runs (θ' := .l) ht)
      · exact (pedge_r (state r) (state q)).mp (by simpa using hp)
  · rintro (⟨q, hr, hf⟩ | ⟨π, μ, q, r, τ, he, hr, ht, hp, hw⟩)
    · exact Or.inl ⟨state q, runs hr, (final_r q).mpr hf⟩
    · exact Or.inr ⟨π, μ, state q, state r, τ, he, runs hr, runs ht,
        (pedge_r r q).mpr hp, hw⟩

theorem rSafe_of_lSafe (h : LSafe ϕ x y ν) : RSafe (constraint ϕ) y x ν := by
  intro ρ hs hx
  have ht := h (tree ∘ ρ) (sat_of_dual hs) ((hasLabel _ _ .bot).mpr hx)
  exact (hasLabel _ _ .bot).mp ht

end Dual

theorem sat_lUnsafe_of_rejected (hn : ν ∉ Lang (construct ϕ x y .l))
    (hs : ∃ ρ, Sat ρ ϕ) : ∃ ρ', Sat ρ' (lUnsafe ϕ x y ν) := by
  apply not_lSafe_iff.mp
  intro hl
  have hr := sat_rUnsafe_of_rejected (fun h => hn (Dual.lang_r.mp h)) (Dual.satisfiable hs)
  exact (not_rSafe_iff.mpr hr) (Dual.rSafe_of_lSafe hl)

theorem complete_r (hs : ∃ ρ, Sat ρ ϕ) (h : RSafe ϕ x y ν) :
    ν ∈ Lang (construct ϕ x y .r) := by
  classical
  by_contra hn
  exact (not_rSafe_iff.mpr (sat_rUnsafe_of_rejected hn hs)) h

theorem complete_l (hs : ∃ ρ, Sat ρ ϕ) (h : LSafe ϕ x y ν) :
    ν ∈ Lang (construct ϕ x y .l) := by
  classical
  by_contra hn
  exact (not_lSafe_iff.mpr (sat_lUnsafe_of_rejected hn hs)) h

theorem entails_iff_universal : Entails ϕ x y ↔
    (¬ ∃ ρ, Sat ρ ϕ) ∨
      ((∀ π, π ∈ Lang (construct ϕ x y .l)) ∧
       (∀ π, π ∈ Lang (construct ϕ x y .r))) := by
  classical
  constructor
  · intro h
    by_cases hs : ∃ ρ, Sat ρ ϕ
    · have hsafe := entails_iff_safe.mp h
      exact Or.inr ⟨fun π => complete_l hs (hsafe π).1,
        fun π => complete_r hs (hsafe π).2⟩
    · exact Or.inl hs
  · rintro (hn | ⟨hl, hr⟩)
    · exact fun ρ hs => (hn ⟨ρ, hs⟩).elim
    · exact entails_of_universal hl hr

theorem entails_iff_universal' : Entails ϕ x y ↔
    (satInfB ϕ = false ∨
      ((∀ π, π ∈ Lang (construct ϕ x y .l)) ∧
       (∀ π, π ∈ Lang (construct ϕ x y .r)))) := by
  rw [entails_iff_universal, ← satInfB_iff]
  simp

end DeciNSSE.Language
