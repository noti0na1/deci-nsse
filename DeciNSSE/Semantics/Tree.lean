import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import DeciNSSE.Semantics.Sym

/-! # Finite and infinite trees

Trees are partial labellings of binary paths: precisely the constructor nodes
have two children. Their non-structural order has bottom below every tree, top
above every tree, and a covariant binary constructor.
-/

namespace DeciNSSE

/-- A finite or infinite binary tree, represented by a well-formed partial labelling of paths. -/
structure Tree where
  /-- The optional label at each binary path. -/
  fn : List (Fin 2) → Option Sym
  /-- The root exists, and exactly the constructor-labelled paths have children. -/
  wf : fn [] ≠ none ∧ ∀ π i, (fn (π ++ [i])).isSome ↔ fn π = some Sym.f

namespace Tree

@[ext] theorem ext {t u : Tree} (h : t.fn = u.fn) : t = u := by
  cases t
  cases u
  cases h
  rfl

theorem root_isSome (t : Tree) : (t.fn []).isSome :=
  Option.isSome_iff_ne_none.mpr t.wf.1

theorem child_isSome_iff (t : Tree) (π : List (Fin 2)) (i : Fin 2) :
    (t.fn (π ++ [i])).isSome ↔ t.fn π = some Sym.f := t.wf.2 π i

theorem domain_append_left (t : Tree) (π ρ : List (Fin 2))
    (h : (t.fn (π ++ ρ)).isSome) : (t.fn π).isSome := by
  induction ρ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton ρ i ih =>
    have hf : t.fn (π ++ ρ) = some Sym.f :=
      (t.child_isSome_iff (π ++ ρ) i).mp (by simpa [List.append_assoc] using h)
    exact ih (by simp [hf])

/-- Every proper prefix of a path in the tree is labelled by the constructor. -/
theorem label_eq_f_of_proper_prefix (t : Tree) {π ρ : List (Fin 2)}
    (hprefix : π.IsPrefix ρ) (hne : π ≠ ρ) (h : (t.fn ρ).isSome) :
    t.fn π = some Sym.f := by
  obtain ⟨σ, rfl⟩ := hprefix
  cases σ with
  | nil => simp at hne
  | cons i σ =>
    apply (t.child_isSome_iff π i).mp
    exact t.domain_append_left (π ++ [i]) σ (by simpa [List.append_assoc] using h)

/-- The least tree, consisting of a single bottom leaf. -/
def bot : Tree where
  fn
    | [] => some Sym.bot
    | _ :: _ => none
  wf := by
    constructor
    · decide
    · intro π i; cases π <;> simp

/-- The greatest tree, consisting of a single top leaf. -/
def top : Tree where
  fn
    | [] => some Sym.top
    | _ :: _ => none
  wf := by
    constructor
    · decide
    · intro π i; cases π <;> simp

/-- The binary constructor applied covariantly to its two subtrees. -/
def node (l r : Tree) : Tree where
  fn
    | [] => some Sym.f
    | i :: π => if i = 0 then l.fn π else r.fn π
  wf := by
    constructor
    · simp
    · intro π i
      cases π with
      | nil => simp only [List.nil_append]; split <;> simp [root_isSome]
      | cons j π =>
        simp only [List.cons_append]
        split <;> simp_all [child_isSome_iff]

@[simp] theorem bot_fn_nil : bot.fn [] = some Sym.bot := rfl
@[simp] theorem bot_fn_cons (i : Fin 2) (π : List (Fin 2)) :
    bot.fn (i :: π) = none := rfl
@[simp] theorem top_fn_nil : top.fn [] = some Sym.top := rfl
@[simp] theorem top_fn_cons (i : Fin 2) (π : List (Fin 2)) :
    top.fn (i :: π) = none := rfl
@[simp] theorem node_fn_nil (l r : Tree) : (node l r).fn [] = some Sym.f := rfl
@[simp] theorem node_fn_zero_cons (l r : Tree) (π : List (Fin 2)) :
    (node l r).fn (0 :: π) = l.fn π := by simp [node]
@[simp] theorem node_fn_one_cons (l r : Tree) (π : List (Fin 2)) :
    (node l r).fn (1 :: π) = r.fn π := by simp [node]

/-- The subtree at a path, if that path belongs to the tree. -/
def subtree (t : Tree) (π : List (Fin 2)) : Option Tree :=
  if h : (t.fn π).isSome then
    some {
      fn := fun ρ => t.fn (π ++ ρ)
      wf := by
        constructor
        · simpa using Option.isSome_iff_ne_none.mp h
        · intro ρ i
          simpa [List.append_assoc] using t.child_isSome_iff (π ++ ρ) i
    }
  else none

@[simp] theorem subtree_isSome_iff (t : Tree) (π : List (Fin 2)) :
    (t.subtree π).isSome ↔ (t.fn π).isSome := by
  unfold subtree
  split <;> simp_all

theorem subtree_fn {t u : Tree} {π : List (Fin 2)} (h : t.subtree π = some u)
    (ρ : List (Fin 2)) : u.fn ρ = t.fn (π ++ ρ) := by
  unfold subtree at h
  split at h
  · cases Option.some.inj h
    rfl
  · contradiction

theorem fn_cons_eq_none_of_root_ne_f (t : Tree) (h : t.fn [] ≠ some Sym.f)
    (i : Fin 2) (π : List (Fin 2)) : t.fn (i :: π) = none := by
  by_contra hsome
  apply h
  apply (t.child_isSome_iff [] i).mp
  exact t.domain_append_left [i] π (Option.isSome_iff_ne_none.mpr hsome)

@[simp] theorem root_eq_bot_iff (t : Tree) : t.fn [] = some Sym.bot ↔ t = bot := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

@[simp] theorem root_eq_top_iff (t : Tree) : t.fn [] = some Sym.top ↔ t = top := by
  constructor
  · intro h
    apply ext
    funext π
    cases π with
    | nil => exact h
    | cons i π =>
      exact t.fn_cons_eq_none_of_root_ne_f (by simp [h]) i π
  · rintro rfl
    rfl

/-- The selected child of a tree whose root is labelled by the constructor. -/
def branch (t : Tree) (i : Fin 2) (h : t.fn [] = some Sym.f) : Tree where
  fn := fun π => t.fn (i :: π)
  wf := by
    constructor
    · exact Option.isSome_iff_ne_none.mp ((t.child_isSome_iff [] i).mpr h)
    · intro π j
      exact t.child_isSome_iff (i :: π) j

/-- A tree with constructor root is the node formed by its two branches. -/
theorem eq_node_of_root_eq_f (t : Tree) (h : t.fn [] = some Sym.f) :
    t = node (t.branch 0 h) (t.branch 1 h) := by
  apply ext
  funext π
  cases π with
  | nil => exact h
  | cons i π => fin_cases i <;> simp [branch]

/-- Every tree is a bottom leaf, a top leaf or a binary node. -/
theorem eq_bot_or_eq_top_or_node (t : Tree) :
    t = bot ∨ t = top ∨ ∃ l r, t = node l r := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp t.root_isSome
  cases s with
  | bot => exact Or.inl ((root_eq_bot_iff t).mp hs)
  | top => exact Or.inr (Or.inl ((root_eq_top_iff t).mp hs))
  | f => exact Or.inr (Or.inr ⟨_, _, t.eq_node_of_root_eq_f hs⟩)

@[simp] theorem node_eq_node_iff (l r l' r' : Tree) :
    node l r = node l' r' ↔ l = l' ∧ r = r' := by
  constructor
  · intro h
    constructor
    · apply ext
      funext π
      simpa using congrArg (fun t : Tree => t.fn (0 :: π)) h
    · apply ext
      funext π
      simpa using congrArg (fun t : Tree => t.fn (1 :: π)) h
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem bot_ne_top : bot ≠ top := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem node_ne_bot (l r : Tree) : node l r ≠ bot := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem node_ne_top (l r : Tree) : node l r ≠ top := by
  intro h
  have := congrArg (fun t : Tree => t.fn []) h
  simp at this

@[simp] theorem top_ne_bot : top ≠ bot := bot_ne_top.symm
@[simp] theorem bot_ne_node (l r : Tree) : bot ≠ node l r := (node_ne_bot l r).symm
@[simp] theorem top_ne_node (l r : Tree) : top ≠ node l r := (node_ne_top l r).symm

/-- Non-structural subtyping: labels are ordered at every path present in both trees. -/
def le (t u : Tree) : Prop :=
  ∀ π a b, t.fn π = some a → u.fn π = some b → a ≤ b

instance : LE Tree := ⟨Tree.le⟩

theorem le_refl (t : Tree) : t ≤ t := by
  intro π a b ha hb
  have : a = b := Option.some.inj (ha.symm.trans hb)
  exact this.le

theorem middle_isSome {t u v : Tree} (htu : t ≤ u) (huv : u ≤ v)
    (π : List (Fin 2)) (ht : (t.fn π).isSome) (hv : (v.fn π).isSome) :
    (u.fn π).isSome := by
  induction π using List.reverseRecOn with
  | nil => exact u.root_isSome
  | append_singleton π i ih =>
    have ht' := (t.child_isSome_iff π i).mp ht
    have hv' := (v.child_isSome_iff π i).mp hv
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih (by simp [ht']) (by simp [hv']))
    have hb' : b = Sym.f := _root_.le_antisymm (huv π b Sym.f hb hv')
      (htu π Sym.f b ht' hb)
    exact (u.child_isSome_iff π i).mpr (by simpa [hb'] using hb)

/-- Non-structural subtyping is transitive. -/
theorem le_trans {t u v : Tree} (htu : t ≤ u) (huv : u ≤ v) : t ≤ v := by
  intro π a c ha hc
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp
    (middle_isSome htu huv π (by simp [ha]) (by simp [hc]))
  exact _root_.le_trans (htu π a b ha hb) (huv π b c hb hc)

/-- Mutual non-structural subtyping identifies trees. -/
theorem le_antisymm {t u : Tree} (htu : t ≤ u) (hut : u ≤ t) : t = u := by
  have labels : ∀ π a b, t.fn π = some a → u.fn π = some b → a = b := by
    intro π a b ha hb
    exact _root_.le_antisymm (htu π a b ha hb) (hut π b a hb ha)
  apply ext
  funext π
  induction π using List.reverseRecOn with
  | nil =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp t.root_isSome
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp u.root_isSome
    rw [ha, hb, labels [] a b ha hb]
  | append_singleton π i ih =>
    have hd : (t.fn (π ++ [i])).isSome ↔ (u.fn (π ++ [i])).isSome := by
      rw [child_isSome_iff, child_isSome_iff, ih]
    cases ht : t.fn (π ++ [i]) <;> cases hu : u.fn (π ++ [i])
    · rfl
    · simp [ht, hu] at hd
    · simp [ht, hu] at hd
    · exact congrArg some (labels _ _ _ ht hu)

instance : PartialOrder Tree where
  le := Tree.le
  le_refl := Tree.le_refl
  le_trans := @Tree.le_trans
  le_antisymm := @Tree.le_antisymm

/-- Bottom is below every tree in the non-structural order. -/
@[simp] theorem bot_le (t : Tree) : bot ≤ t := by
  intro π a b ha hb
  cases π with
  | nil => simp only [bot_fn_nil, Option.some.injEq] at ha; subst a; exact Sym.bot_le b
  | cons i π => simp at ha

/-- Every tree is below top in the non-structural order. -/
@[simp] theorem le_top (t : Tree) : t ≤ top := by
  intro π a b ha hb
  cases π with
  | nil => simp only [top_fn_nil, Option.some.injEq] at hb; subst b; exact Sym.le_top a
  | cons i π => simp at hb

@[simp] theorem le_bot_iff (t : Tree) : t ≤ bot ↔ t = bot :=
  ⟨fun h => le_antisymm h (bot_le t), fun h => h ▸ le_refl bot⟩

@[simp] theorem top_le_iff (t : Tree) : top ≤ t ↔ t = top :=
  ⟨fun h => le_antisymm (le_top t) h, fun h => h ▸ le_refl top⟩

/-- Comparing constructor nodes is equivalent to comparing their children componentwise. -/
@[simp] theorem node_le_node_iff (l r l' r' : Tree) :
    node l r ≤ node l' r' ↔ l ≤ l' ∧ r ≤ r' := by
  constructor
  · intro h
    constructor
    · intro π a b ha hb
      exact h (0 :: π) a b (by simpa using ha) (by simpa using hb)
    · intro π a b ha hb
      exact h (1 :: π) a b (by simpa using ha) (by simpa using hb)
  · rintro ⟨hl, hr⟩ π a b ha hb
    cases π with
    | nil => simpa using (Option.some.inj (ha.symm.trans hb)).le
    | cons i π =>
      fin_cases i
      · exact hl π a b (by simpa using ha) (by simpa using hb)
      · exact hr π a b (by simpa using ha) (by simpa using hb)

/-- Subtyping is generated by bottom, top and covariant comparison of children. -/
theorem le_iff_root_cases (t u : Tree) :
    t ≤ u ↔ t = bot ∨ u = top ∨
      ∃ l r l' r', t = node l r ∧ u = node l' r' ∧ l ≤ l' ∧ r ≤ r' := by
  constructor
  · intro h
    rcases t.eq_bot_or_eq_top_or_node with ht | ht | ⟨l, r, rfl⟩
    · exact Or.inl ht
    · subst t
      exact Or.inr (Or.inl ((top_le_iff u).mp h))
    · rcases u.eq_bot_or_eq_top_or_node with hu | hu | ⟨l', r', rfl⟩
      · subst u
        exact False.elim (node_ne_bot l r ((le_bot_iff _).mp h))
      · exact Or.inr (Or.inl hu)
      · exact Or.inr (Or.inr ⟨l, r, l', r', rfl, rfl, (node_le_node_iff ..).mp h⟩)
  · rintro (rfl | rfl | ⟨l, r, l', r', rfl, rfl, hl, hr⟩)
    · exact bot_le u
    · exact le_top t
    · exact (node_le_node_iff ..).mpr ⟨hl, hr⟩

end Tree
end DeciNSSE
