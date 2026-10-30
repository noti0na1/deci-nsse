import DeciNSSE.Solver.Mask

/-! # Saturation of a bit matrix

The rows encode precisely the reflexive, transitive, constructor closure.
-/

namespace DeciNSSE.Solver
open Mask
attribute [-simp] BitVec.getLsbD_eq_getElem
variable {n k : ℕ}

abbrev Rows (k : ℕ) := Table k (BitVec k)

/-- Decode a bit matrix as a relation. -/
def relation (s : Rows k) : Finset (V k × V k) :=
  Finset.univ.filter fun p => (s p.1).getLsbD p.2 = true

@[simp] theorem mem_relation (s : Rows k) (x y : V k) :
    (x, y) ∈ relation s ↔ (s x).getLsbD y = true := by simp [relation]

/-- Decomposition rules grouped by the source child. -/
def rules (ϕ : Constraint n k) (x : V k) : List (V k × V k × V k) :=
  (lowerLits ϕ).flatMap fun l => (List.finRange n).flatMap fun i =>
    if l.1 i = x then (upperLits ϕ).map fun u => (l.2, u.1, u.2 i) else []

theorem mem_rules (ϕ : Constraint n k) (x u v y : V k) :
    (u, v, y) ∈ rules ϕ x ↔ ∃ a b i,
      Lit.fLe a u ∈ ϕ ∧ Lit.leF v b ∈ ϕ ∧ a i = x ∧ b i = y := by
  simp only [rules, List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨⟨a, u'⟩, hl, i, hi⟩
    split at hi <;> rename_i h
    · obtain ⟨⟨v', b⟩, hu, he⟩ := List.mem_map.mp hi
      cases he
      exact ⟨a, b, i, (mem_lowerLits ..).mp hl, (mem_upperLits ..).mp hu, h, rfl⟩
    · simp at hi
  · rintro ⟨a, b, i, hl, hu, hx, rfl⟩
    exact ⟨(a, u), (mem_lowerLits ..).mpr hl, i,
      by simp only [hx, ite_true]; exact List.mem_map.mpr ⟨(v, b), (mem_upperLits ..).mpr hu, rfl⟩⟩

/-- One simultaneous closure round. -/
def expandRows (rs : V k → List (V k × V k × V k)) (s : Rows k) : Rows k :=
  table fun x => s x ||| singleton x ||| image s (s x) |||
    union (rs x) (fun p => if (s p.1).getLsbD p.2.1 then singleton p.2.2 else BitVec.zero _)

theorem expandRows_spec (ϕ : Constraint n k) (s : Rows k) :
    relation (expandRows (rules ϕ) s) = Closure.expand ϕ (relation s) := by
  ext ⟨x, y⟩
  simp only [mem_relation, expandRows, table_eq, BitVec.getLsbD_or, Bool.or_eq_true,
    bit_singleton, bit_image, bit_union, Closure.mem_expand, mem_relation]
  have hr : (∃ p ∈ rules ϕ x,
      (if (s p.1).getLsbD p.2.1 then singleton p.2.2 else BitVec.zero _).getLsbD y = true) ↔
      ∃ a, ∃ u v : V k, ∃ b i, Lit.fLe a u ∈ ϕ ∧ (s u).getLsbD v = true ∧
        Lit.leF v b ∈ ϕ ∧ a i = x ∧ b i = y := by
    constructor
    · rintro ⟨⟨u, v, z⟩, hp, hb⟩
      split at hb <;> rename_i h
      · obtain rfl := bit_singleton _ _ |>.mp hb
        obtain ⟨a, b, i, hl, hu, hx, hy⟩ := (mem_rules ..).mp hp
        exact ⟨a, u, v, b, i, hl, h, hu, hx, hy⟩
      · simp at hb
    · rintro ⟨a, u, v, b, i, hl, h, hu, hx, hy⟩
      exact ⟨(u, v, y), (mem_rules ..).mpr ⟨a, b, i, hl, hu, hx, hy⟩,
        by simp [h]⟩
  rw [hr]
  simp only [or_assoc]

theorem relation_injective : Function.Injective (relation (k := k)) := by
  intro s t h
  apply Table.ext_fun
  funext x
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simpa only [mem_relation] using Finset.ext_iff.mp h (x, ⟨i, hi⟩)

/-- Saturation stops when no membership bit changes. -/
def closeRowsWith (ϕ : Constraint n k) (rs : Table k (List (V k × V k × V k)))
    (hrs : (rs : V k → List (V k × V k × V k)) = rules ϕ) (s : Rows k) : Rows k :=
  let t := expandRows rs s
  if _h : t = s then s else closeRowsWith ϕ rs hrs t
termination_by k * k - (relation s).card
decreasing_by
  simp only [t, hrs] at *
  have hne : relation (expandRows (rules ϕ) s) ≠ relation s :=
    fun he => _h (relation_injective he)
  rw [expandRows_spec] at *
  have hlt : (relation s).card < (Closure.expand ϕ (relation s)).card :=
    Finset.card_lt_card (lt_of_le_of_ne
    (Finset.subset_union_left : relation s ⊆ Closure.expand ϕ (relation s)) hne.symm)
  have hle := Finset.card_le_univ (s := Closure.expand ϕ (relation s))
  simp only [Fintype.card_prod, Fintype.card_fin] at hle
  change k * k - (Closure.expand ϕ (relation s)).card < k * k - (relation s).card
  omega

theorem closeRowsWith_spec (ϕ : Constraint n k) (rs : Table k (List (V k × V k × V k)))
    (hrs : (rs : V k → List (V k × V k × V k)) = rules ϕ) (s : Rows k) :
    relation (closeRowsWith ϕ rs hrs s) = Closure.close ϕ (relation s) := by
  fun_induction closeRowsWith ϕ rs hrs s with
  | case1 s t he =>
    simp only [t, hrs] at he
    have hfix := congrArg relation he
    rw [expandRows_spec] at hfix
    conv_rhs => rw [Closure.close]
    rw [ite_eq_left (show Closure.expand ϕ (relation s) ⊆ relation s by rw [hfix])]
  | case2 s t he ih =>
    simp only [t, hrs, expandRows_spec] at ih he ⊢
    rw [ih]
    conv_rhs => rw [Closure.close]
    split
    · rename_i hsub
      have heq := Finset.Subset.antisymm hsub Finset.subset_union_left
      exact (he (relation_injective ((expandRows_spec ϕ s).trans heq))).elim
    · rfl

/-- Reuse the decomposition table throughout saturation. -/
def closeRows (ϕ : Constraint n k) (s : Rows k) : Rows k :=
  closeRowsWith ϕ (table (rules ϕ)) (table_eq _) s

theorem closeRows_spec (ϕ : Constraint n k) (s : Rows k) :
    relation (closeRows ϕ s) = Closure.close ϕ (relation s) :=
  closeRowsWith_spec ϕ _ _ s

/-- Materialize constructor arguments before saturation. -/
def cacheLiteral : Lit n k → Lit n k
  | .leF x a => .leF x (table a)
  | .fLe a x => .fLe (table a) x
  | .eqBot x => .eqBot x
  | .eqTop x => .eqTop x

@[simp] theorem cacheLiteral_eq (l : Lit n k) : cacheLiteral l = l := by
  cases l <;> simp [cacheLiteral]

@[simp] theorem map_cacheLiteral (ϕ : Constraint n k) : ϕ.map cacheLiteral = ϕ := by
  induction ϕ with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, cacheLiteral_eq, ih]

/-- Compute the same closure with packed rows. -/
def derivedRows (ϕ : Constraint n k) : Rows k := closeRows (ϕ.map cacheLiteral) (table fun _ => BitVec.zero k)

theorem derivedRows_spec (ϕ : Constraint n k) : relation (derivedRows ϕ) = derivedPairs ϕ := by
  rw [derivedRows, closeRows_spec]
  rw [map_cacheLiteral]
  congr 1
  ext p
  simp [relation]

@[simp] theorem bit_derivedRows (ϕ : Constraint n k) (x y : V k) :
    (derivedRows ϕ x).getLsbD y = true ↔ Derives ϕ x y := by
  rw [← mem_relation, derivedRows_spec, mem_derivedPairs]

/-- Decode packed saturation for callers of the finite-set interface. -/
def derivedPairsFast (ϕ : Constraint n k) : Finset (V k × V k) := relation (derivedRows ϕ)

@[csimp] theorem derivedPairs_fast : @derivedPairs = @derivedPairsFast := by
  funext n k ϕ
  exact (derivedRows_spec ϕ).symm

end DeciNSSE.Solver
