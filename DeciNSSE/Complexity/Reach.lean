import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! # Reachable sets in finite graphs

A step function `next : α → Finset α` on a finite type is a finite graph. The
reachable set of a vertex is computed by saturation: add all successors until
nothing new appears. Each round strictly enlarges the set, so the saturation
stops; it stops at the first closed set, and it never enumerates the vertex
type, which only needs to be `Finite`.

## Main declarations

- `saturate`: the saturation of a finite set under the step function.
- `reachSet`: the saturation of one vertex.
- `mem_reachSet`: membership in `reachSet next a₀` is reflexive-transitive
  reachability from `a₀` along `next`.
-/

namespace DeciNSSE.Complexity

variable {α : Type*} [DecidableEq α] (next : α → Finset α)

/-- Add all successors until the set is closed under the step function. A
recursive call strictly enlarges the set, which is bounded by the type. -/
def saturate [Finite α] (S : Finset α) : Finset α :=
  if S.biUnion next ⊆ S then S else saturate (S ∪ S.biUnion next)
termination_by Nat.card α - S.card
decreasing_by
  rename_i hn
  have : Fintype α := Fintype.ofFinite α
  have hs : S ⊂ S ∪ S.biUnion next :=
    Finset.subset_union_left.ssubset_of_not_subset fun h =>
      hn (Finset.subset_union_right.trans h)
  have hlt := Finset.card_lt_card hs
  have hle := Finset.card_le_univ (S ∪ S.biUnion next)
  rw [Nat.card_eq_fintype_card]
  omega

variable [Finite α]

/-- Saturation contains its input, is closed, and lies in every closed set
containing its input. -/
theorem saturate_spec (S : Finset α) :
    S ⊆ saturate next S ∧ (∀ a ∈ saturate next S, next a ⊆ saturate next S) ∧
      ∀ P : α → Prop, (∀ a ∈ S, P a) → (∀ a b, P a → b ∈ next a → P b) →
        ∀ b ∈ saturate next S, P b := by
  fun_induction saturate next S with
  | case1 S hS =>
    exact ⟨Finset.Subset.refl _, fun a ha => (Finset.subset_biUnion_of_mem next ha).trans hS,
      fun _ hP _ b hb => hP b hb⟩
  | case2 S _ ih =>
    refine ⟨Finset.subset_union_left.trans ih.1, ih.2.1, fun P hP hstep => ih.2.2 P ?_ hstep⟩
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hP b hb
    · obtain ⟨a, ha, hab⟩ := Finset.mem_biUnion.mp hb
      exact hstep a b (hP a ha) hab

/-- The vertices reachable from `a₀`, computed by saturation. -/
def reachSet (a₀ : α) : Finset α := saturate next {a₀}

/-- The computed set is exactly the set of vertices reachable from `a₀`. -/
theorem mem_reachSet {a₀ b : α} :
    b ∈ reachSet next a₀ ↔ Relation.ReflTransGen (fun a b => b ∈ next a) a₀ b := by
  have spec := saturate_spec next {a₀}
  constructor
  · refine spec.2.2 _ (fun a ha => ?_) (fun _ _ ha hb => ha.tail hb) b
    rw [Finset.mem_singleton.mp ha]
  · intro h
    induction h with
    | refl => exact spec.1 (Finset.mem_singleton_self a₀)
    | tail _ hbc ih => exact spec.2.1 _ ih hbc

end DeciNSSE.Complexity
