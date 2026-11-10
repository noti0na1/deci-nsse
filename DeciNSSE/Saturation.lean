import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-! # Saturation of finite sets

An operator on the finite subsets of a finite type is saturated from a set by
adding its image until nothing new appears. Each round strictly enlarges the
set, so the saturation stops; it stops at the first closed set, and the
computation never enumerates the type. The closure of a
constraint system saturates its rules. The reachable set of a vertex in a finite
graph, given by a step function `next : α → Finset α`, saturates the successors.

## Main declarations

- `saturate`, `saturate_spec`: the saturation of a finite set under an operator; it
  contains the set, is closed, and keeps every property that the operator preserves.
- `reachSet`, `mem_reachSet`: the saturation of one vertex under the successors, that
  is, the vertices reachable from it.
-/

namespace DeciNSSE.Saturation

variable {α : Type*} [DecidableEq α]

/-- Add the image of the operator until the set is closed under it. A recursive call
strictly enlarges the set, which is bounded by the type. -/
def saturate [Fintype α] (f : Finset α → Finset α) (S : Finset α) : Finset α :=
  if f S ⊆ S then S else saturate f (S ∪ f S)
termination_by Fintype.card α - S.card
decreasing_by
  rename_i hn
  have hs : S ⊂ S ∪ f S :=
    Finset.subset_union_left.ssubset_of_not_subset fun h =>
      hn (Finset.subset_union_right.trans h)
  have hlt := Finset.card_lt_card hs
  have hle := Finset.card_le_univ (S ∪ f S)
  omega

variable [Fintype α]

/-- Saturation contains its input, is closed, and keeps every property of elements that
the operator preserves. -/
theorem saturate_spec (f : Finset α → Finset α) (S : Finset α) :
    S ⊆ saturate f S ∧ f (saturate f S) ⊆ saturate f S ∧
      ∀ P : α → Prop, (∀ a ∈ S, P a) → (∀ S', (∀ a ∈ S', P a) → ∀ b ∈ f S', P b) →
        ∀ b ∈ saturate f S, P b := by
  fun_induction saturate f S with
  | case1 S hS => exact ⟨Finset.Subset.refl _, hS, fun _ hP _ => hP⟩
  | case2 S _ ih =>
    refine ⟨Finset.subset_union_left.trans ih.1, ih.2.1, fun P hP hstep => ih.2.2 P ?_ hstep⟩
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact hP b hb
    · exact hstep S hP b hb

/-- The vertices reachable from `a₀` along the step function, computed by saturation. -/
def reachSet (next : α → Finset α) (a₀ : α) : Finset α :=
  saturate (fun S => S.biUnion next) {a₀}

/-- The computed set is exactly the set of vertices reachable from `a₀`. -/
theorem mem_reachSet (next : α → Finset α) {a₀ b : α} :
    b ∈ reachSet next a₀ ↔ Relation.ReflTransGen (fun a b => b ∈ next a) a₀ b := by
  have spec := saturate_spec (fun S => S.biUnion next) {a₀}
  constructor
  · refine spec.2.2 _ (fun a ha => ?_) (fun S hS b hb => ?_) b
    · rw [Finset.mem_singleton.mp ha]
    · obtain ⟨a, ha, hab⟩ := Finset.mem_biUnion.mp hb
      exact (hS a ha).tail hab
  · intro h
    induction h with
    | refl => exact spec.1 (Finset.mem_singleton_self a₀)
    | tail _ hbc ih => exact spec.2.1 (Finset.mem_biUnion.mpr ⟨_, ih, hbc⟩)

end DeciNSSE.Saturation
