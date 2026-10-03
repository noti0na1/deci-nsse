import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-! # Tree labels

The labels bottom, the binary constructor and top form a three-element chain.
Their order determines the non-structural comparison of tree labels.
-/

namespace DeciNSSE

/-- The labels of a binary tree, ordered as bottom, constructor, top. -/
inductive Sym where
  | bot | f | top
  deriving DecidableEq, Repr

namespace Sym

/-- The numerical rank realising the three-element label order. -/
def rank : Sym → Nat
  | bot => 0
  | f => 1
  | top => 2

/-- Distinct tree labels have distinct ranks. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder Sym := LinearOrder.lift' rank rank_injective

@[simp] theorem bot_le (a : Sym) : bot ≤ a := by cases a <;> decide
@[simp] theorem le_top (a : Sym) : a ≤ top := by cases a <;> decide

@[simp] theorem le_bot_iff (a : Sym) : a ≤ bot ↔ a = bot := by
  cases a <;> decide

@[simp] theorem top_le_iff (a : Sym) : top ≤ a ↔ a = top := by
  cases a <;> decide

end Sym

end DeciNSSE
