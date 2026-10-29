import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Logic.Equiv.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Convert
import Mathlib.Tactic.ByContra

/-! # Ordered tree labels

Bottom, constructor and top form the three-element chain of node labels.
-/

namespace DeciNSSE

/-- The three tree labels, ordered as bottom, constructor and top. -/
inductive Sym where
  | bot | f | top
  deriving DecidableEq, Repr

namespace Sym

/-- The numerical ranks give the signature its executable linear order. -/
def rank : Sym → Nat
  | bot => 0
  | f => 1
  | top => 2

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
