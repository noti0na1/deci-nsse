import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Fintype.Pigeonhole
import DeciNSSE.Words

/-! # Word images in finite monoids

Binary concatenation is the monoid operation on words. Powers in a finite
monoid eventually repeat, providing the algebraic basis for periodic coverage.
-/

namespace DeciNSSE.TerminalCopy

open Words

scoped instance : Monoid Word := inferInstanceAs (Monoid (FreeMonoid (Fin 2)))

variable {H : Type*} [Monoid H]

@[simp] theorem map_nil (μ : Word →* H) : μ [] = 1 := μ.map_one

@[simp] theorem map_append (μ : Word →* H) (u v : Word) :
    μ (u ++ v) = μ u * μ v := μ.map_mul u v

theorem exists_power_period [Fintype H] (a : H) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ Fintype.card H ∧
      ∀ n, Fintype.card H ≤ n → a^(n + ρ) = a^n := by
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card H + 1) => a^k.val) (by simp)
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have collision : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card H ∧ a^i = a^j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, by omega, he⟩
    · exact ⟨j, i, h, by omega, he.symm⟩
  obtain ⟨i, j, hij, hj, he⟩ := collision
  refine ⟨j - i, by omega, by omega, fun n hn => ?_⟩
  have h := congrArg (fun b : H => b * a^(n - i)) he
  simpa only [← _root_.pow_add, Nat.add_sub_of_le (show i ≤ n by omega),
    show j + (n - i) = n + (j - i) by omega] using h.symm

end DeciNSSE.TerminalCopy
