import DeciNSSE.Coverage.TerminalCopy

/-! # Transport of word images across cuts

Deleting an interval between equal prefix images preserves the total image.
The prefix-product identity relates comparison endpoints to intervening factors.
-/

namespace DeciNSSE.Transport

open Words
open scoped TerminalCopy

variable {H : Type*} [Monoid H]

/-- Delete the interval between two positions of a word. -/
def cut (v : Word) (i j : ℕ) : Word := v.take i ++ v.drop j

/-- Cutting between equal prefix images preserves the whole word image. -/
theorem mu_cut_of_prefix {μ : Word →* H} {v : Word} {i j : ℕ}
    (h : μ (v.take i) = μ (v.take j)) : μ (cut v i j) = μ v := by
  rw [cut, TerminalCopy.map_append, h, ← TerminalCopy.map_append,
    List.take_append_drop]

theorem prefix_product (μ : Word →* H) (w : Word) (s p : ℕ) :
    μ (w.take s) * μ ((w.drop s).take p) = μ (w.take (s + p)) := by
  rw [List.take_add, TerminalCopy.map_append]

end DeciNSSE.Transport
