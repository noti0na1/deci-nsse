import DeciNSSE.Complexity.Unary
import DeciNSSE.Complexity.UnaryExamples
import DeciNSSE.Complexity.SummaryDecision
import DeciNSSE.Complexity.Hardness
import DeciNSSE.Complexity.ExpWitness

/-! # Complexity of non-structural subtype entailment

The combinatorial content behind the complexity bounds. The complexity classes
themselves (space-bounded machines, Savitch's theorem) are not formalized.

* **Summary search** (`Complexity.Summary`). A search over level summaries of the
  block hierarchy decides holes of bounded depth without storing the word.
  `summarySearch_sound` and `summarySearch_complete` prove it correct,
  `card_config_label_le` bounds its configurations by `2 ^ ((n + 1) ^ 2 * 2 ^ 2 ^ (20 * k + 20))`,
  and `decideEntailsSummary`, `decideEntailsRegSummary` and `decideEntailsFinSummary`
  decide entailment through it.
* **Arity one** (`Unary`). A reader over a one-letter alphabet with a hole has one of
  length at most `Fintype.card Q - 1` (`Unary.exists_hole_length_le`), and
  `decideEntailsUnary`, `decideEntailsRegUnary` and `decideEntailsFinUnary` search
  only that far.
* **Hardness** (`Complexity.Hardness`). For every arity `n ≥ 2` and the covariant
  constructor, `hardnessSystem n M` entails `x ≤ r` exactly when the binary automaton
  `M` is universal, in each domain (`entails_hardnessSystem_iff` and its regular and
  finite versions), with linearly many literals.
* **Long witnesses** (`Complexity.ExpWitness`). For every `n ≥ 2` and `k`, `expSystem n k`
  has `9 k + 31` variables and refutes entailment in each domain, and its shortest
  counterexample word has length exactly `2 (k + 1) 2 ^ k` (`expSystem_shortest`,
  `expSystem_shortest_hole`, `expSystem_result`).
-/
