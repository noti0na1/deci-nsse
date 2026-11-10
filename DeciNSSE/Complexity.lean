import DeciNSSE.Complexity.Unary
import DeciNSSE.Complexity.UnaryExamples
import DeciNSSE.Complexity.SummaryDecision
import DeciNSSE.Complexity.Hardness
import DeciNSSE.Complexity.ExpWitness
import DeciNSSE.Complexity.RejectionExamples

/-! # Complexity of non-structural subtype entailment

The combinatorial content behind the complexity bounds. The complexity classes
themselves (space-bounded machines, Savitch's theorem) are not formalized. The
headline declarations, with their fully qualified names and modules:

* **Summary search.** A search over level summaries of the block hierarchy
  decides holes of bounded depth without storing the word.
  - `DeciNSSE.Complexity.Summary.summarySearch_sound` (module `Complexity.SummarySound`)
    and `DeciNSSE.Complexity.Summary.summarySearch_complete`
    (module `Complexity.SummaryComplete`) prove it correct.
  - `DeciNSSE.Complexity.Summary.card_config_label_le` (module `Complexity.SummaryDecision`)
    bounds its configurations by `2 ^ ((n + 1) ^ 2 * 2 ^ 2 ^ (20 * k + 20))`.
  - `DeciNSSE.decideEntailsSummary`, `DeciNSSE.decideEntailsRegSummary` and
    `DeciNSSE.decideEntailsFinSummary` (module `Complexity.SummaryDecision`) decide
    entailment through it, with the correctness theorems
    `DeciNSSE.decideEntailsSummary_correct` and its two variants.
* **Arity one.** A reader over a one-letter alphabet with a hole has one of length at
  most `Fintype.card Q - 1`.
  - `DeciNSSE.Complexity.Unary.exists_hole_length_le` (module `Complexity.Unary`).
  - `DeciNSSE.decideEntailsUnary`, `DeciNSSE.decideEntailsRegUnary` and
    `DeciNSSE.decideEntailsFinUnary` (module `Complexity.Unary`) search only that far,
    with the correctness theorems `DeciNSSE.decideEntailsUnary_correct` and its two
    variants.
* **Hardness.** For every arity `n ≥ 2` and the covariant constructor,
  `DeciNSSE.Complexity.hardnessSystem n M` (module `Complexity.Hardness`) has
  linearly many literals and entails `x ≤ r` exactly when the binary automaton `M` is
  universal, in each domain.
  - `DeciNSSE.Complexity.entails_hardnessSystem_iff`,
    `DeciNSSE.Complexity.entailsReg_hardnessSystem_iff` and
    `DeciNSSE.Complexity.entailsFin_hardnessSystem_iff` (module `Complexity.Hardness`).
  - `DeciNSSE.Complexity.hardnessSystem_length_le` (module `Complexity.Hardness`).
* **Long witnesses.** For every `n ≥ 2` and `k`,
  `DeciNSSE.Complexity.expSystem n k` (module `Complexity.ExpWitness`) has `9 k + 31`
  variables and refutes entailment in each domain, and its shortest counterexample word
  has length exactly `2 (k + 1) 2 ^ k`.
  - `DeciNSSE.Complexity.expSystem_shortest_hole`,
    `DeciNSSE.Complexity.expSystem_shortest_refutesB` and
    `DeciNSSE.Complexity.expSystem_result` (module `Complexity.ExpWitness`).

The supporting modules are `Complexity.BinNFA` (binary automata),
`Complexity.AllFinalCode` (automata whose states are all final), `Complexity.Directions` and
`Complexity.FiniteTrees` (binary directions and finite trees), `Complexity.Counter`
and `Complexity.CounterBinary` (the counter automaton), and the `Complexity.Rejection*`
modules (the rejection system behind both `hardnessSystem` and `expSystem`). The modules
`Complexity.UnaryExamples` and `Complexity.RejectionExamples` hold checks only.
-/
