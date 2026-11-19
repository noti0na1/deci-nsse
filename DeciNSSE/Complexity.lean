import DeciNSSE.Complexity.Unary
import DeciNSSE.Complexity.UnaryExamples
import DeciNSSE.Complexity.SummaryDecision
import DeciNSSE.Complexity.Hardness
import DeciNSSE.Complexity.ExpWitness
import DeciNSSE.Complexity.RejectionExamples
import DeciNSSE.Shortening.Side
import DeciNSSE.Complexity.Tiling.Reduction

/-! # Complexity of non-structural subtype entailment

The combinatorial content behind the complexity bounds. The complexity classes
themselves (space-bounded machines, Savitch's theorem) are not formalized. The
variable count `k` is the number of variables of `Constraint n k`, at most the input size.
The headline declarations below give the witness and reduction results.

* **Singly exponential witnesses and decisions.** A side reader with a hole has one of
  length at most `2 ^ (512 * (k + 1) ^ 4)`, independently of arity and variance.
  - `DeciNSSE.Shortening.exists_shortening` (module `Shortening.Blocks`) shortens
    blocks simultaneously. `DeciNSSE.Shortening.exists_short_hole` (module
    `Shortening.Descent`) bounds the length after descent.
  - `DeciNSSE.Shortening.hole_iff_rpBound` and `DeciNSSE.Shortening.hole_iff_stoppingBound`
    (module `Shortening.Readers`) give the explicit-reader bounds.
    `DeciNSSE.Shortening.rpBound_le_pow_seven` and `DeciNSSE.Shortening.stoppingBound_le`
    bound the two allowances in terms of the state count.
  - `DeciNSSE.Shortening.hole_dichotomy` and `DeciNSSE.Shortening.short_hole_of_omega`
    (module `Shortening.Dichotomy`) handle periodic continuations. For dead ends,
    `DeciNSSE.Shortening.depth_le_of_deadEnd`, `DeciNSSE.Shortening.side_actionBound` and
    `DeciNSSE.Shortening.tower_actionBound` (module `Shortening.Side`) bound the depth
    and number of word actions.
  - `DeciNSSE.Shortening.sideHole_iff_bounded`, `DeciNSSE.Shortening.not_entails_iff_bounded`,
    `DeciNSSE.Shortening.not_entailsReg_iff_bounded` and
    `DeciNSSE.Shortening.not_entailsFin_iff_bounded` (module `Shortening.Side`) give the
    side bound and characterize non-entailment in all three domains.
  - `DeciNSSE.decideEntailsExp`, `DeciNSSE.decideEntailsRegExp` and
    `DeciNSSE.decideEntailsFinExp` (module `Shortening.Side`) enumerate bounded side holes.
    `DeciNSSE.decideEntailsExp_correct`, `DeciNSSE.decideEntailsRegExp_correct` and
    `DeciNSSE.decideEntailsFinExp_correct` prove the three decisions correct.
  Membership of non-entailment in NEXPTIME follows by guessing a side and a word and
  checking the witness. Its length bound and the correctness of bounded search are formalized.
  The running time of the witness check is not formalized.
* **Tiling reduction.** For every arity `n ≥ 2` and every variance, the emitted system
  is finitely satisfiable. For an initial word fitting row zero, its query holds in each domain
  exactly when the torus has no tiling with that word.
  - `DeciNSSE.Complexity.Tiling.bridge_iff` (module `Complexity.Tiling.Source`) reduces
    the torus with a fitting initial word to an open square with a succinct boundary.
  - `DeciNSSE.Complexity.Tiling.tilingReader_hole_iff` and
    `DeciNSSE.Complexity.Tiling.tilingReader_size` (module `Complexity.Tiling.Reader`)
    characterize the encodings of valid grids and bound the binary table size.
  - `DeciNSSE.Complexity.Tiling.emit_correct` and `DeciNSSE.Complexity.Tiling.lifted_holes`
    (module `Complexity.Tiling.Reduction`) realize the table by constraints at each variance.
    `DeciNSSE.Complexity.Tiling.tilingSystem_correct` and
    `DeciNSSE.Complexity.Tiling.tilingSystem_size` give correctness and size for the square.
    `DeciNSSE.Complexity.Tiling.torusSystem_correct` and
    `DeciNSSE.Complexity.Tiling.torusSystem_size` do so for the torus in the same module.
  - `DeciNSSE.Complexity.Tiling.initialWordSystem_correct` and
    `DeciNSSE.Complexity.Tiling.initialWordSystem_size` (module `Complexity.Tiling.Reduction`)
    give correctness and polynomial bounds on the numbers of variables and literals for
    the torus of side `2 ^ (w.length + 1)`.
  The NEXPTIME-hardness of that torus problem for a fixed domino system is cited from
  Tobies, Corollary 5.14. The source hardness and the polynomial running time of the reduction
  are not formalized. With these facts, non-entailment is NEXPTIME-complete and entailment
  is coNEXPTIME-complete for each such arity, variance and tree domain.

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
