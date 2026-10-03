import DeciNSSE.Coverage.EndToEnd
import DeciNSSE.Coverage.RealizedRoots

/-! # Periodic roots of an automaton

The root family associated with an automaton turns its language into
full coverage with a single family indexed by transition images.
-/

namespace DeciNSSE.AutomatonRoots

open Words FullCoverage

section Automata

open EndToEnd

variable {Q : Type} [Fintype Q] [DecidableEq Q]

abbrev automatonRoots (P : CapAutomaton Q) : Rel Q → Set (Rel Q) :=
  RealizedRoots.realizedRoots (transRel P) (EndToEnd.V P) (EndToEnd.U P)

theorem mem_lang_iff_singleton_fullCovered (P : CapAutomaton Q) (w : Word) :
    w ∈ P.Lang ↔ FullCovered (transRel P) (VA P) (fun h => {h}) (automatonRoots P) w :=
  (mem_lang_iff_fullCovered P w).trans
    (RealizedRoots.fullCovered_realized (transRel P) (EndToEnd.V P) (EndToEnd.U P) (VA P) w).symm

end Automata

end DeciNSSE.AutomatonRoots
