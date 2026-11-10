import DeciNSSE.Complexity.RejectionCountermodel
import DeciNSSE.Countermodels
import DeciNSSE.Solver.Checked

/-! # Holes and certificates of the rejection system

The rejection system is satisfiable, so the holes of its side readers, the words
passing the Boolean check `refutesB`, and the words of the refutations passing
the solver's packed checker are its unsafe words. If `A` accepts every word
without the prefix `W`, all of them extend `W`. If moreover all states of `A` are
final, `A` accepts exactly these words and `W` is nonempty, then they are exactly
the binary words that extend `W`, all on the right side.

## Main declarations
- `Rejection.hole_iff_unsafe`
- `Rejection.prefix_of_hole`, `Rejection.prefix_of_refutesB`,
  `Rejection.prefix_of_checkRefutationPacked`
- `Rejection.hole_iff`, `Rejection.refutesB_iff`, `Rejection.checkRefutationPacked_iff`
-/

namespace DeciNSSE.Complexity.Rejection

open Monitor Directions

variable {n m : ℕ} (hn : 2 ≤ n) {A : BinNFA m} {W : List (Fin 2)}

/-- The holes of the side readers are the unsafe words. -/
theorem hole_iff_unsafe (θ : Side) (w : List (Fin n)) :
    SideHole (fun _ => false) (rejectionSystem n A) xVar yVar θ w ↔
      Unsafe (fun _ => false) (rejectionSystem n A) xVar yVar θ w :=
  Monitor.hole_iff_unsafe (satisfiable_rejectionSystem A) θ w

/-- If `A` accepts every word without the prefix `W`, every hole extends `W`. -/
theorem prefix_of_hole (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side} {w : List (Fin n)}
    (h : SideHole (fun _ => false) (rejectionSystem n A) xVar yVar θ w) :
    W.map (embedDir hn) <+: w :=
  prefix_of_unsafe hn hA ((hole_iff_unsafe θ w).mp h)

/-- If `A` accepts every word without the prefix `W`, every word passing the Boolean
certificate check extends `W`. -/
theorem prefix_of_refutesB (hA : ∀ u, ¬ W <+: u → A.Accepts u) {θ : Side}
    {w : List (Fin n)}
    (h : refutesB (fun _ => false) (rejectionSystem n A) xVar yVar θ w = true) :
    W.map (embedDir hn) <+: w :=
  prefix_of_unsafe hn hA ((refutesB_iff_unsafe _ _ _ _ θ w).mp h)

/-- If `A` accepts every word without the prefix `W`, the word of every refutation passing
the solver's packed checker extends `W`. -/
theorem prefix_of_checkRefutationPacked (hA : ∀ u, ¬ W <+: u → A.Accepts u)
    {cert : Certificates.Refutation n}
    (h : Solver.Checked.checkRefutationPacked (fun _ => false) (rejectionSystem n A) xVar yVar
      cert = true) :
    W.map (embedDir hn) <+: cert.word :=
  prefix_of_refutesB hn hA
    ((Solver.Checked.checkRefutationPacked_eq_refutesB _ _ _ _ cert).symm.trans h)

variable (hfin : ∀ q, A.final q = true) (hW : W ≠ []) (hA : ∀ u, A.Accepts u ↔ ¬ W <+: u)
include hfin hW hA

/-- The left side has no hole, and the holes of the right side are exactly the binary
words that extend `W`. -/
theorem hole_iff (θ : Side) (w : List (Fin n)) :
    SideHole (fun _ => false) (rejectionSystem n A) xVar yVar θ w ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (embedDir hn) :=
  (hole_iff_unsafe θ w).trans (unsafe_iff hn hfin hW hA θ w)

/-- The words passing the Boolean certificate check are exactly the binary words that
extend `W`, on the right side. -/
theorem refutesB_iff (θ : Side) (w : List (Fin n)) :
    refutesB (fun _ => false) (rejectionSystem n A) xVar yVar θ w = true ↔
      θ = .r ∧ ∃ v, w = (W ++ v).map (embedDir hn) :=
  (refutesB_iff_unsafe _ _ _ _ θ w).trans (unsafe_iff hn hfin hW hA θ w)

/-- The refutations passing the solver's packed checker are exactly the right-side
refutations whose words extend `W`. -/
theorem checkRefutationPacked_iff (cert : Certificates.Refutation n) :
    Solver.Checked.checkRefutationPacked (fun _ => false) (rejectionSystem n A) xVar yVar
        cert = true ↔
      cert.side = .r ∧ ∃ v, cert.word = (W ++ v).map (embedDir hn) := by
  rw [Solver.Checked.checkRefutationPacked_eq_refutesB]
  exact refutesB_iff hn hfin hW hA cert.side cert.word

end DeciNSSE.Complexity.Rejection
