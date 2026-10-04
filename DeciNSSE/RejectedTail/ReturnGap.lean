import DeciNSSE.RejectedTail.Image

/-! # Return gaps forced by equal states

Deleting the interval of a comparison between equal transition images preserves
the image of the word and leaves a prefix. That prefix ends strictly after the
first rejection: equality at the first rejection would contradict the acceptance
of its predecessor. Thus the deleted interval has length at most `r - 1`, where
`r` is the rejected-tail length. The same bound holds for equal monitor states.
-/

namespace DeciNSSE.RejectedTail
open Words DerivedClass ConstructedAxioms
open scoped TerminalCopy

section Algebra
variable {H : Type*} [Monoid H] {μ : Word →* H} {VA : Set H} {D : Set (H × H)}

/-- Cutting at a comparison preserves the corresponding prefix of the word. -/
theorem comparison_cut_eq_take {w : Word} {s e : ℕ}
    (hse : s < e) (he : e ≤ w.length) (hp : w.drop e <+: w.drop s) :
    Transport.cut w s e = w.take (w.length - (e - s)) := by
  have hpre : Transport.cut w s e <+: w := by
    have hh := (List.prefix_append_right_inj (w.take s)).mpr hp
    simpa only [Transport.cut, List.take_append_drop] using hh
  have hlen : (Transport.cut w s e).length = w.length - (e - s) := by
    simp only [Transport.cut, List.length_append, List.length_take, List.length_drop]
    omega
  simpa only [hlen] using List.prefix_iff_eq_take.mp hpre

/--
Equal images at noninitial positions give the same ordinary acceptance at their predecessors.
-/
theorem equal_images_predecessors (ax : DerivedAxioms μ VA D) {w : Word} {i j : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hil : i ≤ w.length) (hjl : j ≤ w.length)
    (heq : μ (w.take i) = μ (w.take j)) :
    μ (w.take (i - 1)) ∈ VA ↔ μ (w.take (j - 1)) ∈ VA := by
  have hie : w.take i = w.take (i - 1) ++ [w[i - 1]] := by
    simpa only [Nat.sub_add_cancel hi] using
      (List.take_succ_eq_append_getElem (l := w) (by omega : i - 1 < w.length))
  have hje : w.take j = w.take (j - 1) ++ [w[j - 1]] := by
    simpa only [Nat.sub_add_cancel hj] using
      (List.take_succ_eq_append_getElem (l := w) (by omega : j - 1 < w.length))
  rw [hie, hje, TerminalCopy.map_append, TerminalCopy.map_append] at heq
  exact ax.shared _ _ _ _ heq

/--
Equal image states at a comparison force a return gap at most the rejected-tail length minus
one.
-/
theorem image_return_gap (ax : DerivedAxioms μ VA D) {w : Word} {J s e : ℕ}
    (hw : μ w ∉ VA) (hJ : IsFirstRejectedPrefix (imageReader μ) VAᶜ w J)
    (hse : s < e) (he : e ≤ w.length) (hp : w.drop e <+: w.drop s)
    (heq : μ (w.take s) = μ (w.take e)) :
    e - s ≤ (w.length - J) - 1 := by
  have hm : μ (w.take (w.length - (e - s))) = μ w := by
    rw [← comparison_cut_eq_take hse he hp]
    exact Transport.mu_cut_of_prefix heq
  have hmle : w.length - (e - s) ≤ w.length := Nat.sub_le _ _
  have hmlt : w.length - (e - s) < w.length := by omega
  have hmpos : 0 < w.length - (e - s) := by
    by_contra h
    have hz : w.length - (e - s) = 0 := by omega
    have hw1 : μ w = 1 := by simpa only [hz, List.take_zero, TerminalCopy.map_nil] using hm.symm
    have hz := ax.identity w hw1
    have := List.length_eq_zero_iff.mpr hz
    omega
  have hmJ : J ≤ w.length - (e - s) := by
    by_contra h
    exact hJ.2.2 (w.length - (e - s)) (by omega) (by simpa only [imageReader_eval, Set.mem_compl_iff, hm] using hw)
  have hstrict : J < w.length - (e - s) := by
    by_contra h
    have hmJ' : w.length - (e - s) = J := by omega
    have hJpos : 0 < J := by omega
    have hpred : μ (w.take (J - 1)) ∈ VA := by
      have hh := hJ.2.2 (J - 1) (by omega)
      simpa only [imageReader_eval, Set.mem_compl_iff, not_not] using hh
    have heq' : μ (w.take J) = μ (w.take w.length) := by
      simpa only [hmJ', List.take_length] using hm
    have hlast := (equal_images_predecessors ax hJpos (by omega)
      hJ.1 le_rfl heq').mp hpred
    have hreject : μ (w.take (w.length - 1)) ∉ VA :=
      rejected_between ax (by simpa only [imageReader_eval, Set.mem_compl_iff] using hJ.2.1)
        hw (List.take_prefix_take_left (by omega)) (List.take_prefix _ _)
    exact hreject hlast
  omega

end Algebra

section Literal
variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {d : Side}

@[simp] theorem monitor_eval_image (w : Word) :
    ((Bridge.monitor ϕ x y d).eval w).1 = imageμ ϕ x y d w := by
  induction w using List.reverseRecOn with
  | nil => simp [Bridge.monitor, DFA.eval]
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton]
    change ((Bridge.monitor ϕ x y d).eval w).1 * imageμ ϕ x y d [a] = _
    rw [ih, ← TerminalCopy.map_append]

/--
Equal monitor states at a comparison have displacement at most the rejected-tail length
minus one.
-/
theorem literal_return_gap {w : Word} {J s e : ℕ}
    (hw : imageμ ϕ x y d w ∉ imageVA ϕ x y d)
    (hJ : IsFirstRejectedPrefix (imageReader (imageμ ϕ x y d)) (imageVA ϕ x y d)ᶜ w J)
    (hse : s < e) (he : e ≤ w.length) (hp : w.drop e <+: w.drop s)
    (heq : (Bridge.monitor ϕ x y d).eval (w.take s) =
      (Bridge.monitor ϕ x y d).eval (w.take e)) : e - s ≤ (w.length - J) - 1 := by
  apply image_return_gap constructed_derivedAxioms hw hJ hse he hp
  simpa only [monitor_eval_image] using congrArg Prod.fst heq
end Literal
end DeciNSSE.RejectedTail
