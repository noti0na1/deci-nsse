import DeciNSSE.Monitor.Bridge
import DeciNSSE.RejectedTail.Basic

/-! # Eliminating caps from monitor holes

The transition-image reader has the same holes as the literal monitor.
The algebraic admission properties give its rejected-path and admission-cone
conditions, allowing tail bounds to be proved on transition images alone.
-/

namespace DeciNSSE.RejectedTail
open Words Holes DerivedClass
open scoped TerminalCopy

section Image
variable {H : Type*} [Monoid H]

/-- The deterministic reader multiplying the images of successive letters. -/
def imageReader (μ : Word →* H) : DFA (Fin 2) H where
  start := 1
  step q a := q * μ [a]
  accept := ∅

@[simp] theorem imageReader_eval (μ : Word →* H) (w : Word) :
    (imageReader μ).eval w = μ w := by
  induction w using List.reverseRecOn with
  | nil => simp [imageReader, DFA.eval]
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, ih]
    exact (μ.map_mul w [a]).symm

/-- Admission between endpoints when their images factor through an admitted pair. -/
def endpointRelation (D : Set (H × H)) (a b : H) : Prop :=
  ∃ t, a * t = b ∧ (a, t) ∈ D

variable {μ : Word →* H} {VA : Set H} {D : Set (H × H)}

theorem endpointRelation_cuts (ax : DerivedAxioms μ VA D) (w : Word)
    {s e : ℕ} (hse : s ≤ e) :
    endpointRelation D (μ (w.take s)) (μ (w.take e)) ↔
      (μ (w.take s), μ ((w.drop s).take (e - s))) ∈ D := by
  have he : μ (w.take s) * μ ((w.drop s).take (e - s)) = μ (w.take e) := by
    simpa only [Nat.add_sub_of_le hse] using Transport.prefix_product μ w s (e - s)
  constructor
  · rintro ⟨t, ht, hd⟩
    exact (ax.endpoint _ _ _ (ht.trans he.symm)).mp hd
  · intro hd
    exact ⟨_, he, hd⟩

theorem comparison_period {w : Word} {s e : ℕ} (hse : s ≤ e)
    (hp : w.drop e <+: w.drop s) : HasPeriod (w.drop s) (e - s) := by
  apply hasPeriod_iff_list_hasPeriod.mpr
  change w.drop s <+: (w.drop s).take (e - s) ++ w.drop s
  have hd : (w.drop s).drop (e - s) <+: w.drop s := by
    simpa only [List.drop_drop, Nat.add_sub_of_le hse] using hp
  have hh := (List.prefix_append_right_inj ((w.drop s).take (e - s))).mpr hd
  simpa only [List.take_append_drop] using hh

/-- An admitted comparison ends no later than a rejected prefix. -/
theorem image_cone_at_rejected (ax : DerivedAxioms μ VA D) {w : Word} {J s e : ℕ}
    (hw : μ w ∉ VA) (hJ : μ (w.take J) ∉ VA)
    (hse : s < e) (he : e ≤ w.length) (hp : w.drop e <+: w.drop s)
    (hr : endpointRelation D (μ (w.take s)) (μ (w.take e))) : s < J ∧ e ≤ J := by
  have hd := (endpointRelation_cuts ax w hse.le).mp hr
  have hb := cap_root_bound ax hJ
    (by simpa only [List.take_append_drop] using hw)
    (by simpa only [List.take_append_drop] using List.take_prefix J w)
    hd ((hasPeriod_iff_isPrefixOfPower_take (by omega)
      (by simp only [List.length_drop]; omega)).mp (comparison_period hse.le hp))
  simp only [List.length_take, List.length_drop,
    min_eq_left (show s ≤ w.length by omega),
    min_eq_left (show e - s ≤ w.length - s by omega)] at hb
  constructor <;> omega

/-- The image reader satisfies rejection persistence and the admission cone. -/
theorem image_rejectedPath (ax : DerivedAxioms μ VA D) :
    RejectedPath (imageReader μ) (endpointRelation D) VAᶜ where
  between := by
    intro v u w hvu huw hv hw
    simp only [imageReader_eval, Set.mem_compl_iff] at *
    exact rejected_between ax hv hw hvu huw
  cone := by
    intro w J hw hJ s e hse he hp hr
    simp only [imageReader_eval, Set.mem_compl_iff] at hw hr
    exact (image_cone_at_rejected ax hw (by simpa using hJ.2.1) hse he hp hr).2

/-- Cap elimination: holes of the image reader are exactly words without full coverage. -/
theorem image_hole_iff (ax : DerivedAxioms μ VA D) (w : Word) :
    IsReaderHole (imageReader μ) (endpointRelation D) VAᶜ w ↔
      ¬ FullCoverage.FullCovered μ VA (fun h => {h}) (fun e => {h | (e, h) ∈ D}) w := by
  rw [isReaderHole_iff, covered_iff_root]
  simp only [imageReader_eval, Set.mem_compl_iff]
  constructor
  · rintro ⟨hw, hn⟩ (ha | ⟨a, u, r, hwu, hd, hp⟩)
    · exact hw ha
    obtain ⟨hr, _, t, ht⟩ := cap_root_in_prefix ax hw
      (by simpa only [← hwu] using hw) (by rw [← hwu]) hd hp
    have hu : u = r ++ t := List.append_cancel_left (by
      simpa only [List.append_assoc, hwu] using ht)
    have hlen : a.length + r.length ≤ w.length := by simp [ht]
    apply hn a.length (a.length + r.length) (by have := List.length_pos_iff.mpr hr; omega) hlen
    · have hper : HasPeriod u r.length :=
        (hasPeriod_iff_isPrefixOfPower_take (List.length_pos_iff.mpr hr)
          (by simp [hu])).mpr (by simpa [hu] using hp)
      simpa [hwu, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right a.length r.length)] using
        (hasPeriod_iff_list_hasPeriod.mp hper).drop_prefix r.length
    · apply (endpointRelation_cuts ax w (by omega)).mpr
      simpa [hwu, hu, List.take_append, List.drop_append] using hd
  · intro hn
    have hw : μ w ∉ VA := fun ha => hn (Or.inl ha)
    refine ⟨hw, ?_⟩
    intro s e hse he hp hr
    apply hn
    right
    refine ⟨w.take s, w.drop s, (w.drop s).take (e - s),
      (List.take_append_drop s w).symm, (endpointRelation_cuts ax w hse.le).mp hr, ?_⟩
    exact (hasPeriod_iff_isPrefixOfPower_take (by omega)
      (by simp only [List.length_drop]; omega)).mp (comparison_period hse.le hp)

end Image

section NSSE
open ConstructedAxioms
variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {d : Side}

/-- The transition-image reader and the literal constraint monitor have the same holes. -/
theorem nsse_image_hole_iff (w : Word) :
    IsReaderHole (imageReader (imageμ ϕ x y d)) (endpointRelation (imageD ϕ x y d))
      (imageVA ϕ x y d)ᶜ w ↔
    IsReaderHole (Bridge.monitor ϕ x y d) Bridge.relation (Bridge.target ϕ x y d) w := by
  rw [image_hole_iff constructed_derivedAxioms,
    ← mem_lang_iff_image_fullCovered, Bridge.side_hole_iff]

/-- The constraint image reader satisfies the rejected-path conditions. -/
theorem nsse_rejectedPath :
    RejectedPath (imageReader (imageμ ϕ x y d))
      (endpointRelation (imageD ϕ x y d)) (imageVA ϕ x y d)ᶜ :=
  image_rejectedPath constructed_derivedAxioms

end NSSE
end DeciNSSE.RejectedTail
