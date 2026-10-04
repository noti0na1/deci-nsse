import DeciNSSE.Holes.Basic
import DeciNSSE.Monitor.ReaderProjection

/-! # Abstract monitors for coverage

A monitor records the current transition image and all visited variable readers.
Its target condition excludes ordinary and prefix-extension coverage; its
admission relation detects periodic comparisons. Thus rejected words are
exactly holes: target-reaching words with no admitted comparison.
-/

noncomputable section

namespace DeciNSSE.AbstractMonitor
open Words Dominance ConstructedAxioms ReaderProjection Holes

theorem hasPeriod_iff_terminal_prefix (w : Word) {s e : ℕ} (hse : s ≤ e) :
    HasPeriod (w.drop s) (e - s) ↔ w.drop e <+: w.drop s := by
  have h (v : Word) (p : ℕ) : HasPeriod v p ↔ v.drop p <+: v := by
    rw [hasPeriod_iff_list_hasPeriod]
    constructor
    · exact List.HasPeriod.drop_prefix p
    · intro hp
      change v <+: v.take p ++ v
      have he := (List.prefix_append_right_inj (v.take p)).mpr hp
      simpa using he
  simpa only [List.drop_drop, Nat.add_sub_of_le hse] using h (w.drop s) (e - s)

/-- The two sets of variables read from a transition image. -/
abbrev Reader (k : ℕ) := Set (V k) × Set (V k)

/-- An abstract monitor state: the current image and the finite set of visited readers. -/
abbrev Z {k : ℕ} (ϕ : Constraint k) (x y : V k) (d : Side) :=
  Image ϕ x y d × Finset (Reader k)

variable {k : ℕ} {ϕ : Constraint k} {x y : V k} {d : Side}

/-- All readers obtainable by extending a transition image. -/
def Reach (h : Image ϕ x y d) : Finset (Reader k) := by
  classical
  exact Finset.univ.image (fun g : Image ϕ x y d => reader (h * g))

theorem mem_Reach (h : Image ϕ x y d) (B : Reader k) :
    B ∈ Reach h ↔ ∃ t : Word, B = reader (h * imageμ ϕ x y d t) := by
  classical
  simp only [Reach, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨t, rfl⟩ := imageμ_surjective g
    exact ⟨t, hg.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨imageμ ϕ x y d t, rfl⟩

/-- Admission between the readers at two monitor states. -/
def R' (z z' : Z ϕ x y d) : Prop := SideAdm d (reader z.1) (reader z'.1)

/-- States excluding both ordinary acceptance and admitted prefix-extension coverage. -/
def T' (ϕ : Constraint k) (x y : V k) (d : Side) : Set (Z ϕ x y d) :=
  {z | z.1 ∉ imageVA ϕ x y d ∧
    ∀ A ∈ z.2, ∀ B ∈ Reach z.1, ¬ SideAdm d A B}

/-- The monitor recording the current transition image and all readers seen so far. -/
def monitor (ϕ : Constraint k) (x y : V k) (d : Side) : DFA (Fin 2) (Z ϕ x y d) := by
  classical
  exact {
    start := (1, {reader (1 : Image ϕ x y d)})
    step := fun z c =>
      (z.1 * imageμ ϕ x y d [c], insert (reader (z.1 * imageμ ϕ x y d [c])) z.2)
    accept := T' ϕ x y d }

/-- The readers at all prefix positions of a word, including both endpoints. -/
def visited (ϕ : Constraint k) (x y : V k) (d : Side) (w : Word) : Finset (Reader k) := by
  classical
  exact (Finset.range (w.length + 1)).image (fun s => reader (imageμ ϕ x y d (w.take s)))

/-- The monitor computes the word image together with exactly its visited readers. -/
theorem monitor_eval (w : Word) :
    (monitor ϕ x y d).eval w = (imageμ ϕ x y d w, visited ϕ x y d w) := by
  classical
  induction w using List.reverseRecOn with
  | nil => simp [monitor, visited, TerminalCopy.map_nil]
  | append_singleton w c ih =>
    rw [DFA.eval_append_singleton, ih]
    apply Prod.ext
    · simp [monitor, TerminalCopy.map_append]
    · change insert (reader (imageμ ϕ x y d w * imageμ ϕ x y d [c]))
        (visited ϕ x y d w) = visited ϕ x y d (w ++ [c])
      simp only [visited, List.length_append, List.length_singleton]
      rw [Finset.range_add_one (n := w.length + 1), Finset.image_insert]
      rw [← TerminalCopy.map_append]
      have hend : (w ++ [c]).take (w.length + 1) = w ++ [c] := by
        exact List.take_of_length_le (by simp)
      rw [hend]
      congr 1
      apply Finset.image_congr
      intro s hs
      have hs' : s ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
      simp only [List.take_append_of_le_length hs']

theorem mem_visited (w : Word) (A : Reader k) :
    A ∈ visited ϕ x y d w ↔
      ∃ s, s ≤ w.length ∧ A = reader (imageμ ϕ x y d (w.take s)) := by
  classical
  simp only [visited, Finset.mem_image, Finset.mem_range, Nat.lt_succ_iff]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

theorem run_image (w : Word) (s : ℕ) :
    (runPrefix (monitor ϕ x y d) w s).1 = imageμ ϕ x y d (w.take s) := by
  simp only [runPrefix, monitor_eval]

/-- A comparison whose two prefix readers form an admitted pair. -/
def SidePeriodic (ϕ : Constraint k) (x y : V k) (d : Side) (w : Word) : Prop :=
  ∃ s e, s < e ∧ e ≤ w.length ∧
    SideAdm d (reader (imageμ ϕ x y d (w.take s)))
      (reader (imageμ ϕ x y d (w.take e))) ∧ w.drop e <+: w.drop s

/-- Periodic admission is precisely a witnessed admitted pair of monitor states. -/
theorem periodic_part (w : Word) :
    SidePeriodic ϕ x y d w ↔
      ∃ p q, WitnessedPair (monitor ϕ x y d) w p q ∧ R' p q := by
  constructor
  · rintro ⟨s, e, hse, he, ha, hp⟩
    refine ⟨runPrefix (monitor ϕ x y d) w s, runPrefix (monitor ϕ x y d) w e,
      ⟨s, e, hse, he, rfl, rfl, hp⟩, ?_⟩
    simpa only [R', run_image] using ha
  · rintro ⟨p, q, ⟨s, e, hse, he, rfl, rfl, hp⟩, ha⟩
    exact ⟨s, e, hse, he, by simpa only [R', run_image] using ha, hp⟩

/-- Ordinary acceptance or admission witnessed by a prefix and an extension. -/
def RegularCovered (ϕ : Constraint k) (x y : V k) (d : Side) (w : Word) : Prop :=
  imageμ ϕ x y d w ∈ imageVA ϕ x y d ∨
    (ProjectPair reader '' CovPr (imageμ ϕ x y d) w ∩
      {AB | SideAdm d AB.1 AB.2}).Nonempty

theorem prefix_part (w : Word) :
    (ProjectPair reader '' CovPr (imageμ ϕ x y d) w ∩
      {AB | SideAdm d AB.1 AB.2}).Nonempty ↔
    ∃ A ∈ visited ϕ x y d w, ∃ B ∈ Reach (imageμ ϕ x y d w), SideAdm d A B := by
  rw [project_covPr_eq_prod]
  constructor
  · rintro ⟨⟨A, B⟩, ⟨hA, ⟨t, ht⟩⟩, ha⟩
    refine ⟨A, (mem_visited w A).mpr hA, B, (mem_Reach _ B).mpr ⟨t, ?_⟩, ha⟩
    simpa only [TerminalCopy.map_append] using ht
  · rintro ⟨A, hA, B, hB, ha⟩
    obtain ⟨t, ht⟩ := (mem_Reach _ B).mp hB
    refine ⟨(A, B), ⟨(mem_visited w A).mp hA, ⟨t, ?_⟩⟩, ha⟩
    simpa only [TerminalCopy.map_append] using ht

/-- Regular coverage is the complement of the monitor's target condition. -/
theorem regular_part (w : Word) :
    RegularCovered ϕ x y d w ↔ (monitor ϕ x y d).eval w ∉ T' ϕ x y d := by
  classical
  rw [RegularCovered, prefix_part, monitor_eval]
  change (_ ∨ ∃ A ∈ visited ϕ x y d w, ∃ B ∈ Reach (imageμ ϕ x y d w),
    SideAdm d A B) ↔ ¬ (_ ∧ _)
  constructor
  · rintro (ha | ⟨A, hA, B, hB, ha⟩) ht
    · exact ht.1 ha
    · exact ht.2 A hA B hB ha
  · intro hn
    by_cases ha : imageμ ϕ x y d w ∈ imageVA ϕ x y d
    · exact Or.inl ha
    · right
      by_contra hc
      exact hn ⟨ha, fun A hA B hB hab => hc ⟨A, hA, B, hB, hab⟩⟩

theorem proper_periodic_part (w : Word) :
    (ProjectPair reader '' CovPer (imageμ ϕ x y d) w ∩
      {AB | SideAdm d AB.1 AB.2}).Nonempty ↔
    ∃ s e, s < e ∧ e < w.length ∧
      SideAdm d (reader (imageμ ϕ x y d (w.take s)))
        (reader (imageμ ϕ x y d (w.take e))) ∧ w.drop e <+: w.drop s := by
  rw [project_covPer]
  constructor
  · rintro ⟨_, ⟨s, p, hp, hl, hper, rfl⟩, ha⟩
    refine ⟨s, s + p, by omega, by omega, ha, ?_⟩
    apply (hasPeriod_iff_terminal_prefix w (by omega)).mp
    simpa using hper
  · rintro ⟨s, e, hse, he, ha, hp⟩
    refine ⟨(reader (imageμ ϕ x y d (w.take s)),
      reader (imageμ ϕ x y d (w.take e))),
      ⟨s, e - s, by omega, by omega,
        (hasPeriod_iff_terminal_prefix w hse.le).mpr hp, ?_⟩, ha⟩
    rw [Nat.add_sub_of_le hse.le]

theorem endpoint_regular {w : Word} {s : ℕ} (hs : s ≤ w.length)
    (ha : SideAdm d (reader (imageμ ϕ x y d (w.take s)))
      (reader (imageμ ϕ x y d w))) : RegularCovered ϕ x y d w := by
  apply Or.inr
  rw [prefix_part]
  refine ⟨_, (mem_visited w _).mpr ⟨s, hs, rfl⟩, _,
    (mem_Reach _ _).mpr ⟨[], ?_⟩, ha⟩
  simp only [TerminalCopy.map_nil, mul_one]

/-- Automaton acceptance splits into regular coverage and admitted comparisons. -/
theorem covered_iff_regular_or_periodic (w : Word) :
    w ∈ (construct ϕ x y d).Lang ↔
      RegularCovered ϕ x y d w ∨ SidePeriodic ϕ x y d w := by
  rw [mem_lang_iff_proj]
  constructor
  · rintro (ha | ⟨AB, hc, ha⟩)
    · exact Or.inl (Or.inl ha)
    · change AB ∈ ProjectPair reader '' (CovPr (imageμ ϕ x y d) w ∪
        CovPer (imageμ ϕ x y d) w) at hc
      rw [Set.image_union] at hc
      rcases hc with hc | hc
      · exact Or.inl (Or.inr ⟨AB, hc, ha⟩)
      · obtain ⟨s, e, hse, he, hadm, hp⟩ :=
          (proper_periodic_part w).mp ⟨AB, hc, ha⟩
        exact Or.inr ⟨s, e, hse, he.le, hadm, hp⟩
  · rintro (hr | ⟨s, e, hse, he, ha, hp⟩)
    · rcases hr with ha | ⟨AB, ⟨q, hq, hAB⟩, ha⟩
      · exact Or.inl ha
      · exact Or.inr ⟨AB, ⟨q, Or.inl hq, hAB⟩, ha⟩
    · by_cases hend : e = w.length
      · subst e
        rw [List.take_length] at ha
        obtain ha | ⟨AB, ⟨q, hq, hAB⟩, ha⟩ := endpoint_regular hse.le ha
        · exact Or.inl ha
        · exact Or.inr ⟨AB, ⟨q, Or.inl hq, hAB⟩, ha⟩
      · obtain ⟨AB, ⟨q, hq, hAB⟩, ha⟩ := (proper_periodic_part w).mpr
          ⟨s, e, hse, by omega, ha, hp⟩
        exact Or.inr ⟨AB, ⟨q, Or.inr hq, hAB⟩, ha⟩

/-- A word is rejected by the side automaton exactly when it is a monitor hole. -/
theorem side_hole_iff_absHole (w : Word) :
    w ∉ (construct ϕ x y d).Lang ↔
      IsReaderHole (monitor ϕ x y d) R' (T' ϕ x y d) w := by
  classical
  rw [covered_iff_regular_or_periodic, regular_part, periodic_part]
  change ¬ ((monitor ϕ x y d).eval w ∉ T' ϕ x y d ∨
      ∃ p q, WitnessedPair (monitor ϕ x y d) w p q ∧ R' p q) ↔
    runPrefix (monitor ϕ x y d) w w.length ∈ T' ϕ x y d ∧ _
  simp only [runPrefix, List.take_length, not_or, not_not, not_exists, not_and]

end DeciNSSE.AbstractMonitor
