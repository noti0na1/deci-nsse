import Mathlib.Algebra.Group.Submonoid.Basic
import DeciNSSE.Automata.ConstantFree
import DeciNSSE.Coverage.AutomatonRoots
import DeciNSSE.Monitor.DerivedAxioms

/-! # Admission properties of constraint automata

The constructed constraint automata satisfy the algebraic admission properties.
Restricting transition relations to the image of the word morphism gives
the finite monoid used by the monitors.
-/

namespace DeciNSSE.ConstructedAxioms
open Words CapAutomaton CState Construction EndToEnd
open scoped TerminalCopy

variable {k : ℕ} {ϕ : Constraint k} {x y : DeciNSSE.V k} {d : Side}

/-- The transition-relation morphism of a constructed side automaton. -/
abbrev μ (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :=
  transRel (construct ϕ x y d)

/-- The upper-variable coordinate of a transition relation. -/
def P (h : Rel (CState k)) (u v : DeciNSSE.V k) : Prop :=
  (pair (some u) none, pair (some v) none) ∈ h

/-- The lower-variable coordinate of a transition relation. -/
def Q (h : Rel (CState k)) (u v : DeciNSSE.V k) : Prop :=
  (pair none (some u), pair none (some v)) ∈ h

/-- The admitted prefix-image and root-image pairs of a constructed automaton. -/
def D (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    Set (Rel (CState k) × Rel (CState k)) :=
  {p | p.2 ∈ AutomatonRoots.automatonRoots (construct ϕ x y d) p.1}

theorem P_word {w : Word} {u v : DeciNSSE.V k} (hn : w ≠ []) :
    P (μ ϕ x y d w) u v ↔ UpperAt ϕ w u v := by
  change (_, _) ∈ transRel _ w ↔ _
  rw [mem_transRel_iff]
  constructor
  · intro h
    obtain ⟨a, ha, hp⟩ := runs_upper h rfl
    cases Option.some.inj ha
    exact hp
  · exact upperAt_run hn

theorem Q_word {w : Word} {u v : DeciNSSE.V k} (hn : w ≠ []) :
    Q (μ ϕ x y d w) u v ↔ LowerAt ϕ w v u := by
  change (_, _) ∈ transRel _ w ↔ _
  rw [mem_transRel_iff]
  constructor
  · intro h
    obtain ⟨a, ha, hp⟩ := runs_lower h rfl
    cases Option.some.inj ha
    exact hp
  · exact lowerAt_run hn

theorem cartesian (w : Word) (u v a b : DeciNSSE.V k) :
    (pair (some u) (some v), pair (some a) (some b)) ∈ μ ϕ x y d w ↔
      P (μ ϕ x y d w) u a ∧ Q (μ ϕ x y d w) v b := by
  by_cases hn : w = []
  · subst w
    simp [μ, P, Q, TerminalCopy.map_nil]
  · rw [P_word hn, Q_word hn, mem_transRel_iff]
    constructor
    · intro h
      obtain ⟨u', hu, hp⟩ := runs_upper h rfl
      obtain ⟨v', hv, hq⟩ := runs_lower h rfl
      cases Option.some.inj hu
      cases Option.some.inj hv
      exact ⟨hp, hq⟩
    · rintro ⟨hp, hq⟩
      exact Language.pair_run hn hp hq

theorem P_append (v w : Word) (a b : DeciNSSE.V k) :
    P (μ ϕ x y d (v ++ w)) a b ↔
      ∃ c, P (μ ϕ x y d v) a c ∧ P (μ ϕ x y d w) c b := by
  by_cases hv : v = []
  · subst v; simp [P, μ, TerminalCopy.map_nil]
  by_cases hw : w = []
  · subst w; simp [P, μ, TerminalCopy.map_nil]
  simp only [P_word (by simp [hv] : v ++ w ≠ []), P_word hv, P_word hw]
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ := UpperAt.factor h
    exact ⟨c, hc, hb⟩
  · rintro ⟨c, hc, hb⟩
    exact hc.comp hb

theorem Q_append (v w : Word) (a b : DeciNSSE.V k) :
    Q (μ ϕ x y d (v ++ w)) a b ↔
      ∃ c, Q (μ ϕ x y d v) a c ∧ Q (μ ϕ x y d w) c b := by
  by_cases hv : v = []
  · subst v; simp [Q, μ, TerminalCopy.map_nil]
  by_cases hw : w = []
  · subst w; simp [Q, μ, TerminalCopy.map_nil]
  simp only [Q_word (by simp [hv] : v ++ w ≠ []), Q_word hv, Q_word hw]
  constructor
  · intro h
    obtain ⟨c, hc, hb⟩ := LowerAt.factor h
    exact ⟨c, hc, hb⟩
  · rintro ⟨c, hc, hb⟩
    exact hb.comp hc

theorem mem_D_word (e : Rel (CState k)) (w : Word) :
    (e, μ ϕ x y d w) ∈ D ϕ x y d ↔
      ∃ q r, (pair (some x) (some y), q) ∈ e ∧
        (construct ϕ x y d).Runs q w r ∧ (construct ϕ x y d).pedge r q = true := by
  unfold D AutomatonRoots.automatonRoots
  simp only [Set.mem_ofPred_eq]
  rw [RealizedRoots.mem_realizedRoots]
  constructor
  · rintro ⟨⟨⟨r, q⟩, hp⟩, he, hw⟩
    exact ⟨q, r, he, (mem_transRel_iff _ _ _ _).mp hw, hp⟩
  · rintro ⟨q, r, he, hw, hp⟩
    exact ⟨⟨(r, q), hp⟩, he, (mem_transRel_iff _ _ _ _).mpr hw⟩

theorem left_loop (w : Word) (a b : DeciNSSE.V k) :
    (∃ s, (construct ϕ x y .l).Runs (pair (some a) (some b)) w
      (pair (some b) s)) ↔ P (μ ϕ x y .l w) a b := by
  by_cases hn : w = []
  · subst w; simp [P, μ, TerminalCopy.map_nil]
  rw [P_word hn]
  constructor
  · rintro ⟨s, h⟩
    cases s with
    | none => exact (ConstantFree.left_root_iff hn).mp h
    | some c => exact ((ConstantFree.left_pair_root_iff hn).mp h).1
  · intro h; exact ⟨none, (ConstantFree.left_root_iff hn).mpr h⟩

theorem right_loop (w : Word) (a b : DeciNSSE.V k) :
    (∃ s, (construct ϕ x y .r).Runs (pair (some a) (some b)) w
      (pair s (some a))) ↔ Q (μ ϕ x y .r w) b a := by
  by_cases hn : w = []
  · subst w; simp [Q, μ, TerminalCopy.map_nil, eq_comm]
  rw [Q_word hn]
  constructor
  · rintro ⟨s, h⟩
    cases s with
    | none => exact (ConstantFree.right_root_iff hn).mp h
    | some c => exact ((ConstantFree.right_pair_root_iff hn).mp h).2
  · intro h; exact ⟨none, (ConstantFree.right_root_iff hn).mpr h⟩

theorem endpoint_left (v w : Word) :
    (μ ϕ x y .l v, μ ϕ x y .l w) ∈ D ϕ x y .l ↔
      ∃ b, P (μ ϕ x y .l (v ++ w)) x b ∧ Q (μ ϕ x y .l v) y b := by
  rw [mem_D_word]
  constructor
  · rintro ⟨q, r, he, hw, hp⟩
    obtain ⟨a, b, s, rfl, rfl⟩ := Soundness.pedge_l_iff.mp hp
    obtain ⟨ha, hb⟩ := (cartesian v x y a b).mp he
    exact ⟨b, (P_append v w x b).mpr ⟨a, ha, (left_loop w a b).mp ⟨s, hw⟩⟩, hb⟩
  · rintro ⟨b, h, hb⟩
    obtain ⟨a, ha, hab⟩ := (P_append v w x b).mp h
    obtain ⟨s, hs⟩ := (left_loop w a b).mpr hab
    exact ⟨_, _, (cartesian v x y a b).mpr ⟨ha, hb⟩, hs,
      Soundness.pedge_l_iff.mpr ⟨a, b, s, rfl, rfl⟩⟩

theorem endpoint_right (v w : Word) :
    (μ ϕ x y .r v, μ ϕ x y .r w) ∈ D ϕ x y .r ↔
      ∃ a, P (μ ϕ x y .r v) x a ∧ Q (μ ϕ x y .r (v ++ w)) y a := by
  rw [mem_D_word]
  constructor
  · rintro ⟨q, r, he, hw, hp⟩
    obtain ⟨a, b, s, rfl, rfl⟩ := Soundness.pedge_r_iff.mp hp
    obtain ⟨ha, hb⟩ := (cartesian v x y a b).mp he
    exact ⟨a, ha, (Q_append v w y a).mpr ⟨b, hb, (right_loop w a b).mp ⟨s, hw⟩⟩⟩
  · rintro ⟨a, ha, h⟩
    obtain ⟨b, hb, hab⟩ := (Q_append v w y a).mp h
    obtain ⟨s, hs⟩ := (right_loop w a b).mpr hab
    exact ⟨_, _, (cartesian v x y a b).mpr ⟨ha, hb⟩, hs,
      Soundness.pedge_r_iff.mpr ⟨a, b, s, rfl, rfl⟩⟩

theorem endpoint_left_image {e h : Rel (CState k)}
    (he : e ∈ Set.range (μ ϕ x y .l)) (hh : h ∈ Set.range (μ ϕ x y .l)) :
    (e, h) ∈ D ϕ x y .l ↔ ∃ b, P (e * h) x b ∧ Q e y b := by
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hh
  simpa only [TerminalCopy.map_append] using endpoint_left v w

theorem endpoint_right_image {e h : Rel (CState k)}
    (he : e ∈ Set.range (μ ϕ x y .r)) (hh : h ∈ Set.range (μ ϕ x y .r)) :
    (e, h) ∈ D ϕ x y .r ↔ ∃ a, P e x a ∧ Q (e * h) y a := by
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hh
  simpa only [TerminalCopy.map_append] using endpoint_right v w

theorem constructed_E {e h h' : Rel (CState k)}
    (he : e ∈ Set.range (μ ϕ x y d)) (hh : h ∈ Set.range (μ ϕ x y d))
    (hh' : h' ∈ Set.range (μ ϕ x y d)) (heq : e * h = e * h') :
    (e, h) ∈ D ϕ x y d ↔ (e, h') ∈ D ϕ x y d := by
  obtain ⟨v, rfl⟩ := he
  obtain ⟨w, rfl⟩ := hh
  obtain ⟨w', rfl⟩ := hh'
  cases d
  · rw [endpoint_left, endpoint_left, TerminalCopy.map_append,
      TerminalCopy.map_append, heq]
  · rw [endpoint_right, endpoint_right, TerminalCopy.map_append,
      TerminalCopy.map_append, heq]

theorem move_final {q r : CState k} {i : Fin 2}
    (hm : Move ϕ i q r) (hg : ConstantFree.G d r) :
    (construct ϕ x y d).final q = true := by
  cases hm with
  | descend_left hu =>
    cases d with
    | l =>
      apply Bool.or_eq_true_iff.mpr; left
      simp only [childFinalB, decide_eq_true_eq, upperAtB_iff]
      exact ⟨i, _, hu⟩
    | r => simp [ConstantFree.G] at hg
  | descend_right hl =>
    cases d with
    | l => simp [ConstantFree.G] at hg
    | r =>
      apply Bool.or_eq_true_iff.mpr; left
      simp only [childFinalB, decide_eq_true_eq, lowerAtB_iff]
      exact ⟨i, _, hl⟩
  | descend_both hu hl =>
    cases d <;> apply Bool.or_eq_true_iff.mpr <;> left
    · simp only [childFinalB, decide_eq_true_eq, upperAtB_iff]; exact ⟨i, _, hu⟩
    · simp only [childFinalB, decide_eq_true_eq, lowerAtB_iff]; exact ⟨i, _, hl⟩
  | bot hd hb => exact Bool.or_eq_true_iff.mpr (Or.inr ((moveB_iff ..).mpr (.bot hd hb)))
  | top hd ht => exact Bool.or_eq_true_iff.mpr (Or.inr ((moveB_iff ..).mpr (.top hd ht)))
  | reflexivity hd => exact Bool.or_eq_true_iff.mpr (Or.inr ((moveB_iff ..).mpr (.reflexivity hd)))
  | all => rfl

theorem upper_child_letter {a b : DeciNSSE.V k} {i : Fin 2}
    (h : UpperAt ϕ [i] a b) (j : Fin 2) : ∃ c, UpperAt ϕ [j] a c := by
  obtain ⟨z, u, v, hz, hl, _⟩ := upperAt_singleton_iff i a b |>.mp h
  exact ⟨_, (upperAt_singleton_iff j a _).mpr ⟨z, u, v, hz, hl, .refl _⟩⟩

theorem lower_child_letter {a b : DeciNSSE.V k} {i : Fin 2}
    (h : LowerAt ϕ [i] b a) (j : Fin 2) : ∃ c, LowerAt ϕ [j] c a := by
  obtain ⟨z, u, v, hl, hz, _⟩ := lowerAt_singleton_iff i b a |>.mp h
  exact ⟨_, (lowerAt_singleton_iff j _ a).mpr ⟨z, u, v, hl, hz, .refl _⟩⟩

theorem final_iff_letter (q : CState k) (i : Fin 2) :
    (construct ϕ x y d).final q = true ↔
      ∃ r, Move ϕ i q r ∧ ConstantFree.G d r := by
  constructor
  · intro hf
    rcases Bool.or_eq_true_iff.mp hf with hc | hm
    · cases q with
      | all => exact ⟨all, .all, by cases d <;> simp [ConstantFree.G]⟩
      | pair a b =>
        cases d with
        | l =>
          cases a with
          | none => simp [childFinalB] at hc
          | some u =>
            obtain ⟨j, v, hj⟩ : ∃ j v, UpperAt ϕ [j] u v := by
              simpa [childFinalB, upperAtB_iff] using hc
            obtain ⟨v, hv⟩ := upper_child_letter hj i
            exact ⟨_, .descend_left hv, by simp [ConstantFree.G]⟩
        | r =>
          cases b with
          | none => simp [childFinalB] at hc
          | some v =>
            obtain ⟨j, u, hj⟩ : ∃ j u, LowerAt ϕ [j] u v := by
              simpa [childFinalB, lowerAtB_iff] using hc
            obtain ⟨u, hu⟩ := lower_child_letter hj i
            exact ⟨_, .descend_right hu, by simp [ConstantFree.G]⟩
    · exact ⟨all, Language.move_all_letter ((moveB_iff ..).mp hm) i,
        by cases d <;> simp [ConstantFree.G]⟩
  · rintro ⟨r, hm, hg⟩; exact move_final hm hg

theorem ordinary_iff_successor (h : Rel (CState k)) (i : Fin 2) :
    h ∈ VA (construct ϕ x y d) ↔
      ∃ r, (pair (some x) (some y), r) ∈ h * μ ϕ x y d [i] ∧ ConstantFree.G d r := by
  constructor
  · rintro ⟨q, hq, hf⟩
    obtain ⟨r, hm, hg⟩ := (final_iff_letter q i).mp hf
    exact ⟨r, (Rel.mem_mul ..).mpr ⟨q, hq,
      (mem_transRel_iff ..).mpr (.cons (mem_step_iff.mpr hm) (.nil _))⟩, hg⟩
  · rintro ⟨r, hr, hg⟩
    obtain ⟨q, hq, ht⟩ := (Rel.mem_mul ..).mp hr
    have ht := (mem_transRel_iff ..).mp ht
    obtain ⟨s, hs, he⟩ := (runs_cons_iff _).mp ht
    have he := (runs_nil_iff _).mp he
    subst s
    exact ⟨q, hq, move_final (mem_step_iff.mp hs) hg⟩

theorem constructed_S (h g : Rel (CState k)) (a b : Fin 2)
    (heq : h * μ ϕ x y d [a] = g * μ ϕ x y d [b]) :
    h ∈ VA (construct ϕ x y d) ↔ g ∈ VA (construct ϕ x y d) := by
  rw [ordinary_iff_successor h a, ordinary_iff_successor g b, heq]

/-- States with the coordinate selected by the side of the entailment comparison. -/
def Coordinate (d : Side) (r : CState k) : Prop :=
  match d with
  | .l => ∃ a, left r = some a
  | .r => ∃ b, right r = some b

theorem selected_run_final {q r : CState k} {w : Word} (hn : w ≠ [])
    (hr : (construct ϕ x y d).Runs q w r)
    (hc : Coordinate d r) :
    (construct ϕ x y d).final q = true := by
  cases w with
  | nil => exact (hn rfl).elim
  | cons i w =>
    obtain ⟨s, hs, ht⟩ := (runs_cons_iff _).mp hr
    apply move_final (mem_step_iff.mp hs)
    cases d with
    | l =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb, _⟩ := runs_upper ht ha
      cases s <;> simp_all [left, ConstantFree.G]
    | r =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨b, hb, _⟩ := runs_lower ht ha
      cases s <;> simp_all [right, ConstantFree.G]

theorem pedge_coordinate {q r : CState k}
    (hp : (construct ϕ x y d).pedge r q = true) :
    Coordinate d r := by
  cases d with
  | l => obtain ⟨a, b, s, rfl, rfl⟩ := Soundness.pedge_l_iff.mp hp; exact ⟨b, rfl⟩
  | r => obtain ⟨a, b, s, rfl, rfl⟩ := Soundness.pedge_r_iff.mp hp; exact ⟨a, rfl⟩

theorem constructed_entryFinal {e h : Rel (CState k)}
    (hd : (e, h) ∈ D ϕ x y d) : e ∈ VA (construct ϕ x y d) := by
  obtain ⟨w, rfl⟩ := RealizedRoots.realizedRoots_realized _ _ _ _ _ hd
  obtain ⟨q, r, he, hw, hp⟩ := (mem_D_word e w).mp hd
  refine ⟨q, he, ?_⟩
  by_cases hn : w = []
  · subst w
    have heq := (runs_nil_iff _).mp hw
    subst r
    exact Soundness.pedge_self_final hp
  · exact selected_run_final hn hw (pedge_coordinate hp)

theorem constructed_strictCap {e h f t : Rel (CState k)}
    (hd : (e, h) ∈ D ϕ x y d) (heq : f * t = h)
    (ht : t ∈ Set.range (μ ϕ x y d)) (hn : t ≠ 1) :
    e * f ∈ VA (construct ϕ x y d) := by
  obtain ⟨w, rfl⟩ := ht
  have hw : w ≠ [] := by rintro rfl; exact hn (TerminalCopy.map_nil _)
  obtain ⟨⟨⟨r, q⟩, hp⟩, he, hh⟩ := hd.1
  have hh : (q, r) ∈ f * μ ϕ x y d w := heq.symm ▸ hh
  obtain ⟨s, hf, hs⟩ := (Rel.mem_mul ..).mp hh
  exact ⟨s, (Rel.mem_mul ..).mpr ⟨q, he, hf⟩,
    selected_run_final hw ((mem_transRel_iff ..).mp hs) (pedge_coordinate hp)⟩

theorem constructed_identity (w : Word) (heq : μ ϕ x y d w = 1) : w = [] := by
  cases w with
  | nil => rfl
  | cons i w =>
    have hh : (pair none none, pair none none) ∈ μ ϕ x y d (i :: w) := by
      rw [heq]; exact (Rel.mem_one ..).mpr rfl
    obtain ⟨r, hr, _⟩ := (runs_cons_iff _).mp ((mem_transRel_iff ..).mp hh)
    have hm := mem_step_iff.mp hr
    cases hm

theorem final_without_G {q : CState k}
    (hf : (construct ϕ x y d).final q = true) (hg : ¬ ConstantFree.G d q) :
    Move ϕ 0 q all := by
  rcases Bool.or_eq_true_iff.mp hf with hc | hm
  · exfalso
    apply hg
    cases d <;> cases q with
    | all => simp [ConstantFree.G]
    | pair a b =>
      cases a <;> cases b <;> simp_all [childFinalB, ConstantFree.G]
  · exact (moveB_iff ..).mp hm

theorem sink_source_permanent {e : Rel (CState k)} {q : CState k}
    (he : (pair (some x) (some y), q) ∈ e) (hm : Move ϕ 0 q all)
    (w : Word) : e * μ ϕ x y d w ∈ VA (construct ϕ x y d) := by
  cases w with
  | nil =>
    rw [TerminalCopy.map_nil, mul_one]
    exact ⟨q, he, Bool.or_eq_true_iff.mpr (Or.inr ((moveB_iff ..).mpr hm))⟩
  | cons i w =>
    exact ⟨all, (Rel.mem_mul ..).mpr ⟨q, he, (mem_transRel_iff ..).mpr
      (.cons (mem_step_iff.mpr (Language.move_all_letter hm i)) (all_run w))⟩, rfl⟩

theorem constructed_gap {e : Rel (CState k)} {a : Fin 2}
    (he : e ∉ VA (construct ϕ x y d))
    (hea : e * μ ϕ x y d [a] ∈ VA (construct ϕ x y d))
    {t : Rel (CState k)} (ht : t ∈ Set.range (μ ϕ x y d)) :
    e * μ ϕ x y d [a] * t ∈ VA (construct ϕ x y d) := by
  obtain ⟨r, hr, hf⟩ := hea
  obtain ⟨q, hq, hqr⟩ := (Rel.mem_mul ..).mp hr
  have hqr := (mem_transRel_iff ..).mp hqr
  obtain ⟨s, hs, hsr⟩ := (runs_cons_iff _).mp hqr
  have hsr := (runs_nil_iff _).mp hsr
  subst s
  have hg : ¬ ConstantFree.G d r := fun hg => he ⟨q, hq, move_final (mem_step_iff.mp hs) hg⟩
  obtain ⟨w, rfl⟩ := ht
  exact sink_source_permanent hr (final_without_G hf hg) w

theorem pedge_self_sink {q : CState k}
    (hp : (construct ϕ x y d).pedge q q = true) : Move ϕ 0 q all := by
  cases d with
  | l =>
    obtain ⟨a, b, s, hq, he⟩ := Soundness.pedge_l_iff.mp hp
    rw [he] at hq
    have hab : a = b := by simpa [left] using congrArg left hq
    subst b
    rw [he]
    exact .reflexivity (.refl a)
  | r =>
    obtain ⟨a, b, s, hq, he⟩ := Soundness.pedge_r_iff.mp hp
    rw [he] at hq
    have hab : b = a := by simpa [right] using congrArg right hq
    subst b
    rw [he]
    exact .reflexivity (.refl a)

theorem constructed_emptyRoot {e t : Rel (CState k)}
    (hd : (e, 1) ∈ D ϕ x y d) (ht : t ∈ Set.range (μ ϕ x y d)) :
    e * t ∈ VA (construct ϕ x y d) := by
  have hd : (e, μ ϕ x y d []) ∈ D ϕ x y d := by simpa using hd
  obtain ⟨q, r, he, hw, hp⟩ := (mem_D_word e []).mp hd
  have hqr := (runs_nil_iff _).mp hw
  subst r
  obtain ⟨w, rfl⟩ := ht
  exact sink_source_permanent he (pedge_self_sink hp) w

/-- The submonoid of transition relations realised by words. -/
def imageMonoid (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    Submonoid (Rel (CState k)) where
  carrier := Set.range (μ ϕ x y d)
  one_mem' := ⟨[], TerminalCopy.map_nil _⟩
  mul_mem' := by
    rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, TerminalCopy.map_append _ u v⟩

/-- The finite monoid of realised transition relations for one side automaton. -/
abbrev Image (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) := imageMonoid ϕ x y d

instance imageFintype : Fintype (Image ϕ x y d) :=
  inferInstanceAs (Fintype {h : Rel (CState k) // h ∈ Set.range (μ ϕ x y d)})

/-- The word morphism restricted to its image monoid. -/
def imageμ (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) : Word →* Image ϕ x y d where
  toFun w := ⟨μ ϕ x y d w, ⟨w, rfl⟩⟩
  map_one' := Subtype.ext (TerminalCopy.map_nil _)
  map_mul' u v := Subtype.ext (map_mul _ u v)

/-- Ordinarily accepting elements of the transition-image monoid. -/
def imageVA (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) : Set (Image ϕ x y d) :=
  {e | e.val ∈ VA (construct ϕ x y d)}

/-- Admitted pairs restricted to the transition-image monoid. -/
def imageD (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    Set (Image ϕ x y d × Image ϕ x y d) := {p | (p.1.val, p.2.val) ∈ D ϕ x y d}

theorem imageμ_surjective : Function.Surjective (imageμ ϕ x y d) := by
  intro e
  obtain ⟨w, hw⟩ := e.property
  exact ⟨w, Subtype.ext hw⟩

/-- The constructed image monoid satisfies all algebraic admission properties. -/
theorem constructed_derivedAxioms :
    DerivedClass.DerivedAxioms (imageμ ϕ x y d) (imageVA ϕ x y d) (imageD ϕ x y d) where
  shared h g a b heq := constructed_S h.val g.val a b (congrArg Subtype.val heq)
  endpoint e h h' heq := constructed_E e.property h.property h'.property (congrArg Subtype.val heq)
  entry _e _h hd := constructed_entryFinal hd
  strictCap _e _h _f t hd heq _ hn := constructed_strictCap hd (congrArg Subtype.val heq)
    t.property (fun ht => hn (Subtype.ext ht))
  gap _e _a he hea t := constructed_gap he hea t.property
  emptyRoot _e hd t := constructed_emptyRoot hd t.property
  identity w heq := constructed_identity w (congrArg Subtype.val heq)

theorem mem_lang_iff_image_fullCovered (w : Word) :
    w ∈ (construct ϕ x y d).Lang ↔
      FullCoverage.FullCovered (imageμ ϕ x y d) (imageVA ϕ x y d)
        (fun h => {h}) (fun e => {h | (e, h) ∈ imageD ϕ x y d}) w := by
  rw [AutomatonRoots.mem_lang_iff_singleton_fullCovered]
  change FullCoverage.FullCovered (μ ϕ x y d) (VA (construct ϕ x y d))
    (fun h => {h}) (fun e => {h | (e, h) ∈ D ϕ x y d}) w ↔ _
  rw [DerivedClass.covered_iff_root, DerivedClass.covered_iff_root]
  rfl

instance constructedVAdecidable {k : ℕ} (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    DecidablePred (· ∈ ConstructedAxioms.imageVA ϕ x y d) :=
  fun e => inferInstanceAs (Decidable (e.val ∈ EndToEnd.VA (construct ϕ x y d)))

end DeciNSSE.ConstructedAxioms
