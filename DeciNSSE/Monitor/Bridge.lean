import DeciNSSE.Monitor.AbstractMonitor

/-! # Finite monitors and the entailment bridge

Finite sets represent the variable readers and their visited history.
This gives computable finite monitors with the same holes as the abstract
monitors. Entailment holds exactly when the constraints are unsatisfiable
or both side monitors have no hole.
-/

namespace DeciNSSE.Bridge

open Words ConstructedAxioms Holes

/-- A pair of finite sets of variables, giving a computable reader representation. -/
abbrev Reader (k : ℕ) := Finset (DeciNSSE.V k) × Finset (DeciNSSE.V k)

/-- The current transition image paired with the finite set of readers already visited. -/
abbrev State {k : ℕ} (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :=
  Image ϕ x y d × Finset (Reader k)

variable {k : ℕ} {ϕ : Constraint k} {x y : DeciNSSE.V k} {d : Side}

/-- The two finite sets of reachable variables associated with a transition image. -/
def reader (h : Image ϕ x y d) : Reader k :=
  (Finset.univ.filter (fun b => (CState.pair (some x) none,
      CState.pair (some b) none) ∈ h.val),
   Finset.univ.filter (fun b => (CState.pair none (some y),
      CState.pair none (some b)) ∈ h.val))

/-- Embed finite-set readers into the set-valued abstract readers. -/
def readerEmbedding (k : ℕ) : Reader k ↪ AbstractMonitor.Reader k where
  toFun A := (↑A.1, ↑A.2)
  inj' := by
    intro A B h
    apply Prod.ext
    · exact Finset.coe_injective (congrArg Prod.fst h)
    · exact Finset.coe_injective (congrArg Prod.snd h)

theorem readerEmbedding_apply (A : Reader k) :
    readerEmbedding k A = (↑A.1, ↑A.2) := rfl

@[simp] theorem readerEmbedding_reader (h : Image ϕ x y d) :
    readerEmbedding k (reader h) = ReaderProjection.reader h := by
  apply Prod.ext <;> ext b <;>
    simp [readerEmbedding_apply, reader, ReaderProjection.reader, P, Q]

/-- Enumerate the readers reachable by extending the current transition image. -/
def reach (h : Image ϕ x y d) : Finset (Reader k) :=
  Finset.univ.image (fun g : Image ϕ x y d => reader (h * g))

/-- The side-dependent intersection test for admitting two readers. -/
def adm (d : Side) (A B : Reader k) : Prop :=
  match d with
  | .l => (A.2 ∩ B.1).Nonempty
  | .r => (A.1 ∩ B.2).Nonempty

instance admDecidable (d : Side) (A B : Reader k) : Decidable (adm d A B) := by
  cases d <;> unfold adm <;> infer_instance

@[simp] theorem adm_iff (d : Side) (A B : Reader k) :
    adm d A B ↔ ReaderProjection.SideAdm d (readerEmbedding k A)
      (readerEmbedding k B) := by
  cases d <;> simp [adm, ReaderProjection.SideAdm, ReaderProjection.Adm,
    ReaderProjection.AdmRight, readerEmbedding_apply,
    Finset.Nonempty, Set.Nonempty]

/-- Admission between two states of the finite monitor. -/
def relation (z z' : State ϕ x y d) : Prop := adm d (reader z.1) (reader z'.1)

instance relationDecidable : DecidableRel (relation (ϕ := ϕ) (x := x) (y := y) (d := d)) :=
  fun _ _ => admDecidable _ _ _

/-- Monitor states with neither ordinary acceptance nor an admitted prefix extension. -/
def target (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) : Set (State ϕ x y d) :=
  {z | z.1.val ∉ EndToEnd.VA (construct ϕ x y d) ∧
    ∀ A ∈ z.2, ∀ B ∈ reach z.1, ¬ adm d A B}

instance targetDecidable : DecidablePred (· ∈ target ϕ x y d) :=
  fun z => inferInstanceAs (Decidable (z.1.val ∉ EndToEnd.VA (construct ϕ x y d) ∧
    ∀ A ∈ z.2, ∀ B ∈ reach z.1, ¬ adm d A B))

/-- The computable finite monitor for one side of a proposed entailment. -/
def monitor (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    DFA (Fin 2) (State ϕ x y d) where
  start := (1, {reader (1 : Image ϕ x y d)})
  step z c := (z.1 * imageμ ϕ x y d [c],
    insert (reader (z.1 * imageμ ϕ x y d [c])) z.2)
  accept := target ϕ x y d

/-- Interpret a finite monitor state as an abstract monitor state. -/
def toAbstract (z : State ϕ x y d) : AbstractMonitor.Z ϕ x y d :=
  (z.1, z.2.map (readerEmbedding k))

theorem reach_map (h : Image ϕ x y d) :
    (reach h).map (readerEmbedding k) = AbstractMonitor.Reach h := by
  classical
  ext A
  simp only [reach, AbstractMonitor.Reach, Finset.mem_map, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, hA⟩
    exact ⟨g, by simpa using hA⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, ⟨g, rfl⟩, readerEmbedding_reader _⟩

/-- The computable and abstract target conditions agree. -/
theorem target_iff (z : State ϕ x y d) :
    z ∈ target ϕ x y d ↔ toAbstract z ∈ AbstractMonitor.T' ϕ x y d := by
  classical
  change (_ ∧ _) ↔ (z.1 ∉ imageVA ϕ x y d ∧
    ∀ A ∈ z.2.map (readerEmbedding k),
      ∀ B ∈ AbstractMonitor.Reach z.1, ¬ ReaderProjection.SideAdm d A B)
  rw [← reach_map]
  apply and_congr Iff.rfl
  constructor
  · intro h A hA B hB
    obtain ⟨A, hA', rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨B, hB', rfl⟩ := Finset.mem_map.mp hB
    exact fun ha => h A hA' B hB' ((adm_iff d A B).mpr ha)
  · intro h A hA B hB ha
    exact h _ (Finset.mem_map.mpr ⟨A, hA, rfl⟩)
      _ (Finset.mem_map.mpr ⟨B, hB, rfl⟩) ((adm_iff d A B).mp ha)

@[simp] theorem relation_iff (z z' : State ϕ x y d) :
    relation z z' ↔ AbstractMonitor.R' (toAbstract z) (toAbstract z') := by
  simp [relation, AbstractMonitor.R', toAbstract]

theorem toAbstract_start :
    toAbstract (monitor ϕ x y d).start = (AbstractMonitor.monitor ϕ x y d).start := by
  classical
  simp [toAbstract, monitor, AbstractMonitor.monitor]

theorem toAbstract_step (z : State ϕ x y d) (c : Fin 2) :
    toAbstract ((monitor ϕ x y d).step z c) =
      (AbstractMonitor.monitor ϕ x y d).step (toAbstract z) c := by
  classical
  simp [toAbstract, monitor, AbstractMonitor.monitor]

/-- Evaluation commutes with interpreting finite states as abstract states. -/
theorem toAbstract_eval (w : Word) :
    toAbstract ((monitor ϕ x y d).eval w) = (AbstractMonitor.monitor ϕ x y d).eval w := by
  induction w using List.reverseRecOn with
  | nil => exact toAbstract_start
  | append_singleton w c ih =>
    rw [DFA.eval_append_singleton, toAbstract_step, ih, DFA.eval_append_singleton]

/-- A hole is equivalently a target word with no admitted suffix comparison. -/
theorem hole_iff_cuts {Q : Type*} (M : DFA (Fin 2) Q) (R : Q → Q → Prop)
    (T : Set Q) (w : Word) :
    AbsHoleG M R T w ↔ M.eval w ∈ T ∧
      ∀ s e, s < e → e ≤ w.length → w.drop e <+: w.drop s →
        ¬ R (M.eval (w.take s)) (M.eval (w.take e)) := by
  constructor
  · rintro ⟨ht, hn⟩
    refine ⟨by simpa [runG] using ht, ?_⟩
    intro s e hse he hp
    exact hn _ _ ⟨s, e, hse, he, rfl, rfl, hp⟩
  · rintro ⟨ht, hn⟩
    refine ⟨by simpa [runG] using ht, ?_⟩
    rintro p q ⟨s, e, hse, he, rfl, rfl, hp⟩
    exact hn s e hse he hp

/-- The finite and abstract monitors have the same holes. -/
theorem hole_iff_abstract (w : Word) :
    AbsHoleG (monitor ϕ x y d) relation (target ϕ x y d) w ↔
      Holes.AbsHole (AbstractMonitor.monitor ϕ x y d)
        AbstractMonitor.R' (AbstractMonitor.T' ϕ x y d) w := by
  rw [← absHoleG_iff_absHole, hole_iff_cuts, hole_iff_cuts]
  simp only [target_iff, relation_iff, toAbstract_eval]

/-- Rejection by the constructed side automaton is equivalent to a finite monitor hole. -/
theorem side_hole_iff (w : Word) :
    w ∉ (construct ϕ x y d).Lang ↔
      AbsHoleG (monitor ϕ x y d) relation (target ϕ x y d) w :=
  AbstractMonitor.side_hole_iff_absHole w |>.trans (hole_iff_abstract w).symm

/-- Failure of monoid coverage is equivalent to a monitor hole. -/
theorem not_fullCovered_iff_hole (w : Word) :
    ¬ FullCoverage.FullCovered (EndToEnd.transRel (construct ϕ x y d))
      (EndToEnd.VA (construct ϕ x y d)) (EndToEnd.V (construct ϕ x y d))
      (EndToEnd.U (construct ϕ x y d)) w ↔
        AbsHoleG (monitor ϕ x y d) relation (target ϕ x y d) w := by
  rw [← EndToEnd.mem_lang_iff_fullCovered]
  exact side_hole_iff w

/-- The side automaton is universal exactly when its monitor has no hole. -/
theorem universal_iff_no_holes (ϕ : Constraint k) (x y : DeciNSSE.V k) (d : Side) :
    (∀ w, w ∈ (construct ϕ x y d).Lang) ↔
      ¬ ∃ w, AbsHoleG (monitor ϕ x y d) relation (target ϕ x y d) w := by
  classical
  simp only [EndToEnd.mem_lang_iff_fullCovered, not_exists,
    ← not_fullCovered_iff_hole, not_not]

/-- Entailment holds exactly when there is no solution or neither side monitor has a hole. -/
theorem entails_iff_unsat_or_no_holes (ϕ : Constraint k) (x y : DeciNSSE.V k) :
    Entails ϕ x y ↔ (¬ ∃ ρ, Sat ρ ϕ) ∨
      ((¬ ∃ w, AbsHoleG (monitor ϕ x y .l) relation (target ϕ x y .l) w) ∧
       (¬ ∃ w, AbsHoleG (monitor ϕ x y .r) relation (target ϕ x y .r) w)) := by
  rw [Language.entails_iff_universal, universal_iff_no_holes, universal_iff_no_holes]

end DeciNSSE.Bridge
