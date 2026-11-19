import DeciNSSE.Complexity.Tiling.Packets
import DeciNSSE.Complexity.Tiling.ControlRun

/-! # Packet positions on target words

## Main declarations

- `render_of_final` recovers the packets of any target word.
- `paint_run` gives the copy, region and color at every live prefix.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
variable {D : Type*} [DecidableEq D] (I : Square D)
open scoped List

/-- Completing the last master gives the final control. Any earlier master gives way to the
probes of the next copy. -/
def afterMaster (j : ℕ) : Control D :=
  if j = 2*I.p then none else beginPhase D (j+1) false

/-- In a live control the payload slot belongs to the probe traversal. -/
def WellPhased : Control D → Prop
  | none => True
  | some r => r.slot = 2*I.p+2 → r.master = false

/-- A successful transition in a well-phased control updates the cut color on data and changes
or closes the appropriate field on a delimiter. -/
theorem step_shape {r : Registers D} {q : Control D} {a : Letter D}
    (phase : WellPhased I (some r)) (h : tokenStep I (some r) a = some q) :
    match a with
    | .data x => ∃ v, q = some v ∧ v.copy = r.copy ∧ v.master = r.master ∧
        v.color = some (.data x) ∧ (v.master = false → v.slot ≠ 0)
    | .bang => r.master = false ∧ r.slot = 0 ∧ q = beginPhase D r.copy true
    | .stop => (r.master = false ∧ q = some {r with color := some .stop, slot := 0}) ∨
        (r.master = true ∧ q = afterMaster I r.copy) := by
  change (r.slot = 2*I.p+2 → r.master = false) at phase
  by_cases tail : r.slot = 2*I.p+2
  · rcases a with x | _ | _ <;> simp [tokenStep,tail] at h <;>
      subst_vars <;> simp_all [afterMaster]
  by_cases start : r.slot = 0
  · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep,start,afterMaster] at h ⊢ <;>
      grind [afterMaster]
  · by_cases bit : r.slot ≤ 2*I.p
    · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep,tail,start,bit,readBit] at h ⊢
      split_ifs at h <;> simp_all <;> grind
    · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep,tail,start,bit,readTile] at h ⊢
      split_ifs at h <;> simp_all <;> grind

/-- A successful token transition preserves the restriction of payload slots to probes. -/
theorem phased_step {s q : Control D} {a : Letter D}
    (hs : WellPhased I s) (h : tokenStep I s a = some q) :
    WellPhased I q := by
  cases s with
  | none => cases h
  | some r =>
    change r.slot = 2*I.p+2 → r.master = false at hs
    by_cases tail : r.slot = 2*I.p+2
    · cases a <;> simp_all [tokenStep, WellPhased] <;> grind [WellPhased]
    by_cases start : r.slot = 0
    · rcases a with (b | _ | d) | _ | _ <;> simp_all [tokenStep, WellPhased,beginPhase] <;>
        grind [WellPhased]
    · by_cases bit : r.slot ≤ 2*I.p
      · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep,tail,start,bit,readBit] at h
        split_ifs at h <;> simp_all [WellPhased] <;> grind [WellPhased]
      · rcases a with (b | _ | d) | _ | _ <;> simp [tokenStep,tail,start,bit,readTile] at h
        split_ifs at h <;> simp_all [WellPhased] <;> grind [WellPhased]

/-- Successful execution of a word preserves the restriction of payload slots to probes. -/
theorem phased_run {s q : Control D}
    (hs : WellPhased I s) {w} (h : run I s w = some q) : WellPhased I q := by
  induction w generalizing s with
  | nil => cases h; exact hs
  | cons a w ih =>
    obtain ⟨r,he,hr⟩ := Option.bind_eq_some_iff.mp h
    exact ih (phased_step I hs he) hr

/-- A cut's admission data consist of its copy number, traversal region and preceding token
color. -/
structure Paint (α : Type*) where
  /-- The index of the packet copy. -/
  copy : ℕ
  /-- Whether the cut belongs to the master. -/
  master : Bool
  /-- The preceding token in the field, with a sentinel at its start. -/
  color : Option (Token α)
  deriving DecidableEq

/-- Decide equality of the copy, field and color used at a cut. -/
add_decl_doc instDecidableEqPaint

/-- Extract the admission data from a live control, returning `none` at the final control. -/
def paint (s : Control D) := s.map fun r => Paint.mk r.copy r.master r.color

/-- The initial cut of a field has the field-start sentinel as its color. -/
def fresh (j : ℕ) (b : Bool) : Paint (CellLetter D) := ⟨j,b,none⟩

/-- Update the copy, region and color visible to the admission test after reading a token. -/
def advancePaint (last : ℕ) :
    Option (Paint (CellLetter D)) → Letter D → Option (Paint (CellLetter D))
  | none, _ => none
  | some r, .data x => some {r with color := some (.data x)}
  | some r, .bang => some (fresh r.copy true)
  | some r, .stop =>
      if r.master then (if r.copy = last then none else some (fresh (r.copy+1) false))
    else some {r with color := some .stop}

private theorem paint_step {s q : Control D} {a : Letter D} (hs : WellPhased I s)
    (h : tokenStep I s a = some q) : paint q = advancePaint (2*I.p) (paint s) a := by
  cases s with
  | none => cases h
  | some r =>
    have syn := step_shape I hs h
    rcases a with x | _ | _
    · obtain ⟨v,rfl,hc,hm,hcol,_⟩ := syn; simp [paint,advancePaint,hc,hm,hcol]
    · rcases syn with ⟨hm,rfl⟩ | ⟨hm,rfl⟩ <;>
        simp [paint,advancePaint,hm,afterMaster,fresh,beginPhase]
      split <;> rfl
    · obtain ⟨_,_,rfl⟩ := syn; rfl

/-- Along a successful well-phased run, folding the color updates gives the admission data at
the endpoint. -/
theorem paint_run {s q : Control D} (hs : WellPhased I s) {w} (h : run I s w = some q) :
    paint q = w.foldl (advancePaint (2*I.p)) (paint s) := by
  induction w generalizing s with
  | nil => cases h; rfl
  | cons a w ih =>
    obtain ⟨s',he,hr⟩ := Option.bind_eq_some_iff.mp h
    rw [List.foldl_cons, ← paint_step I hs he]; exact ih (phased_step I hs he) hr

private def staged (r : Registers D) (w : List (Letter D)) : Prop :=
  ∃ (past : List (Packet (CellLetter D))) (probes : List (List (CellLetter D)))
      (field : List (CellLetter D)), past.length = r.copy ∧
    w = past.flatMap Packet.render ++ probeText probes ++ (if r.master then [.bang] else []) ++
        field.map Token.data ∧
    (r.master = false → r.slot = 0 → field = [])

/-- The final control state can only be reached after precisely the prescribed
number of packets, each ending in its master delimiter. -/
theorem render_of_final {w} (h : run I (beginPhase D 0 false) w = some none) :
    ∃ ps : List (Packet (CellLetter D)),
      ps.length = 2*I.p+1 ∧ w = ps.flatMap Packet.render := by
  let Goal (q : Control D) (w : List (Letter D)) := match q with
    | none => ∃ ps : List (Packet (CellLetter D)),
        ps.length = 2*I.p+1 ∧ w = ps.flatMap Packet.render
    | some r => staged r w
  have go {q} (w) (hr : run I (beginPhase D 0 false) w = some q) : WellPhased I q ∧ Goal q w := by
    induction w using List.reverseRecOn generalizing q with
    | nil =>
      have eq : q = beginPhase D 0 false := Option.some.inj hr.symm
      subst q
      exact ⟨by simp [WellPhased,beginPhase], [],[],[], rfl,rfl,by simp⟩
    | append_singleton w a ih =>
      obtain ⟨s,hw,ha⟩ := (run_split I).mp hr
      have step : tokenStep I s a = some q := by simpa [run] using ha
      obtain ⟨phase,old⟩ := ih hw
      refine ⟨phased_step I phase step, ?_⟩
      cases s with
      | none => cases step
      | some r =>
        obtain ⟨done,ps,x,hj,text,empty⟩ := old
        have syn := step_shape I phase step
        rcases a with d | _ | _
        · obtain ⟨v,rfl,hc,hm,hcol,hn⟩ := syn
          refine ⟨done,ps,x++[d],hj.trans hc.symm,by simp [hm,text,List.append_assoc],?_⟩
          exact fun he hs => (hn he hs).elim
        · rcases syn with ⟨hm,rfl⟩ | ⟨hm,rfl⟩
          · refine ⟨done,ps++[x],[],hj,?_,by simp⟩
            simp [probeText,text,hm,List.append_assoc]
          · let P : Packet (CellLetter D) := ⟨ps,x⟩
            have he : w ++ [.stop] = (done++[P]).flatMap Packet.render := by
              simp [P,Packet.render,text,hm,List.append_assoc]
            by_cases last : r.copy = 2*I.p
            · rw [show afterMaster I r.copy = none from ite_eq_left last]
              exact ⟨done++[P],by simp [hj,last],he⟩
            · rw [show afterMaster I r.copy = beginPhase D (r.copy+1) false from ite_eq_right last]
              exact ⟨done++[P],[],[],by simp [hj],by simp [he,probeText],by simp⟩
        · obtain ⟨hm,hs,rfl⟩ := syn
          refine ⟨done,ps,[],hj,?_,by simp⟩
          simp [text,hm,empty hm hs]
  exact (go w h).2

end DeciNSSE.Complexity.Tiling.Controller
