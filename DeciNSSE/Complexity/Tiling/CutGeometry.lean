import DeciNSSE.Complexity.Tiling.Roles

/-! # Copy and field labels at packet cuts

## Main declarations

- `FieldCut.cover` locates each nonterminal cut in a packet.
- `FieldCut.pair_iff` identifies admissions at two specified field cuts.
-/

namespace DeciNSSE.Complexity.Tiling
open Controller CoAlignment Holes
open scoped List
variable {α D : Type*}

/-- Select the master data or the complete probe text of a packet. -/
def Packet.field (P : Packet α) (master : Bool) :=
  if master then P.master.map Token.data else probeText P.probes

/-- The probe field starts at the packet's start. The master starts after the probe text and its
field delimiter. -/
def Packet.lead (P : Packet α) (master : Bool) : List (Token α) :=
  if master then probeText P.probes ++ [.bang] else []

/-- A cut in a packet sequence is specified by a copy, a field and an offset through the end of
that field. -/
structure FieldCut {α : Type*} (ps : List (Packet α)) where
  /-- The packet containing the cut. -/
  copy : Fin ps.length
  /-- Select the master field when true and the probe text otherwise. -/
  master : Bool
  /-- The number of tokens before the cut within its field. -/
  offset : ℕ
  /-- The offset is at most the field length, so the end cut is included. -/
  bound : offset ≤ (ps[copy].field master).length

namespace FieldCut
variable {ps : List (Packet α)}

/-- The absolute position of a field cut counts earlier packets, the lead into its field and the
offset within the field. -/
def pos (C : FieldCut ps) :=
  ((ps.take C.copy.val).flatMap Packet.render).length + (ps[C.copy].lead C.master).length + C.offset

/-- The color at a field cut is its preceding token or the field-start sentinel. -/
def color (C : FieldCut ps) := cutColor (ps[C.copy].field C.master) C.offset

/-- Every nonterminal position of the rendered packets is the absolute position of a field cut. -/
theorem cover (ps : List (Packet α)) {i : ℕ} (hi : i < (ps.flatMap Packet.render).length) :
    ∃ C : FieldCut ps, C.pos = i := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    by_cases hp : i < p.render.length
    · by_cases h : i ≤ (probeText p.probes).length
      · exact ⟨⟨0,false,i,h⟩, by simp [pos,Packet.lead]⟩
      · let b := (probeText p.probes).length+1
        have hb : i-b ≤ (p.master.map Token.data).length := by
          simp [Packet.render,b] at hp ⊢; omega
        exact ⟨⟨0,true,i-b,hb⟩,by simp [pos,Packet.lead,b]; omega⟩
    · obtain ⟨C,hC⟩ := ih (i := i-p.render.length)
        (by simp only [List.flatMap_cons,List.length_append] at hi; omega)
      let T : FieldCut (p::ps) := ⟨C.copy.succ,C.master,C.offset,by simpa using C.bound⟩
      exact ⟨T,by simp [T,pos] at hC ⊢; omega⟩

/-- The word before a field cut consists of the earlier packets, the lead into its field and the
retained field prefix. -/
theorem prefix_at (C : FieldCut ps) :
    (ps.flatMap Packet.render).take C.pos = (ps.take C.copy.val).flatMap Packet.render ++
      ps[C.copy].lead C.master ++ (ps[C.copy].field C.master).take C.offset := by
  let Q := ps[C.copy]
  let pre := (ps.take C.copy.val).flatMap Packet.render
  have split := List.take_append_drop C.copy.val ps
  rw [List.drop_eq_getElem_cons C.copy.isLt] at split
  have all : ps.flatMap Packet.render =
      pre ++ (Q.render ++ (ps.drop (C.copy.val+1)).flatMap Packet.render) := by
    simpa only [pre,Q,List.append_assoc] using flatMap_at Packet.render ps C.copy
  rw [all]
  change (pre ++ _).take (pre.length+(Q.lead C.master).length+C.offset) = _
  rw [Nat.add_assoc,List.take_length_add_append]
  have hpre : ∃ t, Q.render = Q.lead C.master ++ (Q.field C.master ++ t) := by
    cases C.master <;> simp [Packet.lead, Packet.field,Packet.render,List.append_assoc]
  obtain ⟨t,ht⟩ := hpre
  rw [ht]; simp only [List.append_assoc,List.take_length_add_append]
  rw [List.take_append_of_le_length C.bound]

/-- Every field cut precedes the end of the complete packet sequence. -/
theorem pos_lt (C : FieldCut ps) : C.pos < (ps.flatMap Packet.render).length := by
  have len := congrArg List.length (flatMap_at Packet.render ps C.copy)
  have h := C.bound
  cases hm : C.master <;>
    simp only [hm, Packet.render, Packet.field, Packet.lead, pos,
      List.length_append, List.length_map,
      List.length_singleton, List.length_nil, Bool.false_eq_true,
      ite_false, ite_true] at h len ⊢ <;> omega

end FieldCut

namespace Controller
variable (last : ℕ)

/-- Reading a field without a phase change keeps its copy and region and records the last token
as its color. -/
theorem fold_field (j : ℕ) (mode : Bool) (xs : List (Letter D))
    (plain : ∀ x ∈ xs, x ≠ .bang ∧ (mode = true → x ≠ .stop)) :
    xs.foldl (advancePaint last) (some (fresh j mode)) = some ⟨j,mode,xs.getLast?⟩ := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs a ih =>
    have h := plain a (by simp)
    rw [List.foldl_append, ih (fun x hx => plain x (List.mem_append_left _ hx))]
    cases a <;> cases mode <;> simp_all [advancePaint]

/-- Both fields exclude the phase delimiter, and the master also excludes the stop token. -/
theorem plain_field (p : Packet (CellLetter D)) (b : Bool) :
    ∀ a ∈ p.field b, a ≠ .bang ∧ (b = true → a ≠ .stop) := by
  cases b <;> simp [Packet.field,probeText]; grind

/-- Reading up to the selected field starts that field with its sentinel color. -/
theorem fold_lead (j : ℕ) (p : Packet (CellLetter D)) (b : Bool) :
    (p.lead b).foldl (advancePaint last) (some (fresh j false)) = some (fresh j b) := by
  cases b with
  | false => rfl
  | true =>
    change (p.field false ++ [Token.bang]).foldl _ _ = _
    rw [List.foldl_append,fold_field last j false _ (plain_field p false)]; rfl

/-- Reading a complete packet starts the next copy or finishes the input at the last copy. -/
theorem fold_packet (j : ℕ) (p : Packet (CellLetter D)) :
    p.render.foldl (advancePaint last) (some (fresh j false)) =
      if j=last then none else some (fresh (j+1) false) := by
  change ((p.lead true ++ p.field true) ++ [Token.stop]).foldl _ _ = _
  rw [List.foldl_append,List.foldl_append, fold_lead,
    fold_field last j true _ (plain_field p true)]; rfl

/-- Reading an initial sequence of complete packets leaves the color registers at the start of
the next copy. -/
theorem fold_before (ps : List (Packet (CellLetter D))) (hl : ps.length ≤ last) :
    (ps.flatMap Packet.render).foldl (advancePaint last) (
      some (fresh 0 false)) = some (fresh ps.length false) := by
  induction ps using List.reverseRecOn with
  | nil => rfl
  | append_singleton ps p ih =>
    simp only [List.length_append,List.length_singleton] at hl ⊢
    simp only [List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.foldl_append]
    rw [ih (by omega), fold_packet, ite_eq_right (by omega)]

/-- At a field cut, the color registers recover its copy, region and preceding token. -/
theorem paint_at {ps : List (Packet (CellLetter D))} (hlen : ps.length = last+1) (C : FieldCut ps) :
    ((ps.flatMap Packet.render).take C.pos).foldl (advancePaint last) (some (fresh 0 false)) =
      some ⟨C.copy.val,C.master,C.color⟩ := by
  rw [C.prefix_at,List.foldl_append,List.foldl_append,
    fold_before last _ (by simp; have := C.copy.isLt; omega)]
  rw [List.length_take, Nat.min_eq_left C.copy.isLt.le, fold_lead]
  rw [fold_field last C.copy C.master _ (fun x hx => plain_field _ _ x (List.mem_of_mem_take hx))]
  cases ho : C.offset with
  | zero => simp [FieldCut.color,ho,cutColor]
  | succ i =>
    have hl : i < (ps[C.copy].field C.master).length := by have := C.bound; omega
    have lastTake (xs : List (Letter D)) (i : ℕ) (hi : i < xs.length) :
        (xs.take (i+1)).getLast? = xs[i]? := by
      rw [List.take_succ_eq_append_getElem hi, List.getLast?_append_of_ne_nil _ (by simp),
        List.getLast?_singleton, List.getElem?_eq_getElem hi]
    simp only [FieldCut.color,ho,cutColor,lastTake _ i hl]

end Controller

namespace FieldCut
variable {t : ℕ} [DecidableEq D] (I : Square D) (e : D ≃ Fin t)
variable {ps : List (Packet (CellLetter D))}

private theorem registers_at (hl : ps.length = 2*I.p+1) (C : FieldCut ps)
    (final : run I (beginPhase D 0 false) (ps.flatMap Packet.render) = some none) :
    ∃ r, run I (beginPhase D 0 false) ((ps.flatMap Packet.render).take C.pos) = some (some r) ∧
      r.copy = C.copy.val ∧ r.master = C.master ∧ r.color = C.color := by
  let w := ps.flatMap Packet.render
  obtain ⟨q,hq,_⟩ := (run_split I (v := w.take C.pos) (w := w.drop C.pos)).mp
    (by rw [List.take_append_drop]; exact final)
  have h := (paint_run I (by simp [WellPhased,beginPhase]) hq).trans (paint_at _ hl C)
  cases q with
  | none => cases h
  | some r =>
    exact ⟨r,hq,congrArg Paint.copy (Option.some.inj h),congrArg Paint.master (Option.some.inj h),
      congrArg Paint.color (Option.some.inj h)⟩

/-- Test whether a cut's color comes from a data token. -/
def afterData (o : Option (Token α)) : Bool := match o with | some (.data _) => true | _ => false

/-- Two field cuts are related when their copies, regions and different colors select a copy
test or a final probe-to-master test. -/
def related (last : ℕ) (A B : FieldCut ps) : Prop :=
  B.copy.val = last ∧ A.color ≠ B.color ∧
    ((A.copy.val < last ∧ A.master = B.master) ∨
     (A.copy.val = last ∧ A.master = false ∧ B.master = true ∧ afterData A.color = true))

/-- On a successful packet sequence, the reader admits two field cuts exactly when their copies,
regions and colors satisfy `related`. -/
theorem pair_iff (hl : ps.length = 2*I.p+1) (A B : FieldCut ps)
    (final : run I (beginPhase D 0 false) (ps.flatMap Packet.render) = some none) :
    let w := ps.flatMap Packet.render
    ((tokenReader I e).dfa.eval (w.take A.pos), (tokenReader I e).dfa.eval (w.take B.pos)) ∈
      (tokenReader I e).pairs
      ↔ related (2*I.p) A B := by
  obtain ⟨r,hr,rc,rm,ro⟩ := registers_at I hl A final
  obtain ⟨s,hs,sc,sm,so⟩ := registers_at I hl B final
  dsimp only
  rw [Controller.pair_iff]
  simp only [hr,hs,Option.some.injEq]
  simp_all [tokenAdmission,related,afterData,and_assoc]
  intro _ _
  rcases A.color with _ | (_ | _ | _) <;> rfl

end FieldCut
end DeciNSSE.Complexity.Tiling
