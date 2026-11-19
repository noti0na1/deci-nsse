import DeciNSSE.Complexity.Tiling.CutGeometry

/-! # Admissions on successful packet runs

## Main declarations

- `hole_packets_iff` characterizes holes reaching the final state by packet
  equality and authentication of the probes in the last packet.
-/

namespace DeciNSSE.Complexity.Tiling
open Controller Holes CoAlignment
open scoped List
variable {α D : Type*} {t : ℕ}

private theorem color_prefix (u v : List α) {i : ℕ} (hi : i ≤ u.length) :
    cutColor (u ++ v) i = cutColor u i := by
  cases i with
  | zero => rfl
  | succ i => exact List.getElem?_append_left (by omega)

private theorem color_after (u v : List α) {i : ℕ} (hi : 0 < i) :
    cutColor (u ++ v) (u.length + i) = cutColor v i := by
  cases i with
  | zero => omega
  | succ i =>
    change (u ++ v)[u.length + i]? = v[i]?
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

private theorem probe_offset (ps : List (List α)) (i : Fin ps.length) {j : ℕ}
    (hj : 0 < j) (le : j ≤ (ps[i].map Token.data).length) :
    let k := (probeText (ps.take i)).length + j
    k ≤ (probeText ps).length ∧
      cutColor (probeText ps) k = cutColor (ps[i].map Token.data) j ∧
      FieldCut.afterData (cutColor (ps[i].map Token.data) j) = true := by
  let f (a : List α) := a.map Token.data ++ [.stop]
  have split := flatMap_at f ps i
  change probeText ps = probeText (ps.take i) ++ (ps[i].map Token.data ++ [.stop]) ++ _ at split
  dsimp only
  refine ⟨by rw [split]; simp only [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
  · conv_lhs =>
      rw [split, List.append_assoc, color_after _ _ hj, List.append_assoc, color_prefix _ _ le]
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have lt : j < ps[i.val].length := by simp only [List.length_map,Fin.getElem_fin] at le; omega
    simp only [Fin.getElem_fin,cutColor,List.getElem?_map,List.getElem?_eq_getElem lt]; rfl

private theorem data_offset (ps : List (List α)) (k : ℕ) (le : k ≤ (probeText ps).length)
    (hd : FieldCut.afterData (cutColor (probeText ps) k) = true) :
    ∃ (i : Fin ps.length) (j : ℕ), 0 < j ∧ j ≤ (ps[i].map Token.data).length ∧
      k = (probeText (ps.take i)).length + j := by
  induction ps generalizing k with
  | nil =>
    have : k = 0 := by simpa [probeText] using le
    subst k; cases hd
  | cons x ps ih =>
    let u := x.map Token.data ++ [.stop]
    have eq : probeText (x::ps) = u ++ probeText ps := rfl
    by_cases small : k ≤ x.length
    · refine ⟨0,k,?_,by simpa using small,by simp [probeText]⟩
      by_contra! e
      have : k = 0 := by omega
      subst k; cases hd
    · have len : u.length = x.length+1 := by simp [u]
      by_cases endCut : k = u.length
      · subst k
        rw [eq, color_prefix _ _ le_rfl, len] at hd
        have hc : cutColor u (x.length+1) = some .stop := by simp [u,cutColor]
        rw [hc] at hd; cases hd
      · let j := k-u.length
        have pos : 0 < j := by dsimp [j]; omega
        have hk : k = u.length + j := by dsimp [j]; omega
        rw [eq,hk,color_after _ _ pos] at hd
        rw [eq,List.length_append] at le
        obtain ⟨i,l,hp,hl,he⟩ := ih j (by omega) hd
        refine ⟨i.succ,l,hp,by simpa using hl,?_⟩
        change k = (u ++ probeText (ps.take i)).length + l
        rw [List.length_append,hk,he,Nat.add_assoc]

private theorem mismatch_shift (u w : List α) (s e : ℕ) (a b : List α) (skip : Bool) :
    mismatch (u++w) (u.length+s) (u.length+e) a b skip ↔ mismatch w s e a b skip := by
  unfold mismatch IsComp
  simp only [Nat.add_assoc,List.drop_length_add_append,List.length_append,Nat.add_lt_add_iff_left,
    Nat.add_le_add_iff_left]

private theorem clear_fields [DecidableEq D] (I : Square D) (e : D ≃ Fin t)
    (ps : List (Packet (CellLetter D))) (hl : ps.length = 2*I.p+1)
    (final : run I (beginPhase D 0 false) (ps.flatMap Packet.render) = some none) :
    let w := ps.flatMap Packet.render
    (tokenReader I e).Hole w ↔ ∀ A B : FieldCut ps,
      IsComp w A.pos B.pos → ¬FieldCut.related (2*I.p) A B := by
  let w := ps.flatMap Packet.render
  dsimp only
  rw [StoppingTable.Hole, isReaderHole_iff]
  have target := (final_iff I e _).mpr final
  constructor
  · rintro ⟨_,clear⟩ A B h rel
    exact clear _ _ h.1 h.2.1 h.2.2 ((FieldCut.pair_iff I e hl A B final).mpr rel)
  · intro clear
    refine ⟨target,?_⟩
    intro s j hsj hj hp pair
    rcases hj.lt_or_eq with he | rfl
    · obtain ⟨A, rfl⟩ := FieldCut.cover ps (hsj.trans he)
      obtain ⟨B, rfl⟩ := FieldCut.cover ps he
      exact clear A B ⟨hsj,hj,hp⟩ ((FieldCut.pair_iff I e hl A B final).mp pair)
    · rw [List.take_length, Controller.pair_iff] at pair
      obtain ⟨_,_,_,impossible,_⟩ := pair
      rw [final] at impossible
      cases impossible

private def earlier (qs : List (Packet α)) (P : Packet α) (i : Fin qs.length) (m : Bool) (j)
    (h : j ≤ (qs[i].field m).length) : FieldCut (qs++[P]) :=
  ⟨⟨i,by simp; omega⟩,m,j,by simpa [List.getElem_append_left i.isLt] using h⟩

private def lastCut (qs : List (Packet α)) (P : Packet α) (m : Bool) (j)
    (h : j ≤ (P.field m).length) : FieldCut (qs++[P]) :=
  ⟨⟨qs.length,by simp⟩,m,j,by simpa using h⟩

private theorem earlier_pos (qs : List (Packet α)) (P : Packet α) (i : Fin qs.length) (m j h) :
    (earlier qs P i m j h).pos =
      ((qs.take i).flatMap Packet.render).length + (qs[i].lead m).length + j := by
  simp [earlier,FieldCut.pos,List.take_append_of_le_length i.isLt.le,
    List.getElem_append_left i.isLt]

private theorem last_pos (qs : List (Packet α)) (P : Packet α) (m j h) :
    (lastCut qs P m j h).pos = (qs.flatMap Packet.render).length + (P.lead m).length + j := by
  simp [lastCut,FieldCut.pos]

private theorem earlier_color (qs : List (Packet α)) (P : Packet α) (i : Fin qs.length) (m j h) :
    (earlier qs P i m j h).color = cutColor (qs[i].field m) j := by
  simp [FieldCut.color,earlier,List.getElem_append_left i.isLt]

private theorem last_color (qs : List (Packet α)) (P : Packet α) (m j h) :
    (lastCut qs P m j h).color = cutColor (P.field m) j := by simp [FieldCut.color,lastCut]

private theorem split_cut (qs : List (Packet α)) (P : Packet α) (C : FieldCut (qs++[P])) :
    (∃ i : Fin qs.length, ∃ h, C = earlier qs P i C.master C.offset h) ∨
      ∃ h, C = lastCut qs P C.master C.offset h := by
  obtain ⟨⟨i,hi⟩,m,j,hj⟩ := C
  by_cases lt : i < qs.length
  · exact Or.inl ⟨⟨i,lt⟩,by simpa [List.getElem_append_left lt] using hj,rfl⟩
  · have eq : i = qs.length := by simp at hi; omega
    subst i; exact Or.inr ⟨by simpa using hj,rfl⟩

private theorem copyClear_iff_fields (qs : List (Packet α)) (P : Packet α) :
    CopyClear qs P ↔ ∀ (i : Fin qs.length) (m : Bool),
      ¬ mismatch ((qs++[P]).flatMap Packet.render)
        (((qs.take i).flatMap Packet.render).length + (qs[i].lead m).length)
        ((qs.flatMap Packet.render).length + (P.lead m).length)
        (qs[i].field m) (P.field m) false := by
  simp only [Bool.forall_bool,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,
    CopyClear, Packet.lead, Packet.field, Bool.false_eq_true, ite_false, ite_true,
    List.length_append, List.length_nil, List.length_singleton, Nat.add_zero, Nat.add_assoc]

/-- A word reaching the final state is a hole exactly when every earlier packet equals the last
and every probe of the last packet is a suffix of its master. -/
theorem hole_packets_iff [DecidableEq D] (I : Square D) (e : D ≃ Fin t)
    (qs : List (Packet (CellLetter D))) (P : Packet (CellLetter D)) (hl : qs.length = 2*I.p)
    (final : run I (beginPhase D 0 false) ((qs++[P]).flatMap Packet.render) = some none) :
    (tokenReader I e).Hole ((qs++[P]).flatMap Packet.render) ↔
      (∀ q ∈ qs, q = P) ∧ ∀ a ∈ P.probes, a <:+ P.master := by
  apply (clear_fields I e _ (by simp [hl]) final).trans
  rw [← copy_test_iff, copyClear_iff_fields, ← suffix_test_iff]
  let pre := qs.flatMap Packet.render
  let w := (qs++[P]).flatMap Packet.render
  have he : w = pre ++ P.render := by simp [w,pre]
  constructor
  · intro clear
    constructor
    · rintro i m ⟨j,hj,k,hk,_,comp,ne⟩
      let A := earlier qs P i m j hj
      let B := lastCut qs P m k hk
      apply clear A B (by simpa only [A,B,earlier_pos,last_pos] using comp)
      exact ⟨hl,by rwa [earlier_color,last_color],Or.inl ⟨hl ▸ i.isLt,rfl⟩⟩
    · rintro i ⟨j,hj,k,hk,positive,comp,ne⟩
      obtain ⟨le,col,dat⟩ := probe_offset P.probes i (positive rfl) hj
      let A := lastCut qs P false _ le
      let B := lastCut qs P true k hk
      have cmp : IsComp w A.pos B.pos := by
        rw [he, show A.pos = _ from last_pos qs P false _ le,
          show B.pos = _ from last_pos qs P true k hk]
        have shift (x y : ℕ) :
            IsComp (pre ++ P.render) (pre.length + x) (pre.length + y) ↔ IsComp P.render x y := by
          simp only [IsComp, List.length_append, Nat.add_lt_add_iff_left,
            Nat.add_le_add_iff_left, List.drop_length_add_append]
        simpa only [pre,Packet.lead,ite_true,Bool.false_eq_true,ite_false,
            List.length_nil,Nat.add_zero,
          List.length_append,List.length_singleton,Nat.add_assoc] using (shift _ _).mpr comp
      apply clear A B cmp
      have co : A.color = cutColor (P.probes[i].map Token.data) j := (last_color ..).trans col
      have cb : B.color = cutColor (P.master.map Token.data) k := last_color qs P true k hk
      exact ⟨hl,by rwa [co,cb],Or.inr ⟨hl,rfl,rfl,co ▸ dat⟩⟩
  · rintro ⟨copies,suf⟩ A B comp ⟨last,ne,rel⟩
    obtain ⟨hb,eqB⟩ : ∃ h, B = lastCut qs P B.master B.offset h := by
      rcases split_cut qs P B with ⟨i,_,he⟩ | right
      · have eq := congrArg (fun c : FieldCut (qs++[P]) => c.copy.val) he
        change B.copy.val = i.val at eq; omega
      · exact right
    rcases rel with ⟨before,same⟩ | ⟨atLast,probe,master,dat⟩
    · obtain ⟨i,ha,eqA⟩ :
          ∃ i : Fin qs.length, ∃ h, A = earlier qs P i A.master A.offset h := by
        rcases split_cut qs P A with left | ⟨_,he⟩
        · exact left
        · have eq := congrArg (fun c : FieldCut (qs++[P]) => c.copy.val) he
          change A.copy.val = qs.length at eq; omega
      have aPos := congrArg FieldCut.pos eqA
      have bPos := congrArg FieldCut.pos eqB
      rw [earlier_pos] at aPos; rw [last_pos,← same] at bPos
      have ca := congrArg FieldCut.color eqA
      have cb := congrArg FieldCut.color eqB
      rw [earlier_color] at ca; rw [last_color,← same] at cb
      exact copies i A.master
        ⟨A.offset,ha,B.offset,same ▸ hb,by simp,
        by rwa [← aPos,← bPos],by rwa [← ca,← cb]⟩
    · obtain ⟨ha,eqA⟩ : ∃ h, A = lastCut qs P A.master A.offset h := by
        rcases split_cut qs P A with ⟨i,_,he⟩ | right
        · have eq := congrArg (fun c : FieldCut (qs++[P]) => c.copy.val) he
          change A.copy.val = i.val at eq; omega
        · exact right
      have ca := congrArg FieldCut.color eqA
      have cb := congrArg FieldCut.color eqB
      rw [last_color,probe] at ca; rw [last_color,master] at cb
      have bound : A.offset ≤ (probeText P.probes).length := by
        simpa [probe,Packet.field] using ha
      obtain ⟨i,j,hpos,hj,heq⟩ := data_offset _ _ bound (ca ▸ dat)
      obtain ⟨_,co,_⟩ := probe_offset P.probes i hpos hj
      have aPos := congrArg FieldCut.pos eqA
      have bPos := congrArg FieldCut.pos eqB
      rw [last_pos,probe] at aPos; rw [last_pos,master] at bPos
      apply suf i
      apply (mismatch_shift pre ..).mp
      refine ⟨j,hj,B.offset,by simpa [master,Packet.field] using hb,fun _ => hpos,?_,?_⟩
      · change IsComp w A.pos B.pos at comp
        rw [he,aPos,bPos,heq] at comp
        simpa [pre,Packet.lead,Nat.add_assoc] using comp
      · change A.color = cutColor (probeText P.probes) A.offset at ca
        change B.color = cutColor (P.master.map Token.data) B.offset at cb
        rw [← co, ← heq, ← ca, ← cb]; exact ne

end DeciNSSE.Complexity.Tiling
