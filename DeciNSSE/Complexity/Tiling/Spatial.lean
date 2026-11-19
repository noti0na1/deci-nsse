import DeciNSSE.Complexity.Tiling.Traversal

/-! # From ordered records to spatial constraints

## Main declarations

- `spatial_iff_checks` converts neighboring records in a traversal into the
  directed edges and boundary conditions of the square.
- `repeated_checks_iff` characterizes the target condition for a repeated packet.
-/

namespace DeciNSSE.Complexity.Tiling.Controller
variable {D : Type*} (I : Square D)

private def fast {p : ℕ} (m : Bool) (a : Addr p) := if m then a.1 else a.2
private def slow {p : ℕ} (m : Bool) (a : Addr p) := if m then a.2 else a.1

private def adjacent {p : ℕ} (m : Bool) (a b : Addr p) :=
  (fast m a).val+1=(fast m b).val ∧ slow m a = slow m b

private theorem adjacent_iff {p : ℕ} (m : Bool) (a b : Addr p) :
    adjacent m a b ↔ Addr.index m a+1 = Addr.index m b ∧ (fast m b).val ≠ 0 := by
  let s := 2^p
  have idx (x : Addr p) : Addr.index m x = s*(slow m x).val+(fast m x).val := by cases m <;> rfl
  rw [idx, idx]
  unfold adjacent
  constructor
  · rintro ⟨he,hs⟩; rw [hs,← he]; constructor <;> omega
  · rintro ⟨num,nonzero⟩
    have ha := (fast m a).isLt
    have hb := (fast m b).isLt
    change _ < s at ha hb
    have eq : slow m a = slow m b := by
      apply Fin.ext
      rcases lt_trichotomy (slow m a).val (slow m b).val with h | h | h
      · have := Nat.mul_le_mul_left s h; rw [Nat.mul_succ] at this; omega
      · exact h
      · have := Nat.mul_le_mul_left s h; rw [Nat.mul_succ] at this; omega
    rw [eq] at num
    exact ⟨by omega,eq⟩

private def Spatial (m : Bool) (g : I.Grid) : Prop :=
  (m = true → ∀ a : Addr I.p, Boundary I a (g a.1 a.2)) ∧
    ∀ a b : Addr I.p, adjacent m a b →
    (g a.1 a.2,g b.1 b.2) ∈ (if m then I.horizontal else I.vertical)

private theorem spatial_master (g : I.Grid) [Fintype D] :
    Spatial I true g ↔ ({I with vertical := Finset.univ} : Square D).Valid g := by
  constructor
  · rintro ⟨bounds,edge⟩ x y
    exact ⟨fun hx => edge (x,y) (⟨x.val+1,hx⟩,y) ⟨rfl,rfl⟩,fun _ => Finset.mem_univ _,
      bounds rfl (x,y)⟩
  · intro h
    refine ⟨fun _ a => (h a.1 a.2).2.2,?_⟩
    rintro ⟨x,y⟩ ⟨x',y'⟩ ⟨hx,hy⟩
    change y = y' at hy; subst y'
    change x.val+1 = x'.val at hx
    exact (show x' = ⟨x.val+1,by omega⟩ from Fin.ext hx.symm).symm ▸
      (h x y).1 (hx ▸ x'.isLt)

private theorem spatial_probes (g : I.Grid) :
    Spatial I false g ↔
      ∀ x y (h : y.val+1 < I.side), (g x y,g x ⟨y.val+1,h⟩) ∈ I.vertical := by
  constructor
  · exact fun ⟨_,edge⟩ x y h => edge (x,y) (x,⟨y.val+1,h⟩) ⟨rfl,rfl⟩
  · intro h
    refine ⟨by simp,?_⟩
    rintro ⟨x,y⟩ ⟨x',y'⟩ ⟨hy,hx⟩
    change x=x' at hx; subst x'
    change y.val+1=y'.val at hy
    exact (show y' = ⟨y.val+1,by omega⟩ from Fin.ext hy.symm).symm ▸ h x y (hy ▸ y'.isLt)

private def previousAt {p : ℕ} (before : Option D) (vs : List (Visit p D)) : ℕ → Option D
  | 0 => before
  | i+1 => vs[i]?.map Visit.tile

private theorem local_at (m) (before) (vs : List (Visit I.p D)) :
    localChecks I m before vs ↔ ∀ i (hi : i < vs.length),
      CellOK I m (previousAt before vs i) vs[i].addr vs[i].tile := by
  induction vs generalizing before with
  | nil => simp [localChecks]
  | cons v vs ih =>
    have prev (i : ℕ) : previousAt before (v::vs) (i+1) = previousAt (some v.tile) vs i := by
      cases i <;> rfl
    rw [localChecks,ih]
    constructor
    · rintro ⟨h,ht⟩ (_ | i) hi
      · exact h
      · rw [prev]; exact ht i (by simpa using hi)
    · intro h
      refine ⟨h 0 (by simp),?_⟩
      intro i hi
      have hh := h (i+1) (by simpa using hi)
      rw [prev] at hh
      exact hh

private theorem positions (m) (vs : List (Visit I.p D))
    (orderEq : vs.map Visit.addr = order I.side m) :
    vs.length = total I.p ∧ ∀ i (hi : i < vs.length), Addr.index m vs[i].addr = i := by
  have eq := congrArg (List.map (Addr.index m)) orderEq
  rw [map_index_order] at eq
  have len := congrArg List.length eq
  simp only [List.length_map,List.length_range] at len
  refine ⟨len,?_⟩
  intro i hi
  have hi' : i < (List.range (total I.p)).length := by simpa [len] using hi
  have get := congrArg (fun xs : List ℕ => xs[i]?) eq
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi',Option.map_some,
    List.getElem_range,Option.some.injEq] using get

private theorem labels_exist (m) (vs : List (Visit I.p D))
    (orderEq : vs.map Visit.addr = order I.side m) :
    ∃ g : I.Grid, ∀ v ∈ vs, v.tile = g v.addr.1 v.addr.2 := by
  obtain ⟨len,pos⟩ := positions I m vs orderEq
  let g (x y : Fin I.side) := vs[Addr.index m (x,y)]'(by rw [len]; exact Addr.index_lt _ _)
  refine ⟨fun x y => (g x y).tile,?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  dsimp [g]
  simp only [Prod.mk.eta, pos i hi]

private theorem spatial_iff_checks (m) (g : I.Grid) (vs : List (Visit I.p D))
    (orderEq : vs.map Visit.addr = order I.side m)
    (tile : ∀ v ∈ vs, v.tile = g v.addr.1 v.addr.2) :
    localChecks I m none vs ↔ Spatial I m g := by
  obtain ⟨len,pos⟩ := positions I m vs orderEq
  have bound (a : Addr I.p) : Addr.index m a < vs.length := (len.symm ▸ Addr.index_lt a m)
  have addr (a : Addr I.p) : (vs[Addr.index m a]'(bound a)).addr = a :=
    Addr.index_inj m (pos _ _)
  have value (a : Addr I.p) : (vs[Addr.index m a]'(bound a)).tile = g a.1 a.2 := by
    rw [tile _ (List.getElem_mem ..),addr]
  rw [local_at]
  constructor
  · intro accepted
    refine ⟨fun hm a => ?_, fun a b adjacent => ?_⟩
    · simpa only [addr,value] using (accepted _ (bound a)).1 hm
    · obtain ⟨next,nz⟩ := (adjacent_iff m a b).mp adjacent
      have previous : previousAt (D := D) none vs (Addr.index m b) = some (g a.1 a.2) := by
        rw [← next,previousAt,List.getElem?_eq_getElem (bound a)]; exact congrArg some (value a)
      have h := (accepted _ (bound b)).2
      rw [addr,value] at h
      apply h
      · cases m <;> exact nz
      · exact previous
  · rintro ⟨bounds,edge⟩ i hi
    rw [tile _ (List.getElem_mem ..)]
    refine ⟨fun h => bounds h _,?_⟩
    intro nz d prev
    cases i with
    | zero => cases prev
    | succ i =>
      have small : i < vs.length := by omega
      rw [previousAt,List.getElem?_eq_getElem small] at prev
      cases Option.some.inj prev
      rw [tile _ (List.getElem_mem ..)]
      exact edge _ _ ((adjacent_iff m ..).mpr ⟨by rw [pos,pos],by cases m <;> exact nz⟩)

private def masterCells (v : Visit I.p D) := record I.p v.addr.1 v.addr.2 v.tile
private def probeCells (v : Visit I.p D) := masterCells I v ++ v.payload

private theorem tape_master (vs : List (Visit I.p D)) :
    tapeOf I true vs = .master (vs.flatMap (masterCells I)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [tapeOf,ih]; rfl

private theorem tape_probes (vs : List (Visit I.p D)) :
    tapeOf I false vs = .probes (vs.map (probeCells I)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [tapeOf,ih]; rfl

private theorem master_word (vs : List (Visit I.p D)) (g : I.Grid)
    (ord : vs.map Visit.addr = order I.side true)
    (tiles : ∀ v ∈ vs, v.tile = g v.addr.1 v.addr.2) :
    vs.flatMap (masterCells I) = masterWord I g := by
  unfold masterWord
  change vs.map Visit.addr = rowOrder I.side at ord
  rw [← ord,List.flatMap_map]
  exact congrArg List.flatten (List.map_inj_left.mpr (fun v hv => by simp [masterCells,tiles v hv]))

private theorem probes_of_visits (vs : List (Visit I.p D)) (g : I.Grid)
    (tiles : ∀ v ∈ vs, v.tile = g v.addr.1 v.addr.2) :
    List.Forall₂ (fun a x => record I.p a.1 a.2 (g a.1 a.2) <+: x)
      (vs.map Visit.addr) (vs.map (probeCells I)) := by
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    exact .cons (by simp [probeCells,masterCells,tiles v List.mem_cons_self])
      (ih fun w hw => tiles w (List.mem_cons_of_mem _ hw))

private theorem visits_of_probes (g : I.Grid) {as : List (Addr I.p)} {xs}
    (hs : List.Forall₂ (fun a x => record I.p a.1 a.2 (g a.1 a.2) <+: x) as xs) :
    ∃ vs : List (Visit I.p D), vs.map Visit.addr = as ∧ vs.map (probeCells I) = xs ∧
      ∀ v ∈ vs, v.tile = g v.addr.1 v.addr.2 := by
  induction hs with
  | nil => exact ⟨[],rfl,rfl,by simp⟩
  | @cons a x _ _ head _ ih =>
    obtain ⟨vs,oa,ot,tiles⟩ := ih
    obtain ⟨p,hp⟩ := head
    exact ⟨⟨a,g a.1 a.2,p⟩::vs,by simp [oa],by simp [probeCells,masterCells,← hp,ot],
      fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ rfl) (tiles v)⟩

/-- A repeated packet completes the register computation exactly when its two traversals satisfy
the grid checks. -/
theorem repeated_checks_iff [DecidableEq D] [Fintype D] (P : Packet (CellLetter D)) :
    run I (beginPhase D 0 false) (copies I P) = some none ↔ Checks I P := by
  have search (m) (T : Tape D m) := read_traversal I m T
  rw [copies_final]
  constructor
  · intro h
    obtain ⟨ms,ord,mt,hms⟩ := (search true (.master P.master)).mp
      (fun j => h j (by have := j.isLt; omega) true)
    obtain ⟨ps,pord,pt,hps⟩ := (search false (.probes P.probes)).mp
      (fun j => h j (by have := j.isLt; omega) false)
    obtain ⟨g,tg⟩ := labels_exist I true ms ord
    obtain ⟨k,tk⟩ := labels_exist I false ps pord
    rw [tape_master] at mt; rw [tape_probes] at pt
    refine ⟨g,k,(Tape.master.inj mt).trans (master_word I ms g ord tg),?_,
      (spatial_master I g).mp ((spatial_iff_checks I true g ms ord tg).mp hms),
      (spatial_probes I k).mp ((spatial_iff_checks I false k ps pord tk).mp hps)⟩
    rw [Tape.probes.inj pt,← (show ps.map Visit.addr = colOrder I.side from pord)]
    exact probes_of_visits I ps k tk
  · rintro ⟨g,k,master,probes,hm,hp⟩ j hj m
    let guard : Guard I.p := ⟨j,by omega⟩
    cases m with
    | true =>
      let vs : List (Visit I.p D) := (rowOrder I.side).map fun a => ⟨a,g a.1 a.2,[]⟩
      have ord : vs.map Visit.addr = order I.side true := by
        simp [vs,order,List.map_map,Function.comp_def]
      have tile (v) (hv : v ∈ vs) : v.tile = g v.addr.1 v.addr.2 := by
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hv; rfl
      apply (search true (.master P.master)).mpr _ guard
      exact ⟨vs,ord,by rw [tape_master,master_word I vs g ord tile,master],
        (spatial_iff_checks I true g vs ord tile).mpr ((spatial_master I g).mpr hm)⟩
    | false =>
      obtain ⟨vs,ord,fields,tile⟩ := visits_of_probes I k probes
      apply (search false (.probes P.probes)).mpr _ guard
      exact ⟨vs,ord,by rw [tape_probes,fields],
        (spatial_iff_checks I false k vs ord tile).mpr ((spatial_probes I k).mpr hp)⟩

end DeciNSSE.Complexity.Tiling.Controller
