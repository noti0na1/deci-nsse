import DeciNSSE.Complexity.Tiling.GridFacts

/-! # Authenticating the exposed tiles against the master

## Main declarations

- `record_at_suffix` locates an exposed record in a row-major master.
- `authenticated_iff` identifies exactly the packets of valid square tilings.
-/

namespace DeciNSSE.Complexity.Tiling
open scoped List
variable {D : Type*} {p : ℕ}

/-- A record contains two `p`-bit coordinates, a marker and a tile. -/
@[simp] theorem length_record (p x y : ℕ) (d : D) : (record p x y d).length = 2*p+2 := by
  simp [record]; omega

private theorem record_inj {a b : Addr p} {d h : D}
    (he : record p a.1 a.2 d = record p b.1 b.2 h) : a = b ∧ d = h := by
  let ds (x : ℕ) : List (CellLetter D) := (List.range p).map (fun i => .bit (x.testBit i))
  have dih (x y : Fin (2^p)) (eq : ds x = ds y) : x = y := by
    apply Fin.ext
    apply Addr.bits_ext x.isLt y.isLt
    intro i hi
    exact CellLetter.bit.inj ((List.map_inj_left.mp eq) i (List.mem_range.mpr hi))
  change [.record] ++ ds a.1 ++ ds a.2 ++ [.tile d] =
    [.record] ++ ds b.1 ++ ds b.2 ++ [.tile h] at he
  obtain ⟨left, tile⟩ := List.append_inj' he rfl
  obtain ⟨left, row⟩ := List.append_inj' left (by simp [ds])
  exact ⟨Prod.ext (dih _ _ (List.append_cancel_left left)) (dih _ _ row),
    CellLetter.tile.inj (List.cons.inj tile).1⟩

private theorem records_length (I : Square D) (g : I.Grid) (xs : List (Addr I.p)) :
    (xs.flatMap fun a => record I.p a.1 a.2 (g a.1 a.2)).length = xs.length * (2*I.p+2) := by
  simp [List.length_flatMap]

private theorem split_record {a : Addr p} {d : D} {g : Fin (2^p) → Fin (2^p) → D}
    (xs : List (Addr p)) {s : List (CellLetter D)} (exposed : record p a.1 a.2 d <+: s)
    (suffix : s <:+ xs.flatMap (fun xy => record p xy.1 xy.2 (g xy.1 xy.2))) :
    ∃ before after, xs = before ++ a :: after ∧ d = g a.1 a.2 ∧
      s = (a::after).flatMap (fun xy => record p xy.1 xy.2 (g xy.1 xy.2)) := by
  induction xs with
  | nil =>
    have zero : s = [] := List.suffix_nil.mp suffix
    have small := exposed.length_le
    simp [zero] at small
  | cons b xs ih =>
    let f (xy : Addr p) := record p xy.1 xy.2 (g xy.1 xy.2)
    change s <:+ f b ++ xs.flatMap f at suffix
    by_cases le : s.length ≤ (xs.flatMap f).length
    · obtain ⟨u,v,rfl,ht,he⟩ := ih
        (List.suffix_of_suffix_length_le suffix (List.suffix_append ..) le)
      exact ⟨b::u,v,rfl,ht,he⟩
    · obtain ⟨t, eq⟩ :=
        List.suffix_of_suffix_length_le (List.suffix_append (f b) (xs.flatMap f)) suffix (by omega)
      subst s
      have ht := List.suffix_append_self_iff.mp suffix
      have full : t = f b := by
        cases t with
        | nil => simp at le
        | cons c t =>
          obtain ⟨rest,hr⟩ := exposed
          have ec : c = .record := by
            change (.record :: _) ++ rest = c :: _ at hr
            exact (List.cons.inj hr).1.symm
          subst c
          change .record :: t <:+ .record :: _ at ht
          rcases List.suffix_cons_iff.mp ht with he | impossible
          · exact he
          · have mem := impossible.mem List.mem_cons_self
            simp at mem
      subst t
      have equal : record p a.1 a.2 d = f b := (List.prefix_of_prefix_length_le exposed
        (List.prefix_append ..) (by simp [f])).eq_of_length (by simp [f])
      obtain ⟨rfl,ht⟩ := record_inj equal
      exact ⟨[],xs,rfl,ht,rfl⟩

/-- A master suffix starting with the record for a given address exposes that cell's tile and
starts at its row-major record offset. -/
theorem record_at_suffix (I : Square D) (g : I.Grid) (xy : Addr I.p) {s d}
    (head : record I.p xy.1 xy.2 d <+: s) (tail : s <:+ masterWord I g) :
    d = g xy.1 xy.2 ∧ s = (masterWord I g).drop (Addr.index true xy * (2*I.p+2)) := by
  obtain ⟨u,v,split,ht,rfl⟩ := split_record (rowOrder I.side) head tail
  have index : Addr.index true xy = u.length := by
    have h := map_index_order I.p true
    change (rowOrder I.side).map _ = _ at h
    rw [split] at h
    have get := congrArg (fun l : List ℕ => l[u.length]?) h
    have len := congrArg List.length h
    simp at len
    have bound : u.length < 2^(2*I.p) := by omega
    simpa [List.getElem?_append_right (show (u.map (Addr.index true)).length ≤ u.length by simp),
      List.getElem?_eq_getElem
          (by simpa using bound : u.length < (List.range (2^(2*I.p))).length)] using get
  refine ⟨ht,?_⟩
  rw [masterWord,split,List.flatMap_append,index,← records_length I g u,List.drop_left]

private theorem all_mem_order (p : ℕ) (master : Bool) (a : Addr p) :
    a ∈ order (2^p) master := by
  rcases a with ⟨x,y⟩
  cases master <;> simp [order,rowOrder,colOrder]

private theorem canonical_probes (I : Square D) (g : I.Grid) (a : Addr I.p) :
    record I.p a.1 a.2 (g a.1 a.2) <+:
      (masterWord I g).drop (Addr.index true a * (2*I.p+2)) := by
  obtain ⟨u,v,he⟩ := List.mem_iff_append.mp (all_mem_order I.p true a)
  change rowOrder I.side = u ++ a :: v at he
  let f (a : Addr I.p) := record I.p a.1 a.2 (g a.1 a.2)
  have pref : f a <+: (a::v).flatMap f := List.prefix_append ..
  have suff : (a::v).flatMap f <:+ masterWord I g := by
    rw [masterWord,he,List.flatMap_append]; exact List.suffix_append ..
  rw [← (record_at_suffix I g a pref suff).2]
  exact pref

/-- A regularly checked packet with every probe authenticated as a master suffix is exactly the
packet of a valid grid. -/
theorem authenticated_iff [Fintype D] (I : Square D) (P : Packet (CellLetter D)) :
    (Checks I P ∧ ∀ a ∈ P.probes, a <:+ P.master) ↔
      ∃ g, I.Valid g ∧ P = gridPacket I g := by
  constructor
  · rintro ⟨⟨g,h,master,probes,valid,vertical⟩,auth⟩
    let suffix (a : Addr I.p) := (masterWord I g).drop (Addr.index true a * (2*I.p+2))
    have extract {xs : List (Addr I.p)} {ps : List (List (CellLetter D))}
        (hp : List.Forall₂ (fun a z => record I.p a.1 a.2 (h a.1 a.2) <+: z) xs ps)
        (ha : ∀ z ∈ ps, z <:+ masterWord I g) :
        ps = xs.map suffix ∧ ∀ a ∈ xs, h a.1 a.2 = g a.1 a.2 := by
      induction hp with
      | nil => simp
      | cons he _ ih =>
        obtain ⟨ht,hs⟩ := record_at_suffix I g _ he (ha _ List.mem_cons_self)
        obtain ⟨eq,agree⟩ := ih (fun _ hy => ha _ (List.mem_cons_of_mem _ hy))
        exact ⟨by rw [List.map_cons,eq,hs],
          fun _ h => (List.mem_cons.mp h).elim (fun e => e ▸ ht) (agree _)⟩
    obtain ⟨list,tiles⟩ := extract probes (by simpa only [← master] using auth)
    have eq : h = g := by funext x y; exact tiles (x,y) (all_mem_order I.p false (x,y))
    subst h
    refine ⟨g,fun x y => ⟨(valid x y).1,vertical x y,(valid x y).2.2⟩,?_⟩
    have hs (a : Addr I.p) : Addr.index true a = a.2.val * I.side + a.1.val := by
      simp [Addr.index,Nat.mul_comm]
    cases P
    simp_all only [gridPacket, suffix]
  · rintro ⟨g,hg,rfl⟩
    refine ⟨⟨g,g,rfl,?_,?_,fun x y => (hg x y).2.1⟩,?_⟩
    · apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      exact fun a _ => by simpa [Addr.index,Nat.mul_comm] using canonical_probes I g a
    · exact fun x y => ⟨(hg x y).1,fun _ => Finset.mem_univ _,(hg x y).2.2⟩
    · intro a ha
      obtain ⟨xy,_,rfl⟩ := List.mem_map.mp ha
      exact List.drop_suffix ..

end DeciNSSE.Complexity.Tiling
