import DeciNSSE.Holes.Hierarchy.Canonical
import DeciNSSE.Complexity.Tiling.Fields
import DeciNSSE.Complexity.Tiling.Controller

/-! # Packets and grid encodings

## Main declarations

- `suffix_test_iff` and `copy_test_iff` characterize clear comparisons.
- `gridPacket` encodes the master and probes.
- `Checks` specifies both traversals and the boundary conditions.
-/

namespace DeciNSSE.Complexity.Tiling
open CoAlignment Holes
open scoped List

/-- A packet contains a list of probe words followed by a master word over the same data
alphabet. -/
structure Packet (α : Type*) where
  /-- The probe words in their order of appearance in the packet. -/
  probes : List (List α)
  /-- The data word against which the probes are authenticated. -/
  master : List α
  deriving DecidableEq

/-- Decide packet equality by comparing the complete list of probes and the master word. -/
add_decl_doc instDecidableEqPacket

variable {α : Type*}

/-- Render the probes as data words, each followed by a stop token. -/
def probeText (ps : List (List α)) : List (Token α) :=
  ps.flatMap fun a => a.map Token.data ++ [.stop]

/-- Render the probes, the field delimiter, the master and the final stop token. -/
def Packet.render (P : Packet α) : List (Token α) :=
  probeText P.probes ++ [.bang] ++ P.master.map Token.data ++ [.stop]

/-- Split a concatenation of word images into the text before an indexed item, its image, and
the text after it. -/
theorem flatMap_at {β γ : Type*} (f : β → List γ) (xs : List β) (i : Fin xs.length) :
    xs.flatMap f = (xs.take i).flatMap f ++ f xs[i] ++ (xs.drop (i.val + 1)).flatMap f := by
  have split := List.take_append_drop i.val xs
  rw [List.drop_eq_getElem_cons i.isLt] at split
  simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc, Fin.getElem_fin]
    using congrArg (List.flatMap f) split.symm

private theorem data_inj : Function.Injective (Token.data : α → Token α) :=
  fun _ _ h => Token.data.inj h

private theorem probes_inj : Function.Injective (probeText (α := α)) := by
  classical
  intro ps qs he
  have parse (v : List (List α)) :
      LetteredHierarchy.cutAt .stop (probeText v) = v.map (List.map Token.data) := by
    have he : probeText v = LetteredHierarchy.expand .stop (v.map (List.map Token.data)) := by
      simp [probeText, LetteredHierarchy.expand, List.flatMap_map]
    rw [he]
    apply LetteredHierarchy.cutAt_expand
    rintro _ hx
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
    simp
  exact List.map_injective_iff.mpr (List.map_injective_iff.mpr data_inj)
    ((parse ps).symm.trans (he ▸ parse qs))

private theorem no_bang (v : List (List α)) : .bang ∉ probeText v := by simp [probeText]

/-- All probe-to-master comparisons are clear exactly when every probe is a suffix of the
master. -/
theorem suffix_test_iff (P : Packet α) :
    (∀ i : Fin P.probes.length, ¬ mismatch P.render (probeText (P.probes.take i)).length
      ((probeText P.probes).length + 1) (P.probes[i].map Token.data)
      (P.master.map Token.data) true) ↔ ∀ a ∈ P.probes, a <:+ P.master := by
  have atProbe (i : Fin P.probes.length) :=
    flatMap_at (fun a : List α => a.map Token.data ++ [.stop]) P.probes i
  have one (i : Fin P.probes.length) :
      (¬ mismatch P.render (probeText (P.probes.take i)).length ((probeText P.probes).length + 1)
        (P.probes[i].map Token.data) (P.master.map Token.data) true) ↔
        P.probes[i] <:+ P.master := by
    let u := probeText (P.probes.take i)
    let rest := probeText (P.probes.drop (i.val + 1)) ++ [.bang]
      ++ P.master.map Token.data ++ [.stop]
    let v := probeText P.probes ++ [.bang]
    have h := atProbe i
    change probeText P.probes = u ++ (P.probes[i].map Token.data ++ [.stop]) ++ _ at h
    have h₁ : P.render = u ++ (P.probes[i].map Token.data ++ .stop :: rest) := by
      unfold Packet.render; rw [h]; simp [rest, List.append_assoc, probeText]
    have h₂ : P.render = v ++ (P.master.map Token.data ++ .stop :: []) := by
      simp [v, Packet.render, List.append_assoc]
    have order : u.length + (P.probes[i].map Token.data).length < v.length := by simp [v, h]
    have equiv := clear_fields_iff h₁ h₂ order (by simp) (by simp) List.nil_prefix true
    simpa only [v, List.length_append, List.length_singleton, Bool.true_eq, ite_true,
      List.suffix_map_iff_of_injective data_inj] using equiv
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    exact (one ⟨i,hi⟩).mp (h _)
  · intro h i
    exact (one i).mpr (h _ (List.getElem_mem _))

/-- Every earlier probe field and master field passes the mismatched-color comparison test
against its counterpart in the last packet. -/
def CopyClear (ps : List (Packet α)) (P : Packet α) : Prop :=
  let w := ps.flatMap Packet.render ++ P.render
  let e := (ps.flatMap Packet.render).length
  ∀ i : Fin ps.length,
    let s := ((ps.take i).flatMap Packet.render).length
    let Q := ps[i]
    ¬ mismatch w s e (probeText Q.probes) (probeText P.probes) false ∧
    ¬ mismatch w (s + (probeText Q.probes).length + 1) (e + (probeText P.probes).length + 1)
      (Q.master.map Token.data) (P.master.map Token.data) false

/-- Comparisons between the corresponding fields of earlier and final packets are clear exactly
when every earlier packet equals the final one. -/
theorem copy_test_iff (ps : List (Packet α)) (P : Packet α) :
    CopyClear ps P ↔ ∀ Q ∈ ps, Q = P := by
  let all := ps.flatMap Packet.render
  let w := all ++ P.render
  have tests (i : Fin ps.length) :
      let u := (ps.take i).flatMap Packet.render
      let Q := ps[i]
      (¬ mismatch w u.length all.length (probeText Q.probes) (probeText P.probes) false ∧
       ¬ mismatch w (u.length + (probeText Q.probes).length + 1)
         (all.length + (probeText P.probes).length + 1)
           (Q.master.map Token.data) (P.master.map Token.data) false)
        ↔ Q = P := by
    let u := (ps.take i).flatMap Packet.render
    let Q := ps[i]
    let mid := (ps.drop (i.val + 1)).flatMap Packet.render
    have split : all = u ++ Q.render ++ mid := flatMap_at _ _ _
    let left := u ++ probeText Q.probes ++ [.bang]
    let right := all ++ probeText P.probes ++ [.bang]
    have h₁ : w = left ++ (Q.master.map Token.data ++ .stop :: (mid ++ P.render)) := by
      simp [w, split, left, Packet.render, List.append_assoc]
    have h₂ : w = right ++ (P.master.map Token.data ++ .stop :: []) := by
      simp [w, right, Packet.render, List.append_assoc]
    have ho : left.length + (Q.master.map Token.data).length < right.length := by
      simp [left, right, split, Packet.render]; omega
    have master := clear_fields_iff h₁ h₂ ho (by simp) (by simp) List.nil_prefix false
    simp only [left, right, List.length_append, List.length_singleton, Bool.false_eq_true,
      ite_false, List.map_injective_iff.mpr data_inj |>.eq_iff] at master
    have probes (hm : Q.master = P.master) :
        (¬ mismatch w u.length all.length (probeText Q.probes) (probeText P.probes) false) ↔
          Q.probes = P.probes := by
      have h₃ : w = u ++ (probeText Q.probes ++ .bang ::
          ((Q.master.map Token.data ++ [.stop]) ++ (mid ++ P.render))) := by
        simp [w, split, Packet.render, List.append_assoc]
      have h₄ :
          w = all ++ (probeText P.probes ++ .bang :: (P.master.map Token.data ++ [.stop])) := by
        simp [w, Packet.render, List.append_assoc]
      have horder : u.length + (probeText Q.probes).length < all.length := by
        rw [split]; simp [Packet.render]
      simpa only [Bool.false_eq_true, ite_false, probes_inj.eq_iff] using
        clear_fields_iff h₃ h₄ horder (no_bang _) (no_bang _)
          (by rw [hm]; exact List.prefix_append ..) false
    change (_ ∧ _) ↔ Q = P
    rw [master]
    constructor
    · rintro ⟨hp, hm⟩
      have he := (probes hm).mp hp
      exact (show ∀ a b : Packet α, a.probes = b.probes → a.master = b.master → a = b by
        rintro ⟨_, _⟩ ⟨_, _⟩ rfl rfl; rfl) Q P he hm
    · intro he
      exact ⟨(probes (congrArg Packet.master he)).mpr (congrArg Packet.probes he),
        congrArg Packet.master he⟩
  constructor
  · intro h Q hQ
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hQ
    exact (tests ⟨i,hi⟩).mp (h _)
  · intro h i
    exact (tests i).mpr (h _ (List.getElem_mem _))

variable {D : Type*} {t : ℕ}

/-- Encode a cell with a record marker, the column and row in `p` bits each, least significant
bit first, and its tile. -/
def record (p x y : ℕ) (d : D) : List (CellLetter D) :=
  [.record] ++ (List.range p).map (fun i => .bit (x.testBit i)) ++
    (List.range p).map (fun i => .bit (y.testBit i)) ++ [.tile d]

/-- List the square's coordinates one row at a time, advancing the column first. -/
def rowOrder (s : ℕ) := (List.finRange s).flatMap fun y => (List.finRange s).map fun x => (x, y)

/-- List the square's coordinates one column at a time, advancing the row first. -/
def colOrder (s : ℕ) := (List.finRange s).flatMap fun x => (List.finRange s).map fun y => (x, y)

/-- Concatenate the grid's cell records in row-major order. -/
def masterWord (I : Square D) (g : I.Grid) :=
  (rowOrder I.side).flatMap fun (x, y) => record I.p x y (g x y)

/-- Form a row-major master and, in column-major order, one complete master suffix starting at
each cell. -/
def gridPacket (I : Square D) (g : I.Grid) : Packet (CellLetter D) :=
  let b := masterWord I g
  ⟨(colOrder I.side).map (fun (x, y) => b.drop ((y.val * I.side + x.val) * (2 * I.p + 2))), b⟩

/-- Repeat the rendered packet once for each of the `2*p` bit checkers and once for the tile
checker. -/
def copies (I : Square D) (P : Packet (CellLetter D)) :=
  (List.replicate (2 * I.p + 1) P.render).flatten

/-- The master lists a grid in row-major order satisfying horizontal and boundary tests. The
exposed probe records list a grid in column-major order satisfying vertical tests. -/
def Checks [Fintype D] (I : Square D) (P : Packet (CellLetter D)) : Prop :=
  ∃ g h : I.Grid, P.master = masterWord I g ∧
    List.Forall₂ (fun (xy : Fin I.side × Fin I.side) a =>
      record I.p xy.1 xy.2 (h xy.1 xy.2) <+: a)
      (colOrder I.side) P.probes ∧
    ({ I with vertical := Finset.univ } : Square D).Valid g ∧
    ∀ x y (hy : y.val + 1 < I.side), (h x y, h x ⟨y.val + 1, hy⟩) ∈ I.vertical

end DeciNSSE.Complexity.Tiling
