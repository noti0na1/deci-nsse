import DeciNSSE.Complexity.Tiling.Numbering

/-! # Fixed-width codes on stopping tables

## Main declarations

- `FixedCode` specifies complete codewords and the states reached at proper prefixes.
- `FixedCode.hole_iff` reflects and preserves holes on all input words.
-/

namespace DeciNSSE.Complexity.Tiling
open Holes CoAlignment
open scoped List
variable {α β : Type*}

/-- A fixed-width code gives injective spellings of one positive length and a decoder whose
phases recognize proper prefixes and complete codewords. -/
structure FixedCode (α β : Type*) where
  /-- The codeword of a source letter. -/
  spell : α → List β
  /-- The number of output letters per codeword. -/
  width : ℕ
  /-- A codeword contains at least one letter. -/
  pos : 0 < width
  /-- Every spelling has the prescribed width. -/
  length : ∀ a, (spell a).length = width
  /-- Distinct letters have distinct spellings. -/
  inj : Function.Injective spell
  /-- The number of decoder phases, including the codeword boundary. -/
  phases : ℕ
  /-- Read one output letter, returning a partial phase, a decoded letter or failure. -/
  parse : ℕ → β → Option (ℕ ⊕ α)
  /-- The word read since the last boundary represents the given phase. -/
  partialWord : List β → ℕ → Prop
  /-- The empty prefix represents phase zero. -/
  initial : partialWord [] 0
  /-- Every represented phase lies within the allocated range. -/
  bounded : ∀ {p i}, partialWord p i → i < phases
  /-- A partial word in phase zero is empty. -/
  boundary : ∀ {p}, partialWord p 0 → p = []
  /-- A successful transition extends a partial word or completes the spelling of a letter. -/
  advance : ∀ {p i b v}, partialWord p i → parse i b = some v →
    match v with
    | .inl j => partialWord (p ++ [b]) j
    | .inr a => spell a = p ++ [b]
  /-- Every next letter of a genuine codeword takes the corresponding partial or final
  transition. -/
  complete : ∀ {a p b r i}, partialWord p i → spell a = p ++ b :: r →
    if r = [] then parse i b = some (.inr a)
    else ∃ j, parse i b = some (.inl j) ∧ partialWord (p ++ [b]) j

namespace FixedCode
variable (C : FixedCode α β) (M : StoppingTable α)

/-- Encode a word by concatenating the spellings of its letters. -/
def encode (u : List α) := u.flatMap C.spell

/-- Encoding a concatenation concatenates the two encodings. -/
@[simp] theorem encode_append (u v : List α) : C.encode (u ++ v) = C.encode u ++ C.encode v :=
  List.flatMap_append

/-- The encoded length equals the number of source letters times the code width. -/
@[simp] theorem encode_length (u : List α) : (C.encode u).length = u.length * C.width := by
  simp [encode, List.length_flatMap, C.length]

/-- Taking a prefix ending at a codeword boundary encodes the corresponding prefix of source
letters. -/
theorem take_encode (u : List α) (i : ℕ) :
    (C.encode u).take (i*C.width) = C.encode (u.take i) := by
  induction u generalizing i with
  | nil => simp [encode]
  | cons a u ih =>
    cases i with
    | zero => simp [encode]
    | succ i =>
      rw [show (i+1)*C.width = (C.spell a).length + i*C.width
        by rw [C.length, Nat.succ_mul, Nat.add_comm], List.take_succ_cons]
      change (C.spell a ++ C.encode u).take ((C.spell a).length + i*C.width) = _
      rw [List.take_length_add_append, ih]; rfl

/-- Dropping a whole number of codewords encodes the remaining source letters. -/
theorem drop_encode (u : List α) (i : ℕ) :
    (C.encode u).drop (i*C.width) = C.encode (u.drop i) := by
  apply List.append_cancel_left (as := C.encode (u.take i))
  rw [← encode_append, List.take_append_drop, ← C.take_encode, List.take_append_drop]

/-- The fixed-width encoding determines its source word. -/
theorem encode_injective : Function.Injective C.encode := by
  intro u
  induction u with
  | nil =>
    intro v h
    have := congrArg List.length h
    simp only [encode_length, List.length_nil, Nat.zero_mul] at this
    simpa [eq_comm, Nat.mul_eq_zero, Nat.ne_of_gt C.pos] using this
  | cons a u ih =>
    intro v h
    cases v with
    | nil =>
      have hl := congrArg List.length h
      simp [C.pos.ne', encode_length] at hl
    | cons b v =>
      obtain ⟨he, ht⟩ := List.append_inj
        (show C.spell a ++ C.encode u = C.spell b ++ C.encode v from h)
        (by simp [C.length])
      rw [C.inj he, ih ht]

/-- One encoded word is a prefix of another exactly when their source words are in the same
prefix relation. -/
theorem prefix_encode {u v : List α} : C.encode u <+: C.encode v ↔ u <+: v := by
  rw [List.prefix_iff_eq_take, encode_length, take_encode, C.encode_injective.eq_iff,
    ← List.prefix_iff_eq_take]

/-- Pair the current source state with a decoder phase, carrying targets and admissions only at
codeword boundaries. -/
def numbering : Numbering β (Fin M.size × ℕ) where
  states := (List.finRange M.size).flatMap fun q => (List.range C.phases).map (q, ·)
  start := (M.start,0)
  go s b := (C.parse s.2 b).map fun
    | .inl j => (s.1,j)
    | .inr a => (M.step s.1 a,0)
  final s := s.2 == 0 && s.1 ∈ M.target
  rel s r := s.2 == 0 && r.2 == 0 && (s.1,r.1) ∈ M.pairs
  initial := by simp [M.start_clear]

private theorem named (s : Fin M.size) {p i} (hp : C.partialWord p i) :
    (s,i) ∈ (C.numbering M).names := by
  apply Numbering.mem_names
  exact List.mem_flatMap.mpr
    ⟨s, List.mem_finRange _, List.mem_map.mpr ⟨i, List.mem_range.mpr (C.bounded hp), rfl⟩⟩

private theorem sound (w : List β) {s i}
    (h : (C.numbering M).read ((C.numbering M).table.dfa.eval w) = some (s,i)) :
    ∃ u p, w = C.encode u ++ p ∧ M.dfa.eval u = s ∧ C.partialWord p i := by
  induction w using List.reverseRecOn generalizing s i with
  | nil =>
    change some (M.start,0) = some (s,i) at h
    cases h; exact ⟨[],[],rfl,rfl,C.initial⟩
  | append_singleton w b ih =>
    rw [DFA.eval_append_singleton] at h
    obtain ⟨⟨q,j⟩, read, _, go, _⟩ := ((C.numbering M).read_step ..).mp h
    obtain ⟨u,p,rfl,eq,hp⟩ := ih read
    change (C.parse j b).map _ = some (s,i) at go
    cases z : C.parse j b with
    | none => simp [z] at go
    | some v =>
      have ha := C.advance hp z
      cases v with
      | inl k =>
        simp [z] at go
        obtain ⟨rfl,rfl⟩ := go
        exact ⟨u,p ++ [b], List.append_assoc .., eq, ha⟩
      | inr a =>
        simp [z] at go
        obtain ⟨rfl,rfl⟩ := go
        exact ⟨u++[a], [], by simp [encode, ha, List.append_assoc],
          by rw [DFA.eval_append_singleton, eq]; rfl, C.initial⟩

private theorem finish (q : Fin M.size) (hq : q ∉ M.target) (a : α) :
    ∀ (rest p : List β) i s, C.partialWord p i → C.spell a = p ++ rest → rest ≠ [] →
      (C.numbering M).read s = some (q,i) →
      (C.numbering M).read ((C.numbering M).table.dfa.evalFrom s rest) = some (M.step q a,0) := by
  intro rest
  induction rest with
  | nil => simp
  | cons b rest ih =>
    intro p i s hp he _ hr
    have advance := C.complete hp he
    have nf : (C.numbering M).final (q,i) = false := by simp [numbering, hq]
    by_cases empty : rest = []
    · subst rest
      simp only [ite_true] at advance
      apply ((C.numbering M).read_step s b _).mpr
      exact ⟨(q,i), hr, nf, by simp [numbering, advance], C.named M _ C.initial⟩
    · rw [ite_eq_right empty] at advance
      obtain ⟨j, hj, hpiece⟩ := advance
      apply ih (p++[b]) j _ hpiece (by simpa [List.append_assoc] using he) empty
      exact ((C.numbering M).read_step s b _).mpr
        ⟨(q,i), hr, nf, by simp [numbering, hj], C.named M _ hpiece⟩

private theorem proper_clear {u : List α} (ht : M.dfa.eval u ∈ M.target) {p : List α}
    (hp : p <+: u) (hl : p.length < u.length) : M.dfa.eval p ∉ M.target := by
  intro bad
  obtain ⟨t, rfl⟩ := hp
  cases t with
  | nil => simp at hl
  | cons a t =>
    change M.dfa.evalFrom M.start _ ∈ M.target at ht
    rw [DFA.evalFrom_of_append, DFA.evalFrom_cons] at ht
    change M.dfa.evalFrom (M.step (M.dfa.eval p) a) t ∈ M.target at ht
    rw [M.stop _ bad] at ht
    have sink (v : List α) : M.dfa.evalFrom M.sink v = M.sink := by
      induction v with
      | nil => rfl
      | cons a w ih => simpa [DFA.evalFrom_cons, StoppingTable.dfa, M.absorb] using ih
    rw [sink] at ht; exact M.sink_clear ht

private theorem at_boundary {u : List α} (ht : M.dfa.eval u ∈ M.target)
    (v : List α) (hv : v <+: u) :
    (C.numbering M).read ((C.numbering M).table.dfa.eval (C.encode v)) = some (M.dfa.eval v,0) := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v a ih =>
    have hp := (List.prefix_append v [a]).trans hv
    have hl := hv.length_le
    simp only [List.length_append, List.length_singleton] at hl
    have step := C.finish M _ (proper_clear M ht hp (by omega)) a (C.spell a) [] 0 _
      C.initial rfl (fun h => C.pos.ne' (by rw [← C.length a,h]; rfl)) (ih hp)
    simpa only [encode, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_singleton, StoppingTable.dfa] using step

private theorem state_target (w : List β) :
    (C.numbering M).table.dfa.eval w ∈ (C.numbering M).table.target ↔
      ∃ u, w = C.encode u ∧ M.dfa.eval u ∈ M.target := by
  rw [Numbering.target_iff]
  constructor
  · rintro ⟨⟨q,i⟩, h, final⟩
    obtain ⟨rfl, ht⟩ : i = 0 ∧ q ∈ M.target := by simpa [numbering] using final
    obtain ⟨u,p,he,rfl,hp⟩ := C.sound M w h
    exact ⟨u, by simpa [C.boundary hp] using he, ht⟩
  · rintro ⟨u,rfl,ht⟩
    exact ⟨_, C.at_boundary M ht u (List.prefix_refl _), by simp [numbering, ht]⟩

private theorem pair (x y : Fin (C.numbering M).table.size) :
    (x,y) ∈ (C.numbering M).table.pairs ↔ ∃ q r,
      (C.numbering M).read x = some (q,0) ∧ (C.numbering M).read y = some (r,0) ∧
        (q,r) ∈ M.pairs := by
  rw [Numbering.pair_iff _ (fun ⟨q,i⟩ => by simp [numbering, M.irrefl])]
  simp only [numbering, Prod.exists, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨q, i, r, j, hx, hy, ⟨rfl,rfl⟩, hm⟩
    exact ⟨q,r,hx,hy,hm⟩
  · rintro ⟨q,r,hx,hy,hm⟩
    exact ⟨q,0,r,0,hx,hy,⟨rfl,rfl⟩,hm⟩

/-- An admission can only relate two complete concatenations of codewords. -/
theorem pair_boundaries (a b : List β)
    (h : ((M.decode C.phases C.parse).dfa.eval a, (M.decode C.phases C.parse).dfa.eval b) ∈
      (M.decode C.phases C.parse).pairs) : ∃ u v, a = C.encode u ∧ b = C.encode v := by
  obtain ⟨q,r,ha,hb,_⟩ := (C.pair M ..).mp h
  obtain ⟨u,p,hu,_,hp⟩ := C.sound M _ ha
  obtain ⟨v,t,hv,_,ht⟩ := C.sound M _ hb
  exact ⟨u,v,by simpa [C.boundary hp] using hu,by simpa [C.boundary ht] using hv⟩

/-- A word is a hole of the decoder table exactly when it is the encoding of a source-table
hole. -/
theorem hole_iff (w : List β) :
    (M.decode C.phases C.parse).Hole w ↔ ∃ u, M.Hole u ∧ w = C.encode u := by
  let P := C.numbering M
  change P.table.Hole w ↔ _
  simp only [StoppingTable.Hole, isReaderHole_iff, Finset.mem_coe]
  rw [C.state_target M]
  constructor
  · rintro ⟨⟨u,rfl,ht⟩, clear⟩
    refine ⟨u,⟨ht, ?_⟩,rfl⟩
    intro s e hse he pref rel
    apply clear (s*C.width) (e*C.width) ((Nat.mul_lt_mul_right C.pos).mpr hse)
      (by rw [encode_length]; exact Nat.mul_le_mul_right _ he)
    · rw [drop_encode, drop_encode, prefix_encode]; exact pref
    · rw [take_encode, take_encode, C.pair M]
      exact ⟨_,_,C.at_boundary M ht _ (List.take_prefix ..),
        C.at_boundary M ht _ (List.take_prefix ..), rel⟩
  · rintro ⟨u,⟨ht,clear⟩,rfl⟩
    refine ⟨⟨u,rfl,ht⟩,?_⟩
    intro s e hse he pref rel
    have cut (j : ℕ) (hj : j ≤ (C.encode u).length) (q)
        (read : P.read (P.table.dfa.eval ((C.encode u).take j)) = some (q,0)) :
        ∃ i ≤ u.length, j = i * C.width ∧ q = M.dfa.eval (u.take i) := by
      obtain ⟨v,p,hv,_,hp⟩ := C.sound M _ read
      rw [C.boundary hp, List.append_nil] at hv
      have hlen := congrArg List.length hv
      rw [List.length_take, Nat.min_eq_left hj, encode_length] at hlen
      refine ⟨v.length,
        (Nat.le_of_mul_le_mul_right (by simpa only [hlen, encode_length] using hj) C.pos),
        hlen, ?_⟩
      rw [hlen, take_encode] at read
      exact congrArg Prod.fst
        (Option.some.inj (read.symm.trans (C.at_boundary M ht _ (List.take_prefix ..))))
    obtain ⟨q,r,hq,hr,hm⟩ := (C.pair M _ _).mp rel
    obtain ⟨i,_,rfl,rfl⟩ := cut s (by omega) q hq
    obtain ⟨j,hj,rfl,rfl⟩ := cut e he r hr
    rw [drop_encode, drop_encode, prefix_encode] at pref
    exact clear i j ((Nat.mul_lt_mul_right C.pos).mp hse) hj pref hm

end FixedCode
end DeciNSSE.Complexity.Tiling
