import DeciNSSE.Satisfiability.VarianceShape
import DeciNSSE.Transfer.RankedExtension

/-! # The four-spine extension

A top-prefix witness along `w` for signed roots `X` and `Y` is a solution whose
normalization has a top of `X` and no top of `Y` on the prefixes of `w`. The
variance extension imposes it with two spines of fresh variables: one from the
base of `X` whose last position is a polarized top, and one from the base of `Y`
whose last position is a polarized constructor bound. Position `j` of a spine is
bounded by a constructor whose child at the letter `w[j]` is position `j + 1`
and whose other children are fillers, a bottom and a top variable chosen by
variance. The side of the bound is the sign of the root shifted by the polarity
of `w[:j]`.

The signed translation of the variance extension is the four-spine extension: a
lower spine from `X` ending in top, a lower spine from `σY` ending in a lower
constructor bound, and their sign duals, an upper spine from `σX` ending in
bottom and an upper spine from `Y` ending in an upper constructor bound. Fresh
lower positions and bottom fillers are sources, their sign duals are sinks.

A solution of the variance extension restricts to a witness. Conversely, a
witness extends along the traces of its roots. Hence a witness exists exactly
when the variance extension is satisfiable, that is, when the four-spine
extension has no label clash.

## Main declarations

- `Spine.varianceExtension`, `Spine.extension`: the variance extension and its signed
  translation, the four-spine extension.
- `Spine.Closure.mem_extension`: the literals of the four-spine extension.
- `Spine.Closure.extension_ranked`: the four-spine extension is a ranked source and sink
  extension of the signed translation.
- `Spine.Closure.witness_of_sat`, `Spine.Closure.extend_sat`,
  `Spine.Closure.witness_iff_not_labelClash`: witnesses and solutions of the variance
  extension.
-/

namespace DeciNSSE.Spine.Closure

/-- A constructor with bottom children lies below exactly the non-bottom trees. -/
theorem node_bot_le_iff {n : ℕ} (t : Tree n) :
    Tree.node (fun _ => Tree.bot) ≤ t ↔ t ≠ Tree.bot := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨a, rfl⟩
  · simp only [Tree.le_bot_iff, Tree.node_ne_bot, ne_eq, not_true_eq_false]
  · simp
  · simp

open SignDuality Safety

variable {n k : ℕ}

theorem signed_ext {K : ℕ} {z z' : V (2 * K)} (hb : base z = base z') (hs : sign z = sign z') :
    z = z' := by
  rw [← sv_base_sign z, ← sv_base_sign z', hb, hs]

theorem flipV_injective {K : ℕ} : Function.Injective (flipV (k := K)) := fun a b h => by
  simpa using congrArg flipV h

section Layout

/-- Embed a signed variable, keeping the index of its base and its sign. -/
def lift {M : ℕ} (z : V (2 * k)) : V (2 * (k + M)) := sv (Fin.castAdd M (base z)) (sign z)

variable {M : ℕ}

@[simp] theorem base_lift (z : V (2 * k)) : base (lift (M := M) z) = Fin.castAdd M (base z) := by
  simp [lift]

@[simp] theorem sign_lift (z : V (2 * k)) : sign (lift (M := M) z) = sign z := by simp [lift]

@[simp] theorem flipV_lift (z : V (2 * k)) : flipV (lift (M := M) z) = lift (flipV z) := by
  simp [lift, flipV]

theorem base_lift_lt (z : V (2 * k)) : (base (lift (M := M) z)).val < k := by
  simp

theorem lift_injective : Function.Injective (lift (k := k) (M := M)) := fun a b h =>
  signed_ext (Fin.castAdd_injective k M (by simpa using congrArg base h))
    (by simpa using congrArg sign h)

/-- Offset of the fresh bases of a spine pair: the pairs through `X` come first. -/
def boff (m : ℕ) : Bool → ℕ
  | false => 0
  | true => m

theorem boff_le (m : ℕ) (s : Bool) : boff m s ≤ m := by cases s <;> simp [boff]

/-- The roots of the two lower spines: `X` (`false`) and `σY` (`true`). -/
def lroot (X Y : V (2 * k)) : Bool → V (2 * k)
  | false => X
  | true => flipV Y

variable (c : Fin n → Bool) (X Y : V (2 * k)) (w : List (Fin n))

/-- The base of position `j` of the spine `s`: the base of the root at position `0`,
and the fresh variable `k + boff |w| s + j - 1` at a position `0 < j ≤ |w|`. -/
def pbase (s : Bool) (j : ℕ) : V (k + (2 * w.length + 2)) :=
  if h : 0 < j ∧ j ≤ w.length then
    ⟨k + boff w.length s + j - 1, by have := boff_le w.length s; have := h.2; omega⟩
  else Fin.castAdd _ (base (lroot X Y s))

/-- The sign of position `j` of the spine `s`: the sign of the root shifted by the
polarity of `w[:j]`. -/
def psign (s : Bool) (j : ℕ) : Bool := Bool.xor (sign (lroot X Y s)) (polarity c (w.take j))

/-- The filler variables: `fbase false` is constrained to bottom and `fbase true` to top. -/
def fbase (q : Bool) : V (k + (2 * w.length + 2)) :=
  ⟨k + 2 * w.length + q.toNat, by have := Bool.toNat_le q; omega⟩

/-- Position `j` of the lower spine `s`, `P_j` (`s = false`) or `W_j` (`s = true`): the
base `pbase s j` at the sign `psign s j`. Position `0` is the lifted root. Its sign dual
is position `j` of the paired upper spine, `Q_j` or `Y_j`. -/
def lv (s : Bool) (j : ℕ) : V (2 * (k + (2 * w.length + 2))) :=
  sv (pbase X Y w s j) (psign c X Y w s j)

/-- The bottom filler of sign `q`; its sign dual is the top filler of sign `!q`. -/
def bfill (q : Bool) : V (2 * (k + (2 * w.length + 2))) := sv (fbase w q) q

/-- Children of the link at position `j` of the lower spine `s` reading `i`: the
next position at `i`, and the bottom filler of the coherent sign elsewhere. -/
def kids (s : Bool) (j : ℕ) (i i' : Fin n) : V (2 * (k + (2 * w.length + 2))) :=
  if i' = i then lv c X Y w s (j + 1)
  else bfill w (Bool.xor (sign (lv c X Y w s j)) (c i'))

/-- Children of the terminal lower bound of `W_m`: bottom fillers of the coherent signs. -/
def endKids (i' : Fin n) : V (2 * (k + (2 * w.length + 2))) :=
  bfill w (Bool.xor (sign (lv c X Y w true w.length)) (c i'))

/-- The variance literal whose signed forms are `f(a^{p ⊕ c}) ≤ u^p` and its sign dual:
a lower constructor bound of `u` when `p` is `false` and an upper one when `p` is `true`. -/
def lowerLit {K : ℕ} (p : Bool) (a : Fin n → V K) (u : V K) : Lit n K :=
  if p then .leF u a else .fLe a u

/-- The variance literal whose signed forms are `u^p = ⊤` and its sign dual. -/
def topLit {K : ℕ} (p : Bool) (u : V K) : Lit n K := if p then .eqBot u else .eqTop u

/-- Children of the variance link at position `j` of the spine `s` reading `i`: the base
of the next position at `i`, and the filler of the coherent sign elsewhere. -/
def linkKids (s : Bool) (j : ℕ) (i i' : Fin n) : V (k + (2 * w.length + 2)) :=
  if i' = i then pbase X Y w s (j + 1) else fbase w (Bool.xor (psign c X Y w s j) (c i'))

/-- The variance links of the spine `s`, one for each letter of `w`. -/
def links (s : Bool) : Constraint n (k + (2 * w.length + 2)) :=
  w.mapIdx fun j i => lowerLit (psign c X Y w s j) (linkKids c X Y w s j i) (pbase X Y w s j)

/-- The variance literals of the two spines: their links, the polarized top at the end of
the spine from `X`, the polarized constructor bound with filler children at the end of the
spine from `σY`, and the two fillers. -/
def spines : Constraint n (k + (2 * w.length + 2)) :=
  links c X Y w false ++ links c X Y w true ++
    [topLit (psign c X Y w false w.length) (pbase X Y w false w.length),
      lowerLit (psign c X Y w true w.length)
        (fun i' => fbase w (Bool.xor (psign c X Y w true w.length) (c i')))
        (pbase X Y w true w.length),
      .eqBot (fbase w false), .eqTop (fbase w true)]

/-- A literal of the lower half of the four spines: a link of a lower spine, `P_m = ⊤`,
`f(B, …, B) ≤ W_m`, or a bottom filler. -/
def LowerHalf (l : Lit n (2 * (k + (2 * w.length + 2)))) : Prop :=
  (∃ s j, ∃ hj : j < w.length, l = .fLe (kids c X Y w s j w[j]) (lv c X Y w s j)) ∨
    l = .eqTop (lv c X Y w false w.length) ∨
    l = .fLe (endKids c X Y w) (lv c X Y w true w.length) ∨ ∃ q, l = .eqBot (bfill w q)

end Layout

/-- The variance extension of `ϕ` along `w` for the signed roots `X` and `Y`: the system
on the old variables together with the two spines. -/
def _root_.DeciNSSE.Spine.varianceExtension (c : Fin n → Bool) (ϕ : Constraint n k)
    (X Y : V (2 * k)) (w : List (Fin n)) : Constraint n (k + (2 * w.length + 2)) :=
  ϕ.map (Lit.rename (Fin.castAdd _)) ++ spines c X Y w

/-- The four-spine extension of `ϕ` along `w` for the signed roots `X` and `Y`: the signed
translation of the variance extension. -/
def _root_.DeciNSSE.Spine.extension (c : Fin n → Bool) (ϕ : Constraint n k)
    (X Y : V (2 * k)) (w : List (Fin n)) : Constraint n (2 * (k + (2 * w.length + 2))) :=
  signed c (Spine.varianceExtension c ϕ X Y w)

section Positions

variable {c : Fin n → Bool} {X Y : V (2 * k)} {w : List (Fin n)}

@[simp] theorem kids_self (s : Bool) (j : ℕ) (i : Fin n) :
    kids c X Y w s j i i = lv c X Y w s (j + 1) := by simp [kids]

theorem kids_of_ne {s : Bool} {j : ℕ} {i i' : Fin n} (h : i' ≠ i) :
    kids c X Y w s j i i' = bfill w (Bool.xor (sign (lv c X Y w s j)) (c i')) := by
  simp [kids, h]

@[simp] theorem lv_zero (s : Bool) : lv c X Y w s 0 = lift (lroot X Y s) := by
  simp [lv, pbase, psign, lift]

theorem base_lv_val {s : Bool} {j : ℕ} (h : 0 < j ∧ j ≤ w.length) :
    (base (lv c X Y w s j)).val = k + boff w.length s + j - 1 := by
  simp [lv, pbase, h]

@[simp] theorem sign_lv (s : Bool) (j : ℕ) : sign (lv c X Y w s j) = psign c X Y w s j := by
  simp [lv]

theorem psign_succ (s : Bool) {j : ℕ} (hj : j < w.length) :
    psign c X Y w s (j + 1) = Bool.xor (psign c X Y w s j) (c w[j]) := by
  simp only [psign]
  rw [List.take_succ_eq_append_getElem hj, polarity_append_singleton, Bool.xor_assoc]

@[simp] theorem base_bfill_val (q : Bool) :
    (base (bfill (k := k) w q)).val = k + 2 * w.length + q.toNat := by simp [bfill, fbase]

@[simp] theorem sign_bfill (q : Bool) : sign (bfill (k := k) w q) = q := by simp [bfill]

theorem base_lv_lt {s : Bool} {j : ℕ} (hj : j ≤ w.length) :
    (base (lv c X Y w s j)).val < k + 2 * w.length := by
  by_cases h : 0 < j
  · rw [base_lv_val ⟨h, hj⟩]; have := boff_le w.length s; omega
  · obtain rfl : j = 0 := by omega
    rw [lv_zero]; have := base_lift_lt (M := 2 * w.length + 2) (lroot X Y s); omega

theorem lv_base_eq {s s' : Bool} {j j' : ℕ} (h : 0 < j ∧ j ≤ w.length)
    (h' : 0 < j' ∧ j' ≤ w.length) (he : base (lv c X Y w s j) = base (lv c X Y w s' j')) :
    s = s' ∧ j = j' := by
  have hv := congrArg Fin.val he
  rw [base_lv_val h, base_lv_val h'] at hv
  cases s <;> cases s' <;> simp only [boff] at hv <;> first | exact ⟨rfl, by omega⟩ | omega

theorem lv_ne_lift {s : Bool} {j : ℕ} (h : 0 < j ∧ j ≤ w.length) (u : V (2 * k)) :
    lv c X Y w s j ≠ lift u := by
  intro he
  have hv := congrArg (fun z => (base z).val) he
  simp only [base_lv_val h] at hv
  have := base_lift_lt (M := 2 * w.length + 2) u; omega

theorem lv_eq_lift {s : Bool} {j : ℕ} (hj : j ≤ w.length) {u : V (2 * k)}
    (h : lv c X Y w s j = lift u) : j = 0 ∧ u = lroot X Y s := by
  by_cases h0 : 0 < j
  · exact absurd h (lv_ne_lift ⟨h0, hj⟩ u)
  · obtain rfl : j = 0 := by omega
    exact ⟨rfl, (lift_injective (by simpa using h)).symm⟩

theorem flipV_lv_eq_lift {s : Bool} {j : ℕ} (hj : j ≤ w.length) {u : V (2 * k)}
    (h : flipV (lv c X Y w s j) = lift u) : j = 0 ∧ u = flipV (lroot X Y s) := by
  have h' : lv c X Y w s j = lift (flipV u) := by rw [← flipV_lift, ← h, flipV_flipV]
  obtain ⟨rfl, hu⟩ := lv_eq_lift hj h'
  exact ⟨rfl, by rw [← hu, flipV_flipV]⟩

theorem lv_eq_lv {s s' : Bool} {j j' : ℕ} (hj : j ≤ w.length) (hj' : j' ≤ w.length)
    (h : lv c X Y w s j = lv c X Y w s' j') : j = j' ∧ lroot X Y s = lroot X Y s' := by
  by_cases h0 : 0 < j <;> by_cases h0' : 0 < j'
  · obtain ⟨rfl, rfl⟩ := lv_base_eq ⟨h0, hj⟩ ⟨h0', hj'⟩ (congrArg base h)
    exact ⟨rfl, rfl⟩
  · obtain rfl : j' = 0 := by omega
    rw [lv_zero] at h; exact absurd h (lv_ne_lift ⟨h0, hj⟩ _)
  · obtain rfl : j = 0 := by omega
    rw [lv_zero] at h; exact absurd h.symm (lv_ne_lift ⟨h0', hj'⟩ _)
  · obtain rfl : j = 0 := by omega
    obtain rfl : j' = 0 := by omega
    exact ⟨rfl, lift_injective (by simpa using h)⟩

theorem lv_eq_flipV_lv {s s' : Bool} {j j' : ℕ} (hj : j ≤ w.length) (hj' : j' ≤ w.length)
    (h : lv c X Y w s j = flipV (lv c X Y w s' j')) :
    j = 0 ∧ j' = 0 ∧ lroot X Y s = flipV (lroot X Y s') := by
  by_cases h0 : 0 < j <;> by_cases h0' : 0 < j'
  · obtain ⟨rfl, rfl⟩ := lv_base_eq ⟨h0, hj⟩ ⟨h0', hj'⟩ (by rw [h, base_flipV])
    have hs := congrArg sign h
    rw [sign_flipV] at hs
    cases hc : sign (lv c X Y w s j) <;> simp [hc] at hs
  · obtain rfl : j' = 0 := by omega
    rw [lv_zero, flipV_lift] at h; exact absurd h (lv_ne_lift ⟨h0, hj⟩ _)
  · obtain rfl : j = 0 := by omega
    rw [lv_zero] at h
    exact absurd (flipV_lv_eq_lift hj' h.symm).1 (by omega)
  · obtain rfl : j = 0 := by omega
    obtain rfl : j' = 0 := by omega
    exact ⟨rfl, rfl, lift_injective (by simpa using h)⟩

theorem bfill_ne_lift (q : Bool) (u : V (2 * k)) : bfill w q ≠ lift u := by
  intro he
  have hv := congrArg (fun z => (base z).val) he
  simp only [base_bfill_val] at hv
  have := base_lift_lt (M := 2 * w.length + 2) u; omega

theorem bfill_ne_lv (q : Bool) {s : Bool} {j : ℕ} (hj : j ≤ w.length) :
    bfill w q ≠ lv c X Y w s j := by
  intro he
  have hv := congrArg (fun z => (base z).val) he
  simp only [base_bfill_val] at hv
  have := base_lv_lt (c := c) (X := X) (Y := Y) (s := s) hj; omega

theorem bfill_ne_flipV_lv (q : Bool) {s : Bool} {j : ℕ} (hj : j ≤ w.length) :
    bfill w q ≠ flipV (lv c X Y w s j) := by
  intro he
  have hv := congrArg (fun z => (base z).val) he
  simp only [base_bfill_val, base_flipV] at hv
  have := base_lv_lt (c := c) (X := X) (Y := Y) (s := s) hj; omega

theorem bfill_ne_flipV_bfill (q q' : Bool) : bfill (k := k) w q ≠ flipV (bfill w q') := by
  intro he
  have hb := congrArg (fun z => (base z).val) he
  have hs := congrArg sign he
  simp only [base_bfill_val, base_flipV, sign_bfill, sign_flipV] at hb hs
  cases q <;> cases q' <;> simp at hb hs

end Positions

section Literals

variable {c : Fin n → Bool} {ϕ : Constraint n k} {X Y : V (2 * k)} {w : List (Fin n)}

theorem mem_signedLit_lowerLit {K : ℕ} (p : Bool) (a : Fin n → V K) (u : V K)
    (l : Lit n (2 * K)) : l ∈ signedLit c (lowerLit p a u) ↔
      l = .fLe (fun i => sv (a i) (Bool.xor p (c i))) (sv u p) ∨
      dualFlip l = .fLe (fun i => sv (a i) (Bool.xor p (c i))) (sv u p) := by
  rw [dualFlip_eq_iff]
  cases p <;> simp [lowerLit, signedLit, dualFlip, Function.comp_def, or_comm]

theorem mem_signedLit_topLit {K : ℕ} (p : Bool) (u : V K) (l : Lit n (2 * K)) :
    l ∈ signedLit c (topLit p u) ↔ l = .eqTop (sv u p) ∨ dualFlip l = .eqTop (sv u p) := by
  rw [dualFlip_eq_iff]
  cases p <;> simp [topLit, signedLit, dualFlip, or_comm]

/-- The signed children of a variance link are the children of the lower link. -/
theorem sv_linkKids (s : Bool) {j : ℕ} (hj : j < w.length) :
    (fun i' => sv (linkKids c X Y w s j w[j] i') (Bool.xor (psign c X Y w s j) (c i'))) =
      kids c X Y w s j w[j] := by
  funext i'
  by_cases h : i' = w[j]
  · subst h
    simp only [linkKids, kids, ite_true, lv, psign_succ s hj]
  · simp [linkKids, kids, h, bfill]

/-- The literals of the four-spine extension: the lifted signed translation, the lower
half of the spines, and its sign dual. -/
theorem mem_extension {l : Lit n (2 * (k + (2 * w.length + 2)))} :
    l ∈ Spine.extension c ϕ X Y w ↔ l ∈ (signed c ϕ).map (Lit.rename lift) ∨
      LowerHalf c X Y w l ∨ LowerHalf c X Y w (dualFlip l) := by
  have hlink (s : Bool) (m : Lit n (2 * (k + (2 * w.length + 2)))) :
      (∃ v ∈ links c X Y w s, m ∈ signedLit c v) ↔
        (∃ j, ∃ hj : j < w.length, m = .fLe (kids c X Y w s j w[j]) (lv c X Y w s j)) ∨
          ∃ j, ∃ hj : j < w.length,
            dualFlip m = .fLe (kids c X Y w s j w[j]) (lv c X Y w s j) := by
    simp only [links, List.mem_mapIdx, ← exists_or]
    constructor
    · rintro ⟨v, ⟨j, hj, rfl⟩, hm⟩
      rw [mem_signedLit_lowerLit, sv_linkKids s hj] at hm
      exact ⟨j, hj, hm⟩
    · rintro ⟨j, hj, hm⟩
      refine ⟨_, ⟨j, hj, rfl⟩, ?_⟩
      rwa [mem_signedLit_lowerLit, sv_linkKids s hj]
  have hend : (fun i' => sv (fbase w (Bool.xor (psign c X Y w true w.length) (c i')))
      (Bool.xor (psign c X Y w true w.length) (c i'))) = endKids c X Y w := by
    funext i'; simp [endKids, bfill]
  have hmap : (ϕ.map (Lit.rename (Fin.castAdd (2 * w.length + 2)))).flatMap (signedLit c) =
      (signed c ϕ).map (Lit.rename lift) := by
    simp only [signed, List.flatMap_map, List.map_flatMap, signedLit_rename]; rfl
  have hfill (q : Bool) :
      (l = .eqTop (sv (fbase w q) (!q)) ↔ dualFlip l = .eqBot (bfill w q)) ∧
        (dualFlip l = .eqTop (sv (fbase w q) (!q)) ↔ l = .eqBot (bfill w q)) := by
    constructor <;> rw [dualFlip_eq_iff] <;> simp [dualFlip, bfill]
  have hbot := mem_signedLit_topLit (c := c) true (fbase w false) l
  have htop := mem_signedLit_topLit (c := c) false (fbase w true) l
  have hf := hfill false
  have ht := hfill true
  simp only [Bool.not_false, Bool.not_true] at hf ht
  simp only [topLit, ite_true, Bool.false_eq_true, ite_false, hf.1, hf.2, ht.1, ht.2]
    at hbot htop
  simp only [Spine.extension, Spine.varianceExtension, spines, signed, List.flatMap_append,
    List.mem_append, List.mem_flatMap (l := links _ _ _ _ _), hlink, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, mem_signedLit_lowerLit, mem_signedLit_topLit, hend,
    LowerHalf, Bool.exists_bool, hbot, htop, hmap]
  refine or_congr_right (Iff.of_eq ?_)
  simp only [lv]
  ac_rfl

theorem lift_mem {l : Lit n (2 * k)} (hl : l ∈ signed c ϕ) :
    l.rename lift ∈ Spine.extension c ϕ X Y w :=
  mem_extension.mpr (Or.inl (List.mem_map_of_mem hl))

theorem half_mem {l : Lit n (2 * (k + (2 * w.length + 2)))} (hl : LowerHalf c X Y w l) :
    l ∈ Spine.extension c ϕ X Y w := mem_extension.mpr (Or.inr (Or.inl hl))

theorem flip_half_mem {l : Lit n (2 * (k + (2 * w.length + 2)))} (hl : LowerHalf c X Y w l) :
    dualFlip l ∈ Spine.extension c ϕ X Y w :=
  mem_extension.mpr (Or.inr (Or.inr (by rwa [dualFlip_dualFlip])))

theorem link_mem (s : Bool) {j : ℕ} (hj : j < w.length) :
    Lit.fLe (kids c X Y w s j w[j]) (lv c X Y w s j) ∈ Spine.extension c ϕ X Y w :=
  half_mem (Or.inl ⟨s, j, hj, rfl⟩)

theorem flip_link_mem (s : Bool) {j : ℕ} (hj : j < w.length) :
    Lit.leF (flipV (lv c X Y w s j)) (flipV ∘ kids c X Y w s j w[j]) ∈
      Spine.extension c ϕ X Y w :=
  flip_half_mem (Or.inl ⟨s, j, hj, rfl⟩)

theorem top_mem : Lit.eqTop (lv c X Y w false w.length) ∈ Spine.extension c ϕ X Y w :=
  half_mem (Or.inr (Or.inl rfl))

theorem bot_mem : Lit.eqBot (flipV (lv c X Y w false w.length)) ∈ Spine.extension c ϕ X Y w :=
  flip_half_mem (l := .eqTop _) (Or.inr (Or.inl rfl))

theorem end_mem :
    Lit.fLe (endKids c X Y w) (lv c X Y w true w.length) ∈ Spine.extension c ϕ X Y w :=
  half_mem (Or.inr (Or.inr (Or.inl rfl)))

theorem flip_end_mem :
    Lit.leF (flipV (lv c X Y w true w.length)) (flipV ∘ endKids c X Y w) ∈
      Spine.extension c ϕ X Y w :=
  flip_half_mem (l := .fLe _ _) (Or.inr (Or.inr (Or.inl rfl)))

theorem bfill_mem (q : Bool) : Lit.eqBot (bfill w q) ∈ Spine.extension c ϕ X Y w :=
  half_mem (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))

/-- Lower constructor literals: lifted, a link of a lower spine, or the terminal bound of `W_m`. -/
theorem mem_fLe {a : Fin n → V (2 * (k + (2 * w.length + 2)))}
    {u : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.fLe a u ∈ Spine.extension c ϕ X Y w) :
    (∃ a' u', Lit.fLe a' u' ∈ signed c ϕ ∧ a = lift ∘ a' ∧ u = lift u') ∨
      (∃ s j, ∃ hj : j < w.length, a = kids c X Y w s j w[j] ∧ u = lv c X Y w s j) ∨
      (a = endKids c X Y w ∧ u = lv c X Y w true w.length) := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (fLe_mem_rename h)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.fLe.injEq, reduceCtorEq] at he
    · exact Or.inr (Or.inl ⟨s, j, hj, he⟩)
    · exact Or.inr (Or.inr he)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp [dualFlip] at he

theorem eq_flipV_of_flipV_eq {K : ℕ} {z z' : V (2 * K)} (h : flipV z = z') : z = flipV z' := by
  rw [← h, flipV_flipV]

/-- Upper constructor literals: lifted, or the sign dual of a lower spine literal. -/
theorem mem_leF {v : V (2 * (k + (2 * w.length + 2)))}
    {b : Fin n → V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.leF v b ∈ Spine.extension c ϕ X Y w) :
    (∃ v' b', Lit.leF v' b' ∈ signed c ϕ ∧ v = lift v' ∧ b = lift ∘ b') ∨
      (∃ s j, ∃ hj : j < w.length,
        b = flipV ∘ kids c X Y w s j w[j] ∧ v = flipV (lv c X Y w s j)) ∨
      (b = flipV ∘ endKids c X Y w ∧ v = flipV (lv c X Y w true w.length)) := by
  have hb {a : Fin n → V (2 * (k + (2 * w.length + 2)))} (h : flipV ∘ b = a) : b = flipV ∘ a := by
    rw [← h]; funext i; simp
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (leF_mem_rename h)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp at he
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.fLe.injEq, reduceCtorEq] at he
    · exact Or.inr (Or.inl ⟨s, j, hj, hb he.1, eq_flipV_of_flipV_eq he.2⟩)
    · exact Or.inr (Or.inr ⟨hb he.1, eq_flipV_of_flipV_eq he.2⟩)

theorem mem_eqTop {u : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.eqTop u ∈ Spine.extension c ϕ X Y w) :
    (∃ u', Lit.eqTop u' ∈ signed c ϕ ∧ u = lift u') ∨ u = lv c X Y w false w.length ∨
      ∃ q, u = flipV (bfill w q) := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (eqTop_mem_rename h)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.eqTop.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inl he)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.eqBot.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inr ⟨q, eq_flipV_of_flipV_eq he⟩)

theorem mem_eqBot {v : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.eqBot v ∈ Spine.extension c ϕ X Y w) :
    (∃ v', Lit.eqBot v' ∈ signed c ϕ ∧ v = lift v') ∨ v = flipV (lv c X Y w false w.length) ∨
      ∃ q, v = bfill w q := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (eqBot_mem_rename h)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.eqBot.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inr ⟨q, he⟩)
  · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.eqTop.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inl (eq_flipV_of_flipV_eq he))

end Literals

section Ranked

variable (c : Fin n → Bool) (X Y : V (2 * k)) (w : List (Fin n))

/-- Sources: fresh lower spine positions and bottom fillers. -/
def Source (z : V (2 * (k + (2 * w.length + 2)))) : Prop :=
  (∃ s j, 0 < j ∧ j ≤ w.length ∧ z = lv c X Y w s j) ∨ ∃ q, z = bfill w q

/-- Sinks: the sign duals of sources, fresh upper spine positions and top fillers. -/
def Sink (z : V (2 * (k + (2 * w.length + 2)))) : Prop := Source c X Y w (flipV z)

variable {c X Y w}

theorem not_source_lift (u : V (2 * k)) : ¬ Source c X Y w (lift u) := by
  rintro (⟨s, j, h0, hj, he⟩ | ⟨q, he⟩)
  · exact lv_ne_lift ⟨h0, hj⟩ u he.symm
  · exact bfill_ne_lift q u he.symm

theorem not_source_flipV_lv {s : Bool} {j : ℕ} (hj : j ≤ w.length) :
    ¬ Source c X Y w (flipV (lv c X Y w s j)) := by
  rintro (⟨s', j', h0, hj', he⟩ | ⟨q, he⟩)
  · exact absurd (lv_eq_flipV_lv hj' hj he.symm).1 (by omega)
  · exact bfill_ne_flipV_lv q hj he.symm

theorem not_source_flipV_bfill (q : Bool) : ¬ Source c X Y w (flipV (bfill w q)) := by
  rintro (⟨s, j, h0, hj, he⟩ | ⟨q', he⟩)
  · have he' := congrArg flipV he
    rw [flipV_flipV] at he'
    exact bfill_ne_flipV_lv q hj he'
  · exact bfill_ne_flipV_bfill q' q he.symm

theorem source_lv {s : Bool} {j : ℕ} (h : 0 < j ∧ j ≤ w.length) : Source c X Y w (lv c X Y w s j) :=
  Or.inl ⟨s, j, h.1, h.2, rfl⟩

theorem source_bfill (q : Bool) : Source c X Y w (bfill w q) := Or.inr ⟨q, rfl⟩

theorem sink_flipV_bfill (q : Bool) : Sink c X Y w (flipV (bfill w q)) := by
  simp only [Sink, flipV_flipV]; exact source_bfill q

theorem lowerHalf_fresh {a : Fin n → V (2 * (k + (2 * w.length + 2)))}
    {u : V (2 * (k + (2 * w.length + 2)))} (h : LowerHalf c X Y w (.fLe a u)) :
    (∀ i, Source c X Y w (a i) ∧ (base u).val < (base (a i)).val) ∧
      ¬ Source c X Y w (flipV u) := by
  rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩
  · simp only [Lit.fLe.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun i => ?_, not_source_flipV_lv hj.le⟩
    by_cases hi : i = w[j]
    · rw [hi, kids_self]
      refine ⟨source_lv (j := j + 1) ⟨by omega, by omega⟩, ?_⟩
      rw [base_lv_val (j := j + 1) ⟨by omega, by omega⟩]
      by_cases h0 : 0 < j
      · rw [base_lv_val ⟨h0, hj.le⟩]; omega
      · obtain rfl : j = 0 := by omega
        rw [lv_zero]; have := base_lift_lt (M := 2 * w.length + 2) (lroot X Y s); omega
    · rw [kids_of_ne hi]
      refine ⟨source_bfill _, ?_⟩
      have := base_lv_lt (c := c) (X := X) (Y := Y) (s := s) hj.le
      simp only [base_bfill_val]; omega
  · simp at he
  · simp only [Lit.fLe.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨fun i => ⟨source_bfill _, ?_⟩, not_source_flipV_lv le_rfl⟩
    have := base_lv_lt (c := c) (X := X) (Y := Y) (s := true) (le_refl w.length)
    simp only [endKids, base_bfill_val]; omega
  · simp at he

theorem variable_cases (z : V (2 * (k + (2 * w.length + 2)))) :
    (∃ u, z = lift u) ∨ Source c X Y w z ∨ Sink c X Y w z := by
  obtain ⟨b, p, rfl⟩ := sv_cases z
  have hpair (z' : V (2 * (k + (2 * w.length + 2)))) (hz : Source c X Y w z')
      (hb : base z' = b) : Source c X Y w (sv b p) ∨ Sink c X Y w (sv b p) := by
    by_cases hp : p = sign z'
    · left; rwa [show sv b p = z' from signed_ext (by simp [hb]) (by simp [hp])]
    · right
      rwa [Sink, show flipV (sv b p) = z' from
        signed_ext (by simp [hb]) (by cases p <;> simp_all)]
  by_cases hb : b.val < k
  · exact Or.inl ⟨sv ⟨b.val, hb⟩ p, signed_ext (Fin.ext (by simp)) (by simp)⟩
  right
  by_cases hf : b.val < k + 2 * w.length
  · by_cases hs : b.val < k + w.length
    · exact hpair _ (source_lv (s := false) (j := b.val - k + 1) ⟨by omega, by omega⟩)
        (Fin.ext (by rw [base_lv_val ⟨by omega, by omega⟩]; simp [boff]; omega))
    · exact hpair _ (source_lv (s := true) (j := b.val - k - w.length + 1) ⟨by omega, by omega⟩)
        (Fin.ext (by rw [base_lv_val ⟨by omega, by omega⟩]; simp [boff]; omega))
  · have := b.isLt
    by_cases hq : b.val = k + 2 * w.length
    · exact hpair _ (source_bfill false) (Fin.ext (by simp; omega))
    · exact hpair _ (source_bfill true) (Fin.ext (by simp; omega))

variable (c X Y w) in
/-- The extension is a ranked source and sink extension of the signed
translation, ranked by base index. -/
theorem extension_ranked (ϕ : Constraint n k) :
    Ranked.Extension lift (signed c ϕ) (Spine.extension c ϕ X Y w) (Source c X Y w) (Sink c X Y w)
      (fun z => (base z).val) where
  injective := lift_injective
  not_source_old := not_source_lift
  not_sink_old u := by simpa [Sink] using not_source_lift (flipV u)
  source_not_sink := by
    rintro z (⟨s, j, h0, hj, rfl⟩ | ⟨q, rfl⟩)
    · exact not_source_flipV_lv hj
    · exact not_source_flipV_bfill q
  variable_cases := variable_cases
  old_mem := fun _ hl => lift_mem hl
  lower := by
    intro a u h
    rcases mem_extension.mp h with h | h | h
    · exact Or.inl (fLe_mem_rename h)
    · exact Or.inr (lowerHalf_fresh h)
    · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp [dualFlip] at he
  upper := by
    intro v b h
    rcases mem_extension.mp h with h | h | h
    · exact Or.inl (leF_mem_rename h)
    · rcases h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp at he
    · obtain ⟨hk, hn⟩ := lowerHalf_fresh h
      refine Or.inr ⟨fun i => ?_, by simpa using hn⟩
      obtain ⟨hs, hr⟩ := hk i
      exact ⟨by simpa [Sink] using hs, by simpa using hr⟩

variable {ϕ : Constraint n k}

/-- A derivation into a source is an identity. -/
theorem derives_into_source {a b : V (2 * (k + (2 * w.length + 2)))}
    (h : Derives (Spine.extension c ϕ X Y w) a b) (hb : Source c X Y w b) : a = b :=
  (extension_ranked c X Y w ϕ).derives_into_source h hb

/-- A derivation out of a sink is an identity. -/
theorem derives_out_of_sink {a b : V (2 * (k + (2 * w.length + 2)))}
    (h : Derives (Spine.extension c ϕ X Y w) a b) (ha : Sink c X Y w a) : b = a :=
  (extension_ranked c X Y w ϕ).derives_out_of_sink h ha

theorem derives_lift {u v : V (2 * k)} (h : Derives (signed c ϕ) u v) :
    Derives (Spine.extension c ϕ X Y w) (lift u) (lift v) :=
  ((extension_ranked c X Y w ϕ).derives_original u v).mpr h

end Ranked

section Solutions

variable {c : Fin n → Bool} {ϕ : Constraint n k} {X Y : V (2 * k)} {w : List (Fin n)}

/-- Along a lower spine, a solution stays below the trace of the spine root. -/
theorem lv_le_trace {M : V (2 * (k + (2 * w.length + 2))) → Tree n}
    (hM : Covariant.Sat M (Spine.extension c ϕ X Y w)) (s : Bool) :
    ∀ j ≤ w.length, M (lv c X Y w s j) ≤ trace (M (lv c X Y w s 0)) (w.take j)
  | 0, _ => by simp
  | j + 1, hj => by
    have hd := descend_mono (hM _ (link_mem (ϕ := ϕ) s (by omega : j < w.length))) w[j]
    simp only [descend_node, Function.comp_apply, kids_self] at hd
    rw [List.take_succ_eq_append_getElem (by omega), trace_append, trace_cons, trace_nil]
    exact le_trans hd (descend_mono (lv_le_trace hM s j (by omega)) _)

/-- Restriction to the old variables commutes with normalization. -/
theorem normalized_comp_castAdd (c : Fin n → Bool) {M : ℕ} (ρ : V (k + M) → Tree n) :
    normalized c (ρ ∘ Fin.castAdd M) = normalized c ρ ∘ lift := by
  funext z; simp [normalized]

/-- A solution of the variance extension restricts to a top-prefix witness. -/
theorem witness_of_sat {ρ : V (k + (2 * w.length + 2)) → Tree n}
    (hρ : Sat c ρ (Spine.varianceExtension c ϕ X Y w)) :
    Sat c (ρ ∘ Fin.castAdd _) ϕ ∧ covPrefTop w (normalized c (ρ ∘ Fin.castAdd _) X) ∧
      ¬ covPrefTop w (normalized c (ρ ∘ Fin.castAdd _) Y) := by
  have hM : Covariant.Sat (normalized c ρ) (Spine.extension c ϕ X Y w) :=
    (sat_iff_signed c ρ _).mp hρ
  rw [sat_iff_signed, normalized_comp_castAdd]
  refine ⟨(sat_rename lift _ _).mp fun l hl => hM _ (mem_extension.mpr (Or.inl hl)), ?_, ?_⟩
  · have h := lv_le_trace hM false w.length le_rfl
    rw [List.take_length, lv_zero, (hM _ top_mem : normalized c ρ _ = Tree.top)] at h
    exact (Tree.top_le_iff _).mp h
  · intro hy
    have h := lv_le_trace hM true w.length le_rfl
    rw [List.take_length, lv_zero] at h
    have hend : Tree.node (normalized c ρ ∘ endKids c X Y w) ≤
        normalized c ρ (lv c X Y w true w.length) := hM _ end_mem
    have hb (i : Fin n) : (normalized c ρ ∘ endKids c X Y w) i = Tree.bot := hM _ (bfill_mem _)
    rw [show (normalized c ρ ∘ endKids c X Y w) = fun _ => Tree.bot from funext hb] at hend
    have hne := (node_bot_le_iff _).mp (le_trans hend h)
    simp only [lroot, ← flipV_lift, normalized_flipV] at hne
    exact hne ((covPrefBot_dual w _).mpr hy)

variable (c X Y w) in
/-- The canonical extension of an assignment `ρ`: an old variable keeps its value; the
fresh variable of a spine position reads the trace of the normalized root along the
prefix of the position, oriented by the sign of the position; the fillers read bottom
and top. -/
def extend (ρ : V k → Tree n) (b : V (k + (2 * w.length + 2))) : Tree n :=
  if hb : b.val < k then ρ ⟨b.val, hb⟩
  else if b.val < k + 2 * w.length then
    Tree.normalize c
      (psign c X Y w (decide (k + w.length ≤ b.val))
        (b.val - k - boff w.length (decide (k + w.length ≤ b.val)) + 1))
      (trace (normalized c ρ (lroot X Y (decide (k + w.length ≤ b.val))))
        (w.take (b.val - k - boff w.length (decide (k + w.length ≤ b.val)) + 1)))
  else if b.val = k + 2 * w.length then Tree.bot else Tree.top

theorem extend_lift (ρ : V k → Tree n) (z : V (2 * k)) :
    normalized c (extend c X Y w ρ) (lift z) = normalized c ρ z := by
  simp [normalized, extend]

theorem extend_lv (ρ : V k → Tree n) (s : Bool) {j : ℕ} (hj : j ≤ w.length) :
    normalized c (extend c X Y w ρ) (lv c X Y w s j) =
      trace (normalized c ρ (lroot X Y s)) (w.take j) := by
  by_cases h0 : 0 < j
  · have hv := base_lv_val (c := c) (X := X) (Y := Y) (s := s) ⟨h0, hj⟩
    have hm := boff_le w.length s
    have hs : decide (k + w.length ≤ k + boff w.length s + j - 1) = s := by
      cases s
      · exact decide_eq_false (by simp only [boff]; omega)
      · exact decide_eq_true (by simp only [boff]; omega)
    have hj' : k + boff w.length s + j - 1 - k - boff w.length s + 1 = j := by omega
    simp only [normalized, extend, hv, hs, hj', sign_lv]
    rw [dite_eq_right (by omega), ite_eq_left (by omega), normalize_involutive]
  · obtain rfl : j = 0 := by omega
    rw [lv_zero, extend_lift]; rfl

theorem extend_bfill (ρ : V k → Tree n) (q : Bool) :
    normalized c (extend c X Y w ρ) (bfill w q) = Tree.bot := by
  simp only [normalized, extend, sign_bfill, base_bfill_val]
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]
  cases q <;> simp

/-- A lower link holds when the next position follows the trace and the fillers are `⊥`. -/
theorem node_le_of_descend {ρ : V (2 * (k + (2 * w.length + 2))) → Tree n}
    {a : Fin n → V (2 * (k + (2 * w.length + 2)))}
    {t : Tree n} {i : Fin n} (ht : t ≠ Tree.bot) (hi : ρ (a i) = descend t i)
    (ho : ∀ i', i' ≠ i → ρ (a i') = Tree.bot) : Tree.node (ρ ∘ a) ≤ t := by
  rcases t.eq_bot_or_eq_top_or_node with rfl | rfl | ⟨b, rfl⟩
  · exact absurd rfl ht
  · exact Tree.le_top _
  · rw [Tree.node_le_node_iff]
    intro i'
    by_cases h : i' = i
    · subst h; simp [hi]
    · simp [ho i' h]

/-- A top-prefix witness extends to a solution of the variance extension. -/
theorem extend_sat {ρ : V k → Tree n} (hρ : Sat c ρ ϕ) (hx : covPrefTop w (normalized c ρ X))
    (hy : ¬ covPrefTop w (normalized c ρ Y)) :
    Sat c (extend c X Y w ρ) (Spine.varianceExtension c ϕ X Y w) := by
  have hroot (s : Bool) : trace (normalized c ρ (lroot X Y s)) w ≠ Tree.bot := by
    cases s
    · rw [lroot, show trace _ w = Tree.top from hx]; exact Tree.top_ne_bot
    · rw [lroot, normalized_flipV]
      exact fun h => hy ((covPrefBot_dual w _).mp h)
  have hcut (s : Bool) (j : ℕ) : trace (normalized c ρ (lroot X Y s)) (w.take j) ≠ Tree.bot := by
    intro h
    apply hroot s
    rw [← List.take_append_drop j w, trace_append, h, trace_bot]
  have hhalf (l) (hl : LowerHalf c X Y w l) :
      Covariant.holds (normalized c (extend c X Y w ρ)) l := by
    rcases hl with ⟨s, j, hj, rfl⟩ | rfl | rfl | ⟨q, rfl⟩
    · change Tree.node (_ ∘ _) ≤ _
      rw [extend_lv ρ s hj.le]
      refine node_le_of_descend (i := w[j]) (hcut s j) ?_ fun i' hi' => ?_
      · rw [kids_self, extend_lv ρ s (by omega), List.take_succ_eq_append_getElem hj,
          trace_append, trace_cons, trace_nil]
      · rw [kids_of_ne hi', extend_bfill]
    · change normalized c (extend c X Y w ρ) _ = Tree.top
      rw [extend_lv ρ false le_rfl, List.take_length]
      exact hx
    · change Tree.node (_ ∘ _) ≤ _
      rw [extend_lv ρ true le_rfl, List.take_length]
      have he : normalized c (extend c X Y w ρ) ∘ endKids c X Y w = fun _ => Tree.bot :=
        funext fun _ => extend_bfill ρ _
      rw [he]
      exact (node_bot_le_iff _).mpr (hroot true)
    · exact extend_bfill ρ q
  rw [sat_iff_signed]
  intro l hl
  rcases mem_extension.mp hl with h | h | h
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
    rw [Lit.holds_rename, show normalized c (extend c X Y w ρ) ∘ lift = normalized c ρ from
      funext (extend_lift ρ)]
    exact (sat_iff_signed c ρ ϕ).mp hρ _ hl'
  · exact hhalf l h
  · exact (holds_dualFlip_normalized c _ l).mp (hhalf _ h)

/-- A top-prefix witness exists exactly when the four-spine extension has no label
clash: both say that the variance extension is satisfiable, and its variance shape
restricts to a witness. -/
theorem witness_iff_not_labelClash :
    (∃ ρ, Sat c ρ ϕ ∧ covPrefTop w (normalized c ρ X) ∧ ¬ covPrefTop w (normalized c ρ Y)) ↔
      ¬ LabelClash (Spine.extension c ϕ X Y w) := by
  rw [Spine.extension, ← satisfiable_iff_signed_not_labelClash]
  exact ⟨fun ⟨ρ, hρ, hx, hy⟩ => ⟨_, extend_sat hρ hx hy⟩, fun ⟨ρ, hρ⟩ => ⟨_, witness_of_sat hρ⟩⟩

end Solutions

end DeciNSSE.Spine.Closure
