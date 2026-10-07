import DeciNSSE.Semantics.Selector
import DeciNSSE.Transfer.RankedExtension

/-! # The four-spine extension

A top-prefix witness along `w` for signed roots `X` and `Y` asks for a top of
`X` and no top of `Y` on the prefixes of `w`. Four spines impose it together
with its sign dual: a lower spine from `X` ending in top, a lower spine from
`σY` ending in a lower constructor bound, and their sign duals, an upper spine
from `σX` ending in bottom and an upper spine from `Y` ending in an upper
constructor bound. Position `j` of a spine carries the sign of its root shifted
by the polarity of `w[:j]`, and the bottom and top fillers come in both signs.
The extension is therefore closed under sign duality and sign coherent
whenever the system is. Fresh lower positions and bottom fillers are sources,
their sign duals are sinks.

Without a label clash, the least shape of the extension, followed by the
polarity selector, is a sign-fixed solution; restricted to the old variables
it is a witness. Conversely, a sign-fixed witness extends along the traces of
its roots.
-/

namespace DeciNSSE.Spine.Closure

open FiniteVariance Safety

variable {n k : ℕ}

theorem take_succ_of_lt {w : List (Fin n)} {j : ℕ} (hj : j < w.length) :
    w.take (j + 1) = w.take j ++ [w[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl

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

/-- Position `j` of the lower spine `s`, `P_j` (`s = false`) or `W_j` (`s = true`).
Position `0` is the lifted root; position `0 < j ≤ |w|` has the fresh base
`k + boff |w| s + j - 1` and the sign of the root shifted by the polarity of
`w[:j]`. Its sign dual is position `j` of the paired upper spine, `Q_j` or `Y_j`. -/
def lv (s : Bool) (j : ℕ) : V (2 * (k + (2 * w.length + 2))) :=
  if h : 0 < j ∧ j ≤ w.length then
    sv ⟨k + boff w.length s + j - 1, by have := boff_le w.length s; have := h.2; omega⟩
      (Bool.xor (sign (lroot X Y s)) (polarity c (w.take j)))
  else lift (lroot X Y s)

/-- The bottom filler of sign `q`; its sign dual is the top filler of sign `!q`. -/
def bfill (q : Bool) : V (2 * (k + (2 * w.length + 2))) :=
  sv ⟨k + 2 * w.length + q.toNat, by have := Bool.toNat_le q; omega⟩ q

/-- Children of the link at position `j` of the lower spine `s` reading `i`: the
next position at `i`, and the bottom filler of the coherent sign elsewhere. -/
def kids (s : Bool) (j : ℕ) (i i' : Fin n) : V (2 * (k + (2 * w.length + 2))) :=
  if i' = i then lv c X Y w s (j + 1)
  else bfill w (Bool.xor (sign (lv c X Y w s j)) (c i'))

/-- Children of the terminal lower bound of `W_m`: bottom fillers of the coherent signs. -/
def endKids (i' : Fin n) : V (2 * (k + (2 * w.length + 2))) :=
  bfill w (Bool.xor (sign (lv c X Y w true w.length)) (c i'))

/-- The links of the lower spine `s`, one for each letter of `w`. -/
def links (s : Bool) : Constraint n (2 * (k + (2 * w.length + 2))) :=
  w.mapIdx fun j i => .fLe (kids c X Y w s j i) (lv c X Y w s j)

/-- The lower half of the spines: the links of both lower spines, `P_m = ⊤`,
`f(B, …, B) ≤ W_m`, and the two bottom fillers. -/
def lowerHalf : Constraint n (2 * (k + (2 * w.length + 2))) :=
  links c X Y w false ++ links c X Y w true ++
    [.eqTop (lv c X Y w false w.length), .fLe (endKids c X Y w) (lv c X Y w true w.length),
      .eqBot (bfill w false), .eqBot (bfill w true)]

end Layout

/-- The four-spine extension of `ψ` along `w` for the roots `X` and `Y`: the
lifted system, the lower half of the spines, and its sign dual. -/
def _root_.DeciNSSE.Spine.extension (c : Fin n → Bool) (ψ : Constraint n (2 * k))
    (X Y : V (2 * k)) (w : List (Fin n)) : Constraint n (2 * (k + (2 * w.length + 2))) :=
  ψ.map (Lit.rename lift) ++ (lowerHalf c X Y w ++ (lowerHalf c X Y w).map dualFlip)

section Positions

variable {c : Fin n → Bool} {X Y : V (2 * k)} {w : List (Fin n)}

@[simp] theorem kids_self (s : Bool) (j : ℕ) (i : Fin n) :
    kids c X Y w s j i i = lv c X Y w s (j + 1) := by simp [kids]

theorem kids_of_ne {s : Bool} {j : ℕ} {i i' : Fin n} (h : i' ≠ i) :
    kids c X Y w s j i i' = bfill w (Bool.xor (sign (lv c X Y w s j)) (c i')) := by
  simp [kids, h]

@[simp] theorem lv_zero (s : Bool) : lv c X Y w s 0 = lift (lroot X Y s) := by simp [lv]

theorem base_lv_val {s : Bool} {j : ℕ} (h : 0 < j ∧ j ≤ w.length) :
    (base (lv c X Y w s j)).val = k + boff w.length s + j - 1 := by
  simp [lv, h]

theorem sign_lv {s : Bool} {j : ℕ} (hj : j ≤ w.length) :
    sign (lv c X Y w s j) = Bool.xor (sign (lroot X Y s)) (polarity c (w.take j)) := by
  by_cases h : 0 < j
  · simp [lv, h, hj]
  · obtain rfl : j = 0 := by omega
    simp

@[simp] theorem base_bfill_val (q : Bool) :
    (base (bfill (k := k) w q)).val = k + 2 * w.length + q.toNat := by simp [bfill]

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

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

theorem mem_links {s : Bool} {l : Lit n (2 * (k + (2 * w.length + 2)))} :
    l ∈ links c X Y w s ↔
      ∃ j, ∃ hj : j < w.length, l = .fLe (kids c X Y w s j w[j]) (lv c X Y w s j) := by
  simp only [links, List.mem_mapIdx]
  exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩⟩

theorem mem_lowerHalf {l : Lit n (2 * (k + (2 * w.length + 2)))} :
    l ∈ lowerHalf c X Y w ↔
      (∃ s j, ∃ hj : j < w.length, l = .fLe (kids c X Y w s j w[j]) (lv c X Y w s j)) ∨
        l = .eqTop (lv c X Y w false w.length) ∨
        l = .fLe (endKids c X Y w) (lv c X Y w true w.length) ∨ ∃ q, l = .eqBot (bfill w q) := by
  simp only [lowerHalf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_links,
    Bool.exists_bool, or_assoc]

theorem mem_extension {l : Lit n (2 * (k + (2 * w.length + 2)))} :
    l ∈ Spine.extension c ψ X Y w ↔
      l ∈ ψ.map (Lit.rename lift) ∨ l ∈ lowerHalf c X Y w ∨ dualFlip l ∈ lowerHalf c X Y w := by
  simp only [Spine.extension, List.mem_append, List.mem_map]
  refine or_congr_right (or_congr_right ⟨fun ⟨l', h, he⟩ => by rwa [← he, dualFlip_dualFlip],
    fun h => ⟨_, h, dualFlip_dualFlip l⟩⟩)

theorem lift_mem {l : Lit n (2 * k)} (hl : l ∈ ψ) :
    l.rename lift ∈ Spine.extension c ψ X Y w :=
  mem_extension.mpr (Or.inl (List.mem_map_of_mem hl))

theorem half_mem {l : Lit n (2 * (k + (2 * w.length + 2)))} (hl : l ∈ lowerHalf c X Y w) :
    l ∈ Spine.extension c ψ X Y w := mem_extension.mpr (Or.inr (Or.inl hl))

theorem flip_half_mem {l : Lit n (2 * (k + (2 * w.length + 2)))} (hl : l ∈ lowerHalf c X Y w) :
    dualFlip l ∈ Spine.extension c ψ X Y w :=
  mem_extension.mpr (Or.inr (Or.inr (by rwa [dualFlip_dualFlip])))

theorem link_mem (s : Bool) {j : ℕ} (hj : j < w.length) :
    Lit.fLe (kids c X Y w s j w[j]) (lv c X Y w s j) ∈ Spine.extension c ψ X Y w :=
  half_mem (mem_lowerHalf.mpr (Or.inl ⟨s, j, hj, rfl⟩))

theorem flip_link_mem (s : Bool) {j : ℕ} (hj : j < w.length) :
    Lit.leF (flipV (lv c X Y w s j)) (flipV ∘ kids c X Y w s j w[j]) ∈
      Spine.extension c ψ X Y w :=
  flip_half_mem (mem_lowerHalf.mpr (Or.inl ⟨s, j, hj, rfl⟩))

theorem top_mem : Lit.eqTop (lv c X Y w false w.length) ∈ Spine.extension c ψ X Y w :=
  half_mem (mem_lowerHalf.mpr (Or.inr (Or.inl rfl)))

theorem bot_mem : Lit.eqBot (flipV (lv c X Y w false w.length)) ∈ Spine.extension c ψ X Y w :=
  flip_half_mem (l := .eqTop _) (mem_lowerHalf.mpr (Or.inr (Or.inl rfl)))

theorem end_mem : Lit.fLe (endKids c X Y w) (lv c X Y w true w.length) ∈ Spine.extension c ψ X Y w :=
  half_mem (mem_lowerHalf.mpr (Or.inr (Or.inr (Or.inl rfl))))

theorem flip_end_mem :
    Lit.leF (flipV (lv c X Y w true w.length)) (flipV ∘ endKids c X Y w) ∈
      Spine.extension c ψ X Y w :=
  flip_half_mem (l := .fLe _ _) (mem_lowerHalf.mpr (Or.inr (Or.inr (Or.inl rfl))))

theorem bfill_mem (q : Bool) : Lit.eqBot (bfill w q) ∈ Spine.extension c ψ X Y w :=
  half_mem (mem_lowerHalf.mpr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩))))

/-- Lower constructor literals: lifted, a link of a lower spine, or the terminal bound of `W_m`. -/
theorem mem_fLe {a : Fin n → V (2 * (k + (2 * w.length + 2)))} {u : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.fLe a u ∈ Spine.extension c ψ X Y w) :
    (∃ a' u', Lit.fLe a' u' ∈ ψ ∧ a = lift ∘ a' ∧ u = lift u') ∨
      (∃ s j, ∃ hj : j < w.length, a = kids c X Y w s j w[j] ∧ u = lv c X Y w s j) ∨
      (a = endKids c X Y w ∧ u = lv c X Y w true w.length) := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (fLe_mem_rename h)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.fLe.injEq, reduceCtorEq] at he
    · exact Or.inr (Or.inl ⟨s, j, hj, he⟩)
    · exact Or.inr (Or.inr he)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp [dualFlip] at he

theorem eq_flipV_of_flipV_eq {K : ℕ} {z z' : V (2 * K)} (h : flipV z = z') : z = flipV z' := by
  rw [← h, flipV_flipV]

/-- Upper constructor literals: lifted, or the sign dual of a lower spine literal. -/
theorem mem_leF {v : V (2 * (k + (2 * w.length + 2)))} {b : Fin n → V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.leF v b ∈ Spine.extension c ψ X Y w) :
    (∃ v' b', Lit.leF v' b' ∈ ψ ∧ v = lift v' ∧ b = lift ∘ b') ∨
      (∃ s j, ∃ hj : j < w.length,
        b = flipV ∘ kids c X Y w s j w[j] ∧ v = flipV (lv c X Y w s j)) ∨
      (b = flipV ∘ endKids c X Y w ∧ v = flipV (lv c X Y w true w.length)) := by
  have hb {a : Fin n → V (2 * (k + (2 * w.length + 2)))} (h : flipV ∘ b = a) : b = flipV ∘ a := by
    rw [← h]; funext i; simp
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (leF_mem_rename h)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp at he
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.fLe.injEq, reduceCtorEq] at he
    · exact Or.inr (Or.inl ⟨s, j, hj, hb he.1, eq_flipV_of_flipV_eq he.2⟩)
    · exact Or.inr (Or.inr ⟨hb he.1, eq_flipV_of_flipV_eq he.2⟩)

theorem mem_eqTop {u : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.eqTop u ∈ Spine.extension c ψ X Y w) :
    (∃ u', Lit.eqTop u' ∈ ψ ∧ u = lift u') ∨ u = lv c X Y w false w.length ∨
      ∃ q, u = flipV (bfill w q) := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (eqTop_mem_rename h)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.eqTop.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inl he)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.eqBot.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inr ⟨q, eq_flipV_of_flipV_eq he⟩)

theorem mem_eqBot {v : V (2 * (k + (2 * w.length + 2)))}
    (h : Lit.eqBot v ∈ Spine.extension c ψ X Y w) :
    (∃ v', Lit.eqBot v' ∈ ψ ∧ v = lift v') ∨ v = flipV (lv c X Y w false w.length) ∨
      ∃ q, v = bfill w q := by
  rcases mem_extension.mp h with h | h | h
  · exact Or.inl (eqBot_mem_rename h)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [Lit.eqBot.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inr ⟨q, he⟩)
  · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;>
      simp only [dualFlip, Lit.eqTop.injEq, reduceCtorEq] at he
    exact Or.inr (Or.inl (eq_flipV_of_flipV_eq he))

end Literals

section Symmetry

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

theorem dualFlip_rename_lift (l : Lit n (2 * k)) :
    dualFlip (l.rename (lift (M := 2 * w.length + 2))) = (dualFlip l).rename lift := by
  cases l <;> simp [dualFlip, Lit.rename, Function.comp_def]

/-- The extension is closed under sign duality. -/
theorem extension_flipClosed (hψ : FlipClosed ψ) : FlipClosed (Spine.extension c ψ X Y w) := by
  intro l hl
  rcases mem_extension.mp hl with h | h | h
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
    rw [dualFlip_rename_lift]; exact lift_mem (hψ l' hl')
  · exact flip_half_mem h
  · exact half_mem h

/-- Children of a lower spine literal carry the sign of the root shifted by their variance. -/
theorem lowerHalf_coherent {a : Fin n → V (2 * (k + (2 * w.length + 2)))}
    {u : V (2 * (k + (2 * w.length + 2)))} (h : Lit.fLe a u ∈ lowerHalf c X Y w) (i : Fin n) :
    sign (a i) = Bool.xor (sign u) (c i) := by
  rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩
  · simp only [Lit.fLe.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    by_cases hi : i = w[j]
    · rw [hi, kids_self, sign_lv (by omega), sign_lv hj.le, take_succ_of_lt hj,
        polarity_append_singleton, Bool.xor_assoc]
    · simp [kids_of_ne hi]
  · simp at he
  · simp only [Lit.fLe.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp [endKids]
  · simp at he

theorem xor_not_left (a b : Bool) : Bool.xor (!a) b = !(Bool.xor a b) := by
  cases a <;> cases b <;> rfl

/-- The extension is sign coherent. -/
theorem extension_signCoherent (hψ : SignCoherent c ψ) :
    SignCoherent c (Spine.extension c ψ X Y w) := by
  constructor
  · intro v b h i
    rcases mem_leF h with ⟨v', b', hl, rfl, rfl⟩ | ⟨s, j, hj, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using hψ.1 v' b' hl i
    · simp only [Function.comp_apply, sign_flipV, xor_not_left]
      rw [lowerHalf_coherent (mem_lowerHalf.mpr (Or.inl ⟨s, j, hj, rfl⟩))]
    · simp only [Function.comp_apply, sign_flipV, xor_not_left]
      rw [lowerHalf_coherent (mem_lowerHalf.mpr (Or.inr (Or.inr (Or.inl rfl))))]
  · intro a u h i
    rcases mem_extension.mp h with h | h | h
    · obtain ⟨a', u', hl', rfl, rfl⟩ := fLe_mem_rename h
      simpa using hψ.2 a' u' hl' i
    · exact lowerHalf_coherent h i
    · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp [dualFlip] at he

end Symmetry

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
    {u : V (2 * (k + (2 * w.length + 2)))} (h : Lit.fLe a u ∈ lowerHalf c X Y w) :
    (∀ i, Source c X Y w (a i) ∧ (base u).val < (base (a i)).val) ∧
      ¬ Source c X Y w (flipV u) := by
  rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩
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
/-- The extension is a ranked source and sink extension of `ψ`, ranked by base index. -/
theorem extension_ranked (ψ : Constraint n (2 * k)) :
    Ranked.Extension lift ψ (Spine.extension c ψ X Y w) (Source c X Y w) (Sink c X Y w)
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
    · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp [dualFlip] at he
  upper := by
    intro v b h
    rcases mem_extension.mp h with h | h | h
    · exact Or.inl (leF_mem_rename h)
    · rcases mem_lowerHalf.mp h with ⟨s, j, hj, he⟩ | he | he | ⟨q, he⟩ <;> simp at he
    · obtain ⟨hk, hn⟩ := lowerHalf_fresh h
      refine Or.inr ⟨fun i => ?_, by simpa using hn⟩
      obtain ⟨hs, hr⟩ := hk i
      exact ⟨by simpa [Sink] using hs, by simpa using hr⟩

variable {ψ : Constraint n (2 * k)}

/-- A derivation into a source is an identity. -/
theorem derives_into_source {a b : V (2 * (k + (2 * w.length + 2)))}
    (h : Derives (Spine.extension c ψ X Y w) a b) (hb : Source c X Y w b) : a = b :=
  (extension_ranked c X Y w ψ).derives_into_source h hb

/-- A derivation out of a sink is an identity. -/
theorem derives_out_of_sink {a b : V (2 * (k + (2 * w.length + 2)))}
    (h : Derives (Spine.extension c ψ X Y w) a b) (ha : Sink c X Y w a) : b = a :=
  (extension_ranked c X Y w ψ).derives_out_of_sink h ha

theorem derives_lift {u v : V (2 * k)} (h : Derives ψ u v) :
    Derives (Spine.extension c ψ X Y w) (lift u) (lift v) :=
  ((extension_ranked c X Y w ψ).derives_original u v).mpr h

end Ranked

section Solutions

variable {c : Fin n → Bool} {ψ : Constraint n (2 * k)} {X Y : V (2 * k)} {w : List (Fin n)}

/-- Along a lower spine, a solution stays below the trace of the spine root. -/
theorem lv_le_trace {M : V (2 * (k + (2 * w.length + 2))) → Tree n}
    (hM : Covariant.Sat M (Spine.extension c ψ X Y w)) (s : Bool) :
    ∀ j ≤ w.length, M (lv c X Y w s j) ≤ trace (M (lv c X Y w s 0)) (w.take j)
  | 0, _ => by simp
  | j + 1, hj => by
    have hd := descend_mono (hM _ (link_mem (ψ := ψ) s (by omega : j < w.length))) w[j]
    simp only [descend_node, Function.comp_apply, kids_self] at hd
    rw [take_succ_of_lt (by omega), trace_append, trace_cons, trace_nil]
    exact le_trans hd (descend_mono (lv_le_trace hM s j (by omega)) _)

/-- A sign-fixed solution of the extension restricts to a sign-fixed top-prefix witness. -/
theorem witness_of_sat {M : V (2 * (k + (2 * w.length + 2))) → Tree n}
    (hM : Covariant.Sat M (Spine.extension c ψ X Y w)) (hfix : Signed.dual M = M) :
    Covariant.Sat (M ∘ lift) ψ ∧ Signed.dual (M ∘ lift) = M ∘ lift ∧
      covPrefTop w (M (lift X)) ∧ ¬ covPrefTop w (M (lift Y)) := by
  refine ⟨(sat_rename lift M ψ).mp fun l hl => hM _ (mem_extension.mpr (Or.inl hl)), ?_, ?_, ?_⟩
  · funext z
    rw [signedDual_eq_flipV, Function.comp_apply, Function.comp_apply, ← flipV_lift,
      ← signedDual_eq_flipV, hfix]
  · have h := lv_le_trace hM false w.length le_rfl
    rw [List.take_length, lv_zero, (hM _ top_mem : M _ = Tree.top)] at h
    exact (trace_eq_top_iff _ _).mp ((Tree.top_le_iff _).mp h)
  · intro hy
    have h := lv_le_trace hM true w.length le_rfl
    rw [List.take_length, lv_zero] at h
    have hend : Tree.node (M ∘ endKids c X Y w) ≤ M (lv c X Y w true w.length) := hM _ end_mem
    have hb (i : Fin n) : (M ∘ endKids c X Y w) i = Tree.bot := hM _ (bfill_mem _)
    rw [show (M ∘ endKids c X Y w) = fun _ => Tree.bot from funext hb] at hend
    have hne := (node_bot_le_iff _).mp (le_trans hend h)
    simp only [lroot, ← flipV_lift, fixed_flipV hfix] at hne
    exact hne ((trace_eq_bot_iff _ _).mpr ((covPrefBot_dual w _).mpr hy))

variable (c X Y w) in
/-- The base values of the canonical extension of `A`: an old base reads the
positive sign; a fresh spine base reads the trace of the lower root, oriented by
the sign of the lower position; the filler bases read bottom and top. -/
def extendBase (A : V (2 * k) → Tree n) (b : V (k + (2 * w.length + 2))) : Tree n :=
  if hb : b.val < k then A (sv ⟨b.val, hb⟩ false)
  else if b.val < k + 2 * w.length then
    Tree.normalize (fun _ => false)
      (sign (lv c X Y w (decide (k + w.length ≤ b.val))
        (b.val - k - boff w.length (decide (k + w.length ≤ b.val)) + 1)))
      (trace (A (lroot X Y (decide (k + w.length ≤ b.val))))
        (w.take (b.val - k - boff w.length (decide (k + w.length ≤ b.val)) + 1)))
  else if b.val = k + 2 * w.length then Tree.bot else Tree.top

variable (c X Y w) in
/-- The canonical sign-fixed extension of `A`: spine positions follow the traces
of their roots along `w`, bottom fillers are `⊥` and top fillers `⊤`. -/
def extend (A : V (2 * k) → Tree n) : V (2 * (k + (2 * w.length + 2))) → Tree n :=
  normalized (fun _ => false) (extendBase c X Y w A)

theorem extend_fixed (A : V (2 * k) → Tree n) :
    Signed.dual (extend c X Y w A) = extend c X Y w A := normalized_fixed _ _

theorem normalize_sign_of_fixed {A : V (2 * k) → Tree n} (hfix : Signed.dual A = A)
    (z : V (2 * k)) : Tree.normalize (fun _ => false) (sign z) (A (sv (base z) false)) = A z := by
  conv_rhs => rw [← sv_base_sign z]
  cases sign z
  · simp
  · change Tree.dual _ = _
    rw [← fixed_flipV hfix, flipV_sv, Bool.not_false]

theorem extend_lift {A : V (2 * k) → Tree n} (hfix : Signed.dual A = A) (z : V (2 * k)) :
    extend c X Y w A (lift z) = A z := by
  simp only [extend, normalized, extendBase, base_lift, sign_lift, Fin.val_castAdd, (base z).isLt,
    dite_true]
  exact normalize_sign_of_fixed hfix z

theorem extend_lv {A : V (2 * k) → Tree n} (hfix : Signed.dual A = A) (s : Bool) {j : ℕ}
    (hj : j ≤ w.length) : extend c X Y w A (lv c X Y w s j) = trace (A (lroot X Y s)) (w.take j) := by
  by_cases h0 : 0 < j
  · have hv := base_lv_val (c := c) (X := X) (Y := Y) (s := s) ⟨h0, hj⟩
    have hm := boff_le w.length s
    have hs : decide (k + w.length ≤ k + boff w.length s + j - 1) = s := by
      cases s
      · exact decide_eq_false (by simp only [boff]; omega)
      · exact decide_eq_true (by simp only [boff]; omega)
    have hj' : k + boff w.length s + j - 1 - k - boff w.length s + 1 = j := by omega
    simp only [extend, normalized, extendBase, hv, hs, hj']
    rw [dite_eq_right (by omega), ite_eq_left (by omega), normalize_involutive]
  · obtain rfl : j = 0 := by omega
    rw [lv_zero, extend_lift hfix]; rfl

theorem extend_bfill (A : V (2 * k) → Tree n) (q : Bool) :
    extend c X Y w A (bfill w q) = Tree.bot := by
  simp only [extend, normalized, extendBase, sign_bfill, base_bfill_val]
  rw [dite_eq_right (by omega), ite_eq_right (by omega)]
  cases q
  · rw [Bool.toNat_false, ite_eq_left (by omega)]; exact normalize_false_variance _
  · rw [Bool.toNat_true, ite_eq_right (by omega), normalize_top]; rfl

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

/-- A sign-fixed witness extends to a solution of the four-spine extension. -/
theorem extend_sat {A : V (2 * k) → Tree n} (hA : Covariant.Sat A ψ) (hfix : Signed.dual A = A)
    (hx : covPrefTop w (A X)) (hy : ¬ covPrefTop w (A Y)) :
    Covariant.Sat (extend c X Y w A) (Spine.extension c ψ X Y w) := by
  have hroot (s : Bool) : trace (A (lroot X Y s)) w ≠ Tree.bot := by
    cases s
    · rw [lroot, (trace_eq_top_iff _ _).mpr hx]; exact Tree.top_ne_bot
    · rw [lroot, fixed_flipV hfix, Ne, trace_eq_bot_iff]
      exact fun h => hy ((covPrefBot_dual w _).mp h)
  have hcut (s : Bool) (j : ℕ) : trace (A (lroot X Y s)) (w.take j) ≠ Tree.bot := by
    intro h
    apply hroot s
    rw [← List.take_append_drop j w, trace_append, h, trace_bot]
  have hhalf : ∀ l ∈ lowerHalf c X Y w, Covariant.holds (extend c X Y w A) l := by
    intro l hl
    rcases mem_lowerHalf.mp hl with ⟨s, j, hj, rfl⟩ | rfl | rfl | ⟨q, rfl⟩
    · change Tree.node (_ ∘ _) ≤ _
      rw [extend_lv hfix s hj.le]
      refine node_le_of_descend (i := w[j]) (hcut s j) ?_ fun i' hi' => ?_
      · rw [kids_self, extend_lv hfix s (by omega), take_succ_of_lt hj, trace_append, trace_cons,
          trace_nil]
      · rw [kids_of_ne hi', extend_bfill]
    · change extend c X Y w A _ = Tree.top
      rw [extend_lv hfix false le_rfl, List.take_length]
      exact (trace_eq_top_iff _ _).mpr hx
    · change Tree.node (_ ∘ _) ≤ _
      rw [extend_lv hfix true le_rfl, List.take_length]
      have he : extend c X Y w A ∘ endKids c X Y w = fun _ => Tree.bot :=
        funext fun _ => extend_bfill A _
      rw [he]
      exact (node_bot_le_iff _).mpr (hroot true)
    · exact extend_bfill A q
  intro l hl
  rcases mem_extension.mp hl with h | h | h
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp h
    rw [Lit.holds_rename, show extend c X Y w A ∘ lift = A from funext (extend_lift hfix)]
    exact hA _ hl'
  · exact hhalf l h
  · rw [← extend_fixed A, holds_signedDual]
    exact hhalf _ h

/-- A sign-fixed top-prefix witness exists exactly when the four-spine extension
has no label clash. The least shape of the extension, made sign-fixed by the
polarity selector, restricts to the witness. -/
theorem fixedWitness_iff_not_labelClash (hf : FlipClosed ψ) (hc : SignCoherent c ψ) :
    (∃ A, Covariant.Sat A ψ ∧ Signed.dual A = A ∧ covPrefTop w (A X) ∧ ¬ covPrefTop w (A Y)) ↔
      ¬ LabelClash (Spine.extension c ψ X Y w) := by
  constructor
  · rintro ⟨A, hA, hfix, hx, hy⟩ hl
    exact hl.unsatisfiable ⟨_, extend_sat hA hfix hx hy⟩
  · intro hl
    have hf' : FlipClosed (Spine.extension c ψ X Y w) := extension_flipClosed hf
    have hB := leastShape_sat hl
    have hM := select_sat_of_coherent (extension_signCoherent hc) hB
      (sat_signedDual_of_flipClosed hf' hB) (leastShape_sameShape_dual hf')
    exact ⟨_, witness_of_sat hM (select_fixed _ _ _)⟩

end Solutions

end DeciNSSE.Spine.Closure
