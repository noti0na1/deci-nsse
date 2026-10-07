import DeciNSSE.Semantics.Tree

/-! # Normalisation of variance

Path polarity is the XOR of the variances encountered from the root. A true
bit reverses comparison by exchanging bottom and top; constructor labels and
domains stay fixed. Normalisation therefore turns variance order into covariance.
-/

namespace DeciNSSE

variable {n : ℕ}

/-- The parity of contravariant positions along a path. -/
def polarity (c : Fin n → Bool) : List (Fin n) → Bool
  | [] => false
  | i :: π => Bool.xor (c i) (polarity c π)

@[simp] theorem polarity_nil (c : Fin n → Bool) : polarity c [] = false := rfl
@[simp] theorem polarity_cons (c : Fin n → Bool) (i : Fin n) (π : List (Fin n)) :
    polarity c (i :: π) = Bool.xor (c i) (polarity c π) := rfl
@[simp] theorem polarity_false (π : List (Fin n)) : polarity (fun _ => false) π = false := by
  induction π with
  | nil => rfl
  | cons i π ih => simp [polarity, ih]

end DeciNSSE

namespace DeciNSSE.Sym

/-- Compare two labels in the direction selected by the polarity bit. -/
def leP (p : Bool) (a b : Sym) : Prop := if p then b ≤ a else a ≤ b

/-- Exchange bottom and top when the polarity bit is true. -/
def flip : Bool → Sym → Sym
  | false, a => a
  | true, bot => top
  | true, f => f
  | true, top => bot

@[simp] theorem flip_false (a : Sym) : flip false a = a := rfl
@[simp] theorem flip_f (p : Bool) : flip p f = f := by cases p <;> rfl
@[simp] theorem flip_involutive (p : Bool) (a : Sym) : flip p (flip p a) = a := by
  cases p <;> cases a <;> rfl
@[simp] theorem flip_eq_f (p : Bool) (a : Sym) : flip p a = f ↔ a = f := by
  cases p <;> cases a <;> decide

theorem leP_iff_flip (p : Bool) (a b : Sym) :
    leP p a b ↔ flip p a ≤ flip p b := by
  cases p <;> cases a <;> cases b <;> simp [leP, flip]

end DeciNSSE.Sym

namespace DeciNSSE

variable {n : ℕ}

/-- Change only leaf labels, using the polarity at each present path. -/
def Tree.normalize (c : Fin n → Bool) (p : Bool) (t : Tree n) : Tree n where
  fn π := (t.fn π).map (Sym.flip (Bool.xor p (polarity c π)))
  wf := by
    constructor
    · simpa using t.wf.1
    · intro π i
      simpa only [Option.isSome_map, Option.map_eq_some_iff, Sym.flip_eq_f,
        exists_eq_right] using t.wf.2 π i

@[simp] theorem normalize_fn (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = (t.fn π).map (Sym.flip (Bool.xor p (polarity c π))) := rfl

@[simp] theorem normalize_domain (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    ((Tree.normalize c p t).fn π).isSome = (t.fn π).isSome := by simp

@[simp] theorem normalize_constructor (c : Fin n → Bool) (p : Bool) (t : Tree n) (π : List (Fin n)) :
    (Tree.normalize c p t).fn π = some Sym.f ↔ t.fn π = some Sym.f := by
  simp only [normalize_fn, Option.map_eq_some_iff, Sym.flip_eq_f, exists_eq_right]

@[simp] theorem normalize_involutive (c : Fin n → Bool) (p : Bool) (t : Tree n) :
    Tree.normalize c p (Tree.normalize c p t) = t := by
  apply Tree.ext; funext π
  cases h : t.fn π <;> simp [h]

theorem normalize_injective (c : Fin n → Bool) (p : Bool) : Function.Injective (Tree.normalize c p) :=
  Function.LeftInverse.injective (normalize_involutive c p)

@[simp] theorem normalize_bot (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.bot = if p then Tree.top else Tree.bot := by
  apply Tree.ext; funext π
  cases p <;> cases π <;> simp [Sym.flip]

@[simp] theorem normalize_top (c : Fin n → Bool) (p : Bool) :
    Tree.normalize c p Tree.top = if p then Tree.bot else Tree.top := by
  apply Tree.ext; funext π
  cases p <;> cases π <;> simp [Sym.flip]

@[simp] theorem normalize_node (c : Fin n → Bool) (p : Bool) (a : Fin n → Tree n) :
    Tree.normalize c p (Tree.node a) = Tree.node (fun i => Tree.normalize c (Bool.xor p (c i)) (a i)) := by
  apply Tree.ext; funext w
  cases w with
  | nil => simp
  | cons i w => simp

@[simp] theorem normalize_false_variance (t : Tree n) : Tree.normalize (fun _ => false) false t = t := by
  apply Tree.ext; funext π; cases h : t.fn π <;> simp [h]

/-- Swap bottom and top everywhere in the actual domain. -/
def Tree.dual : Tree n → Tree n := Tree.normalize (fun _ => false) true

@[simp] theorem dual_fn (t : Tree n) (π : List (Fin n)) :
    (Tree.dual t).fn π = (t.fn π).map (Sym.flip true) := by simp [Tree.dual]

@[simp] theorem dual_involutive (t : Tree n) : Tree.dual (Tree.dual t) = t := normalize_involutive _ _ _
@[simp] theorem dual_bot : Tree.dual (Tree.bot : Tree n) = Tree.top := by simp [Tree.dual]
@[simp] theorem dual_top : Tree.dual (Tree.top : Tree n) = Tree.bot := by simp [Tree.dual]
@[simp] theorem dual_node (a : Fin n → Tree n) :
    Tree.dual (Tree.node a) = Tree.node (fun i => Tree.dual (a i)) := by simp [Tree.dual]

@[simp] theorem normalize_true (c : Fin n → Bool) (t : Tree n) : Tree.normalize c true t = Tree.dual (Tree.normalize c false t) := by
  apply Tree.ext; funext π
  cases h : t.fn π with
  | none => simp [h]
  | some a => cases hp : polarity c π <;> simp [h, hp]

@[simp] theorem dual_le_iff (t u : Tree n) : Tree.dual t ≤ Tree.dual u ↔ u ≤ t := by
  constructor
  · intro h π a b ha hb
    have hh := h π (Sym.flip true b) (Sym.flip true a)
      (by simp [hb]) (by simp [ha])
    exact (Sym.leP_iff_flip true b a).mpr hh
  · intro h π a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
    simpa using (Sym.leP_iff_flip true a' b').mp (h π b' a' hb' ha')

end DeciNSSE
