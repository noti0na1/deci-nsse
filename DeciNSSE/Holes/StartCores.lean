import DeciNSSE.Holes.Hierarchy

/-! # Start cores and runs of markers

Run-length decompositions describe marker blocks and their suffix comparisons.
The number of start-core positions increases by at most one per level,
which bounds the length of levels with empty ordinary support.
-/

namespace DeciNSSE.StartCores
open DeciNSSE.Holes

section RunWords
variable {α : Type*}

def rep (μ : α) (n : ℕ) : List α := List.replicate n μ

def Good (μ : α) (l : List (α × ℕ)) : Prop := ∀ p ∈ l, p.1 ≠ μ

theorem Good.tail {μ : α} {p : α × ℕ} {l : List (α × ℕ)} (h : Good μ (p :: l)) : Good μ l :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

theorem Good.head {μ : α} {p : α × ℕ} {l : List (α × ℕ)} (h : Good μ (p :: l)) : p.1 ≠ μ :=
  h p (List.mem_cons_self ..)

variable (μ : α)

def tl : List (α × ℕ) → List α
  | [] => []
  | p :: l => p.1 :: (rep μ p.2 ++ tl l)

def W (r : ℕ) (l : List (α × ℕ)) : List α := rep μ r ++ tl μ l

@[simp] theorem length_rep (n : ℕ) : (rep μ n).length = n := List.length_replicate

theorem rep_add (m n : ℕ) : rep μ (m + n) = rep μ m ++ rep μ n := List.replicate_add m n μ

@[simp] theorem rep_zero : rep μ 0 = [] := rfl

theorem rep_succ (n : ℕ) : rep μ (n + 1) = μ :: rep μ n := rfl

@[simp] theorem tl_nil : tl μ [] = [] := rfl

@[simp] theorem tl_cons (p : α × ℕ) (l : List (α × ℕ)) :
    tl μ (p :: l) = p.1 :: (rep μ p.2 ++ tl μ l) := rfl

@[simp] theorem W_nil (r : ℕ) : W μ r [] = rep μ r := by simp [W]

theorem W_cons (r : ℕ) (p : α × ℕ) (l : List (α × ℕ)) :
    W μ r (p :: l) = rep μ r ++ p.1 :: W μ p.2 l := rfl

theorem rep_append_W (m n : ℕ) (l : List (α × ℕ)) : rep μ m ++ W μ n l = W μ (m + n) l := by
  simp [W, rep_add]

theorem rep_lt_split {d d' : ℕ} (h : d' < d) :
    rep μ d = rep μ d' ++ μ :: rep μ (d - d' - 1) := by
  rw [← rep_succ, ← rep_add]; congr 1; omega

theorem rep_prefix_iff {d d' : ℕ} {t : List α} (ht : ∀ x ∈ t.head?, x ≠ μ) :
    rep μ d <+: rep μ d' ++ t ↔ d ≤ d' := by
  constructor
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    rw [rep_lt_split μ hlt, List.prefix_append_right_inj] at h
    cases t with
    | nil => exact absurd h.length_le (by simp)
    | cons x t => exact ht x (by simp) (List.cons_prefix_cons.mp h).1.symm
  · intro h
    refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
    rw [show d' = d + (d' - d) by omega, rep_add]
    exact List.prefix_append _ _

theorem rep_cons_prefix_iff {d d' : ℕ} {x x' : α} {s s' : List α} (hx : x ≠ μ) (hx' : x' ≠ μ) :
    rep μ d ++ x :: s <+: rep μ d' ++ x' :: s' ↔ d = d' ∧ x = x' ∧ s <+: s' := by
  rcases lt_trichotomy d d' with h | h | h
  · constructor
    · intro hp
      rw [rep_lt_split μ h, List.append_assoc, List.prefix_append_right_inj] at hp
      simp only [List.cons_append, List.cons_prefix_cons] at hp
      exact absurd hp.1 hx
    · rintro ⟨h', -⟩; omega
  · subst h
    rw [List.prefix_append_right_inj, List.cons_prefix_cons]
    simp
  · constructor
    · intro hp
      rw [rep_lt_split μ h, List.append_assoc, List.prefix_append_right_inj] at hp
      simp only [List.cons_append, List.cons_prefix_cons] at hp
      exact absurd hp.1.symm hx'
    · rintro ⟨h', -⟩; omega

end RunWords

section PrefRL
variable {α : Type*}

def PrefRL : ℕ → List (α × ℕ) → ℕ → List (α × ℕ) → Prop
  | d, [], d', _ => d ≤ d'
  | _, _ :: _, _, [] => False
  | d, p :: l, d', p' :: l' => d = d' ∧ p.1 = p'.1 ∧ PrefRL p.2 l p'.2 l'

@[simp] theorem prefRL_nil (d d' : ℕ) (l' : List (α × ℕ)) : PrefRL d [] d' l' ↔ d ≤ d' := by
  cases l' <;> rfl

@[simp] theorem prefRL_cons_nil (d d' : ℕ) (p : α × ℕ) (l : List (α × ℕ)) :
    PrefRL d (p :: l) d' [] ↔ False := Iff.rfl

@[simp] theorem prefRL_cons_cons (d d' : ℕ) (p p' : α × ℕ) (l l' : List (α × ℕ)) :
    PrefRL d (p :: l) d' (p' :: l') ↔ d = d' ∧ p.1 = p'.1 ∧ PrefRL p.2 l p'.2 l' := Iff.rfl

variable (μ : α)

theorem head_tl_ne {l : List (α × ℕ)} (hl : Good μ l) : ∀ x ∈ (tl μ l).head?, x ≠ μ := by
  cases l with
  | nil => simp
  | cons p l =>
    simp only [tl_cons, List.head?_cons, Option.mem_def, Option.some.injEq]
    rintro x rfl
    exact hl.head

theorem W_prefix_iff : ∀ {l l' : List (α × ℕ)} {d d' : ℕ}, Good μ l → Good μ l' →
    (W μ d l <+: W μ d' l' ↔ PrefRL d l d' l')
  | [], l', d, d', _, hl' => by
      rw [W_nil, prefRL_nil]
      exact rep_prefix_iff μ (head_tl_ne μ hl')
  | p :: l, [], d, d', hl, _ => by
      simp only [prefRL_cons_nil, iff_false, W_cons, W_nil]
      intro h
      have hm := h.subset (by simp : p.1 ∈ rep μ d ++ p.1 :: W μ p.2 l)
      simp only [rep, List.mem_replicate] at hm
      exact hl.head hm.2
  | p :: l, p' :: l', d, d', hl, hl' => by
      rw [W_cons, W_cons, rep_cons_prefix_iff μ hl.head hl'.head,
        W_prefix_iff hl.tail hl'.tail, prefRL_cons_cons]

end PrefRL

section Lift
variable {α : Type*}

def Img (a : ℕ) (r : ℕ × ℕ) (d e : ℕ) : Prop := e = d + (r.1 - r.2) ∨ (e = d ∧ a + d ≤ r.2)

variable (μ : α)

def fstJ (J : List (α × ℕ × ℕ)) : List (α × ℕ) := J.map fun t => (t.1, t.2.1)

def sndJ (J : List (α × ℕ × ℕ)) : List (α × ℕ) := J.map fun t => (t.1, t.2.2)

@[simp] theorem fstJ_nil : fstJ ([] : List (α × ℕ × ℕ)) = [] := rfl
@[simp] theorem sndJ_nil : sndJ ([] : List (α × ℕ × ℕ)) = [] := rfl
@[simp] theorem fstJ_cons (t : α × ℕ × ℕ) (J : List (α × ℕ × ℕ)) :
    fstJ (t :: J) = (t.1, t.2.1) :: fstJ J := rfl
@[simp] theorem sndJ_cons (t : α × ℕ × ℕ) (J : List (α × ℕ × ℕ)) :
    sndJ (t :: J) = (t.1, t.2.2) :: sndJ J := rfl

def GoodJ (J : List (α × ℕ × ℕ)) : Prop := ∀ t ∈ J, t.1 ≠ μ

variable {μ}

theorem GoodJ.tail {t : α × ℕ × ℕ} {J : List (α × ℕ × ℕ)} (h : GoodJ μ (t :: J)) : GoodJ μ J :=
  fun t' ht' => h t' (List.mem_cons_of_mem _ ht')

def SrcOK (a : ℕ) (hs : ℕ × ℕ) (Ts : List (α × ℕ × ℕ)) (ht : ℕ × ℕ) (Tt : List (α × ℕ × ℕ)) :
    Prop :=
  ∀ dt ds, dt ≤ ht.2 → ds ≤ hs.2 → PrefRL dt (sndJ Tt) ds (sndJ Ts) →
    ∃ et es, Img a ht dt et ∧ Img a hs ds es ∧ PrefRL et (fstJ Tt) es (fstJ Ts)

def LiftHyp (a : ℕ) (h : ℕ × ℕ) (J : List (α × ℕ × ℕ)) : Prop :=
  (∀ pre t Tt, J = pre ++ t :: Tt → SrcOK a h J t.2 Tt) ∧
  (∀ pre s Ts pre' t Tt, J = pre ++ s :: Ts → Ts = pre' ++ t :: Tt → SrcOK a s.2 Ts t.2 Tt)

theorem LiftHyp.tail {a : ℕ} {h : ℕ × ℕ} {t : α × ℕ × ℕ} {J : List (α × ℕ × ℕ)}
    (hL : LiftHyp a h (t :: J)) : LiftHyp a t.2 J :=
  ⟨fun pre t' Tt hJ => hL.2 [] t J pre t' Tt rfl hJ,
   fun pre s Ts pre' t' Tt hJ hT => hL.2 (t :: pre) s Ts pre' t' Tt (by simp [hJ]) hT⟩

end Lift

section LemmaU
variable {α : Type*} (μ : α)

def rl [DecidableEq α] : List α → ℕ × List (α × ℕ)
  | [] => (0, [])
  | x :: w => if x = μ then ((rl w).1 + 1, (rl w).2) else (0, (x, (rl w).1) :: (rl w).2)

theorem W_rl [DecidableEq α] : ∀ w : List α, W μ (rl μ w).1 (rl μ w).2 = w ∧ Good μ (rl μ w).2
  | [] => ⟨rfl, by simp [Good, rl]⟩
  | x :: w => by
    obtain ⟨h1, h2⟩ := W_rl w
    by_cases hx : x = μ
    · simp only [rl, hx, ite_true]
      refine ⟨?_, h2⟩
      rw [show (rl μ w).1 + 1 = 1 + (rl μ w).1 by omega, ← rep_append_W μ 1, h1]; rfl
    · simp only [rl, hx, ite_false]
      refine ⟨?_, ?_⟩
      · rw [W_cons, h1]; rfl
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hx
        · exact h2 p hp

def runs [DecidableEq α] (w : List α) : List ℕ := (rl μ w).1 :: (rl μ w).2.map Prod.snd

end LemmaU

section LemmaG
variable {α : Type*}

def Fol (s : ℕ) (γb : List (α × ℕ)) (y : α) (T : List (α × ℕ)) : Prop :=
  ∃ r rest, T = γb ++ (y, r) :: rest ∧ s ≤ r

open Classical in

noncomputable def gRun (s Λ : ℕ) (γb : List (α × ℕ)) (y : α) (r : ℕ) (L : List (α × ℕ)) : ℕ :=
  if Fol s γb y L then r - Λ else r

noncomputable def gJ (s Λ : ℕ) (γb : List (α × ℕ)) (y : α) :
    List (α × ℕ) → List (α × ℕ × ℕ)
  | [] => []
  | p :: L => (p.1, p.2, gRun s Λ γb y p.2 L) :: gJ s Λ γb y L

def GenL (s : ℕ) (γb : List (α × ℕ)) (y : α) (e : ℕ) : List (α × ℕ) → Prop
  | [] => True
  | p :: L => (Fol s γb y L → p.2 = e) ∧ GenL s γb y e L

variable {s Λ e : ℕ} {γb : List (α × ℕ)} {y : α}

@[simp] theorem gJ_nil : gJ s Λ γb y [] = [] := rfl

@[simp] theorem gJ_cons (p : α × ℕ) (L : List (α × ℕ)) :
    gJ s Λ γb y (p :: L) = (p.1, p.2, gRun s Λ γb y p.2 L) :: gJ s Λ γb y L := rfl

theorem GenL.append : ∀ {L₁ L : List (α × ℕ)}, GenL s γb y e (L₁ ++ L) → GenL s γb y e L
  | [], _, h => h
  | _ :: L₁, _, h => GenL.append (L₁ := L₁) h.2

theorem GenL.run {L₁ L : List (α × ℕ)} {p : α × ℕ} (h : GenL s γb y e (L₁ ++ p :: L)) :
    Fol s γb y L → p.2 = e := (GenL.append h).1

end LemmaG

section Codewords
variable {α : Type*}

def pat (s : ℕ) : List (α × ℕ) → List (α × ℕ)
  | [] => []
  | p :: T => if s ≤ p.2 then [(p.1, s)] else p :: pat s T

def sepTails (s : ℕ) : List (α × ℕ) → List (List (α × ℕ))
  | [] => []
  | p :: T => (if s ≤ p.2 then (match T with | [] => [] | _ :: _ => [T]) else []) ++ sepTails s T

def cws (s : ℕ) (l : List (α × ℕ)) : List (List (α × ℕ)) := pat s l :: (sepTails s l).map (pat s)

end Codewords

section StretchLemma
variable {α Q : Type*} [DecidableEq α]

structure SLClass (μ : α) (M : DFA α Q) (R : Q → Q → Prop) (T : Set Q) (B : Finset ℕ)
    (A₀ s₀ : ℕ) (L₀ : List (α × ℕ)) (x : α) (g : ℕ) (A s : ℕ) (L : List (α × ℕ)) : Prop where
  hole : IsReaderHole M R T (W μ A (L ++ [(x, s)]))
  good : Good μ (L ++ [(x, s)])
  letters : L.map Prod.fst = L₀.map Prod.fst
  pos : 1 ≤ s
  fin : s ≤ s₀
  lead : A ≤ A₀
  fresh : A = A₀ ∨ A ∉ B
  card : (cws s (L ++ [(x, s)])).toFinset.card ≤ g

end StretchLemma

section StartCores
universe u v
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]
open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

/-- The number of canonical markers in the initial segment occupied by start cores. -/
def cnt (D0 : Lettered α Q) (w : List α) (j : ℕ) : ℕ :=
  ((hierOf w j).take (sCount D0 w j)).count (markOf w j)

theorem sCount_succ_cnt (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) = min (hierOf w (j + 1)).length (1 + cnt D0 w j) :=
  sCount_succ D0 hw j

theorem cnt_le (D0 : Lettered α Q) (w : List α) (j : ℕ) : cnt D0 w j ≤ sCount D0 w j := by
  have h1 := List.count_le_length (l := (hierOf w j).take (sCount D0 w j)) (a := markOf w j)
  have h2 := List.length_take_le (sCount D0 w j) (hierOf w j)
  unfold cnt; omega

theorem sCount_succ_le (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) (j : ℕ) :
    sCount D0 w (j + 1) ≤ sCount D0 w j + 1 := by
  rw [sCount_succ_cnt D0 hw j]
  have := cnt_le D0 w j
  omega

end StartCores

open DeciNSSE.CoAlignment DeciNSSE.LetteredHierarchy

universe u v

section Descent
variable {α : Type u} {Q : Type v} [DecidableEq α] [Inhabited α]

/-- At level i, at most i positions carry start cores. -/
theorem sCount_le_level (D0 : Lettered α Q) {w : List α} (hw : w ≠ []) :
    ∀ i, sCount D0 w i ≤ i
  | 0 => by rw [sCount_zero]
  | i + 1 => (sCount_succ_le D0 hw i).trans (Nat.succ_le_succ (sCount_le_level D0 hw i))

end Descent

end DeciNSSE.StartCores
