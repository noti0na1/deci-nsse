import DeciNSSE.Holes.Hierarchy.Canonical
import DeciNSSE.Holes.Packets

/-! # Unary levels and pumping

A level of the canonical hierarchy is unary when it is a power of one letter.
The words of `𝓛(d)` have a unary level at most `d`. Some power of a letter `x` is a
hole exactly when some power `x^m` with `1 ≤ m ≤ |C|` is, since the run of a power is
the orbit of the start core under one transition.

## Main declarations

- `IsUnary`, `InL`: unary words, and the words with a unary level at most `d`.
- `core_replicate`, `iterate_small`: runs of powers, and orbits in finite sets.
- `exists_unary_hole_iff`: a unary hole can be chosen with at most `|C|`
  letters.

The declarations are in the namespace `DeciNSSE.LetteredHierarchy`.
-/

namespace DeciNSSE.LetteredHierarchy
open DeciNSSE.CoAlignment
open scoped List

section Bounded
universe u v
variable {α : Type u} {Q : Type v}

/-- A unary word `x^m`. -/
def IsUnary {β : Type*} (u : List β) : Prop := ∀ a ∈ u, ∀ b ∈ u, a = b

variable [DecidableEq α] [Inhabited α]

/-- `w ∈ 𝓛(d)`: some level `i ≤ d` of the canonical hierarchy of `w` is unary. -/
def InL (d : ℕ) (w : List α) : Prop :=
  ∃ i ≤ d, IsUnary (hierOf w i)

/-- The core run of `x^m` is the orbit of `⋆` under `κ(x, ·)`. -/
theorem core_replicate {Γ C : Type*} (D : Lettered Γ C) (x : Γ) (m : ℕ) :
    ∀ k ≤ m, D.core (List.replicate m x) k = (D.κ x)^[k] D.start := by
  intro k hk
  rw [core_eq_kst, List.take_replicate, Nat.min_eq_left hk]
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', kst_append, ih m (by omega), Function.iterate_succ_apply']
    rfl

/-- Orbits in a finite set: every iterate is an iterate of index `< |C|` and not larger. -/
theorem iterate_small {C : Type*} [Fintype C] (f : C → C) (c : C) :
    ∀ n, ∃ t, t ≤ n ∧ t < Fintype.card C ∧ f^[t] c = f^[n] c := by
  intro n
  let A : DFA Unit C := ⟨fun q _ => f q, c, ∅⟩
  have heval (w : List Unit) (q : C) : A.evalFrom q w = f^[w.length] q := by
    induction w generalizing q with
    | nil => rfl
    | cons a w ih =>
      simpa only [DFA.evalFrom_cons, List.length_cons, Function.iterate_succ_apply]
        using ih (f q)
  obtain ⟨w, hw, hcard, he⟩ := Packets.exists_short_evalFrom A c (List.replicate n ())
  exact ⟨w.length, by simpa using hw.length_le, hcard, by simpa only
    [heval, List.length_replicate] using he⟩

/-- A lettered monitor with finitely many cores has a unary hole `x^m` iff it has one
with `1 ≤ m ≤ |C|`: the core before the last letter of `x^m` recurs at some iterate
`t < |C|` of the orbit of `⋆`, and `x^(t+1)` has the final label of `x^m` and the labels
of a prefix of it, so it is a hole as well. -/
theorem exists_unary_hole_iff {Γ C : Type*} [Fintype C] (D : Lettered Γ C) (x : Γ) :
    (∃ m, D.IsHole (List.replicate m x)) ↔
      ∃ m, 1 ≤ m ∧ m ≤ Fintype.card C ∧ D.IsHole (List.replicate m x) := by
  refine ⟨fun ⟨m, hm⟩ => ?_, fun ⟨m, _, _, hm⟩ => ⟨m, hm⟩⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m'
    · exact absurd rfl hm.ne_nil
    · exact ⟨m', rfl⟩
  obtain ⟨t, ht, htC, hte⟩ := iterate_small (D.κ x) D.start m'
  refine ⟨t + 1, by omega, by omega, ?_⟩

  have hsplit : List.replicate (m' + 1) x =
      List.replicate (t + 1) x ++ List.replicate (m' + 1 - (t + 1)) x := by
    rw [← List.replicate_add]; congr 1; omega
  have hlab : ∀ k ≤ t + 1,
      D.label (List.replicate (t + 1) x) k = D.label (List.replicate (m' + 1) x) k := by
    intro k hk
    rw [label_eq_labFrom, label_eq_labFrom, hsplit,
      labFrom_append_le D _ _ _ (by simpa using hk)]
  have hfin : D.label (List.replicate (t + 1) x) (t + 1) =
      D.label (List.replicate (m' + 1) x) (m' + 1) := by
    rw [Lettered.label_succ _ _ (by simp), Lettered.label_succ _ _ (by simp),
      core_replicate D x _ t (by omega), core_replicate D x _ m' (by omega), hte]
    simp
  obtain ⟨⟨c, a, hl, hT⟩, hE, hI⟩ := hm
  simp only [List.length_replicate] at hl hE hI
  refine ⟨⟨c, a, ?_, hT⟩, fun s hs => ?_, fun s e hc he => ?_⟩
  · rw [List.length_replicate, hfin, hl]
  · rw [List.length_replicate] at hs ⊢
    rw [hfin, hlab s hs.le]
    exact hE s (by omega)
  · rw [List.length_replicate] at he
    have he1 : e ≤ t + 1 := by simpa using hc.2.1
    have hc' : IsComp (List.replicate (m' + 1) x) s e := by
      refine ⟨hc.1, by simp; omega, ?_⟩
      rw [List.drop_replicate, List.drop_replicate,
        show m' + 1 - s = (m' + 1 - e) + (e - s) by have := hc.1; omega, List.replicate_add]
      exact List.prefix_append _ _
    rw [hlab s (by have := hc.1; omega), hlab e he.le]
    exact hI s e hc' (by omega)

end Bounded

end DeciNSSE.LetteredHierarchy
