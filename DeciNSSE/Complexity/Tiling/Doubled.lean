import DeciNSSE.Complexity.Tiling.FixedCode
import DeciNSSE.Complexity.Directions

/-! # Doubled direction codes

## Main declarations

- `doubledCode` decodes pairs of identical binary directions at every arity at least two.
-/

namespace DeciNSSE.Complexity.Tiling
variable {n : ℕ}

/-- Encode each binary symbol as two identical constructor directions. The decoder remembers the
first direction until the pair is complete. -/
def doubledCode (hn : 2 ≤ n) : FixedCode (Fin 2) (Fin n) where
  spell a := [Directions.embedDir hn a, Directions.embedDir hn a]
  width := 2
  pos := by decide
  length _ := rfl
  inj := fun _ _ h => Directions.embedDir_injective hn (List.cons.inj h).1
  phases := 3
  parse phase a := if h : a.val < 2 then
    if phase = 0 then some (.inl (a.val + 1))
    else if phase = a.val + 1 then some (.inr ⟨a.val,h⟩) else none
    else none
  partialWord p i := (p = [] ∧ i = 0) ∨
    ∃ b : Fin 2, p = [Directions.embedDir hn b] ∧ i = b.val + 1
  initial := Or.inl ⟨rfl,rfl⟩
  bounded := by rintro _ _ (⟨rfl,rfl⟩ | ⟨b,rfl,rfl⟩) <;> omega
  boundary := by rintro _ (⟨rfl,_⟩ | ⟨b,_,h⟩) <;> simp_all
  advance := by
    rintro p i b res hp h
    split at h <;> rename_i hb
    · rcases hp with ⟨rfl,rfl⟩ | ⟨a,rfl,rfl⟩
      · simp only [ite_true, Option.some.injEq] at h
        subst res
        exact Or.inr ⟨⟨b.val,hb⟩,rfl,rfl⟩
      · simp only [Nat.succ_ne_zero, ite_false] at h
        split at h
        · next eq => cases h; congr 2; apply Fin.ext; simp; omega
        · cases h
    · cases h
  complete := by
    rintro a p b r i (⟨rfl,rfl⟩ | ⟨bit,rfl,rfl⟩) h
    · simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      fin_cases a <;> simp
    · simp only [List.singleton_append, List.cons.injEq, List.nil_eq] at h
      obtain ⟨eq, eq', rfl⟩ := h
      have := Directions.embedDir_injective hn eq
      subst bit; subst b
      simp [a.isLt]

end DeciNSSE.Complexity.Tiling
