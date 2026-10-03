import DeciNSSE.Words

/-! # Periods of binary words

The Fine–Wilf theorem, modular positions and powers of words control periodic
comparisons. These identities support the bounds on rejected tails.
-/

namespace DeciNSSE.Words

variable {u v w : Word} {p q n : ℕ}

theorem fine_wilf (hp : HasPeriod w p) (hq : HasPeriod w q)
    (hlen : p + q - Nat.gcd p q ≤ w.length) : HasPeriod w (Nat.gcd p q) :=
  hasPeriod_iff_list_hasPeriod.mpr
    ((hasPeriod_iff_list_hasPeriod.mp hp).gcd (hasPeriod_iff_list_hasPeriod.mp hq) hlen)

theorem HasPeriod.infix (h : HasPeriod w p) (hv : v <:+: w) : HasPeriod v p :=
  hasPeriod_iff_list_hasPeriod.mpr ((hasPeriod_iff_list_hasPeriod.mp h).infix hv)

theorem HasPeriod.mod_eq (h : HasPeriod w p) (hi : n < w.length) :
    w[n]? = w[n % p]? :=
  ((hasPeriod_iff_list_hasPeriod.mp h).getElem?_mod p n w hi).symm

theorem HasPeriod.eq_of_mod (h : HasPeriod w p) {a b : ℕ}
    (ha : a < w.length) (hb : b < w.length) (heq : a % p = b % p) :
    w[a]? = w[b]? := by rw [h.mod_eq ha, h.mod_eq hb, heq]

theorem hasPeriod_pow (u : Word) (n : ℕ) : HasPeriod (pow u n) u.length := by
  apply hasPeriod_iff_list_hasPeriod.mpr
  cases n with
  | zero => simp
  | succ n =>
    change pow u (n + 1) <+: (pow u (n + 1)).take u.length ++ pow u (n + 1)
    rw [pow_succ, List.take_left]
    exact prefix_append_of_prefix_pow (n + 1) List.prefix_rfl

theorem getElem?_pow (hu : u ≠ []) (hi : n < (pow u q).length) :
    (pow u q)[n]? = u[n % u.length]? := by
  rw [(hasPeriod_pow u q).mod_eq hi]
  cases q with
  | zero => simp at hi
  | succ q =>
    exact List.getElem?_append_left (Nat.mod_lt _ (List.length_pos_iff.mpr hu))

def W (x y z : Word) (i : ℕ) : Word := x ++ pow y i ++ z

end DeciNSSE.Words
