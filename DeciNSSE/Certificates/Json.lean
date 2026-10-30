import DeciNSSE.Solver.Checked
import Lean.Data.Json

/-! # JSON certificate checker

Usage: `nsse-check problem.json certificate.json`.
The problem has `k`, `variance` (or `arity`), `lits`, `x`, and `y`, as
described in the README. Certificates are `{"kind":"unsat"}`,
`{"kind":"refutation","side":"l"|"r","word":[...]}`, or
`{"kind":"entailment","left":C,"right":C}`. Each cover C has natural
`window`, `rays` as pairs `[access, period]` of words, and `access` as a list
of words. Letters and variable indices are checked against their bounds.
-/

set_option autoImplicit false
namespace DeciNSSE.Certificates.Command
open Lean

/-- A parsed problem retains the bounds in the types of all indices. -/
structure Problem where
  n : ℕ
  k : ℕ
  variance : Fin n → Bool
  constraints : Constraint n k
  x : V k
  y : V k

private def array (j : Json) : Except String (List Json) :=
  Array.toList <$> j.getArr?

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def index (n : ℕ) (j : Json) : Except String (Fin n) := do
  let i ← j.getNat?
  if h : i < n then return ⟨i, h⟩
  else throw s!"index {i} is outside 0..{n}"

private def word (n : ℕ) (j : Json) : Except String (List (Fin n)) := do
  (← array j).mapM (index n)

private def children (n k : ℕ) (js : List Json) : Except String (Fin n → V k) := do
  let xs ← js.mapM (index k)
  if h : xs.length = n then
    return fun i => xs.get ⟨i.val, by omega⟩
  else throw s!"expected {n} constructor arguments, got {xs.length}"

private def literal (n k : ℕ) (j : Json) : Except String (Lit n k) := do
  match ← array j with
  | op :: root :: args =>
    let op ← op.getStr?
    let root ← index k root
    match op with
    | "bot" =>
      if args.isEmpty then return .eqBot root else throw "bot takes one variable"
    | "top" =>
      if args.isEmpty then return .eqTop root else throw "top takes one variable"
    | "le" => return .leF root (← children n k args)
    | "ge" => return .fLe (← children n k args) root
    | _ => throw s!"unknown literal: {op}"
  | _ => throw "a literal needs an operator and a variable"

private def optionalNat (j : Json) (key : String) (fallback : ℕ) : Except String ℕ :=
  match j.getObjVal? key with
  | .ok v => v.getNat?
  | .error _ => .ok fallback

/-- Parse the solver's problem format, rejecting invalid indices and variances. -/
def parseProblem (j : Json) : Except String Problem := do
  let k ← (← field j "k").getNat?
  let variance ← match j.getObjVal? "variance" with
    | .ok v => (← array v).mapM fun a => do
      match ← a.getNat? with
      | 0 => return false
      | 1 => return true
      | _ => throw "variance entries must be 0 or 1"
    | .error _ => pure (List.replicate (← optionalNat j "arity" 2) false)
  let n := variance.length
  let arity ← optionalNat j "arity" n
  if arity != n then throw "arity and variance length disagree"
  let constraints ← (← array (← field j "lits")).mapM (literal n k)
  let x ← index k (toJson (← optionalNat j "x" 0))
  let y ← index k (toJson (← optionalNat j "y" 1))
  return ⟨n, k, fun i => variance.get i, constraints, x, y⟩

private def ray (n : ℕ) (j : Json) : Except String (Ray (Fin n)) := do
  match ← array j with
  | [u, v] => return ⟨← word n u, ← word n v⟩
  | _ => throw "a ray must be [access_word, period_word]"

private def cover (n : ℕ) (j : Json) : Except String (Cover (Fin n)) := do
  return ⟨← (← field j "window").getNat?,
    ← (← array (← field j "rays")).mapM (ray n),
    ← (← array (← field j "access")).mapM (word n)⟩

/-- Parse and check a certificate for the given problem. -/
def verify (p : Problem) (j : Json) : Except String Unit := do
  match ← (← field j "kind").getStr? with
  | "unsat" =>
    if Solver.Checked.checkEntailment p.variance p.constraints p.x p.y .unsat then return ()
    else throw "unsatisfiability check failed"
  | "refutation" =>
    let side ← match ← (← field j "side").getStr? with
      | "l" => pure Side.l
      | "r" => pure Side.r
      | _ => throw "side must be l or r"
    let w ← word p.n (← field j "word")
    if Solver.Checked.checkRefutation p.variance p.constraints p.x p.y ⟨side, w⟩ then return ()
    else throw "refutation check failed: system unsatisfiable or word is not a hole"
  | "entailment" =>
    let left ← cover p.n (← field j "left")
    let right ← cover p.n (← field j "right")
    if Solver.Checked.checkEntailment p.variance p.constraints p.x p.y (.cover left right) then return ()
    else throw "cover check failed: invalid ray, missing initial state, uncovered state, or missing successor"
  | kind => throw s!"unknown certificate kind: {kind}"

end DeciNSSE.Certificates.Command

