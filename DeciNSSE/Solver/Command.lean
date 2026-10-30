import DeciNSSE.Solver
import DeciNSSE.Certificates.Json

/-! # JSON entailment queries

`nsse problem.json [--fuel N] [--window N] [--no-countermodel]` prints a
checked answer, its certificate, and the regular countermodel graphs for a
negative answer. With `--no-countermodel` the countermodel is not built.
-/

namespace DeciNSSE.Solver.Command
open Lean Certificates
variable {n k : ℕ}

private def wordJson (w : List (Fin n)) : Json := toJson (w.map Fin.val)

private def coverJson (c : Cover (Fin n)) : Json := Json.mkObj [
  ("window", toJson c.window),
  ("rays", toJson (c.rays.map fun r => toJson [wordJson r.access, wordJson r.period])),
  ("access", toJson (c.access.map wordJson))]

private def entailmentJson : Entailment n → Json
  | .unsat => Json.mkObj [("kind", toJson "unsat")]
  | .cover l r => Json.mkObj [("kind", toJson "entailment"),
      ("left", coverJson l), ("right", coverJson r)]

private def graphJson (g : RGraph n) : Json :=
  Json.mkObj [("root", toJson g.root.val), ("nodes", toJson ((List.finRange g.size).map fun p =>
    match g.label p with
    | .bot => toJson [toJson "B"]
    | .top => toJson [toJson "T"]
    | .f => toJson (toJson "F" :: (List.finRange n).map fun a => toJson (g.child p a).val)))]

/-- Serialize the proof data; proof terms themselves are erased. -/
def resultJson {c : Fin n → Bool} {ϕ : Constraint n k} {x y : V k}
    (r : Result c ϕ x y) : Json :=
  let common := [("answer", toJson r.answer), ("used_fallback", toJson r.usedFallback)]
  match r.evidence with
  | .entailed cert _ => Json.mkObj (common ++ [("certificate", entailmentJson cert)])
  | .complete _ => Json.mkObj (common ++ [("certificate", Json.mkObj [("kind", toJson "complete")])])
  | .refuted cert _ model => Json.mkObj (common ++ [
      ("certificate", Json.mkObj [("kind", toJson "refutation"),
        ("side", toJson (match cert.side with | .l => "l" | .r => "r")),
        ("word", wordJson cert.word)])] ++
      match model with
      | some m => [("countermodel", toJson ((List.finRange k).map fun z => graphJson (m.graphs z)))]
      | none => [])

private def usage : String :=
  "usage: nsse problem.json [--fuel N] [--window N] [--no-countermodel]"

/-- Command-line options: search fuel, terminal window, and whether to build countermodels. -/
private structure Options where
  fuel : ℕ := 100000
  window : ℕ := 0
  withModel : Bool := true

private def natArg (name v : String) : Except String ℕ :=
  match v.toNat? with
  | some n => .ok n
  | none => .error s!"{name} must be a natural number"

private def options (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--fuel" :: v :: rest => do options { o with fuel := ← natArg "fuel" v } rest
  | "--window" :: v :: rest => do options { o with window := ← natArg "window" v } rest
  | "--no-countermodel" :: rest => options { o with withModel := false } rest
  | _ => .error usage

/-- Parse a problem, solve it, and print a single JSON result. -/
def run (args : List String) : IO UInt32 := do
  try
    match args with
    | path :: opts =>
      let text ← IO.FS.readFile path
      let parsed := do
        let o ← options {} opts
        let p ← Certificates.Command.parseProblem (← Json.parse text)
        return (p, o)
      match parsed with
      | .error e => IO.eprintln e; return 2
      | .ok (p, o) =>
        let start ← IO.monoMsNow
        let result := solveWithFuel p.variance p.constraints p.x p.y o.fuel o.window o.withModel
        let output := resultJson result
        let serialized := output.compress
        let elapsed ← IO.monoMsNow
        IO.println serialized
        IO.eprintln s!"elapsed_ms={elapsed - start}"
        return 0
    | [] => IO.eprintln usage; return 2
  catch e => IO.eprintln s!"ERROR: {e}"; return 2

end DeciNSSE.Solver.Command

def main := DeciNSSE.Solver.Command.run
