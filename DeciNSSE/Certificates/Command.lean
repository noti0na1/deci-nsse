import DeciNSSE.Certificates.Json

/-! # The certificate checking command

`nsse-check problem.json certificate.json` parses the problem and the certificate with
`Certificates.Json` and checks the certificate with the packed checkers of
`Solver.Checked`.
-/

/-- Read a problem and a certificate, given alone or as the `certificate` field
of an `nsse` result; return a nonzero status on rejection. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [problemPath, certificatePath] =>
      let problemText ← IO.FS.readFile problemPath
      let certificateText ← IO.FS.readFile certificatePath
      let result := do
        let p ← DeciNSSE.Certificates.Json.parseProblem (← Lean.Json.parse problemText)
        let j ← Lean.Json.parse certificateText
        DeciNSSE.Certificates.Json.verify p ((j.getObjVal? "certificate").toOption.getD j)
      match result with
      | .ok () => IO.println "VERIFIED"; return 0
      | .error reason => IO.println s!"REJECTED: {reason}"; return 1
    | _ => IO.println "usage: nsse-check problem.json certificate.json"; return 2
  catch e =>
    IO.println s!"ERROR: {e}"
    return 2
