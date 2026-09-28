/-
Runtime entry point: apply one or more CERTIFIED `CheckerSpec` JSONs
(certified by `Verify.lean`) to real prompts, and print a block/allow
verdict for each.

Two prompt sources:
  1. stdin, one prompt per line (default)
  2. `--trace <path>` -- a garak scan trace JSON with the shape
     `{"turns": [{"attackerPrompt": "...", ...}, ...]}`. This lets a
     certified checker be checked against prompts an actual `atkgen` run
     threw at a real target model, not just hand-picked samples -- the
     "would this checker have caught what garak's live run actually did"
     question from the brown-bag notes. (Deliberately reads only the
     `attackerPrompt` field so it stays forward-compatible with any
     richer trace schema -- it doesn't require a specific Lean type for
     the trace, just that shape of JSON.)

Usage:
  cat prompts.txt \
    | lake env lean --run bridge/Apply.lean bridge/examples/prompt_injection.json

  # OR-composed across multiple certified checkers:
  cat prompts.txt \
    | lake env lean --run bridge/Apply.lean checkers/toxicity.json checkers/injection.json

  lake env lean --run bridge/Apply.lean --trace trace.json checkers/toxicity.json

This is the deployment-side companion to `Verify.lean`, exactly as
`Apply.lean` is to `Verify.lean` in LOUVRE. For correctness, only run
CheckerSpecs that have actually been certified by `Verify.lean`.

NOTE on composition: LOUVRE's `Apply.lean` folds redaction policies
left-to-right, because each transform's output feeds the next. A
`Checker` doesn't transform text, it makes a block/allow decision, so
composing several certified checkers here is OR across them (a prompt is
blocked if ANY of them would block it) rather than a sequential fold.
-/

import Garak.Checker
import Garak.Types
import Lean.Data.Json

open Lean

/-! Duplicated from `Verify.lean` on purpose (same as LOUVRE's own
    `Verify.lean` / `Apply.lean`, which duplicate `parseMatcher` /
    `parsePolicy` rather than share a module): keeps each bridge script
    fully self-contained and runnable via `lake env lean --run` without
    any extra `lakefile.toml` wiring. -/
inductive Matcher where
  | literal  : String → Matcher
  | prefix   : String → Matcher
  | contains : String → Matcher
  | anyOf    : List Matcher → Matcher
  | allOf    : List Matcher → Matcher
  | never    : Matcher
  | always   : Matcher
  deriving Repr

partial def Matcher.accepts (m : Matcher) (p : Prompt) : Bool :=
  match m with
  | .literal v  => p = v
  | .prefix v   => p.take v.length == v
  | .contains v => (p.splitOn v).length > 1
  | .anyOf ms   => ms.any (fun m => m.accepts p)
  | .allOf ms   => ms.all (fun m => m.accepts p)
  | .never      => false
  | .always     => true

partial def parseMatcher (j : Json) : Except String Matcher := do
  let kind ← j.getObjValAs? String "kind"
  match kind with
  | "literal" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.literal v
  | "prefix" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.prefix v
  | "contains" => do
      let v ← j.getObjValAs? String "value"
      return Matcher.contains v
  | "anyOf" => do
      let items ← j.getObjValAs? (Array Json) "items"
      let ms ← items.mapM parseMatcher
      return Matcher.anyOf ms.toList
  | "allOf" => do
      let items ← j.getObjValAs? (Array Json) "items"
      let ms ← items.mapM parseMatcher
      return Matcher.allOf ms.toList
  | "never"  => return Matcher.never
  | "always" => return Matcher.always
  | k => Except.error s!"unknown matcher kind: {k}"

structure CheckerSpec where
  name               : String
  targetVuln         : VulnCategory
  matcher            : Matcher
  adversarialSamples : List Prompt
  benignSamples      : List Prompt

def parseVulnCategory (s : String) : Except String VulnCategory :=
  match s with
  | "PromptInjection"     => pure .PromptInjection
  | "InsecureOutput"      => pure .InsecureOutput
  | "SensitiveDisclosure" => pure .SensitiveDisclosure
  | "Overreliance"        => pure .Overreliance
  | "ModelTheft"          => pure .ModelTheft
  | "Toxicity"            => pure .Toxicity
  | other => Except.error s!"unknown VulnCategory: {other}"

def parseCheckerSpec (j : Json) : Except String CheckerSpec := do
  let name ← j.getObjValAs? String "name"
  let targetVulnStr ← j.getObjValAs? String "targetVuln"
  let targetVuln ← parseVulnCategory targetVulnStr
  let matcherJson ← j.getObjVal? "matcher"
  let matcher ← parseMatcher matcherJson
  let adv ← j.getObjValAs? (Array String) "adversarialSamples"
  let ben ← j.getObjValAs? (Array String) "benignSamples"
  return { name := name
           targetVuln := targetVuln
           matcher := matcher
           adversarialSamples := adv.toList
           benignSamples := ben.toList }

def CheckerSpec.toChecker (spec : CheckerSpec) : Checker :=
  { name := spec.name, block := fun p => spec.matcher.accepts p }

/-! ## Applying (possibly several) certified checkers to a prompt, OR-composed -/

structure Verdict where
  prompt    : String
  blocked   : Bool
  blockedBy : List String

def applyCheckers (checkers : List (String × Checker)) (p : Prompt) : Verdict :=
  let hits := (checkers.filter (fun nc => nc.2.block p = true)).map (fun nc => nc.1)
  { prompt := p, blocked := !hits.isEmpty, blockedBy := hits }

/-! ## Loading certified specs from disk, one file per positional arg -/

partial def loadCheckerSpecs (paths : List String) :
    IO (Except UInt32 (List (String × Checker))) := do
  match paths with
  | [] => pure (Except.ok [])
  | path :: rest => do
    let raw ← IO.FS.readFile path
    match Json.parse raw with
    | .error e => do
        IO.eprintln s!"JSON parse error in {path}: {e}"
        pure (Except.error 3)
    | .ok j =>
      match parseCheckerSpec j with
      | .error e => do
          IO.eprintln s!"checker spec parse error in {path}: {e}"
          pure (Except.error 4)
      | .ok spec => do
          match ← loadCheckerSpecs rest with
          | .error code => pure (Except.error code)
          | .ok more => pure (Except.ok ((spec.name, spec.toChecker) :: more))

/-! ## Reading prompts: stdin (one per line) or a trace file -/

partial def readAllStdinLines (s : IO.FS.Stream) : IO (List String) := do
  let line ← s.getLine
  if line.isEmpty then
    return []
  else
    let rest ← readAllStdinLines s
    return line.trimRight :: rest

-- Reads only `turns[*].attackerPrompt` from a trace JSON, ignoring every
-- other field, so this stays forward-compatible with a richer schema.
def loadPromptsFromTrace (path : String) : IO (Except String (List String)) := do
  let raw ← IO.FS.readFile path
  match Json.parse raw with
  | .error e => pure (.error s!"JSON parse error in {path}: {e}")
  | .ok j =>
    match j.getObjValAs? (Array Json) "turns" with
    | .error e => pure (.error s!"trace missing 'turns' array: {e}")
    | .ok turns =>
      let prompts := turns.toList.filterMap (fun t =>
        (t.getObjValAs? String "attackerPrompt").toOption)
      pure (.ok prompts)

/-! ## Entry point -/

def printVerdicts (checkers : List (String × Checker)) (prompts : List String) : IO Unit := do
  for p in prompts do
    let v := applyCheckers checkers p
    let verdict := if v.blocked then "BLOCKED" else "ALLOWED"
    let by_ := if v.blockedBy.isEmpty then "-" else String.intercalate ", " v.blockedBy
    IO.println s!"{verdict}\t{by_}\t{v.prompt}"

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Apply.lean: apply certified CheckerSpec JSON(s) to real prompts."
    IO.eprintln ""
    IO.eprintln "Usage:"
    IO.eprintln "  cat prompts.txt | lake env lean --run bridge/Apply.lean <spec.json> ..."
    IO.eprintln "  lake env lean --run bridge/Apply.lean --trace <trace.json> <spec.json> ..."
    return 1
  let (traceArg, specArgs) :=
    match args with
    | "--trace" :: path :: rest => (some path, rest)
    | _ => (none, args)
  if specArgs.isEmpty then
    IO.eprintln "at least one CheckerSpec JSON is required"
    return 1
  match ← loadCheckerSpecs specArgs with
  | .error code => return code
  | .ok checkers => do
    match traceArg with
    | some tracePath => do
        match ← loadPromptsFromTrace tracePath with
        | .error e => do
            IO.eprintln s!"trace load error: {e}"
            return 5
        | .ok prompts => do
            printVerdicts checkers prompts
            return 0
    | none => do
        let stdin ← IO.getStdin
        let prompts ← readAllStdinLines stdin
        printVerdicts checkers prompts
        return 0
