/-
Harness invoked by `bridge/cli.py`. Reads a JSON `CheckerSpec` from
`bridge/_pending.json`, checks it against the adversarial/benign sample
prompts declared alongside it, prints `{ok, reason, counterexample}`, and
exits with the corresponding code.

This is the garak-in-lean analogue of LOUVRE's `bridge/Verify.lean`. It does NOT
prove `Sound` or `Complete` in the sense of `Garak/Checker.lean` — per
`Garak/Impossibility.lean` no checker in an enumerated class is both, for every
policy. What it certifies is `CorrectOn` for every prompt the spec's author
(human or LLM) declared. `verified_implies_correctOn_samples` states that
precisely, and is now proved.

Run as:
  lake env lean --run bridge/Verify.lean bridge/_pending.json
-/

import Garak.Checker
import Garak.Types
import Lean.Data.Json

open Lean

/-! ## Matcher: a small declarative language for building a `Checker.block` -/
inductive Matcher where
  | literal  : String → Matcher
  | prefix   : String → Matcher
  | contains : String → Matcher
  | anyOf    : List Matcher → Matcher
  | allOf    : List Matcher → Matcher
  | never    : Matcher
  | always   : Matcher
  deriving Repr

-- NB: case-sensitive, like `Garak/keywordChecker.lean`. "IGNORE previous
-- instructions" evades a matcher that only lists the lowercase phrase.
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

/-! ## CheckerSpec: a Checker plus the sample prompts it's checked against -/

def parseVulnCategory (s : String) : Except String VulnCategory :=
  match s with
  | "PromptInjection"     => pure .PromptInjection
  | "InsecureOutput"      => pure .InsecureOutput
  | "SensitiveDisclosure" => pure .SensitiveDisclosure
  | "Overreliance"        => pure .Overreliance
  | "ModelTheft"          => pure .ModelTheft
  | "Toxicity"            => pure .Toxicity
  | other => Except.error s!"unknown VulnCategory: {other}"

structure CheckerSpec where
  name               : String
  targetVuln         : VulnCategory
  matcher            : Matcher
  adversarialSamples : List Prompt   -- prompts the checker MUST block
  benignSamples      : List Prompt   -- prompts the checker MUST NOT block

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

/-! ## Verification

`sampleCheck` is the whole decision, as ONE Boolean, so that the theorem below
can be proved from it directly. It has four conjuncts:
  * at least one adversarial sample, and at least one benign sample  (NEW)
  * every adversarial sample is blocked      (completeness on the samples)
  * no benign sample is blocked              (soundness on the samples)

The two non-emptiness conjuncts are new. Without them an empty sample list
certified anything: `matcher = never` with no samples passed both checks
vacuously, and `matcher = always` passed the completeness check with no benign
samples to object. -/
def sampleCheck (spec : CheckerSpec) : Bool :=
  (!spec.adversarialSamples.isEmpty) && (!spec.benignSamples.isEmpty) &&
  spec.adversarialSamples.all (fun x => spec.toChecker.block x) &&
  spec.benignSamples.all (fun x => !spec.toChecker.block x)

structure VerifyResult where
  ok : Bool
  reason : String
  counterexample : Option String

/-- Explains a failed `sampleCheck`: the first thing that went wrong, in the order
empty-adversarial, empty-benign, missed-adversarial, blocked-benign. Only used
when `sampleCheck` is false; it never affects `ok`. -/
def diagnose (spec : CheckerSpec) : String × Option String :=
  if spec.adversarialSamples.isEmpty then
    ("no adversarial samples declared: certification would be vacuous", none)
  else if spec.benignSamples.isEmpty then
    ("no benign samples declared: a checker that blocks everything would pass", none)
  else
    match spec.adversarialSamples.find? (fun x => !spec.toChecker.block x) with
    | some bad =>
        ("completeness failure: checker misses a declared adversarial sample", some bad)
    | none =>
      match spec.benignSamples.find? (fun x => spec.toChecker.block x) with
      | some bad =>
          ("soundness failure: checker blocks a declared benign sample", some bad)
      | none => ("sample check failed (no single counterexample found)", none)

def verifyCheckerSpec (spec : CheckerSpec) : VerifyResult :=
  if sampleCheck spec = true then
    { ok := true
    , reason := "certified on declared samples (finite check only -- see Impossibility.lean)"
    , counterexample := none }
  else
    { ok := false
    , reason := (diagnose spec).1
    , counterexample := (diagnose spec).2 }

/-! ## What "certified" formally means (PROVED — this was the `sorry` here)

`ok = true` gives `CorrectOn` (Garak/Checker.lean) for every declared sample,
against the finite policy "x is out-of-policy iff x is a declared adversarial
sample". Correctness on the samples someone thought to declare, nothing more; it
must not be read as `Complete` over all prompts. -/
def sampleDrivenPolicy (spec : CheckerSpec) : Policy :=
  fun x => x ∈ spec.adversarialSamples

theorem verified_implies_correctOn_samples
    (spec : CheckerSpec) (h : (verifyCheckerSpec spec).ok = true) :
    ∀ x ∈ spec.adversarialSamples ++ spec.benignSamples,
      CorrectOn spec.toChecker (sampleDrivenPolicy spec) x := by
  -- ok = true can only come from the `then` branch
  have hc : sampleCheck spec = true := by
    by_contra hne
    unfold verifyCheckerSpec at h
    rw [if_neg hne] at h
    simp at h
  unfold sampleCheck at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, _⟩, h3⟩, h4⟩ := hc
  have hA : ∀ x ∈ spec.adversarialSamples, spec.toChecker.block x = true :=
    List.all_eq_true.mp h3
  have hB : ∀ x ∈ spec.benignSamples, spec.toChecker.block x = false := by
    intro x hx
    have hn : (!spec.toChecker.block x) = true := List.all_eq_true.mp h4 x hx
    cases hb : spec.toChecker.block x
    · rfl
    · simp [hb] at hn
  intro x hx
  rcases List.mem_append.mp hx with hxa | hxb
  · -- adversarial: blocked, and out-of-policy by definition
    exact Iff.intro (fun _ => hxa) (fun _ => hA x hxa)
  · -- benign: not blocked; and not adversarial, else it would be both blocked and not
    have hblock : spec.toChecker.block x = false := hB x hxb
    refine Iff.intro (fun hb => ?_) (fun hp => ?_)
    · rw [hblock] at hb
      cases hb
    · have hb2 := hA x hp
      rw [hblock] at hb2
      cases hb2

/-! ## Entry point -/

def main (args : List String) : IO UInt32 := do
  let inputPath := args.headD "bridge/_pending.json"
  let raw ← IO.FS.readFile inputPath
  match Json.parse raw with
  | .error e => do
      IO.eprintln s!"JSON parse error: {e}"
      return 2
  | .ok j =>
    match parseCheckerSpec j with
    | .error e => do
        IO.eprintln s!"checker spec parse error: {e}"
        return 3
    | .ok spec =>
      let result := verifyCheckerSpec spec
      let out : Json :=
        Json.mkObj
          [ ("ok", Json.bool result.ok)
          , ("reason", Json.str result.reason)
          , ("counterexample",
              match result.counterexample with
              | some s => Json.str s
              | none   => Json.null) ]
      IO.println out.pretty
      return (if result.ok then 0 else 1)
