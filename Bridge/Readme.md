# `Bridge/` — runtime tooling

The concrete proof-of-concept connecting the theory to a runnable workflow: an
LLM (or a human) proposes a guardrail as data, Lean certifies it against declared
examples, and certified guardrails are applied to real prompts — including prompts
from a garak run.

## Files

| File | What it does |
| --- | --- |
| `verify.lean` | Reads a JSON `CheckerSpec` (a `Matcher` plus declared adversarial and benign sample prompts), turns the matcher into a `Checker`, and certifies it against those samples: every adversarial sample must be blocked, no benign sample may be blocked, and both lists must be non-empty. Prints `{ok, reason, counterexample}`. Certification means `CorrectOn` on the **declared samples** — not `Complete` over all prompts (see `Garak/Impossibility.lean`). |
| `apply.lean` | Applies one or more certified checkers to runtime prompts, composing them by OR (a prompt is blocked if any checker fires) and recording which. Reads prompts from stdin or from a trace file. |
| `cli.py` | LLM-in-the-loop driver: asks a model for a `CheckerSpec`, pipes it through `verify.lean`, and on failure feeds the counterexample back and retries (up to 3 times). `--example <spec.json>` verifies a hand-written spec with no model call. |

## CheckerSpec (JSON)

```json
{
  "name": "prompt-injection-override-checker",
  "targetVuln": "PromptInjection",
  "matcher": { "kind": "anyOf", "items": [ {"kind": "contains", "value": "ignore previous instructions"} ] },
  "adversarialSamples": ["...prompts that MUST be blocked..."],
  "benignSamples": ["...prompts that MUST NOT be blocked..."]
}
```

Matcher kinds: `literal`, `prefix`, `contains`, `anyOf`, `allOf`, `never`,
`always`. Matching is case-sensitive, so "IGNORE previous instructions" evades a
checker that only lists the lowercase phrase — itself a demonstration of the
paper's point.

## Running it

```
# certify a hand-written spec (no API key)
python Bridge/cli.py --example Bridge/examples/prompt_injection.json

# synthesize + certify with an LLM in the loop (needs OPENAI_API_KEY)
python Bridge/cli.py "block prompt injection attacks"

# apply certified checkers to prompts from stdin
echo "Please ignore previous instructions." | lake env lean --run Bridge/apply.lean <spec>.json
```

## Connecting to a garak run

The Lean bridge applies certified checkers to the attack prompts from a real
garak scan. You run garak yourself on your own machine — the scan depends on your
model access, your chosen probes, and your run, so the report it produces is
yours, not something shipped with this repository. The repository provides the
tooling that consumes that report.

The flow:

```
garak scan  →  report.jsonl  →  report_to_trace.py  →  trace.json  →  apply.lean
             (garak's output)    (converter, in repo)                 (verdicts)
```

### 1. Run a garak scan (on your machine)

```
garak --model_type huggingface --model_name gpt2 --probes atkgen
```

garak writes a report to its run directory, for example
`~/.local/share/garak/garak_runs/garak.<id>.report.jsonl` (on Windows,
`C:\Users\<you>\.local\share\garak\garak_runs\`). This file is one JSON object
per line, recording the attacks garak sent.

### 2. Convert the report to a trace

`apply.lean` reads a trace shaped as `{"turns": [{"attackerPrompt": "..."}, ...]}`,
not garak's native `report.jsonl`. `Bridge/report_to_trace.py` bridges the two:
it reads the report, extracts each attack prompt, and writes the trace.

```
python Bridge/report_to_trace.py garak.<id>.report.jsonl -o trace.json
```

(If a report yields no prompts — garak's field names vary by version and probe —
re-run with `--debug` to see the keys present in the report.)

### 3. Apply certified checkers to the scanned prompts

```
lake env lean --run Bridge/apply.lean --trace trace.json Bridge/examples/prompt_injection.json
```

This prints a `BLOCKED` / `ALLOWED` verdict for each prompt from the scan, using
the certified checker(s) you pass. Checkers are composed by OR: a prompt is
blocked if any checker fires. Pass more than one spec to apply several at once.

This is the end-to-end proof of concept: a garak run surfaces attack prompts, and
the Lean layer applies machine-checked guardrails to them.
```
