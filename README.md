# Garak in Lean

This repository is a Lean 4 formalization of ideas from
[garak](https://github.com/NVIDIA/garak), an LLM vulnerability scanner. It models
the pieces of a scanner as checked mathematical objects: prompts, probes,
responses, detectors, guardrail checkers, adaptive attack generation, and the
properties we would like those components to satisfy.

The goal is to make claims about scanner behavior precise enough that Lean
can type-check the definitions and verify the proofs.

## What Is Modeled

- `Probe`, `Response`, `Turn`, and `Conversation` model scanner interactions.
- `Detector` models a detector that scores model responses.
- `Checker` models a guardrail that either blocks or allows prompts.
- `AtkgenStrategy` models an adaptive attack generator that chooses the next
  probe from conversation history.
- `Complete`, `Sound`, and `EventuallyTriggers` state scanner properties as
  Lean propositions.

## Repository Layout

```text
Garak/
  Types.lean          Core data structures for probes, responses, and conversations
  Detector.lean       Detector scores and detector specifications
  Checker.lean        Prompt policies, checker soundness, and completeness
  Atkgen.lean         Adaptive attack generation over conversations
  Theorems.lean       Proved properties about conversations and triggering
  Impossibility.lean  Pigeonhole-style results
  keywordChecker.lean Small keyword-checker example and evasion proof
  Basic.lean          Minimal starter module
Garak.lean            Library entry point
demo.lean             Walkthrough file
lakefile.toml         Lake project configuration
lean-toolchain        Lean version pin
```

## Claims

The project already proves several small but useful facts:

- Running an attack conversation for `0` turns produces an empty conversation.
- Running for `n` turns produces exactly `n` turns.
- If a detector fires at some turn within `maxTurns`, then
  `EventuallyTriggers` holds.
- A finite signatures argument: if there are more adversarial prompts than
  signatures, some adversarial prompt is uncaught.
- A toy keyword checker misses a paraphrased harmful prompt, so it is not
  complete for the demo policy.

## How This Lean Layer Fits With garak

garak remains the executable scanner. This Lean project is a specification and
proof layer that can sit beside garak and make parts of its behavior precise.
In a normal garak run, garak selects probe and detector plugins, runs probes
against a model generator through a harness, and evaluates the detector results.
This repository abstracts that flow into Lean definitions that can be reasoned
about formally.

| garak concept | Lean model in this repo | Role |
| --- | --- | --- |
| Probe plugin | `Probe` and `AtkgenStrategy` | Generates prompts or chooses the next probe |
| Model output | `Response` | Represents the generator's reply |
| Detector plugin | `Detector` | Scores or specifies whether a response shows a failure mode |
| Harness run | `runConversation` | Builds a conversation over a fixed number of turns |
| Guardrail or filter | `Checker` | Blocks or allows prompts according to a policy |
| Evaluation claim | `Complete`, `Sound`, `EventuallyTriggers` | States what should be true about the scan |

A practical integration path would look like this:

1. Model the intended behavior of a garak probe, detector, checker, or harness
   as Lean definitions.
2. Prove invariants about that model, such as conversation length, detector
   triggering, checker completeness, or known evasion cases.
3. Implement or update the corresponding garak Python plugin using those Lean
   definitions as a design contract.
4. Export selected garak scan traces into a simple format, such as JSON, and map
   them back to Lean values like `Conversation`, `Turn`, `Probe`, and `Response`
   for replay or proof-driven analysis.
