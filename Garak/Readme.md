# `Garak/` — scanner model and checker theory

This folder models the pieces of the garak scanner as checked mathematical
objects, and proves the static results the paper contrasts its feedback model
against: no fixed checker is complete, which is why continued discovery and
repair are needed.

Most files are plain Lean and build without Mathlib; `Impossibility.lean` needs
Mathlib (for `Finset` and the diagonal argument).

## Files

| File | What it contains |
| --- | --- |
| `Types.lean` | Core data structures: `VulnCategory` (the six vulnerability classes), `Probe`, `Response`, `Turn`, `Conversation`. Definitions only. |
| `Detector.lean` | `Detector` — a scoring function `Response → Score` deciding whether a response is a hit, plus the `Score` abbreviation. |
| `Atkgen.lean` | Adaptive attack generation: `AtkgenStrategy` (choose the next probe from history), `runConversation` (unroll a multi-turn conversation), and `EventuallyTriggers` (a strategy eventually elicits a toxic response within a turn budget). |
| `Theorems.lean` | Small proved facts about conversations: a 0-turn run is empty, an `n`-turn run has length `n` (induction), and `EventuallyTriggers` instantiated on a concrete strategy. Mathlib-free. |
| `Checker.lean` | The checker model. `Checker` blocks or allows a prompt; `Sound` = never blocks a benign prompt (no false positives); `Complete` = never misses an out-of-policy prompt (no false negatives); `CorrectOn` = blocks exactly the out-of-policy prompts. Proves `correctOn_iff_sound_and_complete`: `Sound ∧ Complete ↔ correct on every prompt`. |
| `keywordChecker.lean` | A concrete keyword-blocklist checker. `demoChecker_misses_evasivePrompt` proves (by `native_decide`) that a harmful prompt paraphrased around the keyword list slips through; `demoChecker_not_complete` concludes it is not `Complete`. Grounds the abstract impossibility in a runnable example. |
| `Impossibility.lean` | The negative results. Pigeonhole: a finite blocklist smaller than the adversarial set must miss one. Evasion: if any blocked attack has an evading extension, completeness fails. Diagonal (the main result): for any enumerated family of checkers there is a policy no member is both sound and complete for. Needs Mathlib. |
| `Survival.lean`, `Process.lean` | Earlier backbone lemmas (geometric decay, a one-round survival step, etc.). The coverage proofs now live in `Proofs/` and are self-contained, so these two are not imported by them — removal candidates pending a check. |

## Notes

- `Complete` is the one-directional "no misses" predicate; `Sound ∧ Complete` is
  the meaningful conjunction (see `correctOn_iff_sound_and_complete`).
- `keywordChecker.lean` uses `native_decide`, which trusts the compiled evaluator
  (adds the axiom `Lean.ofReduceBool`) — `decide` can't be used because
  `String.splitOn` does not reduce in the kernel.
- The impossibility results are about *enumerated (countable)* checker classes;
  they do not claim "every checker misses an attack" (block-everything never does).