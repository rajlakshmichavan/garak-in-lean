# garak-in-lean

![Build](https://github.com/rajlakshmichavan/garak-in-lean/actions/workflows/lean.yml/badge.svg)

[![arXiv](https://img.shields.io/badge/arXiv-XXXX.XXXXX-b31b1b.svg)](https://arxiv.org/abs/2610.09892)

Paper: [*Defensive Sufficiency in a Stackelberg Model of AI Security*](https://arxiv.org/abs/2610.09892)

A machine-checkable verification layer in Lean on top of the garak LLM scanner, with Lean-verified proofs of the coverage theorems from *Defensive Sufficiency in a Stackelberg Model of AI Security*.

## Repository Layout

The repository has three parts. Each folder has its own README with the full
file-by-file detail; this is the overview.

| Folder | What it is | Details |
| --- | --- | --- |
| `Garak/` | The scanner model (types, detectors, attack generation) and the checker / impossibility results — the static picture the paper contrasts against. | [`Garak/README.md`](Garak/README.md) |
| `Proofs/` | The paper's probabilistic coverage theorems (2, 3, 5, 7 and Lemma 6) — the mathematical core. | [`Proofs/README.md`](Proofs/README.md) |
| `Bridge/` | Runtime tooling: certify a checker spec, apply certified checkers to prompts, drive LLM-in-the-loop synthesis — the runnable proof-of-concept. | [`Bridge/README.md`](Bridge/README.md) |

`Garak.lean` is the build root, `demo.lean` is a scratchpad (never imported, and it
contains intentionally false statements), and `lakefile.toml` / `lean-toolchain` /
`lake-manifest.json` hold the Lake config, the Lean version pin, and the Mathlib lock.

### How the pieces fit together

- The `Proofs/` theorems establish, in the abstract, when continued discovery and
  repair guarantee coverage.
- The `Garak/` checker and impossibility results show why feedback is needed: no
  fixed checker is complete.
- The `Bridge/` layer connects the two to practice: a garak run produces attack
  prompts, and the Lean bridge certifies and applies checkers against them.

## Running This Yourself

garak and the Lean proofs both run locally. The two steps are independent, and
garak comes first.

1. **Install and run garak.** garak is NVIDIA's LLM vulnerability scanner. Install
   it with `pip install -U garak`, then run a scan, e.g.
   `garak --model_type huggingface --model_name gpt2 --probes atkgen`. This writes a
   report of attack attempts to garak's run directory.
2. **Install Lean and build the proofs.** Install Lean through `elan`, then from the
   repository root run `lake exe cache get` (downloads prebuilt Mathlib) and
   `lake build`. The first build takes a while; afterwards it is cached.
3. **Run the bridge on a real scan.** See [`Bridge/README.md`](Bridge/README.md) for
   certifying a checker and applying it to prompts from a garak run.

Both steps are local because garak needs your own model access and the Lean build
needs Mathlib downloaded to your machine.

## Notes for AI Agents

If you are an LLM or coding agent working in this repository, read this first.

- **Two independent parts.** `Garak/` + `Proofs/` are Lean proofs (need Mathlib,
  built via `lake build`). `Bridge/` is runtime tooling and does not need the proofs
  to run. Know which one a task touches.
- **Never introduce `sorry`.** If a proof cannot be closed, stop and say so. Do not
  weaken a theorem's statement (its hypotheses or conclusion) to make it compile —
  that changes what is claimed. Flag it instead.
- **Mathlib names drift between versions.** If a lemma name is wrong, fix the name;
  do not replace a real proof with `sorry` or `admit`.
- **A clean build is not a full check.** After `lake build`, audit axioms
  (`#print axioms`); `sorryAx` means an unfinished proof, `Lean.ofReduceBool` means
  `native_decide` was used (expected only in `keywordChecker`).
- **`demo.lean` contains intentionally false statements** for teaching. Never import
  it, and never cite it as a result.
- **The bridge certifies samples, not universal correctness.** `verify.lean`
  certifies `CorrectOn` on the declared samples only — not `Sound`/`Complete` over
  all prompts. Don't overstate it.
- **Claims must match reality.** "Proved" means Lean checked it with no `sorry`. If
  something hasn't built, say "written, not yet verified." Don't upgrade that.
