# `Proofs/` — the coverage theorems

Lean formalizations of the probabilistic coverage results of
*Defensive Sufficiency in a Stackelberg Model of AI Security* (Sections IV–V).
These are the mathematical core: when continued discovery and repair guarantee
coverage, and how long it takes.

All files use the `DefensiveSufficiency` namespace and share the model: covered
sets `D_t` measurable at `F_t`, discovered sets `Z_t` at `F_{t+1}`, conditional
probabilities written as conditional expectations of indicators. Each file builds
with no `sorry` and depends only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`) when compiled.

## Files

| File | Theorem | How the proof works |
| --- | --- | --- |
| `Theorem5.lean` | Theorem 5 — patch regions | The one-round survival bound `P(H_{i,t+1}) ≤ (1-η_i)·P(H_{i,t})` is built from region discoverability (12), region-wide remediation (13), and retention; a union bound over the regions gives the tail bound (14); summing the geometric tails gives `E[T] ≤ Σ_i 1/η_i` (15). |
| `Theorem2.lean` | Theorem 2 — finite surface | Proved as the singleton-region special case of Theorem 5 (`assumption3_singletons`), exactly as the paper remarks. Gives the tail bound (4), `P(T<∞)=1`, and `E[T] ≤ N/ε` (5). This is the one file that imports another (`Proofs.Theorem5`). |
| `Theorem3.lean` | Theorem 3 — growing surface | Self-contained (Mathlib only). Per-attack decay `P(x∉D_t) ≤ (1-ε_x)^{t-a(x)}` (10) by induction from the admission time; the survival probability vanishes, so "never covered" is null; countability of `X^(∞)` intersects these into one probability-one event (11). The level sequence `L_t` is assumed unbounded, which is what makes every admission time `a(x)` finite. |
| `Theorem7.lean` | Lemma 6 and Theorem 7 — time-varying rates | Lemma 6 telescopes the one-round bound to a product `∏(1-q_t)` and, via `1-u ≤ e^{-u}`, to an exponential that vanishes when `Σ q_t` diverges. Theorem 7 applies it at `B_t = {x∉D_t}`, building the one-round bound (16) from remediation, retention and the mixture bound (19); includes countable (`theorem7_countable`) and finite-surface (`theorem7_finite`) completion. |

## Modelling notes (what's assumed, and why)

- **Assumption 2 / discoverability** is taken in its integrated (conditional-
  expectation) form — the form the proofs use when the paper "takes expectations".
- **`q_t(x)` in Theorem 7** is a deterministic lower bound on the weighted
  discovery sum of (19). That is the reading that makes the product bound (20) a
  bound of a probability by a number. Deriving (19) itself from the mechanism-level
  `α_{k,t}` and `p_{k,t}` is not formalized — (19) is taken as a hypothesis, as the
  theorem states.
- **Theorem 3's unboundedness of `L_t`** is an explicit hypothesis here; the paper
  states the resulting finiteness of `a(x)` directly.
- **Corollary 4** (each finite context level completes) follows from Theorem 3 and
  the finite-maximum argument; noted in the paper, not separately formalized.