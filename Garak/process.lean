import Mathlib
import Garak.Survival

/-!
# Feedback / Process  (probabilistic backbone, shared by Theorems 2 and 3)

The testing-and-repair process, reduced to exactly the events the proofs use.

Modelling dictionary (draft symbol ↦ Lean):
* `x ∈ D_t`  (x covered at round t)                     ↦ event `cov t x`
* `x ∈ V_t = {x} \ D_t`  (x still vulnerable, i.e. `B_t(x)`) ↦ event `(cov t x)ᶜ`
* `Z_t = x`  (x is the attack reported in round t)      ↦ event `rep t x`
* admission time `a(x)`                                 ↦ `admit x`

Assumption 1 lives in the `Process` structure (retention + effective remediation).
Assumption 2 is `Discoverable` below, in the INTEGRATED form the proof actually
uses; `discoverable_of_condexp` records how it follows from the draft's
conditional statement (that step is the one `sorry` here, and Theorem 2 does NOT
depend on it — it takes `Discoverable` as a hypothesis).
-/

open MeasureTheory

namespace Garak.Feedback

/-- A testing-and-repair process on a probability space, carrying Assumption 1. -/
structure Process (Ω : Type*) [MeasurableSpace Ω] (X : Type*) (μ : Measure Ω) where
  admit : X → ℕ
  cov : ℕ → X → Set Ω
  rep : ℕ → X → Set Ω
  cov_meas : ∀ t x, MeasurableSet (cov t x)
  rep_meas : ∀ t x, MeasurableSet (rep t x)
  /-- Assumption 1(ii), retention: covered stays covered. -/
  retention : ∀ t x, ∀ᵐ ω ∂μ, ω ∈ cov t x → ω ∈ cov (t + 1) x
  /-- Assumption 1(i), effective remediation: an active, still-uncovered attack
  that is reported is covered by the next round. -/
  remediation : ∀ t x, admit x ≤ t →
    ∀ᵐ ω ∂μ, ω ∉ cov t x → ω ∈ rep t x → ω ∈ cov (t + 1) x

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Assumption 2, integrated form (what averaging (6) over histories gives):
from its admission time on, an uncovered attack is reported with prob ≥ `ε x`. -/
def Discoverable (P : Process Ω X μ) (ε : X → ℝ) : Prop :=
  ∀ x t, P.admit x ≤ t →
    ε x * (μ ((P.cov t x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal

/-- **One round** — the paper's (6), after averaging.
`P(x uncovered at t+1) ≤ (1-ε) · P(x uncovered at t)`.

The heart of the argument, and it is where BOTH halves of Assumption 1 are used:
almost surely `{uncovered at t+1} ⊆ {uncovered at t} \ {reported at t}`, because
retention gives "uncovered later ⇒ uncovered now" and remediation gives "reported
while uncovered ⇒ covered next round". Then split the measure on `{reported}` and
apply discoverability. No `sorry`. -/
theorem survival_step [IsProbabilityMeasure μ] (P : Process Ω X μ) (x : X) (ε : ℝ) (t : ℕ)
    (ht : P.admit x ≤ t)
    (hdisc : ε * (μ ((P.cov t x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal) :
    (μ ((P.cov (t + 1) x)ᶜ)).toReal ≤ (1 - ε) * (μ ((P.cov t x)ᶜ)).toReal := by
  have hR : MeasurableSet (P.rep t x) := P.rep_meas t x
  have hae : ∀ᵐ ω ∂μ, ω ∈ (P.cov (t + 1) x)ᶜ → ω ∈ (P.cov t x)ᶜ \ P.rep t x := by
    filter_upwards [P.retention t x, P.remediation t x ht] with ω hret hrem hω
    have h1 : ω ∉ P.cov t x := fun hc => hω (hret hc)
    have h2 : ω ∉ P.rep t x := fun hr => hω (hrem h1 hr)
    exact ⟨h1, h2⟩
  have hmono : μ ((P.cov (t + 1) x)ᶜ) ≤ μ ((P.cov t x)ᶜ \ P.rep t x) := measure_mono_ae hae
  have hsplit : μ ((P.cov t x)ᶜ ∩ P.rep t x) + μ ((P.cov t x)ᶜ \ P.rep t x)
      = μ ((P.cov t x)ᶜ) := measure_inter_add_diff _ hR
  have hreal : (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal + (μ ((P.cov t x)ᶜ \ P.rep t x)).toReal
      = (μ ((P.cov t x)ᶜ)).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hsplit]
  have hle : (μ ((P.cov (t + 1) x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ \ P.rep t x)).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) hmono
  nlinarith [hle, hsplit, hreal, hdisc]

/-- **Per-attack survival** — the paper's `P(x ∈ V_t) ≤ (1-ε)^t` (and (10) with the
`a(x)` shift). Just `geom_bound` applied to `survival_step`, started from
`P(uncovered at a(x)) ≤ 1`. Conditional probabilities live inside `survival_step`,
so successive rounds need not be independent. No `sorry`. -/
theorem survival_bound [IsProbabilityMeasure μ] (P : Process Ω X μ) (x : X) (ε : ℝ)
    (hε1 : ε ≤ 1)
    (hdisc : ∀ t, P.admit x ≤ t →
      ε * (μ ((P.cov t x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal) :
    ∀ n : ℕ, (μ ((P.cov (P.admit x + n) x)ᶜ)).toReal ≤ (1 - ε) ^ n := by
  intro n
  have hc : 0 ≤ 1 - ε := by linarith
  have hstep : ∀ t, P.admit x ≤ t →
      (μ ((P.cov (t + 1) x)ᶜ)).toReal ≤ (1 - ε) * (μ ((P.cov t x)ᶜ)).toReal :=
    fun t ht => survival_step P x ε t ht (hdisc t ht)
  have h := geom_bound (fun t => (μ ((P.cov t x)ᶜ)).toReal) (1 - ε) hc (P.admit x) hstep n
  have hp : (μ ((P.cov (P.admit x) x)ᶜ)).toReal ≤ 1 := by
    have h1 := ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := μ) (s := (P.cov (P.admit x) x)ᶜ))
    simpa using h1
  calc (μ ((P.cov (P.admit x + n) x)ᶜ)).toReal
      ≤ (1 - ε) ^ n * (μ ((P.cov (P.admit x) x)ᶜ)).toReal := h
    _ ≤ (1 - ε) ^ n * 1 := mul_le_mul_of_nonneg_left hp (pow_nonneg hc n)
    _ = (1 - ε) ^ n := by ring

/-- The survival probability decays to 0, so an attack with a persistent positive
discovery rate is "never covered" only on a null set. No `sorry`. -/
theorem never_covered_null [IsProbabilityMeasure μ] (P : Process Ω X μ) (x : X) (ε : ℝ)
    (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hdisc : ∀ t, P.admit x ≤ t →
      ε * (μ ((P.cov t x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal) :
    μ (⋂ t, (P.cov t x)ᶜ) = 0 := by
  have hb := survival_bound P x ε h1 hdisc
  have hlim : Filter.Tendsto (fun n : ℕ => (1 - ε) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hle : ∀ n : ℕ, (μ (⋂ t, (P.cov t x)ᶜ)).toReal ≤ (1 - ε) ^ n := by
    intro n
    have hsub : (⋂ t, (P.cov t x)ᶜ) ⊆ (P.cov (P.admit x + n) x)ᶜ :=
      Set.iInter_subset (fun t => (P.cov t x)ᶜ) (P.admit x + n)
    exact le_trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)) (hb n)
  have hzero : (μ (⋂ t, (P.cov t x)ᶜ)).toReal ≤ 0 := ge_of_tendsto' hlim hle
  have heq : (μ (⋂ t, (P.cov t x)ᶜ)).toReal = 0 := le_antisymm hzero ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp heq with h | h
  · exact h
  · exact absurd h (measure_ne_top μ _)

/-- Almost surely, `x` is covered from SOME round on (not merely at some round) —
this is where retention upgrades "covered once" to "covered forever after". No
`sorry`. -/
theorem eventually_covered_ae [IsProbabilityMeasure μ] (P : Process Ω X μ) (x : X) (ε : ℝ)
    (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hdisc : ∀ t, P.admit x ≤ t →
      ε * (μ ((P.cov t x)ᶜ)).toReal ≤ (μ ((P.cov t x)ᶜ ∩ P.rep t x)).toReal) :
    ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ t, T ≤ t → ω ∈ P.cov t x := by
  have hnull := never_covered_null P x ε h0 h1 hdisc
  have hret : ∀ᵐ ω ∂μ, ∀ t, ω ∈ P.cov t x → ω ∈ P.cov (t + 1) x :=
    ae_all_iff.mpr (fun t => P.retention t x)
  filter_upwards [hret, compl_mem_ae_iff.mpr hnull] with ω hr hn
  simp only [Set.mem_compl_iff, Set.mem_iInter, not_forall, not_not] at hn
  obtain ⟨t0, ht0⟩ := hn
  refine ⟨t0, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact ht0
  | succ t _ ih => exact hr t ih

/-- OPTIONAL bridge (the one `sorry` in this file; Theorem 2 does not use it).
From the draft's conditional Assumption 2, `P(Z_t=x | F_t) ≥ ε` on `{x ∈ V_t}`,
to the integrated `Discoverable`. Proof is the tower property: with
`B = (cov t x)ᶜ ∈ F_t`,
  `ε·μ(B) = ∫_B ε ≤ ∫_B E[1_rep | F_t] = ∫_B 1_rep = μ(B ∩ rep)`,
the middle equality being `setIntegral_condExp`. Sorried only because I can't
check Mathlib's conditional-expectation lemma names offline. -/
theorem discoverable_of_condexp [IsProbabilityMeasure μ] (P : Process Ω X μ)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (ε : X → ℝ)
    (hadapt : ∀ t x, MeasurableSet[ℱ t] (P.cov t x))
    (hcond : ∀ t x, P.admit x ≤ t → ∀ᵐ ω ∂μ, ω ∉ P.cov t x →
      ε x ≤ (μ[(P.rep t x).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω) :
    Discoverable P ε := by
  sorry

end Garak.Feedback
