/-
  Theorem3.lean
  Theorem 3 of the draft: a GROWING attack surface X(1) ⊆ X(2) ⊆ ··· with union
  X(∞) countable, each attack x admitted at round a(x) and discoverable from then
  on with its own rate ε_x. With V_t the still-vulnerable set and D_t the defense:

    (10)  P(x ∉ D_t) ≤ (1-ε_x)^(t-a(x))          for t ≥ a(x)
    (11)  P( ∀ x∈X(∞) ∃T_x<∞ : ∀t≥T_x, x∈D_t ) = 1

  Corollary 4: each finite context level X(ℓ) is a.s. covered in full from some
  round onward.

  Modelling: the countable universe X(∞) is the type `X` (`[Countable X]`); the
  admission time a(x) is `P.admit x`. For Corollary 4 a context level is modelled
  by `level : X → ℕ` with `{x | level x ≤ ℓ}` finite — the paper's "each fixed
  context level contains only finitely many attacks".

  Contents:
    * theorem3     eqs. (10) and (11)
    * corollary4   finite context levels complete
-/
import Mathlib
import Garak.Survival
import Garak.Process

open MeasureTheory

namespace Garak

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Theorem 3.** Assumption 1 plus per-attack discoverability (Assumption 2 with
rate `ε x` from round `a(x)` on). Then the per-attack survival bound (10) and the
almost-sure eventual-coverage statement (11).

Part (10) is `survival_bound` per attack (its `a(x)`-shift is already built in).
Part (11) combines the per-attack null sets over the countable universe: each
`eventually_covered_ae` is an a.s. statement, and `ae_all_iff` (which needs
`[Countable X]`) intersects the countably many probability-one events. -/
theorem theorem3 [IsProbabilityMeasure μ] [Countable X] (P : Process Ω X μ) (ε : X → ℝ)
    (h0 : ∀ x, 0 < ε x) (h1 : ∀ x, ε x ≤ 1) (hdisc : Discoverable P ε) :
    (∀ x (n : ℕ), (μ ((P.cov (P.admit x + n) x)ᶜ)).toReal ≤ (1 - ε x) ^ n) ∧
    (∀ᵐ ω ∂μ, ∀ x, ∃ T : ℕ, ∀ t, T ≤ t → ω ∈ P.cov t x) := by
  refine ⟨fun x n => survival_bound P x (ε x) (h1 x) (hdisc x) n, ?_⟩
  exact ae_all_iff.mpr fun x => eventually_covered_ae P x (ε x) (h0 x) (h1 x) (hdisc x)

/-- **Corollary 4.** If each context level `{x | level x ≤ ℓ}` is finite, then
almost surely every level is eventually covered in full: for each `ℓ` there is a
finite `T` past which every attack of level `≤ ℓ` is covered.

Proof: work on the single probability-one event of (11). Along that realization
the covered sets grow monotonically (retention), and each level is finite, so
Proposition 1 (`exists_common_time`) gives one common time per level. -/
theorem corollary4 [IsProbabilityMeasure μ] [Countable X] (P : Process Ω X μ) (ε : X → ℝ)
    (h0 : ∀ x, 0 < ε x) (h1 : ∀ x, ε x ≤ 1) (hdisc : Discoverable P ε)
    (level : X → ℕ) (hfin : ∀ ℓ, {x | level x ≤ ℓ}.Finite) :
    ∀ᵐ ω ∂μ, ∀ ℓ : ℕ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ x, level x ≤ ℓ → ω ∈ P.cov t x := by
  have hev := (theorem3 P ε h0 h1 hdisc).2
  have hret : ∀ᵐ ω ∂μ, ∀ x t, ω ∈ P.cov t x → ω ∈ P.cov (t + 1) x :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr fun t => P.retention t x
  filter_upwards [hev, hret] with ω hω hr ℓ
  have hmono : Monotone (fun t => {x | ω ∈ P.cov t x}) :=
    monotone_nat_of_le_succ fun t x hx => hr x t hx
  obtain ⟨T, hT⟩ := exists_common_time (fun t => {x | ω ∈ P.cov t x}) hmono
    {x | level x ≤ ℓ} (hfin ℓ) (fun x _ => by
      obtain ⟨Tx, hTx⟩ := hω x
      exact ⟨Tx, hTx Tx le_rfl⟩)
  exact ⟨T, fun t ht x hx => hmono ht (hT x hx)⟩

end Garak
