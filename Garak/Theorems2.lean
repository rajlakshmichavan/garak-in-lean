/-
  Theorem2.lean
  Theorem 2 of the draft: a fixed finite attack surface, all attacks admitted at
  time 0, uniform discovery rate ε. With T = inf{t : V_t = ∅} and N = |X|:

    (a)  P(T > t) ≤ min{1, N(1-ε)ᵗ}       -- eq. (4)
    (b)  the whole surface is a.s. covered from some round onward
    (c)  ∑ₜ P(T > t) ≤ N/ε                 -- eq. (5)

  On eq. (5): the draft writes `E[T] ≤ min{1,N(1-ε)ᵗ} ≤ N/ε`, which has a stray `t`
  and no sum. The correct statement is `E[T] = ∑ₜ P(T>t) ≤ ∑ₜ N(1-ε)ᵗ = N/ε`; part
  (c) proves the `∑ₜ P(T>t) ≤ N/ε` half. `compTime_lt_top_ae` records `P(T<∞)=1`.

  Contents:
    * compTime             T as an ℕ∞-valued random variable
    * lt_compTime_subset   {T > t} ⊆ {some attack uncovered at t}
    * theorem2             parts (a), (b), (c)
    * compTime_lt_top_ae   P(T < ∞) = 1
-/
import Mathlib
import Garak.Survival
import Garak.Process

open MeasureTheory

namespace Garak

variable {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `T(ω) = inf {t | every attack is covered at round t}`, valued in `ℕ∞`
(`⊤` if it never happens). -/
noncomputable def compTime (P : Process Ω X μ) (ω : Ω) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : ∀ x, ω ∈ P.cov t x), (t : ℕ∞)

/-- `{T > t} ⊆ {some attack uncovered at round t}`: if everything is covered at
round `t`, then `T ≤ t`. The ≤-direction of the paper's `T > t ⟺ V_t ≠ ∅`, which
is all the tail bound needs. -/
theorem lt_compTime_subset (P : Process Ω X μ) (t : ℕ) :
    {ω | (t : ℕ∞) < compTime P ω} ⊆ ⋃ x, (P.cov t x)ᶜ := by
  intro ω hω
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hcon
  exact absurd hω (not_lt.mpr (iInf₂_le t hcon))

/-- **Theorem 2.** Finite surface, all attacks admitted at 0, uniform `ε ∈ (0,1]`. -/
theorem theorem2 [IsProbabilityMeasure μ] [Fintype X] (P : Process Ω X μ) (ε : ℝ)
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hadm : ∀ x, P.admit x = 0)
    (hdisc : Discoverable P (fun _ => ε)) :
    (∀ t : ℕ, (μ (⋃ x, (P.cov t x)ᶜ)).toReal
        ≤ min 1 ((Fintype.card X : ℝ) * (1 - ε) ^ t)) ∧
    (∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ t, T ≤ t → ∀ x, ω ∈ P.cov t x) ∧
    (∑' t : ℕ, μ {ω | (t : ℕ∞) < compTime P ω}
        ≤ ENNReal.ofReal ((Fintype.card X : ℝ) / ε)) := by
  -- per-attack survival, with a(x) = 0 folded in
  have hpoint : ∀ x (t : ℕ), (μ ((P.cov t x)ᶜ)).toReal ≤ (1 - ε) ^ t := by
    intro x t
    have hd : ∀ s, P.admit x ≤ s →
        ε * (μ ((P.cov s x)ᶜ)).toReal ≤ (μ ((P.cov s x)ᶜ ∩ P.rep s x)).toReal :=
      fun s _ => hdisc x s (by simp [hadm x])
    have := survival_bound P x ε h1 hd t
    simpa [hadm x] using this
  -- (a): union bound over the N attacks
  have ha : ∀ t : ℕ, (μ (⋃ x, (P.cov t x)ᶜ)).toReal
      ≤ min 1 ((Fintype.card X : ℝ) * (1 - ε) ^ t) := by
    intro t
    refine le_min ?_ ?_
    · have h := ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := μ) (s := ⋃ x, (P.cov t x)ᶜ))
      simpa using h
    · have hU : μ (⋃ x, (P.cov t x)ᶜ) ≤ ∑ x, μ ((P.cov t x)ᶜ) :=
        measure_iUnion_fintype_le μ _
      have hne : ∀ x ∈ (Finset.univ : Finset X), μ ((P.cov t x)ᶜ) ≠ ⊤ :=
        fun x _ => measure_ne_top μ _
      have hsum_ne : (∑ x, μ ((P.cov t x)ᶜ)) ≠ ⊤ := ENNReal.sum_ne_top.mpr hne
      calc (μ (⋃ x, (P.cov t x)ᶜ)).toReal
          ≤ (∑ x, μ ((P.cov t x)ᶜ)).toReal := ENNReal.toReal_mono hsum_ne hU
        _ = ∑ x, (μ ((P.cov t x)ᶜ)).toReal := by rw [ENNReal.toReal_sum hne]
        _ ≤ ∑ _x : X, (1 - ε) ^ t := Finset.sum_le_sum fun x _ => hpoint x t
        _ = (Fintype.card X : ℝ) * (1 - ε) ^ t := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨ha, ?_, ?_⟩
  · -- (b): each attack a.s. covered from some round on, then take the finite max
    have hev : ∀ x : X, ∀ᵐ ω ∂μ, ∃ T : ℕ, ∀ t, T ≤ t → ω ∈ P.cov t x := by
      intro x
      have hd : ∀ s, P.admit x ≤ s →
          ε * (μ ((P.cov s x)ᶜ)).toReal ≤ (μ ((P.cov s x)ᶜ ∩ P.rep s x)).toReal :=
        fun s _ => hdisc x s (by simp [hadm x])
      exact eventually_covered_ae P x ε h0 h1 hd
    filter_upwards [ae_all_iff.mpr hev] with ω hω
    exact exists_common_time_of_eventually (fun t x => ω ∈ P.cov t x) hω
  · -- (c): ∑ₜ P(T>t) ≤ ∑ₜ N(1-ε)ᵗ = N/ε
    have hN : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
    calc ∑' t : ℕ, μ {ω | (t : ℕ∞) < compTime P ω}
        ≤ ∑' t : ℕ, ENNReal.ofReal ((Fintype.card X : ℝ) * (1 - ε) ^ t) := by
          refine ENNReal.tsum_le_tsum fun t => ?_
          have hnn : 0 ≤ (Fintype.card X : ℝ) * (1 - ε) ^ t :=
            mul_nonneg hN (pow_nonneg (by linarith) t)
          calc μ {ω | (t : ℕ∞) < compTime P ω}
              ≤ μ (⋃ x, (P.cov t x)ᶜ) := measure_mono (lt_compTime_subset P t)
            _ ≤ ENNReal.ofReal ((Fintype.card X : ℝ) * (1 - ε) ^ t) :=
                (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hnn).mpr
                  ((ha t).trans (min_le_right _ _))
      _ = ENNReal.ofReal ((Fintype.card X : ℝ) / ε) := geom_tail_sum _ ε hN h0 h1

/-- `P(T < ∞) = 1`, stated on `compTime`. Immediate from part (b). -/
theorem compTime_lt_top_ae [IsProbabilityMeasure μ] [Fintype X] (P : Process Ω X μ) (ε : ℝ)
    (h0 : 0 < ε) (h1 : ε ≤ 1) (hadm : ∀ x, P.admit x = 0)
    (hdisc : Discoverable P (fun _ => ε)) :
    ∀ᵐ ω ∂μ, compTime P ω ≠ ⊤ := by
  filter_upwards [(theorem2 P ε h0 h1 hadm hdisc).2.1] with ω hω
  obtain ⟨T, hT⟩ := hω
  have hcov : ∀ x, ω ∈ P.cov T x := fun x => hT T le_rfl x
  have hle : compTime P ω ≤ (T : ℕ∞) := iInf₂_le T hcov
  exact ne_top_of_le_ne_top (by simp) hle

end Garak
