module

public import Mathlib

/-!
# Lemma 6 and Theorem 7: accumulating opportunities for repair

Formalization of Lemma 6 and Theorem 7 of *Defensive Sufficiency in a Stackelberg Model of AI
Security* (Section V.C, "Several discovery mechanisms").

Setting (Sections III and V of the paper):
* `(Ω, m0, P)` is a probability space and `ℱ` is a filtration (`ℱ t` = information right before
  round `t`).
* `Xs t : Set α` is the active attack surface `X_t` at round `t` (it may grow over time).
* `D t ω : Set α` is the covered set `D_t` and `Z t ω : Set α` the set `Z_t` of attacks discovered
  in round `t`; membership in `D t` is `ℱ t`-measurable and membership in `Z t` is
  `ℱ (t+1)`-measurable.
* `V_t = X_t \ D_t` is the residual vulnerable set (`activeResidual`).
* The discovery mechanisms are indexed by a finite type `κ`; `sel k t ω` is the selection
  probability `α_{k,t}` and `rep k t ω` the reporting lower bound `p_{k,t}(x)` for the fixed
  attack `x`.
* `P(· | ℱ_t)` of an event is written as the conditional expectation of its indicator.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace DefensiveSufficiency

variable {Ω α : Type*} {m0 : MeasurableSpace Ω}

/-! ## Lemma 6 -/

/-- One-step consequence of (16): `P(B_{t+1}) ≤ (1 - q_t) P(B_t)`. -/
lemma lemma6_step (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (B : ℕ → Set Ω) (q : ℕ → ℝ) (t : ℕ) (hmt : MeasurableSet (B t))
    (hm : MeasurableSet (B (t + 1)))
    (h16 : P[(B (t + 1)).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P]
      (B t).indicator (fun _ => 1 - q t)) :
    P.real (B (t + 1)) ≤ (1 - q t) * P.real (B t) := by
  calc P.real (B (t + 1)) = ∫ ω, (B (t + 1)).indicator (fun _ => (1 : ℝ)) ω ∂P := by
        rw [integral_indicator_const _ hm]; simp
    _ = ∫ ω, (P[(B (t + 1)).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂P :=
        (integral_condExp (ℱ.le t)).symm
    _ ≤ ∫ ω, (B t).indicator (fun _ => 1 - q t) ω ∂P :=
        integral_mono_ae integrable_condExp ((integrable_const _).indicator hmt) h16
    _ = (1 - q t) * P.real (B t) := by
        rw [integral_indicator_const _ hmt, smul_eq_mul, mul_comm]

/-- **Lemma 6.** Let `B_t ∈ ℱ_t` for `t ≥ a` and `q_t ∈ [0,1]` with
`P(B_{t+1} | ℱ_t) ≤ 1_{B_t} (1 - q_t)` (Eq. (16)). Then for `n ≥ a`,
`P(B_n) ≤ P(B_a) ∏_{t=a}^{n-1} (1 - q_t) ≤ P(B_a) exp(-∑_{t=a}^{n-1} q_t)` (Eq. (17)),
and if `∑_{t ≥ a} q_t = ∞` then `P(⋂_{n ≥ a} B_n) = 0`.

Differences from the paper's statement: the hypothesis `B_{t+1} ⊆ B_t` is not needed (it is
implied a.s. by (16)), and of `q_t ∈ [0,1]` only `q_t ≤ 1` is used. Measurability of `B_t` is
only required for `t ≥ a`. The divergence `∑_{t ≥ a} q_t = ∞` is expressed as the partial sums
`∑_{t=a}^{n-1} q_t` tending to `+∞`. -/
theorem lemma6 (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (B : ℕ → Set Ω) (q : ℕ → ℝ) (a : ℕ)
    (hB : ∀ t, a ≤ t → MeasurableSet[ℱ t] (B t))
    (hq1 : ∀ t, a ≤ t → q t ≤ 1)
    (h16 : ∀ t, a ≤ t → P[(B (t + 1)).indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P]
      (B t).indicator (fun _ => 1 - q t)) :
    (∀ n, a ≤ n →
      P.real (B n) ≤ P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t) ∧
      P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t) ≤
        P.real (B a) * Real.exp (-∑ t ∈ Finset.Ico a n, q t)) ∧
    (Tendsto (fun n => ∑ t ∈ Finset.Ico a n, q t) atTop atTop →
      P (⋂ n, ⋂ (_ : a ≤ n), B n) = 0) := by
  have hprod : ∀ n, a ≤ n →
      P.real (B n) ≤ P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hstep := lemma6_step P ℱ B q n (ℱ.le n _ (hB n hn)) (ℱ.le _ _ (hB (n + 1) (by omega)))
        (h16 n hn)
      have h0 : 0 ≤ 1 - q n := by linarith [hq1 n hn]
      calc P.real (B (n + 1)) ≤ (1 - q n) * P.real (B n) := hstep
        _ ≤ (1 - q n) * (P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t)) :=
            mul_le_mul_of_nonneg_left ih h0
        _ = P.real (B a) * ∏ t ∈ Finset.Ico a (n + 1), (1 - q t) := by
            rw [Finset.prod_Ico_succ_top hn]; ring
  have hexp : ∀ n, P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t) ≤
      P.real (B a) * Real.exp (-∑ t ∈ Finset.Ico a n, q t) := by
    intro n
    refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun t ht => ?_) (fun t _ => Real.one_sub_le_exp_neg (q t))
    have := hq1 t (Finset.mem_Ico.mp ht).1
    linarith
  refine ⟨fun n hn => ⟨hprod n hn, hexp n⟩, fun hdiv => ?_⟩
  have hlim : Tendsto (fun n => Real.exp (-∑ t ∈ Finset.Ico a n, q t)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  have hle : P.real (⋂ n, ⋂ (_ : a ≤ n), B n) ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop a] with n hn
    calc P.real (⋂ n, ⋂ (_ : a ≤ n), B n) ≤ P.real (B n) :=
          measureReal_mono (Set.iInter₂_subset n hn)
      _ ≤ P.real (B a) * Real.exp (-∑ t ∈ Finset.Ico a n, q t) := (hprod n hn).trans (hexp n)
      _ ≤ 1 * Real.exp (-∑ t ∈ Finset.Ico a n, q t) :=
          mul_le_mul_of_nonneg_right measureReal_le_one (Real.exp_pos _).le
      _ = Real.exp (-∑ t ∈ Finset.Ico a n, q t) := one_mul _
  exact (measureReal_eq_zero_iff).mp (le_antisymm hle measureReal_nonneg)

/-! ## Theorem 7 -/

/-- The residual vulnerable set `V_t = X_t \ D_t` for a (possibly growing) active surface. -/
def activeResidual (Xs : ℕ → Set α) (D : ℕ → Ω → Set α) (t : ℕ) (ω : Ω) : Set α :=
  Xs t \ D t ω

/-- The admission time `a(x) = min {t | x ∈ X_t}` of an attack (`0` if it is never admitted). -/
noncomputable def admissionTime (Xs : ℕ → Set α) (x : α) : ℕ :=
  sInf {t | x ∈ Xs t}

/-- **Assumption 1** for a (possibly growing) active surface, holding almost surely in every
round. (i) Effective remediation: `Z_t ∩ V_t ⊆ D_{t+1}`. (ii) Retention: `D_t ⊆ D_{t+1}`. -/
structure Assumption1' (P : Measure Ω) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α) : Prop where
  remediation : ∀ t, ∀ᵐ ω ∂P, Z t ω ∩ activeResidual Xs D t ω ⊆ D (t + 1) ω
  retention : ∀ t, ∀ᵐ ω ∂P, D t ω ⊆ D (t + 1) ω

/-- Eq. (19) for the attack `x` from round `a` on:
`P(x ∈ Z_t | ℱ_t) ≥ ∑_k α_{k,t} p_{k,t}(x)` on `{x ∈ V_t}`. -/
def Eq19 {κ : Type*} [Fintype κ] (P : Measure Ω) (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α)
    (D Z : ℕ → Ω → Set α) (sel rep : κ → ℕ → Ω → ℝ) (x : α) (a : ℕ) : Prop :=
  ∀ t, a ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω →
    ∑ k, sel k t ω * rep k t ω ≤ (P[{ω' | x ∈ Z t ω'}.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω

/-- The survival inequality (16) for `B_t = {x ∉ D_t}`, `t ≥ a`. -/
lemma survival_ineq {κ : Type*} [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α)
    (sel rep : κ → ℕ → Ω → ℝ) (q : ℕ → ℝ) (x : α) (a : ℕ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1' P Xs D Z) (hadm : ∀ t, a ≤ t → x ∈ Xs t)
    (h19 : Eq19 P ℱ Xs D Z sel rep x a)
    (hq : ∀ t, a ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω → q t ≤ ∑ k, sel k t ω * rep k t ω)
    (t : ℕ) (ht : a ≤ t) :
    P[{ω | x ∉ D (t + 1) ω}.indicator (fun _ => (1 : ℝ)) | ℱ t] ≤ᵐ[P]
      {ω | x ∉ D t ω}.indicator (fun _ => 1 - q t) := by
  classical
  set Bt : Set Ω := {ω | x ∉ D t ω} with hBtdef
  set Bt1 : Set Ω := {ω | x ∉ D (t + 1) ω} with hBt1def
  set Zx : Set Ω := {ω | x ∈ Z t ω} with hZxdef
  have hBtm : MeasurableSet[ℱ t] Bt := (hD t x).compl
  have hBt : MeasurableSet Bt := ℱ.le t _ hBtm
  have hZm : MeasurableSet Zx := ℱ.le _ _ (hZ t x)
  set f : Ω → ℝ := Bt.indicator (fun _ => (1 : ℝ)) with hfdef
  set g : Ω → ℝ := Zx.indicator (fun _ => (1 : ℝ)) with hgdef
  have hfint : Integrable f P := (integrable_const (1 : ℝ)).indicator hBt
  have hgint : Integrable g P := (integrable_const (1 : ℝ)).indicator hZm
  have hfsm : StronglyMeasurable[ℱ t] f :=
    (stronglyMeasurable_const.indicator hBtm)
  have hfgint : Integrable (f * g) P := by
    have : f * g = (Bt ∩ Zx).indicator (fun _ => (1 : ℝ)) := by
      ext ω; simp only [hfdef, hgdef, Pi.mul_apply, Set.indicator_apply, Set.mem_inter_iff]
      split_ifs <;> simp_all
    rw [this]; exact (integrable_const (1 : ℝ)).indicator (hBt.inter hZm)
  have h_ae : Bt1.indicator (fun _ => (1 : ℝ)) ≤ᵐ[P] f - f * g := by
    filter_upwards [h1.remediation t, h1.retention t] with ω hrem hret
    simp only [hfdef, hgdef, hBt1def, hBtdef, hZxdef, Pi.sub_apply, Pi.mul_apply,
      Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hB : x ∈ D t ω
    · have : x ∈ D (t + 1) ω := hret hB
      simp [hB, this]
    · by_cases hz : x ∈ Z t ω
      · have : x ∈ D (t + 1) ω := hrem ⟨hz, hadm t ht, hB⟩
        simp [hB, hz, this]
      · by_cases h' : x ∈ D (t + 1) ω <;> simp [hB, hz, h']
  have h_mono := condExp_mono (m := ℱ t) ((integrable_const (1 : ℝ)).indicator
    (ℱ.le _ _ (hD (t + 1) x).compl)) (hfint.sub hfgint) h_ae
  have h_sub := condExp_sub (m := ℱ t) hfint hfgint
  have h_f : P[f | ℱ t] = f := condExp_of_stronglyMeasurable (ℱ.le t) hfsm hfint
  have h_fg := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) hfsm hfgint hgint
  filter_upwards [h_mono, h_sub, h_fg, h19 t ht, hq t ht] with ω hm hs hfg h19ω hqω
  refine hm.trans ?_
  rw [hs, Pi.sub_apply, h_f, hfg, Pi.mul_apply]
  simp only [hfdef, Set.indicator_apply, hBtdef, Set.mem_setOf_eq]
  by_cases hB : x ∈ D t ω
  · simp [hB]
  · have hres : x ∈ activeResidual Xs D t ω := ⟨hadm t ht, hB⟩
    have := (hqω hres).trans (h19ω hres)
    simp only [hB, not_false_eq_true, if_true, one_mul]
    linarith

/-- **Theorem 7** (for an attack that is active from round `a` on). Suppose Assumption 1 holds,
the discovery probability for `x` satisfies (19) and `q_t ≤ 1` is a lower bound for the
right-hand side of (19) on `{x ∈ V_t}` (non-negativity of `q_t` is not needed). Then for `n ≥ a`,
`P(x ∉ D_n) ≤ ∏_{t=a}^{n-1} (1 - q_t)` (Eq. (20)), and `∑_{t ≥ a} q_t = ∞` implies that `x` is
almost surely eventually permanently covered. -/
theorem theorem7_of_active {κ : Type*} [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α)
    (sel rep : κ → ℕ → Ω → ℝ) (q : ℕ → ℝ) (x : α) (a : ℕ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1' P Xs D Z) (hadm : ∀ t, a ≤ t → x ∈ Xs t)
    (h19 : Eq19 P ℱ Xs D Z sel rep x a)
    (hq1 : ∀ t, a ≤ t → q t ≤ 1)
    (hq : ∀ t, a ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω → q t ≤ ∑ k, sel k t ω * rep k t ω) :
    (∀ n, a ≤ n → P.real {ω | x ∉ D n ω} ≤ ∏ t ∈ Finset.Ico a n, (1 - q t)) ∧
    (Tendsto (fun n => ∑ t ∈ Finset.Ico a n, q t) atTop atTop →
      ∀ᵐ ω ∂P, ∃ T, ∀ t, T ≤ t → x ∈ D t ω) := by
  set B : ℕ → Set Ω := fun t => {ω | x ∉ D t ω} with hBdef
  have L := lemma6 P ℱ B q a (fun t _ => (hD t x).compl) hq1
    (fun t ht => survival_ineq P ℱ Xs D Z sel rep q x a hD hZ h1 hadm h19 hq t ht)
  refine ⟨fun n hn => ?_, fun hdiv => ?_⟩
  · have hprod : 0 ≤ ∏ t ∈ Finset.Ico a n, (1 - q t) :=
      Finset.prod_nonneg fun t ht => by linarith [hq1 t (Finset.mem_Ico.mp ht).1]
    calc P.real {ω | x ∉ D n ω} ≤ P.real (B a) * ∏ t ∈ Finset.Ico a n, (1 - q t) := (L.1 n hn).1
      _ ≤ 1 * ∏ t ∈ Finset.Ico a n, (1 - q t) :=
          mul_le_mul_of_nonneg_right measureReal_le_one hprod
      _ = ∏ t ∈ Finset.Ico a n, (1 - q t) := one_mul _
  · have hnull := L.2 hdiv
    have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n, ⋂ (_ : a ≤ n), B n := measure_eq_zero_iff_ae_notMem.mp hnull
    have hret : ∀ᵐ ω ∂P, ∀ t, D t ω ⊆ D (t + 1) ω := ae_all_iff.mpr h1.retention
    filter_upwards [hae, hret] with ω hω hr
    simp only [Set.mem_iInter, not_forall, hBdef, Set.mem_setOf_eq, not_not] at hω
    obtain ⟨n, -, hn⟩ := hω
    refine ⟨n, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base => exact hn
    | succ t _ ih => exact hr t ih

/-- **Theorem 7.** Let the active surfaces `X_t` be nondecreasing and let `x` be admitted at some
round, with admission time `a(x)`. Suppose Assumption 1 holds, the discovery probability for `x`
satisfies (19), and `q_t(x) ≤ 1` is a lower bound for the right-hand side of (19) on
`{x ∈ V_t}` (non-negativity of `q_t(x)` is not needed). Then for `n ≥ a(x)`, `P(x ∉ D_n) ≤ ∏_{t=a(x)}^{n-1} (1 - q_t(x))` (Eq. (20)), and
`∑_{t ≥ a(x)} q_t(x) = ∞` implies eventual permanent coverage of `x` almost surely. -/
theorem theorem7 {κ : Type*} [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α)
    (sel rep : κ → ℕ → Ω → ℝ) (q : ℕ → ℝ) (x : α)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (hXs : Monotone Xs) (hx : ∃ t, x ∈ Xs t)
    (h1 : Assumption1' P Xs D Z)
    (h19 : Eq19 P ℱ Xs D Z sel rep x (admissionTime Xs x))
    (hq1 : ∀ t, admissionTime Xs x ≤ t → q t ≤ 1)
    (hq : ∀ t, admissionTime Xs x ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω →
      q t ≤ ∑ k, sel k t ω * rep k t ω) :
    (∀ n, admissionTime Xs x ≤ n →
      P.real {ω | x ∉ D n ω} ≤ ∏ t ∈ Finset.Ico (admissionTime Xs x) n, (1 - q t)) ∧
    (Tendsto (fun n => ∑ t ∈ Finset.Ico (admissionTime Xs x) n, q t) atTop atTop →
      ∀ᵐ ω ∂P, ∃ T, ∀ t, T ≤ t → x ∈ D t ω) := by
  have hadm : ∀ t, admissionTime Xs x ≤ t → x ∈ Xs t := fun t ht =>
    hXs ht (Nat.sInf_mem hx)
  exact theorem7_of_active P ℱ Xs D Z sel rep q x _ hD hZ h1 hadm h19 hq1 hq

/-- **Theorem 7, countable surface.** If every attack `x` of a countable set `S` (e.g. the
countable union `X^(∞)` of finite surfaces) is active from round `a x` on and satisfies the
hypotheses of Theorem 7 with a divergent `∑_{t ≥ a x} q_t(x)`, then almost surely every
`x ∈ S` is eventually permanently covered (on one common probability-one event). -/
theorem theorem7_countable {κ : Type*} [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α)
    (sel : κ → ℕ → Ω → ℝ) (rep : α → κ → ℕ → Ω → ℝ) (q : α → ℕ → ℝ) (a : α → ℕ)
    (S : Set α) (hS : S.Countable)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1' P Xs D Z) (hadm : ∀ x ∈ S, ∀ t, a x ≤ t → x ∈ Xs t)
    (h19 : ∀ x ∈ S, Eq19 P ℱ Xs D Z sel (rep x) x (a x))
    (hq1 : ∀ x ∈ S, ∀ t, a x ≤ t → q x t ≤ 1)
    (hq : ∀ x ∈ S, ∀ t, a x ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω →
      q x t ≤ ∑ k, sel k t ω * rep x k t ω)
    (hdiv : ∀ x ∈ S, Tendsto (fun n => ∑ t ∈ Finset.Ico (a x) n, q x t) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ x ∈ S, ∃ T, ∀ t, T ≤ t → x ∈ D t ω := by
  rw [ae_ball_iff hS]
  intro x hx
  exact (theorem7_of_active P ℱ Xs D Z sel (rep x) (q x) x (a x) hD hZ h1 (hadm x hx) (h19 x hx)
    (hq1 x hx) (hq x hx)).2 (hdiv x hx)

/-- **Theorem 7, finite surface.** Under the hypotheses of `theorem7_countable` for a finite
set `S` of attacks, almost surely there is a finite round `T` with `S ⊆ D_t` for all `t ≥ T`
(finite-time completion of the whole surface). -/
theorem theorem7_finite {κ : Type*} [Fintype κ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xs : ℕ → Set α) (D Z : ℕ → Ω → Set α)
    (sel : κ → ℕ → Ω → ℝ) (rep : α → κ → ℕ → Ω → ℝ) (q : α → ℕ → ℝ) (a : α → ℕ)
    (S : Finset α)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1' P Xs D Z) (hadm : ∀ x ∈ S, ∀ t, a x ≤ t → x ∈ Xs t)
    (h19 : ∀ x ∈ S, Eq19 P ℱ Xs D Z sel (rep x) x (a x))
    (hq1 : ∀ x ∈ S, ∀ t, a x ≤ t → q x t ≤ 1)
    (hq : ∀ x ∈ S, ∀ t, a x ≤ t → ∀ᵐ ω ∂P, x ∈ activeResidual Xs D t ω →
      q x t ≤ ∑ k, sel k t ω * rep x k t ω)
    (hdiv : ∀ x ∈ S, Tendsto (fun n => ∑ t ∈ Finset.Ico (a x) n, q x t) atTop atTop) :
    ∀ᵐ ω ∂P, ∃ T, ∀ t, T ≤ t → (S : Set α) ⊆ D t ω := by
  filter_upwards [theorem7_countable P ℱ Xs D Z sel rep q a (S : Set α) S.countable_toSet hD hZ
    h1 hadm h19 hq1 hq hdiv] with ω hω
  choose T hT using hω
  refine ⟨S.attach.sup fun x => T x.1 x.2, fun t ht x hx => hT x hx t ?_⟩
  exact le_trans (Finset.le_sup (f := fun x : S => T x.1 x.2) (Finset.mem_attach S ⟨x, hx⟩)) ht

end DefensiveSufficiency
