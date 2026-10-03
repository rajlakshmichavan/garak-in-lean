module

public import Mathlib

/-!
# Theorem 3: complete coverage under growing contexts

Self-contained formalization of Theorem 3 of *Defensive Sufficiency in a Stackelberg Model of AI
Security* (Section V.A, "Complete coverage"). This file depends only on Mathlib.

Setting (Sections III and V.A of the paper):
* `(Ω, m0, P)` is a probability space and `ℱ` is a filtration (`ℱ t` = information right before
  round `t`).
* `Xl ℓ : Set α` is the finite attack surface `X^(ℓ)` at context level `ℓ`; the levels are
  nondecreasing, `X^(1) ⊆ X^(2) ⊆ ⋯`.
* `L : ℕ → ℕ` is a nondecreasing, unbounded sequence of context levels, and the active surface at
  round `t` is `X_t = X^(L_t)` (`surface`).
* `X^(∞) = ⋃_ℓ X^(ℓ)` (`attackUniverse`), and `a(x) = min {t | x ∈ X_t}` is the admission time
  (`admissionTime`).
* `D t ω : Set α` is the covered set `D_t` and `Z t ω : Set α` the set `Z_t` of attacks discovered
  in round `t`; membership in `D t` is `ℱ t`-measurable and membership in `Z t` is
  `ℱ (t+1)`-measurable.
* `V_t = X_t \ D_t` is the residual vulnerable set (`vulnerable`).
* A conditional probability `P(A | ℱ_t)` is written as the conditional expectation of the
  indicator of `A`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace DefensiveSufficiency.GrowingContext

variable {Ω α : Type*} {m0 : MeasurableSpace Ω}

/-- The active surface at round `t`: `X_t = X^(L_t)`. -/
def surface (Xl : ℕ → Set α) (L : ℕ → ℕ) (t : ℕ) : Set α := Xl (L t)

/-- The universe of admissible attacks `X^(∞) = ⋃_ℓ X^(ℓ)`. -/
def attackUniverse (Xl : ℕ → Set α) : Set α := ⋃ ℓ, Xl ℓ

/-- The admission time `a(x) = min {t | x ∈ X_t}` (Eq. (8)); it is `0` if `x` is never admitted. -/
noncomputable def admissionTime (Xl : ℕ → Set α) (L : ℕ → ℕ) (x : α) : ℕ :=
  sInf {t | x ∈ surface Xl L t}

/-- The residual vulnerable set `V_t = X_t \ D_t` (Eq. (1)). -/
def vulnerable (Xl : ℕ → Set α) (L : ℕ → ℕ) (D : ℕ → Ω → Set α) (t : ℕ) (ω : Ω) : Set α :=
  surface Xl L t \ D t ω

/-- **Assumption 1**, holding almost surely in every round.
(i) Effective remediation: `Z_t ∩ V_t ⊆ D_{t+1}`. (ii) Retention: `D_t ⊆ D_{t+1}`. -/
structure Assumption1 (P : Measure Ω) (Xl : ℕ → Set α) (L : ℕ → ℕ) (D Z : ℕ → Ω → Set α) :
    Prop where
  remediation : ∀ t, ∀ᵐ ω ∂P, Z t ω ∩ vulnerable Xl L D t ω ⊆ D (t + 1) ω
  retention : ∀ t, ∀ᵐ ω ∂P, D t ω ⊆ D (t + 1) ω

/-- **Discoverability** (Eq. (9)) of the attack `x` with rate `ε ∈ (0,1]`:
`P(x ∈ Z_t | ℱ_t) ≥ ε` on `{x ∈ V_t}` for every `t ≥ a(x)`. -/
structure Discoverable (P : Measure Ω) (ℱ : Filtration ℕ m0) (Xl : ℕ → Set α) (L : ℕ → ℕ)
    (D Z : ℕ → Ω → Set α) (x : α) (ε : ℝ) : Prop where
  pos : 0 < ε
  le_one : ε ≤ 1
  bound : ∀ t, admissionTime Xl L x ≤ t → ∀ᵐ ω ∂P, x ∈ vulnerable Xl L D t ω →
    ε ≤ (P[{ω' | x ∈ Z t ω'}.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω

/-! ## Elementary facts about the surfaces -/

lemma surface_mono {Xl : ℕ → Set α} {L : ℕ → ℕ} (hXl : Monotone Xl) (hL : Monotone L) :
    Monotone (surface Xl L) :=
  fun _ _ h => hXl (hL h)

/-- Every attack of `X^(∞)` is admitted at some round, since the levels `L_t` are unbounded. -/
lemma exists_mem_surface {Xl : ℕ → Set α} {L : ℕ → ℕ} (hXl : Monotone Xl)
    (hLu : ∀ ℓ, ∃ t, ℓ ≤ L t) {x : α} (hx : x ∈ attackUniverse Xl) : ∃ t, x ∈ surface Xl L t := by
  obtain ⟨ℓ, hℓ⟩ := Set.mem_iUnion.mp hx
  obtain ⟨t, ht⟩ := hLu ℓ
  exact ⟨t, hXl ht hℓ⟩

/-- Once admitted, an attack stays active: `x ∈ X_t` for all `t ≥ a(x)`. -/
lemma mem_surface_of_admissionTime_le {Xl : ℕ → Set α} {L : ℕ → ℕ} (hXl : Monotone Xl)
    (hL : Monotone L) (hLu : ∀ ℓ, ∃ t, ℓ ≤ L t) {x : α} (hx : x ∈ attackUniverse Xl) {t : ℕ}
    (ht : admissionTime Xl L x ≤ t) : x ∈ surface Xl L t :=
  surface_mono hXl hL ht (Nat.sInf_mem (exists_mem_surface hXl hLu hx))

/-- `X^(∞)` is countable, being a countable union of finite sets. -/
lemma attackUniverse_countable {Xl : ℕ → Set α} (hfin : ∀ ℓ, (Xl ℓ).Finite) :
    (attackUniverse Xl).Countable :=
  Set.countable_iUnion fun ℓ => (hfin ℓ).countable

/-! ## One round of the survival argument -/

/-- One round: if `x` is active at round `t`, then `P(x ∉ D_{t+1}) ≤ (1 - ε) P(x ∉ D_t)`. -/
lemma survival_step (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Xl : ℕ → Set α) (L : ℕ → ℕ) (D Z : ℕ → Ω → Set α)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P Xl L D Z) (x : α) (ε : ℝ) (t : ℕ) (hxt : x ∈ surface Xl L t)
    (hdisc : ∀ᵐ ω ∂P, x ∈ vulnerable Xl L D t ω →
      ε ≤ (P[{ω' | x ∈ Z t ω'}.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω) :
    P.real {ω | x ∉ D (t + 1) ω} ≤ (1 - ε) * P.real {ω | x ∉ D t ω} := by
  set B : Set Ω := {ω | x ∉ D t ω} with hBdef
  set Zx : Set Ω := {ω | x ∈ Z t ω} with hZxdef
  have hBt : MeasurableSet[ℱ t] B := (hD t x).compl
  have hB : MeasurableSet B := ℱ.le t _ hBt
  have hZm : MeasurableSet Zx := ℱ.le _ _ (hZ t x)
  -- Survival requires surviving now and not being discovered in this round.
  have hsub : {ω | x ∉ D (t + 1) ω} ≤ᵐ[P] (B \ Zx : Set Ω) := by
    filter_upwards [h1.remediation t, h1.retention t] with ω hrem hret
    intro hω
    refine ⟨fun hD' => hω (hret hD'), fun hz => hω (hrem ⟨hz, hxt, ?_⟩)⟩
    intro hD'
    exact hω (hret hD')
  -- The probability of being discovered while vulnerable is at least `ε P(B)`.
  have hint : ε * P.real B ≤ P.real (B ∩ Zx) := by
    have h_ind : Integrable (Zx.indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const (1 : ℝ)).indicator hZm
    calc ε * P.real B = ∫ _ in B, ε ∂P := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in B, (P[Zx.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂P := by
          refine setIntegral_mono_ae_restrict integrableOn_const integrable_condExp.integrableOn ?_
          rw [EventuallyLE, ae_restrict_iff' hB]
          filter_upwards [hdisc] with ω hω hωB
          exact hω ⟨hxt, hωB⟩
      _ = ∫ ω in B, Zx.indicator (fun _ => (1 : ℝ)) ω ∂P :=
          setIntegral_condExp (ℱ.le t) h_ind hBt
      _ = P.real (B ∩ Zx) := by
          rw [integral_indicator_const _ hZm, smul_eq_mul, mul_one,
            measureReal_restrict_apply hZm, Set.inter_comm]
  calc P.real {ω | x ∉ D (t + 1) ω} ≤ P.real (B \ Zx) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
    _ = P.real B - P.real (B ∩ Zx) := by
        rw [← measureReal_inter_add_diff (s := B) hZm]; ring
    _ ≤ (1 - ε) * P.real B := by linarith

/-! ## Theorem 3 -/

/-- **Theorem 3, Eq. (10).** Under Assumption 1, if `x ∈ X^(∞)` is discoverable with rate `ε`,
then `P(x ∉ D_t) ≤ (1 - ε)^(t - a(x))` for every `t ≥ a(x)`. -/
theorem theorem3_survival (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Xl : ℕ → Set α) (L : ℕ → ℕ) (D Z : ℕ → Ω → Set α)
    (hXl : Monotone Xl) (hL : Monotone L) (hLu : ∀ ℓ, ∃ t, ℓ ≤ L t)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P Xl L D Z) (x : α) (hx : x ∈ attackUniverse Xl) (ε : ℝ)
    (hε : Discoverable P ℱ Xl L D Z x ε) (t : ℕ) (ht : admissionTime Xl L x ≤ t) :
    P.real {ω | x ∉ D t ω} ≤ (1 - ε) ^ (t - admissionTime Xl L x) := by
  induction t, ht using Nat.le_induction with
  | base => simp [measureReal_le_one]
  | succ n hn ih =>
    have hstep := survival_step P ℱ Xl L D Z hD hZ h1 x ε n
      (mem_surface_of_admissionTime_le hXl hL hLu hx hn) (hε.bound n hn)
    have h0 : 0 ≤ 1 - ε := by linarith [hε.le_one]
    calc P.real {ω | x ∉ D (n + 1) ω} ≤ (1 - ε) * P.real {ω | x ∉ D n ω} := hstep
      _ ≤ (1 - ε) * (1 - ε) ^ (n - admissionTime Xl L x) := mul_le_mul_of_nonneg_left ih h0
      _ = (1 - ε) ^ (n + 1 - admissionTime Xl L x) := by
        rw [← pow_succ', Nat.sub_add_comm hn]

/-- A single discoverable attack of `X^(∞)` is almost surely eventually permanently covered. -/
theorem theorem3_eventually_covered (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (Xl : ℕ → Set α) (L : ℕ → ℕ) (D Z : ℕ → Ω → Set α)
    (hXl : Monotone Xl) (hL : Monotone L) (hLu : ∀ ℓ, ∃ t, ℓ ≤ L t)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P Xl L D Z) (x : α) (hx : x ∈ attackUniverse Xl) (ε : ℝ)
    (hε : Discoverable P ℱ Xl L D Z x ε) :
    ∀ᵐ ω ∂P, ∃ T, ∀ t, T ≤ t → x ∈ D t ω := by
  set a := admissionTime Xl L x
  -- The event that `x` is never covered from round `a` on has probability zero.
  have hnull : P (⋂ n, ⋂ (_ : a ≤ n), {ω | x ∉ D n ω}) = 0 := by
    have h0 : 0 ≤ 1 - ε := by linarith [hε.le_one]
    have h1' : 1 - ε < 1 := by linarith [hε.pos]
    have hlim : Tendsto (fun n => (1 - ε) ^ (n - a)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1').comp (tendsto_sub_atTop_nat a)
    have hle : P.real (⋂ n, ⋂ (_ : a ≤ n), {ω | x ∉ D n ω}) ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop a] with n hn
      exact (measureReal_mono (Set.iInter₂_subset n hn)).trans
        (theorem3_survival P ℱ Xl L D Z hXl hL hLu hD hZ h1 x hx ε hε n hn)
    exact (measureReal_eq_zero_iff).mp (le_antisymm hle measureReal_nonneg)
  have hae := measure_eq_zero_iff_ae_notMem.mp hnull
  have hret : ∀ᵐ ω ∂P, ∀ t, D t ω ⊆ D (t + 1) ω := ae_all_iff.mpr h1.retention
  filter_upwards [hae, hret] with ω hω hr
  simp only [Set.mem_iInter, not_forall, Set.mem_setOf_eq, not_not] at hω
  obtain ⟨n, -, hn⟩ := hω
  -- Retention makes coverage permanent once it occurs.
  refine ⟨n, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact hn
  | succ t _ ih => exact hr t ih

/-- **Theorem 3.** Let `X^(1) ⊆ X^(2) ⊆ ⋯` be finite attack surfaces and `L_t` a nondecreasing,
unbounded sequence of levels, with active surfaces `X_t = X^(L_t)`. Suppose Assumption 1 holds and
every `x ∈ X^(∞)` is discoverable with a rate `ε_x ∈ (0,1]` (Eq. (9)). Then
* (Eq. (10)) for every `x ∈ X^(∞)` and `t ≥ a(x)`, `P(x ∉ D_t) ≤ (1 - ε_x)^(t - a(x))`;
* (Eq. (11)) almost surely, every `x ∈ X^(∞)` has a finite `T_x` with `x ∈ D_t` for all
  `t ≥ T_x`;
* equivalently, `X^(∞) ⊆ ⋃_t D_t` almost surely;
* with equality `⋃_t D_t = X^(∞)` almost surely if the defended sets lie in `X^(∞)`. -/
theorem theorem3 (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (Xl : ℕ → Set α) (L : ℕ → ℕ) (D Z : ℕ → Ω → Set α)
    (hfin : ∀ ℓ, (Xl ℓ).Finite) (hXl : Monotone Xl) (hL : Monotone L)
    (hLu : ∀ ℓ, ∃ t, ℓ ≤ L t)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P Xl L D Z) (ε : α → ℝ)
    (hε : ∀ x ∈ attackUniverse Xl, Discoverable P ℱ Xl L D Z x (ε x)) :
    (∀ x ∈ attackUniverse Xl, ∀ t, admissionTime Xl L x ≤ t →
      P.real {ω | x ∉ D t ω} ≤ (1 - ε x) ^ (t - admissionTime Xl L x)) ∧
    (∀ᵐ ω ∂P, ∀ x ∈ attackUniverse Xl, ∃ T, ∀ t, T ≤ t → x ∈ D t ω) ∧
    (∀ᵐ ω ∂P, attackUniverse Xl ⊆ ⋃ t, D t ω) ∧
    ((∀ t ω, D t ω ⊆ attackUniverse Xl) → ∀ᵐ ω ∂P, ⋃ t, D t ω = attackUniverse Xl) := by
  have hall : ∀ᵐ ω ∂P, ∀ x ∈ attackUniverse Xl, ∃ T, ∀ t, T ≤ t → x ∈ D t ω := by
    rw [ae_ball_iff (attackUniverse_countable hfin)]
    intro x hx
    exact theorem3_eventually_covered P ℱ Xl L D Z hXl hL hLu hD hZ h1 x hx (ε x) (hε x hx)
  have hsub : ∀ᵐ ω ∂P, attackUniverse Xl ⊆ ⋃ t, D t ω := by
    filter_upwards [hall] with ω hω x hx
    obtain ⟨T, hT⟩ := hω x hx
    exact Set.mem_iUnion.mpr ⟨T, hT T le_rfl⟩
  refine ⟨fun x hx t ht => theorem3_survival P ℱ Xl L D Z hXl hL hLu hD hZ h1 x hx (ε x)
    (hε x hx) t ht, hall, hsub, fun hDX => ?_⟩
  filter_upwards [hsub] with ω hω
  exact Set.Subset.antisymm (Set.iUnion_subset fun t => hDX t ω) hω

/-- Under retention, membership in `⋃_t D_t` is exactly eventual permanent coverage; this is the
equivalence between (11) and the set formulation `X^(∞) ⊆ ⋃_t D_t`. -/
lemma mem_iUnion_iff_eventually {D : ℕ → Ω → Set α} {ω : Ω} (hr : ∀ t, D t ω ⊆ D (t + 1) ω)
    (x : α) : x ∈ ⋃ t, D t ω ↔ ∃ T, ∀ t, T ≤ t → x ∈ D t ω := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    refine ⟨n, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base => exact hn
    | succ t _ ih => exact hr t ih
  · rintro ⟨T, hT⟩
    exact Set.mem_iUnion.mpr ⟨T, hT T le_rfl⟩

end DefensiveSufficiency.GrowingContext
