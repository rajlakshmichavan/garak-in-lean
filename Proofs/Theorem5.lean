module

public import Mathlib

/-!
# Theorem 5: completion under region-level repairs

Formalization of Theorem 5 of *Defensive Sufficiency in a Stackelberg Model of AI Security*.

Setting (Sections III–V of the paper):
* `(Ω, m0, P)` is a probability space and `ℱ` is a filtration (`ℱ t` = information right before
  round `t`).
* `X : Finset α` is the fixed, finite attack surface.
* `D t ω : Set α` is the covered set `D_t` and `Z t ω : Set α` the set `Z_t` of attacks discovered
  in round `t`; membership in `D t` is `ℱ t`-measurable and membership in `Z t` is
  `ℱ (t+1)`-measurable.
* `V_t = X \ D_t` is the residual vulnerable set (`residual`).
* `R : Fin m → Set α` are the patch regions, covering `X`, with discovery rates `η i ∈ (0,1]`.
* `H_{i,t} = {R_i ∩ V_t ≠ ∅}` (`regionUnresolved`).
* `T = inf {t | V_t = ∅}` with `inf ∅ = ∞` (`completionTime`, valued in `ℕ∞`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DefensiveSufficiency

variable {Ω α : Type*} {m0 : MeasurableSpace Ω}

/-- The residual vulnerable set `V_t = X \ D_t` (fixed attack surface `X_t = X`). -/
def residual (X : Finset α) (D : ℕ → Ω → Set α) (t : ℕ) (ω : Ω) : Set α :=
  (X : Set α) \ D t ω

/-- The completion time `T = inf {t ∈ ℕ | V_t = ∅}`, with `inf ∅ = ∞`. -/
noncomputable def completionTime (X : Finset α) (D : ℕ → Ω → Set α) (ω : Ω) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : residual X D t ω = ∅), (t : ℕ∞)

/-- The event `H_{i,t} = {R_i ∩ V_t ≠ ∅}` that the region `R_i` still contains an unresolved
attack at round `t`. -/
def regionUnresolved (X : Finset α) (D : ℕ → Ω → Set α) (Ri : Set α) (t : ℕ) : Set Ω :=
  {ω | (Ri ∩ residual X D t ω).Nonempty}

/-- The event `{Z_t ∩ R_i ∩ V_t ≠ ∅}` that round `t` discovers a vulnerable member of `R_i`. -/
def regionDiscovered (X : Finset α) (D Z : ℕ → Ω → Set α) (Ri : Set α) (t : ℕ) : Set Ω :=
  {ω | (Z t ω ∩ Ri ∩ residual X D t ω).Nonempty}

/-- **Assumption 1** (holding almost surely in every round).
(i) Effective remediation: `Z_t ∩ V_t ⊆ D_{t+1}`. (ii) Retention: `D_t ⊆ D_{t+1}`. -/
structure Assumption1 (P : Measure Ω) (X : Finset α) (D Z : ℕ → Ω → Set α) : Prop where
  remediation : ∀ t, ∀ᵐ ω ∂P, Z t ω ∩ residual X D t ω ⊆ D (t + 1) ω
  retention : ∀ t, ∀ᵐ ω ∂P, D t ω ⊆ D (t + 1) ω

/-- **Assumption 3** for the patch regions `R i` with rates `η i ∈ (0,1]`.
(i) Discoverability: `P(Z_t ∩ R_i ∩ V_t ≠ ∅ | ℱ_t) ≥ η_i` on `H_{i,t}` (Eq. (12)).
(ii) Effective remediation: `Z_t ∩ R_i ∩ V_t ≠ ∅ ⟹ R_i ∩ V_{t+1} = ∅` a.s. (Eq. (13)). -/
structure Assumption3 {m : ℕ} (P : Measure Ω) (ℱ : Filtration ℕ m0) (X : Finset α)
    (D Z : ℕ → Ω → Set α) (R : Fin m → Set α) (η : Fin m → ℝ) : Prop where
  eta_pos : ∀ i, 0 < η i
  eta_le_one : ∀ i, η i ≤ 1
  discoverability : ∀ i t, ∀ᵐ ω ∂P, ω ∈ regionUnresolved X D (R i) t →
    η i ≤ (P[(regionDiscovered X D Z (R i) t).indicator (fun _ => (1 : ℝ)) | ℱ t]) ω
  remediation : ∀ i t, ∀ᵐ ω ∂P, ω ∈ regionDiscovered X D Z (R i) t →
    R i ∩ residual X D (t + 1) ω = ∅

lemma lt_completionTime_iff (X : Finset α) (D : ℕ → Ω → Set α) (ω : Ω) (t : ℕ) :
    (t : ℕ∞) < completionTime X D ω ↔ ∀ s ≤ t, residual X D s ω ≠ ∅ := by
  unfold completionTime
  constructor
  · intro h s hs hV
    have := (iInf₂_le s hV : (⨅ (t : ℕ) (_ : residual X D t ω = ∅), (t : ℕ∞)) ≤ s)
    have := lt_of_lt_of_le h this
    exact absurd (by exact_mod_cast this) (not_lt.mpr hs)
  · intro h
    have : ((t + 1 : ℕ) : ℕ∞) ≤ ⨅ (t : ℕ) (_ : residual X D t ω = ∅), (t : ℕ∞) := by
      refine le_iInf₂ fun s hs => ?_
      have : t < s := by
        by_contra hc
        exact h s (not_lt.mp hc) hs
      exact_mod_cast this
    refine lt_of_lt_of_le ?_ this
    exact_mod_cast Nat.lt_succ_self t

lemma measurableSet_inter_residual_nonempty {mΩ : MeasurableSpace Ω} (X : Finset α)
    (D : ℕ → Ω → Set α) (A : Ω → Set α) (S : Set α) (t : ℕ)
    (hD : ∀ x, MeasurableSet[mΩ] {ω | x ∈ D t ω})
    (hA : ∀ x, MeasurableSet[mΩ] {ω | x ∈ A ω}) :
    MeasurableSet[mΩ] {ω | (A ω ∩ S ∩ residual X D t ω).Nonempty} := by
  classical
  have : {ω | (A ω ∩ S ∩ residual X D t ω).Nonempty} =
      ⋃ x ∈ X, ({ω | x ∈ A ω} ∩ {ω | x ∈ S} ∩ {ω | x ∈ D t ω}ᶜ) := by
    ext ω
    simp only [residual, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.Nonempty, Set.mem_diff, Finset.mem_coe, exists_prop]
    constructor
    · rintro ⟨x, ⟨hA, hS⟩, hX, hD⟩
      exact ⟨x, hX, ⟨hA, hS⟩, hD⟩
    · rintro ⟨x, hX, ⟨hA, hS⟩, hD⟩
      exact ⟨x, ⟨hA, hS⟩, hX, hD⟩
  rw [this]
  refine Finset.measurableSet_biUnion _ fun x _ => ?_
  refine ((hA x).inter ?_).inter (hD x).compl
  by_cases hx : x ∈ S <;> simp [hx]

lemma measurableSet_regionUnresolved (ℱ : Filtration ℕ m0) (X : Finset α)
    (D : ℕ → Ω → Set α) (Ri : Set α) (t : ℕ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω}) :
    MeasurableSet[ℱ t] (regionUnresolved X D Ri t) := by
  have := measurableSet_inter_residual_nonempty (mΩ := ℱ t) X D (fun _ => Set.univ) Ri t
    (hD t) (fun x => by simp)
  simpa [regionUnresolved] using this

lemma measurableSet_regionDiscovered (ℱ : Filtration ℕ m0) (X : Finset α)
    (D Z : ℕ → Ω → Set α) (Ri : Set α) (t : ℕ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω}) :
    MeasurableSet (regionDiscovered X D Z Ri t) :=
  measurableSet_inter_residual_nonempty X D (Z t) Ri t (fun x => ℱ.le t _ (hD t x))
    (fun x => ℱ.le (t + 1) _ (hZ t x))

/-- One-round survival bound for a region: `P(H_{i,t+1}) ≤ (1 - η_i) P(H_{i,t})`. -/
lemma regionUnresolved_step {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (R : Fin m → Set α)
    (η : Fin m → ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h3 : Assumption3 P ℱ X D Z R η) (i : Fin m) (t : ℕ) :
    P.real (regionUnresolved X D (R i) (t + 1)) ≤
      (1 - η i) * P.real (regionUnresolved X D (R i) t) := by
  set H := regionUnresolved X D (R i) t with hHdef
  set H' := regionUnresolved X D (R i) (t + 1) with hH'def
  set E := regionDiscovered X D Z (R i) t with hEdef
  have hHm : MeasurableSet[ℱ t] H := measurableSet_regionUnresolved ℱ X D (R i) t hD
  have hH : MeasurableSet H := ℱ.le t _ hHm
  have hE : MeasurableSet E := measurableSet_regionDiscovered ℱ X D Z (R i) t hD hZ
  -- `H_{t+1} ⊆ H_t \ E` almost surely
  have hsub : H' ≤ᵐ[P] (H \ E : Set Ω) := by
    filter_upwards [h1.retention t, h3.remediation i t] with ω hret hrem hω'
    have hω' : ω ∈ H' := hω'
    refine ⟨?_, fun hωE => ?_⟩
    · obtain ⟨x, hxR, hxX, hxD⟩ := hω'
      exact ⟨x, hxR, hxX, fun h => hxD (hret h)⟩
    · have := hrem hωE
      obtain ⟨x, hx⟩ := hω'
      rw [Set.eq_empty_iff_forall_notMem] at this
      exact this x hx
  have h_le : P.real H' ≤ P.real (H \ E) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have h_split : P.real (H \ E) + P.real (H ∩ E) = P.real H := measureReal_diff_add_inter hE
  -- `η P(H_t) ≤ P(H_t ∩ E)` by the discoverability assumption
  have h_key : η i * P.real H ≤ P.real (H ∩ E) := by
    have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const (1 : ℝ)).indicator hE
    have h_eq : ∫ ω in H, E.indicator (fun _ => (1 : ℝ)) ω ∂P = P.real (H ∩ E) := by
      rw [integral_indicator_const _ hE, smul_eq_mul, mul_one, measureReal_restrict_apply hE,
        Set.inter_comm]
    have h_ce : ∫ ω in H, (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂P =
        ∫ ω in H, E.indicator (fun _ => (1 : ℝ)) ω ∂P :=
      setIntegral_condExp (ℱ.le t) hint hHm
    have h_mono : ∫ ω in H, η i ∂P ≤ ∫ ω in H, (P[E.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω ∂P :=
      setIntegral_mono_on_ae (integrable_const _).integrableOn integrable_condExp.integrableOn hH
        (h3.discoverability i t)
    rw [setIntegral_const, smul_eq_mul] at h_mono
    linarith
  linarith

/-- Region survival bound: `P(H_{i,t}) ≤ (1 - η_i)^t`. -/
lemma regionUnresolved_le_pow {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (R : Fin m → Set α)
    (η : Fin m → ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h3 : Assumption3 P ℱ X D Z R η) (i : Fin m) (t : ℕ) :
    P.real (regionUnresolved X D (R i) t) ≤ (1 - η i) ^ t := by
  induction t with
  | zero => simpa using measureReal_le_one
  | succ t ih =>
    have h0 : 0 ≤ 1 - η i := by linarith [h3.eta_le_one i]
    calc P.real (regionUnresolved X D (R i) (t + 1))
        ≤ (1 - η i) * P.real (regionUnresolved X D (R i) t) :=
          regionUnresolved_step P ℱ X D Z R η hD hZ h1 h3 i t
      _ ≤ (1 - η i) * (1 - η i) ^ t := mul_le_mul_of_nonneg_left ih h0
      _ = (1 - η i) ^ (t + 1) := by ring

/-- `{T > t} ⊆ ⋃ᵢ H_{i,t}`: a remaining vulnerable attack lies in an unresolved region. -/
lemma lt_completionTime_subset {m : ℕ} (X : Finset α) (D : ℕ → Ω → Set α) (R : Fin m → Set α)
    (hcover : (X : Set α) ⊆ ⋃ i, R i) (t : ℕ) :
    {ω | (t : ℕ∞) < completionTime X D ω} ⊆ ⋃ i, regionUnresolved X D (R i) t := by
  intro ω hω
  rw [Set.mem_setOf_eq, lt_completionTime_iff] at hω
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr (hω t le_rfl)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx.1)
  exact Set.mem_iUnion.mpr ⟨i, x, hi, hx⟩

/-- Tail bound (14) without the `min`. -/
lemma tail_le_sum {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (R : Fin m → Set α)
    (η : Fin m → ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (hcover : (X : Set α) ⊆ ⋃ i, R i)
    (h1 : Assumption1 P X D Z) (h3 : Assumption3 P ℱ X D Z R η) (t : ℕ) :
    P {ω | (t : ℕ∞) < completionTime X D ω} ≤ ∑ i, ENNReal.ofReal ((1 - η i) ^ t) := by
  calc P {ω | (t : ℕ∞) < completionTime X D ω}
      ≤ P (⋃ i, regionUnresolved X D (R i) t) :=
        measure_mono (lt_completionTime_subset X D R hcover t)
    _ ≤ ∑ i, P (regionUnresolved X D (R i) t) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal ((1 - η i) ^ t) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (regionUnresolved_le_pow P ℱ X D Z R η hD hZ h1 h3 i t)

lemma measurableSet_lt_completionTime (ℱ : Filtration ℕ m0) (X : Finset α)
    (D : ℕ → Ω → Set α) (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω}) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < completionTime X D ω} := by
  have : {ω | (t : ℕ∞) < completionTime X D ω} =
      ⋂ s ∈ Finset.range (t + 1), regionUnresolved X D Set.univ s := by
    ext ω
    simp only [Set.mem_setOf_eq, lt_completionTime_iff, Set.mem_iInter, Finset.mem_range,
      regionUnresolved, Set.univ_inter, Set.nonempty_iff_ne_empty]
    exact ⟨fun h s hs => h s (by omega), fun h s hs => h s (by omega)⟩
  rw [this]
  exact Finset.measurableSet_biInter _ fun s _ =>
    ℱ.le s _ (measurableSet_regionUnresolved ℱ X D Set.univ s hD)

lemma enat_toENNReal_eq_tsum (n : ℕ∞) :
    (n : ℝ≥0∞) = ∑' t : ℕ, if (t : ℕ∞) < n then (1 : ℝ≥0∞) else 0 := by
  induction n using ENat.recTopCoe with
  | top =>
    simp only [ENat.toENNReal_top, ENat.coe_lt_top, if_true]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe k =>
    rw [tsum_eq_sum (s := Finset.range k)]
    · simp only [Nat.cast_lt]
      rw [Finset.sum_ite_of_true (fun t ht => Finset.mem_range.mp ht)]
      simp
    · intro t ht
      simp only [Finset.mem_range, not_lt] at ht
      simp [Nat.cast_lt, not_lt.mpr ht]

/-- **Theorem 5.** Under Assumptions 1 and 3 (with patch regions covering the finite attack
surface `X`), the completion time `T = inf {t | V_t = ∅}` is finite almost surely, and
* `P(T > t) ≤ min {1, ∑ᵢ (1 - ηᵢ)^t}` for every `t` (Eq. (14)),
* `E[T] ≤ ∑ᵢ ηᵢ⁻¹` (Eq. (15)).

Only the retention part (ii) of Assumption 1 is used in the proof; effective remediation for
regions is provided by Assumption 3(ii). -/
theorem theorem5 {m : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (R : Fin m → Set α)
    (η : Fin m → ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (hcover : (X : Set α) ⊆ ⋃ i, R i)
    (h1 : Assumption1 P X D Z) (h3 : Assumption3 P ℱ X D Z R η) :
    (∀ᵐ ω ∂P, completionTime X D ω < ⊤) ∧
    (∀ t : ℕ, P {ω | (t : ℕ∞) < completionTime X D ω} ≤
      min 1 (∑ i, ENNReal.ofReal ((1 - η i) ^ t))) ∧
    ∫⁻ ω, (completionTime X D ω : ℝ≥0∞) ∂P ≤ ∑ i, ENNReal.ofReal (η i)⁻¹ := by
  have htail := tail_le_sum P ℱ X D Z R η hD hZ hcover h1 h3
  refine ⟨?_, fun t => le_min prob_le_one (htail t), ?_⟩
  · -- almost-sure completion
    rw [ae_iff]
    simp only [not_lt, top_le_iff]
    apply le_antisymm _ (zero_le')
    have hlim : Filter.Tendsto (fun t : ℕ => ∑ i, ENNReal.ofReal ((1 - η i) ^ t))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ _i : Fin m, ENNReal.ofReal 0 by simp]
      refine tendsto_finset_sum _ fun i _ => ENNReal.tendsto_ofReal ?_
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith [h3.eta_le_one i])
        (by linarith [h3.eta_pos i])
    refine ge_of_tendsto' hlim fun t => le_trans (measure_mono fun ω hω => ?_) (htail t)
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]
    exact ENat.coe_lt_top t
  · -- expectation bound
    calc ∫⁻ ω, (completionTime X D ω : ℝ≥0∞) ∂P
        = ∫⁻ ω, ∑' t : ℕ, {ω | (t : ℕ∞) < completionTime X D ω}.indicator 1 ω ∂P := by
          congr 1
          ext ω
          rw [enat_toENNReal_eq_tsum]
          congr 1
          ext t
          simp [Set.indicator_apply]
      _ = ∑' t : ℕ, P {ω | (t : ℕ∞) < completionTime X D ω} := by
          rw [lintegral_tsum fun t =>
            (measurable_one.indicator (measurableSet_lt_completionTime ℱ X D hD t)).aemeasurable]
          congr 1
          ext t
          exact lintegral_indicator_one (measurableSet_lt_completionTime ℱ X D hD t)
      _ ≤ ∑' t : ℕ, ∑ i, ENNReal.ofReal ((1 - η i) ^ t) := ENNReal.tsum_le_tsum htail
      _ = ∑ i, ∑' t : ℕ, ENNReal.ofReal ((1 - η i) ^ t) :=
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable
      _ = ∑ i, ENNReal.ofReal (η i)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h0 : 0 ≤ 1 - η i := by linarith [h3.eta_le_one i]
          have h1' : 1 - η i < 1 := by linarith [h3.eta_pos i]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg h0 t)
            (summable_geometric_of_lt_one h0 h1'), tsum_geometric_of_lt_one h0 h1']
          congr 1
          ring

end DefensiveSufficiency
