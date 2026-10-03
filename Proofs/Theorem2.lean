module

public import RequestProject.Theorem5

/-!
# Theorem 2: complete coverage of a finite attack surface

Formalization of Theorem 2 of *Defensive Sufficiency in a Stackelberg Model of AI Security*
(Section IV), in the same setting as `RequestProject/Theorem5.lean`:
* `(Ω, m0, P)` is a probability space and `ℱ` a filtration;
* `X : Finset α` is the fixed finite attack surface, `N = |X|`;
* `D t ω` is the covered set `D_t`, `Z t ω` the set `Z_t` discovered in round `t`;
* `V_t = X \ D_t` (`residual`), `T = inf {t | V_t = ∅}` (`completionTime`, in `ℕ∞`).

As remarked in the paper (Section V.B), Theorem 2 is the special case of Theorem 5 in which the
patch regions are the singletons `{x}`, `x ∈ X`, all with rate `ε`. The proof below reduces to
Theorem 5 in exactly this way.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DefensiveSufficiency

variable {Ω α : Type*} {m0 : MeasurableSpace Ω}

/-- **Assumption 2** (discoverability of every attack): there is `ε ∈ (0,1]` with
`P(x ∈ Z_t | ℱ_t) ≥ ε` on `{x ∈ V_t}` for every `x ∈ X` and every round `t` (Eq. (3)).
The conditional probability is the conditional expectation of the indicator of `{x ∈ Z_t}`. -/
structure Assumption2 (P : Measure Ω) (ℱ : Filtration ℕ m0) (X : Finset α)
    (D Z : ℕ → Ω → Set α) (ε : ℝ) : Prop where
  eps_pos : 0 < ε
  eps_le_one : ε ≤ 1
  discoverability : ∀ x ∈ X, ∀ t, ∀ᵐ ω ∂P, x ∈ residual X D t ω →
    ε ≤ (P[{ω' | x ∈ Z t ω'}.indicator (fun _ => (1 : ℝ)) | ℱ t]) ω

/-- Assumptions 1 and 2 imply Assumption 3 for the singleton regions `{x}`, `x ∈ X`
(enumerated through `X.equivFin`), with all rates equal to `ε`. -/
lemma assumption3_singletons (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (ε : ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h2 : Assumption2 P ℱ X D Z ε) :
    Assumption3 P ℱ X D Z (fun i => {(X.equivFin.symm i : α)}) (fun _ => ε) where
  eta_pos _ := h2.eps_pos
  eta_le_one _ := h2.eps_le_one
  discoverability i t := by
    set x : α := (X.equivFin.symm i : α)
    have hxX : x ∈ X := (X.equivFin.symm i).2
    set A : Set Ω := {ω | x ∈ Z t ω}
    set B : Set Ω := {ω | x ∈ residual X D t ω}
    have hBm : MeasurableSet[ℱ t] B := by
      have : B = {ω | x ∈ D t ω}ᶜ := by ext ω; simp [B, residual, hxX]
      rw [this]; exact (hD t x).compl
    have hAm : MeasurableSet A := ℱ.le (t + 1) _ (hZ t x)
    have hdisc : regionDiscovered X D Z {x} t = B ∩ A := by
      ext ω; simp [regionDiscovered, A, B, Set.Nonempty, and_comm]
    have hind : (B ∩ A).indicator (fun _ => (1 : ℝ)) = B.indicator (A.indicator fun _ => 1) := by
      rw [Set.indicator_indicator]
    have hce : P[(B ∩ A).indicator (fun _ => (1 : ℝ)) | ℱ t] =ᵐ[P]
        B.indicator (P[A.indicator (fun _ => (1 : ℝ)) | ℱ t]) := by
      rw [hind]
      exact condExp_indicator ((integrable_const (1 : ℝ)).indicator hAm) hBm
    filter_upwards [hce, h2.discoverability x hxX t] with ω hω hε hU
    have hωB : ω ∈ B := by
      obtain ⟨y, hy, hyV⟩ := hU
      rw [Set.mem_singleton_iff.mp hy] at hyV
      exact hyV
    rw [hdisc, hω, Set.indicator_of_mem hωB]
    exact hε hωB
  remediation i t := by
    filter_upwards [h1.remediation t] with ω hrem hdisc
    obtain ⟨y, ⟨hyZ, hy⟩, hyV⟩ := hdisc
    rw [Set.mem_singleton_iff.mp hy] at hyZ hyV
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzV⟩
    rw [Set.mem_singleton_iff.mp hz] at hzV
    exact hzV.2 (hrem ⟨hyZ, hyV⟩)

/-- Per-attack survival bound from the proof of Theorem 2: `P(x ∈ V_t) ≤ (1 - ε)^t`. -/
theorem theorem2_survival (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (ε : ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h2 : Assumption2 P ℱ X D Z ε) (x : α) (hx : x ∈ X) (t : ℕ) :
    P.real {ω | x ∈ residual X D t ω} ≤ (1 - ε) ^ t := by
  have h3 := assumption3_singletons P ℱ X D Z ε hD hZ h1 h2
  have := regionUnresolved_le_pow P ℱ X D Z _ _ hD hZ h1 h3 (X.equivFin ⟨x, hx⟩) t
  simp only [Equiv.symm_apply_apply] at this
  convert this using 2
  ext ω
  simp [regionUnresolved, Set.Nonempty]

/-- Tail bound (4) without the `min`: `P(T > t) ≤ N (1 - ε)^t`. -/
lemma theorem2_tail_le (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (ε : ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h2 : Assumption2 P ℱ X D Z ε) (t : ℕ) :
    P {ω | (t : ℕ∞) < completionTime X D ω} ≤ X.card * ENNReal.ofReal ((1 - ε) ^ t) := by
  have h3 := assumption3_singletons P ℱ X D Z ε hD hZ h1 h2
  have hcover : (X : Set α) ⊆ ⋃ i, ({(X.equivFin.symm i : α)} : Set α) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨X.equivFin ⟨x, hx⟩, by simp⟩
  have := tail_le_sum P ℱ X D Z _ _ hD hZ hcover h1 h3 t
  simpa using this

/-- **Theorem 2.** Under Assumptions 1 and 2, with `N = |X|` and
`T = inf {t ∈ ℕ | V_t = ∅}` (`inf ∅ = ∞`):
* `P(T < ∞) = 1`, i.e. `T < ∞` almost surely;
* `P(T > t) ≤ min {1, N (1 - ε)^t}` for every `t` (Eq. (4));
* `E[T] ≤ ∑_{t ≥ 0} min {1, N (1 - ε)^t} ≤ N / ε` (Eq. (5)).

`E[T]` is the Lebesgue integral of `T` in `ℝ≥0∞`. -/
theorem theorem2 (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (X : Finset α) (D Z : ℕ → Ω → Set α) (ε : ℝ)
    (hD : ∀ t x, MeasurableSet[ℱ t] {ω | x ∈ D t ω})
    (hZ : ∀ t x, MeasurableSet[ℱ (t + 1)] {ω | x ∈ Z t ω})
    (h1 : Assumption1 P X D Z) (h2 : Assumption2 P ℱ X D Z ε) :
    P {ω | completionTime X D ω < ⊤} = 1 ∧
    (∀ t : ℕ, P {ω | (t : ℕ∞) < completionTime X D ω} ≤
      min 1 (X.card * ENNReal.ofReal ((1 - ε) ^ t))) ∧
    ∫⁻ ω, (completionTime X D ω : ℝ≥0∞) ∂P ≤
      ∑' t : ℕ, min 1 (X.card * ENNReal.ofReal ((1 - ε) ^ t)) ∧
    ∑' t : ℕ, min 1 (X.card * ENNReal.ofReal ((1 - ε) ^ t)) ≤
      X.card * ENNReal.ofReal ε⁻¹ := by
  have h3 := assumption3_singletons P ℱ X D Z ε hD hZ h1 h2
  have hcover : (X : Set α) ⊆ ⋃ i, ({(X.equivFin.symm i : α)} : Set α) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨X.equivFin ⟨x, hx⟩, by simp⟩
  have h5 := theorem5 P ℱ X D Z _ _ hD hZ hcover h1 h3
  have htail : ∀ t : ℕ, P {ω | (t : ℕ∞) < completionTime X D ω} ≤
      min 1 (X.card * ENNReal.ofReal ((1 - ε) ^ t)) := fun t =>
    le_min prob_le_one (theorem2_tail_le P ℱ X D Z ε hD hZ h1 h2 t)
  refine ⟨?_, htail, ?_, ?_⟩
  · -- almost-sure completion
    have hm : MeasurableSet {ω | completionTime X D ω < ⊤} := by
      have : {ω | completionTime X D ω < ⊤} =
          (⋂ t : ℕ, {ω | (t : ℕ∞) < completionTime X D ω})ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iInter, not_forall, not_lt]
        constructor
        · intro h
          obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
          exact ⟨k, hk ▸ le_rfl⟩
        · rintro ⟨k, hk⟩
          exact lt_of_le_of_lt hk (ENat.coe_lt_top k)
      rw [this]
      exact (MeasurableSet.iInter fun t => measurableSet_lt_completionTime ℱ X D hD t).compl
    exact (prob_compl_eq_zero_iff hm).mp (ae_iff.mp (by simpa using h5.1))
  · -- `E[T] = ∑ₜ P(T > t) ≤ ∑ₜ min {1, N (1-ε)^t}`
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
      _ ≤ _ := ENNReal.tsum_le_tsum htail
  · -- `∑ₜ min {1, N (1-ε)^t} ≤ N / ε`
    have h0 : 0 ≤ 1 - ε := by linarith [h2.eps_le_one]
    have h1' : 1 - ε < 1 := by linarith [h2.eps_pos]
    calc ∑' t : ℕ, min 1 (X.card * ENNReal.ofReal ((1 - ε) ^ t))
        ≤ ∑' t : ℕ, (X.card : ℝ≥0∞) * ENNReal.ofReal ((1 - ε) ^ t) :=
          ENNReal.tsum_le_tsum fun t => min_le_right _ _
      _ = X.card * ∑' t : ℕ, ENNReal.ofReal ((1 - ε) ^ t) := ENNReal.tsum_mul_left
      _ = X.card * ENNReal.ofReal ε⁻¹ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => pow_nonneg h0 t)
            (summable_geometric_of_lt_one h0 h1'), tsum_geometric_of_lt_one h0 h1']
          congr 2
          ring

end DefensiveSufficiency
