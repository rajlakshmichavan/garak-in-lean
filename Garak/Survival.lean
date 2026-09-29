/-
  Survival.lean
  Deterministic backbone for Theorem 2 (no probability appears here).

  Contents (every declaration below is used by Process.lean or Theorem2.lean):
    * geom_bound                     geometric decay of a contracting sequence
    * geom_tail_sum                  the geometric series  ∑ₜ N(1-ε)ᵗ = N/ε
    * exists_common_time_of_eventually   finite max of per-item "eventually" times
-/
import Mathlib

namespace Garak

/-- If `a` contracts by a factor `c ≥ 0` each round from round `s` on, then
`a (s+n) ≤ cⁿ · a s`. This is the paper's "apply the one-round inequality (6)
repeatedly, starting from `P(B₀) ≤ 1`". -/
theorem geom_bound (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (s : ℕ)
    (h : ∀ t, s ≤ t → a (t + 1) ≤ c * a t) :
    ∀ n : ℕ, a (s + n) ≤ c ^ n * a s := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : a (s + (n + 1)) ≤ c * a (s + n) := h (s + n) (Nat.le_add_right s n)
    calc a (s + (n + 1)) ≤ c * a (s + n) := h1
      _ ≤ c * (c ^ n * a s) := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (n + 1) * a s := by ring

/-- The geometric series `∑ₜ N(1-ε)ᵗ = N/ε`, in `ℝ≥0∞`. Turns the tail bound (4)
into the completion-time bound (5) of Theorem 2.
Build note: uses Mathlib's `summable_geometric_of_lt_one`,
`tsum_geometric_of_lt_one`, `ENNReal.ofReal_tsum_of_nonneg`. -/
theorem geom_tail_sum (N ε : ℝ) (hN : 0 ≤ N) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∑' t : ℕ, ENNReal.ofReal (N * (1 - ε) ^ t) = ENNReal.ofReal (N / ε) := by
  have hr0 : 0 ≤ 1 - ε := by linarith
  have hr1 : 1 - ε < 1 := by linarith
  have hsum : Summable fun t : ℕ => N * (1 - ε) ^ t :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left N
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => mul_nonneg hN (pow_nonneg hr0 t)) hsum]
  congr 1
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have h : (1 - (1 - ε)) = ε := by ring
  rw [h, div_eq_mul_inv]

/-- If every item of a finite type is covered from some round onward, then one
common round `T` covers all of them (the max of the per-item times). This is the
finite-maximum step used to pass from per-attack coverage to whole-surface
completion in Theorem 2. -/
theorem exists_common_time_of_eventually {X : Type*} [Finite X]
    (cov : ℕ → X → Prop) (h : ∀ x, ∃ T, ∀ t, T ≤ t → cov t x) :
    ∃ T, ∀ t, T ≤ t → ∀ x, cov t x := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  choose Tx hTx using h
  exact ⟨Finset.univ.sup Tx, fun t ht x =>
    hTx x t ((Finset.le_sup (Finset.mem_univ x)).trans ht)⟩

end Garak
