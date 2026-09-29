import Mathlib

/-!
# Feedback / Survival  (deterministic backbone)

The parts of Theorems 2 and 3 that mention no probability. Everything here is a
statement about real sequences or finite sets, so it compiles fast and is easy to
check by eye.

* `geom_bound`  — "applying the same inequality repeatedly" (the step from (6) to
                  `P(x ∈ V_t) ≤ (1-ε)^t` in the proof of Theorem 2).
* `geom_tail_sum` — `∑ₜ N(1-ε)ᵗ = N/ε`, the geometric series behind (5).
* `exists_common_time` — Proposition 1 (finite max of witness times).
* `exists_common_time_of_eventually` — the "covered from some round on" variant
                  used to turn per-attack coverage into whole-surface completion.
-/

namespace Garak.Feedback

/-- If `a` contracts by a factor `c ≥ 0` each round from round `s` on, then
`a (s+n) ≤ cⁿ · a s`. This is the paper's "apply (6) repeatedly, starting from
`P(B₀) ≤ 1`". -/
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

/-- `∑ₜ N(1-ε)ᵗ = N/ε` in `ℝ≥0∞`. This is the geometric sum that turns the tail
bound (4) into the completion-time bound (5).

RISK on first build: the three Mathlib lemma names
`summable_geometric_of_lt_one`, `tsum_geometric_of_lt_one`,
`ENNReal.ofReal_tsum_of_nonneg`. If any is renamed in your Mathlib pin, the fix is
mechanical (same lemma, new name) — send me the error. -/
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

/-- **Proposition 1.** A monotone family of covered sets that eventually covers
every element of a FINITE set covers all of it at one common time `T` (the max of
the witness times). Purely deterministic. -/
theorem exists_common_time {X : Type*} (D : ℕ → Set X) (hmono : Monotone D)
    (S : Set X) (hS : S.Finite) (h : ∀ x ∈ S, ∃ t, x ∈ D t) :
    ∃ T, ∀ x ∈ S, x ∈ D T := by
  classical
  choose! t ht using h
  refine ⟨hS.toFinset.sup t, fun x hx => ?_⟩
  exact hmono (Finset.le_sup (hS.mem_toFinset.mpr hx)) (ht x hx)

/-- The "covered from time `T_x` onward" form, over a finite type: one common `T`
past which everything is covered. This is what feeds the a.s. completion in
Theorem 2 (finite surface). -/
theorem exists_common_time_of_eventually {X : Type*} [Finite X]
    (cov : ℕ → X → Prop) (h : ∀ x, ∃ T, ∀ t, T ≤ t → cov t x) :
    ∃ T, ∀ t, T ≤ t → ∀ x, cov t x := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  choose Tx hTx using h
  exact ⟨Finset.univ.sup Tx, fun t ht x =>
    hTx x t ((Finset.le_sup (Finset.mem_univ x)).trans ht)⟩

end Garak.Feedback
