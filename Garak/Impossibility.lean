-- Impossibility.lean
-- Toward: no sound guardrail can be complete.

import Mathlib          -- if slow, narrow later to Finset.Card / Finset.Image
import Garak.Checker

-- (1) PIGEONHOLE (proved). If the checker's finite ruleset is smaller than the
-- set of adversarial prompts it must catch, some adversarial prompt is uncaught.
theorem no_finite_checker_is_complete
    {Sig : Type}
    (Adversarial : Finset Prompt)
    (Signatures  : Finset Sig)
    (catches     : Sig → Prompt)
    (h : Signatures.card < Adversarial.card) :
    ∃ x ∈ Adversarial, ∀ s ∈ Signatures, catches s ≠ x := by
  by_contra hcon
  push_neg at hcon
  have hsub : Adversarial ⊆ Signatures.image catches := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hcon x hx
    exact Finset.mem_image.mpr ⟨s, hs, hsx⟩
  have h1 : Adversarial.card ≤ (Signatures.image catches).card := Finset.card_le_card hsub
  have h2 : (Signatures.image catches).card ≤ Signatures.card := Finset.card_image_le
  omega
  -- if `Finset.card_le_card` errors, your mathlib may want `Finset.card_le_of_subset`

-- (2) CONDITIONAL (proved). If any blocked attack can be extended into a NEW
-- attack that evades the checker, then no checker is complete.
theorem no_complete_checker_if_evadable
    (c : Checker) (policy : Policy)
    (extend  : Prompt → Prompt)
    (h_oops  : ∀ x, policy x → policy (extend x))
    (h_evade : ∀ x, c.block x = true → c.block (extend x) = false)
    (h_exists : ∃ x, policy x) :
    ∃ x, policy x ∧ c.block x = false := by
  obtain ⟨x, hx⟩ := h_exists
  by_cases hb : c.block x = true
  · exact ⟨extend x, h_oops x hx, h_evade x hb⟩
  · refine ⟨x, hx, ?_⟩
    rcases Bool.dichotomy (c.block x) with h | h
    · exact h
    · exact absurd h hb

-- (3) THE REAL TARGET (sorry — this is the work to do with the professor).
-- No checker can be BOTH sound and complete over a rich enough prompt space.
-- `hrich` is a placeholder for that richness assumption — deciding its right
-- form is question #2 for tomorrow. Discharging the proof needs the
-- incompressibility / diagonalization argument (Vassilev 2025).
theorem no_sound_and_complete_checker
    (c : Checker) (policy : Policy)
    (hrich : True) :
    ¬ (Sound c policy ∧ Complete c policy) := by
  sorry
