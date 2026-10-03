-- Impossibility.lean
-- Toward: no fixed class of checkers can be both sound and complete.

import Mathlib
import Garak.Checker

/-! ## (1) Pigeonhole — UNCHANGED from your version (proved)

If the checker's finite ruleset is smaller than the set of adversarial prompts it
must catch, some adversarial prompt is uncaught. -/
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

/-! ### (1b) NEW: tie the pigeonhole result to the actual `Checker` type

In your version (1) never mentions `Checker`, `Complete`, or `block`; it is a
statement about a `Finset` of signatures. Here is the checker that a finite
signature list actually defines, and the statement about it you would want to
quote. Model note: each signature catches exactly ONE prompt (`catches : Sig →
Prompt`). That is narrower than a signature map that can send many prompts to the
same signature, so this is the "literal blocklist" case. -/

open Classical in
/-- The checker whose whole behaviour is a finite list of literal signatures. -/
noncomputable def signatureChecker {Sig : Type}
    (Signatures : Finset Sig) (catches : Sig → Prompt) : Checker :=
  { name := "signature-checker"
  , block := fun p => if ∃ s ∈ Signatures, catches s = p then true else false }

theorem signatureChecker_block_iff {Sig : Type}
    (Signatures : Finset Sig) (catches : Sig → Prompt) (p : Prompt) :
    (signatureChecker Signatures catches).block p = true ↔ ∃ s ∈ Signatures, catches s = p := by
  by_cases h : ∃ s ∈ Signatures, catches s = p <;> simp [signatureChecker, h]

/-- A finite blocklist smaller than the set of out-of-policy prompts is not complete. -/
theorem signatureChecker_not_complete {Sig : Type}
    (Adversarial : Finset Prompt) (Signatures : Finset Sig) (catches : Sig → Prompt)
    (policy : Policy) (hpol : ∀ x ∈ Adversarial, policy x)
    (h : Signatures.card < Adversarial.card) :
    ¬ Complete (signatureChecker Signatures catches) policy := by
  intro hC
  obtain ⟨x, hx, hmiss⟩ := no_finite_checker_is_complete Adversarial Signatures catches h
  have hblock := hC x (hpol x hx)
  rw [signatureChecker_block_iff] at hblock
  obtain ⟨s, hs, hsx⟩ := hblock
  exact hmiss s hs hsx

/-! ## (2) Conditional evasion — UNCHANGED from your version (proved) -/
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

/-- NEW, same hypotheses, stated in the vocabulary of `Complete`. -/
theorem not_complete_of_evadable
    (c : Checker) (policy : Policy)
    (extend  : Prompt → Prompt)
    (h_oops  : ∀ x, policy x → policy (extend x))
    (h_evade : ∀ x, c.block x = true → c.block (extend x) = false)
    (h_exists : ∃ x, policy x) :
    ¬ Complete c policy := by
  intro hC
  obtain ⟨x, hx, hmiss⟩ :=
    no_complete_checker_if_evadable c policy extend h_oops h_evade h_exists
  have hblock := hC x hx
  rw [hmiss] at hblock
  cases hblock

/-! ## (3) THE REAL TARGET — this is where the `sorry` was

Your version:

    theorem no_sound_and_complete_checker (c : Checker) (policy : Policy) (hrich : True) :
        ¬ (Sound c policy ∧ Complete c policy) := by sorry

It cannot be proved, because it is false: `blockAll` is complete for every policy
and sound for `fun _ => True`. `old_statement_is_false` proves that, so the reason
for replacing it is machine-checked rather than asserted. -/
theorem old_statement_is_false :
    ¬ (∀ (c : Checker) (policy : Policy), ¬ (Sound c policy ∧ Complete c policy)) := by
  intro h
  exact h blockAll (fun _ => True) ⟨fun _ _ => trivial, fun _ _ => rfl⟩

/-- `Sound ∧ Complete` is exactly "correct on every prompt". -/
theorem sound_and_complete_iff_correct (c : Checker) (policy : Policy) :
    (Sound c policy ∧ Complete c policy) ↔ (∀ x, CorrectOn c policy x) :=
  (correctOn_iff_sound_and_complete c policy).symm

/-- REPLACEMENT (diagonalisation; no `sorry`).

For ANY enumerated (countable) family of checkers `cs` — every keyword list, every
computable checker, … — there is a policy that NO member is both sound and
complete for. The richness assumption `hrich : True` was standing in for is
`probe`: an injective enumeration of prompts, one witness per checker (`String` is
infinite, so one exists).

The policy disagrees with checker `n` exactly at `probe n`: it declares `probe n`
out-of-policy iff checker `n` lets it through. -/
theorem no_sound_and_complete_checker
    (cs : ℕ → Checker) (probe : ℕ → Prompt) (hinj : Function.Injective probe) :
    ∃ policy : Policy, ∀ n, ¬ (Sound (cs n) policy ∧ Complete (cs n) policy) := by
  refine ⟨fun x => ∃ m, probe m = x ∧ (cs m).block x = false, ?_⟩
  intro n hSC
  obtain ⟨hS, hC⟩ := hSC
  cases hb : (cs n).block (probe n) with
  | true =>
    -- n blocks probe n, so soundness says probe n is out-of-policy, i.e. some m
    -- with probe m = probe n has checker m letting it through; injectivity: m = n.
    obtain ⟨m, hm, hfalse⟩ := hS (probe n) hb
    have hmn : m = n := hinj hm
    subst hmn
    rw [hb] at hfalse
    cases hfalse
  | false =>
    -- n lets probe n through, so probe n IS out-of-policy (witness n), and
    -- completeness then forces n to block it.
    have hblock : (cs n).block (probe n) = true := hC (probe n) ⟨n, rfl, hb⟩
    rw [hb] at hblock
    cases hblock

/-- The same result as "every checker in the class misclassifies some prompt".
NB: "misclassifies" = false positive OR false negative. It cannot be sharpened to
"misses an attack" for EVERY checker, because `blockAll` never misses one
(see the `blockAll` example in Checker.lean). -/
theorem every_enumerated_checker_misclassifies_a_prompt
    (cs : ℕ → Checker) (probe : ℕ → Prompt) (hinj : Function.Injective probe) :
    ∃ policy : Policy, ∀ n, ∃ x, ¬ CorrectOn (cs n) policy x := by
  obtain ⟨policy, h⟩ := no_sound_and_complete_checker cs probe hinj
  refine ⟨policy, fun n => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact h n ((correctOn_iff_sound_and_complete (cs n) policy).mp hcon)
