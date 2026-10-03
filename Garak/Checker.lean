-- Checker.lean
-- Formal model of a guardrail / detector as a "checker"

import Garak.Types

-- A prompt is a string of text (Vassilev's setting).
abbrev Prompt := String

-- A policy marks which prompts are "out-of-policy" and SHOULD be blocked.
abbrev Policy := Prompt → Prop

-- A guardrail / checker: blocks (true) or allows (false) a prompt.
structure Checker where
  name  : String
  block : Prompt → Bool

-- Correct on x: the checker blocks x exactly when x is out-of-policy.
def CorrectOn (c : Checker) (policy : Policy) (x : Prompt) : Prop :=
  c.block x = true ↔ policy x

-- Sound: never blocks an in-policy (benign) prompt.            (no false positives)
def Sound (c : Checker) (policy : Policy) : Prop :=
  ∀ x, c.block x = true → policy x

-- Complete: never MISSES an out-of-policy prompt.              (no false negatives)
--
-- CHANGED from the original `∀ x, CorrectOn c policy x`. That original is an iff,
-- so it already contained `Sound`; the comment said "never misses" but the
-- definition also said "never over-blocks". With it, `Sound ∧ Complete` was
-- literally the same statement as `Complete`. Now the two are the two halves of
-- CorrectOn, and their conjunction is exactly "correct on every prompt"
-- (`correctOn_iff_sound_and_complete`).
def Complete (c : Checker) (policy : Policy) : Prop :=
  ∀ x, policy x → c.block x = true

-- The two halves recombine into the original notion.
theorem correctOn_iff_sound_and_complete (c : Checker) (policy : Policy) :
    (∀ x, CorrectOn c policy x) ↔ (Sound c policy ∧ Complete c policy) := by
  constructor
  · intro h
    exact ⟨fun x hx => Iff.mp (h x) hx, fun x hx => Iff.mpr (h x) hx⟩
  · intro h x
    exact Iff.intro (h.1 x) (h.2 x)

-- Sanity check: "block everything" is complete for EVERY policy (it never misses
-- anything), and is sound only when everything is out-of-policy. This is why
-- "complete" alone is never the goal.
def blockAll : Checker := { name := "block-all", block := fun _ => true }

example (policy : Policy) : Complete blockAll policy := by
  intro x _
  rfl

example : Sound blockAll (fun _ => True) := by
  intro x _
  trivial
