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

-- Complete: correct on EVERY prompt (never misses an out-of-policy prompt).
def Complete (c : Checker) (policy : Policy) : Prop :=
  ∀ x, CorrectOn c policy x

-- Sound: never blocks an in-policy (benign) prompt.
def Sound (c : Checker) (policy : Policy) : Prop :=
  ∀ x, c.block x = true → policy x

-- Sanity check: "block everything" is complete ONLY for the block-everything policy.
def blockAll : Checker := { name := "block-all", block := fun _ => true }

example : Complete blockAll (fun _ => True) := by
  intro x
  constructor
  · intro _; trivial
  · intro _; rfl
