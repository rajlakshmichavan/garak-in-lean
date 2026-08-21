-- Types.lean
-- Core types for the garak formalization
-- Defining types specific to garak based on types already defined under type theory

inductive VulnCategory : Type where
-- VulnCategory: an inductive type (where the inductive type is already defined)
-- Type where is the syntax for defining sub-types for the type VulnCategory
  | PromptInjection
  | InsecureOutput
  | SensitiveDisclosure
  | Overreliance
  | ModelTheft
  | Toxicity
  deriving Repr, DecidableEq

structure Probe where
  name     : String
  prompt   : String
  targets  : VulnCategory
  deriving Repr

structure Response where
  content  : String
  deriving Repr

structure Turn where
  probe    : Probe
  response : Response
  deriving Repr

structure Conversation where
  turns    : List Turn
  deriving Repr
