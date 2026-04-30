-- Types.lean
-- Core types for the garak formalization

inductive VulnCategory : Type where
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
