-- Atkgen.lean
-- Formal model of garak's adaptive attack generator

import Garak.Types
import Garak.Detector

-- An atkgen strategy takes a conversation history
-- and produces the next probe to send
def AtkgenStrategy := Conversation → Probe

-- A run of atkgen: apply a strategy n times
-- starting from an empty conversation
def runConversation (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (n : Nat) : Conversation :=
  match n with
  | 0 => { turns := [] }
  | n + 1 =>
    let prev := runConversation strategy respond n
    let nextProbe := strategy prev
    let nextResponse := respond nextProbe
    { turns := prev.turns ++ [{ probe := nextProbe, response := nextResponse }] }

-- The key property: a detector eventually triggers
-- within maxTurns, or the conversation ends cleanly
def EventuallyTriggers (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (detector : Detector)
    (maxTurns : Nat) : Prop :=
  ∃ n ≤ maxTurns, detector.fn (respond (strategy (runConversation strategy respond n))) ≥ 0.5
