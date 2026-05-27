-- Theorems.lean
-- Proofs about the garak formalization

import Garak.Types
import Garak.Detector
import Garak.Atkgen

-- Theorem 1: A conversation grows monotonically
-- i.e. running for n+1 turns always produces
-- a longer conversation than n turns
-- Running a conversation for n+1 turns gives you exactly one more turn than running it for n turns.
theorem conversation_grows
    (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (n : Nat) :
    (runConversation strategy respond (n + 1)).turns.length =
    (runConversation strategy respond n).turns.length + 1 := by
  simp [runConversation]

-- Theorem 2: An empty conversation has no turns
-- Running a conversation for 0 turns gives you an empty conversation.
theorem empty_conversation_has_no_turns
    (strategy : AtkgenStrategy)
    (respond : Probe → Response) :
    (runConversation strategy respond 0).turns = [] := by
  simp [runConversation]

  -- Theorem 3: After n turns, the conversation has exactly n turns in it.
  theorem conversation_length
    (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (n : Nat) :
    (runConversation strategy respond n).turns.length = n := by
  induction n with
  | zero => simp [runConversation]
  | succ n ih => simp [runConversation, ih]
