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

<<<<<<< HEAD

  -- Theorem 3: Conversation length is exactly n after n turns
theorem conversation_length
=======
  -- Theorem 3: After n turns, the conversation has exactly n turns in it.
  theorem conversation_length
>>>>>>> 3c80367e527148787c9ede2ca4d72630b89a0b85
    (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (n : Nat) :
    (runConversation strategy respond n).turns.length = n := by
  induction n with
<<<<<<< HEAD
=======

-- Helper lemma: if detector fires at turn n within maxTurns,
-- then EventuallyTriggers holds
theorem triggers_at_n
    (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (detector : Detector)
    (maxTurns n : Nat)
    (hn : n ≤ maxTurns)
    (hfire : detector.fn (respond (strategy
        (runConversation strategy respond n))) ≥ 0.5) :
    EventuallyTriggers strategy respond detector maxTurns := by
  exact ⟨n, hn, hfire⟩

-- Main theorem: if there exists an attackable turn,
-- atkgen eventually triggers the detector
theorem eventually_triggers
    (strategy : AtkgenStrategy)
    (respond : Probe → Response)
    (detector : Detector)
    (maxTurns : Nat)
    -- This assumption says: the target IS attackable within maxTurns
    (attackable : ∃ n ≤ maxTurns,
        detector.fn (respond (strategy
            (runConversation strategy respond n))) ≥ 0.5) :
    EventuallyTriggers strategy respond detector maxTurns := by
  exact attackable
>>>>>>> 3c80367e527148787c9ede2ca4d72630b89a0b85
  | zero => simp [runConversation]
  | succ n ih => simp [runConversation, ih]
