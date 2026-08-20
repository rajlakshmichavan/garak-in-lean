import Garak.Checker
import Garak.Atkgen
import Garak.Theorems

#check Nat                    -- a type of numbers
#check String                 -- a type of text
#check Prop                   -- the type of propositions
#check False                  -- a proposition
#check (3 : Nat) + 4          -- a term; its type is Nat

#eval "hello" ++ " " ++ "world"
#eval String.length ("hello " ++ "world")

theorem two_plus_two : 2 + 2 = 4 := by rfl
#print two_plus_two           -- prints the known definition or theorem

-- Point out: `Checker` is a type. `Complete c policy` is a proposition. `blockAll` is a concrete checker term.

#print Checker
#print Complete
#print blockAll

-- `Complete blockAll (fun _ => True)` is a Prop, something we might prove
#check Complete blockAll (fun _ => True)

example : Complete blockAll (fun _ => True) := by
  intro x
  constructor
  · intro _; trivial
  · intro _; rfl


theorem pythagoras_345 : 3 * 3 + 4 * 4 = (5 * 5 : Nat) := by
  /- GOAL (before any tactic): `3 * 3 + 4 * 4 = 5 * 5` -/

  have h3 : 3 * 3 = 9 := by rfl
  have h4 : 4 * 4 = 16 := by rfl
  have h5 : 5 * 5 = 25 := by rfl

  calc
    3 * 3 + 4 * 4 = 9 + 16 := by rw [h3, h4]
    /- GOAL (middle step): `9 + 16 = 25` -/
    _ = 25 := by rfl
    /- GOAL (final step): `25 = 5 * 5` -/
    _ = 5 * 5 := by rw [← h5]
  /- no goals left -/


theorem not_proven_yet : (1 : Nat) = 0 := by
  sorry
