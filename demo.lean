-- Importing files
import Garak.Checker
import Garak.Atkgen
import Garak.Theorems

#check Nat                    -- a type of numbers
#check String                 -- a type of text
#check Prop                   -- the type of propositions
#check False                  -- a proposition
#check (3 : Nat) + 4          -- a term; its type is Nat

-- #eval = computes
#eval "hello" ++ " " ++ "world"
#eval String.length ("hello " ++ "world")

theorem two_plus_two : 2 + 2 = 4 := by rfl
-- type (theorem), theorem name (two_plus_two), statement (2+2 = 4), := signifies that our proof is starting from here
theorem two_plus_two_2 : 2 + 2 = 5 := by rfl

#print two_plus_two           -- prints the known definition or theorem in the Infoview

-- Type here is proposition, theorem is a specific kind of proposition
-- You also need to define what the Nat type is, to specify what are the numbers we are using
-- We end it with by because the proof follows in the lines after
theorem pythagoras_345 : 3 * 3 + 4 * 4 = (5 * 5 : Nat) := by
  /- Our GOAL for this proof (before any tactic): `3 * 3 + 4 * 4 = 5 * 5` -/

  have h3 : 3 * 3 = 9 := by rfl
  have h4 : 4 * 4 = 16 := by rfl
  have h5 : 5 * 5 = 25 := by rfl
-- have = writing hypotheses

-- new tactic used here: calc = uses transitivity to check equality in consecutive statements
-- rw: rewrite, checks if the LHS can be rewritten as the RHS (anything can be rewritten as anything else)
  calc
    3 * 3 + 4 * 4 = 9 + 16 := by rw [h3, h4]
    /- GOAL (middle step): `9 + 16 = 25` -/
    _ = 25 := by rfl
    /- GOAL (final step): `25 = 5 * 5` -/
    _ = 5 * 5 := by rw [← h5]
  /- no goals left -/


theorem not_proven_yet : (1 : Nat) = 0 := by
  sorry
-- sorry = a placeholder for a proof
-- Theorem named not_proven_yet is basically 1 is a part of Natural numbers which is equal to 0, which we are trying to prove by 'sorry'

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
