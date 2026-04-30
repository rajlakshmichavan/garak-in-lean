-- Detector.lean
import Garak.Types

-- A score is simply a Float
abbrev Score := Float

-- A detector has a function, a spec, a name, and a target
structure Detector where
  name     : String
  targets  : VulnCategory
  fn       : Response → Score
  spec     : Response → Prop
