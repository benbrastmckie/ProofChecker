import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Data.Int.Order.Basic

-- Check typeclass exists
#check LinearOrderedAddCommGroup

-- Check Int instance
example : LinearOrderedAddCommGroup Int := inferInstance
