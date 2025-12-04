import Mathlib.Algebra.Order.Group.Defs

#check LinearOrderedAddCommGroup

-- Test that Int has this instance
#check (inferInstance : LinearOrderedAddCommGroup Int)

-- Test that Rat has this instance
#check (inferInstance : LinearOrderedAddCommGroup Rat)

-- Test that Real would have this instance (comment out if Real not available)
-- #check (inferInstance : LinearOrderedAddCommGroup Real)
