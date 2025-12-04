import Mathlib

-- Check what Int has
example : AddCommGroup Int := inferInstance
example : LinearOrder Int := inferInstance

-- Try OrderedAddCommGroup
example : OrderedAddCommGroup Int := inferInstance

-- Try LinearOrderedAddCommGroup
example : LinearOrderedAddCommGroup Int := inferInstance
