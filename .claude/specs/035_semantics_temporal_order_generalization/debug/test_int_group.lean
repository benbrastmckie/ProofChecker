-- Check what Int actually has
#check (inferInstance : AddCommGroup Int)
#check (inferInstance : PartialOrder Int)
#check (inferInstance : LinearOrder Int)

-- Try to build OrderedAddCommGroup manually if needed
-- Check if we can derive it
