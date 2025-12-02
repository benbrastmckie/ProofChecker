import ProofChecker.Semantics.TaskFrame

/-!
# TaskFrame Tests

Tests for task frame structure and constraints.
-/

namespace ProofCheckerTest.Semantics

open ProofChecker.Semantics

-- Test: trivialFrame satisfies nullity
example : TaskFrame.trivialFrame.task_rel () 0 () :=
  TaskFrame.trivialFrame.nullity ()

-- Test: trivialFrame satisfies compositionality (task relation is always true)
example : TaskFrame.trivialFrame.task_rel () 5 () := trivial

-- Test: trivialFrame with negative duration
example : TaskFrame.trivialFrame.task_rel () (-3) () := trivial

-- Test: identityFrame satisfies nullity (with explicit type annotation)
example : (TaskFrame.identityFrame Nat).task_rel (3 : Nat) 0 (3 : Nat) :=
  (TaskFrame.identityFrame Nat).nullity (3 : Nat)

-- Test: natFrame satisfies nullity
example : TaskFrame.natFrame.task_rel (5 : Nat) 0 (5 : Nat) :=
  TaskFrame.natFrame.nullity (5 : Nat)

-- Test: natFrame with non-zero duration (task relation always true)
example : TaskFrame.natFrame.task_rel (0 : Nat) 10 (42 : Nat) := trivial

-- Test: Construct custom simple task frame
def customFrame : TaskFrame where
  WorldState := Bool
  task_rel := fun _ _ _ => True
  nullity := fun _ => trivial
  compositionality := fun _ _ _ _ _ _ _ => trivial

-- Test: Custom frame satisfies properties
example : customFrame.task_rel true 0 true := customFrame.nullity true
example : customFrame.task_rel false 5 true := trivial

end ProofCheckerTest.Semantics
