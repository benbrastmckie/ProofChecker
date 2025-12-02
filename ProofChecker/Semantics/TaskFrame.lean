/-!
# TaskFrame - Task Frame Structure for TM Semantics

This module defines task frames, the fundamental semantic structures for bimodal logic TM.

## Main Definitions

- `TaskFrame`: Structure with world states, times, task relation, and constraints
- `TaskFrame.nullity`: Identity task constraint (`task_rel w 0 w`)
- `TaskFrame.compositionality`: Task composition constraint

## Main Results

- Example task frames for testing and demonstrations

## Implementation Notes

- Times are integers (Int) for MVP simplicity
- Task relation `task_rel w x u` means: world state `u` is reachable from `w` by task of duration `x`
- Nullity: zero-duration task is identity (reflexivity)
- Compositionality: sequential tasks compose (transitivity with addition)

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - Task semantics specification
-/

namespace ProofChecker.Semantics

/--
Task frame for bimodal logic TM.

A task frame consists of:
- A type of world states
- Times as integers (for MVP, can be generalized later)
- A task relation connecting world states via timed tasks
- Nullity constraint: zero-duration task is identity
- Compositionality: tasks compose sequentially with additive time

The task relation `task_rel w x u` means: starting from world state `w`,
executing a task of duration `x` can result in world state `u`.
-/
structure TaskFrame where
  /-- Type of world states -/
  WorldState : Type
  /-- Task relation: `task_rel w x u` means u is reachable from w by task of duration x -/
  task_rel : WorldState → Int → WorldState → Prop
  /--
  Nullity constraint: zero-duration task is identity.

  For any world state `w`, executing a zero-duration task from `w` results in `w`.
  This gives reflexivity of the task relation.
  -/
  nullity : ∀ w, task_rel w 0 w
  /--
  Compositionality constraint: tasks compose with time addition.

  If task of duration `x` takes `w` to `u`, and task of duration `y` takes `u` to `v`,
  then task of duration `x + y` takes `w` to `v`.
  This gives a form of transitivity for the task relation.
  -/
  compositionality : ∀ w u v x y, task_rel w x u → task_rel u y v → task_rel w (x + y) v

namespace TaskFrame

/--
Simple unit-based task frame for testing.

World states are Unit (trivial), task relation is always true.
This is the simplest possible task frame.
-/
def trivialFrame : TaskFrame where
  WorldState := Unit
  task_rel := fun _ _ _ => True
  nullity := fun _ => trivial
  compositionality := fun _ _ _ _ _ _ _ => trivial

/--
Identity task frame: task relation is identity.

World states can be any type, task relation holds iff source equals target and time is 0.
-/
def identityFrame (W : Type) : TaskFrame where
  WorldState := W
  task_rel := fun w x u => w = u ∧ x = 0
  nullity := fun w => ⟨rfl, rfl⟩
  compositionality := by
    intros w u v x y hwu huv
    obtain ⟨h1, h2⟩ := hwu
    obtain ⟨h3, h4⟩ := huv
    subst h1 h3 h2 h4
    simp

/--
Natural number based task frame.

World states are natural numbers. Task relation: task of duration x from w
can reach any state (permissive for MVP simplicity).
-/
def natFrame : TaskFrame where
  WorldState := Nat
  task_rel := fun _ _ _ => True
  nullity := fun _ => trivial
  compositionality := fun _ _ _ _ _ _ _ => trivial

end TaskFrame

end ProofChecker.Semantics
