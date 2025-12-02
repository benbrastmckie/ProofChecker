import ProofChecker.Semantics.TaskFrame

/-!
# WorldHistory - World Histories for Task Semantics

This module defines world histories, which are functions from time domains to world states.

## Main Definitions

- `WorldHistory`: World history structure with domain and task constraint

## Main Results

- Example world histories (constant, trivial)

## Implementation Notes

- For MVP, we simplify the world history structure to avoid Mathlib dependencies
- Domain is represented as a predicate on Int
- Convexity is simplified for MVP
- History must respect the task relation (compositionality)

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - World history specification
* [TaskFrame.lean](TaskFrame.lean) - Task frame structure
-/

namespace ProofChecker.Semantics

/--
World history for a task frame.

A world history assigns a world state to each time in its domain,
such that the history respects the task relation of the frame.

For MVP, we use a simplified structure with Int times directly.
-/
structure WorldHistory (F : TaskFrame) where
  /-- Domain predicate (which times are in the history) -/
  domain : Int → Prop
  /--
  State assignment function.

  For each time `t` in the domain, assigns a world state.
  -/
  states : (t : Int) → domain t → F.WorldState
  /--
  Task relation respect constraint.

  For any times `s, t` in domain with `s ≤ t`, the states at `s` and `t`
  must be related by the task relation with duration `t - s`.

  This ensures the history is consistent with possible task executions.
  -/
  respects_task : ∀ (s t : Int) (hs : domain s) (ht : domain t),
    s ≤ t → F.task_rel (states s hs) (t - s) (states t ht)

namespace WorldHistory

variable {F : TaskFrame}

/--
Universal world history over all time.

This history has every time in its domain and assigns the same world state everywhere.
For the trivial frame, this satisfies task respect trivially.
-/
def universal (F : TaskFrame) (w : F.WorldState) : WorldHistory F where
  domain := fun _ => True
  states := fun _ _ => w
  respects_task := by
    intros s t hs ht hst
    -- Need frame-specific proof; for trivial frame this is immediate
    sorry

/--
Trivial world history for the trivial frame.

Since trivial frame's task relation is always true, this always works.
-/
def trivial : WorldHistory TaskFrame.trivialFrame where
  domain := fun _ => True
  states := fun _ _ => ()
  respects_task := by
    intros s t hs ht hst
    exact True.intro

/--
Get the state at a time (helper function that bundles membership proof).
-/
def stateAt (τ : WorldHistory F) (t : Int) (h : τ.domain t) : F.WorldState :=
  τ.states t h

end WorldHistory

end ProofChecker.Semantics
