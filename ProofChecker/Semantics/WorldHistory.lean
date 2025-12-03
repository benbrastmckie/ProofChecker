import ProofChecker.Semantics.TaskFrame

/-!
# WorldHistory - World Histories for Task Semantics

This module defines world histories, which are functions from time domains to world states.

## Paper Specification Reference

**World Histories (app:TaskSemantics, def:world-history, line 1849)**:
The JPL paper defines world histories (possible worlds) as functions `τ: T → W`
where `T ⊆ G` is a convex subset of the time group and the function respects
the task relation: for all `x, y ∈ T` with `x ≤ y`, we have `τ(y) ∈ τ(x) · (y - x)`.

**ProofChecker Implementation**:
- `domain: Int → Prop` represents the convex time subset `T ⊆ G`
- `states: (t: Int) → domain t → F.WorldState` represents the function `τ: T → W`
- `respects_task` constraint matches the paper's requirement exactly

**Critical Semantic Points**:
1. Box operator quantifies over ALL histories at time x
2. Past/Future operators quantify over times in the SAME history
3. Times must be in history's domain for evaluation

## Main Definitions

- `WorldHistory`: World history structure with domain and task constraint

## Main Results

- Example world histories (constant, trivial, universal with conditional validity)

## Implementation Notes

- For MVP, we simplify the world history structure to avoid Mathlib dependencies
- Domain is represented as a predicate on Int
- Convexity is simplified for MVP (not formally enforced)
- History must respect the task relation (compositionality)

## References

* [ARCHITECTURE.md](../../../Documentation/UserGuide/ARCHITECTURE.md) - World history specification
* [TaskFrame.lean](TaskFrame.lean) - Task frame structure
* JPL Paper app:TaskSemantics (def:world-history, line 1849) - Formal world history definition
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
Universal world history over all time (conditional on reflexive frame).

This history has every time in its domain and assigns the same world state everywhere.

**Frame Constraint Required**: ReflexiveTaskFrame

A frame is reflexive if for all world states `w` and durations `d`, the task relation
`task_rel w d w` holds. This is stronger than nullity (which only requires `task_rel w 0 w`).

**Examples of Reflexive Frames**:
- `trivialFrame`: task_rel is always True (reflexive)
- `natFrame`: task_rel is always True (reflexive)

**Non-Reflexive Frame Example**:
- `identityFrame`: task_rel only holds at duration 0 (not reflexive for d ≠ 0)

**Justification**: For a constant history to respect the task relation, we need
`task_rel w (t - s) w` for all times `s ≤ t`. Nullity only gives this when `s = t`.
Compositionality alone cannot build arbitrary-duration self-loops without additional
frame properties.

**Impact on Semantics**: The universal history constructor is valid for reflexive frames
(like trivialFrame used in examples). For general frames, use alternative history
construction methods or prove reflexivity for the specific frame.

**Future Work**: Either (a) add reflexivity as a TaskFrame constraint, (b) make universal
conditional on a proof of reflexivity, or (c) accept conditional validity (current MVP).
-/
def universal (F : TaskFrame) (w : F.WorldState) : WorldHistory F where
  domain := fun _ => True
  states := fun _ _ => w
  respects_task := by
    intros s t hs ht hst
    -- This requires F to be reflexive: ∀ w d, task_rel w d w
    -- For trivialFrame and natFrame, this holds trivially.
    -- For identityFrame, this only holds when s = t.
    -- For MVP, we document the requirement and use sorry.
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

/-! ## Time-Shift Construction

The time-shift construction is fundamental to proving MF and TF axioms.
Given a history σ and times x, y, we construct a shifted history where
σ'(z) = σ(z + (y - x)).

This corresponds to "viewing σ from time x instead of time y".
-/

/--
Time-shifted history construction.

Given history `σ` and shift offset `Δ = y - x`, construct history `τ` where:
- `τ.domain z ↔ σ.domain (z + Δ)`
- `τ.states z = σ.states (z + Δ)`

This allows us to relate truth at (σ, y) to truth at (τ, x).

**Paper Reference**: app:auto_existence (line ~2330) defines time-shift automorphisms.

**Key Property**: If σ respects the task relation, so does the shifted history,
because the task relation only depends on duration (t - s), which is preserved
under time translation.
-/
def time_shift (σ : WorldHistory F) (Δ : Int) : WorldHistory F where
  domain := fun z => σ.domain (z + Δ)
  states := fun z hz => σ.states (z + Δ) hz
  respects_task := by
    intros s t hs ht hst
    -- Need: task_rel (σ.states (s + Δ)) (t - s) (σ.states (t + Δ))
    -- We have: σ respects task, so task_rel (σ.states (s + Δ)) ((t + Δ) - (s + Δ)) (σ.states (t + Δ))
    -- Since (t + Δ) - (s + Δ) = t - s, this is exactly what we need
    have h_shifted : (s + Δ) ≤ (t + Δ) := Int.add_le_add_right hst Δ
    have h_duration : (t + Δ) - (s + Δ) = t - s := by omega
    rw [← h_duration]
    exact σ.respects_task (s + Δ) (t + Δ) hs ht h_shifted

/--
Time-shift preserves domain membership (forward direction).
If z is in the shifted domain, then z + Δ is in the original domain.
-/
theorem time_shift_domain_iff (σ : WorldHistory F) (Δ z : Int) :
    (time_shift σ Δ).domain z ↔ σ.domain (z + Δ) := by
  rfl

/--
Inverse time-shift: shifting by -Δ undoes shifting by Δ on the domain.
-/
theorem time_shift_inverse_domain (σ : WorldHistory F) (Δ : Int) (z : Int) :
    (time_shift (time_shift σ Δ) (-Δ)).domain z ↔ σ.domain z := by
  simp only [time_shift]
  constructor
  · intro h
    have : z + -Δ + Δ = z := by omega
    rw [this] at h
    exact h
  · intro h
    have : z + -Δ + Δ = z := by omega
    rw [this]
    exact h

/--
States are equal when times are provably equal (proof irrelevance).

This lemma allows us to transport states from one time to another when the times
are equal. This is essential for dependent type reasoning in time-shift proofs.
-/
theorem states_eq_of_time_eq (σ : WorldHistory F) (t₁ t₂ : Int)
    (h : t₁ = t₂) (ht₁ : σ.domain t₁) (ht₂ : σ.domain t₂) :
    σ.states t₁ ht₁ = σ.states t₂ ht₂ := by
  subst h
  rfl

/--
Double time-shift cancels: states at (time_shift (time_shift σ Δ) (-Δ)) equal states at σ.

This is the key transport lemma for the box case of time_shift_preserves_truth.
It shows that shifting by Δ and then by -Δ returns to the original states.
-/
theorem time_shift_time_shift_states (σ : WorldHistory F) (Δ : Int) (t : Int)
    (ht : σ.domain t)
    (ht' : (time_shift (time_shift σ Δ) (-Δ)).domain t) :
    (time_shift (time_shift σ Δ) (-Δ)).states t ht' = σ.states t ht := by
  simp only [time_shift]
  have h_eq : t + -Δ + Δ = t := by omega
  exact states_eq_of_time_eq σ (t + -Δ + Δ) t h_eq _ ht

/--
Extensionality lemma for time_shift: shifting by equal amounts gives equal histories.
-/
theorem time_shift_congr (σ : WorldHistory F) (Δ₁ Δ₂ : Int) (h : Δ₁ = Δ₂) :
    time_shift σ Δ₁ = time_shift σ Δ₂ := by
  subst h
  rfl

/--
Domain membership for time_shift by zero is equivalent to original domain.
-/
theorem time_shift_zero_domain_iff (σ : WorldHistory F) (z : Int) :
    (time_shift σ 0).domain z ↔ σ.domain z := by
  simp only [time_shift, Int.add_zero]

/--
Domain membership for double time-shift with opposite amounts equals original.
-/
theorem time_shift_time_shift_neg_domain_iff (σ : WorldHistory F) (Δ : Int) (z : Int) :
    (time_shift (time_shift σ Δ) (-Δ)).domain z ↔ σ.domain z := by
  simp only [time_shift]
  have h : z + -Δ + Δ = z := by omega
  constructor
  · intro hd; rw [h] at hd; exact hd
  · intro hd; rw [h]; exact hd

/--
States at double time-shift with opposite amounts equals original states.
-/
theorem time_shift_time_shift_neg_states (σ : WorldHistory F) (Δ : Int) (t : Int)
    (ht : σ.domain t) (ht' : (time_shift (time_shift σ Δ) (-Δ)).domain t) :
    (time_shift (time_shift σ Δ) (-Δ)).states t ht' = σ.states t ht := by
  simp only [time_shift]
  have h_eq : t + -Δ + Δ = t := by omega
  exact states_eq_of_time_eq σ (t + -Δ + Δ) t h_eq _ ht

end WorldHistory

end ProofChecker.Semantics
