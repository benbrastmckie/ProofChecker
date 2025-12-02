import ProofChecker.Semantics.TaskModel
import ProofChecker.Semantics.WorldHistory
import ProofChecker.Syntax.Formula

/-!
# Truth - Truth Evaluation in Task Semantics

This module defines truth evaluation for TM formulas in task models.

## Main Definitions

- `truth_at`: Truth of a formula at a model-history-time triple
- Notation: `M, τ, t, ht ⊨ φ` for `truth_at M τ t ht φ`

## Main Results

- Basic truth lemmas (e.g., `bot` is always false)
- Truth evaluation examples

## Implementation Notes

- Truth is defined recursively on formula structure
- Modal box quantifies over all world histories at current time
- Temporal past/future quantify over earlier/later times in current history
- Times are Int for MVP simplicity

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - Truth evaluation specification
* [Formula.lean](../Syntax/Formula.lean) - Formula syntax
* [TaskModel.lean](TaskModel.lean) - Task model structure
-/

namespace ProofChecker.Semantics

open ProofChecker.Syntax

variable {F : TaskFrame}

/--
Truth of a formula at a model-history-time triple.

Given:
- `M`: A task model (frame + valuation)
- `τ`: A world history (function from times to states)
- `t`: A time point
- `φ`: A formula

Returns whether `φ` is true at this semantic configuration.

The evaluation is defined recursively on formula structure:
- Atoms: true iff valuation says so at current state
- Bot (⊥): always false
- Implication: standard material conditional
- Box (□): true iff φ true at all world histories at time t
- Past (P): true iff φ true at all past times in current history
- Future (F): true iff φ true at all future times in current history
-/
def truth_at (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t) :
    Formula → Prop
  | Formula.atom p => M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => truth_at M τ t ht φ → truth_at M τ t ht ψ
  | Formula.box φ => ∀ (σ : WorldHistory F) (hs : σ.domain t), truth_at M σ t hs φ
  | Formula.past φ => ∀ (s : Int) (hs : τ.domain s), s < t → truth_at M τ s hs φ
  | Formula.future φ => ∀ (s : Int) (hs : τ.domain s), t < s → truth_at M τ s hs φ

-- Note: We avoid defining a notation for truth_at as it causes parsing conflicts
-- with the validity notation in Validity.lean. Use truth_at directly.

namespace Truth

/--
Bot (⊥) is false everywhere.
-/
theorem bot_false {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t} :
    ¬(truth_at M τ t ht Formula.bot) := by
  intro h
  exact h

/--
Truth of implication is material conditional.
-/
theorem imp_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ ψ : Formula) :
    (truth_at M τ t ht (φ.imp ψ)) ↔ ((truth_at M τ t ht φ) → (truth_at M τ t ht ψ)) := by
  rfl

/--
Truth of atom depends on valuation at current state.
-/
theorem atom_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (p : String) :
    (truth_at M τ t ht (Formula.atom p)) ↔ M.valuation (τ.states t ht) p := by
  rfl

/--
Truth of box: formula true at all histories at current time.
-/
theorem box_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.box) ↔
      ∀ (σ : WorldHistory F) (hs : σ.domain t), (truth_at M σ t hs φ) := by
  rfl

/--
Truth of past: formula true at all earlier times in history.
-/
theorem past_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.past) ↔
      ∀ (s : Int) (hs : τ.domain s), s < t → (truth_at M τ s hs φ) := by
  rfl

/--
Truth of future: formula true at all later times in history.
-/
theorem future_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.future) ↔
      ∀ (s : Int) (hs : τ.domain s), t < s → (truth_at M τ s hs φ) := by
  rfl

end Truth

end ProofChecker.Semantics
