import ProofChecker.Syntax.Formula

/-!
# Axioms - TM Axiom Schemata

This module defines the 8 axiom schemata for bimodal logic TM (Tense and Modality).

## Main Definitions

- `Axiom`: Inductive type characterizing valid axiom instances
- 8 axiom constructors: `modal_t`, `modal_4`, `modal_b`, `temp_4`, `temp_a`, `temp_l`, `modal_future`, `temp_future`

## Axiom Schemata

The TM logic includes:

### S5 Modal Axioms (metaphysical necessity □)
- **MT** (Modal T): `□φ → φ` - what is necessary is true (reflexivity)
- **M4** (Modal 4): `□φ → □□φ` - necessary truths are necessarily necessary (transitivity)
- **MB** (Modal B): `φ → □◇φ` - truths are necessarily possible (symmetry)

### Temporal Axioms (future F, past P)
- **T4** (Temporal 4): `Fφ → FFφ` - future of future is future (transitivity)
- **TA** (Temporal A): `φ → FPφ` - the present was in the past of the future
- **TL** (Temporal L): `always φ → FPφ` - perpetuity implies recurrence

### Modal-Temporal Interaction Axioms
- **MF** (Modal-Future): `□φ → □Fφ` - necessary truths remain necessary in future
- **TF** (Temporal-Future): `□φ → F□φ` - necessary truths were/will-be necessary

## Implementation Notes

- Each constructor represents an axiom schema (quantified over all formulas)
- The `Axiom` type is a predicate on `Formula`, not a separate type
- Axiom instances are used in the `Derivable` relation

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - TM logic specification section
* [Formula.lean](../Syntax/Formula.lean) - Formula type definition
-/

namespace ProofChecker.ProofSystem

open ProofChecker.Syntax

/--
Axiom schemata for bimodal logic TM.

A formula `φ` is an axiom if it matches one of the 8 axiom schema patterns.
Each constructor takes a formula parameter representing the schema instantiation.
-/
inductive Axiom : Formula → Prop where
  /--
  Modal T axiom: `□φ → φ` (reflexivity).

  What is necessarily true is actually true.
  Semantically: if φ holds at all possible worlds, it holds at the actual world.
  -/
  | modal_t (φ : Formula) : Axiom (Formula.box φ |>.imp φ)

  /--
  Modal 4 axiom: `□φ → □□φ` (transitivity).

  If something is necessary, it is necessarily necessary.
  Semantically: the accessibility relation is transitive.
  -/
  | modal_4 (φ : Formula) : Axiom ((Formula.box φ).imp (Formula.box (Formula.box φ)))

  /--
  Modal B axiom: `φ → □◇φ` (symmetry).

  Truths are necessarily possible.
  Semantically: the accessibility relation is symmetric.
  -/
  | modal_b (φ : Formula) : Axiom (φ.imp (Formula.box φ.diamond))

  /--
  Temporal 4 axiom: `Fφ → FFφ` (temporal transitivity).

  If something will always be true, it will always be true that it will always be true.
  -/
  | temp_4 (φ : Formula) : Axiom ((Formula.future φ).imp (Formula.future (Formula.future φ)))

  /--
  Temporal A axiom: `φ → F(sometime_past φ)` (temporal connectedness).

  If something is true now, at all future times there exists a past time where it was true.
  Semantically: if φ at t, then for all s > t, there exists r < s where φ at r (namely, t).

  Note: Uses existential `sometime_past` (¬P¬φ) not universal `past` (Pφ).
  -/
  | temp_a (φ : Formula) : Axiom (φ.imp (Formula.future φ.sometime_past))

  /--
  Temporal L axiom: `Gφ → GHφ` (perpetuity).

  If something is always true in the future, then in all future times
  it was always true in the past.

  In our notation:
  - `future φ` = Gφ (for all future times, φ)
  - `past φ` = Hφ (for all past times, φ)

  So this axiom is: `Gφ → G(Hφ)` = `future φ → future (past φ)`

  Note: This axiom requires specific frame conditions related to task semantics
  to be valid. The proof may rely on task compositionality constraints.
  -/
  | temp_l (φ : Formula) : Axiom ((Formula.future φ).imp (Formula.future (Formula.past φ)))

  /--
  Modal-Future axiom: `□φ → □Fφ` (modal-future interaction).

  Necessary truths remain necessary in the future.
  -/
  | modal_future (φ : Formula) : Axiom ((Formula.box φ).imp (Formula.box (Formula.future φ)))

  /--
  Temporal-Future axiom: `□φ → F□φ` (temporal-modal interaction).

  Necessary truths will always be necessary.
  -/
  | temp_future (φ : Formula) : Axiom ((Formula.box φ).imp (Formula.future (Formula.box φ)))

end ProofChecker.ProofSystem
