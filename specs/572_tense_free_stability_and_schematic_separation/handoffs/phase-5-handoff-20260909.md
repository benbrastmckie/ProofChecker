# Phase 4-5 handoff (task 572)

## Immediate next action

Phase 6: documentation, indices, and the full gate.

## State

`FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` builds green:

- imports `FormalSystem.Semantics.StarStateLocal`
- `fn_sentDet_atom` is **deleted**; `fn_sentDet_stateLocal (φ) (hφ : φ.StateLocal)` replaces it
- `fn_separates` strengthened to `(∀ φ, φ.StateLocal → FN.StarValidOn (sentDet φ)) ∧ ¬ FN.Deterministic`
- `fn_sentDet_bounds (p : Atom)` added — the two-sided bound as one object
- `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` byte-for-byte unchanged
- module docstring Main Results and the two schematic-reading paragraphs updated

`grep -rn 'fn_sentDet_atom' FormalSystem/ Tests/` now hits only three markdown files, which are
Phase 6's work: `Metalogic/Independence/README.md:64`, `StarLanguage/README.md:59,83,91`.

Phase 5 is `[COMPLETED WITH EXCLUSIONS]`: zero widenings outside Phase 4, table in the plan.

## Measured axiom sets

`fn_sentDet_stateLocal`, `fn_separates`, `fn_sentDet_bounds` — all
`[propext, Classical.choice, Quot.sound]`, matching the retired `fn_sentDet_atom`.

## Concurrency note

`FormalSystem/Semantics/StarNonValidities.lean` is being edited concurrently by the L⋆
proof-theory work and was transiently red mid-phase. It is green again; do not edit it here.
