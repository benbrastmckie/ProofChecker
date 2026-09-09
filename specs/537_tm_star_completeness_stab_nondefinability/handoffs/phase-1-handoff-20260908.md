# Phase 1 handoff — task 537

- **Done**: `FormalSystem/Metalogic/Deterministic/Validity.lean` + subtree aggregator
  `FormalSystem/Metalogic/Deterministic.lean`, registered in `FormalSystem/Metalogic.lean`.
  Landed: `DetSat`, `ValidDetIn`, `PlusValidDetIn`, `DeterminedValid`, `DeterminedSat`,
  `PlusValidDeterminedIn`, `deterministic_determinedValid`, `determinedSat_of_detSat`,
  `determinedValid_not_deterministic` (strictness via `F0`), four monotonicity lemmas and six
  binder-shape adapters. Scoped build clean.
- **Next action**: Phase 2 — widen the four countermodel producers with a `Deterministic`
  existential binder.
- **Key decision**: the determinism lemmas for the engines' frames will be hosted at their
  frames' definition sites (`Algebraic/FlowFrame.lean`, `WeakCanonical/.../ReynoldsBridge.lean`)
  rather than in a new `Deterministic/Frames.lean`, because the countermodel producers that
  consume them sit *below* `Metalogic/Deterministic/` in the import order.
- **Deviations**: recorded inline on the Phase 1 checklist.
