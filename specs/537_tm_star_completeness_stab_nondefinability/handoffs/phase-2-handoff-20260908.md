# Phase 2 handoff — task 537

- **Done**: the four countermodel producers now expose their frame's determinism as an extra
  existential binder, with witnesses from two new lemmas hosted beside their frames:
  `Algebraic.multiFamTaskFrameGen_deterministic` / `bundleFlowFrame_deterministic`
  (`Metalogic/Algebraic/FlowFrame.lean`) and `multiFamTaskFrame_deterministic` /
  `zTaskFrameV2_deterministic` (`WeakCanonical/IntegerModel/ReynoldsBridge.lean`).
  Full `lake build` clean; the four engines' `#print axioms` still report exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Scope hypothesis reconciled**: four producers (as asserted) and **four** destructuring call
  sites, not five — `BXCanonical/DiscreteCarrierProbe.lean` mentions `countermodel_discrete`
  only in prose.
- **Next action**: Phase 3 (deterministic-hypothesis engines) and Phase 4 (erasure, drafted).
