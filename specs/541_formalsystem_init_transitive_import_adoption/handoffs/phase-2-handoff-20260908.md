# Phase 2 Handoff — Task 541

- **Next action**: Phase 3 — add `import FormalSystem.Init` to the six mid-fan-out leaves,
  content-matched after the last existing `import` line (`OrderIsoReal.lean`'s block starts at
  line 42).
- **State**: missing count 456 -> **425** (drop of 31 across the two leaves' overlapping
  fan-outs of 17 and 19). Checker exits 1. Targeted build of the 34-target dependent set exits 0.
- **Key decisions**: the guard's build mode needs `-- build <targets>`; `-- <targets>` exits 77.
- **Deviations**: dependent set narrowed by three targets (two whole-tree roll-ups plus
  `FormalSystem.Automation.ProofStepExport`).
- **Pre-existing defect found, NOT introduced here**: `FormalSystem.Automation.ProofStepExport`
  (the `lake exe proof_extractor` root) fails to elaborate with three
  `Application type mismatch` errors at lines 1479/1496/1497 — `@theorem_flip_weakened`,
  `@theorem_app1_weakened` and `@b_combinator_weakened` are called with `(A := …) (B := …)`
  named arguments and a positional `Formula`, but each declaration's first explicit-under-`@`
  parameter is `{fc : FrameClass}`, so the positional lands in the wrong slot. Verified
  pre-existing by stashing this phase's two import lines and rebuilding that module alone:
  byte-identical errors. It sits outside the `FormalSystem` root closure (so `lake build` and
  `checkInitImports` both never see it) and is absent from
  `scripts/module-invariants-manifest.txt`, so C6 does not compile-check it either. Out of this
  task's scope (plan Non-Goals excludes out-of-closure modules); worth a follow-up task.
