# Phase 3+4 handoff — task 573

- **Next action**: Phase 5 (`FormalSystem/StarLanguage/Embedding.lean`).
- **State**: `StarAxiom` (17 constructors, count confirmed against the Scope Hypothesis) with
  `StarAxiom.minFrameClass` and four `rfl` pins; `StarDerivationTree` (seven rules), `⊢⋆[fc]`,
  `StarDerivable`, `.mono`, `lift`/`height`/`ofWeakeningNil`/`height_ofWeakeningNil_lt`/
  `mp_height_gt_left`/`mp_height_gt_right`, `stabNecessitationOfPlus`, three smoke tests.
  Scoped build of `FormalSystem.StarLanguage` green (691 jobs).
- **Decisions / exclusion**: general `⊡`-necessitation is NOT derivable in TM⋆ — MS arrives only
  through `ofBase`, at `ofPlus` instances. Landed as `stabNecessitationOfPlus` under a distinct
  name; Phase 4 is `[COMPLETED WITH EXCLUSIONS]` with the record in the plan.
- **Concurrency note**: task 572 is editing `FormalSystem/Semantics/StarTruth.lean` and
  `Semantics.lean` in the same worktree. Do not edit those files; keep commits file-scoped.
