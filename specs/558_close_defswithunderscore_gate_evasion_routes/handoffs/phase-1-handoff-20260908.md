# Phase 1 handoff — baseline measurement and exemption-set lock

## Immediate next action
Phase 2: add `ENFORCE_C26` and the tree-wide textual snake_case scanner to
`scripts/check-module-invariants.sh`, placed after the C25 block.

## Measured state (authoritative; supersedes the plan's Opening Measurement)

| Reading | Measured |
|---|---|
| public snake_case `def`/`abbrev` outside `Boneyard/` | 0 |
| `private` snake_case `def`/`abbrev` outside `Boneyard/` | 0 |
| `def`/`abbrev`/`instance` names ending `_N` / `_mathlib` | 0 |
| trailing-underscore-only names (must NOT be flagged) | 2 — `MonadicFormula.true_`, `MonadicFormula.false_` |
| snake_case `instance` declarations | 23, **all `thmInfo` by elaboration** (probed all 23, zero NOT FOUND) |
| in-source `nolint` attribute sites outside `Boneyard/` | 5 sites covering 7 declarations |
| `nolint` attributes under `Tests/` | 0 |
| next free check ID | C26 (script has B0, C1-C25, C9D; zero occurrences of `C26`) |

## nolint inventory (allow-list seed)
- `FormalSystem/Automation/ProofSearch/Core.lean:222` `@[nolint structureInType]` -> `MembershipWitness`
- `FormalSystem/Automation/ProofSearch/Core.lean:1280` `attribute [nolint docBlame] iddfsSearch.iterate`
- `FormalSystem/Automation/ProofSearch/Strategies.lean:67` `attribute [nolint docBlame] PriorityQueue.insert.insertSorted`
- `FormalSystem/Automation/ProofSearch/Strategies.lean:192` `attribute [nolint docBlame] bestFirstSearch.searchLoop`
- `FormalSystem/Automation/Tactics/UserTactics.lean:270` `attribute [nolint defsWithUnderscore]` -> `tacticApply_axiom`, `tacticModal_t`, `tacticAssumption_search`

## runLinter target measurement (input to Phase 4)
`lake exe runLinter <ModuleName>` accepts any module name — library root or `lean_exe` root.
Sweep over all 15 lakefile roots with the tree already built: **44 s wall clock**.

Findings per root: FormalSystem 0 - ProofStepExport 0 - BenchmarkAnchors 0 -
TableauProofStepPipeline 0 - ProofFirstExporter 0 - DatasetValidator 1 - CheckInitImports 1 -
EnumBenchmark 4 - TraceExporter 5 - BenchmarkOracle 9 - TableauBridge 12 -
MachineAppendixExport 16 - DatasetExport 32 - BimodalTest 85. **Total non-`FormalSystem`: 179.**

`defsWithUnderscore` specifically: DatasetExport **20**, BimodalTest **36**, every other root 0.

## Key decision recorded in Phase 1
The 20 DatasetExport `defsWithUnderscore` findings are auto-generated **structure field
projections** of `DatasetRecord` (data-valued, so `defnInfo`). A textual scan cannot separate
them from the 188 textually snake_case structure fields tree-wide, the overwhelming majority of
which are Prop-valued and correctly named — `runLinter FormalSystem` reports 0 on all of them.
Field-shaped violations are therefore assigned to the **elaboration-based root widening**
(Phase 4), reporting-only, not to C26's textual scan. C26's textual scan covers declared
`def`/`abbrev` names only; `instance` is exempt on the measured `thmInfo` evidence.

## Deviations
None so far. Plan counts for nolint sites were 4/7; measured 5/7 — the measurement wins,
as the plan's Scope Hypothesis directs.
