# Implementation Summary: Resolve unpinned paper anchors (C15 gate)

- **Task**: 538 - resolve_unpinned_paper_anchors_c15_gate
- **Status**: [COMPLETED]
- **Date**: 2026-09-07
- **Plan**: `specs/538_resolve_unpinned_paper_anchors_c15_gate/plans/01_resolve-c15-paper-anchors.md`
- **Research**: `specs/538_resolve_unpinned_paper_anchors_c15_gate/reports/01_c15-anchor-resolution.md`
- **Type**: lean4 (no `.lean` file changed — see Scope below)

## Outcome

`bash scripts/check-module-invariants.sh` now exits 0 and reports **ALL CHECKS PASSED**, with
zero `FAIL` lines. C15 reads:

```
PASS  C15  all 52 paper-anchor citation(s) resolve against specs/paper-definitions-of-record.md
```

C15 was the sole failing group at the start of the task (`1 CHECK GROUP(S) FAILED`, one `FAIL`
line, `4 paper-anchor citation(s) resolve to nothing`), so this single edit restored the whole
invariant script to green.

## What changed

One file: `specs/paper-definitions-of-record.md`, +24 lines, purely additive.

**Four `LIVE-UNPINNED` rows** in the `KNOWN-ANCHORS` block, placed in the block's existing ASCII
sort (LIVE-UNPINNED rows before DANGLING rows):

| Anchor | Paper environment | Why `LIVE-UNPINNED` rather than manifest-pinned |
|---|---|---|
| `app:ObjectiveModality` | `\subsection{Objective Modality}%`, label on the following line | **Structurally unpinnable.** `resolve_env` (`scripts/check-paper-definitions.sh:161-172`) reads the environment name off the same line as the `\label{}` (line 166), so a sectioning label on its own line can never resolve. Same shape as the already-recorded `app:TaskSemantics`. |
| `app:drift` | `Tthm` | Pinnable in principle, useless in practice: the `Tthm` block carries only the statement, while the text `DriftFrame.lean` engages with (the `λ ≔ (v − w)/(x + y)` interpolation, the compactness/finite-intersection *Saturation* argument) sits in the `\begin{proof}` block *after* `\end{Tthm}`, which `resolve_env` does not capture. A pin would hash text the tree never quotes. |
| `cor:no-characterization` | `Cthm` | Cited by name only. |
| `lem:deterministic-singleton` | `Lthm` | Cited by name only; `StateSetTruth.lean` names its choice-free (⇒) direction but quotes no text. |

**One dated narrative subsection** under `## Recording provenance`:
`### Anchor classification (2026-09-07): four LIVE-UNPINNED rows for the C15 gate`, carrying the
same per-anchor table plus the citing sites.

## Scope

- **No `.lean` file was modified.** Every citing docstring was spot-checked against the live
  `.tex` and is faithful; no correction was needed. The three files in the task's declared
  `file_scope` (`Metalogic/Independence/{DriftFrame,RealTranslationFrame,StateSetTruth}.lean`)
  were read only. No `lake build` was therefore required.
- **No manifest row, `FILE_CHECKSUM`, `PINNED_COMMIT`, or `LINE_COUNT` sentinel was touched.**
- **No paper-side (`possible_worlds.tex`) edit**, and no cross-repo coordination.

## Corrections to the task description

The task description shipped a pre-computed classification that measurement contradicted on three
points:

1. **Four anchors, not three.** `app:ObjectiveModality` (cited at
   `FormalSystem/BaseLanguage/Axioms.lean:100`) entered the cited set with the `Axioms.lean`
   paper-name correspondence table, after the task was written. Fixing only the three named
   anchors would have left C15 red.
2. **Nothing is "LIVE BUT UNLABELLED".** All four resolve to live, non-commented `\label{}`
   targets, in the paper worktree *and* in the paper repository's `HEAD`:
   `app:ObjectiveModality` (worktree 1917 / HEAD 1898), `lem:deterministic-singleton` (3576/3557),
   `app:drift` (3705/3686), `cor:no-characterization` (3741/3722). None is `DANGLING`, so the
   plan's contingency branch (add a `DANGLING` row and fix the citation site) never fired.
3. **No appendix section is missing.** The `app:ObjectiveModality` appendix subsection exists; it
   is simply not of a shape `resolve_env` can pin.

The general lesson is the one already recorded as a memory candidate at plan time: a
classification shipped with a task description is a hypothesis with a timestamp, not input data.
The plan carried it as an explicit Scope Hypothesis on the measuring phase, which is what made the
measured set authoritative over the report.

## Verification

| Check | Result |
|---|---|
| `bash scripts/check-module-invariants.sh` | exit 0, `ALL CHECKS PASSED`, 0 `FAIL` lines |
| C15 specifically | `PASS`, all 52 cited anchors resolve |
| `.lean` files modified | none |
| `sorry` / vacuous definitions / new axioms introduced | none (no Lean source touched) |
| `FILE_CHECKSUM` / `PINNED_COMMIT` sentinels | unchanged |
| `KNOWN-ANCHORS` ASCII sort, LIVE-UNPINNED before DANGLING | preserved |

## Plan Deviations

- None (implementation followed plan).

## Reasoned Exclusions

The `scripts/check-paper-definitions.sh` drift wave — re-measured at **15 drifted definitions /
9 dangling anchors** — was excluded, as the plan's Non-Goals declared. Evidence:

- `grep -c 'check-paper-definitions' scripts/check-module-invariants.sh` returns `0`: the
  invariant script never invokes it.
- `.github/workflows/ci.yml` runs only `leanprover/lean-action@v1` (build/test/lint) plus a
  `Report results` step; it invokes neither script.
- C15 resolves citations against `specs/paper-definitions-of-record.md`, never against the live
  `.tex`, by documented design — paper drift cannot turn C15 red.
- Seven of the nine dangling anchors (`def:BLplus-semantics`, `def:BLplus-defined`,
  `thm:BLplus-PastFuture`, `thm:BLplus-NextPrevious`, `def:TMplus-f`, `def:TMplus-d`,
  `def:TMplus-c`) are the declared scope of the open fragment-removal / BX-rename work, whose
  description names the three `def:TMplus-*` renames and the Past/Future fragment removal
  explicitly. Absorbing them here would duplicate and pre-empt that task.

The full table with the same evidence is recorded under Phase 3 in the plan.
