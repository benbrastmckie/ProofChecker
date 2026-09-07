# Phase 1 handoff (2026-09-07)

## Immediate next action
Phase 2: insert four `LIVE-UNPINNED` rows in the `KNOWN-ANCHORS` block of
`specs/paper-definitions-of-record.md` (block runs lines 1472-1494) plus a dated narrative
subsection under `## Recording provenance` (insert before `### Rename absorption (2026-09-02)`).

## Measured state
`bash scripts/check-module-invariants.sh` -> `1 CHECK GROUP(S) FAILED`; the only `FAIL` line is
C15: `4 paper-anchor citation(s) resolve to nothing`. Measured unresolved set (matches research
exactly, four not three):

| Anchor | Paper label (worktree) | Env | HEAD | Citing sites |
|---|---|---|---|---|
| `app:drift` | line 3705 | `Tthm` (label on `\begin` line) | line 3686 | DriftFrame.lean, RealTranslationFrame.lean |
| `app:ObjectiveModality` | line 1917 | `\subsection{...}%` with label on the NEXT line | line 1898 | BaseLanguage/Axioms.lean:100 |
| `cor:no-characterization` | line 3741 | `Cthm` | line 3722 | Independence/README.md, DriftFrame.lean |
| `lem:deterministic-singleton` | line 3576 | `Lthm` | line 3557 | RealTranslationFrame.lean, StateSetTruth.lean |

All four LIVE in both the paper worktree and paper `HEAD`. None DANGLING; the contingency branch
in the plan's Rollback section does not fire.

## Key decisions
- `app:ObjectiveModality` is structurally unpinnable: `resolve_env`
  (`scripts/check-paper-definitions.sh:161-172`) reads the environment name off the same line as
  `\label{}` (line 166), so a `\subsection` label on its own line can never resolve.
- `app:drift` is pinnable in principle but a pin would be useless: the `Tthm` block holds only the
  statement; the text DriftFrame.lean actually discusses (the `λ := (v-w)/(x+y)` interpolation, the
  finite-intersection/compactness Saturation argument) is in the `\begin{proof}` block AFTER
  `\end{Tthm}`, which `resolve_env` does not capture.
- `cor:no-characterization` and `lem:deterministic-singleton` are cited by name only.

## Deviations
None.
