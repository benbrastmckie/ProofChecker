# Implementation Summary: CI linter and invariant gates

- **Task**: 529 - WAVE 5 (publication infrastructure): turn on tests and Mathlib environment linters in CI, and close the review's gaps in `check-module-invariants.sh`
- **Status**: [COMPLETED]
- **Started**: 2026-09-04T06:43:46Z
- **Completed**: 2026-09-04T15:20:00Z
- **Effort**: ~8.5 hours across 11 phases
- **Dependencies**: None (external)
- **Artifacts**: plans/01_ci-linter-invariant-gates.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Turned on the Lean test suite and the Mathlib/Batteries environment-linter suite in CI
(`ci.yml`), and closed five gaps in `scripts/check-module-invariants.sh` and
`scripts/readme-lint.sh` that let the source review's Critical findings pass unnoticed. All 11
plan phases closed `[COMPLETED]` or `[COMPLETED WITH EXCLUSIONS]`; the two exclusion phases and
the one authorized deviation are recorded below. The task's two headline mechanisms both landed
on a materially better design than the plan originally sketched: `scripts/nolints.json`
(Batteries/Mathlib's standard grandfathering file) replaced a lint-args narrowing that turned out
to be structurally impossible, and a live, validated textual approximation replaced a
would-have-been-static dupNamespace count.

## What Changed

- `.github/workflows/ci.yml` -- deleted the `[ci]` commit-message gate; `test: true`, `lint: true`
  (no `lint-args`, made unnecessary by `scripts/nolints.json`); added `lint-status` to the report
  step.
- `lakefile.lean` -- `lintDriver := "batteries/runLinter"`; 9 `lean_exe` docstrings rewritten to
  drop task citations; new `lean_exe checkInitImports` block.
- `scripts/nolints.json` -- new. Grandfathers the 307 pre-existing Batteries env_linter findings
  present when generated (`lake exe runLinter --update FormalSystem`).
- `scripts/check-module-invariants.sh` -- new C16 (env_linter batch, nolints.json-aware blocking
  half; live textual dupNamespace approximation, reporting-only), C17 (dead-declaration scan,
  reporting-only), C18 (paragraph duplication across the four top-level READMEs, reporting-only),
  C19 (docstring-coverage floor, reporting-only, refined G-12 heuristic); C9 widened to
  `lakefile.lean`/`README.md`/`scripts/`; C14 widened (interposed word + `schema` terminal, plus a
  new `covers` precision guard); header `# Checks:` inventory and Usage/Companion-files sections
  updated throughout.
- `scripts/readme-lint.sh` -- Check 4 now compares a present `Last verified` stamp against the
  directory's last commit date (reporting-only `STALE DATE` warning).
- `FormalSystem/Semantics/{TaskFrame,Truth,WorldHistory,FrameProperty,BLTruth}.lean` -- one
  `assert_not_exists` line each (G-15), asserting the lower semantic layer cannot reach the proof
  system.
- `FormalSystem/Init.lean` -- new. Intended root file for `FormalSystem`, imports `Mathlib.Init`
  and `Mathlib.Tactic.Common`.
- `scripts/CheckInitImports.lean` -- new. Reports which `FormalSystem` modules do not yet
  transitively import `FormalSystem.Init` (baseline: 434, not fixed here).
- `scripts/module-invariants-manifest.txt` -- new entry for `FormalSystem.Init` (newly-unreachable
  live module, per C6's rot-guard convention).
- `FormalSystem/ProofSystem.lean`, `docs/project-info/implementation-status.md`,
  `docs/user-guide/examples.md` -- three stale axiom-count claims corrected (21/14 -> 45; the
  third, in `ProofSystem.lean`, was found by the widened C14 scan, not named by the plan).
- `scripts/run_dataset_generation.sh`, `scripts/typst-machine-appendix.sh`,
  `scripts/typst-status-counts.sh`, `scripts/typst-sync-check.sh` -- 7 task-number citations
  removed (found by the widened C9 scan; the plan's research pass measured 0 in `scripts/*.sh`,
  the actual count was 7).

## Decisions

- **`scripts/nolints.json` over `lint-args` narrowing** (Phase 2). The plan's lint-args-narrowing
  design proved structurally impossible: `runLinter`'s CLI has no linter-selection flag at all
  (always runs every registered env_linter), and `simpNF` has no `linter.X`-registered option
  reachable via the builtin/text-linter path either. `nolints.json` -- the standard
  Batteries/Mathlib grandfathering mechanism -- achieves the plan's actual goal (`lint: true`
  landing) via a stronger mechanism: the full six-linter env_linter set stays live as a
  regression gate, rather than being permanently narrowed to two linters.
- **Live textual dupNamespace approximation over a static count** (Phases 3 and 5, split across
  two commits after a mid-flight correction -- see Deviations). A hardcoded count in this script
  is the exact defect class C14 (and the two/three stale-document fixes in Phase 6) exists to
  catch. The final embedded-Python check tracks `namespace`/`section`/`end` nesting and accounts
  for a `structure`/`class`'s auto-generated field projections and `.mk` constructor -- validated
  to reproduce the real linter's 14 `ChronicleTypes.lean` findings exactly, at the same lines.
- **C19's docstring-coverage heuristic refined, with user authorization** (Phase 9). G-12's
  unrefined heuristic measured 89.40%, under the 90% floor -- the plan's own STOP condition.
  Escalated rather than resolved unilaterally; the user authorized crediting an enclosing `/-!`
  section comment (a blind spot the heuristic's own documentation already anticipated), applied
  once as a precisely-specified rule and validated in both directions (an early draft over-
  credited; fixed by also ending a section's scope at the next already-documented declaration).
  Refined figure: 92.34%, within 0.5 points of research's own 92.8%.

## Plan Deviations

- **Phase 1**: `simpNF` (1 finding) and `dupNamespace` (14 findings, only measurable via a
  different tool than the plan's own Phase 1 task specified) are both real, unrelated,
  pre-existing gaps -- not zero as Contingency #1 initially assumed. Superseded Contingency #3
  (which the gaps would otherwise have triggered) via the `nolints.json` mechanism discovered in
  Phase 2.
- **Phase 2**: no `lint-args` lands in `ci.yml`; superseded by `scripts/nolints.json`. See
  Decisions above.
- **Phase 3**: C16's blocking half is the full env_linter batch (nolints.json-aware), not a
  simpNF/dupNamespace pair. dupNamespace was initially a static count (rebuild-cost constraint);
  the team lead objected to the static count specifically after this phase committed, and it was
  replaced with a live, validated textual check in Phase 5.
- **Phase 4**: `BLValidity.lean` excluded from the `assert_not_exists` targets (a third exclusion
  beyond the plan's two) after a real build failure showed it transitively imports the
  `ProofSystem` seam via `Validity.lean` -- a Scope Hypothesis gap the plan's direct-import-only
  grep could not see.
- **Phase 5**: `scripts/*.sh` actually had 7 task-number citations, not the 0 the plan's Scope
  Hypothesis measured; all 7 cleared. The Phase 3 dupNamespace static-count follow-up landed here.
- **Phase 6**: a third genuinely stale claim (`FormalSystem/ProofSystem.lean:21`) found beyond the
  plan's two named documents; a new `covers` precision guard added for a genuine subset-claim
  false positive (`ProofSearch/Core.lean:697`) the existing `axiom` guard did not exclude.
- **Phase 9**: the G-12 heuristic was refined with user authorization; see Decisions above.
- **Phase 10**: `FormalSystem/Init.lean` has one extra CSLib-analogue import, not two, and
  `CheckInitImports.lean`'s exceptions list needs one entry, not two -- both plan-parenthetical
  imprecisions found by reading CSLib's actual source directly, confirmed empirically.
- **Phase 11**: `check-module-invariants.sh` (both modes) exits 1, not 0 -- solely from the
  pre-existing C15 gap. No `lint-args` narrowing is present in `ci.yml` -- correctly so, per the
  Phase 2 decision.

## Verification

- Build: Success (`lake build`, 2591 jobs, exit 0)
- Tests: Passed (`lake test`, exit 0)
- Files verified: Yes -- every new/modified file confirmed to exist and build/lint/parse cleanly
  at the point of its own phase, and re-confirmed in Phase 11's full acceptance run

## Impacts

- CI now runs on every push/PR (not gated behind a `[ci]` commit-message marker) with the Lean
  test suite and the Batteries environment-linter suite both live, catching any *new* violation
  in either from the moment this lands, without requiring the pre-existing debt to be cleared
  first.
- `scripts/check-module-invariants.sh` gained four new checks (C16-C19) and two widened checks
  (C9, C14), closing the specific gaps the source review's Critical findings exploited: an
  environment-linter regression gate, a dead-declaration census, a paragraph-duplication census,
  a docstring-coverage floor, and a wider net for task-number citations and stale axiom-count
  claims.
- `scripts/nolints.json` and the `FormalSystem.Init`/`CheckInitImports` mechanism are both new,
  checked-in artifacts that a future contributor will encounter; both are documented at the point
  of definition (the file's own header comments) and in this summary.

## Follow-ups

- **`scripts/nolints.json`'s 307-entry grandfathering commitment.** This is a large baseline
  (unusedArguments=217, docBlame=51, defsWithUnderscore=33, tacticDocs=4, simpNF=1,
  structureInType=1) accepted wholesale to unblock `lint: true`, not audited or triaged
  declaration-by-declaration. A follow-up task should decide whether and how to burn it down
  (starting with the smallest categories -- simpNF, structureInType, tacticDocs -- is the
  cheapest path) rather than let it stand indefinitely as an ever-growing exemption list.
- **`dupNamespace`'s 14 real findings** (`FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
  -- `structure Chronicle` nested inside `namespace ...Chronicle`, double-namespacing every
  field). The fix is a rename, touching every `Chronicle.*` projection site across the tree -- a
  real refactor, not attempted here (this task's scope was wiring the gate, not fixing what it
  finds).
- **`simpNF`'s 1 real finding** (`FormalSystem.Metalogic.Decidability.BiLasso.Extraction.length_range_map`,
  "simp can prove this" -- likely a one-line fix, but genuinely out of this task's scope).
- **The three low-coverage keyword categories from C19's per-keyword breakdown**: `class` 16.3%,
  `instance` 57.6%, `lemma` 55.6% (measured against the unrefined G-12 figures). Real, small-
  sample documentation gaps worth a dedicated documentation pass.
- **The ~430-file `FormalSystem.Init` import rewrite** that would make `CheckInitImports`'s
  baseline violation count (434) go to zero. Explicitly out of this task's scope (Non-Goal); the
  mechanism plus the recorded baseline is this task's deliverable.
- **`specs/paper-definitions-of-record.md`'s C15 gap** (3 unresolved paper-anchor citations:
  `app:drift`, `cor:no-characterization`, `lem:deterministic-singleton`, all traced to a prior
  task's `FormalSystem/Metalogic/Independence/` additions). Pre-existing at this task's starting
  commit and unrelated to its scope; this is the one item keeping
  `bash scripts/check-module-invariants.sh` from printing ALL CHECKS PASSED. Fixing it requires
  paper-content knowledge (classifying each anchor as LIVE-UNPINNED or DANGLING) outside this
  task's authority.
- **`specs/ROADMAP.md`'s "Check grounding" line** now understates the invariant-gate coverage
  (names only C5 and C9; this task added C16-C19 and widened C9/C14). No `roadmap_flag` was set
  on this dispatch, so this was recorded rather than acted on, per the plan's own Overview note.
- **"CI green on a plain push" is inferred, not observed** -- no push is permitted under this
  task's own constraints (`.claude/rules/pr-prohibition.md`). Every local equivalent (`lake
  build`, `lake test`, `lake check-lint`, plain `lake lint`, both invariants-script modes, a YAML
  parse of `ci.yml`) passed in Phase 11's acceptance run; this is the one residual acceptance risk
  the plan itself named in advance (Risk R7).

## References

- Plan: `specs/529_ci_linter_and_invariant_gates/plans/01_ci-linter-invariant-gates.md`
- Progress files: `specs/529_ci_linter_and_invariant_gates/progress/phase-{1..11}-progress.json`
- Research report: `specs/529_ci_linter_and_invariant_gates/reports/01_ci-linter-invariant-gates.md`
