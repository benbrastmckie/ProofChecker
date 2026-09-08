# Implementation Summary: Task #558

- **Task**: 558 - Close the `defsWithUnderscore` gate evasion routes
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T09:20:00Z
- **Completed**: 2026-09-08T11:35:00Z
- **Effort**: ~2.5 hours
- **Dependencies**: 555 (completed), 557 (completed)
- **Artifacts**: plans/01_close-gate-evasion-routes.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`defsWithUnderscore` had reopened three times, the third time invisibly: every standing gate was
green while real violations existed, because each of four routes produces *no linter finding* for
a finding-counting gate to count. This task added the standing gate that does not inherit
`runLinter`'s observation model — **C26** in `scripts/check-module-invariants.sh`, a repo-local
textual scan plus an in-source `nolint` attribute inventory — and widened C16's linter target
from the single `FormalSystem` root to every root declared in `lakefile.lean`, reporting-only on
a measurement. All four routes were negative-tested, each observing both a printed `FAIL` line
and a non-zero shell exit, then a restore and a re-observed `PASS` with exit 0. No `.lean` file
was changed permanently; every negative-test seed was reverted.

## What Changed

- `scripts/check-module-invariants.sh` — new `ENFORCE_C26` flag and C26 check in two halves;
  new `ENFORCE_C16_ROOTS` flag and C16 second half (the widened, reporting-only env_linter sweep
  over every lakefile root); the `lakefile.lean` root scrape hoisted to one site with two
  consumers (C16's widened half and C25), extended to `lean_lib` roots alongside `lean_exe` ones.
- `scripts/nolint-attribute-allowlist.txt` — new companion file, seeded from a live inventory:
  7 declarations across 5 attribute sites, each carrying its linter and its reason.
- `docs/development/NAMING_CONVENTION_DEVIATION.md` — one appended section mapping each of the
  four evasion routes to the gate that now closes it and the residual it does not cover. Verified
  append-only: `git diff` shows 63 insertions and **zero** deletions.
- `docs/development/MODULE_INVARIANTS.md` — C26 check-table row, a companion-file subsection for
  the allow-list with its admission bar, an `ENFORCE_C16_ROOTS` entry beside the existing
  `ENFORCE_C9_DOCS` live example, and the four-negative-test record in "Adding a Check".

## Decisions

- **`instance` is exempt from the textual scan, on elaboration evidence rather than taste.** All
  23 live snake_case `instance` declarations were probed against the built oleans; every one is
  recorded by Lean as a `thmInfo`, not a `defnInfo` — they are `Prop`-valued, which is exactly
  why the upstream linter never fires on them and why snake_case is correct for them. A scan that
  did not exempt them would have shipped red on 23 conformant names.
- **Structure fields are excluded from the textual half and assigned to the elaboration-based
  sweep.** Lean turns each field into a projection `def`, so a data-valued underscored field
  genuinely is a violation — 20 live ones exist, all projections of one structure in an
  out-of-closure module. But 188 fields tree-wide are textually snake_case and the great majority
  are `Prop`-valued, hence theorems, hence correct: `runLinter FormalSystem` reports zero on all
  of them. `Prop`-ness is not decidable from source text, so flagging fields textually would mean
  188 findings to catch 20.
- **The naming rule flags an underscore anywhere but the trailing position**, deliberately not
  inheriting Mathlib's `_1`/`_2`/`_mathlib` skip. The trailing carve-out is required, not a
  softening: `true`/`false` are keywords and two live names disambiguate by suffix.
- **The C16 widening ships reporting-only**, on a measurement taken before the decision: the
  widened scope carries 179 pre-existing findings across 10 of 14 non-`FormalSystem` roots
  (BimodalTest 85, DatasetExport 32, MachineAppendixExport 16, FormulaMutator 14, TableauBridge
  12, BenchmarkOracle 9, TraceExporter 5, EnumBenchmark 4, DatasetValidator 1, CheckInitImports
  1), 56 of them `defsWithUnderscore`. Enforcing it would hold the gate hostage to a burndown
  this task does not own; abandoning it would leave the elaboration-only shapes uninstrumented.
  No existing `ENFORCE_` flag was flipped to 0.
- **Roots are built before they are linted.** `lake exe runLinter <Module>` builds the runLinter
  *executable*, not the module named; the module is read back from its `.olean`. This was caught
  by the route-1 negative test, not reasoned about in advance — see below.

## Plan Deviations

- **Phase 2** altered: `instance` is *excluded* from C26's kinds rather than included subject to
  Phase 1's answer, and structure fields are excluded too, both with the measurement recorded at
  the exemption site in the script.
- **Phase 4** altered: rather than parameterizing C25's scraper in place, the scrape was *hoisted*
  to a single site above C16 (which runs earlier in the script) and C25 now consumes it. The
  plan's "keep one scraping site" constraint is satisfied; the location differs.
- Phase 1 measured 5 nolint attribute sites covering 7 declarations, against the plan's
  provisional 4 sites / 7 declarations. The measurement won, as the plan's Scope Hypothesis
  directs.
- Phase 5: the restore-and-re-`PASS` half of routes 2, 3 and 4 was observed under `--no-build`
  (C26 is textual and needs no oleans); every `FAIL` observation for routes 1, 3 and 4 was a full
  run, which is where the C1/C16/C25 contrast lives, and Phase 6 closed on a full run.

## Verification

- Build: Success — `lake build` exit 0, 2615 jobs, via `lake-build-guard.sh`.
- Full gate: `bash scripts/check-module-invariants.sh` prints `ALL CHECKS PASSED`, exit 0.
- `lake exe runLinter FormalSystem` exit 0, unchanged from baseline.
- Sorry count: 0 live (C3 `PASS`; the census's remaining hits are all under `Boneyard/`).
- Vacuous count: 0 attributable to this task. The single-line grep heuristic returns one hit,
  `int_domain_universal ... := trivial` in `FormalSystem/Examples/TemporalStructures.lean` — a
  pre-existing theorem with a real statement that happens to be closed by `trivial`, not a
  placeholder. This task changed no `.lean` file (`git diff --name-only` over its commits,
  filtered to `*.lean`, is empty).
- Axiom count: 10, unchanged — no `.lean` change, so no axiom could have been introduced.
- Tests: N/A (no Lean declarations added or changed).
- Files verified: Yes. `git status --short` shows no residue under `FormalSystem/` or `scripts/`.

### The four negative tests

| Route | Seed | Observed | Same-run contrast |
|---|---|---|---|
| (1) out-of-closure module | `def negative_test_route_one` in `FormalSystem/Theorems/ContextualProofs.lean`, whose only importer is a `lean_exe` root | `FAIL C26  1 snake_case ... name(s)`, exit **1**; restored -> `PASS`, exit **0** | `PASS C1`, `PASS C16` (enforced half), `PASS C25` all green on a real violation |
| (2) in-source suppression | `attribute [nolint docBlame] ...` in `FormalSystem/Semantics/ShiftSet.lean`, absent from the allow-list | `FAIL C26  1 in-source nolint attribute(s) not on ...`, exit **1**; restored -> `PASS`, exit **0** | C26's first half still printed `PASS` in the same run — neither half masks the other |
| (3) the `_1` heuristic | `@[inline] def negativeTestRoute_1` in `FormalSystem/Examples/TemporalStructures.lean`, confirmed **inside** the linted closure, attribute-decorated | `FAIL C26`, exit **1**; restored -> `PASS`, exit **0** | `PASS C16` — `runLinter FormalSystem` reported zero on the very module holding the violation |
| (4) private declaration | `private def negative_test_route_four`, same in-closure module | `FAIL C26`, exit **1**; restored -> `PASS`, exit **0** | `PASS C16` and `PASS C1` — inside the closure and still invisible to the env_linter |

The stale-entry branch was exercised separately: an allow-list row matching nothing produced
`INFO C26  1 allow-list entr(y/ies) match nothing in the tree`.

**The route-1 test found a bug in the widening written one phase earlier.** Its first run showed
the widened sweep reporting an unchanged count with the seed in place, while the identical
`runLinter` command run by hand a moment later saw it — the module was being read from a stale
`.olean`, silently, on exactly the out-of-closure modules the widening exists to cover. After
building each root before linting it, the same test reported 180 findings across 11 roots, up
from 179 across 10. Without the negative test the widening would have shipped inert.

## Impacts

- A fourth reopening of this category now fails `scripts/check-module-invariants.sh` with a
  non-zero exit instead of accumulating silently, for declared `def`/`abbrev` names anywhere in
  the live tree — out-of-closure modules, `private` declarations and `_1`-shaped names included.
- Any new in-source `nolint` attribute now fails the gate unless it is added to
  `scripts/nolint-attribute-allowlist.txt` with a reason.
- The full gate is slower: the widened C16 half lints every lakefile root, and builds each first.
  Measured at 44 s for the sweep with the tree already built; the per-root builds it now performs
  are work C25 would otherwise do a few checks later, so the net addition is small.

## Follow-ups

- `ENFORCE_C16_ROOTS` is 0. Burning down the 179 findings on the non-`FormalSystem` roots — 56 of
  them `defsWithUnderscore`, concentrated in `Tests/BimodalTest/Integration/Helpers.lean` and in
  the `DatasetRecord` structure's field names — is the work that lets it flip to 1.
- `MODULE_INVARIANTS.md`'s check table documents B0, C1-C15, C24, C25, C9D and now C26, but has
  no rows for C16 through C23. That gap predates this task and was left alone rather than widened
  into it.
- The textual scan covers declared `def`/`abbrev` names only. A `Type`-valued `instance` with an
  underscored name, and a data-valued structure field, are both real violations it does not see;
  both are named as residuals at the exemption site and both are visible to the widened C16 half.

## References

- `specs/558_close_defswithunderscore_gate_evasion_routes/plans/01_close-gate-evasion-routes.md`
- `specs/558_close_defswithunderscore_gate_evasion_routes/handoffs/phase-1-handoff-20260908.md`
- `specs/558_close_defswithunderscore_gate_evasion_routes/handoffs/phase-5-handoff-20260908.md`
- `docs/development/NAMING_CONVENTION_DEVIATION.md`
- `docs/development/MODULE_INVARIANTS.md`
