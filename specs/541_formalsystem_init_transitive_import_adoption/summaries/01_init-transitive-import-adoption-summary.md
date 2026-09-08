# Implementation Summary: Task #541

- **Task**: 541 - FormalSystem Init transitive import adoption
- **Status**: [COMPLETED]
- **Started**: 2026-09-08
- **Completed**: 2026-09-08
- **Effort**: ~5 hours (dominated by three full-tree rebuilds)
- **Dependencies**: None
- **Artifacts**: plans/01_init-transitive-import-adoption.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`FormalSystem/Init.lean` is the library's root file — the single place from which
repository-wide linter options and common tactic imports are meant to be inherited — but no
live module imported it, so the guarantee was empty and `lake exe checkInitImports` could only
report. Eleven `import FormalSystem.Init` lines, placed at the eleven minimal elements of the
internal import DAG, now give every module in the `FormalSystem` root closure a transitive path
to the root. The checker was made exit-status-correct and wired into
`scripts/check-module-invariants.sh` as enforced check **C24**, and the gate was observed to
fail and then pass again under the deliberate negative test the harness's own "Adding a Check"
section mandates.

## What Changed

Import adoption — one `import FormalSystem.Init` line each, inserted after the last existing
`import` line matched by content, never by a fixed line number (`OrderIsoReal.lean`'s block
begins at line 42, and its import landed at line 47):

- `FormalSystem/Automation/NormalizationAttr.lean`, `FormalSystem/Automation/LemmaDB.lean`,
  `FormalSystem/Automation/TruthNormAttr.lean` — the three `Lean`-only attribute modules
- `FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean`,
  `FormalSystem/Metalogic/SoundnessLemmas/DiscreteOrder.lean`,
  `FormalSystem/Metalogic/WeakCanonical/MonadicFO.lean`,
  `FormalSystem/Metalogic/WeakCanonical/RealModel/OrderIsoReal.lean`
- `FormalSystem/Semantics/TemporalOrder.lean`,
  `FormalSystem/Semantics/Ultraproduct/IndexFilter.lean`, `FormalSystem/Syntax/Atom.lean`
- `FormalSystem/ForMathlib.lean` — the sibling aggregator *beside* the `ForMathlib/` directory,
  carrying the import on its consumers' behalf so that nothing *under* the directory imports
  `FormalSystem.*`

Tooling and documentation:

- `scripts/CheckInitImports.lean` — `return diff.length.toUInt32` replaced with
  `return if diff.isEmpty then 0 else 1`; `FormalSystem.ForMathlib.Order.PFilter` added to
  `exceptions` with its upstreaming-rule rationale; module docstring corrected (it claimed the
  check was reporting-only and the rewrite a follow-up, and cited a stale "~430-file" figure)
- `FormalSystem/Init.lean` — docstring corrected (it claimed the rewrite was "an explicit
  follow-up, not done here")
- `scripts/check-module-invariants.sh` — C24 wired at four sites: `# Checks:` header row,
  `--no-build` usage line, `ENFORCE_C24=${ENFORCE_C24:-1}` beside `ENFORCE_C23`, and the
  `RUN_BUILD`-guarded check block built on the C16 template, placed between C22 and C9D
- `scripts/module-invariants-manifest.txt` — the `FormalSystem.Init` entry deleted; the root is
  no longer unreachable, and C6 fails on a manifest entry naming a reachable module
- `docs/development/MODULE_INVARIANTS.md` — C24 row in "What It Checks", plus a paragraph in
  "Adding a Check" recording C24's negative test beside C15's
- `README.md`, `FormalSystem/README.md` and five per-directory `README.md` files — generated
  inventory blocks regenerated via `--emit-inventory` to absorb the added lines

## Decisions

- **Constant exit status over the CSLib original's count.** A POSIX exit status is 8 bits, so
  `return diff.length.toUInt32` truncates mod 256. This was not hypothetical: the measured
  baseline of 457 missing modules exited **201**, and any count that happened to be a non-zero
  multiple of 256 would have exited **0** — a gate reporting failure while telling the shell it
  passed. Fixed before the check was allowed to gate.
- **Variant C for `ForMathlib`.** `FormalSystem/ForMathlib/Order/PFilter.lean` is staged for
  upstreaming and may not depend on anything under `FormalSystem`, so it is recorded in
  `exceptions` rather than edited; the sibling aggregator carries the import instead. The
  documented upstreaming rule is intact — that file still has zero `FormalSystem.*` imports.
- **C24 ships enforced with no soft period**, unlike C8/C9/C10. Their debt was outstanding the
  day they were written; C24's adoption work landed in the same change, so a soft window would
  only be a window in which the invariant could regress unnoticed.
- **Low-fan-out-first phase ordering paid off.** The first two leaves cost a 34-target build;
  had the mechanism been wrong, that is where it would have shown, not after the 426-dependent
  `Syntax/Atom.lean` edit.

## Plan Deviations

- **Phase 2** altered: the build guard requires a recognized lake subcommand as its first
  wrapped argument, so every invocation is `-- build <targets>`, not `-- <targets>` (the latter
  exits 77 before any build runs). The dependent set was computed from the import graph rather
  than assumed, and narrowed by three targets — the two whole-tree roll-ups
  `FormalSystem.FormalSystem`/`FormalSystem.MainResults`, and
  `FormalSystem.Automation.ProofStepExport` (see Follow-ups).
- **Phase 3** altered: same target-narrowing; the computed dependent closure was 437 targets.
- **Phase 1 and Phase 4** additions: `bash scripts/check-module-invariants.sh
  --emit-inventory` had to be run twice, because the `INV` check gates generated line-count
  blocks and both the Init.lean docstring rewrite (+5 lines) and the eleven import lines drift
  them. Each regeneration's diff was confirmed to be exactly the expected line delta.
- **Phase 5** altered: the plan asserted no companion file would change. One did —
  `scripts/module-invariants-manifest.txt` — because `FormalSystem.Init` became reachable and
  C6 fails on a manifest entry naming a reachable module. The manifest's own comment had
  pre-authorised exactly that deletion ("DELETE this line when that rewrite lands").
- **Phase 6** scope-hypothesis correction: the negative test was predicted to name ~18 modules
  (the leaf plus its 17 dependents). It named **1**. That is the correct post-adoption answer —
  those 17 dependents now reach `Init` through other minimal elements too, so removing one leaf
  import isolates only the leaf. The assertion that mattered held: `FAIL C24`, non-zero script
  exit, and the affected module named in the log tail.

## Verification

Measured progression of `lake exe checkInitImports` (count missing / process exit status):

| Point | Missing | Exit |
|-------|---------|------|
| Baseline | 457 | 201 (truncated) |
| After Phase 1 (`exceptions` + constant return) | 456 | 1 |
| After Phase 2 (2 leaves) | 425 | 1 |
| After Phase 3 (6 leaves) | 38 | 1 |
| After Phase 4 (3 leaves) | **0** | **0** |
| Negative test (one leaf import removed) | 1 | 1 |
| After restore | **0** | **0** |

- Build: Success — full `lake build` exits 0 (2615 jobs), run detached through
  `.claude/scripts/lake-build-guard.sh`
- Sorry count: 0 live (`PASS C3  structural sorry inventory is ZERO across FormalSystem/`);
  the census's only hits are under the excluded `FormalSystem/Boneyard/` archive
- Vacuous count: 1, unchanged from the pre-implementation baseline at `70f189b11` — a
  pre-existing `theorem int_domain_universal … := trivial` in
  `FormalSystem/Examples/TemporalStructures.lean`, not introduced here
- Axiom count: 10, unchanged from the same baseline
- Tests: `bash scripts/check-module-invariants.sh` reports **ALL CHECKS PASSED** with
  `PASS C24`, exit 0; `--no-build` reports ALL CHECKS PASSED with
  `INFO C24 … skipped (--no-build)`, exit 0
- Negative test both directions observed: `FAIL C24` with script exit 1 and the affected module
  named, then `PASS C24` and ALL CHECKS PASSED after restoring the line
- No import cycle introduced: `scripts/check-metalogic-cycles.sh` still reports exactly 1
  directory-level cycle (the documented `BXCanonical` <-> `WeakCanonical` pair). This is also
  true by construction — `FormalSystem/Init.lean` imports only `Mathlib.Init` and
  `Mathlib.Tactic.Common`, so no back-edge into `FormalSystem.*` can exist
- Files verified: Yes; working tree carries no leftover scratch or probe files

## Impacts

- Every module in the `FormalSystem` root closure now inherits whatever `FormalSystem/Init.lean`
  sets, and C24 keeps it that way. Turning on a repo-wide linter set (e.g.
  `linter.mathlibStandardSet`) is now a one-file change with a gate behind it — that was the
  point of the Init root, and it was not previously true.
- The measured concern that giving the three `Lean`-only attribute modules the full 1582-module
  Mathlib environment would produce a wave of new linter findings did not materialise: C16's
  `env_linter` batch is green against the unchanged `scripts/nolints.json` baseline.
- Adding a new module to the tree now carries an obligation: it must reach `Init`, or the
  invariants harness fails. In practice this is automatic — any module importing another
  `FormalSystem` module inherits it.

## Follow-ups

- **`FormalSystem/Automation/ProofStepExport.lean` does not elaborate**, and did not before this
  task. Three `Application type mismatch` errors at lines 1479, 1496 and 1497:
  `@b_combinator_weakened`, `@theorem_flip_weakened` and `@theorem_app1_weakened` are each called
  with `(A := …) (B := …)` named arguments plus a positional `Formula`, but under `@` each
  declaration's first parameter is `{fc : FrameClass}`, so the positional lands in the wrong
  slot. Verified pre-existing by stashing this task's import lines and rebuilding that module
  alone: byte-identical errors. It is the `lake exe proof_extractor` root, sits outside the
  `FormalSystem` root closure (so neither `lake build` nor `checkInitImports` sees it), and is
  absent from `scripts/module-invariants-manifest.txt`, so C6 does not compile-check it either.
  Out of scope here (the plan's Non-Goals exclude out-of-closure modules) but worth its own task,
  together with the question of why an out-of-closure `lean_exe` root is not manifested.
- `docs/development/MODULE_INVARIANTS.md`'s "What It Checks" table is still missing rows for
  C16–C23; only the C24 row was added, per the plan's Non-Goals.
- Turning on `linter.mathlibStandardSet` (or any repo-wide option set) via the lakefile's
  `theoryLeanOptions` is now unblocked and is a separate task.

## References

- `specs/541_formalsystem_init_transitive_import_adoption/plans/01_init-transitive-import-adoption.md`
- `specs/541_formalsystem_init_transitive_import_adoption/reports/01_init-transitive-import-adoption.md`
- `specs/541_formalsystem_init_transitive_import_adoption/handoffs/` — per-phase handoffs 1–5
- `docs/development/MODULE_INVARIANTS.md` — C24 row and its negative-test record
