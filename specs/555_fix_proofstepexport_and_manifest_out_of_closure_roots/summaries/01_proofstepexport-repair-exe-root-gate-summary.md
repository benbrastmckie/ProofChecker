# Implementation Summary: Task #555

- **Task**: 555 - Fix ProofStepExport elaboration failure and bring out-of-closure `lean_exe` roots under compile checking
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T08:30:00Z
- **Completed**: 2026-09-08T08:45:00Z
- **Effort**: ~1.5 hours (plan estimated 6.5; the verified repair patch applied clean, removing the largest estimated block)
- **Dependencies**: None upstream. Downstream: tasks 557 and 558 both depend on this one.
- **Artifacts**: plans/01_proofstepexport-repair-exe-root-gate.md, reports/01_proofstepexport-out-of-closure-gate.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`FormalSystem/Automation/ProofStepExport.lean` — the `lake exe proof_extractor` root — did not
elaborate, and no gate in the repository was able to observe that: it sits outside both library
root closures, so `lake build` never touched it, C24's closure walk never reached it, and CI was
green throughout. The module is repaired and now elaborates, builds and runs. The structural hole
is closed by a new invariant **C25**, which scrapes the `lean_exe` root list out of `lakefile.lean`
at run time and compile-checks every root, plus a matching CI step so the coverage is continuous
rather than local-only. The task stayed deliberately compile-only: the lint closure was not
widened, and the non-regression proving that is recorded below.

## What Changed

- `FormalSystem/Automation/ProofStepExport.lean` — repaired (77 changed lines, 42+/35-). Three
  parts: `.Base` supplied positionally at the three `@`-applied call sites
  (`b_combinator_weakened`, `theorem_flip_weakened`, `theorem_app1_weakened`), whose first
  implicit parameter under `@` is `{fc : FrameClass}` so the positional `Formula` landed in the
  wrong slot; `mkEntry` split into `mkEntryAt (fc : FrameClass)` plus a `.Base`-pinning `mkEntry`
  wrapper whose `DerivationTree .Base` argument type fixes `fc` by unification at the 456 generic
  sites; and 31 genuinely non-`.Base` registry entries rewritten to `mkEntryAt ... .ZTime` /
  `.Dense`. Registry totals 487 entries (456 + 31).
- `scripts/check-module-invariants.sh` — new **C25** block plus `ENFORCE_C25=1`, the header
  `# Checks:` entry, and the `--no-build` usage line. C25 scrapes roots with the same regex C6's
  reachability walk uses, builds each as a **module** target (no linking), skips cleanly under
  `--no-build`, and fails on an empty scrape rather than passing silently.
- `docs/development/MODULE_INVARIANTS.md` — C25 row in `## What It Checks`, and the negative-test
  paragraph in `## Adding a Check` alongside the C15 and C24 records.
- `.github/workflows/ci.yml` — one new step compiling every scraped `lean_exe` root module after
  the `lean-action` step, with a comment recording why `@[default_target]` was rejected.
- `README.md`, `FormalSystem/Automation/README.md` — generated inventory blocks regenerated for
  the repair's +7 lines (via `--emit-inventory`, machine-owned).

## Decisions

- **C25 is a new check, not a manifest entry.** The task title's literal reading — add
  ProofStepExport to `scripts/module-invariants-manifest.txt` — would have failed by construction:
  C6 seeds its reachability walk from these same `root :=` lines, so an exe root is already
  *reachable* by C6's definition and a manifest line for one trips C6's stale-manifest branch.
  The manifest was left untouched and verified untouched at every commit.
- **The root list is scraped, not maintained.** A newly declared `lean_exe` is covered the day it
  is added, with no second list to forget. An empty scrape is a hard failure, so a change to the
  lakefile's shape surfaces rather than silently disabling the gate.
- **Module targets, never exe targets.** `lake exe` per root would link a 240-310 MB binary,
  thirteen times over, to buy elaboration coverage a module build gives for free.
- **Shipped enforced with no soft period**, on the C24 precedent: the repair landed in the same
  change, so every root is green from the first run and a soft window would only be a window in
  which the invariant could regress unnoticed.
- **The negative test was run on `TraceExporter`, not on the module under repair.** A failure in
  `ProofStepExport` would have proved nothing about the gate.

## Plan Deviations

- **Phase 3 scope hypothesis** altered: the plan expected **12** scraped roots (11
  `FormalSystem.Automation.*` plus `CheckInitImports`); the actual count is **13** (12 Automation
  roots plus `CheckInitImports`), confirmed against `grep 'root :=' lakefile.lean`. All 13 build
  clean, so the substance of the hypothesis — a green gate on day one — held. Every C25 message
  and doc reference states 13.
- **Phase 2 contingency** not exercised: the `maximum recursion depth reached in the code
  generator` risk did not materialise under real C emission, so the registry was not chunked.
- Otherwise the implementation followed the plan.

## Verification

Every result below was observed, not assumed.

- **Pre-repair baseline**: 3 errors under `lake env lean -DmaxErrors=100000`.
- **Masking confirmed (F3)**: with only the three call sites repaired, the module reports
  **873** errors — matching the research measurement exactly. The three mismatches were masking
  two orders of magnitude more work than the task description anticipated.
- **Post-repair**: **0** errors under `-DmaxErrors=100000`; `git diff --stat` shows exactly one
  file changed.
- **Transcription fidelity**: all 31 rewritten entries verified to carry a `fc := .X` inside the
  derivation tree matching the `.X` now passed to `mkEntryAt` — zero mismatches. `peirce_axiom_rs`,
  the entry a naive chunker mis-classifies, correctly stayed `mkEntry` (Base).
- **Real build**: `lake build FormalSystem.Automation.ProofStepExport` exit 0 (C emission
  exercised, 1431 jobs).
- **Executable**: `lake exe proof_extractor` exit 0 — Theorems processed **487/487**, Total proof
  steps **12077**, Axiom coverage **42/45**, Rule coverage **7/7**. Re-confirmed after all
  subsequent phases.
- **C25 cost**: 10s wall-clock for all 13 roots with the tree already built by C1, which is the
  position C25 runs in. Recorded in the check's comment block.
- **Negative test (mandated)**: one character deleted from `FrameClass` at
  `FormalSystem/Automation/TraceExporter.lean:193` →
  `FAIL C25  1 of 13 lean_exe root module(s) do not compile`, the broken root named, **script exit
  1**. In the same run C1 reported `lake build exits 0` — the invisible-failure condition C25
  exists to close, demonstrated directly. File restored (sha256 byte-identical,
  `git status --porcelain` clean) → `PASS C25`, `ALL CHECKS PASSED`, **exit 0**.
- **`--no-build`**: `INFO C25  lean_exe root compile check skipped (--no-build)`, exit code
  unaffected.
- Build: **Success** — full `bash .claude/scripts/lake-build-guard.sh build -- build` exit 0
  (2615 jobs).
- Invariants: `bash scripts/check-module-invariants.sh` → `PASS C25`, **ALL CHECKS PASSED**,
  exit 0. C6 passes; `scripts/module-invariants-manifest.txt` untouched.
- **Lint-closure non-regression**: `lake exe runLinter FormalSystem` → `Linting passed for
  FormalSystem.`, exit 0. `scripts/nolints.json` unchanged — no grandfathering was needed or
  added.
- Sorry count: **0** — zero `sorry`/`admit` added anywhere in this task's diff.
- Vacuous count: **0**.
- Axiom count: **unchanged** — the `^axiom ` set under `FormalSystem/` (Boneyard excluded) is
  byte-identical between the plan-creation commit and HEAD.
- Tests: covered by C1's `lake build BimodalTest`, which passed.
- Files verified: Yes.
- CI step: YAML parses (`yaml.safe_load`); the step's command run verbatim locally exits 0 over
  all 13 roots; `git diff` shows no change to the `lint:` input or any other `lean-action` input.

## Impacts

- `lake exe proof_extractor` is functional again, producing 12,077 proof steps across 487
  theorems. `specs/ROADMAP.md` Phase 6 (Dataset and Training Infrastructure) depends on this
  producer, which had been silently non-functional.
- No `lean_exe` root can fail invisibly again, locally (C25) or in CI (the new step). A root
  declared tomorrow is covered the day it is declared.
- `FormalSystem/Theorems/ContextualProofs.lean` is now compiled again as a transitive dependency
  of the repaired module. It is **compiled, not linted**: the compile-only boundary means its
  `defsWithUnderscore` debt is not yet exposed.

## Follow-ups

- **The `ContextualProofs` exposure is 65 findings, not the 66 the task description predicted**
  (`mp_chain_2` is exempt under the `_1`/`_2`/`_mathlib` rule in Mathlib's
  `isBadNameWithUnderscore` — the description counted `def`s, not linter findings). **It is not
  triggered by this task**, and becomes live only when task 558 widens the lint closure. The
  `runLinter` non-regression above is the evidence that it did not fire here.
- **The full debt behind the exe-root wall is 158, not 65.** The other 93 are in the exe roots
  themselves (`DatasetExport` alone accounts for 20, and those are structure projections whose
  names are the emitted JSON field names — renaming them is a data-format change, not a cosmetic
  one). Those 93 are in **no current task's `file_scope`**, and they become CI failures the moment
  task 558 widens the lint closure. Raised as a non-blocking `user_decision` on this dispatch:
  scope the exe-root lint burndown before 558 lands, or accept a red window. This implementation
  proceeded on the recommended option (spawn a dedicated task before 558) without blocking, since
  nothing in this task depends on the answer.
- Re-run C25's negative test after any change to its scope or to its root-scraping regex, checking
  the shell's exit status as well as the printed line.

## References

- `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/plans/01_proofstepexport-repair-exe-root-gate.md`
- `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/reports/01_proofstepexport-out-of-closure-gate.md`
- `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/verified-repair.patch`
- `docs/development/MODULE_INVARIANTS.md` (C25 row; `## Adding a Check` negative-test record)
- `scripts/check-module-invariants.sh` (C25 block and its comment block)
