# Implementation Plan: Task #555

- **Task**: 555 - Fix ProofStepExport elaboration failure and bring out-of-closure `lean_exe` roots under compile checking
- **Status**: [IMPLEMENTING]
- **Effort**: 6.5 hours
- **Dependencies**: None upstream. Downstream: tasks 557 and 558 both depend on this one.
- **Research Inputs**: specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/reports/01_proofstepexport-out-of-closure-gate.md
- **Artifacts**: plans/01_proofstepexport-repair-exe-root-gate.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

`FormalSystem/Automation/ProofStepExport.lean` — the `lake exe proof_extractor` root — does not
elaborate, and has not for some time, because it sits outside both library root closures and is
therefore never built by `lake build`, never walked by C6's rot guard, and never seen by CI. The
plan repairs the module using the research-verified `mkEntry`/`mkEntryAt` split (77 changed lines,
not the 3 the task description anticipated), proves the repair through a real `lake build` and a
real `lake exe proof_extractor` run, then closes the structural hole with a **new invariant C25**
that derives its target list from `lakefile.lean`'s `root :=` declarations at run time, plus a CI
step so the gate is continuous rather than local-only. The task stays deliberately **compile-only**:
widening the lint closure is task 558's job, and doing it here would turn CI red on 158 findings
that no current task scopes.

### Research Integration

Five findings from `reports/01_proofstepexport-out-of-closure-gate.md` shape this plan directly:

- **F3 (load-bearing)**: repairing only the three reported call sites surfaces **873** further
  errors across 583 lines (`don't know how to synthesize implicit argument 'fc'`) that the three
  mismatches were masking. The task description's "repair the three call sites" understates the
  work by two orders of magnitude. Phase 1 is sized against 873, not 3.
- **F4**: a verified 77-line repair exists and is saved at
  `specs/555_.../verified-repair.patch` (`git apply --check` clean). Zero errors after applying;
  `proof_extractor` processes 487/487 theorems emitting 12,077 steps.
- **F6**: `scripts/module-invariants-manifest.txt` is the **wrong** mechanism and would actively
  fail — C6's reachability walk already seeds itself from every `root :=` in `lakefile.lean`, so
  every `lean_exe` root is *reachable* by C6's definition, and a manifest line for it trips C6's
  `stale_manifest` branch. The task title's "manifest out-of-closure roots" must be read as *bring
  under a gate*, not *add to that file*. This plan adds a check; it does not touch the manifest.
- **F8**: `@[default_target]` on the exe targets is ruled out on measured cost (240-310 MB linked
  binary each, twelve of them). Module targets give elaboration coverage without linking.
- **F10/F11**: the linter exposure is **65**, not 66, and does not occur at all under a
  compile-only gate. The full debt behind the exe-root wall is 158.

### Prior Plan Reference

No prior plan. This is round 1 for task 555.

### Roadmap Alignment

`specs/ROADMAP.md` Phase 6 (Dataset and Training Infrastructure) depends on the extraction
executables this task repairs — `proof_extractor` is a producer for that front, and it has been
non-functional. Phase 7 (Repository Hygiene and Programme Metadata) is where the gate-hardening
half belongs: C25 is the same class of work as the dangling-edge scan and the ROADMAP split
already recorded there. No ROADMAP.md edit is in scope for this task (no `roadmap_flag` was set on
this dispatch); this section is alignment context only.

## Goals & Non-Goals

**Goals**:
- `FormalSystem/Automation/ProofStepExport.lean` elaborates with **zero** errors under
  `lake env lean -DmaxErrors=100000`, and builds under the real `lake build` (C emission exercised).
- `lake exe proof_extractor` links, runs, and reports 487/487 theorems and 12,077 proof steps.
- A new invariant (C25) compile-checks **every** `lean_exe` root scraped from `lakefile.lean`, so a
  future exe root is covered the day it is declared, with no list to maintain.
- The mandated negative test is performed on a *different* out-of-closure root, observed FAIL then
  PASS, and its observation recorded in `docs/development/MODULE_INVARIANTS.md`.
- A CI step makes the new coverage continuous, not local-only.
- `lake build` green and `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.

**Non-Goals**:
- **Widening the lint closure.** No `@[default_target]` on exe targets, no `runLinter` argument
  changes, no `lake lint` scope change. That is task 558's charter, and doing it here exposes 158
  findings (65 in `ContextualProofs`, 93 in the exe roots) that would turn CI red mid-sequence.
- **Renaming any `snake_case` declaration in `ContextualProofs.lean`.** That is task 557's
  `file_scope`, and it is unnecessary here because a compile-only gate does not lint.
- **Adding anything to `scripts/module-invariants-manifest.txt`** (F6 — C6 fails on it by
  construction).
- **Burning down the 93 exe-root lint findings** (F11). Out of every current task's `file_scope`;
  surfaced as a `user_decision` instead.
- No `sorry`, no `axiom`, no deferral placeholder anywhere in this task.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The 488-element registry list trips `maximum recursion depth reached in the code generator` under real C emission (observed once during research, on a different intermediate file) | H | M | Phase 2 is a dedicated real-`lake build` phase with a declared contingency: split the registry list into chunked sub-lists concatenated at the top level. Never assume the `lake env lean` result carries over |
| `verified-repair.patch` has gone stale against the working tree | M | L | The patch is a convenience, not the deliverable. The three mechanical rules in F4 are the durable form; if `git apply --check` fails, re-derive rather than force |
| Adding `ProofStepExport` to `scripts/module-invariants-manifest.txt` (the task title's literal reading) | H | M | Explicitly prohibited by this plan's Non-Goals. C6 fails on it by construction (F6) — the failure mode is a red gate, not a silent no-op |
| C25 lands red because another exe root is also broken | M | L | F7 measured all eleven siblings build clean, so C25 is green on day one. Phase 3 re-measures rather than trusting the measurement |
| The negative test is run on `ProofStepExport` itself and proves nothing about the gate | M | M | Phase 4 mandates `TraceExporter` (smallest, 0 build errors) and explicitly forbids using the module under repair |
| C25's `lake build` per root makes the gate materially slower | M | M | Module targets only, no linking; all transitive dependencies are already built by C1. Phase 3 records the measured added wall-clock in the check's comment block |
| Task 558 lands and CI goes red on the 93 unscoped exe-root lint findings | H | M | Surfaced now as a non-blocking `user_decision`, before 557 starts, per research recommendation 6 |
| A `lake build` exceeds the dispatch's patience and is killed mid-write | M | M | All builds run detached via `.claude/scripts/lake-build-guard.sh`. Note the guard takes the lake *subcommand* (`-- build X`), not `-- lake build X` |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 5 | 2 |
| 4 | 4 | 3 |
| 5 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel. Waves 2 and 3 are serialized behind Phase 1
deliberately: C25 (Phase 3) and the CI step (Phase 5) both compile `ProofStepExport`, so landing
either before the repair would leave a red commit.

---

### Phase 1: Repair ProofStepExport.lean [COMPLETED]

**Goal**: The module elaborates with zero errors — all 873 masked errors resolved, not just the
three reported mismatches.

**Tasks**:
- [ ] Establish the baseline: `lake env lean -DmaxErrors=100000 FormalSystem/Automation/ProofStepExport.lean`
      and record the error count (expected 3, capped reporting).
- [ ] Try `git apply --check specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/verified-repair.patch`.
      If clean, apply it. If not, re-derive from the three rules below.
- [ ] Rule 1 — insert `.Base` positionally after `@` at the three reported sites (lines ~1479,
      ~1496, ~1497): `@b_combinator_weakened .Base (A := p) ... s`, and likewise for
      `theorem_flip_weakened` and `theorem_app1_weakened`. This matches the ~16 existing
      `@bCombinator .Base (A := p) ...` sites in the same file.
- [ ] Rule 2 — rename `mkEntry` -> `mkEntryAt`, changing `{fc : FrameClass}` to an explicit
      `(fc : FrameClass)` second parameter; add a new
      `private def mkEntry (name) {Γ φ} (tree : DerivationTree .Base Γ φ) := mkEntryAt name .Base tree`
      with the docstring explaining that the `.Base` in the *argument type* is what pins `fc` by
      unification at the ~455 generic sites.
- [ ] Rule 3 — rewrite the 31 genuinely non-Base entries to `mkEntryAt "<name>" .ZTime` /
      `mkEntryAt "<name>" .Dense`, per the Appendix list in the research report. **Caution**:
      `peirce_axiom_rs` is Base but sits immediately above the `.ZTime` block; a naive "next
      `mkEntry` starts the next entry" chunker mis-classifies it (observed and corrected during
      research).
- [ ] Re-measure with `-DmaxErrors=100000` and confirm **0** errors.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The repair is ~77 changed lines resolving 873 errors across 583 lines, of
which 31 entries are non-Base. Confirm at implementation time by (a) `git diff --stat` on the
single file, and (b) the before/after `-DmaxErrors=100000` error counts. If the pre-repair count
is not 3 or the intermediate count is not near 873, the file has changed since the research and
the 31-entry list must be re-derived from the source rather than transcribed from the Appendix.

**Files to modify**:
- `FormalSystem/Automation/ProofStepExport.lean` - `mkEntry`/`mkEntryAt` split, 3 `@`-call-site
  repairs, 31 non-Base entry rewrites.

**Verification**:
- `lake env lean -DmaxErrors=100000 FormalSystem/Automation/ProofStepExport.lean` reports zero
  errors. The default 100-error cap must be defeated explicitly — an uncapped run under-reports.
- `git diff --stat` shows exactly one file changed.
- The 31 rewritten entries each still carry their original `(fc := .ZTime)` / `(fc := .Dense)`
  inside the derivation tree — the rewrite is a faithful transcription, not a semantic change.

---

### Phase 2: Prove the repair through a real build and a real run [COMPLETED]

**Goal**: Confirm the repair survives C emission and linking, and that the executable produces the
expected output — the elaboration check of Phase 1 is not sufficient evidence.

**Tasks**:
- [ ] `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build FormalSystem.Automation.ProofStepExport`
      (detached; note the guard takes the lake *subcommand*, so `-- build X`, never `-- lake build X`).
- [ ] `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- exe proof_extractor -- --output <tmp>`
      and confirm exit 0.
- [ ] Confirm the reported counts: `Theorems processed: 487/487`, `Total proof steps: 12077`,
      `Axiom coverage: 42/45`, `Rule coverage: 7/7`.
- [ ] **Contingency** (only if `maximum recursion depth reached in the code generator` appears):
      split the 488-element registry list into chunked sub-lists concatenated at the top level,
      then re-run both commands. Do not work around it with a `set_option maxRecDepth` bump without
      first confirming the chunked form does not fix it.
- [ ] Commit the repair once both commands are green.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: The expected run output is 487/487 theorems and 12,077 steps. Confirm by
reading the executable's own report, not by assuming — a count that differs means the registry
changed shape during the repair (most likely a dropped or duplicated entry in the 31-entry
rewrite), and the diff must be re-audited before proceeding.

**Files to modify**:
- `FormalSystem/Automation/ProofStepExport.lean` - only under the contingency branch (registry
  chunking). Otherwise no edits; this phase is a verification and commit boundary.

**Verification**:
- Real `lake build` of the module exits 0 (this, not `lake env lean`, is what exercises C emission).
- `lake exe proof_extractor` exits 0 with the four expected counts.
- `git log -1` shows the repair committed.

---

### Phase 3: Add invariant C25 — every `lean_exe` root compiles [COMPLETED]

**Goal**: A self-maintaining gate that compile-checks every `lean_exe` root declared in
`lakefile.lean`, so no exe root can fail invisibly again.

**Tasks**:
- [ ] Add a C25 block to `scripts/check-module-invariants.sh`, modelled structurally on the
      existing C24 block (comment block stating the rationale, `RUN_BUILD` guard, `pass`/`fail`/
      `info` calls, `ENFORCE_C25` variable declared beside the others near line 500).
- [ ] Scrape the root list the same way the C6 reachability block already does:
      `re.findall(r"root\s*:=\s*`([A-Za-z0-9_.]+)", lakefile_text)` — derived at run time, so a
      newly declared `lean_exe` is covered the day it is added and there is no list to forget.
- [ ] Run `lake build <root>` per scraped root (module target, **not** exe target — elaboration
      only, no linking; F8's measured 240-310 MB per linked binary is why).
- [ ] Skip cleanly under `--no-build` with an `info` line, exactly as C1/C2/C6/C16/C24 do.
- [ ] Ship it **enforced** (`ENFORCE_C25=1`), with the C24 precedent cited: the work clearing its
      debt lands in the same change, so a soft period would only open a regression window.
- [ ] Update the script's own header comment list (the `# Checks:` block) with a C25 line, and the
      `--no-build` usage line from `skip C1/C2/C6/C16/C24` to include C25.
- [ ] Add a C25 row to the `## What It Checks` table in `docs/development/MODULE_INVARIANTS.md`,
      in the same voice as the C24 row (what it checks + why it exists, naming the invisible-failure
      history as the reason).
- [ ] Record the measured added wall-clock of C25 in its comment block.
- [ ] **Do not** add any entry to `scripts/module-invariants-manifest.txt` — C6 fails on it by
      construction (F6).

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: 12 exe roots are expected to be scraped (11 `FormalSystem.Automation.*` plus
`CheckInitImports`), and F7 measured all eleven non-ProofStepExport roots build clean. Confirm both
at implementation time: print the scraped list and compare it against `grep 'root :=' lakefile.lean`,
and observe C25 PASS on the first full run. If a second root is broken, repair it in this phase
rather than deferring — a red new gate is not an acceptable landing state.

**Files to modify**:
- `scripts/check-module-invariants.sh` - new C25 block, `ENFORCE_C25` declaration, header check
  list, `--no-build` usage line.
- `docs/development/MODULE_INVARIANTS.md` - C25 row in the `## What It Checks` table.

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` prints `INFO C25 ... skipped (--no-build)`
  and does not affect the exit code.
- A full `bash scripts/check-module-invariants.sh` run prints `PASS C25` and reports
  `ALL CHECKS PASSED`.
- C6 still passes — confirming the manifest was not touched.

---

### Phase 4: The mandated negative test [COMPLETED]

**Goal**: Prove C25 actually catches a break, per `docs/development/MODULE_INVARIANTS.md`'s
"Adding a Check" mandate, and record the observation the way C15 and C24 recorded theirs.

**Tasks**:
- [ ] Choose `FormalSystem/Automation/TraceExporter.lean` as the subject — smallest out-of-closure
      root, 0 build errors. **Do not use `ProofStepExport`**: it is the module under repair, so a
      failure there proves nothing about the gate.
- [ ] Introduce a deliberate one-character break in `TraceExporter.lean`.
- [ ] Run `bash scripts/check-module-invariants.sh` and observe `FAIL C25` **and** a non-zero
      script exit (both, not just the printed line — C24's history is exactly a case where a
      failure printed while the shell received a 0).
- [ ] Restore the file (`git checkout` on that path only; the tree is otherwise clean at this
      point), re-run, and observe `PASS C25` and exit 0.
- [ ] Record the negative test in the C25 comment block in `scripts/check-module-invariants.sh`,
      in the same voice as C24's paragraph, including the instruction to re-run it after any change
      to C25's scope.
- [ ] Record it in `docs/development/MODULE_INVARIANTS.md`'s `## Adding a Check` section alongside
      the C15/C24 paragraphs.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Files to modify**:
- `scripts/check-module-invariants.sh` - negative-test paragraph inside the C25 comment block.
- `docs/development/MODULE_INVARIANTS.md` - negative-test paragraph in `## Adding a Check`.
- `FormalSystem/Automation/TraceExporter.lean` - transiently broken and restored; **must** be
  byte-identical to its committed state at phase close (verify with `git status --porcelain`).

**Verification**:
- The FAIL observation and the PASS observation are both recorded with their exit codes.
- `git status --porcelain` shows no modification to `TraceExporter.lean` at phase close.
- The recorded paragraphs name the subject module and the exit-code check explicitly.

---

### Phase 5: Make the gate continuous in CI [COMPLETED]

**Goal**: The new coverage runs on every push and PR, not only when someone runs the invariants
script locally.

**Tasks**:
- [ ] Add one step to `.github/workflows/ci.yml`, after the `lean-action` step, running
      `lake build` over the twelve exe root **modules** (not exe targets — elaboration only, no
      linking, sharing the cache the action already populated).
- [ ] Give the step a comment explaining why it exists: `@[default_target]` was rejected on
      measured link cost, and these modules are otherwise outside every closure CI touches.
- [ ] Do **not** change the `lint:` input or add a `runLinter` invocation — the compile-only
      boundary is deliberate (see Non-Goals).
- [ ] Verify the YAML parses and the step's command is exactly what runs green locally.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `.github/workflows/ci.yml` - one new build step plus its explanatory comment.

**Verification**:
- YAML parses (`python -c "import yaml,sys; yaml.safe_load(open('.github/workflows/ci.yml'))"`).
- The step's command, run verbatim locally, exits 0.
- `git diff` shows no change to the `lint:` input or any other lean-action input.

**Note on file scope**: `.github/workflows/ci.yml` is **outside** task 555's recorded `file_scope`
(`FormalSystem/Automation/ProofStepExport.lean`, `scripts/module-invariants-manifest.txt`,
`scripts/check-module-invariants.sh`). `file_scope` is descriptive rather than enforced, but this
addition is named here deliberately rather than arriving unannounced. Note also that
`scripts/module-invariants-manifest.txt` — which *is* in the recorded scope — is deliberately
**not** touched by this plan (F6).

---

### Phase 6: Final gate and lint-closure non-regression [IN PROGRESS]

**Goal**: Every acceptance criterion observed in one pass, and the compile-only boundary proven
intact so tasks 557 and 558 can sequence off a green baseline.

**Tasks**:
- [ ] `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` — full build green.
- [ ] `bash scripts/check-module-invariants.sh` — `ALL CHECKS PASSED`, including `PASS C25`.
- [ ] `lake exe runLinter FormalSystem` — still `Linting passed for FormalSystem.`, exit 0. This is
      the non-regression that proves the lint closure did **not** widen.
- [ ] `git diff` on `scripts/nolints.json` — empty. No grandfathering was needed or added
      (`docs/development/NAMING_CONVENTION_DEVIATION.md` records grandfathering `defsWithUnderscore`
      as exactly the silent-drift failure this project already reversed once).
- [ ] `lake exe proof_extractor` — still 487/487, re-confirmed after all subsequent phases.
- [ ] Record in the execution summary that the `ContextualProofs` exposure is **65** findings (not
      66 — `mp_chain_2` is exempt by the `_1`/`_2`/`_mathlib` rule in Mathlib's
      `isBadNameWithUnderscore`), that it is **not** triggered by this task, and that it becomes
      live only when 558 widens the lint closure.
- [ ] Final commit.

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

**Files to modify**:
- None. This phase is the gate pass, the summary record, and the final commit boundary.

**Verification**:
- All five commands above produce their stated results, each observed rather than assumed.
- Every phase heading in this plan reads `[COMPLETED]`.
- Working tree clean.

---

## Testing & Validation

- [ ] `FormalSystem/Automation/ProofStepExport.lean` elaborates with zero errors under
      `lake env lean -DmaxErrors=100000`.
- [ ] Real `lake build FormalSystem.Automation.ProofStepExport` exits 0 (C emission exercised).
- [ ] `lake exe proof_extractor` exits 0 with 487/487 theorems and 12,077 proof steps.
- [ ] A deliberately reintroduced break in `TraceExporter` (an out-of-closure root that is **not**
      the module under repair) is CAUGHT: `FAIL C25` observed with non-zero exit, then `PASS`
      observed after restore.
- [ ] `lake build` green.
- [ ] `bash scripts/check-module-invariants.sh` reports `ALL CHECKS PASSED`.
- [ ] `bash scripts/check-module-invariants.sh --no-build` still runs and skips C25 cleanly.
- [ ] `lake exe runLinter FormalSystem` still passes — lint closure unchanged.
- [ ] `scripts/nolints.json` unchanged.
- [ ] Zero `sorry` and zero new `axiom` introduced anywhere.

## Artifacts & Outputs

- Repaired `FormalSystem/Automation/ProofStepExport.lean` (~77 changed lines).
- New invariant C25 in `scripts/check-module-invariants.sh`, with its negative test recorded in
  its comment block.
- `docs/development/MODULE_INVARIANTS.md`: C25 table row plus a negative-test paragraph in
  `## Adding a Check`.
- One new build step in `.github/workflows/ci.yml`.
- `specs/555_.../summaries/01_*-summary.md` recording the 65-finding staged exposure for 557/558.

## Rollback/Contingency

Each phase commits independently and every commit is green, so rollback is per-phase `git revert`.
Specifically:

- **Phase 1-2 fail** (code generator recursion survives chunking): revert the repair commit. The
  module returns to its current non-elaborating state — no worse than today, since nothing imports
  it. Re-open with a registry-splitting design rather than a call-site fix.
- **Phase 3 fails** (a second exe root is broken and cannot be repaired in-phase): do **not** ship
  C25 soft to hide it. Land C25 enforced with the second root repaired, or stop and report — a soft
  gate here recreates exactly the invisible-failure condition this task exists to close.
- **Phase 5 fails** (CI step is too slow or the runner cannot cache): drop the CI step only, keep
  C25. The gate degrades from continuous to local, which is still strictly better than today.
- **Any phase**: `scripts/module-invariants-manifest.txt` must be unchanged at every commit. If it
  has been modified, that is a wrong-mechanism error (F6), not a rollback candidate — revert that
  file specifically.
