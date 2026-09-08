# Implementation Plan: FormalSystem.Init Transitive Import Adoption

- **Task**: 541 - FormalSystem Init transitive import adoption
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/541_formalsystem_init_transitive_import_adoption/reports/01_init-transitive-import-adoption.md
- **Artifacts**: plans/01_init-transitive-import-adoption.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Make the `FormalSystem.Init` import invariant enforceable by giving every module in the
`FormalSystem` root closure a transitive path to it, then flipping `checkInitImports` from a
reporting-only executable to a gating check wired into `scripts/check-module-invariants.sh` as
C24. The edit surface is small and precisely known — 11 files gain one `import FormalSystem.Init`
line each, one `exceptions` entry is added, one return value is corrected, one check block is
added, and three documentation surfaces are corrected — but the *rebuild* surface is the whole
tree, so phase ordering is chosen to make invalidation cheap early and expensive only once. Done
means: `lake exe checkInitImports` reports zero missing modules and exits 0, C24 gates
(demonstrated by a deliberate negative test), `lake build` is green, and
`bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.

### Research Integration

The research report supersedes three claims in the task description and the plan is built on the
corrected versions:

- **Count**: the live figure is **457**, not 434 (`lake exe checkInitImports` plus an independent
  static import-graph model produced byte-identical name lists). 434 is the historical figure
  recorded when the mechanism landed and appears in this plan only as history.
- **Edit surface**: the fix is **11 file edits**, not 434/457 import lines. The internal
  `FormalSystem` DAG has exactly 11 minimal elements (modules with zero `FormalSystem.*` imports);
  Init reaches everything else transitively from those. Each of the 11 is also *necessary* — none
  has another `FormalSystem` import through which Init could arrive.
- **`AxiomNames.lean`**: needs **no** treatment (research D3), contradicting the task description's
  anticipation. It sits outside the root closure the check imports, so it can never appear in the
  diff; importing Init there would take a deliberately Mathlib-free `lean_exe`-shared leaf from 0
  to 1582 upstream modules for zero gate benefit.

Three further research findings shape the phases directly:

- **Variant C** (research D2) is adopted: Init goes into 10 of the 11 leaves plus the *sibling
  aggregator* `FormalSystem/ForMathlib.lean`, and `FormalSystem.ForMathlib.Order.PFilter` is added
  to `exceptions`. This preserves the documented rule that nothing *under*
  `FormalSystem/ForMathlib/` imports `FormalSystem.*`.
- **The gate has a silent-pass hole** (research R2): `main` ends `return diff.length.toUInt32` and
  a POSIX exit status is 8 bits — 457 currently exits **201**, and any count ≡ 0 mod 256 would exit
  **0**. This must be fixed to a constant return *before* the check gates.
- **No import cycle is structurally possible**: `FormalSystem/Init.lean` imports only
  `Mathlib.Init` and `Mathlib.Tactic.Common`, nothing under `FormalSystem.*`, so no back-edge can
  be created. The acceptance criterion is satisfied by construction and re-asserted by `lake build`
  and by `scripts/check-metalogic-cycles.sh`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in the dispatch context; no roadmap consultation performed.

## Goals & Non-Goals

**Goals**:

- Every module in the `FormalSystem` root closure transitively imports `FormalSystem.Init`, via 11
  file edits placed at the minimal elements of the internal import DAG.
- `scripts/CheckInitImports.lean` returns a constant exit status (1 on failure, 0 on success)
  rather than a truncated count.
- `FormalSystem.ForMathlib.Order.PFilter` is recorded in `exceptions` with a rationale naming the
  upstreaming rule as its technical constraint.
- A new **C24** check runs `lake exe checkInitImports` inside `scripts/check-module-invariants.sh`,
  ships **enforced** (`ENFORCE_C24=${ENFORCE_C24:-1}`), and has been *observed to fail* under a
  deliberate negative test.
- The three documentation surfaces asserting the now-removed deferral are corrected in the same
  change (C14 is a live tripwire for exactly this drift).
- `lake build` green; `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.

**Non-Goals**:

- Adding `import FormalSystem.Init` to `FormalSystem/Automation/AxiomNames.lean` (research D3).
- Widening the check's scope beyond the `FormalSystem` root closure — the 26 other out-of-closure
  live modules and the 168 archived `FormalSystem/Boneyard/` modules stay untouched (research D4).
- Turning on `linter.mathlibStandardSet` or any other repo-wide linter set. Init is the import
  carrier; the lakefile's `theoryLeanOptions` is the option setter. That lever is a separate task.
- Editing `.github/workflows/ci.yml`. CI does not invoke `check-module-invariants.sh` at all;
  wiring C24 into the harness is the whole of the gating requirement.
- Back-filling the missing C16–C23 rows into `docs/development/MODULE_INVARIANTS.md` (research D6).
  Only the C24 row is added. That table is 8 checks stale for unrelated reasons.
- Any `sorry`, new axiom, or deferral. None is required by any part of this change.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Full-tree rebuild: `Syntax.Atom` (426 dependents) and `TruthNormAttr` (424) invalidate nearly every `.olean` | H (time) | H (certain) | Sequence low-fan-out leaves first (Phases 2–3) so mistakes surface against ~36 modules, not 457. Do the `Init.lean` docstring edit in Phase 1, *before* adoption, so it does not force a second full rebuild. |
| Exit-code truncation makes the gate a silent no-op at any count ≡ 0 mod 256 | H (gate correctness) | M | Phase 1 replaces the truncating return with a constant; Phase 6 proves the gate can actually fail. |
| Hard-coded line numbers corrupt `OrderIsoReal.lean`, whose import block starts at line 42 | M | M | Every insertion is made *after the last existing `import` line*, matched by content. Never a fixed line number. |
| The naive 11-leaf edit violates the documented `ForMathlib` upstreaming rule | M (architectural) | H if unguarded | Variant C: `FormalSystem/ForMathlib/Order/PFilter.lean` is left untouched and goes into `exceptions`; the sibling aggregator `FormalSystem/ForMathlib.lean` carries the import instead. |
| C14 fires on the two now-false docstrings | M | H (certain if ignored) | Both docstrings corrected in Phase 1; the `MODULE_INVARIANTS.md` C24 row in Phase 5. |
| New linter warnings across the tree once Mathlib linters become importable everywhere | L | L (measured) | A two-file `lake env lean` probe showed byte-identical output vs. baseline. Phase 2's small build confirms cheaply. If warnings do appear they are fixed in-tree, never by reverting the import. |
| Three `Lean`-only attribute modules (`LemmaDB`, `NormalizationAttr`, `TruthNormAttr`) go from 0 to 1582 upstream modules | L | M | Low-fan-out-first ordering puts `NormalizationAttr` in Phase 2, so the first evidence arrives at the cheapest point. |
| Memory pressure — the build guard already warned during research | M | M | Every `lake` invocation runs detached through `.claude/scripts/lake-build-guard.sh` per `context/project/lean4/operations/long-builds.md`. No concurrent builds from other sessions during the rebuild. |
| A count asserted in this plan (457, 456, 11, fan-outs) drifts before implementation | L | L | Every count-asserting phase carries a Scope Hypothesis line naming the command that confirms it at implementation time. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This plan is fully sequential: each build
phase depends on the previous one's green build, and the gate-wiring phases depend on a clean
checker.

### Phase 1: Baseline, Gate-Correctness Fix, and Docstring Corrections [COMPLETED]

**Goal**: Capture the measured before-state, make the checker's exit status meaningful, record the
`ForMathlib` exception, and correct both in-tree docstrings that assert the deferral this task
removes — all *before* any import edit, so the `Init.lean` docstring change does not later force a
second full-tree rebuild.

**Tasks**:

- [x] Run `lake exe checkInitImports` through the build guard; record the reported count and the
      shell's `$?`. Save the sorted name list to a scratch file for later diffing.
- [x] In `scripts/CheckInitImports.lean`, replace `return diff.length.toUInt32` with a constant
      return: `1` when `diff` is non-empty, `0` otherwise. Add a comment at the site stating this
      is a deliberate deviation from the near-verbatim CSLib original, and why (8-bit exit-status
      truncation makes a count-returning gate silently pass at any multiple of 256).
- [x] Add `` `FormalSystem.ForMathlib.Order.PFilter `` to `exceptions` in the same file, with a
      one-line rationale comment naming the documented upstreaming rule ("Nothing under
      `FormalSystem/ForMathlib/` imports `FormalSystem.*`") as the technical constraint.
- [x] Correct the `scripts/CheckInitImports.lean` module docstring: it currently says the check is
      "Reporting-only: not wired into `check-module-invariants.sh`" and cites a "~430-file import
      rewrite" follow-up. Both become false; the figure is also stale (457) and wrong in kind (11
      files).
- [x] Correct the `FormalSystem/Init.lean` module docstring: it currently says "Rewriting the tree
      so every module actually imports `FormalSystem.Init` is an explicit follow-up, not done
      here."
- [x] Rebuild the executable and re-run it. Confirm the count is unchanged except for the removal
      of the one exception, and that `$?` is now `1`, not a truncated count.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

`scripts/CheckInitImports.lean` is a `lean_exe` root with no importers, and at this point in the
sequence nothing imports `FormalSystem/Init.lean` either, so both edits are genuinely
single-module. The docstring halves are `prose`; the return-value and `exceptions` changes are
`local` and the strictest applicable tier governs the phase. Verification is building and running
the executable itself.

**Scope Hypothesis**: The pre-edit count is **457** and the post-exception count is **456** (457
minus `FormalSystem.ForMathlib.Order.PFilter`, whose only removal cause is the new `exceptions`
entry). Confirm by running `lake exe checkInitImports` before and after the edit and diffing the
two sorted name lists — the diff must be exactly that one name. If the before-count is not 457,
record the live figure and carry it forward; the 11-leaf structure does not depend on the count.

**Files to modify**:

- `scripts/CheckInitImports.lean` - constant exit return; new `exceptions` entry; docstring
  correction
- `FormalSystem/Init.lean` - docstring correction (deferral claim removed)

**Verification**:

- `lake exe checkInitImports` runs, prints a count one lower than the baseline, and exits `1`.
- The removed name is exactly `FormalSystem.ForMathlib.Order.PFilter`.
- `bash scripts/check-module-invariants.sh --no-build` still reports ALL CHECKS PASSED (C14 should
  now be satisfied by the corrected docstrings rather than tripped by them).

---

### Phase 2: Low-Fan-Out Leaves [COMPLETED]

**Goal**: Exercise the adoption mechanism against the two cheapest minimal elements before
invalidating anything expensive, so a surprise (new linter warnings, an elaboration change in a
`Lean`-only attribute module) is caught at ~36 modules of cost rather than 457.

**Tasks**:

- [x] Add `import FormalSystem.Init` to `FormalSystem/Automation/NormalizationAttr.lean` (fan-out
      17). Insert **after the last existing `import` line**, located by content, never by a fixed
      line number.
- [x] Add `import FormalSystem.Init` to `FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean`
      (fan-out 19), same insertion rule.
- [x] Build the two modules and their dependents through the guard *(deviation: altered — the
      guard requires a recognized lake subcommand as its first wrapped argument, so the
      invocation is `-- build <targets>`, not `-- <targets>`; and the dependent set was
      computed from the import graph and narrowed to 34 targets, excluding the two whole-tree
      roll-ups `FormalSystem.FormalSystem`/`FormalSystem.MainResults` and the out-of-closure
      `FormalSystem.Automation.ProofStepExport`, which fails identically without this phase's
      edits — see the summary's pre-existing-defect note)*:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- FormalSystem.Automation.NormalizationAttr FormalSystem.Metalogic.Decidability.BiLasso.Periodic`
      run detached via `Bash(run_in_background: true)`.
- [x] Inspect the build output for **new** warnings, especially in `NormalizationAttr` — this is
      the first of the three `Lean`-only attribute modules to gain the full 1582-module Mathlib
      environment, and is the cheapest place to observe R8 if it is real.
- [x] Commit at green.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: interface

Adding an import changes the elaboration environment of the module and everything downstream of it,
so verification must reach past the edited file. The enumerated dependent set for this phase is
small (~36 modules), and a targeted `lake build <module>` covers each module's closure exactly.
The blind spot — transitive breakage outside this enumerated set — is closed by Phase 4's full
build and Phase 6's final gate, not deferred past the task.

**Scope Hypothesis**: These two leaves have fan-outs of 17 and 19 respectively and are minimal
elements (zero `FormalSystem.*` imports today). Confirm at implementation time by checking that
neither file's import block contains any `import FormalSystem.` line before the edit, and that the
targeted build touches roughly that many modules. A larger-than-expected build is a signal the
graph model drifted, not a reason to proceed.

**Files to modify**:

- `FormalSystem/Automation/NormalizationAttr.lean` - one import line
- `FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean` - one import line

**Verification**:

- Targeted build exits 0 with no new warnings attributable to the added import.
- `lake exe checkInitImports` count drops by approximately the combined fan-out.

---

### Phase 3: Mid-Tier Leaves [COMPLETED]

**Goal**: Adopt the six mid-fan-out minimal elements in one batch, now that the mechanism has been
shown to work, keeping the two tree-invalidating leaves for last.

**Tasks**:

- [x] Add `import FormalSystem.Init` after the last existing `import` line in each of:
      - `FormalSystem/Metalogic/WeakCanonical/RealModel/OrderIsoReal.lean` (fan-out 24) —
        **its import block begins at line 42, not line 7**; content-matched insertion is mandatory
        here
      - `FormalSystem/Metalogic/SoundnessLemmas/DiscreteOrder.lean` (fan-out 38)
      - `FormalSystem/Semantics/Ultraproduct/IndexFilter.lean` (fan-out 160)
      - `FormalSystem/Automation/LemmaDB.lean` (fan-out 187)
      - `FormalSystem/Metalogic/WeakCanonical/MonadicFO.lean` (fan-out 199)
      - `FormalSystem/Semantics/TemporalOrder.lean` (fan-out 238)
- [x] Build the six modules and their dependents through the guard, detached *(deviation: altered — the computed dependent closure is 437 targets, and `FormalSystem.Automation.ProofStepExport` was excluded from it as a pre-existing, out-of-closure breakage recorded in the Phase 2 handoff)*.
- [x] Inspect output for new warnings; `LemmaDB` is the second `Lean`-only attribute module.
- [x] Commit at green.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: interface

Same reasoning as Phase 2 at larger scale: the dependent sets are enumerated (the six fan-outs) and
covered by targeted builds. Transitive breakage outside them is closed by Phase 4's full build.

**Scope Hypothesis**: Six files, fan-outs 24/38/160/187/199/238, all minimal elements. Confirm by
grepping each file for a pre-existing `import FormalSystem.` line (there must be none) before
editing, and by re-running `lake exe checkInitImports` after the build — the count must fall
monotonically. Note the fan-outs overlap heavily, so the count drop is not their sum.

**Files to modify**:

- `FormalSystem/Metalogic/WeakCanonical/RealModel/OrderIsoReal.lean` - one import line
- `FormalSystem/Metalogic/SoundnessLemmas/DiscreteOrder.lean` - one import line
- `FormalSystem/Semantics/Ultraproduct/IndexFilter.lean` - one import line
- `FormalSystem/Automation/LemmaDB.lean` - one import line
- `FormalSystem/Metalogic/WeakCanonical/MonadicFO.lean` - one import line
- `FormalSystem/Semantics/TemporalOrder.lean` - one import line

**Verification**:

- Targeted builds exit 0, no new warnings.
- `lake exe checkInitImports` count falls; no module that previously had Init loses it.

---

### Phase 4: High-Fan-Out Leaves, the ForMathlib Aggregator, and Zero Missing [NOT STARTED]

**Goal**: Adopt the last three edit sites — the two tree-invalidating leaves plus the `ForMathlib`
aggregator — take the one unavoidable full rebuild, and reach zero modules missing
`FormalSystem.Init`.

**Tasks**:

- [ ] Add `import FormalSystem.Init` after the last existing `import` line in
      `FormalSystem/Syntax/Atom.lean` (fan-out 426).
- [ ] Same for `FormalSystem/Automation/TruthNormAttr.lean` (fan-out 424) — the third and last
      `Lean`-only attribute module.
- [ ] Same for `FormalSystem/ForMathlib.lean` — the sibling aggregator *beside* the directory, not
      a file under it, so this does not violate the upstreaming rule.
- [ ] Confirm `FormalSystem/ForMathlib/Order/PFilter.lean` is **untouched** and still has zero
      `FormalSystem.*` imports.
- [ ] Full rebuild through the guard, detached:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 --` with no module argument.
- [ ] Run `lake exe checkInitImports`; confirm zero missing and exit status `0`.
- [ ] Run `bash scripts/check-metalogic-cycles.sh` and confirm the Metalogic directory-level cycle
      count is still exactly 1 (the documented `BXCanonical` ↔ `WeakCanonical` pair) — the
      mechanical half of the "no import cycle introduced" acceptance criterion.
- [ ] Commit at green.

**Timing**: 1.5 hours (dominated by the full rebuild)

**Depends on**: 3

**Verification Tier**: full

These two leaves invalidate essentially the entire `.olean` set; the phase's verification is a
complete `lake build` of the repository plus the cycle check. Nothing is deferred past this tier.

**Scope Hypothesis**: Three files here, eleven across Phases 2–4 in total, and after them the
missing count is **0**. Confirm with `lake exe checkInitImports` reporting no modules and exiting
0. If any module remains, it is a minimal element the static model missed: identify it by name,
verify it has zero `FormalSystem.*` imports, add Init to it, and record the correction — do not
add Init to arbitrary non-minimal modules to force the count down.

**Files to modify**:

- `FormalSystem/Syntax/Atom.lean` - one import line
- `FormalSystem/Automation/TruthNormAttr.lean` - one import line
- `FormalSystem/ForMathlib.lean` - one import line (aggregator; the rule's scope is the directory)

**Verification**:

- `lake build` exits 0 across the whole tree.
- `lake exe checkInitImports` prints nothing and exits 0.
- `scripts/check-metalogic-cycles.sh` still reports exactly 1 directory-level cycle.
- `FormalSystem/ForMathlib/Order/PFilter.lean` has no `import FormalSystem.` line.

---

### Phase 5: Wire C24 into check-module-invariants.sh [NOT STARTED]

**Goal**: Turn the now-clean checker into an enforced gate inside the invariants harness, following
the harness's own five-part wiring shape and the C16 build-requiring template.

**Tasks**:

- [ ] Add a `C24` row to the `# Checks:` header block, describing it as: every `FormalSystem`
      module transitively imports `FormalSystem.Init`, via `lake exe checkInitImports`.
- [ ] Add `ENFORCE_C24=${ENFORCE_C24:-1}   # every module transitively imports FormalSystem.Init (enforced)`
      to the flags block near line 497, with the other `ENFORCE_C*` declarations.
- [ ] Add the C24 check block following the **C16 template**: a `# ---` banner, a prose rationale
      explaining why the Init root exists (single place from which repo-wide linter/tactic imports
      are inherited) and why the check ships enforced with no soft period, then
      `if [ "$RUN_BUILD" -eq 1 ]; then` … `C24_LOG=$(mktemp)` … `lake exe checkInitImports` …
      `pass`/`fail` (with `soft` on `ENFORCE_C24=0`) … `note`-ed `tail` of the log on failure …
      `rm -f "$C24_LOG"` … `else info C24 "… skipped (--no-build)"; fi`.
- [ ] The block **must** sit inside the `RUN_BUILD` guard: `CoreM.withImportModules` needs the
      built `.olean`s and cannot run under `--no-build`.
- [ ] No new companion file is introduced, so the `# Companion files:` header block is unchanged.
- [ ] Add a C24 row to the "What It Checks" table in `docs/development/MODULE_INVARIANTS.md`. Do
      **not** back-fill the missing C16–C23 rows (research D6; out of scope).
- [ ] Commit at green.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: full

The phase's verification is running `bash scripts/check-module-invariants.sh` in build mode, which
is the repository's complete gate set by definition.

**Scope Hypothesis**: **C24** is the next free check identifier (the header block currently runs
B0, C1–C23, C9D, INV, and `grep -c C24 scripts/check-module-invariants.sh` returns 0). Confirm that
grep returns 0 before authoring the block; if it does not, take the next free identifier and use it
consistently across all four wiring sites.

**Files to modify**:

- `scripts/check-module-invariants.sh` - header row, `ENFORCE_C24` flag, `RUN_BUILD`-guarded check
  block
- `docs/development/MODULE_INVARIANTS.md` - one C24 row in the "What It Checks" table

**Verification**:

- `bash scripts/check-module-invariants.sh --no-build` emits `INFO C24 … skipped (--no-build)` and
  still reports ALL CHECKS PASSED.
- `bash scripts/check-module-invariants.sh` emits `PASS C24` and reports ALL CHECKS PASSED.

---

### Phase 6: Mandated Negative Test and Final Gate [NOT STARTED]

**Goal**: Prove the new gate can actually fail — `docs/development/MODULE_INVARIANTS.md`
§"Adding a Check" mandates a deliberate negative test, on the C15 precedent — then close the task
against the full acceptance criteria.

**Tasks**:

- [ ] Negative test: temporarily remove the `import FormalSystem.Init` line from one low-fan-out
      leaf (`FormalSystem/Automation/NormalizationAttr.lean` is the cheapest — fan-out 17).
- [ ] Rebuild through the guard and run `bash scripts/check-module-invariants.sh`. Confirm
      `FAIL C24`, a non-zero script exit status, and that the `note`-ed log tail names the affected
      modules.
- [ ] Restore the import line, rebuild, and confirm `PASS C24` plus ALL CHECKS PASSED. Record both
      observed outcomes in the execution summary — a gate that has never been observed to fail is
      not evidence of anything.
- [ ] Confirm the exit-status fix independently: `lake exe checkInitImports; echo $?` must print 0
      on the clean tree, and 1 (never a truncated count) with the import removed.
- [ ] Final acceptance sweep: `lake build` green; `lake exe checkInitImports` reports zero missing;
      `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.
- [ ] Re-read `FormalSystem/Init.lean` and `scripts/CheckInitImports.lean` docstrings and confirm
      no residual claim that the rewrite or the wiring is a follow-up.
- [ ] Commit at green.

**Timing**: 1 hour

**Depends on**: 5

**Verification Tier**: full

The negative test deliberately drives the tree red and back to green; only the full gate set can
establish that both transitions happened as intended.

**Scope Hypothesis**: The negative test asserts that removing exactly one leaf import produces a
`FAIL C24` naming approximately 18 modules (the leaf plus its 17 dependents). Confirm against the
actual `note`-ed count; the exact figure matters less than that it is non-zero and that the script
exit status is non-zero.

**Files to modify**:

- `FormalSystem/Automation/NormalizationAttr.lean` - transiently, for the negative test only;
  restored before the phase closes. No net change.

**Verification**:

- Observed `FAIL C24` with a non-zero script exit during the negative test.
- Observed `PASS C24` and ALL CHECKS PASSED after restoration.
- `lake exe checkInitImports` exits 0 on the clean tree.
- Working tree contains no leftover scratch or probe files.

---

## Lean Challenge Statements

Not applicable. This task has **no proof obligations** — the work is import-graph adoption and
build-tooling wiring, with no theorem to state and no goal state to close. The `- **Goals**:`
bullets above name no theorem identifiers (every backticked token there is a module path, a file
path, a shell variable, or a check identifier), so there is no identifier set for a Challenge
module to pin and no ```` ```lean ```` block is provided.

## Testing & Validation

- [ ] `lake exe checkInitImports` reports **zero** modules missing `FormalSystem.Init` and exits 0.
- [ ] `lake exe checkInitImports` exits **1** (not a truncated count) when the condition is violated
      — observed directly during the Phase 6 negative test.
- [ ] `lake build` exits 0 across the whole tree.
- [ ] `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED, including `PASS C24`.
- [ ] `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED, with C24
      cleanly skipped rather than failing.
- [ ] `FAIL C24` observed at least once, with a non-zero script exit (mandated negative test).
- [ ] `scripts/check-metalogic-cycles.sh` still reports exactly 1 directory-level cycle — no import
      cycle introduced.
- [ ] `FormalSystem/ForMathlib/Order/PFilter.lean` still has zero `FormalSystem.*` imports; the
      documented upstreaming rule is intact.
- [ ] No `sorry`, no new axiom, no deferral introduced (C3 and C14 assert this independently).

## Artifacts & Outputs

- `FormalSystem/Init.lean` — corrected docstring (deferral claim removed)
- `scripts/CheckInitImports.lean` — constant exit return, new `exceptions` entry, corrected
  docstring
- `scripts/check-module-invariants.sh` — C24 header row, `ENFORCE_C24` flag, gated check block
- `docs/development/MODULE_INVARIANTS.md` — C24 row in the "What It Checks" table
- Eleven `FormalSystem/**/*.lean` files — one `import FormalSystem.Init` line each (the ten
  non-`ForMathlib` minimal elements plus `FormalSystem/ForMathlib.lean`)
- `specs/541_formalsystem_init_transitive_import_adoption/summaries/01_*-summary.md` — execution
  summary recording both negative-test outcomes and the final measured count

## Rollback/Contingency

Every phase commits only at green, so `git revert` of any phase commit returns the tree to a
building state. The change is additive and import-only: there is no data migration, no signature
change, and no deleted code.

- **If new linter warnings appear at scale** (R3): they surface in the Phase 2 build against ~36
  modules. Fix them in-tree. Do **not** revert the Init import to silence them — that reintroduces
  the debt this task exists to clear.
- **If the full rebuild in Phase 4 cannot complete** (memory pressure, R7): the tree is still green
  at the Phase 3 commit. Re-run through the guard with no concurrent builds; if it still fails,
  stop and mark the phase `[PARTIAL]` rather than committing a half-built state.
- **If a module remains missing after all 11 edits**: the static model missed a minimal element.
  Identify it by name from the checker output, confirm it has zero `FormalSystem.*` imports, and
  add Init to it. Do not force the count down by importing Init into non-minimal modules.
- **If C24 cannot be made to fail during the negative test**: do not ship the gate. A gate that
  passes on everything is worse than no gate — investigate the exit-status path first (that is the
  known R2 failure mode), then the harness wiring.
