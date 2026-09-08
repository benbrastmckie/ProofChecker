# Implementation Plan: Task #550

- **Task**: 550 - Decompose `MintBound.lean` for publication legibility
- **Status**: [COMPLETED]
- **Effort**: 10.75 hours (phase timings sum exactly; build waits are passive)
- **Dependencies**: 549 (completed), 554 (completed) — both resolved; no live blocker
- **Research Inputs**: specs/550_decompose_mintbound_for_publication_legibility/reports/01_decompose-mintbound-publication-legibility.md
- **Artifacts**: plans/01_decompose-mintbound-publication-legibility.md (this file),
  summaries/01_decompose-mintbound-publication-legibility-summary.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` is 15,684 lines —
3.08x the next-largest live file in the tree — and is therefore effectively unreviewable. This
plan splits it into 18 modules under `MintBound/`, retaining `MintBound.lean` as the sibling
aggregator that invariant C8 requires and that preserves the downstream interface exactly. The
cut is at existing `/-!` section boundaries in **file order**, which the research measured to be
the dependency order (zero forward references); the C9 do-not-re-attempt register — 908 lines of
pure prose carrying zero declarations — is extracted first as `Register.lean`. Definition of
done: `lake build` green, `scripts/check-module-invariants.sh` green, all 751 declaration names
preserved byte-for-byte, sorry count and `#print axioms` baselines unchanged.

### Research Integration

The report is the measurement this plan is built on and its numbers are adopted wholesale: the
composition table (49.0% code / 45.0% prose), the 30-section line budget, the 18-module partition
with per-module minimal imports, and the 16 cross-boundary `private` declarations. Three findings
shape the phase structure directly:

1. **`private` is the only interface change.** Lean 4 `private` is module-scoped, and the repo has
   already paid for ignoring this once (`pick_split'` at `:6001-6003` duplicates `Fuel.lean`'s
   private `pick_split`). Sixteen declarations lose the modifier; nothing else about them moves.
   This is isolated into its own phase precisely so that every later phase is a pure relocation.
2. **File order is the only acyclic cut.** The thematic A/B/C/D grouping is cyclic on measurement
   (A↔B, C↔D), so realizing it would require reordering declarations and re-elaborating the file.
   Rejected on measurement, not taste.
3. **Builds are expensive (5-25 min).** Verification is batched into five build gates rather than
   one per file (18 builds, prohibitive) or one at the very end (no failure localization).

Four facts were confirmed against the tree during planning and are **not** in the report:

- **Zero name collisions.** Each of the 16 names to be de-privatized is declared exactly once
  across `FormalSystem/` and `Tests/` (excluding Boneyard). De-privatization cannot collide.
- **Zero file-scoped `set_option`.** All 25 `set_option` lines (23 `maxHeartbeats`, 2
  `linter.unusedTactic`) are the per-declaration `... in` form and travel with their declaration.
  Nothing must be replicated into module headers. The report's "22" is 23.
- **Extraction spans must be adjusted at both ends of the file.** `Invariants.lean` takes lines
  **61**-1068, not 1-1068: lines 1-60 are the license, the sole import, the 47-line module
  docstring, `namespace`, and `open`, and they are the basis of the aggregator. `Register.lean`
  takes the `/-! ## C9 ... -/` block only; line 15684's `end FormalSystem.Metalogic.Decidability`
  stays with the residual file and must be re-added at its new tail the moment C9 leaves.
- **No `section ... end` block straddles a cut.** All five (`MultiplicityRefutation` 4632-4787,
  `BranchingNonVacuity` 5100-5128, `FreshWorldRefutation` 5817-5987,
  `FreshWorldRefutationAtEveryLabel` 11421-11575, `PostBlockingSettlesRefutation` 11599-12911) sit
  entirely inside a single proposed module.

### Prior Plan Reference

No prior plan. This is the first planning round for this task.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only and not modified. It references `MintBound.lean` at
lines 148, 158, 296, 327 and 339 — notably line 327, which states the C9 register "carries the
full, itemised list (24 entries as of 2026-08-25)". That count is now 25 and the register's own
header still says "Twenty-four". Extracting the register to its own module is what makes this
class of drift visible. No roadmap phase is added: `roadmap_flag` was not set on this dispatch,
so ROADMAP.md is neither snapshotted nor updated here.

## Goals & Non-Goals

**Goals**:
- Split `MintBound.lean` into 18 modules under
  `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/`, each cut at an existing
  `/-!` section boundary, max module 1,815 lines against today's 15,684.
- Extract the C9 do-not-re-attempt register into `MintBound/Register.lean` so that a reader can
  tell locally whether they are reading a live result or a record of a refuted approach.
- Retain `MintBound.lean` as the aggregator (invariant C8), preserving the downstream interface
  exactly: `FormalSystem/Metalogic/Decidability.lean` is not edited.
- Preserve all 751 declaration names and all proof terms byte-for-byte; widen visibility on
  exactly 16 declarations and nothing else.
- Keep `lake build` green, sorry-free and axiom-free, with the `#print axioms` baseline unchanged.
- Bring `Termination/README.md` and a new `MintBound/README.md` into agreement with the result.

**Non-Goals**:
- Removing, renaming, merging, or reordering any declaration. Disposition was settled by tasks 549
  and 554; this is a decomposition.
- Re-elaborating, shortening, or improving any proof.
- Realizing the thematic A/B/C/D grouping — rejected on a measured dependency cycle.
- Rewriting or condensing C9 register content. The register moves; it does not shrink.
- Any change to `Fuel.lean`, including retiring the `pick_split'` / `pick_splitOrdered'`
  duplicates that a de-privatized `Fuel.lean` would make removable. That is a separate decision.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A cross-boundary `private` consumer is missed; build fails after a 5-25 min pass | M | M | Phase 1 builds a static cross-boundary checker and re-runs it against the split tree before every build gate. Costs seconds, catches the whole error class. The 16-name list is already a whole-file reference cross-product, not a reading. |
| An extraction drops or duplicates lines silently | H | L | Phase 1 records the declaration-name set and per-range line counts; every extraction phase re-derives both from the split tree and diffs against baseline before its build gate. A `sed`-range extraction that loses a line changes the name set or the line total. |
| Elaboration behaves differently across a module boundary (instance or simp-set visibility) | H | L | The `open` is replicated into every code-bearing module; all `set_option` are per-declaration; all five `attribute [local simp]` blocks are section-scoped and fully contained. The build gate at each phase is the real check, and phases are batched at 4-5 modules so a failure localizes. |
| De-privatization collides with an existing public name | H | VL | Pre-checked during planning: each of the 16 names is declared exactly once tree-wide. Phase 2's isolated build gate confirms. |
| A build gate fails and the cause is ambiguous between several modules | M | M | Five gates, not one. The only semantic change (Phase 2) has a gate to itself, so every later failure is by construction a relocation error. |
| Register extraction leaves the residual file without its namespace `end` | M | M | Called out explicitly in Phase 3's tasks: line 15684 stays behind and is re-appended at the new tail. Caught immediately by the phase's build gate. |
| Foreground `lake build` livelocks at the 10-minute tool cap | H | H | Every build in this plan runs detached and guarded per `context/project/lean4/operations/long-builds.md`: `Bash(run_in_background: true)` around `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- <args>`. Never a plain foreground `lake build`. |
| `Register.lean`, having no imports, becomes the sole new `checkInitImports` violation | L | M | Give it one import (`...Termination.Fuel`) for graph hygiene, per the research recommendation. |
| README module tables drift from the result | L | M | Phase 7 writes both from the partition table, in parallel with extraction; Phase 8 re-verifies the line counts against the tree before closing. The existing stale row (14,770 vs 15,684) is the evidence this drifts when deferred. |
| A concurrent session claims `MintBound.lean` mid-split | H | L | Both blocking dependencies are `completed` and 554's commit `973c4a39e` has landed. `file_scope` names this file exclusively. Phase 1 records `git rev-parse HEAD`; any phase finding the file changed underneath it stops rather than merging. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 7 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |
| 7 | 8 | 6, 7 |

Phases within the same wave can execute in parallel. Phase 7 (documentation) touches only
markdown and is deliberately overlapped with the extraction phases, which touch only Lean.

---

### Phase 1: Baseline capture and static extraction harness [COMPLETED]

**Goal**: Establish the invariants every later phase is checked against, and build the
seconds-cheap static checks that catch relocation errors before an expensive build does.

**Tasks**:
- [x] Record `git rev-parse HEAD` and confirm `MintBound.lean` is unmodified in the working tree.
- [x] Record baselines to a scratch file: total line count (expect 15,684); declaration count
      (expect 751) and the full sorted declaration-name set; `private` count (expect 92);
      `grep -c sorry` on the file; `#print axioms` output for the flagship theorems named in
      `docs/development/MODULE_INVARIANTS.md`'s C2 baseline.
- [x] Write a scratch harness script (under the session scratchpad, **not** under `.claude/**` or
      `FormalSystem/**`) providing three checks, each runnable in seconds:
      (a) declaration-name-set diff between the split tree and baseline;
      (b) total-line and per-module line accounting against the partition table;
      (c) cross-boundary `private` use — for each module, every name it references that is
      declared `private` in a different module.
- [x] Verify the 18-way partition covers lines 1-15,684 with no gap and no overlap, and that each
      boundary line is an existing `/-!` header (confirmed at planning for all 17 interior
      boundaries).
- [x] Verify no `section ... end` block straddles a boundary (five blocks, all confirmed contained
      at planning; re-confirm mechanically). *(deviation: altered — five real `section ... end`
      blocks confirmed contained; separately, the plan's "five `attribute [local simp]` blocks"
      measured as three (`:4696`, `:5870`, `:11471`), each inside one of those sections and so
      still fully contained)*
- [x] Run check (c) against the *current* single file partitioned notionally, and confirm it
      reproduces exactly the 16 names in the research table. A different answer means the plan's
      de-privatization set is wrong and Phase 2 must be re-scoped before proceeding.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts 15,684 lines, 751 declarations, 92 `private`
declarations, exactly 16 cross-boundary private uses, and an 18-module partition whose spans are
gapless. Confirm each mechanically in this phase's own tasks; a mismatch on any of them
invalidates the partition table and must be reported before Phase 2 begins rather than absorbed.

**Files to modify**:
- (none under version control) — scratch harness and baseline record only.

**Verification**:
- Baseline file exists and records all six figures above.
- Harness check (c) returns exactly the 16 names from the research table.
- Partition coverage check reports no gap, no overlap, no straddled section.

---

### Phase 2: De-privatize the 16 cross-boundary declarations, in place [COMPLETED]

**Goal**: Make the one and only semantic change of this task, in the file's current single-module
form, so that every subsequent phase is a pure relocation and any later build failure is
unambiguously an extraction error.

**Tasks**:
- [x] Drop the leading `private ` modifier from exactly these 16 declarations in
      `MintBound.lean`, changing nothing else on those lines or in those proofs: `pickOrd`
      (`:963`), `pick_ord_eq` (`:972`), `pickBranches` (`:1132`), `pick_branches_eq` (`:1139`),
      `pick_stage_source` (`:1163`), `pickOrd_mono` (`:1928`), `mfp` (`:4634`), `mfq` (`:4635`),
      `fwp` (`:5819`), `rm_bn` (`:5859`), `mwE` (`:7286`), `mwG` (`:7287`), `mwP` (`:7288`),
      `mwQ` (`:7289`), `pickBranches_time_dichotomy` (`:7157`),
      `pickBranches_knownTimes_subset` (`:13335`).
- [x] Re-run Phase 1 check (a): the declaration-name set must be unchanged; only the private count
      changes, 92 to 76.
- [x] **Build gate.** Detached and guarded:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- FormalSystem` under
      `Bash(run_in_background: true)`. Never a plain foreground `lake build`.
      *(deviation: altered — the plan's argument vector is rejected by the guard, which requires a
      recognized lake subcommand as the first argument after `--` and exits 77 without building.
      The corrected form, used at every gate in this task, is
      `bash .claude/scripts/lake-build-guard.sh build --timeout 2400 --no-share -- build FormalSystem`,
      with the exit code captured directly rather than through a pipe that would mask it.)*
- [x] Confirm the build is green, sorry count unchanged, and the C2 `#print axioms` baseline
      unchanged.
- [x] Commit.

**Timing**: 0.75 hours (edits are minutes; the build gate is a passive wait)

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that exactly 16 declarations need de-privatizing and that
none collides with an existing public name. Confirm by re-running Phase 1 check (c) before editing
and by the build gate after; a 17th name surfacing means the partition, not just this phase, needs
revisiting.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — remove the `private`
  modifier on 16 declarations; no other change.

**Verification**:
- `lake build` green.
- Declaration-name set identical to baseline; private count 76.
- Sorry count and `#print axioms` baselines unchanged.

---

### Phase 3: Extract the register and the foundation head (4 modules) [COMPLETED]

**Goal**: Create `MintBound/`, land the highest-value extraction (the C9 register) and the three
foundation modules, and prove the extraction shape works before committing to it fourteen more
times.

Each extracted module gets, in order: the 4-line Apache license header identical to
`MintBound.lean`'s; its minimal `import` lines; a `/-! # ... -/` module docstring promoted from
the section's existing `## `-level header; `namespace FormalSystem.Metalogic.Decidability`;
`open FormalSystem.Syntax`; the extracted body verbatim; `end FormalSystem.Metalogic.Decidability`.
`Register.lean` is the exception — zero declarations, so no namespace and no `open`.

**Tasks**:
- [x] Create `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/`.
- [x] Extract `Register.lean` from the `/-! ## C9 ... -/` block (lines 14,777-15,682). Give it one
      import (`...Termination.Fuel`) for `checkInitImports` hygiene. Promote its heading `## C9.`
      to `#`. **Re-append `end FormalSystem.Metalogic.Decidability` at the residual file's new
      tail** — line 15,684 does not travel with the register.
- [x] In `Register.lean` only, correct the register header's "Twenty-four statements" to
      "Twenty-five". This is an additive correction of a demonstrably wrong count (the register
      carries 25 numbered entries), not a weakening of register content; no entry is altered,
      condensed, or dropped.
- [x] Extract `Invariants.lean` from lines **61**-1,068 (not 1-1,068). Imports: `...Termination.Fuel`.
- [x] Extract `OrderingTimes.lean` from lines 1,069-2,071. Imports: `...MintBound.Invariants`.
- [x] Extract `MintPotential.lean` from lines 2,072-3,886. Imports: `...MintBound.OrderingTimes`.
- [x] Update the residual `MintBound.lean`: keep lines 1-60 (license, module docstring, namespace,
      `open`) and replace its single `Fuel` import with imports of the four new modules; the body
      now begins at what was line 3,887.
- [x] Re-run Phase 1 checks (a), (b), (c) against the split tree. *(deviation: altered — three
      further checks were added and run alongside: (d) import-closure, which proves every
      cross-module reference lands inside the referencing module's import closure; a line-multiset
      provenance audit, which showed the only content difference between the split tree and the
      pre-split snapshot is the four promoted `##`->`#` headings; and an axiom-set diff against the
      Phase 2 build's 41 `#print axioms` rows.)*
- [x] **Prose hygiene, not in the plan but forced by the split.** Four same-line docstring edits,
      made before extraction so no line number shifts: the three self-citations
      `MintBound.lean:1260` (once) and `MintBound.lean:1071` (twice) are replaced by the
      declaration names they meant, because the aggregator will be ~40 lines and invariant C20
      tier 1 gates out-of-range `file.lean:NNN` citations repo-wide; and the pre-existing C9
      violation at `:12413` ("Task 433's narrowing") becomes "`PostBlockingSettlesRun`'s
      narrowing", which is the durable anchor the same invariant asks for.
- [x] **Build gate** (detached + guarded, as in Phase 2).
- [x] Commit the batch as one objective once green.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts four modules at spans 61-1,068 / 1,069-2,071 /
2,072-3,886 / 14,777-15,682, and that `Register.lean` carries zero declarations. Confirm with
Phase 1 checks (a) and (b) before the build gate: the declaration-name set must be unchanged and
the per-module line accounting must total 15,684 plus the new per-module headers.

**Files to modify**:
- `.../Termination/MintBound/Register.lean` — new, ~915 lines, zero declarations.
- `.../Termination/MintBound/Invariants.lean` — new, ~1,015 lines, 63 declarations.
- `.../Termination/MintBound/OrderingTimes.lean` — new, ~1,010 lines, 51 declarations.
- `.../Termination/MintBound/MintPotential.lean` — new, ~1,822 lines, 90 declarations.
- `.../Termination/MintBound.lean` — imports rewritten; lines 61-3,886 and the C9 block removed;
  namespace `end` re-appended at the new tail.

**Verification**:
- `lake build` green; sorry and axiom baselines unchanged.
- Declaration-name set identical to baseline.
- `Register.lean` contains zero declarations and 25 numbered register entries.

---

### Phase 4: Extract the measure and closure stack (4 modules) [COMPLETED]

**Goal**: Extract the C7-C10 and D1 mid-stack, the first point at which the import DAG gains real
parallel branches (`TimeCensus` alongside `Terminus`/`ClosureResidual`).

**Tasks**:
- [x] Extract `Measure.lean` from lines 3,887-5,129. Imports: `...MintBound.MintPotential`.
      Contains `section MultiplicityRefutation` and `section BranchingNonVacuity` in full.
- [x] Extract `Terminus.lean` from lines 5,130-5,388. Imports: `...MintBound.Measure`.
- [x] Extract `ClosureResidual.lean` from lines 5,389-6,535. Imports: `...MintBound.Terminus`.
      Contains `section FreshWorldRefutation` in full.
- [x] Extract `TimeCensus.lean` from lines 6,536-7,218. Imports: `...MintBound.MintPotential`
      (a parallel branch, not a chain link — do not import `ClosureResidual`).
- [x] Update the residual `MintBound.lean` imports; body now begins at what was line 7,219.
- [x] Re-run Phase 1 checks (a), (b), (c).
- [x] **Build gate** (detached + guarded).
- [x] Commit the batch as one objective once green.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts four modules at spans 3,887-5,129 / 5,130-5,388 /
5,389-6,535 / 6,536-7,218, and that `TimeCensus` depends on `MintPotential` rather than on the
`Terminus`/`ClosureResidual` chain. Confirm the spans with check (b) and the import claim with
check (c) plus the build gate; a missing-import failure at the gate falsifies the parallel-branch
hypothesis and the import is added rather than the partition changed.

**Files to modify**:
- `.../MintBound/Measure.lean` — new, ~1,250 lines, 73 declarations.
- `.../MintBound/Terminus.lean` — new, ~266 lines, 7 declarations.
- `.../MintBound/ClosureResidual.lean` — new, ~1,154 lines, 57 declarations.
- `.../MintBound/TimeCensus.lean` — new, ~690 lines, 33 declarations.
- `.../Termination/MintBound.lean` — imports extended; lines 3,887-7,218 removed.

**Verification**:
- `lake build` green; sorry and axiom baselines unchanged.
- Declaration-name set identical to baseline.
- All three `section ... end` blocks in this range are wholly inside a single new module.

---

### Phase 5: Decompose D2, the verdict section (5 modules) [COMPLETED]

**Goal**: Break up the single largest section — D2 at 3,944 lines, itself 78% of the next-largest
live file in the repository. This is the phase that most directly delivers reviewability.

The five cuts fall on D2's own existing `###`/`####` sub-headers at 7,975 / 8,467 / 9,451 /
10,205. Those heading levels read wrong as module docstrings and must be promoted to `#`/`##`
during extraction; D2's own `## D2. MintPaysForTime: the verdict` preamble prose (7,219-7,974)
travels with `TimeReuse.lean` as its module docstring context.

**Tasks**:
- [x] Extract `TimeReuse.lean` from lines 7,219-7,974. Imports: `...MintBound.Measure`. Carries
      `mwE`/`mwG`/`mwP`/`mwQ`, now public.
- [x] Extract `MonotoneIssuance.lean` from lines 7,975-8,466. Imports:
      `...MintBound.ClosureResidual`, `...MintBound.TimeReuse`.
- [x] Extract `OrientedGate.lean` from lines 8,467-9,450. Imports: `...MintBound.MonotoneIssuance`.
- [x] Extract `FourComponent.lean` from lines 9,451-10,204. Imports: `...MintBound.TimeCensus`,
      `...MintBound.OrientedGate`.
- [x] Extract `SigmaFixed.lean` from lines 10,205-11,162. Imports: `...MintBound.FourComponent`.
- [x] Promote every extracted `###`/`####` module heading to `#`/`##`; read all five new files
      through once to confirm the docstrings read as module-level prose, not as fragments.
      *(deviation: altered — the read found three docstrings opening on a deictic that no longer
      had a referent once the cut was made, so three same-line prose repairs were added:
      `OrientedGate`'s "Phase 1's gate above" now names `MonotoneIssuance.lean`, `SigmaFixed`'s
      "The subsection above" now names `FourComponent.lean`, and `MonotoneIssuance`'s "nothing
      below it is assumed anywhere above" becomes a statement about its import direction. The
      repair is scoped to these five module docstrings; body-level "above"/"below" deictics that
      now cross a module boundary are NOT swept, and are recorded as a follow-up.)*
- [x] Update the residual `MintBound.lean` imports; body now begins at what was line 11,163.
- [x] Re-run Phase 1 checks (a), (b), (c).
- [x] **Build gate** (detached + guarded).
- [x] Commit the batch as one objective once green.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts that D2's 3,944 lines split cleanly at 7,975 / 8,467 /
9,451 / 10,205 into five modules totalling 207 declarations, and that each cut point is an
existing sub-header. Confirm the header claim by reading each boundary line before cutting
(verified at planning) and the declaration total with check (a); a cut that lands mid-declaration
changes the name set and is caught before the build gate.

**Files to modify**:
- `.../MintBound/TimeReuse.lean` — new, ~763 lines, 46 declarations.
- `.../MintBound/MonotoneIssuance.lean` — new, ~500 lines, 24 declarations.
- `.../MintBound/OrientedGate.lean` — new, ~991 lines, 55 declarations.
- `.../MintBound/FourComponent.lean` — new, ~761 lines, 26 declarations.
- `.../MintBound/SigmaFixed.lean` — new, ~965 lines, 56 declarations.
- `.../Termination/MintBound.lean` — imports extended; lines 7,219-11,162 removed.

**Verification**:
- `lake build` green; sorry and axiom baselines unchanged.
- Declaration-name set identical to baseline.
- No new module docstring opens at `###` or deeper.

---

### Phase 6: Extract the residual tail and finalize the aggregator (5 modules) [COMPLETED]

**Goal**: Move the last five sections out and reduce `MintBound.lean` to a BiLasso-shaped
aggregator: license, 18 imports, and a reader-facing `## Submodules` map.

**Tasks**:
- [x] Extract `LabelHeadroom.lean` from lines 11,163-11,577. Imports:
      `...MintBound.ClosureResidual`, `...MintBound.TimeCensus`. Contains
      `section FreshWorldRefutationAtEveryLabel` in full.
- [x] Extract `PostBlocking.lean` from lines 11,578-12,912. Imports: `...MintBound.SigmaFixed`.
      Contains `section PostBlockingSettlesRefutation` and its nested `section
      PostBlockingRunProbe` in full.
- [x] Extract `UntlSnceFree.lean` from lines 12,913-13,598. Imports: `...MintBound.SigmaFixed`.
- [x] Extract `BoxFree.lean` from lines 13,599-14,128. Imports: `...MintBound.UntlSnceFree`.
- [x] Extract `MintPaysAssembly.lean` from lines 14,129-14,776. Imports:
      `...MintBound.UntlSnceFree`.
- [x] Reduce `MintBound.lean` to the aggregator: keep the license header; replace the body with 18
      `import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.*` lines; adapt
      the existing 47-line module docstring (lines 9-55) into a `## Submodules` map with one entry
      per module, matching `FormalSystem/Metalogic/Decidability/BiLasso.lean`'s shape. Drop
      `namespace` and `open` — the aggregator declares nothing.
- [x] Confirm `FormalSystem/Metalogic/Decidability.lean` is **not** edited: the aggregator
      re-exports everything, so the single downstream edge is preserved automatically.
- [x] Re-run Phase 1 checks (a), (b), (c). Check (c) must now return empty.
- [x] **Build gate** (detached + guarded).
- [x] Commit the batch as one objective once green.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: This phase asserts five modules at spans 11,163-11,577 / 11,578-12,912 /
12,913-13,598 / 13,599-14,128 / 14,129-14,776, and that the finished aggregator contains exactly
18 imports and zero declarations. Confirm the import count and the zero-declaration claim
mechanically before the build gate; check (c) returning non-empty here means a private consumer
was missed and Phase 2's set was short.

**Files to modify**:
- `.../MintBound/LabelHeadroom.lean` — new, ~422 lines, 32 declarations.
- `.../MintBound/PostBlocking.lean` — new, ~1,342 lines, 68 declarations.
- `.../MintBound/UntlSnceFree.lean` — new, ~693 lines, 37 declarations.
- `.../MintBound/BoxFree.lean` — new, ~537 lines, 14 declarations.
- `.../MintBound/MintPaysAssembly.lean` — new, ~655 lines, 19 declarations.
- `.../Termination/MintBound.lean` — reduced to aggregator: license, 18 imports, `## Submodules`
  map. Zero declarations.

**Verification**:
- `lake build` green; sorry and axiom baselines unchanged.
- Declaration-name set identical to baseline; 751 declarations across the 18 modules, 0 in the
  aggregator.
- Cross-boundary private check returns empty.
- `Decidability.lean` shows no diff.

---

### Phase 7: Documentation — directory README and module tables [COMPLETED]

**Goal**: Bring the two READMEs into agreement with the 18-module result, in parallel with the
extraction phases. Markdown only; zero compile surface.

**Tasks**:
- [x] Add `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/README.md` following
      the repo's directory-README convention, carrying the 18-module table (module, lines,
      declarations, one-line role) and the import DAG's shape, including its parallel branches.
- [x] Update `Termination/README.md`: the `| MintBound.lean | 14770 | ... |` row is already stale
      against 15,684 and must now describe the aggregator plus its directory.
- [x] Cite declaration names and file names only. **No task-number citations** anywhere under
      `FormalSystem/` — invariant C9 of `docs/development/MODULE_INVARIANTS.md` and
      `.claude/rules/no-task-references-in-deliverables.md`.
- [x] Verify every module name and path written here resolves against the tree as it stands when
      this phase runs; leave line counts to Phase 8 to confirm.

**Timing**: 1 hour

**Depends on**: 3 *(deviation: altered — run after Phase 6 rather than overlapped with Phase 4,
so that every module path the READMEs cite already resolves and no intermediate commit can leave
C5/C12/C13 red. There is no second agent here, so the overlap bought nothing.)*

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts an 18-row module table with per-module line counts taken
from the partition table. Those counts are plan-time estimates that exclude the new per-module
headers; Phase 8 confirms them against the tree and corrects them there rather than here.

**Files to modify**:
- `.../Termination/MintBound/README.md` — new.
- `.../Termination/README.md` — `MintBound.lean` row rewritten; directory added.

**Verification**:
- Both files render; every path cited exists (paths for modules not yet extracted are checked in
  Phase 8).
- Zero task-number citations under `FormalSystem/`.

---

### Phase 8: Final gate — invariants, baselines, and count reconciliation [COMPLETED]

**Goal**: Close the task against the full repository gate set and reconcile every asserted count
with the tree as built.

**Tasks**:
- [x] **Two gate failures surfaced and were fixed, neither anticipated by the plan.** C16's
      `docBlame` linter reported 7 new findings — `mfp`, `mfq`, `fwp`, `mwE`, `mwG`, `mwP`, `mwQ`,
      the witness atoms Phase 2 de-privatized, since `docBlame` does not see `private`
      declarations. Each was given a one-line docstring; grandfathering them via
      `runLinter --update` was rejected because the regression is real. `INV` reported two stale
      generated inventory blocks (also failing before this task began, from concurrent work);
      the split's +18 files and +199 lines made them stale on this task's own account too, so
      `--emit-inventory` was run and both blocks are now current.
- [x] Run `bash scripts/check-module-invariants.sh`; confirm C4 (imports resolve), C6 (no
      unreachable live module; no manifest entry needed, since the aggregator imports all 18) and
      C8 (`MintBound.lean` sits beside `MintBound/`) all pass.
- [x] Run `lake exe checkInitImports`; confirm no new violation, in particular that `Register.lean`
      is not flagged. *(deviation: altered — the plan's expectation is falsified, and the reason
      matters. `checkInitImports` reports 453 modules that do not transitively import
      `FormalSystem.Init`, and `Fuel.lean`, `TimeTypeBound.lean`, `SubformulaProperty.lean` and
      the pre-split `MintBound.lean` were all already among them. Every new module imports `Fuel`,
      so all 18 inherit the status structurally; giving `Register.lean` a `Fuel` import for
      "hygiene" cannot avoid it, because `Fuel` is itself flagged. The set grows from 435 to 453 —
      no new KIND of violation. The executable is declared in `lakefile.lean` and is not wired
      into CI or into `check-module-invariants.sh`, so nothing gates on it.)*
- [x] **Final full build gate** (detached + guarded), from a clean state.
- [x] Diff against the Phase 1 baseline: declaration-name set identical (751 names); sorry count
      unchanged; `#print axioms` output for the C2 flagship theorems unchanged.
- [x] Reconcile the per-module line counts in both READMEs against `wc -l` on the tree; correct
      any that drifted from the plan-time estimates.
- [x] Confirm `MintBound.lean` is now under 100 lines and the largest module is under 2,000.
      *(deviation: altered — the largest module is `MintPotential.lean` at 1,828 lines, under
      2,000 as asserted. The aggregator is 121 lines, not under 100: the `## Submodules` map with
      18 entries plus the retained A/B/C/D overview does not fit in 100, and the overview is the
      file's orientation. Measured and reported rather than met by deleting prose.)*
- [x] Confirm zero task-number citations under `FormalSystem/`.
- [x] Commit.

**Timing**: 1 hour

**Depends on**: 6, 7

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that the sorry count, the declaration-name set (751), and
the `#print axioms` baseline are all unchanged from Phase 1, and that the README line counts match
the tree. Confirm each by direct diff against the Phase 1 baseline record; any divergence is a
defect to fix, never a baseline to update.

**Files to modify**:
- `.../Termination/MintBound/README.md`, `.../Termination/README.md` — line-count corrections only,
  if any.

**Verification**:
- `check-module-invariants.sh` green on C1, C2, C3, C4, C6, C8, C9, C14.
- `lake build` green from clean.
- Baseline diff empty on names, sorries, and axioms.

---

## Lean Challenge Statements

This plan proves no theorems. It relocates existing proof terms without re-elaborating any goal,
alters no statement, and introduces no declaration. The identifier set under `- **Goals**:` is
therefore empty by construction, and this section's identifier set is empty to match — the two
agree, as the cross-validation requires. No fenced `lean` block is given, because emitting one
would assert a proof obligation this task does not have.

The zero-debt claim rests on this: the task does not merely avoid `sorry`, it has no proof
obligation at all. The `#print axioms` baseline is untouched because the proof terms are untouched.

## Testing & Validation

- [x] `lake build` green at every one of the five build gates (Phases 2, 3, 4, 5, 6) and at the
      final gate (Phase 8), each run detached and guarded per
      `context/project/lean4/operations/long-builds.md`.
- [x] `bash scripts/check-module-invariants.sh` passes C4, C6 and C8 after the split.
- [x] `lake exe checkInitImports` reports no new violation. *(deviation: altered — it reports the
      same KIND of finding for the 18 new modules that it already reported for `Fuel.lean`,
      `TimeTypeBound.lean`, `SubformulaProperty.lean` and the pre-split `MintBound.lean`; the
      total moves 435 -> 453. The executable is not wired into CI or the invariant gate.)*
- [x] Declaration-name set is byte-identical to the Phase 1 baseline: 751 names, no addition, no
      removal, no rename.
- [x] `private` count drops from 92 to 76 and by no more.
- [x] Sorry count unchanged (zero); `#print axioms` unchanged for the C2 flagship theorems.
- [x] `FormalSystem/Metalogic/Decidability.lean` has no diff across the whole task.
- [x] Cross-boundary private-use check returns empty against the final tree.
- [x] The C9 register in `Register.lean` retains all 25 entries verbatim, with only the header's
      "Twenty-four" corrected.
- [x] Zero task-number citations under `FormalSystem/`.

## Artifacts & Outputs

- `plans/01_decompose-mintbound-publication-legibility.md` (this file)
- `summaries/01_decompose-mintbound-publication-legibility-summary.md`
- 18 new modules under
  `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/`: `Invariants`,
  `OrderingTimes`, `MintPotential`, `Measure`, `Terminus`, `ClosureResidual`, `TimeCensus`,
  `TimeReuse`, `MonotoneIssuance`, `OrientedGate`, `FourComponent`, `SigmaFixed`, `LabelHeadroom`,
  `PostBlocking`, `UntlSnceFree`, `BoxFree`, `MintPaysAssembly`, `Register`
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — reduced to an
  aggregator
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/README.md` — new
- `FormalSystem/Metalogic/Decidability/Verified/Termination/README.md` — updated module table

## Rollback/Contingency

Every phase commits only on a green build, so the working tree is never left red at a phase
boundary and `git revert` of a phase's commit restores a known-green state. Because the phases are
strictly sequential on the same file, revert in reverse order.

- **A build gate fails**: the failure is localized to that phase's 4-5 modules. Re-run the
  cross-boundary private check first (seconds) before re-reading Lean errors; a missed private
  consumer is the most likely cause and the cheapest to confirm. Do not proceed to the next phase
  with a red gate.
- **A missed cross-boundary `private` surfaces after Phase 2**: drop the modifier on that name in
  the module that declares it, note it as a Phase 2 undercount in the summary, and re-run the
  gate. Do not work around it by duplicating the declaration — that is precisely the
  `pick_split'` failure mode this task exists to stop reproducing.
- **The declaration-name set diverges from baseline**: a `sed` range is wrong. Revert the phase's
  commit and re-extract; never reconcile by editing declarations.
- **Full abandonment**: revert all phase commits back to the Phase 1 baseline SHA. Nothing outside
  `Verified/Termination/` and its two READMEs is touched, and `Decidability.lean` is never edited,
  so the blast radius of a full revert is contained to this directory.
