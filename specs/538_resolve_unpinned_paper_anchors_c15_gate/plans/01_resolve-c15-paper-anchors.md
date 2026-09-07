# Implementation Plan: Resolve unpinned paper anchors (C15 gate)

- **Task**: 538 - resolve_unpinned_paper_anchors_c15_gate
- **Status**: [IMPLEMENTING]
- **Effort**: 1 hour
- **Dependencies**: None
- **Research Inputs**: specs/538_resolve_unpinned_paper_anchors_c15_gate/reports/01_c15-anchor-resolution.md
- **Artifacts**: plans/01_resolve-c15-paper-anchors.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

C15 (paper-anchor citation resolution) is the sole failing check group in
`scripts/check-module-invariants.sh`. Research established that the unresolved set is FOUR
anchors, not the three named in the task description, and that all four resolve to live, labelled
`\label{}` targets in the current paper — so the DANGLING/unlabelled classification supplied with
the task is stale and no paper-side edit or cross-repo coordination is required. The fix is four
`LIVE-UNPINNED` rows inside the `KNOWN-ANCHORS` block of `specs/paper-definitions-of-record.md`
plus a dated narrative line; no `.lean` file changes, no manifest pins, no checksum re-pinning.
Definition of done: `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.

### Research Integration

Key findings carried into this plan from `reports/01_c15-anchor-resolution.md`:

- **Fourth anchor**: `app:ObjectiveModality` (cited at `FormalSystem/BaseLanguage/Axioms.lean:100`)
  was introduced by commit `d155835f2` after the task was written. Fixing only three leaves C15 red.
- **All four are LIVE and labelled** in `~/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`
  in both the working tree and `HEAD`: `app:ObjectiveModality` (`\subsection` label),
  `lem:deterministic-singleton` (`Lthm`), `app:drift` (`Tthm`), `cor:no-characterization` (`Cthm`).
  The task description's items (2) and (3) — "LIVE BUT UNLABELLED" and "expects an APPENDIX
  SECTION, which the paper does not have" — are no longer true.
- **All four are LIVE-UNPINNED, none manifest-pinnable.** Three are cited by name only.
  `DriftFrame.lean` quotes fragments, but those live in the paper's `\begin{proof}` block, which
  `resolve_env` does not capture — a pin would hash text the tree never quotes.
  `app:ObjectiveModality` cannot be pinned at all: `resolve_env` requires `\begin{...}` on the same
  line as `\label{}`, and this is a `\subsection{...}%` with the label on the following line
  (the existing `app:TaskSemantics` precedent).
- **Every citing docstring is faithful** — spot-checked against the live `.tex`; no docstring
  correction is needed anywhere.
- **Dry run confirms sufficiency**: with the four rows applied to a scratch copy, C15's exact
  pipeline returns an empty unresolved set over 52 cited anchors. C15 was the only failing group,
  so this is sufficient for ALL CHECKS PASSED.
- **`check-paper-definitions.sh` drift is OUT OF SCOPE** (re-measured at 15 drifted definitions /
  9 dangling anchors). That script is not invoked by `check-module-invariants.sh` and not run by
  CI; seven of the nine dangling anchors are the declared scope of the open fragment-removal /
  BX-rename work. It is recorded as a Reasoned Exclusion, not folded in.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context. `specs/ROADMAP.md` exists and treats
`scripts/check-module-invariants.sh` as its standing verification instrument (its header and the
2026-08-25 re-verification note both cite it), but carries no checkbox item specific to C15
anchor resolution. This plan restores that instrument to a fully green baseline; it advances no
named roadmap checkbox and adds none.

## Goals & Non-Goals

**Goals**:
- Record all four unresolved anchors as `LIVE-UNPINNED` rows in the `KNOWN-ANCHORS` block of
  `specs/paper-definitions-of-record.md`, with per-anchor classification notes.
- Log the classification decision as a dated line in the record's prose narrative, matching how
  earlier waves were logged.
- Make `bash scripts/check-module-invariants.sh` report ALL CHECKS PASSED.

**Non-Goals**:
- Any `.lean` edit. No docstring is dishonest; the three files in the task's declared `file_scope`
  (`Independence/{DriftFrame,RealTranslationFrame,StateSetTruth}.lean`) are read-only here.
- Any manifest pin, `FILE_CHECKSUM` re-pin, or `PINNED_COMMIT` re-pin.
- Any paper-side (`possible_worlds.tex`) edit, and any coordination with the PossibleWorlds
  `repair_paper_lean_anchor_drift` work — that work has already landed.
- Absorbing the `check-paper-definitions.sh` drift wave (15 drifted / 9 dangling). Excluded with
  evidence; see the Reasoned Exclusions obligation in Phase 3.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The unresolved set has drifted again since research (a new commit adds a fifth anchor) | M | M | Phase 1 re-measures the live unresolved set before editing and treats research's "four" as a hypothesis, not a fact |
| An anchor is recorded `LIVE-UNPINNED` while actually dangling, converting a detectable citation error into an undetectable one | H | L | Phase 1 re-confirms each anchor's `\label{}` against the live `.tex` before Phase 2 writes any row |
| ASCII sort order of the `KNOWN-ANCHORS` block broken by insertion | L | M | Phase 2 uses the research-supplied insertion points and Phase 3's full script run re-checks the block |
| Scope creep into the `check-paper-definitions.sh` drift wave | M | M | Explicit Non-Goal plus a required Reasoned Exclusions record in Phase 3 |
| Another check group regresses between the research baseline and now | M | L | Phase 3 runs the complete script, not just C15 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |

Phases within the same wave can execute in parallel.

### Phase 1: Re-measure the unresolved anchor set and confirm liveness [COMPLETED]

- **Goal:** Establish the current, measured unresolved-anchor set and confirm each member resolves
  to a live `\label{}` in the paper, before any file is edited.
- **Tasks:**
  - [x] Run `bash scripts/check-module-invariants.sh` and capture the C15 failure line and the
        enumerated unresolved anchors verbatim.
  - [x] Confirm C15 is still the only failing group; note any other failure for Phase 3.
  - [x] For each unresolved anchor, grep
        `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` for its
        `\label{}` and record the environment kind (`Lthm`/`Tthm`/`Cthm`/`\subsection`) and line.
  - [x] Classify each as `LIVE-UNPINNED` or `DANGLING` on that measured evidence; if any anchor
        does not resolve to a live label, stop and record it as `DANGLING` with the citing-site
        obligation rather than adding a live row.
  - [x] If the measured set differs from the four research names, carry the measured set forward —
        it, not the report, is authoritative for Phase 2.
- **Timing:** 20 minutes
- **Depends on:** none
- **Verification Tier:** prose
- **Scope Hypothesis:** Research asserts the unresolved set is exactly four anchors —
  `app:ObjectiveModality`, `app:drift`, `cor:no-characterization`, `lem:deterministic-singleton` —
  all four LIVE and labelled. Confirm by reading the C15 failure output from the live script run
  and by grepping each `\label{}` in `possible_worlds.tex`. A different count or a
  non-resolving label supersedes the report.
- **Files to modify:**
  - None (measurement only).
- **Verification:**
  - The captured C15 output enumerates a definite unresolved set.
  - Every member of that set has a recorded `\label{}` line number, or an explicit DANGLING finding.

---

### Phase 2: Add the LIVE-UNPINNED rows and the dated narrative line [COMPLETED]

- **Goal:** Record the measured anchors in `specs/paper-definitions-of-record.md` so C15 resolves.
- **Tasks:**
  - [x] Insert one row per anchor inside `<!-- KNOWN-ANCHORS:BEGIN -->` / `<!-- KNOWN-ANCHORS:END -->`,
        in the block's existing ASCII-sorted LIVE-UNPINNED-then-DANGLING ordering, format
        `anchor_id|status|note`:
        - `app:ObjectiveModality` before `app:TaskSemantics`
        - `app:drift` between `app:deterministic` and `app:topology-r0`
        - `cor:no-characterization` before `cor:perpetuity-valid`
        - `lem:deterministic-singleton` before `lem:history-time-shift-preservation`
  - [x] Write each note to state *why* the anchor is unpinned rather than manifest-pinned — cited
        by name only, or (for `app:ObjectiveModality`) structurally unpinnable because
        `resolve_env` requires `\begin{...}` on the `\label{}` line.
  - [x] Add a dated line to the record's prose narrative recording the classification decision,
        matching the format of earlier waves.
  - [x] Confirm no manifest row, `FILE_CHECKSUM`, or `PINNED_COMMIT` sentinel was touched
        (`git diff` on the record shows changes only inside `KNOWN-ANCHORS` and the narrative).
- **Timing:** 20 minutes
- **Depends on:** 1
- **Verification Tier:** local
- **Scope Hypothesis:** This phase asserts the edit is confined to exactly one file
  (`specs/paper-definitions-of-record.md`) and to four added rows plus one narrative line. Confirm
  with `git status --short` (one modified file) and `git diff --stat` (line count consistent with
  four rows plus narrative). A larger footprint means the phase overreached.
- **Files to modify:**
  - `specs/paper-definitions-of-record.md` - four `LIVE-UNPINNED` rows in the `KNOWN-ANCHORS`
    block, plus one dated narrative line.
- **Verification:**
  - Re-run C15's resolution in isolation (the script's C15 group, or the same MANIFEST +
    KNOWN-ANCHORS known-set / cited-set comparison) and confirm the unresolved set is empty.
  - `git diff` on the record touches nothing outside `KNOWN-ANCHORS` and the narrative.

---

### Phase 3: Full invariant run, exclusion record, and summary [NOT STARTED]

- **Goal:** Confirm ALL CHECKS PASSED across the whole invariant script and record the excluded
  `check-paper-definitions.sh` drift with evidence.
- **Tasks:**
  - [ ] Run `bash scripts/check-module-invariants.sh` in full; capture the terminal line and
        confirm it reads ALL CHECKS PASSED with no group failing.
  - [ ] Confirm C15 now passes with a resolved-citation count (research measured 52 cited anchors;
        treat the exact number as measured-at-run, not asserted).
  - [ ] Record a `#### Reasoned Exclusions` subsection under this phase for the
        `check-paper-definitions.sh` drift, with evidence: that script is not invoked by
        `check-module-invariants.sh` and not run by `.github/workflows/ci.yml` (which runs only
        `lean-action` build/test/lint), C15 resolves against the record and never the paper by
        documented design, and seven of the nine dangling anchors fall under the open
        fragment-removal / BX-rename work.
  - [ ] Write the implementation summary to
        `specs/538_resolve_unpinned_paper_anchors_c15_gate/summaries/01_c15-anchor-resolution-summary.md`,
        noting the four-not-three correction and the stale task-description classification.
- **Timing:** 20 minutes
- **Depends on:** 2
- **Verification Tier:** full
- **Scope Hypothesis:** This phase assumes C15 was the sole failing group and that Phase 2's edit
  is therefore sufficient for ALL CHECKS PASSED, and that the resolved-citation count is around 52.
  Confirm from the full script run's own output — the terminal ALL CHECKS PASSED line and C15's
  reported count. Any other failing group means the hypothesis was wrong and that failure must be
  reported, not absorbed into this task.
- **Files to modify:**
  - `specs/538_resolve_unpinned_paper_anchors_c15_gate/summaries/01_c15-anchor-resolution-summary.md` - new summary.
  - `specs/538_resolve_unpinned_paper_anchors_c15_gate/plans/01_resolve-c15-paper-anchors.md` - phase status markers and the Reasoned Exclusions record.
- **Verification:**
  - `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.
  - The Reasoned Exclusions table is present with `Item`, `Reason`, `Evidence` columns.

## Testing & Validation

- [ ] `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED, no group failing.
- [ ] C15 reports every cited paper anchor resolving against `specs/paper-definitions-of-record.md`.
- [ ] `git status --short` shows no `.lean` file modified by this task.
- [ ] The `KNOWN-ANCHORS` block remains ASCII-sorted with LIVE-UNPINNED rows before DANGLING rows.
- [ ] No `FILE_CHECKSUM` or `PINNED_COMMIT` sentinel changed.
- [ ] No `lake build` needed (no `.lean` file touched); if any Lean file is touched, the build must
      be run and must pass.

## Artifacts & Outputs

- `specs/paper-definitions-of-record.md` - four `LIVE-UNPINNED` `KNOWN-ANCHORS` rows plus a dated
  narrative line.
- `specs/538_resolve_unpinned_paper_anchors_c15_gate/summaries/01_c15-anchor-resolution-summary.md` -
  implementation summary including the Reasoned Exclusions record.
- `specs/538_resolve_unpinned_paper_anchors_c15_gate/plans/01_resolve-c15-paper-anchors.md` -
  this plan, with phase status markers updated.

## Rollback/Contingency

The entire change is additive text in one Markdown file under `specs/`. To revert:
`git checkout HEAD -- specs/paper-definitions-of-record.md` restores the prior record and returns
C15 to its known-red baseline; nothing else is affected because no `.lean` file, manifest pin, or
checksum sentinel is touched.

Contingency: if Phase 1 measurement finds an anchor that does NOT resolve to a live `\label{}`,
that anchor is `DANGLING`. Do not add a `LIVE-UNPINNED` row for it — add a `DANGLING` row and
ensure the citing site says so, per the record's own rule that every in-tree citation of a
DANGLING anchor must acknowledge it at the citation site. If the citing docstring cannot honestly
be made to say so within this task's scope, mark Phase 2 `[PARTIAL]` and report the blocker rather
than recording a structurally dangling anchor as live.
