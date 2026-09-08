# Implementation Summary: Task #548

- **Task**: 548 - Re-pin the paper anchors changed by the paper's z/d/r refactor and its removal of the Past/Future fragment
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T18:20Z
- **Completed**: 2026-09-08T03:05Z
- **Effort**: ~5.5 hours
- **Dependencies**: None
- **Artifacts**: plans/01_repin-bx-z-d-r-anchors.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The JPL paper renamed `def:TMplus-f/-d/-c` to `def:BX-z/-d/-r`, collapsed the `BL^+` fragment
cluster into `BL`, dropped the `+` superscript from the TM family, and edited fifteen other pinned
anchors. `specs/paper-definitions-of-record.md` absorbed the whole wave — nine anchors retired,
three newly pinned, sixteen entries re-hashed, sentinels re-pinned twice — and every in-tree
citation and every prose claim the wave invalidated was corrected. `check-paper-definitions.sh`
went from exit 1 (15 drifted, 9 dangling) to the quiet case-(a) pass.

## What Changed

- `specs/paper-definitions-of-record.md` — 9 manifest rows retired with their prose entries kept
  and marked `DANGLING` (`def:directed`, `def:BLplus-semantics`, `def:BLplus-defined`,
  `thm:BLplus-PastFuture`, `thm:BLplus-NextPrevious`, `TMP-CO`, `def:TMplus-f/-d/-c`); 9 matching
  `KNOWN-ANCHORS` `DANGLING` rows plus a `prop:archimedean` `LIVE-UNPINNED` row added; 3 new
  prose entries and manifest rows for `def:BX-z` / `def:BX-d` / `def:BX-r`; 16 entries re-quoted
  and re-hashed; `FILE_CHECKSUM` / `PINNED_COMMIT` / `LINE_COUNT` re-pinned (twice); a dated
  wave-narrative section, a refreshed `def:derivability` / `def:soundness` exclusion bullet, and
  an extended dirty-pin caveat.
- 18 files re-labelled `def:TMplus-f/-d/-c` -> `def:BX-z/-d/-r` (32 lines), including
  `FormalSystem/Semantics/FrameProperty.lean`, `FrameClassValidity.lean`,
  `Metalogic/Conservativity.lean`, `Semantics.lean`, `docs/theorem-index.md`, `README.md`.
- `FormalSystem/Metalogic/Conservativity.lean` — the sentence deferring the rename ("the record's
  re-pin is separate work") rewritten; it now names the new anchors as pinned and the old as
  `DANGLING`.
- Hoelder attribution corrected at 7 sites: the Z-time narrowing is now attributed to `def:BX-z`
  citing `prop:archimedean`, with Hoelder named as the paper's earlier route and as the source of
  `IsZTime`'s name.
- Dangling-citation honesty pass: `def:directed` retargeted to `def:frame`'s opening clause
  across `TaskFrame.lean`, `FrameAxioms.lean`, `Extension/Constraint.lean`,
  `Algebraic/FlowFrame.lean` and `typst/chapters/02-semantics.typ`; `def:BLplus-semantics` ->
  `def:BL-semantics` and `def:BLplus-defined` -> `def:BLplus-language` across `Truth.lean`,
  `Formula.lean`, `Axioms.lean` and two typst chapters; `TMP-CO` -> the live `CO` in
  `DedekindDerived.lean`, `Formula.lean` and `Conservativity.lean`.
- Three claims true of the old text and now false, corrected rather than re-labelled: the paper no
  longer splits directedness into two halves; the ball-space footnote says *at least as strong as*
  rather than *strictly stronger* (`TaskFrame.lean`, `README.md`); `def:BX-r` derives `CO` rather
  than restating it.
- `typst/FormalFoundations.typ` — the one verbatim quotation of the old `def:TMplus-f` closing
  sentence refreshed, plus a naming-provenance `#remark`.
- `typst/sync-check-whitelist.txt` — two stale whitelist entries retired.
- `docs/theorem-index.md` — naming rows refreshed (TM/BL without superscripts; the `BL` name
  collision recorded).
- 6 `Metalogic/` files — 14 `Syntax/Formula.lean:NNN` citations bumped by +1 to repair the C20
  offset this task's own docstring edit introduced.
- 4 generated inventory blocks regenerated for this task's line-count deltas.

## Decisions

- **The acceptance gate is `check-paper-definitions.sh`, not C15** (the plan's reframing, carried
  through): C15 was already green and cannot detect a stale hash.
- **Absorbed the whole wave as one unit** — nine dangling anchors, not just the three renamed
  ones. The record's own step 4 cannot succeed while any stay pinned.
- **`cor:saturation-finite`'s `Cthm` -> `Lthm` change** is hash-visible with the statement
  word-identical; the manifest `kind` stays `env` because the resolver reads the environment name
  off the `\label{}` line.
- **`prop:archimedean` recorded `LIVE-UNPINNED`, not pinned** — it is a pen-and-paper result this
  repository does not check.
- **Mentions of the retired labels were kept where the tree records the rename**, matching the
  record's existing `thm:occurrence` / `lem:fibers` convention (and making the new `KNOWN-ANCHORS`
  notes accurate); the plan's "grep returns nothing" phrasing is superseded by this.
- **Inventory numbers restricted to this task's own +38-line delta** rather than absorbing
  concurrent task 550's 18 uncommitted modules into a committed README.

## Plan Deviations

- **Phase 4** altered: live census measured 32 lines across **18** files, not 17 — the extra is
  `typst/sync-check-whitelist.txt`, whose two now-unused entries were retired rather than re-keyed.
- **Phase 5** altered: the verbatim old-text quotation is in `typst/FormalFoundations.typ`, not
  `FrameClassValidity.lean` (both Lean sites were paraphrases, as the research measured). The
  quotation was refreshed; the document-wide rename of that 1561-line report (~57 sites) is a
  follow-up, not done here.
- **Phase 5** altered: the plan's risk that a `prop:archimedean` citation without a KNOWN-ANCHORS
  row would turn C15 red is false — C15's regex covers `(def|thm|lem|cor|app|rmk):`, not `prop:`.
  The row was added as a record decision regardless.
- **Phase 5** scope addition: dangling-anchor citation honesty (~25 sites) and the "strictly
  stronger" ball-space correction, both required by the record's own conventions and both
  discovered in Phase 2.
- **Phase 6** altered: the paper moved four times mid-implementation; the fourth move genuinely
  drifted `def:BX-z` (comment-only deletion inside the environment) and was absorbed with a second
  sentinel re-pin.
- **Phase 6** altered: the first invariants run surfaced a C20 regression this task caused (14
  citations pushed onto blank lines by a one-line docstring addition); fixed, and the second run
  reports C20 PASS.

## Verification

- Build: Success — `lake build` completed successfully (2610 jobs), 0 errors, run detached through
  `lake-build-guard.sh`.
- `scripts/check-paper-definitions.sh`: exit 0, no output (quiet case-(a) pass).
- `scripts/check-module-invariants.sh`: both C15 lines PASS (56 paper-anchor citations resolve; 52
  theorem-index rows carry their anchor); C20 tier 1 PASS (1022 citations); C20 tier 2 PASS.
- Standalone C15 reproduction: no unresolved anchor (known=75, cited=63).
- `scripts/typst-sync-check.sh`: unchanged at the same 4 pre-existing, unrelated violations.
- `typst compile FormalFoundations.typ`: succeeds.
- Sorry count: 0 in live scope (only pre-existing `Boneyard/` hits, which are archived and out of
  scope).
- Vacuous count: 0. Axiom count: unchanged — this task wrote no Lean declarations at all.
- The three unrelated `LIVE-UNPINNED` anchors (`app:drift`, `cor:no-characterization`,
  `lem:deterministic-singleton`) are untouched by this task's diff (0 diff lines mention them).
- Files verified: Yes.

## Impacts

- The record once again describes the live paper, so any task quoting it is quoting the current
  text rather than the pre-refactor text.
- Nine anchors the paper no longer defines are now recorded as retired with their last-resolved
  text kept, so a future reader can tell "moved" from "never existed".
- The tree's Z-time narrowing story now matches the paper's: `prop:archimedean` plus the
  Extensions-section Hoelder step, rather than an inline Hoelder derivation the paper cut.

## Follow-ups

- `typst/FormalFoundations.typ` still presents the paper's pre-2026-09 naming (`BX_f`/`BX_c`,
  `TM^+`, `BL^+`) at ~57 sites. A `#remark` records this; the re-transcription is separate work.
- `scripts/check-module-invariants.sh` still reports `INV` (2 files) and `C16` failures. Both are
  caused by concurrent task 550's uncommitted modules under
  `Metalogic/Decidability/Verified/Termination/MintBound/`, not by this task; task 550's own
  inventory regeneration will absorb them.
- The pinned paper is under active edit. Expect the pin to be behind again; the case-(b)/(c)
  distinction in `check-paper-definitions.sh` is what tells a future reader whether that matters.
- `latex/subfiles/02-Semantics.tex` still restates `def:directed` as a live anchor. It is outside
  C15's swept scope and outside this plan's file list.

## References

- specs/548_repin_renamed_paper_anchors_bx_z_d_r/plans/01_repin-bx-z-d-r-anchors.md
- specs/548_repin_renamed_paper_anchors_bx_z_d_r/reports/01_repin-bx-z-d-r-anchors.md
- specs/paper-definitions-of-record.md
