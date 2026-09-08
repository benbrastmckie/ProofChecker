# Implementation Summary: Task #551

- **Task**: 551 - Boneyard disposition for publication
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T04:32:35Z
- **Completed**: 2026-09-08T06:40:00Z
- **Effort**: ~2h wall clock (plan estimate 11h)
- **Dependencies**: None
- **Artifacts**: plans/01_boneyard-keep-and-document.md, reports/01_boneyard-disposition-recommendation.md, notes/phase-1-baseline.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The disposition question is answered and recorded: **KEEP** `FormalSystem/Boneyard/` — 168
archived `.lean` files, 91,618 lines — and repair the documentation that describes it. Cutting was
unavailable (96 files outside the archive cite it, including the published LaTeX at
`latex/subfiles/04-Metalogic.tex:383,389` and 45 live `.lean` docstrings); splitting would have
bought ~2% of the archive's lines at the cost of ADR-005's single-archive invariant, and would
have preferentially deleted *refuted* routes, the category with the most scholarly value. All ten
plan phases closed. No archived file was deleted, and the two headline properties — zero `.olean`
under any `Boneyard` path, zero structural `sorry` in the live tree — were re-verified by census
rather than assumed.

The task's own reason for existing was that the tree shipped undecided and unexplained. Both
halves are now fixed: the decision is an ADR, and the archive's own README leads with the two
machine-checked facts that neutralize its size.

## What Changed

- `docs/architecture/ADR-009-Boneyard-Retention.md` — **new.** The KEEP decision record: why CUT
  is unavailable, why SPLIT is not worth its cost, and the four obligations keeping the archive
  carries.
- `docs/architecture/README.md` — ADR-009 added to the catalog and the details section.
- `scripts/check-module-invariants.sh` — the archive-aware inventory generator. `markdown_targets()`
  no longer prunes `Boneyard` (the mechanical root cause of the drift: the archive README was the
  one README in the tree whose counts were hand-typed and ungated). `scan()` gained
  `is_archive_base()` plus archive-shaped `rows=totals`, and an `empty=skip|include` option so
  README-only tombstone subtrees get rows instead of being silently dropped. Both new options are
  documented in the `--emit-inventory` header block. **The change was a byte-for-byte no-op on
  existing output at the moment it landed** — capability added, nothing moved.
- `FormalSystem/Boneyard/README.md` — the bulk of the work:
  - a publication-facing opening section stating what the tree is, that no `.olean` is produced
    under any `Boneyard` path, that the live tree's structural sorry count is zero while the
    archive carries every `sorry` **by design**, that both are asserted by C1/C3/B0/C11 rather
    than by prose, and why retired-attempt provenance is worth shipping;
  - §One Archive's counts table is now a **generated** block (`rows=totals`), gated by `INV`;
  - §Directory Inventory rebuilt as a **generated 40-row block** (`rows=both cols=files-lines
    link=yes empty=include sort=lines-desc`) — four rows naming entries that ADR-005 had moved
    under `Kamp/` are gone, five missing subtrees including `Kamp/` itself (47.6% of the archive)
    are present, the disagreeing total row is gone;
  - §Archival Reason Taxonomy rebuilt with a fifth category and an exhaustive 40-row table
    carrying **two orthogonal classifications** per entry — archival reason, and provenance class
    (Superseded / Refuted / Orphaned-Unfinished);
  - §Subdirectory Details rebuilt alphabetically with 15 new entries — 39/39 coverage;
  - §Task Cross-References retired and replaced by **Provenance: When Each Subtree Was Archived**,
    37 rows keyed on date + commit SHA;
  - the `#exit` policy made explicit and mandatory, and the archive's one root-level file
    (`VacuousKEquiv.lean`) admitted by policy rather than tolerated.
- `FormalSystem/Boneyard/Kamp/README.md` — generated per-subtree inventory for the archive's
  largest component.
- Six **new** subtree READMEs, each with a generated file inventory:
  `BXCanonicalQuasimodel/`, `DeadConvergenceProof/`, `FMPVariants/`, `RestrictedMCSDeferral/`,
  `SoundnessVariants/`, `StaviDiscretePath/`. Every subtree now has one.
- Twelve archived `.lean` files gained `#exit`; eleven of those also gained the
  `ARCHIVED (Boneyard)` banner they had never carried. All 168 archived files are now guarded.
- `FormalSystem/README.md` — the duplicate hand-typed "156 archived `.lean` files" retired for a
  description carrying no number, restoring ADR-005 decision 4.
- `FormalSystem/FormalSystem.lean` — module docstring corrected: the "two-Boneyard counting
  caveat", "Both Boneyard trees" and "either tree" language is gone (it contradicted ADR-005),
  and the stale "(210 live files)" for `Metalogic` — measured live count 348 — was removed rather
  than re-typed, since no gate owns that number.
- `README.md` — the archive's line in the directory tree reframed; generated rollups regenerated.

## Decisions

- **Phase 2 Scope Hypothesis confirmed, research report corrected.** The report expected a
  Boneyard-aware variant of `live_subdirs`/`live_files` in `scripts/lib/live_walk.py`. Measured:
  the exclusion is by the literal directory *name*, no subdirectory of the archive carries that
  name, so `live_subdirs("FormalSystem/Boneyard")` returns all 39 subtrees and `live_files`
  returns all 168 files unmodified. **`live_walk.py` was not changed.**
- **Generation over hand-maintained registration** for the Directory Inventory. Registration
  would have kept the richer six-column table, but generation gates the counts, which is the
  whole point — D1/D2 were a drift problem, not a formatting one. The six columns collapse to
  four; the `Task` column's removal is also Phase 6's D4 repair.
- **`#exit` made mandatory rather than declared optional.** The README's two sections disagreed,
  and under the permissive reading eleven archived files carried no archival marker of any kind —
  a reader opening one saw a copyright header, imports and an ordinary docstring. `#exit` is
  redundant against the build and that is not the point: it makes inertness a *local*, greppable
  property instead of a global reachability argument.
- **`VacuousKEquiv.lean` stays at the archive root.** Moving it would have edited a live file
  (`Metalogic/WeakCanonical/OrderedSum.lean`) to no benefit; the policy was amended to admit a
  documented root-level file, and the generated inventory gives it a row automatically. Its
  citation was also de-numbered (`OrderedSum.lean:54` → a searchable identifier) so it cannot rot.
- **C9's `/Boneyard/` exclusion stays, with the measurement recorded.** 90 C9-shaped occurrences
  across 34 archived files at the start; the two in the top-level README are cleared, leaving 88
  across 33. Narrowing the filter would turn a green gate red over occurrences that sit next to
  the code they describe. `scripts/check-module-invariants.sh`'s C9 filter was **not** modified;
  the README records the reason and the reproducing command.
- **A fifth taxonomy category was genuinely needed.** 11 of 40 entries are correct code, often
  still compiling at archival, retired only because nothing imported it. Calling those "dead
  ends" misdescribes them and "superseded" implies a replacement that does not exist, so
  **Orphaned, Not Refuted** was added.
- **Provenance recovered through the pre-rename path.** `git log --follow` on a current path
  stops at `5359fef7d` (`Theories/Bimodal` → `FormalSystem`); querying
  `Theories/Bimodal/Boneyard/<name>` alongside recovers every per-event commit. The technique is
  recorded in the README so it does not have to be rediscovered.

## Plan Deviations

- **Phase 2**, final `--emit-inventory --check` step **altered**: it passed byte-for-byte when the
  edit landed, but a later re-run reported one changed file — `README.md`'s `Live lines` rollup
  moving 282,014 → 282,051, entirely the concurrent live-tree work described below. The diff was
  inspected line-by-line and the file restored untouched.
- **Phase 3** offered two options for `#exit` and two for the loose file; option (a) and the
  amend-the-policy option were taken, both recorded inline on the plan's checklist.
- **Phase 6** left `scripts/check-module-invariants.sh` unmodified: the measurement did not
  support narrowing the C9 filter, which is the outcome the plan's own contingency anticipated.
- **Phase 8** did not edit `FormalSystem/README.md`'s Boneyard row; Phase 9 had already rewritten
  it, exactly as the plan's coordination note directed. Phase 8 edited the top-level `README.md`
  tree comment instead.
- Phases were executed **1, 2, 3, 4, 9, 5, 6, 7, 8, 10** — Phase 9 taken ahead of Phase 5 under
  the phase-closure contract's cheapest-closure-first rule (both are unblocked by Phase 4, and
  Phase 8 requires Phase 9 to land first regardless).

## Verification

- **Build**: `lake build` **green** — 2610 jobs, exit 0, run detached through
  `.claude/scripts/lake-build-guard.sh`.
- **Full gate**: `bash scripts/check-module-invariants.sh` → **ALL CHECKS PASSED**, including
  B0, C1, C2, C3, C5, C7, C9, C11, C12, C13, C14, C15, C16, C20, C21, C22, C23 and INV.
- **Sorry count (live tree)**: **0** — C3, asserted by content across `FormalSystem/` with the
  archive excluded. Unchanged from baseline.
- **Vacuous count**: **0** — no `def X := True` / `:= trivial` shaped placeholder was written;
  this task proved no Lean declarations at all.
- **Axiom count**: unchanged. C2's four flagship axiom sets match baseline; C14's pinned
  declarations match; C21 confirms all 27 `MainResults.lean` declarations remain pinned.
- **`.olean` census**: **0** under any `Boneyard` path (baseline 0). Total under `.lake/build`
  547 against a baseline of 546; the +1 is a live module added by concurrent work — this task
  added no live module and touched no live `.lean` file except `FormalSystem.lean`'s docstring.
- **B0**: exactly 1 archive directory; the exclusion removes 168 of 646 files. Identical to
  baseline.
- **C11**: all 536 archived import lines in all 168 archived files resolve (7 waived). Identical
  to baseline — the `#exit` insertions did not disturb any import block.
- **INV**: every generated inventory block current, every hand-maintained one exhaustive. Proven
  to be a real gate and not merely correct: perturbing one digit of the archive's generated file
  count made INV fail, and reverting restored it.
- **Archive intact**: **zero** archived `.lean` files deleted across the whole task's diff. 168
  files before and after; 39 subtrees before and after; 91,539 → 91,618 lines, the +79 being
  exactly the 12 `#exit`/banner insertions.
- **Independent re-derivation**: all four generated archive counts (168 / 91,618 / 39 / 1) were
  re-derived with `find`/`wc` and agreed with the generator.
- **Exhaustiveness, checked in both directions**: every one of the 40 top-level entries has
  exactly one inventory row and one taxonomy row, and every row names something that exists; all
  39 subtrees appear under both §Archival Reason Taxonomy and §Subdirectory Details.
- **Adjacent lints**: `readme-lint.sh` PASS, `typst-status-counts.sh` PASS,
  `check-copyright-headers.sh` PASS. `typst-sync-check.sh` FAILs on 4 pre-existing violations in
  `typst/chapters/p4-proof-automation.typ` (`AesopRules.lean`, `Automation/Tactics/Helpers.lean`,
  `Tactics/Helpers.lean`, `tm_auto 5`) — caused by the `RetiredTactics/` archival in commit
  `1ff119610`, which is a different task. The same citations were present before this task's
  first commit, and this task never touched `typst/`. Not repaired here, and not concealed.
- **Files verified**: Yes.

### Concurrency caveat, stated rather than glossed

A separate session executed the `WorldHistory` → `ConvexHistory` rename in the same working tree
throughout. Consequences worth recording:

- The Phase 1 baseline gate had **one pre-existing failure** (C12, on the renamed file's path),
  and transient C5/C11/C20/INV findings appeared and cleared as their work progressed. Every such
  finding named `WorldHistory` or `ReynoldsBridge`; the working rule was that a check is green for
  this task when its only remaining findings do. By Phase 6 they had cleared their own residuals
  and the gate went fully green.
- An unguarded `lake build` launched by this task's gate run collided with their guarded build
  (one `lean` process at 4.7 GB RSS on a machine already under memory pressure). It was killed
  immediately, and every subsequent build in this task went through
  `.claude/scripts/lake-build-guard.sh` detached.
- Every commit here went through `git-commit-scoped.sh` with an explicit pathspec. The sweep was
  not symmetric: this task's Phase 9 edits to `FormalSystem/FormalSystem.lean` and
  `FormalSystem/README.md` were committed by *their* session in `b9fd6f15c` before this task's
  own Phase 9 commit ran. The content is correct and present; only the attribution is off.

## Impacts

- The archive is no longer shipped undecided. A reviewer asking "why is a quarter of this
  repository dead code?" has a one-click answer in ADR-009 and a framing paragraph that leads
  with checks rather than assurances.
- The class of defect that produced D1/D2 is closed at the mechanism. Every count published about
  the archive is now either generated and `INV`-gated, or a named check ID. There is no hand-typed
  archive figure left outside `specs/`.
- The generator is archive-aware for everyone, not just this README: any future archive markdown
  can register a generated inventory, and README-only subtrees no longer vanish from generated
  tables.
- Provenance is followable from outside this working copy: 37 archival events keyed to commits
  that `git show` resolves, plus the recorded technique for recovering more across the tree-wide
  rename.
- The archive's inertness is now checkable file-locally (`#exit` in all 168) as well as globally
  (reachability, B0, C11).

## Follow-ups

- `typst-sync-check.sh`'s 4 violations in `typst/chapters/p4-proof-automation.typ` are stale
  citations left by the `RetiredTactics/` archival and belong to that work, not this one. They
  need either re-pointing at `Boneyard/RetiredTactics/` or a whitelist entry.
- C9D reports 142 task-number citations under `docs/` (100 of them in
  `docs/development/PHASED_IMPLEMENTATION.md`), still soft. Out of scope here — this task's
  changes to `docs/` add none.
- The 88 task-number citations remaining across 33 archived files are recorded with their
  measurement and the exact command to re-run. If they are ever cleared, drop `grep -v
  '/Boneyard/'` from C9 and the rule becomes gate-enforced across all of `FormalSystem/`.
- `scripts/module-invariants-manifest.txt` and the archive are independent mechanisms for
  not-live code; nothing here changed that boundary, but the Archival Criterion section is the
  place a future reader will look for it.

## References

- `specs/551_boneyard_disposition_for_publication/plans/01_boneyard-keep-and-document.md`
- `specs/551_boneyard_disposition_for_publication/reports/01_boneyard-disposition-recommendation.md`
- `specs/551_boneyard_disposition_for_publication/notes/phase-1-baseline.md` — the frozen
  before-state Phase 10 re-verified against
- `specs/551_boneyard_disposition_for_publication/handoffs/phase-9-handoff-20260908T044815Z.md`
- `docs/architecture/ADR-009-Boneyard-Retention.md`
- `docs/architecture/ADR-005-Single-Boneyard.md`
- `FormalSystem/Boneyard/README.md`
