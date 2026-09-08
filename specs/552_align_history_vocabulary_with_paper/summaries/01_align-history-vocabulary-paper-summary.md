# Implementation Summary: Task #552

- **Task**: 552 - Align history vocabulary with paper (`WorldHistory` -> `ConvexHistory`)
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T21:10:00Z
- **Completed**: 2026-09-07T22:05:00Z
- **Effort**: ~2 hours of agent work; wall-clock dominated by two ~2600-module builds
- **Dependencies**: None (the paper-anchor re-pin dependency was discharged before this task ran)
- **Artifacts**: plans/01_align-history-vocabulary-paper.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This repository's `WorldHistory` denoted the paper's *convex history* — one tier below what its
name suggested — making `∀ σ : WorldHistory F, …` without an `IsTotal` guard a quantifier over
strictly more than `H_F`. The whole live tree has been shifted back into alignment with the
paper's three tiers (*partial history* -> *convex history* -> *possible world*) by alpha-renaming
plus re-quotation, with **no change to any proof term**. `TaskFrame.HF` is now the documented sole
Lean name for the paper's possible worlds, and the string "world history" no longer appears
anywhere in the live tree outside `Boneyard/`, `specs/`, and generated `latex/**/build/` artifacts.

## What Changed

- `FormalSystem/Semantics/WorldHistory.lean` -> `FormalSystem/Semantics/ConvexHistory.lean`
  (`git mv`), with the structure, namespace, and all four derived identifiers renamed:
  `toWorldHistory` -> `toConvexHistory`, `worldHistory_ext` -> `convexHistory_ext`,
  `isTotal_toWorldHistory` -> `isTotal_toConvexHistory`,
  `toWorldHistory_toPartialHistory` -> `toConvexHistory_toPartialHistory`.
- 620 identifier occurrences rewritten across **71 live `.lean` files** plus 4 `FormalSystem`
  READMEs, driven from an explicit `git ls-files` list with `/Boneyard/` filtered out — never a
  repo-root `grep -rl`. The 7 `import FormalSystem.Semantics.ConvexHistory` lines and
  `FormalSystem/Semantics.lean`'s markdown link resolved with the rename.
- `PartialHistory`, `toPartialHistory`, `IsTotal`, `ofTotal`, `timeShift` and `TaskFrame.HF` all
  keep their names, as instructed. No `abbrev PossibleWorld` was introduced.
- `FormalSystem/Semantics/PartialHistory.lean` and `ConvexHistory.lean` module docstrings
  **re-quoted** from the current `def:world-history` text (`possible_worlds.tex:2880-2886`,
  sha256 `550661d3…`), not adjusted in place. `PartialHistory.lean`'s block-quote of the paper's
  deleted inline `%` converse-convention gloss was removed, and the justification it supported
  re-grounded on `def:task-relation`, where the convention actually lives.
- `TaskFrame.HF`'s docstring now says an element of `F.HF` **is** a possible world and that
  `ConvexHistory.IsTotal` is the predicate form of the same notion.
- `ConvexHistory.lean`'s module docstring records, once, the paper's own residual body/appendix
  split and cites `possible_worlds.tex:1049`'s collapse sentence ("Since the classes in `W_F` will
  play no further role below, I will also refer to `H_F` as the set of *possible worlds*") as the
  licence both for `H_F` = possible worlds and for this repository carrying no `W_F` quotient.
  No reconciliation footnote was reintroduced.
- `FormalSystem/Semantics.lean:185`'s single false-friend table row split into two, one per tier;
  `docs/theorem-index.md:34`'s glossary row split into three (partial / convex / possible world).
- Four substantive (non-terminological) documentation errors corrected:
  `Semantics/README.md`'s "Partial world-histories **on convex subsets**" (partial histories are
  precisely the tier *without* a convexity requirement) and "`WorldHistory`: **Infinite sequence**
  of worlds" (a convex history may be bounded — the paper's finite game of chess);
  `Semantics/Extension/README.md`'s "partial **world** histories"; and
  `docs/development/DIRECTORY_README_STANDARD.md`'s stale three-parameter signature
  `h : WorldHistory W S T`.
- Prose swept onto the paper's vocabulary across `FormalSystem/` (94 lines), `docs/` (~60),
  `typst/` (~30), `latex/` (~14), `Tests/` (2), `README.md` and `ORGANISATION.md`. The
  `total world histor*` -> "possible world(s)" collapse was run as its own first pass in each
  root, before any bare-phrase substitution, so the 34 total-tier sites were never mistranslated
  as convex.
- `typst/chapters/02-semantics.typ`'s section label `<sec:world-histories>` renamed to
  `<sec:convex-histories>` with all 8 `@`-references updated.
- `latex/subfiles/04-Metalogic.tex:54`'s stale line citation re-derived: `timeShift` is at
  `ConvexHistory.lean:304`, not the cited `:246`.
- `specs/paper-definitions-of-record.md`: six stale-prose sites corrected (the `def:world-history`,
  `thm:extension` and `cor:occurrence` headings, the layering sentence, the `H_F` sentence, and the
  box-clause commentary), plus a "Vocabulary alignment (2026-09-07): prose only, no re-pin"
  addendum. **No `sha256:` line, no verbatim block, no manifest row, and neither the
  `PINNED_COMMIT` nor the `FILE_CHECKSUM` sentinel was touched.**

## Decisions

- **No `abbrev PossibleWorld F := F.HF`.** It would break dot-notation on the subtype and
  reintroduce the very ambiguity the rename removes. `HF` is the name; `IsTotal` is its predicate
  form. This is stated explicitly in the `HF` docstring so it is not re-litigated.
- **Proof-term safety was proven, not asserted.** A script strips Lean comments and docstrings
  from every changed `.lean` file at `HEAD` and in the working tree, applies the rename to the
  `HEAD` side, and diffs. All 90 changed files matched exactly. The only non-comment differences
  anywhere were `#exit` insertions under `Boneyard/` belonging to a concurrently running task-551
  agent, which that agent has since committed.
- **The generic tier keeps the generic word.** Notation-file section comments
  (`typst/notation/bimodal-notation.typ:70`, `latex/assets/bimodal-notation.sty:72`) group
  `\history`/`\histories`, which span all three tiers, so they became "Histories" rather than being
  pushed onto either specific tier — matching the paper's own use of *history* as the generic term.
- **`docs/architecture/BFMCS_ARCHITECTURE.md`'s metaphorical use was mapped to the total tier.** An
  FMCS carries one MCS per time point, i.e. it is total across time, so its scare-quoted
  "world history" became "possible world" rather than "convex history".

## Plan Deviations

- **Phase 1, "How to extend this record" item** altered: steps 1-3 of that procedure are
  anchor-addition steps and were vacuous, since no anchor was added or re-pinned. Only step 4
  (re-run the checker) applied. An addendum subsection was written instead.
- **Phase 1, archival-site verification** altered: the plan named lines 195, 228, 231, 339, 521 as
  archival sites to protect. Measured at implementation time, only 228 carries the phrase at all;
  195/231/339/521 do not and needed no protection.
- **Phase 2's build** altered and merged into Phase 5's: the first attempt was SIGTERM-killed
  (Lean exit 143) under host memory pressure at module 1008 of 1008, on
  `Metalogic/Decidability/Verified/Termination/MintBound/MintPotential.lean` — a module this task
  never touches, containing zero `ConvexHistory` occurrences. Every rename-affected module compiled
  in that attempt; the run logged exactly one error, the unrelated kill. Rather than pay a second
  ~250-module cycle for the same evidence, Phase 2's build was folded into Phase 5's single
  `--memory-bound` rebuild.
- **Phases 2 and 3 landed in one commit** (altered): Phase 3 edits docstrings inside the same ~30
  files Phase 2 renames identifiers in, and Phase 2's close slipped past Phase 3's start when its
  build was killed; the two edit sets are not separable by pathspec after that. Phase 2's
  atomic-batch guarantee is preserved in substance — the pure-rename property was verified *before*
  any Phase 3 edit.
- **Phase 3 addition**: `specs/paper-definitions-of-record.md`'s "Untracked sources" block, which
  Phase 1 was told to leave unchanged as a hashed verbatim quotation, was found to quote the
  **superseded** text of the finite-case footnote. The live paper (`possible_worlds.tex:1772`) now
  reads "bounded convex history" where the block read "bounded world history", and gained a comma
  after "In this case". The block is in fact **untracked** — no `sha256:` line, no manifest row,
  not read by `check-paper-definitions.sh` — so re-quoting it moves no pin. It was re-quoted
  together with `Metalogic/Decidability/BiLasso/Agreement.lean`, which block-quotes the same
  footnote, and both now match the live paper character-for-character.
- **Phase 5 addition — two gate regressions repaired.** The plan's Phase 5 checked only C19 against
  `check-module-invariants.sh`; the run surfaced two other checks that had regressed from the
  baseline's `ALL CHECKS PASSED`, both caused by this task:
  - **C11** (dangling archived import): `Boneyard/ChainCompleteness/Bundle/SuccChainWorldHistory.lean:3`
    imported the renamed module. The plan's Non-Goals forbid edits under `Boneyard/` — a rule aimed
    at the *identifier sweep*, not at a one-word import repair the gate itself asks for ("repair the
    import, or add … to `scripts/boneyard-import-waivers.txt` with a reason"). The import was
    repaired rather than waived, because a waiver would record the module as permanently missing
    when it exists under a new name. The archived file's body and its own filename were left alone.
  - **C20** (stale `file.lean:NNN` citation): `CompletenessDedekind.lean:202` and `:218` cited
    `ReynoldsBridge.lean:739` and `:663`. Both were *already* pointing at the wrong content before
    this task (measured at the merge-base: line 739 read "The multi-family approach resolves the box
    semantics mismatch:" and 663 read a `⊇`-definitional sentence, neither of them the cited
    declaration); the two-line docstring expansion here shifted them onto blank lines, which is what
    C20 detects. Repaired the way C20 asks — by dropping the volatile `:NNN` and citing the
    declaration by name — rather than by re-deriving line numbers that will shift again.
- **Phase 4's file list** was wider than the plan's Scope Hypothesis: `docs/ARCHITECTURE.md`,
  `docs/user-guide/INTEGRATION.md`, `docs/development/MODULE_ORGANIZATION.md`,
  `docs/development/PHASED_IMPLEMENTATION.md`, `docs/project-info/test-coverage.md`,
  `docs/project-info/implementation-status.md`, `README.md` and `ORGANISATION.md` also carried the
  identifier and had to be swept for Phase 5's absence-grep to be clean.

## Verification

- Build: **Success** — `lake build FormalSystem` reports `Build completed successfully (2610 jobs)`,
  run detached through `lake-build-guard.sh`. (The preceding run failed only on
  `WeakCanonical/IntegerModel/ShiftAndGlue` with `error: no such file or directory` on its own
  `.olean` output path — an output-path race with the concurrent unguarded build that
  `check-module-invariants.sh` spawns. `ShiftAndGlue.lean` contains zero `ConvexHistory`
  occurrences and was last touched by an unrelated task; once the competing build was stopped it
  built clean.)
- Sorry count: 331 (live tree, excluding `Boneyard/`) — **unchanged from the pre-task baseline**.
  The plan's figure of 348 was stale; 331 was re-measured against the merge-base before any edit.
- Vacuous count: 0 introduced. The single tree-wide grep hit,
  `Examples/TemporalStructures.lean:496` (`int_domain_universal … := trivial`), is byte-identical at
  the merge-base and is not vacuous in substance: `intTimeHistory.domain t` *is* `True` by
  definition (universal domain), so `trivial` is the honest proof.
- Axiom count: **0 before, 0 after**. Enumerated both sides: every `^axiom ` grep hit in the live
  tree is a docstring prose line that begins with the word "axiom" after wrapping, not a
  declaration, and the two lists are identical.
- `scripts/check-module-invariants.sh`: **`ALL CHECKS PASSED`**, exit 0. C19 refined docstring
  coverage **92.33%** (9617/10416, floor 90%) — bit-for-bit the pre-task baseline, so the bulk
  docstring rewriting eroded none of the 2.33 points of headroom (every change was a replacement,
  never a deletion). C3 confirms the structural sorry inventory is zero across `FormalSystem/`.
  The 331 `sorry` tokens the raw grep counts are all inside comments and deprecation markers.
- `scripts/typst-sync-check.sh`: `TOTAL_VIOLATIONS=4` (baseline 4), `MISMATCH_COUNT=0`,
  `MA_COUNT_MISMATCHES=0`.
- `scripts/readme-lint.sh`: `RESULT: PASS`, broken file references **0**, stale dates **9**
  (baseline 11 — the two READMEs edited here were re-stamped, plus the Bridge README).
- `scripts/check-paper-definitions.sh`: exit 1, drifted set exactly
  `{def:S5, def:BX, def:BX-z, def:BX-d, def:BX-r, def:TMplus}`, 0 unresolved — byte-identical to
  the pre-task baseline. `def:world-history`, `thm:extension` and `cor:occurrence` do **not**
  appear in it. Exit 1 is the baseline here, not a failure; the six drifted anchors belong to the
  separate re-pin work.
- Identifier-absence grep: `WorldHistory`/`worldHistory` appear nowhere outside `Boneyard/`,
  `specs/`, `.claude/`, `.lake/` and `latex/**/build/`.
- Prose-absence grep: "world histor*" / "world-histor*" appear nowhere outside the same exclusions,
  other than the `def:world-history` anchor id itself, which is deliberately stable.
- No proof term changed: verified mechanically over all 90 changed `.lean` files (see Decisions).
- Files verified: Yes

## Impacts

- `ConvexHistory F` now says what it means, so a reader can no longer mistake a bounded convex
  history for a possible world; a `∀ σ : ConvexHistory F` with no `IsTotal` guard is now visibly
  wider than `H_F` rather than invisibly so.
- The paper and this repository now share one vocabulary with no reconciliation note on either
  side. Nothing in the paper needs to change for this task to land.
- The separate question of whether the convex layer should exist at all is now answerable on its
  own merits: costing a collapse against a tree whose names still misled would have produced a plan
  that read as its own opposite.

## Follow-ups

- `specs/ROADMAP.md:223` and `:742` name `WorldHistory` in **live steering prose** and are now
  stale identifiers. They were deliberately not edited — the dispatch's scope boundary excludes
  `specs/` — and want a one-line follow-up.
- The paper's own body prose (`possible_worlds.tex:1014-1052`) still uses the older two-word phrase
  for the total tier before collapsing it at line 1049, while the settled appendix definition uses
  *possible world*. That is the paper's residual drift, not this repository's, and is recorded once
  in `ConvexHistory.lean`'s module docstring so a future reader does not "correct" the tree back
  toward it.
- `Metalogic/Decidability/Verified/Termination/MintBound/MintPotential.lean` needs ~5 GB RSS and
  several minutes of CPU to elaborate; it is the module that OOM-killed the first build. Note that
  `scripts/check-module-invariants.sh` runs its **own unguarded** `lake build`, which will contend
  with a guarded build on exactly this module — worth routing through the build guard.

## References

- `specs/552_align_history_vocabulary_with_paper/plans/01_align-history-vocabulary-paper.md`
- `specs/552_align_history_vocabulary_with_paper/reports/01_align-history-vocabulary-paper.md`
- `specs/paper-definitions-of-record.md` — `def:world-history`, `thm:extension`, `cor:occurrence`
- `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex:2880-2886` (the pinned
  definition), `:1014-1052` (the body layering), `:1772` (the finite-case footnote)
- Commits: `ed20a9814`, `b9fd6f15c`, `995567d05`, `c580a0bf7`
