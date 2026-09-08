# Implementation Plan: Task #552

- **Task**: 552 - Align history vocabulary with paper (`WorldHistory` -> `ConvexHistory`)
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: None (the paper-anchor re-pin dependency is discharged for this task's three
  anchors — see Research Integration; the sibling task's six drifted anchors are disjoint)
- **Research Inputs**: `specs/552_align_history_vocabulary_with_paper/reports/01_align-history-vocabulary-paper.md`
- **Artifacts**: plans/01_align-history-vocabulary-paper.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This repository's `WorldHistory` denotes the paper's *convex history*, one tier below what its
name suggests; the paper reserves "world history" (where it survives at all) for the *total*
tier and has settled on *possible world* for it. The mismatch is a uniform shift-by-one across
583 live `.lean` lines in 71 files plus ~174 lines of prose in five roots, and it is repaired by
alpha-renaming plus re-quotation — no proof term changes. Done means: `ConvexHistory` is the sole
Lean name for the convex tier, `TaskFrame.HF` is the sole Lean name for the paper's possible
worlds, every live docstring and document uses "convex history" or "possible world" per the tier
it actually means, `lake build FormalSystem` is green with no new `sorry`, and no live-tree file
outside `Boneyard/` and `specs/` contains the identifier `WorldHistory`.

### Research Integration

Four research findings materially reshape the dispatch's instructions and are built into the
phases below:

1. **The record file is already re-pinned.** `specs/paper-definitions-of-record.md` carries the
   *current* paper text and hash for `def:world-history` (now at line 717, not the dispatch's
   577-593), `thm:extension` and `cor:occurrence`. **No `sha256:` line, no verbatim block, and no
   `FILE_CHECKSUM` / `PINNED_COMMIT` sentinel changes in this task.** Only the repo's own
   surrounding *prose* is stale (5 sites). Dispatch item (e) collapses from a re-pin to a prose
   edit; dispatch item (f)'s sentinel instruction is vacuous here.
2. **The paper never uses "world history" for the convex tier.** Its 8 surviving "world histor*"
   lines (body prose, `possible_worlds.tex:1014-1052`) all denote the *total* tier. The false
   friend is a direct inversion, not an imprecision — which strengthens the rename. Line 1049
   ("Since the classes in `\W_F` will play no further role below, I will also refer to `H_F` as
   the set of *possible worlds*") is the paper's own licence for `H_F` = possible worlds and for
   this repository's absence of a `\W_F` quotient.
3. **`possible_worlds.tex:1051-1052` (the "bounded convex history is not a possibility in which
   time begins or ends" argument the dispatch cites) is currently COMMENTED OUT.** Do not quote
   those lines as live paper text. The live equivalents are lines 1098 and 1772.
4. **The rebuild blast radius dominates cost.** 241 of 479 live modules transitively import
   `Semantics/WorldHistory.lean`; 247 import `Semantics/PartialHistory.lean`. Lean hashes whole
   files, so a docstring-only edit to either invalidates ~250 `.olean`s. This plan therefore
   budgets exactly **two** full-tree builds (Phase 2 and Phase 5), both guarded and detached, and
   never a per-file build cadence.

**Correction to the research, measured at plan time**: research Finding 3 reported
`check-paper-definitions.sh` silently exiting 0 via its whole-file-checksum fast path. That is no
longer true — the paper has since changed, the fast path no longer triggers, and the checker now
runs the full manifest and **exits 1 with 6 drifted anchors**: `def:S5`, `def:BX`, `def:BX-z`,
`def:BX-d`, `def:BX-r`, `def:TMplus`. All six belong to the sibling re-pin task; none is this
task's. The verification consequence is recorded in Phase 5: compare the **drifted-anchor set**
against that six-element baseline, never the exit code, and never "green".

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only; no `roadmap_flag` was set, so no roadmap phases are
added and the file is not modified. Two ROADMAP lines (223, 742) name `WorldHistory` in live
steering prose and will become stale identifiers after this task. They are **deliberately not
edited** — the dispatch's scope boundary excludes `specs/`. Phase 5 records the finding for a
follow-up rather than acting on it.

## Goals & Non-Goals

**Goals**:
- Rename `FormalSystem/Semantics/WorldHistory.lean` -> `ConvexHistory.lean` and the structure,
  namespace and four derived identifiers with it, with zero change to any proof term.
- Make `TaskFrame.HF` the documented sole Lean name for the paper's *possible world*.
- Bring every live docstring, README, `docs/`, `typst/` and `latex/` line onto the paper's
  three-tier vocabulary: *partial history* / *convex history* / *possible world*.
- Re-quote the stale `verbatim:` paper quotations from the current `def:world-history` text.
- Correct the record file's stale prose without touching any pinned text, hash, or sentinel.

**Non-Goals**:
- No `abbrev PossibleWorld F := F.HF` (breaks dot-notation on a subtype and reintroduces the
  ambiguity being removed).
- No `\W_F` quotient construction.
- No collapse, weakening or deletion of the convex layer; no removal of any `IsTotal` hypothesis;
  no touching the `∃ (ht : τ.domain t)` guard in `TruthAt`'s atom clause.
- No edits under `Boneyard/`, under `specs/` other than `paper-definitions-of-record.md`, or to
  generated artifacts (`latex/**/build/*`, `*.aux`, `*.toc`, `*.log`).
- No change to the paper itself, and no reconciliation footnote reintroduced.
- No `sha256:`, `FILE_CHECKSUM`, or `PINNED_COMMIT` change; no re-pinning of the six sibling-task
  drifted anchors.
- No new theorem, definition, or proof.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Mechanical `s/WorldHistory/ConvexHistory/` escapes into `Boneyard/` or `specs/` (~2505 archival occurrences) | H | M | Drive sed from an explicit file list: `git ls-files 'FormalSystem/**/*.lean' 'FormalSystem/*.lean' 'Tests/**/*.lean' \| grep -v '/Boneyard/'`. Never `grep -rl` from the repo root. Confirm with `git status --short` that no `specs/` or `Boneyard/` path is modified in Phase 2. |
| Blanket "world history" -> "convex history" substitution mistranslates the 34 sites that mean the total tier | H | H | Do the `total world histor*` -> "possible world" collapse as its own first pass in each prose phase, before any bare-phrase substitution. The modifier is absorbed, not translated. |
| `typst-sync-check.sh` breaks silently: it prints `FAIL` and still exits 0 | M | H | Compare `TOTAL_VIOLATIONS` numerically to the recorded baseline **4**; any value > 4 is a regression. Phase 4 must update `typst/chapters/02-semantics.typ:262, 285, 341`, which backtick the renamed path and type. |
| `check-paper-definitions.sh` exit code misread as a gate | M | H | Baseline is **exit 1, 6 drifted, 0 unresolved**. Compare the drifted-anchor *set* to `{def:S5, def:BX, def:BX-z, def:BX-d, def:BX-r, def:TMplus}`. Appearance of `def:world-history`, `thm:extension` or `cor:occurrence` in that set is a hard failure. |
| C19 docstring-coverage floor eroded by bulk docstring rewriting (92.33% actual vs 90% floor — 2.33 points of headroom) | M | M | Every docstring change is a *replacement*, never a deletion. Re-run `check-module-invariants.sh` in Phase 5 and compare the C19 refined percentage to 92.33%. |
| Repeated ~250-module rebuilds turn a 7-hour task into a multi-day one | M | M | Exactly two builds, both `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build FormalSystem` under `run_in_background: true`. Never a foreground or per-file `lake build`. |
| A proof term needs to change | H | L | **Stop and record**, per the dispatch. This is a signal that the rename is not alpha-equivalent, not something to adapt the proof around. |
| Re-quoting from the wrong paper text (commented-out lines 1051-1052) | M | M | Copy only from `possible_worlds.tex:2880-2886` (sha256 `550661d3…`) and, for the body layering, from the live lines 1019-1023 and 1049. Never from a `%`-prefixed line. |
| A future reader "corrects" the repo back toward the paper's own residual body-prose drift | L | M | Record the split once, in the `ConvexHistory.lean` module docstring: cite `def:world-history` (appendix, settled) as authoritative and note line 1049's collapse sentence. Do not add a reconciliation footnote. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 2 |
| 3 | 5 | 1, 2, 3, 4 |

Phases within the same wave can execute in parallel. Territories are disjoint by wave:
Phase 1 owns `specs/paper-definitions-of-record.md` only; Phase 2 owns the live `.lean` tree;
Phase 3 owns `FormalSystem/**` (`.lean` docstrings + `README.md`); Phase 4 owns
`docs/`, `typst/`, `latex/`. Phase 5 owns no files (verification only).

---

### Phase 1: Correct the record file's stale prose [COMPLETED]

**Goal**: Bring `specs/paper-definitions-of-record.md`'s own commentary onto the paper's
vocabulary, without touching any pinned text, hash, or sentinel.

**Tasks**:
- [x] Confirm the three anchors are already current: run `bash scripts/check-paper-definitions.sh`
      and verify `def:world-history`, `thm:extension`, `cor:occurrence` are absent from the
      drifted list (expected drift set: the six `def:S5`/`def:BX*`/`def:TMplus` anchors).
- [x] Line 714 heading: `partial history, world history, totality, the extension order, \`H_F\``
      -> `partial history, convex history, possible world, the extension order, \`H_F\``.
- [x] Line ~728 layering sentence: `**world history** (convex domain)` -> `**convex history**
      (convex domain)`; `**total** / **possible world**` -> `**possible world**`. This sentence is
      the wording that seeded the Lean naming; correcting it is the point of the phase.
- [x] Line 733 heading: `extends to a total world history` -> `extends to a possible world`.
- [x] Line 745 heading: `in some total world history` -> `in some possible world`.
- [x] Line ~898 commentary: `the full set of *total* world histories` -> `the set of possible
      worlds`.
- [x] Follow the file's own "How to extend this record" procedure (~line 1613) for any addendum
      note recording that this task changed prose only. *(deviation: altered — steps 1-3 of that
      procedure are anchor-addition steps and were vacuous here since no anchor was added or
      re-pinned; only step 4, the checker re-run, applied. An addendum subsection "Vocabulary
      alignment (2026-09-07): prose only, no re-pin" was added recording that.)*
- [x] Verify by inspection that lines 195, 228, 231, 339, 521 (archival drift-log entries) and
      line ~1768 (a `>`-quoted **verbatim paper footnote**, hashed) are UNCHANGED. *(deviation:
      altered — measured at implementation time, only lines 228 and 1768 carry the phrase at all;
      195/231/339/521 do not and needed no protection.)*
- [x] `git diff` review: zero changes to any line matching `^sha256:`, `FILE_CHECKSUM`,
      `PINNED_COMMIT`, or to any line inside a fenced ` ```latex ` block.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: five stale-prose sites at lines 714, ~728, 733, 745, ~898, with archival
sites at 195/228/231/339/521 and a verbatim-quotation site at ~1768 that must not move. Confirm
at implementation time with `grep -n 'world histor' specs/paper-definitions-of-record.md` and
classify every hit as edit / archival / verbatim-quotation before touching any of them; line
numbers will have drifted if any sibling task has landed since this plan was written.

**Files to modify**:
- `specs/paper-definitions-of-record.md` — prose headings and commentary only

**Verification**:
- `grep -n 'world histor' specs/paper-definitions-of-record.md` returns only the archival
  drift-log lines and the verbatim paper-footnote quotation.
- `git diff -- specs/paper-definitions-of-record.md | grep -E '^[-+]sha256:|FILE_CHECKSUM|PINNED_COMMIT'` is empty.
- `bash scripts/check-paper-definitions.sh` drift set is unchanged (still exactly the six sibling
  anchors).

---

### Phase 2: Lean identifier and file rename [COMPLETED]

**Goal**: `ConvexHistory` becomes the name of the convex-tier structure, namespace, module file
and every derived identifier, with a green `lake build FormalSystem` and zero proof-term change.

**Tasks**:
- [x] `git mv FormalSystem/Semantics/WorldHistory.lean FormalSystem/Semantics/ConvexHistory.lean`.
- [x] Build the explicit target list:
      `git ls-files 'FormalSystem/**/*.lean' 'FormalSystem/*.lean' 'Tests/**/*.lean' | grep -v '/Boneyard/'`.
- [x] Apply `s/WorldHistory/ConvexHistory/g` over that list only. This correctly handles every
      CamelCase site including `toWorldHistory`, `isTotal_toWorldHistory` and
      `toWorldHistory_toPartialHistory`.
- [x] Apply the separate lowercase rule `s/worldHistory_ext/convexHistory_ext/g` over the same
      list (4 sites: `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean` ×3,
      `Semantics/ShiftSet.lean` ×1).
- [x] Confirm the 7 `import FormalSystem.Semantics.ConvexHistory` lines resolved
      (`Semantics.lean`, `Semantics/Truth.lean`, `Semantics/IntNormalForm.lean`,
      `Semantics/TaskModel.lean`, `Semantics/Extension/Extension.lean`,
      `Metalogic/Decidability/Propositional/Decidable.lean`, `Examples/TemporalStructures.lean`).
- [x] Update `FormalSystem/Semantics.lean:242`'s markdown link target
      `[WorldHistory.lean](Semantics/WorldHistory.lean)` -> `ConvexHistory.lean` path.
- [x] Update `FormalSystem/Semantics/README.md:23`'s file reference to the renamed module (same
      commit as the rename, so `readme-lint.sh` broken-file-references stays at 0).
- [x] Confirm `PartialHistory`, `toPartialHistory`, `IsTotal`, `ofTotal`, `timeShift` and
      `TaskFrame.HF` are all unchanged.
- [x] `git diff` review confirming **no proof term changed** — every hunk is an identifier, an
      import path, or a comment. If a tactic block or term body differs, STOP and record.
- [x] Single guarded background build:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build FormalSystem`
      under `run_in_background: true`. Do not close the phase before the completion notification.
      *(deviation: altered — the first attempt was SIGTERM-killed (Lean exit 143) under host memory
      pressure at module 1008 of 1008 on
      `Metalogic/Decidability/Verified/Termination/MintBound/MintPotential.lean`, a module this
      task never touches and which contains zero `ConvexHistory` occurrences. Rather than pay a
      second ~250-module cycle for the same evidence, Phase 2's build was merged into Phase 5's
      single `--memory-bound` rebuild, which covers both. Every rename-affected module compiled
      in the first attempt: it logged exactly one error, the unrelated SIGTERM.)*

**Timing**: 1.5 hours (dominated by the ~250-module rebuild)

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 583 `WorldHistory` lines across 71 live `.lean` files plus 2 `Tests/` files;
7 import lines; 4 `worldHistory_ext` sites; `ConvexHistory` free at 0 live occurrences. Confirm at
implementation time by re-running the census commands in the Verification block **before** editing
(to establish the pre-edit count) and again after; a post-edit `ConvexHistory` count materially
below the pre-edit `WorldHistory` count means the target list was too narrow.

**Files to modify**:
- `FormalSystem/Semantics/WorldHistory.lean` -> `FormalSystem/Semantics/ConvexHistory.lean` (git mv)
- ~71 live `FormalSystem/**/*.lean` files — identifier occurrences only
- `Tests/BimodalTest/Semantics/TruthTest.lean`, `Tests/BimodalTest/.../SemanticBenchmark.lean`
- `FormalSystem/Semantics.lean` — lines 21, 52, 104, 107, 167, 185, 234, 242 (identifier and link
  only; the line-185 table-row split belongs to Phase 3)
- `FormalSystem/Semantics/README.md` — line 23 file reference only

**Verification**:
- `git ls-files 'FormalSystem/**/*.lean' 'FormalSystem/*.lean' 'Tests/**/*.lean' | grep -v '/Boneyard/' | xargs grep -c 'WorldHistory' | grep -v ':0'` returns nothing.
- `git status --short` lists no path under `specs/` or `Boneyard/`.
- `lake build FormalSystem` green; `sorry` count (live tree, excl. `Boneyard/`) still **348**.

---

### Phase 3: Lean prose, docstrings and paper re-quotation [COMPLETED]

**Goal**: Every live Lean docstring and `FormalSystem/` README states the paper's three tiers
correctly, with all `verbatim:` quotations copied fresh from the current paper text.

**Tasks**:
- [x] First pass: collapse all `total world histor*` occurrences under `FormalSystem/` to
      "possible world(s)". The modifier is absorbed; do not translate it.
- [x] Second pass: remaining bare "world history" occurrences -> "convex history" where the convex
      tier is meant, "possible world" where the total tier is meant. Classify each; do not batch.
- [x] Re-quote the `PartialHistory.lean` module docstring (lines ~20-35) by **copying** the
      current `def:world-history` block from `possible_worlds.tex:2880-2886` (sha256
      `550661d3…`), not by adjusting in place. Note the paper's two additional changes: "over a
      frame" -> "over a **task** frame", and the deleted inline `%` converse-convention comment
      that lines 24-26 still block-quote — remove that quotation, it no longer exists in source.
- [x] Re-quote the same block in the `ConvexHistory.lean` module docstring (lines ~20-30), and add
      the one-time record that the paper's own body prose (lines 1014-1052) still says "world
      history" for the *total* tier while the settled appendix definition governs — citing line
      1049's collapse sentence. No reconciliation footnote.
- [x] Fix the remaining stale-`verbatim:` sites: `PartialHistory.lean:88-90, 92, 171`;
      `ConvexHistory.lean:119` (the `convex` field docstring), `:355`, `:370` (`IsTotal`);
      `Semantics/Extension/Extension.lean:132-134`;
      `Metalogic/Algebraic/FlowFrame.lean:51, 349, 389`;
      `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean:386`.
- [x] Dispatch item (c): rewrite the `TaskFrame.HF` docstring (`ConvexHistory.lean` ~405-420) to
      say that an element of `F.HF` **is a possible world** and that `IsTotal` is the predicate
      form of the same notion. **Keep** the already-current quotation at ~425-426 ("The set of all
      possible worlds over $\F$ is denoted $H_{\F}$") and build the rewrite around it. Introduce
      no `abbrev PossibleWorld`.
- [x] Dispatch item (d): split `FormalSystem/Semantics.lean:185`'s single row
      `| World History | τ : X → W convex | WorldHistory F with convex proof |` into two rows,
      one per tier (convex history -> `ConvexHistory F`; possible world -> `F.HF` / `IsTotal`).
      Update the surrounding lines 107 and 167 prose to match.
- [x] Fix the four substantive (non-terminological) README errors:
      - `FormalSystem/Semantics/README.md:39` — "Partial world-histories **on convex subsets**"
        is doubly wrong; partial histories are precisely the tier without a convexity requirement.
      - `FormalSystem/Semantics/README.md:49` — "`WorldHistory`: **Infinite sequence** of worlds"
        is wrong; a convex history may be bounded (the chess example).
      - `FormalSystem/Semantics/Extension/README.md:1,3` — "partial **world** histories" / "Every
        partial **world** history extends to a total one" -> "partial histories" / "…extends to a
        possible world".
      - Re-stamp the dates on `FormalSystem/Semantics/README.md` and
        `FormalSystem/Semantics/Extension/README.md` (both already flagged STALE DATE by
        `readme-lint.sh`, and both edited here).
- [x] Confirm no docstring was net-shortened by deletion — every change is a replacement (C19
      headroom is 2.33 points).
- [x] Do **not** build in this phase; the docstring invalidations are paid once in Phase 5.
- [x] *(deviation: added — `specs/paper-definitions-of-record.md`'s "Untracked sources" block,
      which Phase 1 was told to leave unchanged as a hashed verbatim quotation, was found to carry
      the **superseded** text of the finite-case footnote: the live paper
      (`possible_worlds.tex:1772`) now reads "bounded convex history" where the block reads
      "bounded world history", and gained a comma after "In this case". The block is in fact
      **untracked** — no `sha256:` line, no manifest row, not read by
      `check-paper-definitions.sh` — so re-quoting it moves no pin. It was re-quoted here together
      with `Metalogic/Decidability/BiLasso/Agreement.lean`, which block-quotes the same footnote,
      so the two copies agree and both are verbatim against the live paper.)*
- [x] *(deviation: altered — Phases 2 and 3 landed in one commit. Phase 3 edits docstrings inside
      the same ~30 files Phase 2 renames identifiers in, and Phase 2's close slipped past Phase 3's
      start when its build was OOM-killed; the two edit sets are not separable by pathspec after
      that. Phase 2's atomic-batch guarantee is preserved in substance: the pure-rename property was
      verified before any Phase 3 edit, by diffing every changed line with the rename applied.)*

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: ~94 "world histor*" prose lines under `FormalSystem/`, of which ~34 tree-wide
are the `total world histor*` idiom; heaviest files `Semantics/ConvexHistory.lean` (22),
`Semantics/Extension/Extension.lean` (12), `Semantics/IntNormalForm.lean` (8), `Semantics.lean`
(6), `Metalogic/Algebraic/FlowFrame.lean` (6), `Semantics/PartialHistory.lean` (5),
`Semantics/Extension/README.md` (5). Confirm at implementation time with
`grep -rin 'world histor' FormalSystem | grep -v '/Boneyard/' | wc -l` before and after; the
after-count must be 0, and the per-file distribution should match within a line or two. All line
numbers in the task list above are pre-Phase-2 and will have shifted.

**Files to modify**:
- `FormalSystem/Semantics/PartialHistory.lean`, `FormalSystem/Semantics/ConvexHistory.lean`,
  `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/Extension/Extension.lean`,
  `FormalSystem/Semantics/IntNormalForm.lean`, `FormalSystem/Metalogic/Algebraic/FlowFrame.lean`,
  `FormalSystem/Metalogic/Decidability/Verified/Bridge/RegionFrame.lean`, and the residual
  `FormalSystem/**` prose sites — docstrings and comments only
- `FormalSystem/Semantics/README.md`, `FormalSystem/Semantics/Extension/README.md`

**Verification**:
- `grep -rin 'world histor' FormalSystem | grep -v '/Boneyard/'` returns nothing.
- `git diff` shows every hunk inside a `/-- … -/`, `/-! … -/`, `--` comment, or markdown file.
- The re-quoted blocks match `sed -n '2880,2886p' /home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`
  modulo the docstring's own line wrapping.
- No `%`-prefixed paper line is quoted anywhere.

---

### Phase 4: docs / typst / latex prose [COMPLETED]

**Goal**: The documentation, Typst and LaTeX trees use the paper's vocabulary and reference the
renamed module, with `typst-sync-check.sh` violations not exceeding the baseline of 4.

**Tasks**:
- [x] First pass again: `total world histor*` -> "possible world(s)" across all three roots.
- [x] Second pass: remaining "world history" -> "convex history" or "possible world" by tier.
- [x] `typst/chapters/02-semantics.typ` — the typst-sync-check-coupled sites:
      - line 262: backticked `Semantics/WorldHistory.lean` path and `WorldHistory` /
        `WorldHistory.IsTotal` type names -> `ConvexHistory` forms.
      - line 285: footnote "quantifies over all total world histories (`WorldHistory.IsTotal`)"
        -> "quantifies over all possible worlds (`ConvexHistory.IsTotal`)".
      - line 341: footnote path `timeShift` in `Semantics/WorldHistory.lean` -> `ConvexHistory.lean`.
      - remaining ~13 prose lines in the same file.
- [x] `typst/chapters/00-introduction.typ` (~9), `typst/FormalFoundations.typ` (~2, including the
      lines 247-249 restatement of the old two-step layering), plus 3 singleton files.
- [x] `docs/theorem-index.md:34` — split the glossary row
      `| world history / possible world | FormalSystem.Semantics.WorldHistory | … |` into two
      rows, mirroring the `Semantics.lean:185` fix. This row is the false friend written down.
- [x] `docs/architecture/BFMCS_ARCHITECTURE.md` (~11), `docs/user-guide/architecture.md` (~8),
      `docs/reference/operators.md` (~7), `docs/user-guide/tutorial.md` (~3),
      `docs/reference/API_REFERENCE.md` (~2), `docs/development/LEAN_STYLE_GUIDE.md` (~2),
      `docs/development/DIRECTORY_README_STANDARD.md` (~1 — also fix line ~411's stale
      three-parameter signature `h : WorldHistory W S T`; current is `ConvexHistory (F : TaskFrame)`).
- [x] `latex/subfiles/02-Semantics.tex` (~10), `latex/subfiles/00-Introduction.tex` (~3),
      `latex/subfiles/06-Notes.tex` (~1), `latex/assets/bimodal-notation.sty:72`
      (`% --- World History ---` section comment).
- [x] `latex/subfiles/04-Metalogic.tex:54` — the sole `latex/` identifier site. Update the module
      path AND correct the stale line citation: it cites `WorldHistory.lean:246` for `timeShift`,
      which now lives near line 304 (re-derive the post-rename line number rather than trusting
      either figure).
- [x] `Tests/BimodalTest/Semantics/TruthTest.lean:35` comment (1 line).
- [x] Skip `latex/**/build/*` and `latex/build/*` entirely — generated `.aux`, `.toc`, `.log`.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: ~35 lines in `docs/`, ~30 in `typst/`, ~14 in source `latex/` (excluding
generated `build/`), 1 in `Tests/`; 1 identifier site in `latex/`. Confirm at implementation time
with `grep -rin 'world histor' docs typst latex Tests | grep -v '/build/' | wc -l` before and
after (after must be 0), and with a `--include` filtered grep confirming the excluded generated
files were never written.

**Files to modify**:
- `typst/chapters/02-semantics.typ`, `typst/chapters/00-introduction.typ`,
  `typst/FormalFoundations.typ`, 3 further `typst/` singletons
- `docs/theorem-index.md`, `docs/architecture/BFMCS_ARCHITECTURE.md`,
  `docs/user-guide/architecture.md`, `docs/user-guide/tutorial.md`, `docs/reference/operators.md`,
  `docs/reference/API_REFERENCE.md`, `docs/development/LEAN_STYLE_GUIDE.md`,
  `docs/development/DIRECTORY_README_STANDARD.md`
- `latex/subfiles/02-Semantics.tex`, `00-Introduction.tex`, `06-Notes.tex`, `04-Metalogic.tex`,
  `latex/assets/bimodal-notation.sty`
- `Tests/BimodalTest/Semantics/TruthTest.lean` (comment line only)

**Verification**:
- `grep -rin 'world histor' docs typst latex Tests | grep -v '/build/'` returns nothing.
- `bash scripts/typst-sync-check.sh` reports `TOTAL_VIOLATIONS=4` (baseline), `MISMATCH_COUNT=0`,
  `MA_COUNT_MISMATCHES=0`. Read the numbers, not the exit code.
- `git status --short` lists no path under `latex/**/build/`.

---

### Phase 5: Full gate and invariant reconciliation [NOT STARTED]

**Goal**: Prove the whole change green against the complete gate set with no regression on any
recorded baseline.

**Tasks**:
- [ ] Single guarded background rebuild (pays for Phase 3's ~250-module docstring invalidation):
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build FormalSystem`
      under `run_in_background: true`. Wait for the completion notification before proceeding.
- [ ] `sorry` count over the live tree excluding `Boneyard/` equals **348** (the gate is "no *new*
      sorry", not zero).
- [ ] `bash scripts/check-module-invariants.sh` — expect `ALL CHECKS PASSED`, exit 0, and a C19
      refined docstring-coverage figure **>= 92.33%**.
- [ ] `bash scripts/typst-sync-check.sh` — `TOTAL_VIOLATIONS` must be **<= 4**. Do not read the
      exit code.
- [ ] `bash scripts/readme-lint.sh` — `RESULT: PASS`, broken file references **0**, stale-date
      count **<= 2** (the two READMEs re-stamped in Phase 3 should have cleared).
- [ ] `bash scripts/check-paper-definitions.sh` — drifted set must be **exactly**
      `{def:S5, def:BX, def:BX-z, def:BX-d, def:BX-r, def:TMplus}`, 0 unresolved. Exit 1 is the
      baseline, not a failure. Appearance of `def:world-history`, `thm:extension` or
      `cor:occurrence` in the drift set is a hard failure and must be repaired before closing.
- [ ] Identifier-absence grep: `grep -rn 'WorldHistory\|worldHistory' --exclude-dir=.git .` returns
      hits ONLY under `Boneyard/`, `specs/` (archival, plus the two live `specs/ROADMAP.md`
      mentions), and `latex/**/build/` generated artifacts.
- [ ] Prose-absence grep: `grep -rin 'world histor' --exclude-dir=.git . | grep -v '/Boneyard/' |
      grep -v '^specs/' | grep -v '/build/'` returns nothing.
- [ ] Confirm no proof term changed across the whole task: `git diff <base>..HEAD` hunks are
      identifiers, imports, comments, docstrings and markdown only.
- [ ] Record in the summary, without acting on them: (a) `specs/ROADMAP.md:223, 742` name
      `WorldHistory` in live steering prose and are left stale by the dispatch's `specs/` scope
      boundary — recommend a follow-up; (b) the paper's own body prose (`possible_worlds.tex`
      lines 1014-1052) still uses "world history" for the total tier, which is the paper's drift,
      not this repository's.

**Timing**: 1.5 hours (dominated by the rebuild)

**Depends on**: 1, 2, 3, 4

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: gate baselines are `sorry`=348, C19 refined 92.33%, `typst-sync-check`
`TOTAL_VIOLATIONS=4`, `readme-lint` PASS with 2 stale dates and 0 broken refs,
`check-paper-definitions` exit 1 with 6 drifted / 0 unresolved. Every one of these was measured
at plan time and may have moved if a sibling task landed since. Re-measure each baseline against
the merge-base commit before comparing, and report any baseline that has moved rather than
treating the plan's figure as authoritative.

**Files to modify**:
- None (verification only)

**Verification**:
- All eight checks above pass against their recorded (or freshly re-measured) baselines.
- The task is complete when the two absence-greps are clean and the build is green.

## Lean Challenge Statements

This task introduces, removes and reproves **no** declarations: it is alpha-renaming plus prose,
and any change to a proof term is an explicit stop-and-report signal (see Risks). The identifier
set named under `- **Goals**:` is therefore empty, and this section's declaration set is
correspondingly empty — the two sets agree trivially. No ```` ```lean ```` block is emitted,
because emitting one would declare an identifier this plan does not commit to proving.

## Testing & Validation

- [ ] `lake build FormalSystem` green (Phase 2 and Phase 5), no new errors.
- [ ] Live-tree `sorry` count unchanged at 348 (excluding `Boneyard/`).
- [ ] `scripts/check-module-invariants.sh`: `ALL CHECKS PASSED`, C19 refined >= 92.33%.
- [ ] `scripts/typst-sync-check.sh`: `TOTAL_VIOLATIONS <= 4`.
- [ ] `scripts/readme-lint.sh`: `RESULT: PASS`, 0 broken file references.
- [ ] `scripts/check-paper-definitions.sh`: drift set exactly the six sibling-task anchors.
- [ ] Identifier `WorldHistory` absent from the live tree outside `Boneyard/`, `specs/`, and
      generated `latex/**/build/`.
- [ ] Phrase "world histor*" absent from the live tree outside `Boneyard/`, `specs/`, and
      generated artifacts.
- [ ] No proof term changed anywhere in the task diff.

## Artifacts & Outputs

- `FormalSystem/Semantics/ConvexHistory.lean` (renamed from `WorldHistory.lean`)
- ~71 modified live `FormalSystem/**/*.lean` files and 2 `Tests/` files
- Updated `FormalSystem/Semantics/README.md`, `FormalSystem/Semantics/Extension/README.md`
- Updated `docs/`, `typst/`, `latex/` prose (8 + 6 + 5 files)
- Updated `specs/paper-definitions-of-record.md` (prose only)
- `specs/552_align_history_vocabulary_with_paper/summaries/01_*-summary.md`

## Rollback/Contingency

Every phase is an ordinary git commit on the task branch and the whole task is revertible with
`git revert` over the phase commits in reverse order; the file rename reverts cleanly because it
was made with `git mv`. If Phase 2's build fails, revert only Phase 2's atomic-batch commit — no
later phase depends on it having landed. If a proof term is found to require change at any point,
**stop**, record the specific declaration and the reason in the summary, and leave the task
`[BLOCKED]` rather than adapting the proof: that outcome falsifies the alpha-renaming premise and
belongs to the separate convex-layer-collapse question, not to this task.
