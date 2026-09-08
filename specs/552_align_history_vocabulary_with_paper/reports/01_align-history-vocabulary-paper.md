# Research Report: Task #552

**Task**: 552 - Align history vocabulary with paper (`WorldHistory` -> `ConvexHistory`)
**Started**: 2026-09-07T00:00:00Z
**Completed**: 2026-09-07T00:00:00Z
**Effort**: Medium-large (mechanical identifier sweep is small; the prose sweep is ~181 occurrences across 5 roots; one full ~250-module rebuild)
**Dependencies**: Paper-anchor re-pin task (file-serialisation only on `specs/paper-definitions-of-record.md`) -- **this research finds that dependency is already discharged; see Finding 2**
**Sources/Inputs**:
- Codebase (`FormalSystem/`, `Tests/`, `docs/`, `typst/`, `latex/`), grep/AST-free identifier census
- Literature source: `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` (`def:world-history`, `thm:extension`, `cor:occurrence`, body SS at lines 1014-1052)
- `specs/paper-definitions-of-record.md` + `scripts/check-paper-definitions.sh` (43-anchor manifest audit)
- Repo gates: `scripts/check-module-invariants.sh`, `scripts/typst-sync-check.sh`, `scripts/readme-lint.sh`
- `.claude/context/project/lean4/operations/long-builds.md`
- lean-lsp MCP: not required (see Decisions)

**Artifacts**: - `specs/552_align_history_vocabulary_with_paper/reports/01_align-history-vocabulary-paper.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The dispatch's premise is correct and the rename is safe.** `WorldHistory` in this repository
  denotes the paper's *convex history*; the paper's own surviving uses of "world history" denote
  the *total* tier. The false-friend is therefore sharper than the description states, not softer.
  `ConvexHistory` is free (0 live-tree occurrences). The identifier sweep is pure alpha-renaming:
  no structure extends `WorldHistory`, `toWorldHistory` is a hand-written `def` (not an
  auto-generated parent projection), and no build script, manifest, allowlist, JSON fixture or
  benchmark file names the type.
- **Work item (e) is already done and must not be redone.** `specs/paper-definitions-of-record.md`
  already quotes the *current* paper text for all three anchors, and all 43 manifest hashes match
  the live paper (verified anchor-by-anchor). What remains in that file is three stale section
  **headings** and one stale layering **commentary** paragraph -- prose only, no hash or checksum
  sentinel change. The dispatch's "15 drifted / 9 unresolved" figure is stale.
- **`check-paper-definitions.sh` is currently a no-op gate.** The pinned `FILE_CHECKSUM` matches
  the live paper byte-for-byte, so the script takes its case-(a) fast path and exits 0 *without
  resolving a single anchor*. "Checker green" is therefore not evidence of anything for this task;
  verification must re-hash per anchor via `--resolve` (a 43-anchor loop is given below).
- **The real work is prose, and much of it is stale *verbatim* quotation, not word choice.**
  ~181 occurrences of "world histor*" on 175 live lines. At least 8 Lean docstrings quote
  `def:world-history` under an explicit "verbatim:" label with text that **no longer exists in the
  paper** -- the paper also changed "over a frame" -> "over a task frame" and deleted an inline
  `%` converse-convention comment that `PartialHistory.lean` still block-quotes. These must be
  re-quoted from the current source, exactly as the dispatch says.
- **Recommended approach**: one batched, verify-once phase structure -- (1) record-file prose,
  (2) Lean identifier + file rename, (3) Lean prose/docstring re-quote, (4) docs/typst/latex
  prose, (5) single guarded background `lake build FormalSystem` + gate sweep. A sorry-free path
  exists trivially: no proof term changes.

## Context & Scope

Researched: whether the described rename is mechanically safe, what the paper actually says today,
what state the definitions-of-record file is really in, which repo gates the change couples to,
and how large the prose sweep is. Constraints honoured: no proof term may change; `PartialHistory`,
`IsTotal`, `ofTotal`, `timeShift`, `TaskFrame.HF` keep their names; `Boneyard/` and `specs/` are
out of scope; the convex layer is not to be collapsed (that is a separate, already-created task,
visible at `specs/TODO.md:157`).

## Findings

### Codebase Patterns

**Identifier census (live tree = `FormalSystem/` excl. `Boneyard/`, plus `Tests/`)**

| Token | Live sites | Where |
|---|---|---|
| `WorldHistory` (bare) | 611 | 71 `.lean` files |
| `toWorldHistory` | 6 | `Semantics/Extension/Extension.lean` only |
| `worldHistory_ext` | 4 | `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean` (3), `Semantics/ShiftSet.lean` (1, prose mention) |
| `isTotal_toWorldHistory` | 2 | `Semantics/Extension/Extension.lean` |
| `toWorldHistory_toPartialHistory` | 1 | `Semantics/Extension/Extension.lean` |
| **Total live `.lean` lines** | **583** | across **71** files |
| `import FormalSystem.Semantics.WorldHistory` | **7** (not 8) | `Semantics.lean`, `Semantics/Truth.lean`, `Semantics/IntNormalForm.lean`, `Semantics/TaskModel.lean`, `Semantics/Extension/Extension.lean`, `Metalogic/Decidability/Propositional/Decidable.lean`, `Examples/TemporalStructures.lean` |
| `ConvexHistory` / `convexHistory` | **0** live (10 hits, all in `specs/TODO.md` + `specs/state.json` task descriptions) | target name is free |

Heaviest live files (unchanged from the dispatch's measurement): `Semantics/Truth.lean` 64,
`Metalogic/Decidability/Verified/Decidable.lean` 57, `Semantics/IntTransfer.lean` 33,
`Semantics/WorldHistory.lean` 32, `Semantics/Validity.lean` 31, `Semantics/StarTruth.lean` 30,
`Semantics/StarPasting.lean` 22.

**Rename-safety probes (all clean)**

- `grep 'extends.*WorldHistory'` over the live tree: **no results**. Nothing extends the
  structure, so there is no auto-generated `toWorldHistory` parent projection to worry about.
  The `toWorldHistory` that exists is a hand-written `def` in the `PartialHistory` namespace
  (`Semantics/Extension/Extension.lean:151`), promoting a total `PartialHistory`.
  `toPartialHistory` (the genuine auto-generated projection, from
  `structure WorldHistory ... extends PartialHistory F`) is untouched by the rename.
- `namespace WorldHistory` / `end WorldHistory` occur exactly once each
  (`Semantics/WorldHistory.lean:126,403`). No `open WorldHistory` anywhere.
- No non-`.lean`, non-`.md` file in the repo names the type: `scripts/*.txt`, `*.json`, `*.yml`,
  `*.sh`, `*.py`, `lakefile.lean`, `.github/` all return zero. `MainResults.lean` does not name it.
  This confirms the dispatch's "no fixture tail" claim.
- Only lowercase-initial variants in the live tree are the three `toWorldHistory*` forms and
  `worldHistory_ext`. A naive `s/WorldHistory/ConvexHistory/g` handles every CamelCase site
  correctly; `worldHistory_ext -> convexHistory_ext` needs its own lowercase rule. No `world_history`
  snake_case identifier exists.
- `Boneyard/` (7 files, incl. `ChainCompleteness/Bundle/SuccChainWorldHistory.lean`) is **not
  built**: `lakefile.lean`'s `lean_lib FormalSystem` uses `roots := #[`FormalSystem]` with default
  globs, and `FormalSystem.lean` -> `FormalSystem/FormalSystem.lean` never reaches `Boneyard`.
  Leaving `WorldHistory` there cannot break the build. Confirmed: no live file imports
  `FormalSystem.Boneyard.*`.

**`Tests/` (6 sites, 2 files)** -- `Tests/BimodalTest/Semantics/TruthTest.lean` (5, using
`WorldHistory.trivial` / `WorldHistory.ofTotal` inside `simp` sets) and
`SemanticBenchmark.lean:57`. Purely mechanical.

### Finding 1 -- The paper's real vocabulary, and a correction to the dispatch

The dispatch states the paper "does NOT use the term *world history*". **That is false of the
current text**: "world histor*" survives on 8 lines, all confined to the body prose block at
lines 1014-1052, *before* the sentence that settles the terminology. The layering there reads:

- line 1019: an individual game of chess "may be identified with a **convex history**"
- line 1020: "A \textit{world history} is any **convex history** $\tau : X \to W$ whose domain is
  \textit{total}, so that $X = D$."
- line 1023: "Since partial histories, convex histories, and world histories differ only in their
  domains, I will refer to these generically as \textit{histories} wherever the distinction is
  immaterial."
- lines 1044-1047: `\W_{\F} := \{[\tau]_{\F} \mid \tau \in H_{\F}\}` -- the time-shift equivalence
  classes -- is introduced as "the set of all possible worlds"
- line 1049: "**Since the classes in $\W_{\F}$ will play no further role below, I will also refer
  to $H_{\F}$ as the set of \textit{possible worlds}.**"

Everything after line 1049 -- the whole appendix, `def:world-history`, `thm:extension`,
`cor:occurrence` -- uses "possible world" for the top tier and never says "world history" again.
"convex history" occurs 32 times paper-wide.

**Consequences for this task, and they strengthen rather than weaken it:**

1. The paper *never* uses "world history" for the convex tier. In the paper the phrase always
   denotes the **total** tier. This repository's `WorldHistory` denotes the **convex** tier. The
   false-friend is a direct inversion at every one of the 611 sites, not a mere imprecision.
2. `possible world` is unambiguously the right target for the total tier, licensed by line 1049
   in the paper's own voice. `H_F` = possible worlds is the paper's own identification, and the
   absence of a `\W_F` quotient here is explicitly licensed by "will play no further role".
   Record this once, per the dispatch; do not build a quotient.
3. **The dispatch's supporting citation for "a bounded convex history is NOT a possibility in
   which time begins or ends" is drawn from LaTeX lines that are currently COMMENTED OUT**
   (`possible_worlds.tex:1051-1052`, both `%`-prefixed). The live argument for the same point is
   at line 1098 (the chess-blunder passage) and 1772. Do not quote the commented lines as live
   paper text in any docstring.
4. The 8 body-prose "world history" lines are **the paper's own residual drift**, not this
   repository's. They are out of scope (the paper is read-only input), but they should be recorded
   so a future reader does not "fix" the repo back toward them.

**Verbatim current `def:world-history` (`possible_worlds.tex:2880-2886`, sha256
`550661d3b388c3ef494ffb81c643ab5a550f996a5a86329afc557f41ed7872e7`)** -- this is the text every
re-quote must copy from:

```latex
\begin{Ddef} \label{def:world-history}
	A \textit{partial history} over a task frame $\F = \tuple{W, \D, \Rightarrow}$ is a function $\tau : X \to W$ on a nonempty set $X \subseteq D$ where $\tau(x) \Rightarrow_{y-x} \tau(y)$ for all times $x, y \in X$.
	A \textit{convex history} is any partial history whose domain $X$ is \textit{convex}, so that $y \in X$ whenever $x, z \in X$ and $x < y < z$.
  A \textit{possible world} is any convex history whose domain is total, so that $X = D$.
	A partial history $\sigma$ \textit{extends} $\tau$ just in case $\dom{\tau} \subseteq \dom{\sigma}$ and $\tau(x) = \sigma(x)$ for all $x \in \dom{\tau}$.
	The set of all possible worlds over $\F$ is denoted $H_{\F}$.
\end{Ddef}
```

`thm:extension` (`65811dcf...`) and `cor:occurrence` (`231c1d3c...`) both already read "possible
world", exactly as the dispatch predicts.

### Finding 2 -- `specs/paper-definitions-of-record.md` is already re-pinned; only prose is stale

The dispatch says the record "still quotes the SUPERSEDED wording" at lines 577-593. **It does
not.** The entry has moved to line 714 and its fenced `latex` block is the *current* paper text
verbatim, with the current hash. A prior task (the HEAD-adjacent 548/550 cluster) landed the
re-pin. I audited **all 43 manifest anchors** by resolving each against the live paper and
comparing to the pinned hash:

```
---- ok=43 drifted=0 unresolved=0 ----
```

What is still stale in that file is **prose around the entries**, and only that:

| Line | Stale text | Should become |
|---|---|---|
| 714 | `### \`def:world-history\` — partial history, **world history**, totality, the extension order, \`H_F\`` | `...partial history, convex history, possible world, the extension order, \`H_F\`` |
| ~726-731 | "**partial history** (nonempty domain, no convexity requirement) -> **world history** (convex domain) -> **total** / **possible world** (`X = D`)" | convex tier renamed to **convex history**; this sentence *is* the wording that seeded the Lean naming |
| 733 | `### \`thm:extension\` — every partial history extends to a **total world history**` | `...extends to a possible world` |
| 745 | `### \`cor:occurrence\` — ... in some **total world history**` | `...in some possible world` |

No `sha256:` line changes. **No `FILE_CHECKSUM` / `PINNED_COMMIT` sentinel change** -- they are
already correct (`FILE_CHECKSUM: 1b3c33a2...` equals `sha256sum` of the live paper). The
dispatch's item (f) instruction to "leave the whole-file checksum sentinels to whichever re-pin
lands second" is therefore vacuous for this task: there is nothing left to re-pin.

Also note lines 195, 228, 231, 339 and 521 of the record contain historical drift-log entries
mentioning these anchors. Those are **archival history** and must not be rewritten -- same
principle as `specs/`.

### Finding 3 -- `check-paper-definitions.sh` currently proves nothing (verification hazard)

```bash
$ bash scripts/check-paper-definitions.sh ; echo EXIT=$?
EXIT=0          # ... with zero output
```

Reading the script (lines 237-245), this is the **case-(a) fast path**: when
`sha256sum(paper) == PINNED_CHECKSUM`, it `exit 0` *before parsing the manifest at all*. Since the
checksum now matches, the gate never resolves an anchor. It cannot detect record drift, and a
green run is not evidence that `def:world-history` is correctly pinned.

**Recommended verification substitute** (this is what I ran; it should go in the plan's verify
step, since it is the only thing that actually exercises the 43 anchors):

```bash
sed -n '/<!-- MANIFEST:BEGIN -->/,/<!-- MANIFEST:END -->/p' specs/paper-definitions-of-record.md \
  | grep -v '<!--' | grep -v '^```' | grep -v '^#' | grep -v '^[[:space:]]*$' \
  | while IFS='|' read -r a k e l h; do
      got=$(bash scripts/check-paper-definitions.sh --resolve "$a|$k|$e|$l" | awk '/^sha256:/{print $2}')
      [ "$got" = "$h" ] || echo "DRIFT $a"
    done
```

### Finding 4 -- Stale *verbatim* quotations (the part that cannot be word-swapped)

At least 8 Lean docstrings quote `def:world-history` under an explicit `verbatim:` or `>` block
label with text that is **no longer in the paper**. The paper changed three things, not one:
`world history` -> `convex history` / `possible world`; **`over a frame` -> `over a task frame`**;
and it **deleted the inline `%` converse-convention comment** that `PartialHistory.lean:24-26`
still block-quotes as source text (`grep 'these instances are covered by the' possible_worlds.tex`
returns nothing).

| File:line | Stale quoted text |
|---|---|
| `Semantics/PartialHistory.lean:20-35` | module block-quote: "over a **frame**", the deleted `%` comment, "A \textit{world history} is any partial history whose domain $X$ is convex", "A world history is \textit{total}--- equivalently, a \textit{possible world}" |
| `Semantics/PartialHistory.lean:88-90` | "verbatim: A \textit{partial history} over a **frame**..." |
| `Semantics/PartialHistory.lean:92` | "The paper's `\textit{world history}` is the **convex** special case" |
| `Semantics/PartialHistory.lean:171` | "verbatim: A world history is \textit{total}--- equivalently..." |
| `Semantics/WorldHistory.lean:20-30` | module docstring, same three defects |
| `Semantics/WorldHistory.lean:119` | structure `convex` field docstring |
| `Semantics/WorldHistory.lean:355`, `:370` | `IsTotal` docstrings |
| `Semantics/Extension/Extension.lean:132-134` | both superseded sentences |
| `Metalogic/Algebraic/FlowFrame.lean:51, 349, 389` | "A world history is *total* — equivalently, a *possible world*" (3x) |
| `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean:386` | same |
| `typst/FormalFoundations.typ:247-249` | restates the old two-step layering |
| `typst/chapters/02-semantics.typ:175` | "A world history is *total* --- equivalently, a *possible world*" |

The `TaskFrame.HF` docstring's quote (`WorldHistory.lean:425-426`, "The set of all possible worlds
over $\F$ is denoted $H_{\F}$.") is the **one that is already current** -- keep it and build item
(c)'s rewrite around it.

### Finding 5 -- Prose sweep sizing and the dominant idiom

**181 occurrences of "world histor*" on 175 lines** in the live tree (excluding `Boneyard/`,
`specs/`, and generated build artifacts).

| Root | Lines | Notes |
|---|---|---|
| `FormalSystem/` | 94 | top files: `Semantics/WorldHistory.lean` 22, `Semantics/Extension/Extension.lean` 12, `Semantics/IntNormalForm.lean` 8, `Semantics.lean` 6, `Metalogic/Algebraic/FlowFrame.lean` 6, `Semantics/PartialHistory.lean` 5, `Semantics/Extension/README.md` 5 |
| `docs/` | 35 | `architecture/BFMCS_ARCHITECTURE.md` 11, `user-guide/architecture.md` 8, `reference/operators.md` 7, `user-guide/tutorial.md` 3, `reference/API_REFERENCE.md` 2, `development/LEAN_STYLE_GUIDE.md` 2, `theorem-index.md` 1, `development/DIRECTORY_README_STANDARD.md` 1 |
| `typst/` | 30 | `chapters/02-semantics.typ` 16, `chapters/00-introduction.typ` 9, `FormalFoundations.typ` 2, plus 3 singletons |
| `latex/` | 15 source (+2 in generated `build/*.aux`,`*.toc` -- **do not edit**) | `subfiles/02-Semantics.tex` 10, `subfiles/00-Introduction.tex` 3, `subfiles/06-Notes.tex` 1, `assets/bimodal-notation.sty:72` (a `% --- World History ---` section comment) |
| `Tests/` | 1 | `TruthTest.lean:35` comment |

**The dominant idiom is `total world histor*` -- 35 occurrences.** Every one of these means the
top tier and collapses to plain "possible world(s)"; the modifier is absorbed, not translated.
This is the single highest-leverage mechanical pattern in the sweep. Note the dispatch's count of
"5 in latex/" for the identifier includes 4 lines inside `latex/**/build/*.log` -- generated
artifacts. Real `latex/` identifier work is **one line**: `subfiles/04-Metalogic.tex:54`.

**Substantive editorial errors uncovered (fix while passing through, they are not merely
terminological):**

- `FormalSystem/Semantics/README.md:39` -- "`PartialHistory.lean` | Partial world-histories **on
  convex subsets** of the duration group". Doubly wrong: partial histories are precisely the tier
  *without* a convexity requirement.
- `FormalSystem/Semantics/README.md:49` -- "`WorldHistory`: **Infinite sequence** of worlds indexed
  by time". Wrong: a convex history may be bounded (that is the whole point of the chess example).
- `FormalSystem/Semantics/Extension/README.md:1,3` -- "partial **world** histories" / "Every
  partial **world** history extends to a total one". Under the new vocabulary "partial world
  history" is a category error; it should read "partial histories".
- `docs/theorem-index.md:34` -- the glossary row `| world history / possible world |
  FormalSystem.Semantics.WorldHistory | def:world-history; a total history is a possible world |`
  is the false friend written down explicitly. Split into two rows, mirroring the fix the dispatch
  already prescribes for `FormalSystem/Semantics.lean:185`.
- `latex/subfiles/04-Metalogic.tex:54` cites `FormalSystem/Semantics/WorldHistory.lean:246` for
  `timeShift`; `timeShift` is actually at line 304. Pre-existing line-number drift that the rename
  touches anyway.
- `docs/development/DIRECTORY_README_STANDARD.md:411` shows `h : WorldHistory W S T` -- a stale
  three-parameter signature (current: `WorldHistory (F : TaskFrame)`).

Confirmed: **`FormalSystem/Semantics.lean` names the module at lines 21, 52, 104, 107, 167, 185,
234, 242** -- the dispatch's list plus lines 52 and 104, which it omits.

### Finding 6 -- Gate coupling and rebuild blast radius

| Gate | Baseline today | Coupling to this task |
|---|---|---|
| `scripts/check-module-invariants.sh` | `ALL CHECKS PASSED`, exit 0 (C19 refined docstring coverage 92.33% vs 90% floor; C9D 142 doc task-citations, not yet enforced) | **No file/manifest reference to `WorldHistory`.** Watch C19: this task deletes and rewrites docstring prose in bulk; the refined floor has only 2.33 points of headroom. Do not shorten docstrings net-net. |
| `scripts/typst-sync-check.sh` | prints `FAIL` with `TOTAL_VIOLATIONS=4` but **exits 0**; all 4 are pre-existing and in `chapters/p4-proof-automation.typ` | **Directly coupled.** Check 1 resolves backticked `Path.lean` names against the live Lean tree. `typst/chapters/02-semantics.typ` backticks `Semantics/WorldHistory.lean` at lines 262 and 341, and `WorldHistory` / `WorldHistory.IsTotal` at 262 and 285. Renaming the file without updating those adds **new** violations. Updating typst is mandatory, not optional. |
| `scripts/readme-lint.sh` | `RESULT: PASS`; already reports 2 pre-existing `STALE DATE` READMEs (`Semantics/Correspondence`, `Semantics/Extension`) | Non-blocking, but renaming a file inside `FormalSystem/Semantics/` moves the directory mtime -- re-stamp `FormalSystem/Semantics/README.md` (and `Semantics/Extension/README.md`, which this task edits anyway). "Broken file references: 0" today; `Semantics/README.md:23` names `WorldHistory.lean` and must be updated in the same commit as the rename. |
| `lake build FormalSystem` | not re-run in this dispatch (see Decisions); HEAD is `08eddacb "task 550: complete implementation"`, a clean terminus | Baseline live `sorry` count (excl. `Boneyard/`): **348**. The gate is "no *new* sorry", not zero. |

**Rebuild blast radius (the dominant cost).** Computed over the live import graph
(479 live `FormalSystem` modules):

- modules transitively importing `FormalSystem.Semantics.WorldHistory`: **241**
- modules transitively importing `FormalSystem.Semantics.PartialHistory`: **247**

Per `.claude/context/project/lean4/operations/long-builds.md`, Lean hashes whole files, so a
**docstring-only** edit to either module invalidates the `.olean` of all ~250 dependents. This
task edits *both*. Any per-file build cadence pays ~250 modules repeatedly. Batch all Lean edits,
build **once**, detached and guarded:

```bash
bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build FormalSystem
```

run under `Bash(run_in_background: true)`, and do not write final metadata before the completion
notification arrives.

### External Resources

No Mathlib search was required and none was performed -- see Decisions. Relevant Mathlib context
checked only for collision: `ConvexHistory` collides with nothing (Mathlib has `Convex`, not
`ConvexHistory`), and the new namespace is `FormalSystem.Semantics.ConvexHistory`.

### Recommendations

**A sorry-free path exists and is not in doubt**: this task changes no proof term. If any proof
term needs to change, that is a stop-and-report signal per the dispatch, not something to adapt
around.

Recommended phase decomposition, each sized to one agent run:

1. **Record-file prose** (`specs/paper-definitions-of-record.md`): 3 headings + 1 layering
   paragraph. No hash, no sentinel, no archival drift-log edits. Cheap, independent, commit first
   -- this also discharges the file-serialisation dependency cleanly.
2. **Lean identifier + file rename**: `git mv FormalSystem/Semantics/WorldHistory.lean
   FormalSystem/Semantics/ConvexHistory.lean`; `s/WorldHistory/ConvexHistory/g` over the 71 live
   `.lean` files + 2 `Tests/` files; separate `s/worldHistory_ext/convexHistory_ext/g`; fix the 7
   import lines and `FormalSystem/Semantics.lean`'s 8 mention-lines. Do **not** build yet.
3. **Lean prose + re-quote**: rewrite the `PartialHistory.lean` and `ConvexHistory.lean` module
   docstrings by copying the verbatim block in Finding 1 (do not adjust in place); rewrite item
   (c)'s `TaskFrame.HF` docstring; fix the 8 stale-verbatim sites in Finding 4; split
   `Semantics.lean:185` into two table rows; apply the "total world history" -> "possible world"
   collapse across the remaining ~94 `FormalSystem/` prose lines; fix the four substantive README
   errors in Finding 5.
4. **docs / typst / latex prose**: 35 + 30 + 15 lines. Must include
   `typst/chapters/02-semantics.typ` lines 262, 285, 341 (typst-sync-check coupling) and the
   `docs/theorem-index.md:34` row split. Skip `latex/**/build/*` entirely.
5. **Single verify phase**: one guarded background `lake build FormalSystem`; then
   `check-module-invariants.sh`, `typst-sync-check.sh` (expect `TOTAL_VIOLATIONS=4`, unchanged),
   `readme-lint.sh`, the 43-anchor `--resolve` loop from Finding 3, the live-tree
   `WorldHistory`-absent grep, and a `sorry` count of 348.

Because phases 2-4 all invalidate the same ~250 modules, phases 2, 3 and 4 should be committed
without an intervening build and verified together in phase 5. This is the one place where the
usual commit-per-green-substep cadence must be reconciled with a ~250-module rebuild cost; declare
the Lean phases a batch and put the single green gate at phase 5.

## Decisions

- **No Mathlib/LeanSearch/Loogle/state_search queries were run, and none should be.** The task
  introduces no new mathematics and seeks no lemma. `lean_local_search` would only re-derive the
  identifier census that `grep` gives exactly and cheaply. Spending rate-limited search budget here
  would be pure waste. Recorded so the absence of a "Tactic Survey Results" table is understood as
  a decision, not an omission.
- **No `lake build` was run during this research dispatch.** A build here would cost a full
  ~250-module elaboration and answer only "was HEAD green", which HEAD's own
  `task 550: complete implementation` commit already asserts. The baseline that *is* needed
  (`sorry` = 348, gate outputs) was obtained without building. The implementation phase must run
  the build; research need not.
- **`--resolve`-loop verification replaces `check-paper-definitions.sh` bare invocation** as this
  task's paper gate, because the bare invocation is currently a no-op (Finding 3).
- **The dispatch's `def:world-history` line reference (577-593) and its "15 drifted / 9
  unresolved" figure are stale and were not followed**; the live record was re-measured instead.
- **`latex/**/build/*` and `latex/build/*` are excluded** from the prose sweep as generated
  artifacts, reducing the dispatch's latex counts (5 identifier / 17 prose) to 1 / 15.

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| The paper's own body prose (lines 1014-1052) still says "world history" for the *total* tier, so a future reader may "correct" the repo back | Record the split explicitly in the `ConvexHistory.lean` module docstring: cite `def:world-history` (appendix, settled) as authoritative and note line 1049's own collapse sentence. Do not reintroduce a reconciliation footnote -- the dispatch is right that the paper's footnote was removed. |
| Renaming the file breaks `typst-sync-check.sh` Check 1 silently (it exits 0 even on FAIL) | Compare `TOTAL_VIOLATIONS` numerically against the baseline **4**, not the exit code. Any value > 4 is a regression. |
| C19 docstring-coverage floor (92.33% vs 90%) erodes during a bulk docstring rewrite | Rewrites must be replacements, not deletions. Re-run `check-module-invariants.sh` in phase 5 and compare the C19 refined percentage to 92.33%. |
| ~250-module rebuild repeated per phase turns a 1-hour task into a multi-hour one | Batch phases 2-4; single guarded, detached build in phase 5. Never run a foreground `lake build`. |
| A naive global `s/WorldHistory/ConvexHistory/` also rewrites `Boneyard/` and `specs/` | Restrict the sed target list explicitly: `git ls-files 'FormalSystem/**/*.lean' 'Tests/**/*.lean' | grep -v '/Boneyard/'`. `specs/` carries ~2505 archival occurrences that must survive untouched. |
| "world history" -> mechanical substitution produces "convex history" where "possible world" is meant | Handle the 35 `total world histor*` sites **first**, as their own pass (they always become "possible world"), before any bare-phrase substitution. The residue is then overwhelmingly the convex tier. |
| Editing the record file concurrently with the sibling paper-anchor task | Finding 2 shows the sibling's work already landed; the dependency may be dropped and this task run standalone, exactly as the dispatch's DEPENDENCY NOTE permits. |

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task changes no proof term; see Decisions for
  why no Mathlib or tactic search was run.

## Context Extension Recommendations

- **Topic**: Gate scripts whose exit code does not reflect their own reported failure.
- **Gap**: `scripts/check-paper-definitions.sh` returns a silent `exit 0` whenever the whole-file
  checksum matches, bypassing all 43 anchor checks; `scripts/typst-sync-check.sh` prints
  `typst-sync-check.sh: FAIL` with `TOTAL_VIOLATIONS=4` and still exits 0. Both are easy for an
  agent to read as "green". No context file records this class of trap.
- **Recommendation**: add `context/project/lean4/operations/gate-exit-code-traps.md` (or extend
  the existing verification-standards file) documenting, per repo gate, what its exit code
  actually means and which numeric field must be compared to a recorded baseline instead.

- **Topic**: Docstring-only edits at the base of the import graph.
- **Gap**: `long-builds.md` states that whole-file hashing makes a docstring edit
  cache-invalidating, but no context file gives agents the reverse-dependency counts needed to
  *plan* around it.
- **Recommendation**: record the measured blast radius for this repo's hot base modules
  (`Semantics/PartialHistory.lean` -> 247 dependents, `Semantics/ConvexHistory.lean` -> 241 of 479
  live modules) in the lean4 operations context, with the batch-then-build-once prescription.

## Appendix

**Paper probes**
- `grep -n 'def:world-history' possible_worlds.tex` -> 8 `\ref` sites + the definition at 2880
- `sed -n '2880,2886p'` -> the verbatim block quoted in Finding 1
- `grep -n 'world histor' possible_worlds.tex` -> 8 lines, all in 1020-1048
- `grep -c 'convex histor' possible_worlds.tex` -> 32
- `sed -n '1014,1052p'` -> the body layering block, including the line-1049 collapse sentence and
  the two commented-out lines (1051-1052)
- `sha256sum possible_worlds.tex` -> `1b3c33a2...`, equal to the record's `FILE_CHECKSUM`

**Record probes**
- 43-anchor `--resolve` loop -> `ok=43 drifted=0 unresolved=0`
- `grep -n 'PAPER_PATH:\|PINNED_COMMIT:\|FILE_CHECKSUM:' specs/paper-definitions-of-record.md`
- `sed -n '714,760p'` -> the three entries, all already current
- `sed -n '1613,1625p'` -> "How to extend this record", 4-step procedure

**Codebase probes**
- `grep -rn 'WorldHistory' --include='*.lean' FormalSystem Tests | grep -v '/Boneyard/' | wc -l` -> 583
- `grep -rn 'extends.*WorldHistory'` -> none
- `grep -rn 'ConvexHistory' --exclude-dir=.git .` -> 10, all under `specs/`
- reverse-import closure script (479 live modules; 241 / 247 dependents)
- `grep -rin 'world histor' ... | wc -l` -> 175 lines / 181 occurrences

**Gate baselines**
- `check-module-invariants.sh` -> `ALL CHECKS PASSED`, C19 refined 92.33%
- `typst-sync-check.sh` -> `TOTAL_VIOLATIONS=4`, `MISMATCH_COUNT=0`, `MA_COUNT_MISMATCHES=0`
- `readme-lint.sh` -> `RESULT: PASS`, broken refs 0, 2 stale dates
- live `sorry` count -> 348

**References**
- `.claude/context/project/lean4/operations/long-builds.md` -- detach + guard, canonical invocation
- `specs/decisions/total-history-validity-decisions.md` -- Decisions A (HF subtype vs `IsTotal`
  predicate) and B (`extends` layering); both remain correct under the rename and are cited by the
  docstrings being rewritten
- `specs/TODO.md:157` -- the sibling collapse-question task this rename deliberately does not
  pre-empt
