# C15 paper-anchor resolution — research

**Status**: researched
**Scope**: make `scripts/check-module-invariants.sh` report ALL CHECKS PASSED by resolving every
unresolved paper-anchor citation.

## Headline findings

1. **There are FOUR unresolved anchors, not three.** The task description names `app:drift`,
   `cor:no-characterization`, `lem:deterministic-singleton`. The measured C15 failure also lists
   **`app:ObjectiveModality`** (cited in `FormalSystem/BaseLanguage/Axioms.lean:100`), introduced
   by commit `d155835f2` ("Extend Axioms.lean paper-name correspondence table") *after* the task
   was written. Fixing only three anchors leaves C15 red.

2. **The classification supplied in the task description is STALE. All four anchors are LIVE and
   LABELLED in the current paper**, in both the working tree and the committed `HEAD`. The
   PossibleWorlds `repair_paper_lean_anchor_drift` work the task told us to coordinate with has
   already landed: the footnote it described has been promoted to two numbered, labelled results.

   Measured in `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`
   (working tree / `HEAD` line numbers):

   | Anchor | LaTeX | Working tree | `HEAD` |
   |---|---|---|---|
   | `app:ObjectiveModality` | `\subsection{Objective Modality}` + `\label{}` on next line | 1917 | 1898 |
   | `lem:deterministic-singleton` | `\begin{Lthm} \label{...}` | 3576 | 3557 |
   | `app:drift` | `\begin{Tthm} \label{...}` | 3705 | 3686 |
   | `cor:no-characterization` | `\begin{Cthm} \label{...}` | 3741 | 3722 |

   In particular the task's caution "(2) LIVE BUT UNLABELLED … it cannot be recorded against a
   label that does not exist" and "(3) … The citing docstring expects an APPENDIX SECTION, which
   the paper does not have" are both **no longer true**. No paper-side edit and no cross-repo
   coordination is needed. Nothing is DANGLING.

3. **All four are LIVE-UNPINNED, none should be pinned into the manifest.** Verified below.

4. **The correct fix is four rows in the record's `KNOWN-ANCHORS` block and nothing else.**
   A dry-run of C15's exact resolution pipeline against a patched copy of the record returns an
   **empty** unresolved set (52 cited anchors, all resolving). No Lean file needs editing, no
   docstring is dishonest, no hash or checksum sentinel is touched.

## Verification that each anchor is genuinely live

`app:drift` (Tthm 3705) states: *"There is a non-deterministic task frame over which
`φ → ⊡φ` is valid for every sentence `φ` of BL⁺ extended with ⊡ — equivalently, of BL⋆ without
the store and recall operators."* Its proof constructs `F°` (`W = ℝ`, `w ⇒_x u` iff
`x ≤ u − w ≤ 2x` for `x ≥ 0`), discharges all six frame axioms, runs the `S_φ` induction, and
closes with the store/recall counterexample.

`cor:no-characterization` (Cthm 3741) states: *"No set of sentences of BL⋆ without the store and
recall operators characterizes the Deterministic task frames."* Its proof introduces `F¹`
(`u = w + x`) and applies `app:drift`'s induction verbatim, citing `lem:deterministic-singleton`
for `⟨τ⟩_x = {τ}`.

`lem:deterministic-singleton` (Lthm 3576) states: *"F is Deterministic if and only if
`⟨τ⟩_x = {τ}` for all `τ ∈ H_F` and `x ∈ D`"*, with a footnote that only left-to-right is
choice-free and the converse goes through `thm:extension` and Zorn.

`app:ObjectiveModality` (1917) is the `\subsection{Objective Modality}` label of the
objective-modality appendix.

### The citing docstrings are all faithful — no correction needed

Spot-checked every claim the tree makes about these anchors against the live `.tex`:

- `DriftFrame.lean:42` "`app:drift` states the relation only for `x ≥ 0`" — paper says
  `$x \leq u - w \leq 2x$ for $x \geq 0$, extended to negative durations by def:task-relation`. ✓
- `DriftFrame.lean:59` "`app:drift` interpolates with `λ := (v − w)/(x + y)`" — paper's proof:
  `$\lambda \coloneq (v - w)/(x + y) \in [1,2]$`. ✓
- `DriftFrame.lean:63` "`app:drift` argues by the finite intersection property directly" — paper:
  "a family of compact sets with the finite intersection property has nonempty intersection". ✓
- `DriftFrame.lean` `fzero_not_deterministic` — paper: `$0 \Rightarrow_1 1$ and
  `$0 \Rightarrow_1 2$ where $1 \neq 2$`. ✓
- `DeterminismUndefinable.lean:167` "**`Deterministic` is not L⋆-definable**
  (`cor:no-characterization`)" — verbatim the corollary's content. ✓
- `StarDeterminism.lean:33` / `DeterminismUndefinable.lean:33` "the (⇒) half … is choice-free" —
  matches the Lthm's own footnote. ✓
- `Axioms.lean:100` `**Appendix: Objective Modality (\S app:ObjectiveModality)**` — the anchor
  really is a `\subsection` label, so `\S` is the right sigil. ✓

## Why LIVE-UNPINNED and not manifest pins

The record's own criterion (§"Known anchors outside the manifest"): pin only where a docstring
quotes the anchor's *text* verbatim; name-only pointers gain nothing from a pin and cost a
re-quote-and-re-hash on every paper wave.

- Three of the four are cited **by name only** across every site
  (`Independence/{DriftFrame,DriftHistories,RealTranslationFrame,StateSetTruth,OrderTransfer,DeterminismUndefinable}.lean`,
  `Independence.lean`, `Independence/README.md`, `Semantics/StarDeterminism.lean`).
- `DriftFrame.lean` *does* quote fragments (`x ≤ u − w ≤ 2x`, `λ := (v − w)/(x + y)`), but those
  live in the paper's `\begin{proof}` block. `resolve_env` in `scripts/check-paper-definitions.sh`
  captures `\begin{Env} … \end{Env}` only — the proof is outside it — so a pin on `app:drift`
  would hash the one-sentence statement the tree never quotes and would **not** protect the
  quoted material. Pinning buys nothing here.
- `app:ObjectiveModality` **cannot** be pinned at all: `resolve_env` requires `\begin{...}` on
  the same line as `\label{}`, and this is a `\subsection{...}%` with the label on the next line,
  so `env` resolution returns 1. This is exactly the existing `app:TaskSemantics|LIVE-UNPINNED|
  section label for the task-semantics appendix; cited as a pointer` precedent.
- `app:drift` is exactly parallel to the existing `app:deterministic|LIVE-UNPINNED|determinism
  CORRESPONDENCE theorem, not the definition` row — an `app:`-prefixed *theorem*, not a section.

## Recommended change (single file, four lines)

`specs/paper-definitions-of-record.md`, inside `<!-- KNOWN-ANCHORS:BEGIN/END -->`, keeping the
block's existing ASCII-sorted LIVE-UNPINNED-then-DANGLING ordering:

```
app:ObjectiveModality|LIVE-UNPINNED|subsection label for the objective-modality appendix; cited as a pointer from the Axioms.lean correspondence table
app:drift|LIVE-UNPINNED|the drift-frame theorem (a Tthm), not an appendix section; cited as a pointer, statement text never quoted
cor:no-characterization|LIVE-UNPINNED|non-definability corollary; cited as a pointer, text never quoted
lem:deterministic-singleton|LIVE-UNPINNED|the singleton bridge; cited as a pointer, text never quoted
```

Insertion points (ASCII order): `app:ObjectiveModality` **before** `app:TaskSemantics`;
`app:drift` **between** `app:deterministic` and `app:topology-r0`; `cor:no-characterization`
**before** `cor:perpetuity-valid`; `lem:deterministic-singleton` **before**
`lem:history-time-shift-preservation`.

Optionally add a dated line to the record's prose narrative recording the decision, matching how
earlier waves were logged.

**No other edit is required.** No `.lean` file changes; no `FILE_CHECKSUM` / `PINNED_COMMIT`
re-pin (those sentinels are consumed by `check-paper-definitions.sh` against the *paper*, and
`KNOWN-ANCHORS` rows are not parsed by that script at all).

## Verification performed (dry run)

Copied the record to scratch, applied the four rows, and re-ran C15's exact pipeline
(MANIFEST field-1 + KNOWN-ANCHORS field-1 as the known set; the same
`grep -rhoE '\b(def|thm|lem|cor|app|rmk):[A-Za-z0-9][A-Za-z0-9_-]*'` over
`FormalSystem Tests typst docs README.md` minus `Boneyard` as the cited set):

```
UNRESOLVED AFTER PATCH:
(end)
total cited: 52
```

Since C15 was the *only* failing group in the baseline run (`1 CHECK GROUP(S) FAILED`), this
change is sufficient for ALL CHECKS PASSED. Implementation must still re-run the real script.

## Re-measured: the `check-paper-definitions.sh` drift (OUT OF SCOPE)

The task asked for a re-measurement. Current state is **worse** than the 18-changed/6-dangling
figure quoted: **15 recorded definitions drifted and 9 recorded anchors dangling**:

`def:directed`, `def:BLplus-semantics`, `def:BLplus-defined`, `thm:BLplus-PastFuture`,
`thm:BLplus-NextPrevious`, `TMP-CO`, `def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c`.

This is **not** in this task's scope and must not be folded in:

- `check-paper-definitions.sh` is **not** invoked by `check-module-invariants.sh` and **not** run
  by CI (`.github/workflows/ci.yml` runs only `lean-action` build/test/lint). It cannot affect
  this task's ALL CHECKS PASSED acceptance.
- C15 resolves against the *record*, never the paper — by explicit design, documented in the
  script's own C15 header comment, precisely so the check cannot go red when the author edits the
  paper.
- Seven of the nine dangling anchors (`def:TMplus-{f,d,c}`, `def:BLplus-*`, `thm:BLplus-*`) are
  the declared scope of the open fragment-removal / BX-rename tasks. `def:directed` and `TMP-CO`
  are new drift from the paper's uncommitted `def:frame` edit (which folds the `⊇-directed`
  definition into `def:frame`, retiring `def:directed`'s own environment) and belong with that
  same wave.

Recommend the implementer records this as a Reasoned Exclusion with the above citation, exactly
as prior phases did.

## Tactic survey

Not applicable. This task contains no proof obligation: the deliverable is four lines of
Markdown in a specs file. No `lake build` is needed either — no `.lean` file is touched — though
running the invariant script is required for acceptance.

## Zero-debt note

The recommended approach completes the task fully with no `sorry`, no new axiom, and no deferral.
