# Implementation Plan: Task #548

- **Task**: 548 - Re-pin the paper anchors changed by the paper's z/d/r refactor and its removal of the Past/Future fragment
- **Status**: [IMPLEMENTING]
- **Effort**: 5.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/548_repin_renamed_paper_anchors_bx_z_d_r/reports/01_repin-bx-z-d-r-anchors.md
- **Artifacts**: plans/01_repin-bx-z-d-r-anchors.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

The paper renamed `def:TMplus-f/-d/-c` to `def:BX-z/-d/-r`, folded the `BL^+` fragment cluster
away, and edited fifteen other pinned anchors. `specs/paper-definitions-of-record.md` still pins
the three retired names, so it asserts three things about the paper that are no longer true. This
plan absorbs the whole drift wave into the record (retire nine dangling pins, add three new ones,
re-hash fifteen drifted entries, re-pin the file sentinels), then re-labels the thirty-two in-tree
citation sites and corrects the prose that the paper's Hölder/`prop:archimedean` restructuring
made inaccurate. Done means `scripts/check-paper-definitions.sh` exits 0 with the quiet case-(a)
pass, C15 remains green, and `lake build` is clean.

### Research Integration

The research report reframes the task in three load-bearing ways, and this plan is built on that
reframing rather than on the dispatch description's premises:

- **The acceptance gate is `check-paper-definitions.sh`, not C15.** C15 is measured green today
  (53/53 citations resolve) and is structurally incapable of detecting this defect: it checks
  anchor *names* against the record, never hashes against the paper, so a stale manifest row keeps
  a renamed anchor resolving indefinitely. `check-paper-definitions.sh` is the gate that is
  actually red (exit 1; 15 drifted, 9 dangling). C15 is therefore a *regression guard* in this
  plan (Phase 4 is what could break it), never the completion criterion.
- **The drift wave is 4-5x the named scope and must be absorbed as one unit.** Six dangling
  anchors beyond the three renamed ones (`def:directed`, `def:BLplus-semantics`,
  `def:BLplus-defined`, `thm:BLplus-PastFuture`, `thm:BLplus-NextPrevious`, `TMP-CO`) belong to
  the same paper wave; the record's own step 4 ("confirm the quiet case-(a) pass") cannot succeed
  while any of them stay pinned.
- **Ordering is load-bearing.** Re-labelling docstrings before the new manifest rows exist turns
  C15 red mid-implementation. Record first, tree second — Phases 1-3 strictly precede Phase 4.

Three dispatch-description premises the research measured as false, and which this plan
deliberately does **not** implement (they are recorded as corrections in Phase 3's narrative
section instead): the Z1 footnote is commented out in the paper, not live; `thm:TM-soundness`
needs no re-hash (every change named lives in the `\begin{proof}` block outside the hashed
environment); and `def:BX-r`'s second axiom is `SEP`, not `SP`. `prop:fragment` and `rmk:fragment`
require no action at all — nothing pins or cites them.

The report's measured hashes (15 drifted + 3 new) are usable verbatim by the implementer, but
every one is re-derived via `--resolve` at implementation time rather than trusted — the paper
file is dirty and may have moved since the measurement.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch. A read-only check of `specs/ROADMAP.md` found no
item this task advances (its "anchor" occurrences are the unrelated `boxAnchoredCheck`
decidable-branch-gate family). No roadmap phases are added.

## Goals & Non-Goals

**Goals**:
- `scripts/check-paper-definitions.sh` exits 0 with the quiet case-(a) pass.
- The record pins `def:BX-z`, `def:BX-d`, `def:BX-r` with verbatim text and re-derived hashes, and
  retires every anchor the paper no longer defines, per the record's `DANGLING` convention.
- Every in-tree citation of `def:TMplus-f/-d/-c` names the new anchor instead.
- Prose that the paper's restructuring made inaccurate (the Hölder narrowing, the TM⁺/BL⁺ system
  naming at the four bare `def:TMplus` sites) is corrected, not merely re-labelled.
- C15 stays green and `lake build` stays clean throughout.

**Non-Goals**:
- No Lean proof terms, no new declarations, no `sorry` discharge. This task edits Markdown,
  docstrings, and comments only.
- No promotion of `def:derivability` / `def:soundness` to the manifest (Phase 3 corrects their
  exclusion bullet instead; the "proof-theoretic, not semantic" rationale still holds).
- No rows for `prop:fragment` / `rmk:fragment` — nothing pins or cites them, and the record's
  "adding a row here is a decision, not a formality" instruction forbids speculative rows.
- No action on `lem:temporal-duality` / `thm:TD-valid` beyond a narrative note (0 in-tree hits, no
  manifest rows).
- The three unrelated `LIVE-UNPINNED` anchors (`app:drift`, `cor:no-characterization`,
  `lem:deterministic-singleton`) are already absorbed and are out of scope.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Ordering inversion: tree re-labelled before manifest rows exist, turning C15 red | H | M | Phase 4's entry gate is a grep for `def:BX-z\|env` in the MANIFEST block; Phases 1-3 strictly precede it |
| Partial absorption leaves `check-paper-definitions.sh` permanently red | H | M | Phase 2 absorbs the whole wave, not just the named three; Phase 3's exit criterion is exit 0 |
| Hashes measured during research are stale (paper file is dirty, may have changed) | M | M | Every hash is re-derived via `--resolve` in-phase; report hashes are cross-checks, not inputs |
| `check-module-invariants.sh` exceeds 15 minutes and blocks the session | M | H | Phase 6 backgrounds it and waits with a single blocking `tail --pid=<pid> -f /dev/null`; never busy-poll |
| Docstring edit breaks Lean syntax (unbalanced `-/`) | M | L | Phases 4-5 carry tier `local`: build each touched module; Phase 6 re-confirms with a full `lake build` |
| Rewritten prose cites `prop:archimedean` without a KNOWN-ANCHORS row, turning C15 red | M | M | Phase 5 adds the `LIVE-UNPINNED` row in the same change as the citation, and re-runs the standalone C15 reproduction before closing |
| Dirty-source pin: `PINNED_COMMIT` will not reproduce `FILE_CHECKSUM` | L | H | Phase 3 extends the record's existing "Dirty-pin caveat" section with this wave's date rather than pretending the pin is clean |
| Implementing a false dispatch premise (Z1 footnote, `thm:TM-soundness` re-hash, `SP`) | M | M | Each is named as an explicit Non-Goal and recorded as a correction in Phase 3's narrative |

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

Phases within the same wave can execute in parallel. This plan's chain is strictly linear: the
record must be correct before the tree is re-labelled, and the sentinel re-pin must follow the
forcing run that validates it.

---

### Phase 1: Retire dangling pins and pin `def:BX-z/-d/-r` [COMPLETED]

**Goal**: The record stops asserting anchors the paper no longer defines, and starts pinning the
three renamed ones with verbatim text and re-derived hashes.

**Tasks**:
- [x] Run `bash scripts/check-paper-definitions.sh` with **no tail-truncation** and capture the
      full drift + dangling report to a scratch file. Confirm the dangling set against the
      report's list of nine.
- [x] For each of the nine dangling anchors, remove its MANIFEST row, **retain** its prose entry,
      and mark that entry `DANGLING` per the record's established convention (see the existing
      `lem:fibers` / `thm:occurrence` entries for the exact shape).
- [x] Add a `DANGLING` row to the KNOWN-ANCHORS block for each of the nine, with a note naming
      what replaced it (`def:TMplus-f` → renamed `def:BX-z`; `def:directed` → folded into
      `def:frame`'s opening clause; the `BL^+` cluster → collapsed into `BL`; `TMP-CO` →
      superseded by the plain `\aitem{CO}`).
- [x] Re-derive the three new hashes:
      `bash scripts/check-paper-definitions.sh --resolve 'def:BX-z|env|-|-'` and likewise for
      `def:BX-d`, `def:BX-r`. Cross-check against the report's `385f73e8…` / `555db844…` /
      `b35751c7…`; if any differs, use the freshly resolved value and note the divergence.
- [x] Add three `### \`def:BX-z\`` / `-d` / `-r` prose entries quoting the resolved text verbatim,
      placed in paper order near the existing `def:TMplus` entry.
- [x] Add the three MANIFEST rows with the re-derived hashes. Use `SEP` (not `SP`) wherever the
      new prose names `def:BX-r`'s second axiom.
- [x] Commit.

**Timing**: 1.0 hours

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: The report asserts **9 dangling pinned anchors** (`def:directed`,
`def:BLplus-semantics`, `def:BLplus-defined`, `thm:BLplus-PastFuture`, `thm:BLplus-NextPrevious`,
`TMP-CO`, `def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c`). Confirm by reading the untruncated
dangling section of the `check-paper-definitions.sh` run at the top of this phase; if the live
count differs, absorb the live set and record the divergence rather than the report's list.

**Files to modify**:
- `specs/paper-definitions-of-record.md` - retire 9 manifest rows, mark 9 prose entries
  `DANGLING`, add 9 KNOWN-ANCHORS rows, add 3 prose entries and 3 manifest rows

**Verification**:
- `grep -c 'def:TMplus-[fdc]|env' specs/paper-definitions-of-record.md` inside the MANIFEST block
  returns 0.
- `grep 'def:BX-z|env' specs/paper-definitions-of-record.md` returns exactly one manifest row, and
  likewise for `-d` and `-r`.
- Re-running `check-paper-definitions.sh` no longer reports any dangling anchor (drifted entries
  are still expected red — Phase 2 handles those).

---

### Phase 2: Absorb the drifted-entry wave [NOT STARTED]

**Goal**: Every pinned entry whose paper text changed is re-quoted and re-hashed, so the only
remaining failure is the stale file-level sentinel.

**Tasks**:
- [ ] For each drifted anchor, run `check-paper-definitions.sh --resolve` to obtain live text plus
      sha256. Rewrite the entry's latex fence **and** its sha line, plus the matching MANIFEST row.
      Do not hand-edit a hash without a `--resolve` run behind it.
- [ ] Give particular attention to the two entries that are not mere re-quotes:
      `cor:saturation-finite` changed environment (`Cthm` → `Lthm`, so the row's `kind`/enclosing
      metadata must be re-checked, not only its hash), and `def:frame` absorbed the `⊇`-directed
      definition inline while softening "strictly stronger" to "at least as strong as" (so the
      prose entry's surrounding commentary must be re-read for accuracy, not only the fence).
- [ ] Re-run `bash scripts/check-paper-definitions.sh` **with the old `FILE_CHECKSUM` sentinel
      still in place**. This forces full anchor validation; expect the case-(b) notice pass. Do
      not touch the sentinels in this phase.
- [ ] Commit.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: The report asserts **15 drifted entries** (`def:frame`, `def:world-history`,
`thm:extension`, `cor:occurrence`, `def:BL-semantics`, `def:BLplus-language`, `def:S5`, `def:BX`,
`def:TMplus`, `app:discrete`, `app:dense`, `app:complete`, `def:frame-properties`,
`cor:saturation-finite`, `cor:tm-completeness`) with the hashes listed in the report's Finding 2.
Confirm by re-running the checker at the start of this phase and diffing the live drifted set
against that list; re-derive every hash via `--resolve` rather than copying the report's, and
treat any mismatch as evidence the paper moved since the research run.

**Files to modify**:
- `specs/paper-definitions-of-record.md` - re-quote + re-hash each drifted entry and its manifest
  row

**Verification**:
- `check-paper-definitions.sh` reports zero drifted entries and zero dangling anchors, exiting on
  the case-(b) notice path (the stale `FILE_CHECKSUM` is the only remaining complaint).

---

### Phase 3: Re-pin sentinels and record the wave narrative [NOT STARTED]

**Goal**: The record's file-level pin matches the live paper, and the wave — including the three
corrected dispatch premises — is documented for the next reader.

**Tasks**:
- [ ] Compute the live paper's sha256 and its repo commit; update `FILE_CHECKSUM`, `PINNED_COMMIT`
      and `LINE_COUNT` in the record header to the freshly measured values (the report measured
      `93fd9b14…` at commit `f61bbd75`; re-measure rather than copy).
- [ ] Add a dated `### Drift correction and rename absorption (2026-09-07)` narrative section,
      following the shape of the existing 2026-09-02 and 2026-08-25 sections: what the paper did,
      what was retired, what was newly pinned, what was re-hashed.
- [ ] Record the three corrections in that section so a future reader does not re-derive them:
      the Z1 footnote is **commented out** in the paper (author note at paper line 1334) and is
      not recorded as live; `thm:TM-soundness` needed no re-hash because the changed text lives in
      the `\begin{proof}` block outside the hashed environment; `def:BX-r`'s second axiom is
      `SEP`, not `SP`. Add a one-line note that `lem:temporal-duality` / `thm:TD-valid` have no
      repository-side consequence (0 in-tree hits, no manifest rows), and that `prop:archimedean`
      is a pen-and-paper `Pthm` this repository does not check — recorded as such, not pinned as
      verified.
- [ ] Update the "Deliberately not covered" bullet for `def:derivability` / `def:soundness`: they
      are now stated for **TM** and the full language `BL` (paper lines 4016, 4020); the exclusion
      stands, its justification is refreshed.
- [ ] Extend the existing `### Dirty-pin caveat` section with this wave's date, since the pinned
      source file is again uncommitted in its own repository.
- [ ] Re-run `bash scripts/check-paper-definitions.sh` and confirm the **quiet case-(a) pass**
      (exit 0, no output). This is the task's acceptance gate.
- [ ] Commit.

**Timing**: 0.5 hours

**Depends on**: 2

**Verification Tier**: prose

**Files to modify**:
- `specs/paper-definitions-of-record.md` - header sentinels, new narrative section, exclusion
  bullet, dirty-pin caveat

**Verification**:
- `bash scripts/check-paper-definitions.sh; echo $?` prints `0` with no other output.
- The header `FILE_CHECKSUM` equals `sha256sum` of the live paper file.

---

### Phase 4: Re-label the in-tree citation sites [NOT STARTED]

**Goal**: No file outside `specs/` cites `def:TMplus-f`, `def:TMplus-d`, or `def:TMplus-c`.

**Entry gate**: `grep 'def:BX-z|env' specs/paper-definitions-of-record.md` inside the MANIFEST
block returns a row. Do not begin this phase otherwise — re-labelling before the row exists turns
C15 red.

**Tasks**:
- [ ] Re-take the citation census (`grep -rn` for each of the three old labels over
      `FormalSystem Tests typst docs README.md`, excluding `Boneyard`) and diff it against the
      report's inventory before editing anything.
- [ ] Replace `def:TMplus-f` → `def:BX-z`, `def:TMplus-d` → `def:BX-d`, `def:TMplus-c` →
      `def:BX-r` at every site. Use a bounded pattern that cannot also match bare `def:TMplus`.
- [ ] Update `FormalSystem/Metalogic/Conservativity.lean:32-34`, whose prose explicitly defers
      this rename ("the record's re-pin is separate work") — that sentence becomes stale the
      moment this phase lands and must be rewritten, not merely re-labelled.
- [ ] Build each touched Lean module (`lake build FormalSystem.<Module>`) to confirm no docstring
      was broken.
- [ ] Re-run the standalone C15 reproduction (seconds, see Phase 6) and confirm it is still green.
- [ ] Commit.

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: The report asserts **32 occurrences across 17 files** — 19 of
`def:TMplus-f`, 2 of `def:TMplus-d`, 11 of `def:TMplus-c` — with `FrameProperty.lean` (6) and
`Conservativity.lean` (3+1+1) the densest sites. Confirm with the re-taken census at the top of
this phase; treat any file the report did not name as a genuine addition to scope, not a mistake,
and record the corrected count in the phase's commit message.

**Files to modify**:
- `FormalSystem/Semantics/FrameProperty.lean`, `FormalSystem/Metalogic/Conservativity.lean`,
  `FormalSystem/Semantics/FrameClassValidity.lean`, `FormalSystem/Semantics.lean`,
  `FormalSystem/Semantics/Validity.lean`, `FormalSystem/Semantics/BLValidity.lean`,
  `FormalSystem/Semantics/Correspondence/Indicator.lean`,
  `FormalSystem/Semantics/Correspondence/README.md`,
  `FormalSystem/Metalogic/Independence/LexIntWitness.lean`,
  `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean`,
  `FormalSystem/ProofSystem/Axioms.lean`, `FormalSystem/Theorems/DedekindDerived.lean`,
  `FormalSystem/Syntax/Formula.lean`, `FormalSystem/Metalogic/SoundnessLemmas/CoValidity.lean`,
  `FormalSystem/README.md`, `README.md`, `docs/theorem-index.md` - label substitution

**Verification**:
- `grep -rn 'def:TMplus-[fdc]' --exclude-dir=Boneyard --exclude-dir=specs .` returns nothing
  outside `specs/`.
- Each touched Lean module builds.
- The standalone C15 reproduction reports no unresolved anchor.

---

### Phase 5: Correct the prose the paper's restructuring invalidated [NOT STARTED]

**Goal**: The tree's claims about *why* the ℤ-time narrowing holds, and about the system names
`TM` / `BL`, match the current paper rather than the pre-refactor one.

**Tasks**:
- [ ] At the six sites phrasing the narrowing as "`def:TMplus-f`'s Hölder narrowing", rewrite to
      attribute the narrowing to `def:BX-z` and cite `prop:archimedean` (paper line 3265, a live
      `Pthm`) for the failure over non-Archimedean discrete orders — the paper now defers the
      Hölder step to the §Extensions footnote (paper lines 1408-1411). Keep the parenthetical
      explaining where the predicate's name comes from; it remains accurate.
- [ ] Re-read `FrameClassValidity.lean:94-98` and `FrameProperty.lean:131-137`. The dispatch
      description says one of them quotes the old closing sentence verbatim; the research measured
      both as paraphrases ("restated here in the tree's own voice rather than quoted"). Confirm
      which is true at implementation time; if a verbatim quotation exists, refresh it against the
      new `def:BX-z` text, and if not, correct only the attribution.
- [ ] If any rewritten prose names `prop:archimedean`, add a
      `prop:archimedean|LIVE-UNPINNED|…` row to the record's KNOWN-ANCHORS block **in the same
      change** — otherwise C15 goes red. Do not add the row speculatively if no site cites it.
- [ ] At the four bare `def:TMplus` sites (`Conservativity.lean`, `Conservativity/Fragment.lean`,
      `typst/chapters/03-proof-theory.typ`, `docs/theorem-index.md`), review the prose for the
      TM⁺/BL⁺ → TM/BL and f/d/c → z/d/r shifts. The label is unchanged; only the surrounding
      claims may be stale.
- [ ] Build each touched Lean module; re-run the standalone C15 reproduction.
- [ ] Commit.

**Timing**: 1.0 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: The report asserts **6 Hölder-attribution sites** and **4 bare
`def:TMplus` sites**. Confirm with `grep -rn -i 'holder\|hölder'` and
`grep -rnP 'def:TMplus(?![-A-Za-z0-9_])'` over live scope before editing — note that a plain `\b`
boundary matches `-` and over-counts the bare form by roughly 15.

**Files to modify**:
- `FormalSystem/Semantics/FrameProperty.lean`, `FormalSystem/Semantics/FrameClassValidity.lean`,
  `FormalSystem/Metalogic/Conservativity.lean`,
  `FormalSystem/Metalogic/Conservativity/Fragment.lean`,
  `typst/chapters/03-proof-theory.typ`, `docs/theorem-index.md` - prose corrections
- `specs/paper-definitions-of-record.md` - conditional `prop:archimedean` KNOWN-ANCHORS row

**Verification**:
- No live site attributes the Hölder narrowing to a `def:TMplus-*` anchor.
- If `prop:archimedean` is cited anywhere in live scope, it has a KNOWN-ANCHORS row.
- The standalone C15 reproduction reports no unresolved anchor.

---

### Phase 6: Full-gate verification [NOT STARTED]

**Goal**: Every gate this task touches is confirmed green end to end, with the expensive one run
exactly once.

**Tasks**:
- [ ] Standalone C15 reproduction (~1 second): extract the MANIFEST and KNOWN-ANCHORS blocks by
      their HTML-comment sentinels, `cut -d'|' -f1`, strip comments, `sort -u`; sweep citations
      with `grep -rhoE '\b(def|thm|lem|cor|app|rmk):[A-Za-z0-9][A-Za-z0-9_-]*'` over
      `FormalSystem Tests typst docs README.md` (excluding `Boneyard`); `comm -23`. Expect empty.
- [ ] `bash scripts/check-paper-definitions.sh; echo $?` — expect `0` and no output.
- [ ] `lake build`, backgrounded, to confirm no docstring syntax breakage anywhere.
- [ ] `bash scripts/check-module-invariants.sh`, backgrounded, budgeting **>15 minutes**. Wait
      with a single blocking `tail --pid=<pid> -f /dev/null`; never busy-poll. Confirm both C15
      lines pass (citation resolution and theorem-index anchor coverage).
- [ ] Confirm the three unrelated `LIVE-UNPINNED` anchors (`app:drift`, `cor:no-characterization`,
      `lem:deterministic-singleton`) are untouched by this task's diff.
- [ ] Commit.

**Timing**: 0.75 hours (mostly wall-clock wait)

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- None (verification only; any failure routes back to the owning phase)

**Verification**:
- `check-paper-definitions.sh` exit 0, quiet.
- `lake build` clean.
- `check-module-invariants.sh` reports both C15 lines PASS.

---

## Lean Challenge Statements

None. This plan introduces no Lean declarations and proves no theorems — its `- **Goals**:`
bullets name zero Lean identifiers, so the identifier set this section would pin is empty. `lake
build` appears in Phases 4-6 solely to confirm docstring syntax integrity, never to close a goal.

## Testing & Validation

- [ ] `bash scripts/check-paper-definitions.sh` exits 0 with no output (quiet case-(a) pass).
- [ ] Standalone C15 reproduction reports no unresolved anchor.
- [ ] `bash scripts/check-module-invariants.sh` reports both C15 lines PASS.
- [ ] `lake build` completes clean.
- [ ] `grep -rn 'def:TMplus-[fdc]'` returns nothing outside `specs/`.
- [ ] The record's `FILE_CHECKSUM` equals `sha256sum` of the live paper file.
- [ ] No new `sorry` anywhere (trivially satisfied — no proof terms are written).

## Artifacts & Outputs

- `specs/paper-definitions-of-record.md` — 9 retired pins, 3 new pins, 15 re-hashed entries,
  re-pinned sentinels, a dated wave-narrative section, a refreshed exclusion bullet, an extended
  dirty-pin caveat, and (conditionally) a `prop:archimedean` KNOWN-ANCHORS row.
- 17 in-tree files with re-labelled anchor citations; a subset of those with corrected prose.
- `specs/548_repin_renamed_paper_anchors_bx_z_d_r/summaries/01_*-summary.md` at completion.

## Rollback/Contingency

Every phase ends in its own commit, so any phase can be reverted with `git revert` without
disturbing its predecessors. The two ordering-sensitive rollbacks:

- Reverting Phase 1 or 3 **after** Phase 4 has landed turns C15 red (the tree would cite anchors
  with no manifest row). Revert Phase 4 first, or not at all.
- If the paper moves mid-implementation and hashes stop reproducing, stop rather than force a pin:
  re-run `check-paper-definitions.sh` from a clean checkout of the record, re-derive from
  `--resolve`, and note the moving-target condition in the narrative section. A hash written
  without a `--resolve` run behind it is worse than a red gate.

If the wave proves larger than Phase 2's confirmed scope (the paper is dirty and actively edited),
absorb what is measured, mark Phase 2 `[PARTIAL]` with the residual enumerated, and do **not**
advance to Phase 3 — an incorrect `FILE_CHECKSUM` pin would mask the residual permanently.
