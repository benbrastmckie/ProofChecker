# Implementation Plan: Replace historical system names in docstrings

- **Task**: 547 - Replace historical system names in docstrings
- **Status**: [IMPLEMENTING]
- **Effort**: 7 hours
- **Dependencies**: 546 (completed). Blocks 548 (anchor re-pinning).
- **Research Inputs**: `specs/547_replace_historical_system_names_in_docstrings/reports/01_historical-system-name-sweep.md`
- **Artifacts**: plans/01_replace-historical-system-names.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false (no Lean declaration, term, tactic, axiom or `sorry` is added or changed)

## Overview

Retire the historical extension names `TM⁺_f`, `TM⁺_c`, `TM⁺_dc`, `TM_f`, `TM_c`, `TM_dc`,
`BX_f`, `BX_c` from every live comment, docstring, README and doc page, replacing them with the
paper's current `z`/`d`/`r` subscripts, and record in one place how this repository's two base
systems (`TM⁺` over `BL`, `TM` over the Past/Future fragment) map onto the paper's. The sweep is
comment-and-docstring-only: no Lean identifier, no anchor label, and no entry in
`specs/paper-definitions-of-record.md` is touched. Definition of done is a scoped grep returning
no output, `lake build FormalSystem` green, and `scripts/check-module-invariants.sh` no worse than
the Phase 1 baseline.

The plan's central constraint, established by research, is that **this is not a token swap**.
Twelve passages assert things *about the paper* that the `z`/`d`/`r` revision has retracted or
resolved: verbatim quotations of sentences the paper has deleted, a "real gap" argument the paper
has closed, an "open question" the paper has answered, and a `TM⁺_c`-vs-`TM⁺_dc` contrast that
collapses to a single name (a naive `sed` there yields the nonsense "this is TM⁺_r, not TM⁺_r").
Those passages are rewritten by hand, in separate phases from the mechanical rename, with the
files partitioned so that no two phases own the same file.

### Research Integration

Findings from `reports/01_historical-system-name-sweep.md` that shape this plan:

- **Census (re-verified while planning)**: 59 matching lines across 14 `.lean` files, 15 lines
  across 5 non-Lean files (`docs/theorem-index.md` 4, `docs/user-guide/architecture.md` 2,
  `FormalSystem/README.md` 6, `README.md` 2, `typst/SYNC-MAP.md` 1). `scripts/` and `Tests/`
  contain **zero** occurrences, contrary to the task description's estimate.
- **Sed-safety verified**: no matched token is a prefix of a longer word, `TM_dc` does not contain
  `TM_c` as a substring, and `TM⋆` (`Metalogic/Conservativity/Star/`) has no `_f`/`_c`/`_dc`
  occurrences at all — so `Star/` needs no exclusion logic beyond not matching.
- **The live paper's basis is now this tree's basis**: `def:BX-r` is `BX_d + PU + SEP` with **CO
  derived**, and `def:TMplus`'s `TM_r` is completeness over the dense-and-complete class. The
  "TM⁺_c gap" argument (`ProofSystem/Axioms.lean:513`) and the "the paper bases BX_c on the single
  axiom CO" note (`ProofSystem/Axioms.lean:394`) are therefore obsolete *in the repository's
  favour* and must be recorded as resolved, not renamed.
- **The paper's axiom label is `SEP`, not `SP`** (matching this tree's `Axiom.sep`); use `SEP` in
  all new prose.
- **Three verbatim quotations quote deleted text**: `Semantics/FrameClassValidity.lean:95-96`,
  `Semantics/FrameProperty.lean:43-44` and `Metalogic/Conservativity.lean:137-142` all quote
  `def:TMplus-f`'s "successor-Archimedean discrete class" sentence, which the paper has cut. These
  are **de-quoted** (paraphrased in the tree's own voice) rather than token-swapped.
- **Hard scope boundary with task 548**: C15 resolves `def:`/`thm:` citations against
  `specs/paper-definitions-of-record.md`, so renaming an anchor label here turns C15 red until 548
  pins the new rows. 547 leaves every anchor label and every record entry untouched.
- **The verification grep must be scoped**: a repo-wide grep cannot pass, because `specs/TODO.md`,
  `specs/state.json` and this task's own artifacts quote every old name by construction.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not passed as a roadmap input for this dispatch and carries no
item covering paper-name alignment or documentation naming (grep for the historical names and for
"naming" returns no roadmap item). No roadmap phases are added and no roadmap item is advanced.

## Goals & Non-Goals

**Goals**:

- Every live occurrence of `TM⁺_f`, `TM⁺_c`, `TM⁺_dc`, `TM_f`, `TM_c`, `TM_dc`, `BX_f`, `BX_c`
  under `FormalSystem/`, `Tests/`, `typst/`, `docs/`, `scripts/` and `README.md` is replaced by
  the `z`/`d`/`r` vocabulary.
- One canonical mapping passage — repository `TM⁺` = the paper's `TM`; repository `TM`
  (`BaseLanguage/`, H/G primitive) and its `TM_z`/`TM_d`/`TM_r` extensions = no paper system —
  exists in `FormalSystem/Metalogic/Conservativity.lean`'s module docstring and in
  `docs/README.md`, with a single "these have no paper name" sentence anchored in
  `BaseLanguage/Axioms.lean` and cross-referenced from elsewhere.
- The twelve retracted-claim passages state what is now true of the live paper, with no verbatim
  quotation of text the paper has deleted.
- `TMFrag`'s docstring (`Metalogic/Conservativity/Fragment.lean`) describes the H/G-fragment of
  `TM⁺` as the set of Past/Future theorems of the paper's `TM`, not as a fragment of a named
  paper system.
- `lake build FormalSystem` green and `scripts/check-module-invariants.sh` no worse than baseline.

**Non-Goals**:

- No Lean identifier is renamed. The `⁺` superscript is retained; bare `TM` is not renamed (the
  earlier proposal to do so is withdrawn — bare `TM` is not greppable and the `TM`/`TM⁺`
  distinction is load-bearing throughout `Conservativity/`).
- **No anchor label is renamed.** `def:TMplus-f` / `def:TMplus-c` stay exactly as written; the
  `def:BX-z` / `def:BX-r` relabelling belongs to task 548.
- **`specs/paper-definitions-of-record.md` is not edited.** Its 4 occurrences are pinned entries
  with content hashes owned by task 548.
- `Metalogic/Conservativity/Star/` (`TM⋆`) is not touched.
- No new axiom, `sorry`, theorem, or proof term. No documented axiom/sorry count is edited (C14).
- The five task-546 `FrameClass.Dedekind` / `FrameClass.Discrete` residue sites *outside* the
  paragraphs this task rewrites are reported as a follow-up, not swept silently.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A blanket `sed` produces "this is TM⁺_r, not TM⁺_r" in the four collapsed-distinction passages | H | H | Class A (Phase 3) covers only files whose occurrences are pure labels; every collapsed-distinction file is hand-edited in Phase 4 or 5. Phase 3's file list is closed and enumerated. |
| Renaming an anchor label turns C15 red before 548 lands | H | M | Explicit non-goal; Phase 7 diffs `check-module-invariants.sh` against the Phase 1 baseline, and the Phase 7 grep gate includes an anchor-label invariance check. |
| Writing the task description's mapping paragraph verbatim asserts a paper footnote that does not exist | H | H | Research verified `possible_worlds.tex:1331-1341` is commented out. Phase 2 writes the corrected paragraph; the divergence is surfaced as a non-blocking `user_decision`. |
| A doc-comment edit crosses a `/-` `-/` boundary and breaks elaboration (the `prose` tier blind spot) | M | L | Phase 7's `full` gate (`lake build FormalSystem`) is the designated catcher; each `prose` phase re-reads its own diff for comment-boundary integrity before commit. |
| `docs/README.md` structural lint rejects a new section | M | M | Phase 2 runs `bash scripts/readme-lint.sh` immediately after the addition. |
| New line-number citations into `possible_worlds.tex` drift again (the existing `:4614` citation is already stale — that line is now 4274) | M | M | Rewritten prose cites anchor names (`def:BX-z`, `cor:tm-completeness`), never line numbers, except where evidencing that a passage is commented out. |
| Scope creep into 548's record work | M | M | Phase 7's grep gate excludes `specs/` entirely; `specs/paper-definitions-of-record.md` appears in no phase's file list. |
| Overlap with 548 on `FrameClassValidity.lean` (548's description also claims that file) | M | M | 547 rewrites *system names* and de-quotes; 548 renames the *anchor label*. Phase 7 records the split in the handoff so 548 does not re-litigate. |
| A long `lake build` stalls the dispatch | M | M | Run detached per `context/project/lean4/operations/long-builds.md` in Phases 1 and 7. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4, 5, 6 | 2 |
| 4 | 7 | 3, 4, 5, 6 |

Phases within the same wave can execute in parallel. Every phase owns a disjoint file set; no
file appears in two phases.

---

### Phase 1: Baseline capture [COMPLETED]

**Goal**: Record a pre-edit green baseline so Phase 7 can diff against it rather than against an
assumption.

**Tasks**:
- [x] Run `lake build FormalSystem` detached per
      `context/project/lean4/operations/long-builds.md`; record exit status and any warnings.
- [x] Run `bash scripts/check-module-invariants.sh` in full (no `tail` truncation) and save the
      complete output to the task directory as the baseline. *(deviation: altered — baseline exits 1 on a pre-existing C9 task-number citation in `MintBound.lean`, unrelated to this file set; C14 and C15 both PASS)*
- [x] Re-run the census grep and record the per-file counts, confirming or correcting the figures
      in this plan's Scope Hypothesis: *(deviation: altered — counts confirmed at 74 lines/19 files, but `FormalSystem/README.md`'s 6 lines sit at 194/195/197/199/201/361, not the line numbers Phase 6 guessed)*
      `grep -rcE 'TM⁺?_(f|c|dc)|BX_(f|c)' --include='*.lean' --include='*.md' --include='*.typ' --include='*.sh' --exclude-dir=Boneyard FormalSystem Tests typst docs scripts README.md`
- [x] Confirm the sed-safety and `Star/` invariants still hold: `grep -rnE 'TM⁺?_(f|c|dc)[A-Za-z0-9_]'`
      and `grep -rnE 'TM⋆_(f|c|dc)'` over `FormalSystem/` both return empty.

**Timing**: 0.5 hours (mostly detached build wait)

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: 59 matching lines across 14 `.lean` files and 15 lines across 5 non-Lean
files; `scripts/` and `Tests/` contain zero. Confirm with the census grep above before any edit;
if the counts differ, reconcile the affected phase's file list before proceeding.

**Files to modify**: none (read-only baseline)

**Verification**:
- Build green and invariant output saved before any edit lands.
- Census counts recorded and reconciled against this plan.

---

### Phase 2: Canonical mapping passage [COMPLETED]

**Goal**: Fix the canonical vocabulary and the two-base-systems mapping in one place first, so
every later phase's prose can reference it rather than re-inventing wording.

**Tasks**:
- [x] Write the mapping paragraph into `FormalSystem/Metalogic/Conservativity.lean`'s module
      docstring. Substance (polish the wording, keep the claims):
      `TM⁺` (`ProofSystem/`, full language `BL`, `S`/`U` primitive) **is the paper's `TM`**
      (`def:TMplus`); its extensions `TM⁺_z`, `TM⁺_d`, `TM⁺_r` are the paper's `TM_z`, `TM_d`,
      `TM_r`, named for the class each is complete over (ℤ-time, dense task frames, ℝ-time), built
      on the Burgess-Xu cores `BX_z`, `BX_d`, `BX_r` *(deviation: altered — cited as `def:TMplus-f`/`def:TMplus-d`/`def:TMplus-c`, the labels pinned in `specs/paper-definitions-of-record.md`; citing the paper's live `def:BX-*` labels would turn C15 red before task 548 re-pins the record)*, where
      `BX_r = BX_d + PU + SEP` with `CO` derived. `TM` (`BaseLanguage/`, Past/Future fragment,
      `H`/`G` primitive) and its extensions `TM_z`, `TM_d`, `TM_r` (adding `DF`, `DN`, and
      `DN`+`CO`) **have no paper name**; the `z`/`d`/`r` subscripts there are Lean-only, chosen to
      run parallel to the `TM⁺` side and to the `FrameClass` tags `.ZTime`, `.Dense`, `.RTime`.
      Do not read `TM_z` as a paper system.
- [x] In the same docstring, rewrite the "Two live-paper facts bearing on the discrete rows" block
      (research item B11, currently ~lines 135-152): the quoted `def:TMplus-f` Hölder sentence has
      been cut from the paper, so restate the ℤ-time conclusion from the live `def:BX-z` closing
      sentence in the tree's own voice, and either update the commented-line citation (now
      `possible_worlds.tex:4274`, reading `TM_z`) or drop the line number entirely. *(deviation: altered — the line number was dropped; the commented line sits inside the definition the record pins as `def:TMplus-f`, not at 4274, which is a different comment)*
- [x] Rename the remaining historical names in this file to `z`/`d`/`r`.
- [x] Add the same mapping paragraph (prose-adapted) to `docs/README.md`.
- [x] Run `bash scripts/readme-lint.sh` and fix any structural-lint complaint about the new
      section.

**Timing**: 1.25 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: 8 matching lines in `Metalogic/Conservativity.lean`; `docs/README.md`
currently has none and gains an additive section. Confirm both with the Phase 1 census before
editing.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity.lean` - mapping paragraph added to module docstring; B11
  "two live-paper facts" block rewritten and de-quoted; historical names renamed.
- `docs/README.md` - mapping section added.

**Verification**:
- Diff read-through: every changed hunk lies inside a `/-! -/`, `/-- -/`, `--` region, or inside
  markdown prose.
- No anchor label (`def:TMplus-f`, `def:TMplus-c`, `cor:tm-completeness`) was renamed.
- `scripts/readme-lint.sh` passes.

---

### Phase 3: Class A mechanical rename [COMPLETED]

**Goal**: Apply the literal rename over the files whose occurrences are pure labels carrying no
retracted claim, where a scripted replacement is provably safe.

**Rename rules** (literal, no regex classes needed): `TM⁺_f`→`TM⁺_z`, `TM_f`→`TM_z`,
`BX_f`→`BX_z`, `TM⁺_c`→`TM⁺_r`, `TM⁺_dc`→`TM⁺_r`, `TM_c`→`TM_r`, `TM_dc`→`TM_r`, `BX_c`→`BX_r`.

**Tasks**:
- [x] Apply the rules to `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean`. *(deviation: altered — also de-staled the adjacent "By Hölder (paper `def:TMplus-f`, line 4613)" sentence, which cites a line number that has moved and an argument the paper has replaced)*
- [x] Apply the rules to `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean`.
- [x] Apply the rules to `FormalSystem/BaseLanguage/Derivation.lean`.
- [x] Apply the rules to `docs/theorem-index.md`.
- [x] Read each resulting diff for a collapsed-distinction artefact of the form "X, not X" (the
      `TM⁺_c`/`TM⁺_dc` collapse); if one appears, that passage is Class B and must be hand-written
      here rather than left as produced.
- [x] Confirm no anchor label and no `Star/` file was touched.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: 4 files, 15 matching lines total (`Z1Countermodel.lean` 7,
`TMCompletenessReduction.lean` 1, `Derivation.lean` 3, `docs/theorem-index.md` 4). Confirm against
the Phase 1 census; the closed file list here is what makes the scripted rename safe, so a
discrepancy means re-triaging the extra file into Phase 4 or 5, not widening this phase.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean`
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean`
- `FormalSystem/BaseLanguage/Derivation.lean`
- `docs/theorem-index.md`

**Verification**:
- `grep -nE 'TM⁺?_(f|c|dc)|BX_(f|c)'` over the four files returns nothing.
- No "TM⁺_r, not TM⁺_r"-shaped sentence in the diff.
- Diff read-through confirms every hunk is comment or markdown prose.

---

### Phase 4: ProofSystem and Semantics editorial rewrites [COMPLETED]

**Goal**: Rewrite the four heaviest retracted-claim clusters — the "gap" argument, the CO-basis
note, and the two `ValidComplete` caveats — plus the two de-quotation sites in `Semantics/`.

**Tasks**:
- [x] `ProofSystem/Axioms.lean` (research B1-B4):
      - B1 (~line 394): `def:BX-r` bases `BX_r` on `BX_d + PU + SEP` with CO a *derived* theorem —
        repository and paper now agree; drop the "single extra axiom CO rather than this triple"
        contrast.
      - B2 (~lines 426-430): the "correcting the paper means switching BX_c's basis, routed through
        the fix.md C4 process" note is discharged — the paper has done exactly that. Record as
        resolved, and add that the machine-checked `Metalogic.Independence.CoNotPriorU` witness
        establishes what `def:BX-r`'s commented block only conjectures, while the paper's ℚ-flow
        sketch is the route refuted here.
      - B3 (~line 493): `FrameClass.RTime` is the paper's `TM⁺_r` (`cor:tm-completeness`, ℝ-time
        row); delete the "`TM⁺_dc` … not `TM⁺_c`" contrast entirely.
      - B4 (~lines 513-522): delete the "real gap" claim. `ValidComplete` survives as a
        **repository-only** predicate (forgetful-bridge target, Hölder-dichotomy statement),
        explicitly not the binder set of any paper system.
- [x] `Semantics/Validity.lean` (B8, ~lines 686-689): replace "it is not the paper's `TM⁺_c`"
      with: `ValidComplete` is the class of no paper system; `cor:tm-completeness`'s ℝ-time row is
      `TM_r` (this tree's `TM⁺_r`), whose class is `FrameClass.RTime` / `ValidRTime`.
- [x] `Semantics/FrameProperty.lean` (B9, ~lines 32, 43-44, 192-193) *(deviation: altered — a fourth site, the `TaskFrame.IsZTime` docstring at ~line 131, also quotes the deleted Hölder sentence and was de-quoted here; the census grep missed it because its markdown emphasis splits the token as ``**BX**`_f```)*: retarget the two
      `cor:tm-completeness` references to `TM⁺_r`, and **de-quote** the deleted Hölder sentence —
      paraphrase, or requote `def:BX-z`'s live closing sentence instead.
- [x] `Semantics/FrameClassValidity.lean` (B10, ~lines 35, 42, 95-96, 102): rewrite the
      per-constructor anchors in the `z`/`d`/`r` vocabulary and **de-quote** the ℤ-time sentence.
      Keep the anchor labels `def:TMplus-f` and `cor:tm-completeness` verbatim (548 renames them).
- [x] Cross-reference the Phase 2 mapping paragraph rather than restating it.

**Timing**: 1.75 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: 4 files, 15 matching lines (`ProofSystem/Axioms.lean` 6,
`Semantics/FrameClassValidity.lean` 4, `Semantics/FrameProperty.lean` 3, `Semantics/Validity.lean`
2), and 7 named rewrite passages (B1-B4, B8, B9, B10). Line numbers are from the research report
and are approximate — locate each passage by its quoted text, not by line number, and confirm the
passage count at implementation time.

**Files to modify**:
- `FormalSystem/ProofSystem/Axioms.lean` - B1, B2, B3, B4.
- `FormalSystem/Semantics/Validity.lean` - B8.
- `FormalSystem/Semantics/FrameProperty.lean` - B9 (includes de-quotation).
- `FormalSystem/Semantics/FrameClassValidity.lean` - B10 (includes de-quotation and the
  per-constructor anchor rewrite).

**Verification**:
- No sentence of the form "X, not X" survives.
- *(deviation: altered — the anchor-count check is recorded as non-decreasing rather than exact. `def:TMplus-f` 18 → 19, `def:TMplus-c` 10 → 11, `cor:tm-completeness` 40 → 44: the rewrites cite the pinned anchors in more places than the retired quotations did. No label was renamed or removed, which is the property C15 actually gates on.)*
- No quotation marks enclose the deleted "successor-Archimedean discrete class" sentence anywhere
  in these files.
- The strings `def:TMplus-f`, `def:TMplus-c`, `cor:tm-completeness` are unchanged in count and
  spelling.
- No documented axiom or sorry count was edited (C14 safety).

---

### Phase 5: BaseLanguage, Fragment and Theorems rewrites [NOT STARTED]

**Goal**: Retire the `TM_dc`-vs-`TM_c` fidelity caveats on the BaseLanguage side, reword the
`TMFrag` docstring, and place the one-time "no paper name" sentence at the system table where
`TM_z`/`TM_d`/`TM_r` are first tabulated.

**Tasks**:
- [ ] `BaseLanguage/Axioms.lean` (B6, ~lines 25, 121, 209): the CO row becomes `TM_r`; delete the
      "`TM_c` (see the caveat below)" annotation and the "at the paper's `TM_dc`, not at `TM_c`"
      caveat. Add here, once, the sentence that `TM_z`/`TM_d`/`TM_r` on the BaseLanguage side are
      Lean-only names with no paper counterpart, pointing at `Metalogic/Conservativity.lean`'s
      mapping paragraph for the full statement.
- [ ] `BaseLanguage/AxiomDischarge.lean` (B7, ~line 327): replace the "`TM_dc`, not `TM_c`"
      contrast with the single name `TM_r`.
- [ ] `Metalogic/Conservativity/Backward.lean` (B5, ~lines 144-155): the CEC "fidelity caveat"
      evaporates — the row is `TM_r ⟶ TM⁺_r` at `.RTime`, and `TM⁺_r` *is* the paper's `TM_r`.
      Keep only the still-true content (`.RTime` sits above `.Dense`; CO's translation via
      `coDerived`) and rename the remaining occurrences.
- [ ] `Metalogic/Conservativity/Fragment.lean`: rename the historical names, and reword the
      `TMFrag` docstring so it describes the H/G-fragment of `TM⁺` as **the set of Past/Future
      theorems of the paper's `TM`**, not as a fragment of a named paper system.
- [ ] `Theorems/DedekindDerived.lean` (B12, ~line 335): CO is *derived* in `BX_r`, not "the extra
      axiom of the paper's complete-order extension `BX_c`".
- [ ] `Theorems/DiscreteUnfolding.lean` (B12, ~line 356): DF distinguishes this tree's `TM_z` from
      `TM` — drop "the paper's", since the BaseLanguage systems have no paper name.

**Timing**: 1.25 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: 6 files, 25 matching lines (`Backward.lean` 11, `BaseLanguage/Axioms.lean` 6,
`Fragment.lean` 5, `AxiomDischarge.lean` 1, `DedekindDerived.lean` 1, `DiscreteUnfolding.lean` 1),
and 6 named rewrite passages. Locate each by quoted text rather than line number; confirm counts
against the Phase 1 census.

**Files to modify**:
- `FormalSystem/BaseLanguage/Axioms.lean` - B6 plus the one-time "no paper name" sentence.
- `FormalSystem/BaseLanguage/AxiomDischarge.lean` - B7.
- `FormalSystem/Metalogic/Conservativity/Backward.lean` - B5.
- `FormalSystem/Metalogic/Conservativity/Fragment.lean` - rename plus `TMFrag` docstring rewording.
- `FormalSystem/Theorems/DedekindDerived.lean` - B12.
- `FormalSystem/Theorems/DiscreteUnfolding.lean` - B12.

**Verification**:
- The "no paper name" sentence appears exactly once across the repository.
- No "`TM_dc`, not `TM_c`"-shaped contrast survives.
- `TMFrag`'s docstring names the paper's `TM` (via `TM⁺`), not any `_f`/`_c`/`_dc` system.
- Diff read-through confirms every hunk is inside a comment or docstring.

---

### Phase 6: Markdown and typst prose sweep [NOT STARTED]

**Goal**: Bring the user-facing READMEs, the architecture guide and the typst sync map into the new
vocabulary, retiring the two paragraphs the live paper has answered.

**Tasks**:
- [ ] `README.md` (~lines 197-199): the assertion "`FrameClass.RTime` *is* the paper's `TM⁺_c` …
      There is no gap" becomes the single true statement that `FrameClass.RTime` is the paper's
      `TM⁺_r`. Retire the open question "either the paper's `BX_c` should carry the density axioms,
      or this tree should record that `completeness_rtime` proves a stronger-premise statement" —
      `def:BX-r` extends `BX_d`, so the paper answers it.
- [ ] `FormalSystem/README.md` (~lines 174, 182, 194, 195, 201, 202): same rewrite, plus the
      opportunistic fix of the task-546 `FrameClass.Dedekind` / `FrameClass.Discrete` residue at
      lines 194, 195 and 202, which sit inside the rewritten text.
- [ ] `docs/user-guide/architecture.md`: rename the two `TM⁺_c` occurrences to `TM⁺_r`.
- [ ] `typst/SYNC-MAP.md` (~line 472): rename `TM_c` to `TM_r`.
- [ ] Record, without fixing, the five out-of-scope task-546 residue sites for the Phase 7
      follow-up list: `FormalSystem/ProofSystem/README.md:49`, `FormalSystem/Theorems/README.md:17`,
      `FormalSystem/Semantics/Correspondence/README.md:20`,
      `FormalSystem/Metalogic/Decidability/BiLasso/README.md:161`,
      `docs/development/NAMING_CONVENTION_DEVIATION.md:232`.

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: 4 files, 11 matching lines (`FormalSystem/README.md` 6,
`docs/user-guide/architecture.md` 2, `README.md` 2, `typst/SYNC-MAP.md` 1), plus 3 co-located
task-546 residue lines fixed opportunistically and 5 recorded but not fixed. Confirm against the
Phase 1 census and a fresh `grep -rn 'FrameClass.Dedekind\|FrameClass.Discrete'`.

**Files to modify**:
- `README.md`
- `FormalSystem/README.md`
- `docs/user-guide/architecture.md`
- `typst/SYNC-MAP.md`

**Verification**:
- No "there is no gap" / "open question" paragraph referring to `BX_c`'s density axioms survives.
- `grep -nE 'TM⁺?_(f|c|dc)|BX_(f|c)'` over the four files returns nothing.
- The five out-of-scope residue sites are listed verbatim for the handoff, untouched on disk.

---

### Phase 7: Gate and handoff [NOT STARTED]

**Goal**: Prove the sweep complete and non-regressive, and record the 547/548 boundary so the
follow-on task does not re-litigate it.

**Tasks**:
- [ ] Run the scoped completeness grep; expect no output:
      ```bash
      grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)' \
        --include='*.lean' --include='*.md' --include='*.typ' --include='*.sh' \
        --exclude-dir=Boneyard \
        FormalSystem Tests typst docs scripts README.md
      ```
- [ ] Confirm anchor-label invariance: the repo-wide counts of `def:TMplus-f`, `def:TMplus-c` and
      `cor:tm-completeness` match the Phase 1 baseline exactly.
- [ ] Confirm `specs/paper-definitions-of-record.md` is unmodified (`git diff --stat` shows no
      entry for it).
- [ ] Confirm `Metalogic/Conservativity/Star/` is unmodified.
- [ ] Run `lake build FormalSystem` detached; require green.
- [ ] Run `bash scripts/check-module-invariants.sh` in full and diff against the Phase 1 baseline;
      C14 and C15 must be no worse.
- [ ] Run `bash scripts/readme-lint.sh`.
- [ ] Write the handoff note recording the 547/548 split (547 renamed system names in prose and
      de-quoted three deleted quotations; 548 owns every anchor label and every
      `paper-definitions-of-record.md` row) and the five unfixed task-546 residue sites.

**Timing**: 0.75 hours (mostly detached build wait)

**Depends on**: 3, 4, 5, 6

**Verification Tier**: full

**Files to modify**: none (gate only; the handoff note is a task artifact, not a source file)

**Verification**:
- Scoped grep empty.
- `lake build FormalSystem` green.
- `check-module-invariants.sh` no worse than the Phase 1 baseline, C15 in particular.
- Anchor labels and the definitions-of-record byte-identical to baseline.

---

## Lean Challenge Statements

None. This task's `- **Goals**:` bullets name no Lean identifier, and the task introduces, renames
and proves no Lean declaration — every edit lands inside a comment, docstring, or markdown file.
The identifier set pinned by this section is therefore empty, matching the empty identifier set
named under Goals.

## Testing & Validation

- [ ] `grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)' --include='*.lean' --include='*.md' --include='*.typ' --include='*.sh' --exclude-dir=Boneyard FormalSystem Tests typst docs scripts README.md` returns no output.
- [ ] `lake build FormalSystem` exits green (detached; see `context/project/lean4/operations/long-builds.md`).
- [ ] `bash scripts/check-module-invariants.sh` is no worse than the Phase 1 baseline; C15 in
      particular still resolves every anchor citation.
- [ ] `bash scripts/readme-lint.sh` passes.
- [ ] `git diff` touches no Lean identifier: every hunk is inside `/-! -/`, `/-- -/`, `--`, or a
      markdown/typst file.
- [ ] `specs/paper-definitions-of-record.md` and `FormalSystem/Metalogic/Conservativity/Star/`
      are unmodified.
- [ ] No sentence of the form "X, not X" and no quotation of the deleted "successor-Archimedean
      discrete class" sentence survives anywhere in live scope.

## Artifacts & Outputs

- `specs/547_replace_historical_system_names_in_docstrings/plans/01_replace-historical-system-names.md` (this plan)
- Phase 1 baseline: saved `check-module-invariants.sh` output and census counts under the task
  directory.
- Edited sources: 14 `.lean` files under `FormalSystem/` and 5 non-Lean files
  (`README.md`, `FormalSystem/README.md`, `docs/README.md`, `docs/theorem-index.md`,
  `docs/user-guide/architecture.md`, `typst/SYNC-MAP.md` — `docs/README.md` gains content rather
  than being renamed).
- A handoff note recording the 547/548 boundary and the five unfixed task-546 residue sites.
- `specs/547_replace_historical_system_names_in_docstrings/summaries/01_*-summary.md` at
  implementation close.

## Rollback/Contingency

Every change is comment, docstring or markdown text; nothing is load-bearing for elaboration.
Each phase commits separately (`per-substep`, the default mode), so any single phase can be
reverted with `git revert` on its commit without disturbing the others. If Phase 7's
`check-module-invariants.sh` diff shows C15 red, the cause is almost certainly an accidental
anchor-label edit: locate it by diffing the anchor-label counts against the Phase 1 baseline and
restore the label, rather than reverting the whole sweep. If `lake build` breaks, the cause is a
crossed `/-` `-/` comment boundary in the offending file's diff — a localized fix, not a rollback
of the task.
