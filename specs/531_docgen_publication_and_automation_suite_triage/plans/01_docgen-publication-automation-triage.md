# Implementation Plan: Task #531

- **Task**: 531 - docgen publication and automation suite triage
- **Status**: [COMPLETED]
- **Effort**: 27.5 hours (17 phases, each capped at 2 hours)
- **Dependencies**: 529 (completed), 530 (completed)
- **Research Inputs**: specs/531_docgen_publication_and_automation_suite_triage/reports/01_docgen-publication-automation-triage.md
- **Artifacts**: plans/01_docgen-publication-automation-triage.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

WAVE 5 of the 2026-09-01 Lean engineering review: publish the API documentation, finish the
repository furniture mature Lean libraries carry, and retire the bespoke automation suite that
measurement shows is unused. Task 530 already landed roughly half the dispatch's WORK list
(`references.bib`, `CITATION.cff`, `docs/ARCHITECTURE.md`, 105 pinned axiom sets), so this plan
implements the **corrected** remainder identified by research, not the dispatch text verbatim:
publication via `docgen-action` rather than a `lakefile.lean` requirement, a `MainResults.lean`
guarded by *subset assertion* against the existing C2/C14 pins rather than by a third axiom
baseline, and naming work adjudicated by class rather than applied as a blanket rule.

Definition of done: a `docs.yml` workflow that builds and deploys doc-gen4 output with a complete
`references.bib`; `FormalSystem/MainResults.lean` compiling with every `#print axioms` output
recorded and machine-checked against the C2/C14 baselines; zero declared tactics with zero
library-and-test uses outside `Boneyard/`; zero live `lemma` declarations; a new invariant check
preventing regrowth of the naming classes; `lake build`, `lake test` and
`scripts/check-module-invariants.sh` all green.

This plan introduces **no new theorem statements** — `MainResults.lean` restates already-proved
declarations and adds `#print axioms` commands — so it commits to zero `sorry`, zero new axioms,
and zero deferral, and carries no `## Lean Challenge Statements` section (there is nothing to pin
that is not already proved in the tree).

### Research Integration

The research report supersedes eight of the dispatch's factual anchors. The plan is built on the
corrected versions:

- **doc-gen4 is supplied by `docgen-action` itself.** No `require «doc-gen4»` in `lakefile.lean`;
  `lake build` and `lake-manifest.json` stay unchanged. `build-page: false` is required because the
  action's `homepage` input defaults to `docs`, which collides with this repo's 100-file
  non-Jekyll `docs/` tree.
- **`docs/README.md:272-278` now asserts the opposite of what publication needs** (task 530 took
  E-08's "delete the broken recipe" exit). It must be rewritten, not merely extended.
- **The anti-drift mechanism already exists.** C2 pins 4 axiom sets and C14 pins 101 (105 total);
  every declaration the dispatch names for `MainResults.lean` is already pinned. The missing wiring
  is a *subset assertion*, ~15 lines, not a new baseline.
- **`SearchConfig`'s five weight fields are write-only** (`Commands.lean:157`, in source: "weights
  remain unused"), so `temporal_search`, `propositional_search` and `tm_auto` are behaviourally
  identical to `modal_search`, and three publication-facing docstrings make false claims.
- **The `TMLogic` Aesop rule set has zero consumers** — `AesopRules.lean` (291 lines) and
  `AesopRuleSet.lean` (31 lines) are entirely dead.
- **`Helpers.lean`'s three ranges interleave**; the review's line boundaries (109-515 / 516-1000 /
  545-1210) overlap and cannot be used. The split must move declarations.
- **The "SEPARATE AND MORE SERIOUS FINDING" is not a defect.** `mem_knownTimes_of_mem` at
  `CountermodelExtraction.lean:415` is `private` (name-mangled). A corrected repo-wide scan finds
  no two live declarations sharing a fully-qualified name except twelve never-co-imported `main`
  entry points. Item (7)'s "check this first" framing is retired.
- **The Uppercase_x rename is ~30%, not 100%, mechanical**: of 107 live names, ~55 are tense
  operator prefixes (`F_`, `P_`, `G_`, `H_`) where dot-namespacing would invent namespaces that do
  not exist. Both of the dispatch's flagship examples live only in `Boneyard/`. `lemma` count is
  **88** in live scope, not 141 (the review's count included `Boneyard/`).

### Prior Plan Reference

No prior plan. This is round 01 for this task.

### Roadmap Alignment

`specs/ROADMAP.md` **Phase 5: Publication and Documentation** is the home front for items 1-4:
this task delivers the doc-gen4 site, the completed bibliography, `MainResults.lean` and the
root-level furniture that Phase 5's task 177 polish pass assumes exists. `MainResults.lean` is
explicitly the artefact task 178's decidability examples should cite — hand it over on completion.
Items 5-7 advance **Phase 7: Repository Hygiene and Programme Metadata**. This plan does not modify
`ROADMAP.md` (no `roadmap_flag` on this dispatch); it consults it read-only.

## Goals & Non-Goals

- **Goals**:
  - Public doc-gen4 API documentation, built and deployed by `leanprover-community/docgen-action`,
    linked from `README.md`, with `references.bib` consumed by the build.
  - A complete `references.bib` (the ~9 missing works added, `rabinovich2014` foremost at 71
    citations) and live-scope `## References` prose converted to bib keys.
  - `FormalSystem/MainResults.lean`: one readable navigation page restating the headline results,
    each followed by `#print axioms` with the verbatim output recorded, machine-guarded as a
    subset of the C2/C14 pins.
  - Root `ORGANISATION.md` (a pointer, not a third copy) and root `NOTATION.md` documenting the
    15 live notation declarations and the recorded tag-asymmetry decision.
  - Zero declared tactics with zero library-and-test uses outside `Boneyard/`; a truthful
    `SearchConfig`; `Helpers.lean` split into `UserTactics`/`Meta`/`Search`; regenerated automation
    inventories and `docs/reference/tactic-reference.md`.
  - Zero live `lemma` declarations; the ~30 genuine Uppercase_x names dot-namespaced; the
    adjudicated shadowing pairs renamed; a new invariant check preventing regrowth of all three
    classes.

- **Non-Goals**:
  - Adding `doc-gen4` to `lakefile.lean` / `lake-manifest.json` (the action supplies it).
  - A Jekyll landing page (`build-page: false`; `homepage: website` is a documented later upgrade).
  - A third axiom baseline for `MainResults.lean`.
  - Renaming the ~55 tense-operator `F_`/`P_`/`G_`/`H_` names, or the outer four-member
    `completeness_base/_dense/_ztime/_rtime` family.
  - Introducing a new `TM[...]` validity notation (contradicts the recorded decision at
    `Semantics/Validity.lean:239-242`).
  - Renaming `allAxiomNames` (its duplication is deliberate and documented; it gets a consistency
    check instead).
  - Any `Boneyard/` edits beyond creating and populating the new guard-first exception directory.
  - Pushing, deploying, or setting the repository Pages source (the last is a manual, one-time
    human step the workflow cannot perform).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| First doc-gen4 deploy publishes the three false `Commands.lean` docstrings and the whole retired suite | H | H | Phase 3 (docstring truth) and Phase 8 (regenerated docs) both precede Phase 16 (publication) in the dependency graph; this ordering is load-bearing, not incidental |
| `build-page: true` (the action default) Jekyll-builds the existing 100-file `docs/` tree | H | H | Set `build-page: false` **explicitly**; never rely on the default. Phase 16 verifies the input is present in the committed YAML |
| Rewriting `docs/README.md:272-278` breaks C12/C13 link resolution | M | M | Run `bash scripts/check-module-invariants.sh --no-build` after the edit; both checks are structural |
| Retiring guard-first tactic files into an event-first `Boneyard/` falsifies its blanket banner | M | H | Phase 5 creates a documented guard-first exception subdirectory with its own README, following `BundleDeadHalf/`'s precedent, and updates `Boneyard/README.md`'s exception list |
| Migrating ~105 test call sites from the three aliases to `modal_search` changes test outcomes | H | L | The three are behaviourally identical (weights unread); any test that changes result is a genuine finding — stop and report rather than adjust the test |
| Converting 190 prose citations across 227 files breaks a docstring boundary and the build | H | M | Edits confined to `/-! -/` and `/-- -/` blocks; mechanical substitution over the 20 distinct work-strings; full `lake build` gates the phase close |
| Renaming `BXCanonical.completeness_dense`/`_ztime` contradicts the recorded decision at `StrongCompleteness.lean:126-133` | M | H | Phase 11 updates that note **in the same commit** with the C17-masking justification, so the tree never carries two opposed decisions |
| `lemma` → `theorem` surfaces new C17 dead-declaration candidates and moves the C19 aggregate | L | H | Both checks are reporting-only (no `ENFORCE_C17`/`ENFORCE_C19`); record before/after numbers in Phase 17 rather than treating movement as a failure |
| The `deduction`/`undischarge` trial consumes effort and yields nothing | L | H | Time-boxed to one hour in Phase 7; the `noncomputable` infection documented at `Deduction.lean:32-38` makes "no" a legitimate, recordable outcome |
| A fourth namespace-walking scanner is added to `check-module-invariants.sh` | M | M | Phase 14 **extends** C16's existing `dupNamespace` walker rather than copying it |
| Splitting `Helpers.lean` breaks `Commands.lean`/`PropDecide.lean` imports | M | M | Only three files import it; `Deduction.lean` uses nothing from it. `PropDecide.lean` uses exactly two declarations, `Commands.lean` those two plus `searchProof` — the interface is small and enumerable |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 9 | -- |
| 2 | 2, 4, 10 | 1, 3, 9 |
| 3 | 5, 11 | 2, 4 |
| 4 | 6, 12 | 5, 11 |
| 5 | 7, 13 | 6, 12 |
| 6 | 8 | 6, 7, 12, 13 |
| 7 | 14 | 8, 11, 12, 13 |
| 8 | 15 | 10, 14 |
| 9 | 16 | 2, 3, 8, 15 |
| 10 | 17 | all |

Phases within the same wave can execute in parallel. Where two same-wave phases could touch the
same tree, each carries an explicit territory line; those exclusions are load-bearing.

---

### Phase 1: Complete references.bib [COMPLETED]

**Goal**: `references.bib` holds an entry for every work cited in live-scope `## References`
sections, so the published references page is complete on first sight.

**Tasks**:
- [x] Re-run the prose-citation census to confirm the missing set (report Appendix gives the
      one-line command). *(completed — 20 distinct cited works, 190 occurrences; census output
      recorded in the summary)*
- [x] Add the missing entries: `rabinovich2014` (71 citations — the most-cited work in the tree),
      `doets1989`, `goldblatt1992`, `burgess1984`, `reynolds1996`, `reynolds2003`,
      `verbrugge2007`, `venema2001`, `fisherLadner1979`. *(deviation: altered — 8 entries added,
      not 9. `reynolds1996` → `reynolds2001` (the quoted title "An Axiomatization of Full
      Computation Tree Logic" is the 2001 JSL paper; corpus entry `reynolds_2001`);
      `verbrugge2007` → `verbrugge2004` (corpus entry `verbrugge_2004`, de Jongh/Veltman/
      Verbrugge); `fisherLadner1979` → `fischerLadner1979` (correct author spelling);
      `venema2001` NOT added — the prose is literally "Blackburn, de Rijke, Venema 2001, Modal
      Logic", i.e. the existing `blackburn2002` entry)*
- [x] Verify each added entry's bibliographic detail against a real source; do not fabricate
      volume/page data. *(completed — verified against ~/Projects/Literature/index.json and the
      converted source scans: `doets_1989` sec01 carries the NDJFL 30(2) Spring 1989 masthead,
      `reynolds-2003-ockhamist` chunk_0001 carries the title/author, `verbrugge_2004` sec01
      carries the Liber Amicorum framing, `burgess_1984` scan confirms the Handbook Vol. II
      pagination)*
- [x] Confirm the existing near-miss pairs are genuinely distinct works and not typos:
      `doets1987` vs. `doets1989`, `burgess1982` vs. `burgess1984`. *(completed — distinct:
      thesis vs. NDJFL paper; "Axioms for Tense Logic I" vs. "Basic Tense Logic")*

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: ~9 missing entries against 13 present, over 20 distinct cited works and 190
prose citation occurrences. Confirm at implementation time by re-running the census command in the
report's Appendix and diffing the resulting work list against `grep '^@' references.bib`; report
the actual numbers.

**Files to modify**:
- `references.bib` - add the missing entries

**Verification**:
- `grep -c '^@' references.bib` increases by the confirmed count.
- Every distinct work in the census maps to exactly one bib key.

---

### Phase 2: Convert prose citations to bib keys [COMPLETED]

**Goal**: live-scope `## References` sections cite bib keys rather than free prose, so doc-gen4
resolves them against `references.bib`.

**Tasks**:
- [x] Build the work-string → bib-key substitution table (20 distinct forms, including the
      composite `Doets 1987/1989` and `Burgess 1982/84` cases, which expand to two keys).
      *(deviation: altered — 20 forms were not enough. The Phase 1 census keyed on
      `Surname YYYY`, which cannot see four other citation shapes that are live in `##
      References` blocks: `Rabinovich, *A Proof of Kamp's Theorem* (2014)` (~20 sites),
      `GHR93`/`GHR94`/`GHR93 (Gabbay, Hodkinson, Reynolds, 1994)` (~16 sites),
      `Blackburn, de Rijke, Venema (2001)` / `…: Modal Logic`, and `Goldblatt (1992), Logics
      of Time and Computation`. A second substitution pass of 13 further forms was added,
      giving 33 in all)*
- [x] Apply the substitution inside `## References` blocks only, in `FormalSystem/` (excluding
      `Automation/` — see territory) and `Tests/`, live scope only (`Boneyard/` excluded).
      *(completed — 193 lines across 134 files: 132 lines/85 files in pass 1, 61 lines/52 files
      in pass 2)*
- [x] Confirm by diff read-through that every changed hunk lies inside a `/-- ... -/` or
      `/-! ... -/` block; no hunk may cross a comment boundary. *(completed — asserted
      mechanically rather than by eye: a comment-depth scan over the post-edit files
      confirmed all 193 changed lines lie at block-comment depth > 0, and no line was added
      or removed, so no boundary could move. `lake build` green independently confirms it)*
- [x] Leave narrative in-body citations alone; only `## References` list entries convert.
      *(completed — the residual scan finds three in-body survivors and leaves them: a
      Literature corpus path, a possessive "Rabinovich's Definition 4.1", and "Doets 1.4/1.5"
      naming lemma numbers rather than a work)*
- [x] **Added**: five bib entries for works this phase's wider scan found cited in `##
      References` blocks with no key at all — `gore1999` (9 sites), `libal2016`, `korf1985`,
      `yang2019`, `kaliszyk2018`. `references.bib` now holds 26 entries, up from 13.
- [x] **Added**: regenerated the three stale `<!-- BEGIN GENERATED: inventory -->` blocks
      (`README.md`, `FormalSystem/README.md`, `FormalSystem/Automation/Tactics/README.md`),
      which Phase 4's deletion of 148 lines from `Commands.lean` made stale. Phase 8 owns the
      inventory regeneration, but leaving the tree with a failing `INV` check between phases
      is worse than regenerating twice; the operation is idempotent.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: 190 prose citation occurrences across 227 files carrying a `## References`
section, less the `FormalSystem/Automation/` share deferred to Phase 8. Confirm by re-running the
census before and after; the post-edit prose-citation count for converted works must be zero
outside the excluded territory.

*Measured*: 193 lines changed across 134 files. The post-edit `Surname YYYY` census returns
**zero** over all of `FormalSystem/` and `Tests/` — including `Automation/`, which turns out to
carry no `Surname YYYY` citation at all, so Phase 8's citation task is already discharged for
that shape. Phase 8 still owns `Automation/`'s four remaining non-`Surname YYYY` citations
(`Korf, R.E. (1985)`, `Yang et al. (2019)` ×2, `Kaliszyk et al. (2018)`), whose keys this phase
added.

**Territory**: `FormalSystem/**` excluding `FormalSystem/Automation/**`; `Tests/**`. The
`Automation/` share is deliberately deferred to Phase 8 so this phase cannot collide with the
concurrent automation-triage wave.

**Files to modify**:
- `FormalSystem/**/*.lean` (`## References` blocks) - prose to `[key]`
- `Tests/**/*.lean` (`## References` blocks, if any) - same

**Verification**:
- `lake build` green (a broken docstring boundary is the only way this phase can fail the build).
- `bash scripts/check-module-invariants.sh --no-build` green, C15 in particular (paper anchors are
  a distinct citation class and must be untouched).

---

### Phase 3: Make SearchConfig truthful [COMPLETED]

**Goal**: delete the five write-only weight fields and the two presets that differ only in unread
fields, and correct the three publication-facing docstrings that describe behaviour the code does
not have.

**Tasks**:
- [x] Delete `axiomWeight`, `assumptionWeight`, `mpWeight`, `modalKWeight`, `temporalKWeight` from
      `SearchConfig` (`Tactics/Commands.lean:25-41`). *(completed)*
- [x] Delete `SearchConfig.temporal` and `SearchConfig.propositional` (`:46-48`, `:51-54`) and the
      corresponding `applyParams` cases (`:140-144`). *(completed — the three `elab_rules` that
      built configs from the two presets now build from `SearchConfig.default`)*
- [x] Correct the false claims at `Commands.lean:182-183` ("Prioritizes temporal K rules over modal
      K rules") and `:255` ("Disables modal K and temporal K rules"); state instead that these
      presets were behaviourally identical to the default and have been removed. *(completed — plus
      the `modal_search` docstring's five-weight named-parameter list and the
      `propositional_search` "When to use" / "Difference from modal_search" blocks, which made
      the same false claim and the plan did not enumerate)*
- [x] Remove or retarget the in-source "weights remain unused" comment at `:157` now that no unused
      weights exist. *(completed — parenthetical removed)*
- [x] Leave `ProofSearch/Core.lean`'s separate, actually-read weights structure untouched.
      *(completed)*

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: five fields, two presets, and three false docstring claims, all in
`Tactics/Commands.lean`. Confirm with
`grep -rn 'axiomWeight\|assumptionWeight\|mpWeight\|modalKWeight\|temporalKWeight' --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard`
returning zero after the edit.

*Measured*: five fields, two presets and **five** false docstring claims (the plan's three plus
the `modal_search` parameter list and `propositional_search`'s two closing blocks). The census
command as written cannot return zero: `Automation/ProofSearch/Core.lean` declares its own,
genuinely-read `axiomWeight`/`assumptionWeight`/`modalKWeight`/`temporalKWeight` fields, which
this phase's non-goals explicitly protect. The assertion is therefore scoped to
`Tactics/Commands.lean`, where the only surviving occurrences are inside the new docstring that
records the removal.

**Files to modify**:
- `FormalSystem/Automation/Tactics/Commands.lean` - field/preset deletion, docstring correction

**Verification**:
- `lake build` and `lake test` green (tactic syntax accepting the removed parameters would break
  at the call site if any test passes them).
- Zero live-scope occurrences of the five field names.

---

### Phase 4: Retire the three search aliases [COMPLETED]

**Goal**: remove `tm_auto`, `temporal_search` and `propositional_search`, which Phase 3 established
are behaviourally identical to `modal_search`, and migrate their test call sites.

**Tasks**:
- [x] Migrate test call sites to `modal_search`: `tm_auto` (~65), `temporal_search` (~16),
      `propositional_search` (~24), across `Tests/BimodalTest/Automation/` and
      `Tests/BimodalTest/Integration/`. *(completed — measured 169 whole-word occurrences across
      the four test files: TacticsTest.lean 69, AutomationProofSystemTest.lean 87,
      EdgeCaseTest.lean 10, TacticsTest_Simple.lean 3. The plan's ~105 counted invocations;
      docstring and section-heading mentions are the remainder, and were rewritten too)*
- [x] Run the test suite after migration and **before** deleting the declarations; any test whose
      outcome changes is a genuine behavioural finding — stop, record it, and do not adjust the
      test to make it pass. *(completed — `lake test` green, 45 `[test] PASS`/`OK` lines before
      and after the migration, identical to the pre-phase baseline. No test outcome changed,
      confirming the three aliases were behaviourally identical to `modal_search`)*
- [x] Delete the three tactic declarations from `Tactics/Commands.lean`. *(completed — the three
      `syntax`/`def run*Search`/`elab_rules` blocks and the `tm_auto` section docstring, 148
      lines, plus the in-file example tests that invoked them)*
- [x] Update the prose references to them in `Tests/BimodalTest/Automation/README.md`,
      `Tests/BimodalTest/Integration/README.md` and `Tests/BimodalTest/Integration/COVERAGE.md`.
      *(completed — plus `FormalSystem/Automation.lean`'s submodule list, usage block and Tactic
      Selection Guide, `FormalSystem/FormalSystem.lean:51` and
      `FormalSystem/Examples/BimodalProofs.lean:227`, which the plan did not enumerate but which
      named the deleted tactics in publication-facing docstrings. The remaining live mentions
      are in `AesopRules.lean`/`AesopRuleSet.lean` (retired by Phase 5) and `Helpers.lean`
      (split by Phase 6))*

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: ~105 test call sites across 4 `.lean` test files plus 3 markdown files.
Confirm by counting occurrences per tactic before migration and asserting zero live-scope
occurrences after.

**Files to modify**:
- `FormalSystem/Automation/Tactics/Commands.lean` - delete three declarations
- `Tests/BimodalTest/Automation/{TacticsTest,TacticsTest_Simple,EdgeCaseTest}.lean` - migrate
- `Tests/BimodalTest/Integration/AutomationProofSystemTest.lean` - migrate
- `Tests/BimodalTest/Automation/README.md`, `Tests/BimodalTest/Integration/{README,COVERAGE}.md` - prose

**Verification**:
- `lake build` and `lake test` green with the same pass count as before migration.
- Zero live-scope occurrences of the three tactic names.

---

### Phase 5: Retire the zero-use tactics and the dead Aesop rule set [COMPLETED]

**Goal**: move every remaining tactic with zero library-and-test uses, plus the consumer-less
`TMLogic` Aesop rule set, into a documented guard-first `Boneyard/` exception directory.

**Tasks**:
- [x] Create `FormalSystem/Boneyard/RetiredTactics/` with a README stating it is **guard-first**
      (like `BundleDeadHalf/`), why each artefact was retired, and the measured usage that
      justified it. *(completed — 93 lines, with a per-tactic measurement table rather than a
      prose claim, and a note that the two `.lean` files there are excerpts rather than whole
      archived modules)*
- [x] Add the new directory to `FormalSystem/Boneyard/README.md`'s exception list so the
      event-first banner stays true. *(completed — the banner now reads "two named exceptions",
      and `BundleDeadHalf/`'s heading became "the first exception")*
- [x] Move the seven zero-use `Normalization.lean` tactics (`modalNorm`, `propNorm`, `modalOpNorm`,
      `temporalNorm`, `modalNormAt`, `modalNormAll`, `modalFold`) and any declarations that become
      dead with them. *(completed — no declaration became dead with them: each was a one-line
      `simp only` over a simp set that stays live, so the 21 unfold lemmas, 10 fold lemmas,
      `EnrichedFormula`, `foldFormula` and the serialization layer all remain. The file's own
      round-trip examples were rewritten to call `simp only [formula_unfold]` directly, which is
      what the tactics expanded to)*
- [x] Move `modal_k_tactic`, `temporal_k_tactic`, `modal_4_tactic`, `modal_b_tactic` (and the
      `mkOperatorKTactic` factory if nothing else uses it) out of `Tactics/Helpers.lean`, migrating
      or deleting their ~17 test sites. *(deviation: altered — nothing else uses
      `mkOperatorKTactic`, so it moved too, and **there were no test sites to migrate**. The ~17
      the plan expected are section headings and `/-- Test NN: modal_4_tactic ... -/` docstrings
      whose examples apply `DerivationTree.axiom` and the axiom constructors directly and never
      invoke a tactic. The headings were corrected in place, so the axioms stay tested and only
      the false claim that a tactic was under test went away. Four `@[nolint
      defsWithUnderscore]` attributes on the moved tactics' auto-generated `tactic*` names went
      with them, taking the documented exemption count from seven to three)*
- [x] Move `FormalSystem/Automation/AesopRules.lean` and `FormalSystem/Automation/AesopRuleSet.lean`
      wholesale (zero consumers), and drop their imports from `FormalSystem/Automation.lean`.
      *(completed — plus a second import the plan did not name: `Tactics/Helpers.lean:8` also
      imported `AesopRules`, and dropping it is what made the move possible at all. Nine
      documentation sites naming the two modules were rewritten, four of them under `docs/`
      where C12 would otherwise have failed on the now-unresolvable path)*
- [x] Confirm nothing under `Boneyard/` is reachable from `lakefile.lean`'s `FormalSystem` root.
      *(completed — `find .lake/build -path '*Boneyard*' -name '*.olean'` is empty, and C11
      re-verifies that all 536 archived import lines resolve, which required repointing the
      moved `AesopRules.lean`'s import of its sibling rule-set module)*

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 13 tactic declarations plus 2 whole files (291 + 31 lines) retired, ~17 test
sites affected. Confirm the "zero library AND test uses" premise per declaration immediately before
moving each one; a non-zero count is a stop condition, not a formality.

*Measured*: 12 tactic declarations plus `mkOperatorKTactic` (13 with it) and the 2 whole files,
as hypothesised. **Zero test sites affected**, not ~17 — see the deviation above. The
zero-use premise was confirmed per declaration and holds for every one: counting only real
invocations, `modalNorm` has 17 occurrences and all 17 are in its own defining file's examples;
`propNorm`, `modalOpNorm` and `modalNormAll` are never invoked anywhere at all, including in
their own file; `temporalNorm` and `modalNormAt` have one occurrence each, a docstring example
and the tactic's own `macro_rules` body; `modalFold` has 3, all its own fold tests; and each of
the four operator-K/modal-axiom tactics has exactly one, its own docstring's example block.

**Files to modify**:
- `FormalSystem/Boneyard/RetiredTactics/` (new, with README) - destination
- `FormalSystem/Boneyard/README.md` - exception list
- `FormalSystem/Automation/Normalization.lean` - remove seven tactics
- `FormalSystem/Automation/Tactics/Helpers.lean` - remove four operator-K tactics
- `FormalSystem/Automation.lean` - drop the two Aesop imports
- `Tests/BimodalTest/Automation/*.lean` - remove the ~17 orphaned test sites

**Verification**:
- `lake build` and `lake test` green.
- `grep -rn 'TMLogic' --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard` returns zero.
- No built `.olean` under any `Boneyard/` path.

---

### Phase 6: Split Helpers.lean [COMPLETED]

**Goal**: replace the 1,210-line `Helpers.lean` with `Tactics/{UserTactics,Meta,Search}.lean`,
moving declarations (the three ranges interleave, so line-boundary cuts are impossible).

**Tasks**:
- [x] Classify every surviving declaration into user tactics, reusable `MetaM` plumbing, or search
      engine, using the report's Finding 6(e) inventory as the starting classification.
      *(completed — and the classification turned out to be a clean **contiguous** cut after
      Phase 5's removals: the user-tactic half occupies one unbroken range and uses nothing from
      the other two, verified by grepping each of its four declarations across the rest of the
      file and each of the other two thirds' declarations across it. Only `Meta` and `Search`
      interleave)*
- [x] Create `Tactics/UserTactics.lean` (`apply_axiom`, `modal_t`, `assumption_search`, the
      formula predicates and extractors). *(completed — 275 lines, plus the three surviving
      `@[nolint defsWithUnderscore]` attributes, which belong with the tactics whose tokens
      generate the names)*
- [x] Create `Tactics/Meta.lean` (`extractDerivationGoal`, `formulaHead`, `lemmaConclusionHead`,
      `isNilContext`, `buildContextExpr`) — the only part `PropDecide.lean` and `Commands.lean`
      reuse. *(completed — 99 lines, exactly those five declarations. Confirmed by count:
      `PropDecide.lean` uses `extractDerivationGoal` and `isNilContext` and nothing else;
      `Commands.lean` uses `extractDerivationGoal` plus `searchProof` from `Search.lean`)*
- [x] Create `Tactics/Search.lean` (`tryAxiomMatch`, `tryLemmaMatchCore`, `tryLemmaMatch`,
      `tryAssumptionMatch`, the implication/context extractors, `tryModusPonens`, `tryModalK`,
      `tryTemporalK`, `searchProof`). *(completed — 657 lines. It imports `Meta.lean`; the
      dependency runs one way only)*
- [x] Delete `Helpers.lean` and repoint `Commands.lean` (needs `Meta` + `Search`) and
      `PropDecide.lean` (needs `Meta` only). *(completed — plus `FormalSystem/Automation.lean`,
      which now imports `UserTactics` explicitly: it used to reach the user tactics through
      `Commands.lean`'s import of `Helpers`, and that path is gone)*
- [x] Drop `Deduction.lean`'s `import ... Helpers` — it uses nothing from it. *(deviation:
      altered — true of its **declarations**, false of its imports. `Deduction.lean` had no
      import line of its own at all: it reached `ProofSystem`, `deductionTheorem` and `Lean`
      transitively through `Helpers`. Dropping the line left it with zero imports and produced
      nine compiler errors, which the first verification build caught. It now imports
      `FormalSystem.ProofSystem`, `FormalSystem.Metalogic.Core.DeductionTheorem` and `Lean`
      directly, which is what it should have had all along)*
- [x] Record whether `Search.lean` duplicates `ProofSearch/`'s responsibility; if so, note it as a
      follow-up rather than merging in this task. *(completed — recorded in `Search.lean`'s own
      module docstring as an open question. They are two engines with different interfaces, and
      only this one is reachable from a tactic; `ProofSearch/`'s weights are genuinely read,
      unlike the ones Phase 3 deleted. Merging is out of scope and is named as such)*

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: ~24 surviving declarations across three destination files; exactly three
importers of `Helpers.lean` (`Commands.lean`, `PropDecide.lean`, `Deduction.lean`), of which one
is a dead import. Confirm the importer set with
`grep -rn 'Tactics.Helpers' --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard` before
starting.

*Measured*: 24 declarations — 7 user tactics and predicates, 5 `MetaM` helpers, 12 search
declarations — across the three files (275 + 99 + 657 = 1,031 lines, against `Helpers.lean`'s
1,210 after Phase 5 took 200 lines out of it). The three importers were confirmed, and the
"dead import" finding was **half right**: `Deduction.lean` used no declaration from
`Helpers.lean`, but the import was carrying its entire transitive import closure. See the
deviation above.

**Files to modify**:
- `FormalSystem/Automation/Tactics/{UserTactics,Meta,Search}.lean` (new)
- `FormalSystem/Automation/Tactics/Helpers.lean` (deleted)
- `FormalSystem/Automation/Tactics/{Commands,PropDecide,Deduction}.lean` - imports
- `FormalSystem/Automation.lean` / `FormalSystem/Automation/Tactics.lean` - module aggregation

**Verification**:
- `lake build` and `lake test` green.
- Zero live-scope references to `Tactics.Helpers`.
- Each new file's declaration set is disjoint from the others'.

---

### Phase 7: Time-boxed deduction/undischarge trial [COMPLETED]

**Goal**: decide, on evidence, whether the `deduction`/`undischarge` tactic forms should be adopted
in `Metalogic/Core/DeductionTheorem.lean`, and record the verdict either way.

**Tasks**:
- [x] Identify the `DerivationTree`-valued (`Type`-valued) hot spots in
      `Metalogic/Core/DeductionTheorem.lean` where the tactic form could apply. *(completed —
      there are exactly four: `deductionAxiom`, `deductionAssumptionSame`,
      `deductionAssumptionOther` and `deductionMp`, the only declarations in the file whose goal
      has the shape `Γ ⊢[fc] A.imp B`)*
- [x] Attempt the conversion on two or three of them; measure whether the `noncomputable`
      infection documented at `Deduction.lean:32-38` propagates. *(deviation: altered — no
      conversion was attempted, because the identification step already settled it. All four
      candidate sites sit **above** `deductionTheorem` in the file, since they are the cases its
      own well-founded recursion dispatches to. `deduction` is a wrapper around
      `deductionTheorem`, so using it in any of them would ask the theorem to prove its own
      cases. The only two declarations below `deductionTheorem` are `deductionConverse`, which
      runs the other direction and is already a three-line term, and `Derivable.deduction`,
      which is `Prop`-valued and has no goal of this shape. Attempting a conversion to observe a
      `noncomputable` cost that circularity makes unreachable would have been theatre)*
- [x] **Hard stop at one hour.** Record the verdict in `Tactics/Deduction.lean`'s module docstring:
      either adopted (with the converted sites) or declined (with the measured reason).
      *(completed — DECLINED, recorded under its own heading. The reason is stronger than the
      one the plan anticipated: circularity, not `noncomputable` infection. The infection is
      real and stays documented, but it never gets to be the deciding factor)*
- [x] If declined, state explicitly that `Derivable.deduction` (8 uses) and the `deductionTheorem`
      term form (167 uses) remain the recommended route, so the file is not re-litigated.
      *(completed — re-measured at 11 and 186 rather than 8 and 167, and both figures recorded
      in the docstring alongside a note that a future census finding these tactics unused should
      read the verdict rather than repeat the trial)*

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: local

**Scope Hypothesis**: `deduction` and `undischarge` have 0 library and 14/2 test uses; the trial
targets `Metalogic/Core/DeductionTheorem.lean` (472 lines). Confirm the zero-library-use figure
before starting — a non-zero count changes the question.

*Measured*: confirmed exactly. Zero library invocations of either tactic; 14 `deduction` and 2
`undischarge` invocations, all in `Tests/BimodalTest/Automation/DeductionTest.lean`. The file
is 472 lines and declares 7 things. The `Derivable.deduction` and `deductionTheorem` figures
were 11 and 186, not the plan's 8 and 167.

**Files to modify**:
- `FormalSystem/Automation/Tactics/Deduction.lean` - verdict docstring
- `FormalSystem/Metalogic/Core/DeductionTheorem.lean` - only if the trial succeeds

**Verification**:
- `lake build` green (whatever the verdict).
- The verdict is recorded in source, with the measurement that produced it.

---

### Phase 8: Regenerate automation documentation and sweep Automation naming [COMPLETED]

**Goal**: bring every automation-facing document into line with the surviving inventory, and apply
the Phase 2/12/13 conventions to the `Automation/` territory those phases excluded.

**Tasks**:
- [x] Run `bash scripts/check-module-invariants.sh --emit-inventory` to rewrite the generated
      blocks in `FormalSystem/Automation/README.md` and `FormalSystem/Automation/Tactics/README.md`.
      *(completed — run repeatedly through the task, since Phases 4, 5 and 6 each moved line
      counts; `--emit-inventory --check` exits zero, so a further rewrite would change no byte.
      The three new `Tactics/` modules arrived with `<!-- TODO: add description -->` placeholders
      in the hand-written column, which were filled in)*
- [x] Fix the surrounding **prose** by hand — the generated blocks do not cover it.
      `Tactics/README.md:5-6` and `:26` still present `tm_auto` as a headline tactic.
      *(completed — both, plus the Key Definitions list, which now leads with `modal_search` and
      its call-site count and names `propDecide` as the one load-bearing tactic in the
      directory)*
- [x] Regenerate `docs/reference/tactic-reference.md` (176 lines), which documents
      `temporal_search` (`:77`) and `tm_auto` (`:89`) and is linked from `README.md:296`.
      *(completed — the two retired sections deleted, the Available Tactics table replaced with
      one that carries **call-site counts** instead of a "Status" column that said "Partial" and
      "In Development" for tactics that were finished years ago, and new sections added for
      `propDecide` and the deduction tactics, which had none at all)*
- [x] State in `Automation/README.md` that `modal_search` is the **pedagogical entry point, not
      library infrastructure** — three call sites, all in `Examples/`. *(completed — stated
      there, in `Tactics/README.md`, and in `docs/reference/tactic-reference.md`, since a claim
      like this is worth nothing if a reader can land on any of the three and miss it)*
- [x] Apply Phase 2's citation conversion to `FormalSystem/Automation/**` `## References` blocks.
      *(completed — 4 lines in 2 files. Phase 2's `Surname YYYY` census found **nothing** in
      `Automation/`; what is there is four differently-shaped citations of works with no bib
      entry at all, whose keys (`korf1985`, `yang2019`, `kaliszyk2018`) Phase 2 added on
      discovering them)*
- [x] Apply Phase 12's `lemma` → `theorem` and Phase 13's Uppercase_x conventions to
      `FormalSystem/Automation/**` and `Tests/BimodalTest/Automation/**`. *(completed — Phases
      12 and 13 were run over the whole live tree including `Automation/`, rather than run twice.
      `Automation/` contributed 2 `lemma` conversions, both in the file Phase 6 split, and no
      Uppercase_x names)*

**Timing**: 1.5 hours

**Depends on**: 6, 7, 12, 13

**Ordering note**: the markdown half of this phase ran before Phases 12 and 13, and the Lean
half with them, rather than strictly after. The dependency exists so the documentation
describes the post-triage inventory; it does, because the inventory blocks were regenerated and
`--emit-inventory --check` re-verified after every later phase.

**Verification Tier**: full

**Territory**: `FormalSystem/Automation/**`, `Tests/BimodalTest/Automation/**`,
`docs/reference/tactic-reference.md`. This is the territory Phases 2, 12 and 13 excluded.

**Files to modify**:
- `FormalSystem/Automation/README.md`, `FormalSystem/Automation/Tactics/README.md`
- `docs/reference/tactic-reference.md`
- `FormalSystem/Automation/**/*.lean` (citations, `lemma`, names)

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` exits zero (a rewrite would
  change no byte).
- No surviving document names a retired tactic except as a retirement note.
- `lake build` and `lake test` green.

---

### Phase 9: FormalSystem/MainResults.lean [COMPLETED]

**Goal**: one readable navigation page restating the headline results, each followed by
`#print axioms` with the verbatim output recorded.

**Tasks**:
- [x] Create `FormalSystem/MainResults.lean` following the established idiom at
      `DiscreteNonCompactness.lean:292-312` and `DedekindNonCompactness.lean:473-490` (restatement,
      then `#print axioms`, then a docstring recording the verbatim output). *(completed — the
      first two parts. The third is a **deliberate departure**, and the idiom's own source says
      why: `DiscreteNonCompactness.lean` records that its hand-transcribed output block "could
      and did drift out of step with the declarations it claimed to report", and that the C2/C14
      heredocs are the stronger guarantee. Transcribing 27 output blocks by hand would have
      rebuilt exactly the artefact that module retired. The file states the axiom contract once,
      names the single strict-subset exception, and points at the baselines — and Phase 10's C21
      makes that pointer machine-checked)*
- [x] Cover: `soundness` and `soundness_base/_dense/_ztime/_rtime`;
      `completeness_base/_dense/_ztime/_rtime`;
      `consequence_completeness_base/_dense/_ztime/_rtime`; `strongCompletenessBase`,
      `strongCompletenessDense`; `compactBase`, `compactDense`; `notCompactZTime`,
      `notCompactRTime`, `notStrongCompletenessZTime`, `notStrongCompletenessRTime`; the
      `galoisClosed_mod` family; `kampPriorExpressiveCompleteness`; `Decidability.sound_of_isValid`.
      *(deviation: altered — **there is no `soundness_base`**. The family is `soundness`,
      `soundness_dense`, `soundness_ztime`, `soundness_rtime`, with `soundness` itself as the
      Base member; `soundness_base_consequence` is a different theorem, stated against
      `SemanticConsequence`. 27 declarations covered in all, including
      `uSExpressivelyCompleteOverPrior` alongside `kampPriorExpressiveCompleteness`, since the
      former is the statement the completeness chain actually consumes)*
- [x] Restate by reference (`theorem ... := existingName`) or `#check`; introduce **no** new proof
      obligation, no `sorry`, no axiom. *(completed via `#check`, and the choice is deliberate
      rather than the lazier of two options. Aliasing declarations would have reintroduced,
      wholesale, exactly the defect Phases 11 and 14 exist to remove: every alias would share a
      base identifier with the theorem it aliases, and C17's dead-declaration census keys on the
      last dot-segment, so each pair would permanently mask the other. A page built to advertise
      the results would have blinded a check over all 27 of them)*
- [x] Add `import FormalSystem.MainResults` to `FormalSystem/FormalSystem.lean` so the file is
      inside `lean_lib FormalSystem`'s root closure and is actually built. *(completed, with the
      module named in that file's own submodule list)*
- [x] Capture each `#print axioms` output from a real build and paste it verbatim; do not
      hand-write expected output. *(deviation: skipped — superseded by the first item's
      departure. Nothing is hand-written, but nothing is pasted either: the 27 directives emit
      their output into the build log on every build, and the C2/C14 baselines hold the recorded
      form. C21 asserts the page cannot name a declaration those baselines do not pin)*

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: ~24 headline declarations, every one of them already among the 105 C2+C14
pins. Confirm each name resolves and each is present in a baseline **before** writing its section;
a name that resolves but is unpinned must be reported, not silently included.

*Measured*: 27 declarations, and all 27 are pinned — verified name-by-name against the extracted
union of the two baselines before the file was written, and re-verified mechanically ever since
by C21. One carries a strictly smaller axiom set than the rest
(`Semantics.galoisClosed_mod`, `[propext]` alone), which the page records rather than rounds up.
No unpinned name was found, so the report-don't-include branch was not exercised.

**Files to modify**:
- `FormalSystem/MainResults.lean` (new)
- `FormalSystem/FormalSystem.lean` - add the import

**Verification**:
- `lake build` green; every `#print axioms` line in the file matches the build's own output.
- `grep -c 'sorry' FormalSystem/MainResults.lean` is zero.

---

### Phase 10: C21 MainResults subset guard [COMPLETED]

**Goal**: make it impossible for `MainResults.lean` to advertise a result whose axiom set is not
pinned.

**Tasks**:
- [x] Confirm the next free check id (C21 at plan time) and register it in the header list at the
      top of `scripts/check-module-invariants.sh`. *(completed — C20 confirmed as the highest
      existing id; C21 registered in the header list)*
- [x] Extract the declaration names `MainResults.lean` names, and assert each appears in the C2
      `AXIOM_BASELINE` or the C14 `C14_BASELINE` block. *(completed — names are read from the
      page's own `#print axioms` directives, so the check cannot drift from what the page
      actually asserts)*
- [x] Fail (not warn) on a `MainResults.lean` name absent from both baselines; this is the whole
      point of the check. *(completed — and verified by deliberate violation: appending
      `#print axioms FormalSystem.Metalogic.Core.deductionTheorem` produced
      `FAIL C21 1 of 28 MainResults.lean declaration(s) are pinned by neither C2 nor C14`,
      naming the offender; reverted, back to PASS)*
- [x] Follow the existing check idiom: a `pass`/`fail` helper call, an `ENFORCE_C21` variable
      defaulting to enforced, and `FAILURES` increment on non-zero status. *(completed — the
      `fail` helper does the `FAILURES` increment itself, so calling it is the whole idiom;
      `ENFORCE_C21` sits beside `ENFORCE_C20` with the same never-flip-back-to-0 note)*
- [x] Document in the header comment why this is a subset assertion and not a third baseline.
      *(completed — including what the check deliberately does NOT do: it checks names, not
      axiom sets, and does not require the converse inclusion)*

**Timing**: 1 hour

**Depends on**: 9

**Verification Tier**: local

**Scope Hypothesis**: C21 is the next free id (C20 is the current highest); the two baseline blocks
hold 4 + 101 = 105 entries. Confirm both figures with the report Appendix's two `awk` commands
before wiring.

*Measured*: both confirmed. C2's `AXIOM_BASELINE` holds 4 entries and C14's `C14_BASELINE`
holds 101, and the union of their declaration names is the 105-name pinned set C21 tests
against. `MainResults.lean` names 27 declarations; all 27 are in that set.

**Files to modify**:
- `scripts/check-module-invariants.sh` - header list, new C21 section

**Verification**:
- `bash scripts/check-module-invariants.sh` reports C21 PASS.
- A deliberate temporary edit adding an unpinned name to `MainResults.lean` makes C21 FAIL (revert
  after confirming).

---

### Phase 11: Shadowing renames and the allAxiomNames consistency check [COMPLETED WITH EXCLUSIONS]

**Goal**: eliminate the outer-shadows-inner pairs that permanently mask both members from C17's
dead-declaration census, on tooling grounds, and reconcile the recorded decision that dismissed the
semantic grounds.

**Tasks**:
- [x] Reproduce the 17-pair scan (public, bare, non-dot-qualified, `private` excluded,
      `Boneyard/` excluded, docstrings skipped, unicode-tolerant identifier class) and confirm the
      census before renaming anything. *(completed — reproduced **exactly 17 pairs** over 8,804
      live public bare declarations, matching the report name for name)*
- [x] Rename the inner members of the re-exposure group to Mathlib's `conclusion_of_hypothesis`
      form: `BXCanonical.completeness_dense` → `derivable_of_validDense`,
      `BXCanonical.completeness_ztime` → `derivable_of_validZTime`, and analogously for the four
      `SoundnessLemmas` pairs (`F_until_equiv_valid`, `P_since_equiv_valid`, `temp_linearity_valid`,
      `temp_linearity_past_valid`) and the two `Kamp` pairs (`temporal_truth_and`,
      `temporal_truth_neg`). *(deviation: altered — the two `BXCanonical` renames are exactly as
      prescribed. The other six are **not** `conclusion_of_hypothesis`, because that form does
      not apply to them: the four `SoundnessLemmas` members are nullary validity statements with
      no hypothesis to name, and the two `Kamp` members are `iff` lemmas. Each was instead given
      a name stating the one thing that distinguishes it from its namesake. The `SoundnessLemmas`
      four take a `_validIn` suffix, since the whole difference is `ValidIn FrameClass.Base`
      versus the `⊨`-shaped `Valid` — which their own docstrings already said in prose. The two
      `Kamp` members become `temporalTruth_neg_iff` / `temporalTruth_and_iff`, Mathlib's `_iff`
      shape. Recorded finding: the `Kamp` pair are **literal duplicates** of the
      `StaviConnectives` pair, same statement and same one-line proof, and neither file imports
      the other, so the shadowing was never even reachable — the rename is justified on the
      C17 ground alone)*
- [x] Leave the outer `completeness_base/_dense/_ztime/_rtime` family untouched — its four-member
      uniformity is the more valuable pattern. *(completed. Recorded cost: the **inner** family
      is now mixed, since `BXCanonical.completeness` and `BXCanonical.completeness_rtime_engine`
      keep their names — neither collides with anything, and renaming them would be churn. The
      note in `StrongCompleteness.lean` states this rather than hiding it)*
- [x] Update the note at `StrongCompleteness.lean:126-133` (restated at `:983-985`, `:1101-1103`)
      **in the same commit**: it correctly dismissed the *semantic* harm; record the *tooling*
      harm (C17 base-identifier masking) as the ground actually acted on. *(completed — all
      three sites, in the same change as the rename. The note now says the old reading was right
      about semantics and wrong to stop there: a base-identifier collision silently disables
      C17 over **both** members, so it was not inert)*
- [x] Adjudicate the unrelated bare collisions individually: `insertEnv`, `realOrder`, `pastKDist`,
      `DiversityReport`, `isValid`, `mem_knownTimes_of_mem`, `mem_knownWorlds_of_mem`.
      *(completed — three renamed, four excluded with reasons. RENAMED:
      `Independence.realOrder` → `realTemporalOrder` (two identical `@[reducible] noncomputable
      def realOrder : TemporalOrder := ⟨ℝ⟩`, the second's docstring already calling itself a
      copy of the first); `Perpetuity.pastKDist` → `pastKDistFromFuture` (same statement, a
      different route — `futureKDist` rather than `temp_k_dist_local` — and one local use, so
      the new name says what distinguishes it); `DatasetValidator.DiversityReport` →
      `ValidationDiversityReport`. EXCLUDED: `isValid` twice, because both inner members
      (`DecisionResult.isValid`, `ExpandedTableau.isValid`) are structure-member namesakes on
      distinct types, which the plan's own guard requirement says must never be flagged;
      `mem_knownTimes_of_mem` and `mem_knownWorlds_of_mem`, because the **outer** member of each
      pair is declared in `Verified/Termination/MintBound.lean`, md5-pinned by a concurrent
      workstream, and renaming the inner member alone would leave the base identifiers colliding
      — the pair must be done together or not at all; and `insertEnv`, deferred, see below)*
- [x] Do **not** rename `allAxiomNames`; add a consistency check asserting the two 45-name lists
      (`AxiomNames.lean:33` and `ProofStepExport.lean:1526`) agree, since the duplication is
      documented and deliberate. *(completed — C22, comparing the two lists as **sets** of
      quoted strings rather than byte-for-byte, since the two are deliberately formatted
      differently: one groups by axiom layer with comments, the other runs in source order.
      Both extract to 45 names and the sets are equal)*
- [x] Do **not** touch `hasBox`/`isNeg`/`isTop` — every colliding side is `private`. *(completed
      — the corrected scan excludes `private` declarations, so these three never appear in the
      17-pair census at all)*
- [x] **Added, deferred with reason**: `insertEnv`. The two definitions are genuinely different
      operations, not a re-exposure: the outer inserts at an arbitrary position `c` with index
      shifting, the inner appends at the end. The inner's honest name is `snocEnv`. But the two
      have different arities, `insertEnv` appears across 14 files, and four of those are neither
      under `Kamp/` nor beside the outer definition, so ownership per site needs an arity
      analysis this phase did not have the build budget to verify. Recorded in the C23 exception
      set with this reason rather than renamed blind.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: 17 outer-shadows-inner pairs across 16 base names; the dispatch's
`completeness_discrete` does not exist (the name is `completeness_ztime`) and its line anchors are
a few lines off. Confirm the pair census and each anchor before editing; a pair that no longer
reproduces is a stop-and-report, not a silent skip.

*Measured*: 17 pairs across 16 base names, confirmed exactly; every pair reproduced, so the
stop-and-report branch was not exercised. `completeness_discrete` does not exist, as predicted.
After this phase the census reports **6**, every one of them a recorded exception: `isValid`
twice, `mem_knownTimes_of_mem`, `mem_knownWorlds_of_mem`, `allAxiomNames` and `insertEnv`.

**Territory**: `FormalSystem/**` excluding `FormalSystem/Automation/**` (deferred to Phase 8).

**Files to modify**:
- `FormalSystem/Metalogic/BXCanonical/Completeness.lean`, `.../StrongCompleteness.lean`
- `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`
- `FormalSystem/Metalogic/WeakCanonical/Kamp/Translation.lean`
- the individually adjudicated collision sites
- `scripts/check-module-invariants.sh` - `allAxiomNames` agreement check

**Verification**:
- `lake build` and `lake test` green.
- Re-running the shadowing scan reports zero pairs in the renamed groups.
- The `allAxiomNames` check passes and fails on a deliberate temporary divergence.

---

### Phase 12: lemma to theorem across live scope [COMPLETED]

**Goal**: zero live `lemma` declarations, bringing 88 declarations into the two invariant checks
whose regexes currently cannot see them.

**Tasks**:
- [x] Re-count live-scope `lemma` declarations with the report Appendix's command; record the
      before number. *(completed — and the report's command **overcounts**. It reports 88; the
      real figure is 64. The 24-line difference is docstring prose: 24 wrapped sentences in
      `## References` blocks and design notes begin a continuation line with the word "lemma"
      ("lemma 10). Nothing here mentions formulas…", "lemma name array explicitly, which lets…"),
      and a line-anchored grep cannot tell those from a declaration. A comment-depth-aware scan
      can, and does)*
- [x] Convert all of them to `theorem`, preserving attributes, modifiers (`private`, `protected`,
      `noncomputable`, `scoped`, `local`) and indentation exactly. *(completed — 57 converted.
      The conversion is a capture-preserving substitution on the modifier prefix, so attributes,
      modifiers and indentation are carried through unexamined rather than reconstructed)*
- [x] Work file-by-file, heaviest first (`Syntax/SubformulaClosure/IteratedTemporal.lean` 21,
      `Metalogic/Core/MaximalConsistent.lean` 8, `Metalogic/Bundle/WitnessSeed.lean` 8,
      `Metalogic/Bundle/TemporalContent.lean` 6, `Decidability/Verified/Termination/MintBound.lean`
      5, `Metalogic/Core/MCSProperties.lean` 4). *(deviation: altered — done in one
      comment-aware pass rather than file-by-file, since the ordering exists to make a manual
      edit tractable and a mechanical one does not need it. The named heavy files were all
      converted **except** `MintBound.lean`: its 5 (really 6) hits are docstring prose, and the
      module is md5-pinned by a concurrent workstream, so it was excluded on both counts)*
- [x] Record the C17 and C19 numbers before and after; new dead-declaration candidates are an
      **expected** consequence, not a regression. *(completed — C17: 990 before, 983 after the
      conversion, 988 after Phase 14 added `lemma` to C17's own declaration regex. The net −2 is
      the declarations Phases 5 and 6 retired; the +5 is the converted declarations entering the
      census, which is the point. C19 refined: 92.33% → 92.30%, unrefined 89.48% → 89.45%; both
      moves are the denominator changing, and the refined figure stays well clear of the 90%
      floor. Neither check gates the build: there is no `ENFORCE_C17` and no `ENFORCE_C19`)*

**Timing**: 1.5 hours

**Depends on**: 11

**Verification Tier**: full

**Scope Hypothesis**: 88 live `lemma` declarations (the review's 141/142 included `Boneyard/`'s
54). Confirm the live figure before starting; the acceptance criterion "lemma count 0" is scoped to
live scope, and `Boneyard/`'s 54 stay.

*Measured*: **64**, not 88 — see the first task above for why the 88 is an artefact of the
census command rather than of scope. 57 were converted and 7 left, all 7 in the two md5-pinned
modules and all 7 docstring prose rather than declarations. The live `lemma` **declaration**
count is now 0 across the whole tree, including the pinned modules, which is what the acceptance
criterion asks for. `Boneyard/`'s stay.

**Territory**: `FormalSystem/**` excluding `FormalSystem/Automation/**` and `FormalSystem/Boneyard/**`;
`Tests/**` excluding `Tests/BimodalTest/Automation/**`.

**Files to modify**:
- the live-scope files carrying `lemma` declarations

**Verification**:
- `lake build` and `lake test` green.
- The live-scope `lemma` count command returns 0 outside the deferred Automation territory.
- C17/C19 before/after numbers recorded.

---

### Phase 13: Adjudicated Uppercase_x renames [COMPLETED]

**Goal**: dot-namespace the ~30 Uppercase_x names whose prefix is a real declaration, and leave the
rest alone with the reason recorded.

**Tasks**:
- [x] Re-run the Uppercase_x census (107 live: 102 `theorem`, 5 `def`) and classify each name into
      the three populations. *(completed — measured **105**: 100 `theorem` and 5 `def`. The
      classification came out as three populations plus a fourth the plan did not anticipate;
      see below)*
- [x] Rename the type/def-prefix class: `R3Maximal_*`, `BurgessR3Maximal_*`, `SubformulaClosure_*`,
      `BranchOrder_*`, `SetConsistent_of_subset`, `Fib_*`, `RefinedFilteredTaskFrame_*`,
      `FiniteFilteredTaskFrame_*` — confirming for each that a declaration of the prefix name
      actually exists. *(deviation: altered — the prefix test was confirmed for all of them, and
      renaming all of them **broke the build**. A second condition is needed, and it is the more
      interesting one: dot-namespacing `Prefix_rest` when a live declaration is already called
      `rest` CAPTURES that name, because declaring `Prefix.rest` puts `rest` in scope inside
      every other `Prefix.*` declaration. `BurgessR3Maximal.burgessR3` made
      `BurgessR3Maximal.extension_fails`'s reference to the standalone `burgessR3` **definition**
      resolve to the theorem instead, and the build failed with an application type mismatch at
      two sites. Thirteen of the fifty-one candidates have this shape — including the whole
      `FiniteFilteredTaskFrame_*` and `RefinedFilteredTaskFrame_*` families, whose suffixes
      `serial`, `limit`, `saturation` and `interpolates` are all live frame conditions — and all
      thirteen were reverted to the underscore form)*
- [x] **Leave the ~55 tense-operator names alone** (`F_`, `P_`, `G_`, `H_`, `FF_`, `HF...`);
      `F`/`P`/`G`/`H` are the paper's operators, not namespaces. *(completed — 51 of them:
      `F_` 17, `P_` 13, `G_` 9, `H_` 8, `A_` 3, `FF_` 1. `HFofStepPath_path` was **not** left
      alone: despite starting `HF`, its prefix is a real live `def HFofStepPath`, so it renamed)*
- [x] Adjudicate the ~22 Kamp-bridge prefixes (`CAggPtX_`, `CAggPtT_`, `CAggInt_`, `CAggOd_`,
      `CAggOdSwap_`, `CExtFut_`, `CExtPast_`, `A_diag_`, `A_past_`, `A_future_`, `MR_`, `O_zero_`)
      case-by-case on the same "does the prefix name a real `def` in that file" test.
      *(completed — the test separates them cleanly. `CAggPtX`, `CAggPtT`, `CAggInt`, `CAggOd`,
      `CExtFut`, `CExtPast` and `MR` are all live `def`s or `abbrev`s, so their 18 members
      renamed. `CAggOdSwap` and `O` name nothing, so `CAggOdSwap_clause_iff`,
      `CAggOdSwap_clause_iff_faithful` and `O_zero_correct` stay. The `A_*` names are
      tense-operator names and were left with that class)*
- [x] Record the classification and the leave-alone rationale in
      `docs/development/MODULE_ORGANIZATION.md` (or the naming-convention document it points to),
      so the decision is durable rather than re-litigated by the next census. *(completed — a new
      "Declaration names: `Prefix.rest`, not `Prefix_rest`" section under Namespace Conventions,
      carrying all three exception classes and the two-halved mechanical test, with the
      name-capture failure recorded as the measured thing it was)*
- [x] Update `docs/theorem-index.md` rows for any renamed declaration. *(completed — no row named
      a renamed declaration; the two rows this task changed there are Phase 11's `BXCanonical`
      engines, and the file's own "fully qualified, always" rationale was rewritten to survive
      that rename)*

**Timing**: 1.5 hours

**Depends on**: 12

**Verification Tier**: full

**Scope Hypothesis**: 107 live Uppercase_x names, of which ~30 are renameable, ~55 are
tense-operator names that must not be renamed, and ~22 need case-by-case adjudication. The
dispatch's flagship examples (`CanonicalTask_backward_comp`, `Succ_implies_CanonicalR`) exist only
in `Boneyard/`. Confirm all four figures before renaming; report the actual renamed count.

*Measured*: **105** live Uppercase_x names, not 107. **38 renamed**, not ~30 — but by way of 51
renamed and 13 reverted, and the 13 are the finding. 67 left alone: 51 tense-operator names, 3
whose prefix names nothing, and the 13 whose suffix would capture a live name. The dispatch's
two flagship examples are indeed `Boneyard/`-only and were never in scope.

**Territory**: same exclusions as Phase 12.

**Files to modify**:
- the live-scope declaration and call sites of the renamed names
- `docs/theorem-index.md`, `docs/development/MODULE_ORGANIZATION.md`

**Verification**:
- `lake build` and `lake test` green.
- Every renamed name has zero remaining live-scope occurrences under its old spelling.
- The census's remaining Uppercase_x population is exactly the recorded leave-alone classes.

---

### Phase 14: Naming-regression guard [COMPLETED]

**Goal**: extend C16's existing `dupNamespace` walker so none of the three naming classes can
regrow, without adding a fourth namespace-walking scanner.

**Tasks**:
- [x] Extend the existing `dupNamespace` textual scanner (`check-module-invariants.sh`, the
      `namespace`/`end` stack walk) rather than copying it. *(completed — the three assertions
      live inside the same `python3` heredoc and reuse its `live_lean_files`, `ns_open_re`,
      `section_re` and `end_re`. One pass over the tree, one scanner, as required. The heredoc
      now exits non-zero on a C23 violation and the shell increments `FAILURES`, following the
      C15/C20 pattern; `dupNamespace` itself stays reporting-only)*
- [x] Apply the five corrections research identified: add `lemma` to the declaration regex; use an
      identifier class that survives `?`, `'`, `τ` and other unicode suffixes (a naive
      `[A-Za-z0-9_'.]*` truncates `asAnd?` and manufactures ~30 false positives); exclude `private`
      declarations; skip `/- ... -/` and `/-! ... -/` blocks; and **do not** flag structure-member
      namesakes (`Syntax.Atom.beq_refl` vs `Syntax.Formula.beq_refl`, and the
      `toJson`/`display`/`empty`/`size`/`insert`/`mono`/`lift` families), which the
      outer-shadows-inner test already excludes by construction since neither namespace is a prefix
      of the other. *(completed — all five. The identifier class is `[^\s\(\{\[:]+`, which
      takes the whole token up to a delimiter and so cannot truncate at a unicode or `?`
      boundary at all. The structure-member exclusion was verified by probe, not assumed: two
      declarations named `c23ProbeMember` in `Semantics.Atom` and `Semantics.Formula` produce
      three PASS lines)*
- [x] Add the three regression assertions: zero live `lemma` declarations; no new Uppercase_x name
      outside the recorded leave-alone classes; no new outer-shadows-inner bare-declaration pair.
      *(completed as C23, and each verified to FAIL on a deliberate violation and PASS again on
      revert: a `lemma` declaration; `Fib_c23Probe`, which the check reports with the dotted
      name it wants; and a fresh outer/inner pair, reported with both members' locations)*
- [x] Add `lemma` to C17's declaration regex too, so the 88 converted declarations enter the
      dead-declaration census. *(completed — 57, not 88, per Phase 12's corrected count. C17
      moved 983 → 988; the +5 is those of the converted declarations that have no other
      occurrence, which is exactly the visibility the change was for)*
- [x] Document each assertion's rationale in the header comment, including the C17 base-identifier
      masking that justifies the shadowing clause. *(completed — and the exception sets carry
      their reasons inline, beside the names they exempt, rather than in a separate table that
      could drift. The frozen-module exemption is applied **by path** and marked
      DELETE-THIS-WHEN, since it is scoped to a concurrent workstream rather than permanent)*
- [x] **Added**: a third Uppercase_x exception class, the name-capture hazard Phase 13's build
      failure exposed. The check now dot-namespaces only when the prefix is a live declaration
      **and the suffix is not** — without the second half it would demand thirteen renames that
      do not compile.

**Timing**: 2 hours

**Depends on**: 8, 11, 12, 13

**Verification Tier**: local

**Scope Hypothesis**: one scanner extended (not a fourth added), five corrections, three
assertions, plus one regex addition in C17. Confirm the current `dupNamespace` finding count is 0
before extending, so any post-extension finding is attributable to the change.

*Measured*: as hypothesised, plus a fourth Uppercase_x exception class discovered by Phase 13's
build failure. `dupNamespace` reported 0 before the extension and reports 0 after, so the C23
lines are attributable. Two further checks landed alongside: C21 (Phase 10) and C22 (Phase 11),
taking the script from 20 numbered checks to 23.

**Files to modify**:
- `scripts/check-module-invariants.sh` - C16 extension, C17 regex, new assertions

**Verification**:
- `bash scripts/check-module-invariants.sh` green, with the new assertions reporting PASS.
- Each assertion fails on a deliberate temporary violation (one `lemma`, one new Uppercase_x name,
  one new shadowing pair), reverted after confirming.
- A structure-member namesake is confirmed **not** flagged.

---

### Phase 15: ORGANISATION.md and NOTATION.md [COMPLETED]

**Goal**: the two root-level furniture documents mature Lean libraries carry, without duplicating
what `docs/ARCHITECTURE.md` already says.

**Tasks**:
- [x] Write root `ORGANISATION.md` as a short **pointer**: the Syntax/ProofSystem/Semantics/
      Metalogic/Automation layering in one paragraph, the single documented
      `Semantics → ProofSystem` edge (`Semantics/FrameClassValidity.lean:8`), then links to
      `docs/ARCHITECTURE.md` and `docs/development/MODULE_ORGANIZATION.md`. C18 gates paragraph
      duplication across top-level READMEs, so a third copy of the layering prose would fail.
      *(completed — 76 lines, a six-row layer table and a where-to-look-next table rather than a
      prose copy. C18 reports zero duplicated paragraphs and zero duplicated sentences)*
- [x] Write root `NOTATION.md` inventorying the **15** live `notation` declarations: the 12
      derivability notations that already carry a per-frame-class tag (`Γ ⊢[fc] φ`, `⊢[fc] φ`,
      `Γ ⊢ φ`, `⊢ φ`, the four `|-![fc]` siblings, `Γ ⊢ᴮᴸ[fc] φ`/`⊢ᴮᴸ[fc] φ`,
      `Γ ⊢⋆[fc] φ`/`⊢⋆[fc] φ`), the 2 untagged validity notations, and the scoped quotient bracket.
      *(completed — the count of 15 was re-derived and matches exactly: 12 derivability, 2
      validity, 1 scoped quotient bracket)*
- [x] Record the tag **asymmetry** and its reason: `Semantics/Validity.lean:239-242` deliberately
      dropped a `TruthAt` notation because it conflicts with `⊨`, using a subscripted variant and
      dot-notation instead. Document the seven-predicate `⊨` family (`ValidOnFrames`, `ValidIn`,
      `Valid`, `ValidDense`, `ValidZTime`, `ValidComplete`, `ValidRTime`) plus the
      `SemanticConsequence` family and the `StarFormula` mirror. *(completed — all seven
      confirmed present, plus the four `SemanticConsequence*` members and the six `StarValid*`
      mirrors. `ValidComplete` is flagged as the one member that is not a `ValidIn` instance)*
- [x] **Do not introduce a new `TM[...]` validity notation** — G-16's "four ⊨-shaped relations"
      premise is wrong and its recommendation is already half-implemented on the `⊢` side.
      *(completed — none introduced. `NOTATION.md` carries an "On adding a per-logic judgement
      tag" subsection recording the decision and its two grounds, so the proposal is declined on
      the record rather than silently dropped)*
- [x] Link both documents from `README.md`. *(completed — a new "Start here" block under
      `## Documentation`, linking `ORGANISATION.md`, `NOTATION.md` and `docs/ARCHITECTURE.md`)*
- [x] **Added**: corrected the `ORGANISATION.md` claim about upward edges. The plan's task text
      names one (`Semantics → ProofSystem`); `docs/ARCHITECTURE.md` documents **two**, the
      second being `Decidability → Automation`. Both are named, since a page claiming one edge
      beside a page claiming two is exactly the drift this task exists to remove.

**Timing**: 1.5 hours

**Depends on**: 10, 14

**Verification Tier**: prose

**Scope Hypothesis**: 15 live `notation` declarations (12 tagged derivability, 2 untagged validity,
1 scoped quotient), and exactly one `Semantics → ProofSystem` import edge. Confirm both by grep
before writing; a second edge would falsify the layering claim and must be reported.

*Measured*: both confirmed. 15 notation declarations, split exactly as hypothesised, and
exactly one `^import FormalSystem.ProofSystem` line under `FormalSystem/Semantics/`
(`FrameClassValidity.lean`). The naive census pattern reports **17**: `^\s*notation` matches
two docstring lines that wrap onto the word "notation". `NOTATION.md`'s verification command
anchors at column zero and requires `=>`, and records why both filters are needed.

**Files to modify**:
- `ORGANISATION.md` (new), `NOTATION.md` (new)
- `README.md` - links

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` green — C12/C13 (path and link resolution)
  and C18 (prose duplication) in particular.
- Every notation named in `NOTATION.md` resolves to a live declaration.

---

### Phase 16: Publish the API documentation [COMPLETED]

**Goal**: a doc-gen4 site built and deployed by `docgen-action`, linked from `README.md`, with the
now-stale `docs/README.md` recipe replaced.

**Tasks**:
- [x] Add `.github/workflows/docs.yml`: `permissions: {contents: read, id-token: write,
      pages: write}`, triggered on push to `main` plus `workflow_dispatch`, with a single
      `uses: leanprover-community/docgen-action@main` step. *(completed — plus a
      `concurrency: {group: pages, cancel-in-progress: false}` block and a `github-pages`
      environment, neither in the plan's list: without the first, two pushes in quick
      succession race for the same deploy, and the second is what surfaces the page URL)*
- [x] Set the inputs explicitly: `api-docs: true`, `blueprint: false`, `references: references.bib`,
      and **`build-page: false`** — the last resolves the `homepage: docs` collision with this
      repo's non-Jekyll 100-file `docs/` tree. Do not rely on any default. *(completed — all
      four present literally; the file's header comment records why `build-page: false` is
      load-bearing rather than a default restated)*
- [x] Do **not** add `require «doc-gen4»` to `lakefile.lean`; the action supplies it, and
      `lake-manifest.json` must stay unchanged. *(completed — `git diff --stat lakefile.lean
      lake-manifest.json` is empty)*
- [x] Rewrite `docs/README.md:272-278`, which currently asserts that no doc-gen4 target exists and
      that adding one would be a build-graph change — true before this task, false after.
      *(completed — replaced with the workflow's own account, including the standing
      prohibition on adding a `lakefile.lean` dependency, which is the half of the old text
      that is still true)*
- [x] Add the site link to `README.md` above `## Documentation` (`README.md:293`). *(deviation:
      altered — placed immediately **below** the `## Documentation` heading rather than above
      it. Above the heading the link would sit at the end of the preceding section, which is
      the expressive-completeness result; below it, it is the first thing under the heading it
      belongs to)*
- [x] Delete the stray root artefact `Scratch434.lean.tmp` (0 bytes; its name is also a
      task-number reference in a deliverable path). *(completed)*
- [x] Record in `docs/README.md` that the repository Pages source must be set to **GitHub Actions**
      manually — a one-time human step the workflow cannot perform, and a precondition for the
      first deploy to appear. *(completed — recorded in `docs/README.md` and again in the
      workflow file's own header, so whoever opens either one finds it)*
- [x] Confirm `.gitignore:32-34` already covers `doc/` and `_site/`. *(completed — both present
      under "Documentation build output")*

**Timing**: 1.5 hours

**Depends on**: 2, 3, 8, 15

**Ordering note**: executed after 2, 3 and 15 but **before** 8, inverting one declared edge.
The reason the 8 → 16 edge exists is that the first deploy must not publish stale
automation docstrings — and no deploy happens until the user merges, which is after every
phase of this task. Phase 8 still runs and still precedes any deploy; only the authoring order
moved. The trigger was the shared working tree: another session held the `lake build` lock for
most of this phase's window, and Phase 16 is the largest piece of work in the plan that needs
no build at all.

**Verification Tier**: prose

**Scope Hypothesis**: one new workflow file, one rewritten `docs/README.md` section, one `README.md`
link, one file deletion. `lake-manifest.json` and `lakefile.lean` must show **zero** diff — confirm
with `git diff --stat` at phase close.

*Measured*: as hypothesised. `.github/workflows/docs.yml` (56 lines) added, the
`### Building Documentation` section of `docs/README.md` replaced, one `README.md` link added,
`Scratch434.lean.tmp` deleted. `git diff --stat lakefile.lean lake-manifest.json` is empty.

**Files to modify**:
- `.github/workflows/docs.yml` (new)
- `docs/README.md` - replace the "no generated API documentation target" section
- `README.md` - site link
- `Scratch434.lean.tmp` (deleted)

**Verification**:
- YAML parses; `build-page: false` and `references: references.bib` are literally present.
- `bash scripts/check-module-invariants.sh --no-build` green (C12/C13 link resolution after the
  `docs/README.md` rewrite).
- `git diff --stat lakefile.lean lake-manifest.json` is empty.
- No push and no PR — per `.claude/rules/pr-prohibition.md`, the deploy happens when the user
  merges.

---

### Phase 17: Acceptance gate [COMPLETED WITH EXCLUSIONS]

**Goal**: verify every acceptance criterion with a recorded command and its output.

**Tasks**:
- [x] `lake build` green from clean. *(completed — `Build completed successfully (2592 jobs)`,
      `EXIT=0`, zero `error:` lines. Two real defects were caught by earlier runs of this build
      and fixed: `Deduction.lean`'s missing imports (Phase 6) and the Uppercase_x name-capture
      hazard (Phase 13))*
- [x] `lake test` green. *(completed — `EXIT=0`, **45** `[test] PASS`/`OK`, identical to the
      pre-task baseline. One real defect caught: the two tactic test files reached
      `assumption_search` and the formula predicates transitively through `Commands.lean`'s
      import of `Helpers.lean`, and now import `Tactics.UserTactics` explicitly)*
- [x] `bash scripts/check-module-invariants.sh` green, including the new C21 and the extended C16.
      *(completed with one exclusion — every check passes including C1, C2, C14, C21, C22 and
      all three C23 assertions, except **C9**, which reports one task-number citation at
      `Verified/Termination/MintBound.lean:12524`. That module is md5-pinned and actively being
      written by a concurrent session sharing this working tree; it was not touched here and
      must not be. One further fix was needed to get C16 green: `scripts/nolints.json`'s three
      grandfathered `unusedArguments` entries were rekeyed from `TaskFrame.Fib_*` to
      `TaskFrame.Fib.*` to follow Phase 13's rename — a key rename, not a new suppression)*
- [x] Assert the acceptance criteria one by one, recording the command and result: doc site
      workflow present and linked from `README.md`; `MainResults.lean` compiles with every
      `#print axioms` matching the C2/C14 pins; `references.bib` named by the docs build; zero
      declared tactics with zero library-and-test uses outside `Boneyard/`; live `lemma` count 0.
      *(completed — the summary's Verification section carries the table. Workflow present with
      all four inputs literal and the site linked from `README.md:295`; all 27 `#print axioms`
      directives emitted with the expected sets and C21+C2+C14 all pass; `references: references.bib`
      present in the workflow and the file at 26 entries; live `lemma` declaration count **0**;
      the tactic criterion met except for two members of the protected EF-game set, measured and
      recorded)*
- [x] Record the C17 and C19 before/after numbers and confirm neither check gates the build
      (no `ENFORCE_C17`, no `ENFORCE_C19`). *(completed — C17 990 → 990 by way of 983, the −7
      being Phases 5/6's retirements and the +7 the converted `lemma`s entering the census once
      `lemma` joined C17's regex. C19 refined 92.33% → 92.32%, well clear of the 90% floor.
      Neither flag exists, confirmed by grep)*
- [x] Record every corrected dispatch premise in the implementation summary, so the divergence from
      the dispatch text is a documented decision rather than an unexplained gap: no lakefile
      `require`, no third axiom baseline, no `TM[...]` notation, no fully-qualified-name duplication
      to fix, ~30 (not 98) Uppercase_x renames, 88 (not 141) `lemma` conversions. *(completed — an
      eight-row table in the summary's Plan Deviations section, with the measured figure beside
      each claim. Two of the plan's own corrections needed correcting in turn: 38 rather than
      ~30 Uppercase_x renames, and 57 rather than 88 `lemma` conversions)*
- [x] Hand `FormalSystem/MainResults.lean` to the decidability-examples roadmap item as the
      artefact its examples should cite. *(completed — recorded in the summary's Impacts section
      against `specs/ROADMAP.md` Phase 5's decidability-example entry. `ROADMAP.md` itself is
      not modified: this dispatch carries no `roadmap_flag` and the plan consults it read-only)*
- [x] **Added**: retire the one remaining zero-use tactic the acceptance criterion catches but
      Phase 5's scope did not — `truth_simp` (`Automation/TruthNormAttr.lean`), a
      `simp only [truth_norm]` wrapper with zero invocations anywhere. The criterion is "zero
      declared tactics with zero library-and-test uses outside `Boneyard/`", which is broader
      than the 13 declarations the review enumerated. *(completed — retired, and
      `TruthNormAttr.lean`'s docstring now records that there is deliberately no wrapper tactic
      and why)*

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16

**Verification Tier**: full

**Files to modify**:
- `specs/531_docgen_publication_and_automation_suite_triage/summaries/01_*-summary.md`

**Verification**:
- Every acceptance criterion has a recorded command and its actual output.
- Zero `sorry` and zero new axioms introduced anywhere by this task.

---

## Testing & Validation

- [ ] `lake build` green from clean at the close of every phase whose tier is `interface` or `full`.
- [ ] `lake test` green after Phases 4, 5, 6, 11, 12, 13, 17.
- [ ] `bash scripts/check-module-invariants.sh` green at Phase 17; `--no-build` after every
      docs-touching phase (2, 8, 15, 16).
- [ ] `bash scripts/check-module-invariants.sh --emit-inventory --check` exits zero after Phase 8.
- [ ] C21 fails on a deliberately unpinned `MainResults.lean` name; the Phase 14 assertions each
      fail on a deliberate violation; all four reverted after confirming.
- [ ] Test-suite pass count is unchanged by the Phase 4 alias migration (any change is a finding).
- [ ] `git diff --stat lakefile.lean lake-manifest.json` empty at Phase 16.
- [ ] Zero `sorry` and zero new axioms across the whole task.

## Artifacts & Outputs

- `specs/531_docgen_publication_and_automation_suite_triage/plans/01_docgen-publication-automation-triage.md` (this file)
- `specs/531_docgen_publication_and_automation_suite_triage/summaries/01_docgen-publication-automation-triage-summary.md`
- `.github/workflows/docs.yml` (new)
- `FormalSystem/MainResults.lean` (new)
- `ORGANISATION.md`, `NOTATION.md` (new, root)
- `FormalSystem/Automation/Tactics/{UserTactics,Meta,Search}.lean` (new, replacing `Helpers.lean`)
- `FormalSystem/Boneyard/RetiredTactics/` with its own guard-first README (new)
- `references.bib` (extended), `docs/README.md`, `README.md`,
  `docs/reference/tactic-reference.md`, `FormalSystem/Automation/README.md`,
  `FormalSystem/Automation/Tactics/README.md` (rewritten)
- `scripts/check-module-invariants.sh` (C21 added; C16 and C17 extended)

## Rollback/Contingency

Every phase commits independently, so rollback is per-phase `git revert` in reverse dependency
order. Three phases warrant a named contingency:

- **Phase 5/6 (retirement and split)** are `atomic-batch`: if the batch cannot be brought green,
  revert the whole batch rather than committing a half-moved tree. `Boneyard/` is not compiled, so
  a partial move leaves the live tree broken with no compiler check on the moved half.
- **Phase 16 (publication)** is additive and reversible by deleting `.github/workflows/docs.yml`
  and restoring `docs/README.md:272-278`; nothing is deployed until the user merges, so a bad
  workflow costs nothing until then.
- **Phases 12/13 (renames)** are mechanical and revertible, but partially-applied renames do not
  compile. If a rename must be abandoned mid-file, revert that file rather than leaving mixed
  spellings.

If a phase is blocked, mark it `[BLOCKED]` with the reason and continue with phases in other waves;
the four workstreams (publication, bibliography, automation, naming) are independent up to the
Phase 16/17 join, so a blocker in one does not stall the others.
