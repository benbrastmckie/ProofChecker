# Implementation Plan: Task #531

- **Task**: 531 - docgen publication and automation suite triage
- **Status**: [IMPLEMENTING]
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

### Phase 5: Retire the zero-use tactics and the dead Aesop rule set [NOT STARTED]

**Goal**: move every remaining tactic with zero library-and-test uses, plus the consumer-less
`TMLogic` Aesop rule set, into a documented guard-first `Boneyard/` exception directory.

**Tasks**:
- [ ] Create `FormalSystem/Boneyard/RetiredTactics/` with a README stating it is **guard-first**
      (like `BundleDeadHalf/`), why each artefact was retired, and the measured usage that
      justified it.
- [ ] Add the new directory to `FormalSystem/Boneyard/README.md`'s exception list so the
      event-first banner stays true.
- [ ] Move the seven zero-use `Normalization.lean` tactics (`modalNorm`, `propNorm`, `modalOpNorm`,
      `temporalNorm`, `modalNormAt`, `modalNormAll`, `modalFold`) and any declarations that become
      dead with them.
- [ ] Move `modal_k_tactic`, `temporal_k_tactic`, `modal_4_tactic`, `modal_b_tactic` (and the
      `mkOperatorKTactic` factory if nothing else uses it) out of `Tactics/Helpers.lean`, migrating
      or deleting their ~17 test sites.
- [ ] Move `FormalSystem/Automation/AesopRules.lean` and `FormalSystem/Automation/AesopRuleSet.lean`
      wholesale (zero consumers), and drop their imports from `FormalSystem/Automation.lean`.
- [ ] Confirm nothing under `Boneyard/` is reachable from `lakefile.lean`'s `FormalSystem` root.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 13 tactic declarations plus 2 whole files (291 + 31 lines) retired, ~17 test
sites affected. Confirm the "zero library AND test uses" premise per declaration immediately before
moving each one; a non-zero count is a stop condition, not a formality.

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

### Phase 6: Split Helpers.lean [NOT STARTED]

**Goal**: replace the 1,210-line `Helpers.lean` with `Tactics/{UserTactics,Meta,Search}.lean`,
moving declarations (the three ranges interleave, so line-boundary cuts are impossible).

**Tasks**:
- [ ] Classify every surviving declaration into user tactics, reusable `MetaM` plumbing, or search
      engine, using the report's Finding 6(e) inventory as the starting classification.
- [ ] Create `Tactics/UserTactics.lean` (`apply_axiom`, `modal_t`, `assumption_search`, the
      formula predicates and extractors).
- [ ] Create `Tactics/Meta.lean` (`extractDerivationGoal`, `formulaHead`, `lemmaConclusionHead`,
      `isNilContext`, `buildContextExpr`) — the only part `PropDecide.lean` and `Commands.lean`
      reuse.
- [ ] Create `Tactics/Search.lean` (`tryAxiomMatch`, `tryLemmaMatchCore`, `tryLemmaMatch`,
      `tryAssumptionMatch`, the implication/context extractors, `tryModusPonens`, `tryModalK`,
      `tryTemporalK`, `searchProof`).
- [ ] Delete `Helpers.lean` and repoint `Commands.lean` (needs `Meta` + `Search`) and
      `PropDecide.lean` (needs `Meta` only).
- [ ] Drop `Deduction.lean`'s `import ... Helpers` — it uses nothing from it.
- [ ] Record whether `Search.lean` duplicates `ProofSearch/`'s responsibility; if so, note it as a
      follow-up rather than merging in this task.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: ~24 surviving declarations across three destination files; exactly three
importers of `Helpers.lean` (`Commands.lean`, `PropDecide.lean`, `Deduction.lean`), of which one
is a dead import. Confirm the importer set with
`grep -rn 'Tactics.Helpers' --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard` before
starting.

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

### Phase 7: Time-boxed deduction/undischarge trial [NOT STARTED]

**Goal**: decide, on evidence, whether the `deduction`/`undischarge` tactic forms should be adopted
in `Metalogic/Core/DeductionTheorem.lean`, and record the verdict either way.

**Tasks**:
- [ ] Identify the `DerivationTree`-valued (`Type`-valued) hot spots in
      `Metalogic/Core/DeductionTheorem.lean` where the tactic form could apply.
- [ ] Attempt the conversion on two or three of them; measure whether the `noncomputable`
      infection documented at `Deduction.lean:32-38` propagates.
- [ ] **Hard stop at one hour.** Record the verdict in `Tactics/Deduction.lean`'s module docstring:
      either adopted (with the converted sites) or declined (with the measured reason).
- [ ] If declined, state explicitly that `Derivable.deduction` (8 uses) and the `deductionTheorem`
      term form (167 uses) remain the recommended route, so the file is not re-litigated.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: local

**Scope Hypothesis**: `deduction` and `undischarge` have 0 library and 14/2 test uses; the trial
targets `Metalogic/Core/DeductionTheorem.lean` (472 lines). Confirm the zero-library-use figure
before starting — a non-zero count changes the question.

**Files to modify**:
- `FormalSystem/Automation/Tactics/Deduction.lean` - verdict docstring
- `FormalSystem/Metalogic/Core/DeductionTheorem.lean` - only if the trial succeeds

**Verification**:
- `lake build` green (whatever the verdict).
- The verdict is recorded in source, with the measurement that produced it.

---

### Phase 8: Regenerate automation documentation and sweep Automation naming [NOT STARTED]

**Goal**: bring every automation-facing document into line with the surviving inventory, and apply
the Phase 2/12/13 conventions to the `Automation/` territory those phases excluded.

**Tasks**:
- [ ] Run `bash scripts/check-module-invariants.sh --emit-inventory` to rewrite the generated
      blocks in `FormalSystem/Automation/README.md` and `FormalSystem/Automation/Tactics/README.md`.
- [ ] Fix the surrounding **prose** by hand — the generated blocks do not cover it.
      `Tactics/README.md:5-6` and `:26` still present `tm_auto` as a headline tactic.
- [ ] Regenerate `docs/reference/tactic-reference.md` (176 lines), which documents
      `temporal_search` (`:77`) and `tm_auto` (`:89`) and is linked from `README.md:296`.
- [ ] State in `Automation/README.md` that `modal_search` is the **pedagogical entry point, not
      library infrastructure** — three call sites, all in `Examples/`.
- [ ] Apply Phase 2's citation conversion to `FormalSystem/Automation/**` `## References` blocks.
- [ ] Apply Phase 12's `lemma` → `theorem` and Phase 13's Uppercase_x conventions to
      `FormalSystem/Automation/**` and `Tests/BimodalTest/Automation/**`.

**Timing**: 1.5 hours

**Depends on**: 6, 7, 12, 13

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

### Phase 9: FormalSystem/MainResults.lean [NOT STARTED]

**Goal**: one readable navigation page restating the headline results, each followed by
`#print axioms` with the verbatim output recorded.

**Tasks**:
- [ ] Create `FormalSystem/MainResults.lean` following the established idiom at
      `DiscreteNonCompactness.lean:292-312` and `DedekindNonCompactness.lean:473-490` (restatement,
      then `#print axioms`, then a docstring recording the verbatim output).
- [ ] Cover: `soundness` and `soundness_base/_dense/_ztime/_rtime`;
      `completeness_base/_dense/_ztime/_rtime`;
      `consequence_completeness_base/_dense/_ztime/_rtime`; `strongCompletenessBase`,
      `strongCompletenessDense`; `compactBase`, `compactDense`; `notCompactZTime`,
      `notCompactRTime`, `notStrongCompletenessZTime`, `notStrongCompletenessRTime`; the
      `galoisClosed_mod` family; `kampPriorExpressiveCompleteness`; `Decidability.sound_of_isValid`.
- [ ] Restate by reference (`theorem ... := existingName`) or `#check`; introduce **no** new proof
      obligation, no `sorry`, no axiom.
- [ ] Add `import FormalSystem.MainResults` to `FormalSystem/FormalSystem.lean` so the file is
      inside `lean_lib FormalSystem`'s root closure and is actually built.
- [ ] Capture each `#print axioms` output from a real build and paste it verbatim; do not
      hand-write expected output.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: ~24 headline declarations, every one of them already among the 105 C2+C14
pins. Confirm each name resolves and each is present in a baseline **before** writing its section;
a name that resolves but is unpinned must be reported, not silently included.

**Files to modify**:
- `FormalSystem/MainResults.lean` (new)
- `FormalSystem/FormalSystem.lean` - add the import

**Verification**:
- `lake build` green; every `#print axioms` line in the file matches the build's own output.
- `grep -c 'sorry' FormalSystem/MainResults.lean` is zero.

---

### Phase 10: C21 MainResults subset guard [NOT STARTED]

**Goal**: make it impossible for `MainResults.lean` to advertise a result whose axiom set is not
pinned.

**Tasks**:
- [ ] Confirm the next free check id (C21 at plan time) and register it in the header list at the
      top of `scripts/check-module-invariants.sh`.
- [ ] Extract the declaration names `MainResults.lean` names, and assert each appears in the C2
      `AXIOM_BASELINE` or the C14 `C14_BASELINE` block.
- [ ] Fail (not warn) on a `MainResults.lean` name absent from both baselines; this is the whole
      point of the check.
- [ ] Follow the existing check idiom: a `pass`/`fail` helper call, an `ENFORCE_C21` variable
      defaulting to enforced, and `FAILURES` increment on non-zero status.
- [ ] Document in the header comment why this is a subset assertion and not a third baseline.

**Timing**: 1 hour

**Depends on**: 9

**Verification Tier**: local

**Scope Hypothesis**: C21 is the next free id (C20 is the current highest); the two baseline blocks
hold 4 + 101 = 105 entries. Confirm both figures with the report Appendix's two `awk` commands
before wiring.

**Files to modify**:
- `scripts/check-module-invariants.sh` - header list, new C21 section

**Verification**:
- `bash scripts/check-module-invariants.sh` reports C21 PASS.
- A deliberate temporary edit adding an unpinned name to `MainResults.lean` makes C21 FAIL (revert
  after confirming).

---

### Phase 11: Shadowing renames and the allAxiomNames consistency check [NOT STARTED]

**Goal**: eliminate the outer-shadows-inner pairs that permanently mask both members from C17's
dead-declaration census, on tooling grounds, and reconcile the recorded decision that dismissed the
semantic grounds.

**Tasks**:
- [ ] Reproduce the 17-pair scan (public, bare, non-dot-qualified, `private` excluded,
      `Boneyard/` excluded, docstrings skipped, unicode-tolerant identifier class) and confirm the
      census before renaming anything.
- [ ] Rename the inner members of the re-exposure group to Mathlib's `conclusion_of_hypothesis`
      form: `BXCanonical.completeness_dense` → `derivable_of_validDense`,
      `BXCanonical.completeness_ztime` → `derivable_of_validZTime`, and analogously for the four
      `SoundnessLemmas` pairs (`F_until_equiv_valid`, `P_since_equiv_valid`, `temp_linearity_valid`,
      `temp_linearity_past_valid`) and the two `Kamp` pairs (`temporal_truth_and`,
      `temporal_truth_neg`).
- [ ] Leave the outer `completeness_base/_dense/_ztime/_rtime` family untouched — its four-member
      uniformity is the more valuable pattern.
- [ ] Update the note at `StrongCompleteness.lean:126-133` (restated at `:983-985`, `:1101-1103`)
      **in the same commit**: it correctly dismissed the *semantic* harm; record the *tooling*
      harm (C17 base-identifier masking) as the ground actually acted on.
- [ ] Adjudicate the unrelated bare collisions individually: `insertEnv`, `realOrder`, `pastKDist`,
      `DiversityReport`, `isValid`, `mem_knownTimes_of_mem`, `mem_knownWorlds_of_mem`.
- [ ] Do **not** rename `allAxiomNames`; add a consistency check asserting the two 45-name lists
      (`AxiomNames.lean:33` and `ProofStepExport.lean:1526`) agree, since the duplication is
      documented and deliberate.
- [ ] Do **not** touch `hasBox`/`isNeg`/`isTop` — every colliding side is `private`.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: 17 outer-shadows-inner pairs across 16 base names; the dispatch's
`completeness_discrete` does not exist (the name is `completeness_ztime`) and its line anchors are
a few lines off. Confirm the pair census and each anchor before editing; a pair that no longer
reproduces is a stop-and-report, not a silent skip.

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

### Phase 12: lemma to theorem across live scope [NOT STARTED]

**Goal**: zero live `lemma` declarations, bringing 88 declarations into the two invariant checks
whose regexes currently cannot see them.

**Tasks**:
- [ ] Re-count live-scope `lemma` declarations with the report Appendix's command; record the
      before number.
- [ ] Convert all of them to `theorem`, preserving attributes, modifiers (`private`, `protected`,
      `noncomputable`, `scoped`, `local`) and indentation exactly.
- [ ] Work file-by-file, heaviest first (`Syntax/SubformulaClosure/IteratedTemporal.lean` 21,
      `Metalogic/Core/MaximalConsistent.lean` 8, `Metalogic/Bundle/WitnessSeed.lean` 8,
      `Metalogic/Bundle/TemporalContent.lean` 6, `Decidability/Verified/Termination/MintBound.lean`
      5, `Metalogic/Core/MCSProperties.lean` 4).
- [ ] Record the C17 and C19 numbers before and after; new dead-declaration candidates are an
      **expected** consequence, not a regression.

**Timing**: 1.5 hours

**Depends on**: 11

**Verification Tier**: full

**Scope Hypothesis**: 88 live `lemma` declarations (the review's 141/142 included `Boneyard/`'s
54). Confirm the live figure before starting; the acceptance criterion "lemma count 0" is scoped to
live scope, and `Boneyard/`'s 54 stay.

**Territory**: `FormalSystem/**` excluding `FormalSystem/Automation/**` and `FormalSystem/Boneyard/**`;
`Tests/**` excluding `Tests/BimodalTest/Automation/**`.

**Files to modify**:
- the live-scope files carrying `lemma` declarations

**Verification**:
- `lake build` and `lake test` green.
- The live-scope `lemma` count command returns 0 outside the deferred Automation territory.
- C17/C19 before/after numbers recorded.

---

### Phase 13: Adjudicated Uppercase_x renames [NOT STARTED]

**Goal**: dot-namespace the ~30 Uppercase_x names whose prefix is a real declaration, and leave the
rest alone with the reason recorded.

**Tasks**:
- [ ] Re-run the Uppercase_x census (107 live: 102 `theorem`, 5 `def`) and classify each name into
      the three populations.
- [ ] Rename the type/def-prefix class: `R3Maximal_*`, `BurgessR3Maximal_*`, `SubformulaClosure_*`,
      `BranchOrder_*`, `SetConsistent_of_subset`, `Fib_*`, `RefinedFilteredTaskFrame_*`,
      `FiniteFilteredTaskFrame_*` — confirming for each that a declaration of the prefix name
      actually exists.
- [ ] **Leave the ~55 tense-operator names alone** (`F_`, `P_`, `G_`, `H_`, `FF_`, `HF...`);
      `F`/`P`/`G`/`H` are the paper's operators, not namespaces.
- [ ] Adjudicate the ~22 Kamp-bridge prefixes (`CAggPtX_`, `CAggPtT_`, `CAggInt_`, `CAggOd_`,
      `CAggOdSwap_`, `CExtFut_`, `CExtPast_`, `A_diag_`, `A_past_`, `A_future_`, `MR_`, `O_zero_`)
      case-by-case on the same "does the prefix name a real `def` in that file" test.
- [ ] Record the classification and the leave-alone rationale in
      `docs/development/MODULE_ORGANIZATION.md` (or the naming-convention document it points to),
      so the decision is durable rather than re-litigated by the next census.
- [ ] Update `docs/theorem-index.md` rows for any renamed declaration.

**Timing**: 1.5 hours

**Depends on**: 12

**Verification Tier**: full

**Scope Hypothesis**: 107 live Uppercase_x names, of which ~30 are renameable, ~55 are
tense-operator names that must not be renamed, and ~22 need case-by-case adjudication. The
dispatch's flagship examples (`CanonicalTask_backward_comp`, `Succ_implies_CanonicalR`) exist only
in `Boneyard/`. Confirm all four figures before renaming; report the actual renamed count.

**Territory**: same exclusions as Phase 12.

**Files to modify**:
- the live-scope declaration and call sites of the renamed names
- `docs/theorem-index.md`, `docs/development/MODULE_ORGANIZATION.md`

**Verification**:
- `lake build` and `lake test` green.
- Every renamed name has zero remaining live-scope occurrences under its old spelling.
- The census's remaining Uppercase_x population is exactly the recorded leave-alone classes.

---

### Phase 14: Naming-regression guard [NOT STARTED]

**Goal**: extend C16's existing `dupNamespace` walker so none of the three naming classes can
regrow, without adding a fourth namespace-walking scanner.

**Tasks**:
- [ ] Extend the existing `dupNamespace` textual scanner (`check-module-invariants.sh`, the
      `namespace`/`end` stack walk) rather than copying it.
- [ ] Apply the five corrections research identified: add `lemma` to the declaration regex; use an
      identifier class that survives `?`, `'`, `τ` and other unicode suffixes (a naive
      `[A-Za-z0-9_'.]*` truncates `asAnd?` and manufactures ~30 false positives); exclude `private`
      declarations; skip `/- ... -/` and `/-! ... -/` blocks; and **do not** flag structure-member
      namesakes (`Syntax.Atom.beq_refl` vs `Syntax.Formula.beq_refl`, and the
      `toJson`/`display`/`empty`/`size`/`insert`/`mono`/`lift` families), which the
      outer-shadows-inner test already excludes by construction since neither namespace is a prefix
      of the other.
- [ ] Add the three regression assertions: zero live `lemma` declarations; no new Uppercase_x name
      outside the recorded leave-alone classes; no new outer-shadows-inner bare-declaration pair.
- [ ] Add `lemma` to C17's declaration regex too, so the 88 converted declarations enter the
      dead-declaration census.
- [ ] Document each assertion's rationale in the header comment, including the C17 base-identifier
      masking that justifies the shadowing clause.

**Timing**: 2 hours

**Depends on**: 8, 11, 12, 13

**Verification Tier**: local

**Scope Hypothesis**: one scanner extended (not a fourth added), five corrections, three
assertions, plus one regex addition in C17. Confirm the current `dupNamespace` finding count is 0
before extending, so any post-extension finding is attributable to the change.

**Files to modify**:
- `scripts/check-module-invariants.sh` - C16 extension, C17 regex, new assertions

**Verification**:
- `bash scripts/check-module-invariants.sh` green, with the new assertions reporting PASS.
- Each assertion fails on a deliberate temporary violation (one `lemma`, one new Uppercase_x name,
  one new shadowing pair), reverted after confirming.
- A structure-member namesake is confirmed **not** flagged.

---

### Phase 15: ORGANISATION.md and NOTATION.md [NOT STARTED]

**Goal**: the two root-level furniture documents mature Lean libraries carry, without duplicating
what `docs/ARCHITECTURE.md` already says.

**Tasks**:
- [ ] Write root `ORGANISATION.md` as a short **pointer**: the Syntax/ProofSystem/Semantics/
      Metalogic/Automation layering in one paragraph, the single documented
      `Semantics → ProofSystem` edge (`Semantics/FrameClassValidity.lean:8`), then links to
      `docs/ARCHITECTURE.md` and `docs/development/MODULE_ORGANIZATION.md`. C18 gates paragraph
      duplication across top-level READMEs, so a third copy of the layering prose would fail.
- [ ] Write root `NOTATION.md` inventorying the **15** live `notation` declarations: the 12
      derivability notations that already carry a per-frame-class tag (`Γ ⊢[fc] φ`, `⊢[fc] φ`,
      `Γ ⊢ φ`, `⊢ φ`, the four `|-![fc]` siblings, `Γ ⊢ᴮᴸ[fc] φ`/`⊢ᴮᴸ[fc] φ`,
      `Γ ⊢⋆[fc] φ`/`⊢⋆[fc] φ`), the 2 untagged validity notations, and the scoped quotient bracket.
- [ ] Record the tag **asymmetry** and its reason: `Semantics/Validity.lean:239-242` deliberately
      dropped a `TruthAt` notation because it conflicts with `⊨`, using a subscripted variant and
      dot-notation instead. Document the seven-predicate `⊨` family (`ValidOnFrames`, `ValidIn`,
      `Valid`, `ValidDense`, `ValidZTime`, `ValidComplete`, `ValidRTime`) plus the
      `SemanticConsequence` family and the `StarFormula` mirror.
- [ ] **Do not introduce a new `TM[...]` validity notation** — G-16's "four ⊨-shaped relations"
      premise is wrong and its recommendation is already half-implemented on the `⊢` side.
- [ ] Link both documents from `README.md`.

**Timing**: 1.5 hours

**Depends on**: 10, 14

**Verification Tier**: prose

**Scope Hypothesis**: 15 live `notation` declarations (12 tagged derivability, 2 untagged validity,
1 scoped quotient), and exactly one `Semantics → ProofSystem` import edge. Confirm both by grep
before writing; a second edge would falsify the layering claim and must be reported.

**Files to modify**:
- `ORGANISATION.md` (new), `NOTATION.md` (new)
- `README.md` - links

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` green — C12/C13 (path and link resolution)
  and C18 (prose duplication) in particular.
- Every notation named in `NOTATION.md` resolves to a live declaration.

---

### Phase 16: Publish the API documentation [NOT STARTED]

**Goal**: a doc-gen4 site built and deployed by `docgen-action`, linked from `README.md`, with the
now-stale `docs/README.md` recipe replaced.

**Tasks**:
- [ ] Add `.github/workflows/docs.yml`: `permissions: {contents: read, id-token: write,
      pages: write}`, triggered on push to `main` plus `workflow_dispatch`, with a single
      `uses: leanprover-community/docgen-action@main` step.
- [ ] Set the inputs explicitly: `api-docs: true`, `blueprint: false`, `references: references.bib`,
      and **`build-page: false`** — the last resolves the `homepage: docs` collision with this
      repo's non-Jekyll 100-file `docs/` tree. Do not rely on any default.
- [ ] Do **not** add `require «doc-gen4»` to `lakefile.lean`; the action supplies it, and
      `lake-manifest.json` must stay unchanged.
- [ ] Rewrite `docs/README.md:272-278`, which currently asserts that no doc-gen4 target exists and
      that adding one would be a build-graph change — true before this task, false after.
- [ ] Add the site link to `README.md` above `## Documentation` (`README.md:293`).
- [ ] Delete the stray root artefact `Scratch434.lean.tmp` (0 bytes; its name is also a
      task-number reference in a deliverable path).
- [ ] Record in `docs/README.md` that the repository Pages source must be set to **GitHub Actions**
      manually — a one-time human step the workflow cannot perform, and a precondition for the
      first deploy to appear.
- [ ] Confirm `.gitignore:32-34` already covers `doc/` and `_site/`.

**Timing**: 1.5 hours

**Depends on**: 2, 3, 8, 15

**Verification Tier**: prose

**Scope Hypothesis**: one new workflow file, one rewritten `docs/README.md` section, one `README.md`
link, one file deletion. `lake-manifest.json` and `lakefile.lean` must show **zero** diff — confirm
with `git diff --stat` at phase close.

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

### Phase 17: Acceptance gate [NOT STARTED]

**Goal**: verify every acceptance criterion with a recorded command and its output.

**Tasks**:
- [ ] `lake build` green from clean.
- [ ] `lake test` green.
- [ ] `bash scripts/check-module-invariants.sh` green, including the new C21 and the extended C16.
- [ ] Assert the acceptance criteria one by one, recording the command and result: doc site
      workflow present and linked from `README.md`; `MainResults.lean` compiles with every
      `#print axioms` matching the C2/C14 pins; `references.bib` named by the docs build; zero
      declared tactics with zero library-and-test uses outside `Boneyard/`; live `lemma` count 0.
- [ ] Record the C17 and C19 before/after numbers and confirm neither check gates the build
      (no `ENFORCE_C17`, no `ENFORCE_C19`).
- [ ] Record every corrected dispatch premise in the implementation summary, so the divergence from
      the dispatch text is a documented decision rather than an unexplained gap: no lakefile
      `require`, no third axiom baseline, no `TM[...]` notation, no fully-qualified-name duplication
      to fix, ~30 (not 98) Uppercase_x renames, 88 (not 141) `lemma` conversions.
- [ ] Hand `FormalSystem/MainResults.lean` to task 178 as the artefact its examples should cite.

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
