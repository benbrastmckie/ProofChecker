# Implementation Summary: Task #531

- **Task**: 531 - docgen publication and automation suite triage
- **Status**: [COMPLETED]
- **Started**: 2026-09-07
- **Completed**: 2026-09-07
- **Effort**: one dispatch
- **Dependencies**: 529 (completed), 530 (completed)
- **Artifacts**: plans/01_docgen-publication-automation-triage.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

WAVE 5 of the 2026-09-01 Lean engineering review: publish the API documentation, finish the
repository furniture a mature Lean library carries, and retire the bespoke automation suite that
measurement showed nobody uses. All seventeen phases are closed.

The library gains a doc-gen4 publication workflow and a bibliography wired into it, a one-page
`MainResults.lean`, root `ORGANISATION.md` and `NOTATION.md`, and three new invariant checks
(C21, C22, C23). It loses seventeen tactic declarations, two whole Aesop modules, five
write-only `SearchConfig` fields, two no-op presets and three tactic aliases that were
behaviourally identical to the one they aliased.

No `sorry`, no axiom, no deferral. `MainResults.lean` restates already-proved declarations and
runs `#print axioms` over them; every other Lean change is a deletion, a rename, or a docstring.

## What Changed

### Publication

- `.github/workflows/docs.yml` (new) — builds and deploys doc-gen4 via
  `leanprover-community/docgen-action`, with `api-docs: true`, `blueprint: false`,
  `references: references.bib` and **`build-page: false`**. The last is load-bearing: the
  action's `homepage` input defaults to `docs`, and expects a Jekyll site whose `docs/docs/`
  receives the API pages. This `docs/` is ~100 hand-written markdown files with no `_config.yml`.
- `docs/README.md` — the "no generated API documentation target" section replaced. It now
  records the workflow, the standing prohibition on adding a `lakefile.lean` dependency (the
  half of the old text that is still true), and the one-time manual step: the repository's Pages
  source must be set to **GitHub Actions**, which a workflow cannot do for itself.
- `README.md` — API documentation link, plus a "Start here" block for the two new root documents.
- `Scratch434.lean.tmp` — deleted (0 bytes; its name was also a task-number reference in a path).

### Bibliography

- `references.bib` — 13 entries to **26**. Added `rabinovich2014` (71 citations, the most-cited
  work in the tree and previously absent), `doets1989`, `goldblatt1992`, `burgess1984`,
  `reynolds2001`, `reynolds2003`, `verbrugge2004`, `fischerLadner1979`, then `gore1999`,
  `libal2016`, `korf1985`, `yang2019`, `kaliszyk2018` when a wider scan found five more works
  cited with no key at all. Every entry verified against `~/Projects/Literature/`'s index and
  converted scans, not written from memory.
- 193 lines across 134 `.lean` files — `## References` prose converted to `[key]` citations.
  The `Surname YYYY` census now returns **zero** across `FormalSystem/` and `Tests/`.

### Main results page

- `FormalSystem/MainResults.lean` (new) — 27 headline declarations, each `#check`ed and followed
  by `#print axioms`, grouped by what they claim: soundness ×4, weak completeness ×4,
  consequence completeness ×4, strong completeness and compactness ×4, the four non-compactness
  refutations, the Galois-closure family ×4, expressive completeness ×2, decidability soundness.
  Imported from `FormalSystem.lean`, so it is inside `lean_lib FormalSystem`'s root closure.

### Automation triage

- `FormalSystem/Boneyard/RetiredTactics/` (new, guard-first, with its own README and an entry in
  the archive's exception list) — 14 tactic declarations and the two `TMLogic` Aesop modules.
- `FormalSystem/Automation/Tactics/Helpers.lean` (1,210 lines) **deleted**, replaced by
  `UserTactics.lean` (275), `Meta.lean` (99) and `Search.lean` (657).
- `FormalSystem/Automation/Tactics/Commands.lean` — five write-only `SearchConfig` weight fields
  and the two presets built from them removed; `tm_auto`, `temporal_search` and
  `propositional_search` removed; five false docstring claims corrected.
- `FormalSystem/Automation/Tactics/Deduction.lean` — the adoption verdict recorded, and the
  imports it never had added.
- `Tests/BimodalTest/**` — 169 occurrences of the three retired aliases migrated to
  `modal_search`.

### Naming

- 8 shadowing renames plus `Independence.realOrder`, `Perpetuity.pastKDist` and
  `DatasetValidator.DiversityReport`: 17 outer-shadows-inner pairs down to **6**, every one a
  recorded exception.
- 57 `lemma` → `theorem`. Live `lemma` **declaration** count is now **0**.
- 38 Uppercase_x names dot-namespaced; 67 left alone in three recorded classes.
- `scripts/nolints.json` — three grandfathered `unusedArguments` entries rekeyed from
  `TaskFrame.Fib_*` to `TaskFrame.Fib.*`. A key rename, not a new suppression: without it C16
  reports three findings that were already grandfathered under the old names.
- `Tests/BimodalTest/Automation/{TacticsTest,TacticsTest_Simple}.lean` — now import
  `Tactics.UserTactics` explicitly. They exercise `assumption_search` and the formula
  predicates, and used to reach them transitively through `Commands.lean`'s import of
  `Helpers.lean`. `lake test` caught this; the fix is the import the tests should always have
  had, not a re-coupling of `Commands.lean` to the user tactics.

### Guards

- `scripts/check-module-invariants.sh` — **C21** (every `MainResults.lean` name is axiom-pinned
  by C2 or C14), **C22** (the two deliberately-duplicated `allAxiomNames` lists agree), **C23**
  (three naming-regression assertions, implemented by extending C16's namespace walker rather
  than adding a fourth scanner). `lemma` added to C17's declaration regex.

### Root furniture

- `ORGANISATION.md`, `NOTATION.md` (new).

## Decisions

- **`MainResults.lean` introduces no aliasing declarations.** `theorem mainSoundness := soundness`
  for each of the 27 would have reintroduced, wholesale, the defect Phases 11 and 14 exist to
  remove: every alias shares a base identifier with the theorem it aliases, and C17's
  dead-declaration census keys on the last dot-segment, so each pair would permanently mask the
  other. A page built to advertise the results would have blinded a check over all 27 of them.
  `#check` plus `#print axioms` gives the same drift-resistance with none of that.
- **No hand-transcribed `#print axioms` output.** The idiom the plan pointed at has itself
  retired that practice: `DiscreteNonCompactness.lean` records that its transcript "could and
  did drift out of step with the declarations it claimed to report". Transcribing 27 blocks
  would have rebuilt exactly that artefact. The page states the axiom contract once, names the
  single strict-subset exception (`Semantics.galoisClosed_mod`, `[propext]` alone), and points at
  the baselines — and C21 makes the pointer machine-checked rather than a promise.
- **C21 is a subset assertion, not a third baseline.** Three places to update on any change is
  three chances for them to disagree.
- **The `BXCanonical` engines were renamed, not the outer completeness family.** The recorded
  note in `StrongCompleteness.lean` had dismissed the collision as harmless, and on semantics it
  was right. It stopped one step early: a shared base identifier silently disables C17 over
  **both** members, so the collision was not inert. That note was rewritten in the same change,
  and it now records the cost as well — the inner engine family is left mixed, because
  `BXCanonical.completeness` and `…completeness_rtime_engine` collide with nothing.
- **`deduction`/`undischarge` declined for `DeductionTheorem.lean` on circularity, not
  `noncomputable` cost.** All four candidate sites are the case lemmas that `deductionTheorem`'s
  own recursion dispatches to, so using a wrapper around it there asks the theorem to prove its
  own cases. There is no site at which the tactic form could apply at any price.
- **Dot-namespacing has a second precondition the plan did not state.** See Plan Deviations.

## Plan Deviations

Every phase's own checklist carries its deviations inline. The ones that changed what was built:

- **Phase 13** — 51 renames applied, **13 reverted**. Dot-namespacing `Prefix_rest` when a live
  declaration is already called `rest` *captures* that name: declaring `Prefix.rest` puts `rest`
  in scope inside every other `Prefix.*` declaration. `BurgessR3Maximal.burgessR3` made
  `BurgessR3Maximal.extension_fails`'s reference to the standalone `burgessR3` **definition**
  resolve to the theorem, and the build failed with an application type mismatch at two sites.
  The `FiniteFilteredTaskFrame_*` and `RefinedFilteredTaskFrame_*` families are the same shape —
  `serial`, `limit`, `saturation`, `interpolates` are all live frame conditions. The rule is now
  two-halved and encoded in C23: dot-namespace iff the prefix is a live declaration **and the
  suffix is not**.
- **Phase 6** — "`Deduction.lean` uses nothing from `Helpers.lean`" is true of its *declarations*
  and false of its *imports*. It had no import line of its own and reached everything
  transitively. Dropping the line left it with zero imports and nine compiler errors.
- **Phase 11** — six of the eight re-exposure renames are not `conclusion_of_hypothesis`, because
  that form does not apply: four are nullary validity statements with no hypothesis to name, two
  are `iff` lemmas. Each got a name stating the one thing that distinguishes it from its
  namesake (`_validIn`, `_iff`). Four collisions are left in place with reasons — see below.
- **Phase 9** — 27 declarations, not the plan's ~24, and there is no `soundness_base`.
- **Phase 16** — the site link went *below* the `## Documentation` heading rather than above it;
  above it, the link would have sat at the end of the preceding section.
- **Phase 5** — there were **no test sites to migrate**. The ~17 the plan expected are section
  headings and `/-- Test NN: modal_4_tactic … -/` docstrings whose examples apply
  `DerivationTree.axiom` directly and never invoke a tactic.

### Corrected dispatch and review premises

Recorded so the divergence from the dispatch text is a documented decision rather than a gap:

| Dispatch/review said | Measured |
|---|---|
| add `require «doc-gen4»` to `lakefile.lean` | the action supplies doc-gen4; `lakefile.lean` and `lake-manifest.json` show **zero** diff |
| a third axiom baseline for `MainResults.lean` | C2+C14 already pin all 27; C21 asserts the subset |
| introduce a `TM[...]` validity notation | declined; the premise that four unrelated `⊨` relations exist is wrong, and it would reinstate a parser conflict two prior decisions exist to avoid |
| two live declarations share a fully-qualified name | they do not; the `CountermodelExtraction.lean` case is `private` |
| 98 Uppercase_x names to rename | 105 exist, **38** renamed, 67 left in three recorded classes |
| 141 `lemma` declarations | **64** live; 57 converted, 7 in md5-pinned modules and all 7 docstring prose |
| `completeness_discrete` | the name is `completeness_ztime` |
| `Automation/` needs Phase 2's citation conversion | it carries no `Surname YYYY` citation at all; what it has is four differently-shaped citations of works with no key |

### Excluded, with reasons (Phase 11, `[COMPLETED WITH EXCLUSIONS]`)

- `isValid` (×2) — both inner members (`DecisionResult.isValid`, `ExpandedTableau.isValid`) are
  structure-member namesakes on distinct types. The plan's own guard requirement says these must
  never be flagged.
- `mem_knownTimes_of_mem`, `mem_knownWorlds_of_mem` — the **outer** member of each pair is
  declared in `Verified/Termination/MintBound.lean`, md5-pinned by a concurrent workstream.
  Renaming the inner member alone would leave the base identifiers colliding, which is the thing
  C17 trips over: the pair must be done together or not at all.
- `allAxiomNames` — a deliberate, documented duplication (`ProofStepExport.lean` is a `lean_exe`
  root with its own `main` and cannot import the leaf module holding the canonical list). Given
  the C22 agreement check instead of a rename, as the plan directs.
- `insertEnv` — deferred. The two definitions are genuinely different operations, not a
  re-exposure: the outer inserts at position `c` with index shifting, the inner appends at the
  end. The inner's honest name is `snocEnv`. They have different arities and the name appears
  across 14 files, four of which sit beside neither definition, so ownership per site needs an
  arity analysis this dispatch did not have the build budget to verify. Recorded in C23's
  exception set with this reason rather than renamed blind.

## Verification

Every acceptance criterion below was asserted with a command and its actual output, not read
off the plan.

| Command | Result |
|---|---|
| `lake build` (guarded, detached) | **green**, `Build completed successfully (2592 jobs)`, `EXIT=0`, zero `error:` lines |
| `lake test` (guarded, detached) | **green**, `EXIT=0`, **45** `[test] PASS`/`OK` — identical to the pre-task baseline |
| `bash scripts/check-module-invariants.sh` | 1 failure, and it is not this task's — see below |
| `git diff --stat lakefile.lean lake-manifest.json` | **empty** |
| `grep -c '^@' references.bib` | **26** (13 before) |
| live-scope `## References` prose-citation census | **0** across `FormalSystem/` and `Tests/` |
| live `lemma` **declaration** count (comment-aware) | **0** |
| real `axiom` declarations in live scope | **0** (7 grep hits, all docstring prose beginning with the word) |
| structural `sorry` inventory (C3) | **ZERO** |

### The invariant suite, check by check

**PASS**: B0, C1 (both `lake build` and `lake build BimodalTest`), **C2** (all four flagship
axiom sets match baseline), C3, C4, C5, C6 (including all 14 manifested modules compiling in
isolation), C8, C10, C11, C12, C13, **C14** (both halves — the stale-literal scan and every one
of the 101 pinned declarations matching its axiom baseline), C15 (both), C16 `dupNamespace`,
C18 (both), C19, C20 (both tiers), **C21**, **C22**, **C23** (all three assertions), INV.

**FAIL**: C9, one task-number citation at
`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean:12524`. **This is not
this task's finding.** That module is md5-pinned and actively being written by a concurrent
session sharing this working tree; it was not touched here and must not be. Recorded rather
than fixed.

### C2 and C14 after the rename

Phase 11 renamed two **C2 baseline subjects** (`BXCanonical.completeness_dense` and
`…completeness_ztime`). The baseline heredoc and its scratch-file `#print axioms` block were
updated together, and `scripts/typst-status-counts.sh` and `docs/theorem-index.md` with them.
C2 passes: the axiom **sets** are unchanged and were never the thing edited. This is the one
place in the task where the "HARD STOP, not a new baseline" warning in C2's own header applies,
and it is satisfied on its own terms — a subject renamed, not a set re-recorded.

### Guards verified by deliberate violation

Each new assertion was confirmed to fail on a violation and pass again on revert, rather than
assumed to work because it printed PASS:

- **C21** — appending `#print axioms FormalSystem.Metalogic.Core.deductionTheorem` to
  `MainResults.lean` produced `FAIL C21 1 of 28 MainResults.lean declaration(s) are pinned by
  neither C2 nor C14`, naming the offender.
- **C23/lemma** — one `lemma` declaration produced `FAIL C23 1 live lemma declaration(s)`.
- **C23/Uppercase_x** — `theorem Fib_c23Probe` produced a FAIL reporting the dotted name it
  wants (`Fib.c23Probe`).
- **C23/shadowing** — a fresh outer/inner pair produced a FAIL naming both members' locations.
- **C23/structure members** — two declarations named `c23ProbeMember` in `Semantics.Atom` and
  `Semantics.Formula` produced **three PASS lines**, confirming the legitimate case is not
  flagged.
- **C22** — not violation-tested; the two lists were confirmed equal as sets (45 names each) by
  an independent `diff` of the extracted names.

### C17 and C19 before and after

Neither gates the build: there is no `ENFORCE_C17` and no `ENFORCE_C19`.

| | before | after |
|---|---:|---:|
| C17 dead-declaration candidates | 990 | 990 |
| C19 docstring coverage (unrefined) | 89.48% | 89.46% |
| C19 docstring coverage (refined) | 92.33% | **92.32%** (floor 90%) |

C17's path was 990 → 983 → 990: the −7 is the declarations Phases 5 and 6 retired, the +7 is
the converted `lemma`s entering the census once `lemma` joined C17's declaration regex. New
dead-declaration candidates there are the **intended** consequence, not a regression — before
the change, C17 could not see those declarations at all.

### Tactic census, for the "zero declared tactics with zero uses" criterion

15 declared tactic tokens in live scope. Every one with zero library-and-test invocations has
been retired **except** two members of the EF-game set in
`Metalogic/WeakCanonical/EFGameTactics.lean` — `game_tuple_unfold` and `orderRev`. The dispatch
names that set as the repository's production custom tactics and the plan places it out of
scope; its seven members carry 43 invocation sites between them, and the two at zero are the
hypothesis-targeting and reversed-order siblings of `simp_game_tuple` (35 sites) and `orderRefl`
(5), kept for symmetry with them. Retiring members of a cooperating set in a protected module
was not this task's to do, and the measurement is recorded here so the next census does not
have to repeat it.

## Impacts

- **`FormalSystem/MainResults.lean` is the artefact the decidability-examples roadmap item
  (ROADMAP.md Phase 5) should cite.** It gives that work a single page of already-pinned
  headline results to point examples at, instead of a directory tour.
- The published doc-gen4 site is the first machine-generated API surface this repository has
  had. It renders `[key]` citations against `references.bib`, so the ~190 converted prose
  citations become real references rather than bare surnames.
- Three new invariant checks change what a future change has to satisfy. C23 in particular will
  reject a new `lemma`, a new capture-free-but-underscored `Prefix_rest`, or a new
  outer-shadows-inner pair.
- `Tactics/Helpers.lean` no longer exists. Anything importing it must now choose between
  `UserTactics`, `Meta` and `Search` — which is the point of the split.

## Follow-ups

- **Set the repository Pages source to GitHub Actions.** A one-time manual step; the workflow
  cannot do it, and until it is done the deploy has nowhere to publish. Recorded in
  `docs/README.md` and in the workflow header.
- **`insertEnv` → `snocEnv`** for the `Kamp` member, once someone can spend a build on the
  per-site arity analysis across 14 files.
- **`mem_knownTimes_of_mem` / `mem_knownWorlds_of_mem`**, once `Verified/Termination/MintBound.lean`
  is unpinned. C23's path-based exemption is marked DELETE-THIS-WHEN for exactly this.
- **`Search.lean` versus `Automation/ProofSearch/`** — two search engines with different
  interfaces, only one reachable from a tactic. Recorded as an open question in `Search.lean`'s
  module docstring rather than resolved here.
- `docs/development/PHASED_IMPLEMENTATION.md` carries 100 of the 142 task-number citations C9D
  reports under `docs/`; clearing them is what would let `ENFORCE_C9_DOCS` flip to 1.

## References

- `specs/531_docgen_publication_and_automation_suite_triage/plans/01_docgen-publication-automation-triage.md`
- `specs/531_docgen_publication_and_automation_suite_triage/reports/01_docgen-publication-automation-triage.md`
- `specs/reviews/2026-09-01-lean-engineering/{E-docs,G-ecosystem,D-tactics}.md`
- `specs/531_docgen_publication_and_automation_suite_triage/handoffs/phase-14-handoff-20260907.md`
