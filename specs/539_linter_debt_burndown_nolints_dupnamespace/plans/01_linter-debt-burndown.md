# Implementation Plan: Linter Debt Burndown (nolints.json, dupNamespace)

- **Task**: 539 - Draw down the linter debt that the CI/linter-gates work recorded rather than fixed
- **Status**: [IMPLEMENTING]
- **Effort**: 10.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/539_linter_debt_burndown_nolints_dupnamespace/reports/01_linter-debt-burndown.md
- **Artifacts**: plans/01_linter-debt-burndown.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Burn `scripts/nolints.json` down from 307 grandfathered findings to 217 by fixing five of the six
linter categories outright, and drive `dupNamespace` from 14 findings to 0 by relocating
`structure Chronicle` out of its same-named namespace. The one surviving category,
`unusedArguments` (217), is permanently grandfathered on measured evidence and gets a written
rationale in `docs/development/NAMING_CONVENTION_DEVIATION.md`, which is refreshed in the same
pass along with seven stale numeric claims in `.github/workflows/ci.yml` and
`scripts/check-module-invariants.sh`. Definition of done: `simpNF` and `dupNamespace` both report
zero, `nolints.json` carries only `unusedArguments`, plain `lake lint` exits 0, and C16's textual
dupNamespace scan reports PASS.

### Research Integration

The research report is unusually load-bearing for this plan, because **both code fixes were
prototyped end-to-end, compile-verified, and then reverted**. Phases 1 and 2 therefore transcribe
a verified change rather than design one. Three further research findings shape the plan directly:

1. **`lake env lean <file>` runs the real `dupNamespace` linter in ~2 seconds**, reusing existing
   oleans and writing none. The ~10-minute cost documented in `check-module-invariants.sh` applies
   only to the `lake lint --builtin-only --lint-only .dupNamespace` path, not to this route. Every
   phase below uses `lake env lean` as its cheap per-file pre-check before paying for a guarded
   full build.
2. **`unusedArguments` should be permanently grandfathered on evidence**, not burned down: 207 of
   217 findings (95.4%) have *only* instance-implicit arguments unused, dominated by
   `[DecidableEq sig.preds]` (130), `[Fintype sig.preds]` (122), `[Nontrivial D]` (41). These are
   typeclass parameters retained for signature uniformity; the linter's own advice (delete the
   argument) is wrong for a uniform-interface family.
3. **`lake exe runLinter --update` must never be run in this task.** It rewrites `nolints.json`
   wholesale from current findings and grandfathers every new finding, including a genuine
   regression. Every phase instead removes exactly one category with a `jq` filter and proves the
   removal with a green `lake exe runLinter FormalSystem`.

**Line numbers in the research report must be re-derived, not trusted.** The report warned that a
concurrent session had shifted anchors in `scripts/check-module-invariants.sh`; that has already
happened again — the report's `:434` and `:1395` are now `:435` and `:1497`. Every phase below
instructs the implementer to locate anchors with `grep -n` immediately before editing.

Baseline re-confirmed live at plan time: `jq -r '.[][0]' scripts/nolints.json | sort | uniq -c`
returns exactly `unusedArguments 217`, `docBlame 51`, `defsWithUnderscore 33`, `tacticDocs 4`,
`structureInType 1`, `simpNF 1` (total 307), matching the report category-for-category.

### Prior Plan Reference

No prior plan. This is the first planning round for this task.

### Roadmap Alignment

`roadmap_path` was not supplied in the delegation context, so no roadmap phases are added. A
read-only consultation of `specs/ROADMAP.md` confirms it tracks the decidability/tableau,
completeness, and publication fronts; repository linter hygiene is not a named roadmap item, so
this plan advances none and modifies nothing there.

## Goals & Non-Goals

**Goals**:
- `simpNF` findings: 1 -> 0 (delete the redundant `length_range_map`).
- `dupNamespace` findings: 14 -> 0 (relocate `structure Chronicle` one namespace up).
- `defsWithUnderscore`: 33 -> 0 (rename to lowerCamelCase per the project's own settled rule).
- `docBlame`: 51 -> 0 (48 by docstring, 3 by in-source `@[nolint docBlame]`).
- `tacticDocs`: 4 -> 0 (docstrings on the second `syntax` command of each tactic pair).
- `structureInType`: 1 -> 0 in `nolints.json`, migrated to an in-source `@[nolint]` with reason.
- `scripts/nolints.json` reduced 307 -> 217, carrying only `unusedArguments`.
- A written, evidence-backed grandfathering policy for `unusedArguments` recorded in
  `docs/development/NAMING_CONVENTION_DEVIATION.md`.
- Seven stale numeric/status claims corrected across `ci.yml` and `check-module-invariants.sh`.

**Non-Goals**:
- Removing the 10 genuine dead hypotheses inside the `unusedArguments` set
  (`branchTruthAt_untl`/`_snce`, `regionFrame`/`regionHistory`, `StepD.badComp_isBadInterval`,
  `ghr93_strategy_compose.compose_wc`/`_right`, `exists_singleton_class_between`/
  `kEquiv_classBlock`/`goodDense_unionClasses`). These are real signature changes with call-site
  fallout; record them as a named future item instead.
- Renaming the `Chronicle` *type* or the `…BXCanonical.Chronicle` *namespace* (research options A
  and B, both rejected).
- Any change introducing a `sorry` or a new axiom. Every edit here is a rename, a docstring, a
  declaration relocation, an attribute, or a deletion.
- Editing `specs/reviews/review-2026-09-07.md`, which is a dated historical record.
- Running `lake exe runLinter --update` at any point.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Option C breaks a downstream file using `open …Chronicle` + bare `Chronicle` as a type | H | L | No such site exists today (audited: 4 files use the `open` form, none uses `Chronicle` as a type). `autoImplicit := false` makes it a hard error, not a silent implicit. The Phase 2 full build is the gate; the fix is adding `open FormalSystem.Metalogic.BXCanonical` to the affected file. |
| `--update` silently grandfathers a regression | H | L | Never run it. Per-category `jq` removal + green `lake exe runLinter FormalSystem` in every phase that touches `nolints.json`. |
| Cited line numbers are stale by edit time (already observed twice) | M | H | Every phase re-derives anchors with `grep -n` immediately before editing. Never `sed -i` against a number quoted from the report or this plan. |
| Rebuild cost dominates; docstring edits deep in the import graph invalidate large olean subtrees | M | H | Batch each category into one guarded build. Use `lake env lean <file>` (~2-3 s) as the per-file pre-check. Every `lake build` runs detached and guarded per `context/project/lean4/operations/long-builds.md`. |
| A rename in Phases 3-4 misses a call site in `Tests/` or a string/docstring occurrence | M | M | Rename by exact-token grep across `FormalSystem/` **and** `Tests/`; the full build plus test build in Phase 4 is the gate. |
| A concurrent session edits the same files mid-phase | M | M | Re-derive anchors immediately before each edit; scope every commit to the phase's own file set (never `git add -A`). |
| `docBlame` on `where`-clause helpers cannot be fixed by a docstring | L | Certain | Confirmed by research. Use the verified in-source `attribute [nolint docBlame] …` route for those 3. |

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
| 7 | 7 | 6 |
| 8 | 8 | 7 |
| 9 | 9 | 8 |

Phases within the same wave can execute in parallel. **This plan is deliberately fully
sequential even where file sets are disjoint**: the Lake build cache and `scripts/nolints.json`
are both shared mutable state, so two phases running concurrently would invalidate each other's
oleans and race on the same JSON file. The wave table records that reality rather than an
idealized parallelism the toolchain cannot deliver.

---

### Phase 1: Delete the redundant `length_range_map` (simpNF 1 -> 0) [COMPLETED]

**Goal**: Remove the single `simpNF` finding by deleting a lemma that duplicates two Mathlib simp
lemmas, and drop the `simpNF` row from `nolints.json`.

**Tasks**:
- [x] `grep -n "length_range_map" FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean` to
      re-derive all anchors (expected: 1 declaration + 5 use sites).
- [x] Delete the `@[simp] theorem length_range_map` declaration and its `@[simp]` attribute line.
- [x] Rewrite the two `simp only [Periodic.cyc, length_range_map]` sites as
      `simp only [Periodic.cyc, List.length_map, List.length_range]`.
- [x] Rewrite the three `rw [h?D, length_range_map]` sites as `rw [h?D]; simp` (preserving each
      site's own hypothesis name `hbD` / `hmD` / `hfD`).
- [x] Confirm no reference survives anywhere:
      `grep -rn "length_range_map" FormalSystem/ Tests/` returns nothing.
- [x] Drop the category from `nolints.json`:
      `jq 'map(select(.[0] == "simpNF" | not))' scripts/nolints.json > /tmp/n.json && mv /tmp/n.json scripts/nolints.json`
      (the `| not` form is required by the repo's jq-escaping rule).

**Timing**: 1 hour (mostly build wall-time)

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: 1 declaration + 5 use sites, all inside `Extraction.lean`, and no reference
from any other module or from `Tests/`. Confirm with
`grep -rn "length_range_map" FormalSystem/ Tests/ scripts/ docs/` before editing; if any site
outside `Extraction.lean` appears, stop and re-scope the phase rather than proceeding.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean` - delete lemma, rewrite 5 use sites
- `scripts/nolints.json` - drop the 1 `simpNF` row (307 -> 306)

**Verification**:
- `lake env lean FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean` exits 0 with zero
  diagnostic output (the unmodified baseline is also zero, so any output is a regression).
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached,
  `run_in_background: true`) exits 0.
- `lake exe runLinter FormalSystem` exits 0 — this is what proves the category is genuinely fixed
  and not merely un-grandfathered.
- `jq 'length' scripts/nolints.json` reports 306.

---

### Phase 2: Relocate `structure Chronicle` (dupNamespace 14 -> 0) [COMPLETED]

**Goal**: Move `structure Chronicle` out of `namespace FormalSystem.Metalogic.BXCanonical.Chronicle`
and into the parent `FormalSystem.Metalogic.BXCanonical`, so `…BXCanonical.Chronicle` becomes the
structure's own namespace (the standard Lean/Mathlib idiom) rather than a sibling of it.

**Tasks**:
- [x] Re-derive anchors:
      `grep -n "^namespace \|^end \|^structure Chronicle\|^def Chronicle\.c" FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
      (expected shape: namespace opens near the top, `structure Chronicle where` mid-file, nine
      `def Chronicle.cN`, namespace closes near the end).
- [x] Close the `…BXCanonical.Chronicle` namespace immediately before the structure, declare the
      structure inside `namespace FormalSystem.Metalogic.BXCanonical`, then reopen
      `namespace FormalSystem.Metalogic.BXCanonical.Chronicle` immediately after it. Note the Lean
      constraint: a namespace opened with a dotted path must be closed by the same dotted `end`,
      so this is an `end …Chronicle` / `namespace …BXCanonical` / structure / `end …BXCanonical` /
      `namespace …BXCanonical.Chronicle` sandwich, not a one-segment `end Chronicle`.
- [x] Rename the nine `def Chronicle.cN` to `def cN` (`c0`, `c1`, `c2`, `c2'`, `c3`, `c4`, `c4'`,
      `c5`, `c5'`) — they now sit inside the structure's own namespace, so the prefix would
      re-introduce the duplication.
- [x] Make **no other edit**. The change is reference-transparent: bare `Chronicle`, `χ.f`/`.g`/
      `.dom`, `χ.cN` dot notation, explicit `Chronicle.cN`, `⟨…⟩` anonymous constructors,
      `{ f := … }` structure instances, and `structure ValidChronicle extends Chronicle` all
      resolve to the same referents before and after.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: exactly 10 changed lines in exactly 1 file (1 structure relocation + 9 `def`
renames), with zero edits required in the 13 downstream files that open the namespace. Confirm the
zero-downstream-edits half with the full `lake build` — a build error naming a downstream file
falsifies the hypothesis and means the contingency below applies. Confirm the collision half with
a search for declarations named `f`, `g`, `dom`, `mk`, `c0`..`c5'`, or `toChronicle` in the
`…BXCanonical.Chronicle` namespace before editing (research audited this to zero).

**Files to modify**:
- `FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` - structure relocation + 9
  `def` renames

**Verification**:
- `lake env lean FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` reports zero
  errors and zero `dupNamespace` warnings, down from 14 (~2 s).
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached) exits 0.
  **This full build is the real gate** for the 13 downstream files in the namespace; the per-file
  check above cannot see them.
- `bash scripts/check-module-invariants.sh` reports
  `PASS C16 dupNamespace: zero declaration(s) …` from its live textual scan.

**Contingency (in-phase, not a rollback)**: if the build reports `unknown identifier 'Chronicle'`
in a file that does `open FormalSystem.Metalogic.BXCanonical.Chronicle` without a matching
`namespace`, add `open FormalSystem.Metalogic.BXCanonical` to that file. The four known
`open`-form sites are `WeakCanonical/ChronicleExtraction.lean`, `IntegerModel/ReynoldsBridge.lean`,
`GroupModel/GroupableCompanion.lean`, and `GroupModel/CountermodelBase.lean`; none currently uses
`Chronicle` as a type.

---

### Phase 3: `defsWithUnderscore` — the `FormalSystem.BaseLanguage` group (20 of 33) [COMPLETED]

**Goal**: Rename the 20 `BaseLanguage` declarations to lowerCamelCase, per the project's own
settled rule in `docs/development/NAMING_CONVENTION_DEVIATION.md` (data-producing declarations,
explicitly including `DerivationTree`-valued results, take lowerCamelCase).

**Tasks**:
- [x] Enumerate the group:
      `jq -r '.[] | select(.[0]=="defsWithUnderscore") | .[1]' scripts/nolints.json | grep '^FormalSystem\.BaseLanguage\.'`
- [x] For each declaration, find every token occurrence across `FormalSystem/` and `Tests/` with an
      exact-token grep (`grep -rnw`), then rename declaration and call sites together.
- [x] Do **not** touch `nolints.json` in this phase — the category is dropped in Phase 4, once all
      33 are done, so a single green `runLinter` proves the whole category at once.
- [x] Spot-check each edited file with `lake env lean <file>` (~2-3 s each) before paying for a
      build.

**Timing**: 1.25 hours

**Depends on**: 2

**Verification Tier**: interface

**Scope Hypothesis**: 20 declarations in the `FormalSystem.BaseLanguage` namespace, most with 1-2
call sites (research measured 141 token occurrences across all 33 declarations; median 2; largest
`co_derived` at 16). Confirm the count with the `jq | grep` above at implementation time, and
confirm each declaration's true call-site count with `grep -rnw` rather than assuming the median.

**Files to modify**:
- `FormalSystem/BaseLanguage/**` - 20 declaration renames plus their call sites
- Any `FormalSystem/**` or `Tests/**` file holding a call site (enumerated at implementation time,
  not guessable from the plan)

**Verification**:
- `lake env lean <file>` clean for each directly edited file.
- Build of the changed modules plus their enumerated direct dependents exits 0 (the `interface`
  tier's obligation — these are name changes with cross-file call sites).
- `jq -r '.[] | select(.[0]=="defsWithUnderscore") | .[1]' scripts/nolints.json | grep -c '^FormalSystem\.BaseLanguage\.'`
  still reports 20 (the JSON is deliberately untouched here; the entries are now stale, which is
  harmless — a `nolints` entry that never fires is simply unused).

---

### Phase 4: `defsWithUnderscore` — the remaining 13, and drop the category [NOT STARTED]

**Goal**: Rename the remaining 13 `defsWithUnderscore` declarations (including giving explicit
lowerCamelCase names to two anonymous instances), then remove the whole category from
`nolints.json` and prove the removal with a green `runLinter`.

**Tasks**:
- [ ] Enumerate the remainder:
      `jq -r '.[] | select(.[0]=="defsWithUnderscore") | .[1]' scripts/nolints.json | grep -v '^FormalSystem\.BaseLanguage\.'`
      (expected 13, spread across `Metalogic.WeakCanonical` ×5, `Theorems.TemporalDerived` ×2, and
      one each in `Theorems.DedekindDerived`, `StarLanguage`, `Semantics`,
      `Metalogic.Independence`, `Metalogic.Decidability.Verified.Bridge.TemporalCarrier`,
      `Metalogic.BXCanonical.Chronicle`).
- [ ] Rename each declaration and its call sites (exact-token grep across `FormalSystem/` and
      `Tests/`).
- [ ] Handle the two Lean-generated instance names specially:
      `instSuccOrderLexProdRatInt_formalSystem` and `instPredOrderLexProdRatInt_formalSystem` have
      zero references and come from anonymous instances in
      `FormalSystem/Metalogic/WeakCanonical/GroupModel/RamseyFactorization.lean`. Fix by giving
      those two instances explicit lowerCamelCase names. (Mathlib's linter whitelists a `_mathlib`
      suffix but not `_formalSystem`, so no whitelist route exists.)
- [ ] Drop the category:
      `jq 'map(select(.[0] == "defsWithUnderscore" | not))' scripts/nolints.json > /tmp/n.json && mv /tmp/n.json scripts/nolints.json`

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: 13 remaining declarations, of which exactly 2 are Lean-generated instance
names needing the explicit-naming treatment rather than a plain rename. Confirm both halves with
the `jq | grep -v` enumeration and by locating the two anonymous `instance` declarations in
`RamseyFactorization.lean` with `grep -n "^instance"` before editing.

**Files to modify**:
- `FormalSystem/Metalogic/WeakCanonical/**`, `FormalSystem/Theorems/**`,
  `FormalSystem/StarLanguage/**`, `FormalSystem/Semantics/**`,
  `FormalSystem/Metalogic/Independence/**`,
  `FormalSystem/Metalogic/Decidability/Verified/Bridge/TemporalCarrier*`,
  `FormalSystem/Metalogic/BXCanonical/Chronicle/**` - 13 renames plus call sites (exact paths
  enumerated at implementation time)
- `FormalSystem/Metalogic/WeakCanonical/GroupModel/RamseyFactorization.lean` - name the two
  anonymous instances
- `scripts/nolints.json` - drop 33 `defsWithUnderscore` rows (306 -> 273)

**Verification**:
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached) exits 0.
- `lake exe runLinter FormalSystem` exits 0 with the category removed — this simultaneously proves
  all 33 renames landed and that no new finding appeared.
- `jq 'length' scripts/nolints.json` reports 273.

---

### Phase 5: `docBlame` — structure field docstrings (33 of 51) [NOT STARTED]

**Goal**: Add a `/-- … -/` docstring above each undocumented structure field flagged by
`docBlame`. Purely mechanical, no signature or behavior change.

**Tasks**:
- [ ] Enumerate: `jq -r '.[] | select(.[0]=="docBlame") | .[1]' scripts/nolints.json` and pick out
      the field-projection entries. Research's grouping: `ProofStep.*` ×9, `RuleProfile.*` ×7,
      `OperatorDistribution.*` ×6, `EnrichedCountermodel.*` ×5, `DecideCacheKey.*` ×2,
      `TheoremEntry.*` ×2, `MinCyc.*` ×2 = 33.
- [ ] Locate each structure with `grep -rn "^structure <Name>" FormalSystem/`.
- [ ] Add one `/-- … -/` per flagged field, stating what the field holds — not restating its type.
- [ ] Leave `nolints.json` untouched; the category is dropped in Phase 6 after the remaining 18
      `docBlame` entries are handled.

**Timing**: 1.25 hours

**Depends on**: 4

**Verification Tier**: local

**Scope Hypothesis**: 33 field-projection entries across 7 structures, in the counts listed above.
Confirm by re-running the `jq` enumeration and classifying each entry at implementation time; the
7-structure grouping is a research-time hypothesis, not a checked fact for the current tree.

**Files to modify**:
- The files declaring `ProofStep`, `RuleProfile`, `OperatorDistribution`, `EnrichedCountermodel`,
  `DecideCacheKey`, `TheoremEntry`, `MinCyc` (paths located at implementation time via `grep -rn`)

**Verification**:
- `lake env lean <file>` exits 0 with zero diagnostics for each edited file. This matters more
  than it looks: a `/--` doc-comment inside a `structure` body is parsed syntax, not inert prose,
  so a misplaced one is a hard elaboration error — which is exactly why this phase is `local` and
  not `prose`.
- `lake exe runLinter FormalSystem 2>&1 | grep -c "docBlame"` shows the residual count dropping
  toward 18.

---

### Phase 6: `docBlame` residue + `tacticDocs`, and drop both categories [NOT STARTED]

**Goal**: Clear the remaining 18 `docBlame` findings and all 4 `tacticDocs` findings, then remove
both categories from `nolints.json`.

**Tasks**:
- [ ] **Tactic-syntax docstrings (5 entries, also clears all 4 `tacticDocs`)**: in
      `FormalSystem/Automation/Tactics/Commands.lean`, each search tactic is declared twice — a
      bare-`num` form and a named-parameter form. Only the first of each pair inherits the
      preceding `/-- … -/`; the second gets an auto-disambiguated name
      (`tacticModal_search__1`, `tacticPropositional_search__1`, `tacticTemporal_search__1`,
      `tacticTm_auto_`, plus `modalSearchParam`) and no docstring. Add a docstring to the second
      `syntax` command of each pair. Re-derive the declaration sites with
      `grep -n "syntax" FormalSystem/Automation/Tactics/Commands.lean`.
- [ ] **`QZStructure` + `.interp` / `.toMonadic` / `.toOrdered` (4)**: add docstrings.
- [ ] **Plain defs (6)**: add docstrings to `decidableValidZTime`, `decidableValidZTimeFamily`,
      `goodGroupable`, `nextConj`, `noBlockingTriple`, `IsContempEquivDenseCD`.
- [ ] **`where`-clause auto-helpers (3)**: `bestFirstSearch.searchLoop`, `iddfsSearch.iterate`,
      `PriorityQueue.insert.insertSorted` cannot carry a docstring at all. Add an in-source
      `attribute [nolint docBlame] <name>` at the enclosing declaration, with the reason stated in
      a comment at the site. (Research verified with `lean_run_code` that Lean accepts this
      attribute form on a `where`-generated name.)
- [ ] Drop both categories:
      `jq 'map(select(.[0] == "docBlame" | not)) | map(select(.[0] == "tacticDocs" | not))' scripts/nolints.json > /tmp/n.json && mv /tmp/n.json scripts/nolints.json`

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: local

**Scope Hypothesis**: 18 residual `docBlame` entries splitting 5 tactic-syntax / 4 `QZStructure` /
6 plain defs / 3 `where`-helpers, and 4 `tacticDocs` entries that are cleared as a side effect of
the 5 tactic-syntax docstrings. Confirm the split by re-running the `jq` enumeration after Phase 5
and classifying the residue; confirm the `tacticDocs` side effect by observing the category
disappear from `runLinter` output before removing its rows from the JSON.

**Files to modify**:
- `FormalSystem/Automation/Tactics/Commands.lean` - 5 syntax docstrings
- `FormalSystem/Automation/ProofSearch/Core.lean`, `FormalSystem/Automation/Tactics/Helpers.lean` -
  `where`-helper `@[nolint docBlame]` attributes (exact homes located at implementation time)
- The files declaring `QZStructure` and the 6 plain defs (located via `grep -rn`)
- `scripts/nolints.json` - drop 51 `docBlame` + 4 `tacticDocs` rows (273 -> 218)

**Verification**:
- `lake env lean <file>` exits 0 with zero diagnostics for each edited file.
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached) exits 0 —
  the `Automation/` edits sit under a widely-imported subtree.
- `lake exe runLinter FormalSystem` exits 0 with both categories gone from `nolints.json`.
- `jq 'length' scripts/nolints.json` reports 218.

---

### Phase 7: `structureInType` -> in-source `@[nolint]` [NOT STARTED]

**Goal**: Move the single `structureInType` exemption from the central JSON to the declaration
itself, with the large-elimination reason stated at the site.

**Tasks**:
- [ ] Locate the declaration: `grep -n "MembershipWitness" FormalSystem/Automation/ProofSearch/Core.lean`.
- [ ] Add `@[nolint structureInType]` to `FormalSystem.Automation.MembershipWitness`, with a
      comment stating the reason: the `Type` universe is load-bearing because
      `findMembershipWitness` returns `Option (MembershipWitness Γ φ)` and the proof-search layer
      eliminates it in data position, which a `Prop`-valued structure could not support (large
      elimination). This is the same argument `NAMING_CONVENTION_DEVIATION.md` already makes for
      `DerivationTree`.
- [ ] Drop the row:
      `jq 'map(select(.[0] == "structureInType" | not))' scripts/nolints.json > /tmp/n.json && mv /tmp/n.json scripts/nolints.json`

**Timing**: 0.5 hours

**Depends on**: 6

**Verification Tier**: local

**Scope Hypothesis**: exactly 1 `structureInType` entry, on `FormalSystem.Automation.MembershipWitness`.
Confirm with `jq -r '.[] | select(.[0]=="structureInType")' scripts/nolints.json` before editing.

**Files to modify**:
- `FormalSystem/Automation/ProofSearch/Core.lean` - add `@[nolint structureInType]` + reason comment
- `scripts/nolints.json` - drop the 1 row (218 -> 217)

**Verification**:
- `lake env lean FormalSystem/Automation/ProofSearch/Core.lean` exits 0 with zero diagnostics.
- `lake exe runLinter FormalSystem` exits 0 — proving the in-source attribute genuinely suppresses
  the finding that the JSON row used to.
- `jq -r '.[][0]' scripts/nolints.json | sort -u` prints exactly `unusedArguments`, and
  `jq 'length'` reports 217.

---

### Phase 8: Record the policy; correct the stale claims [NOT STARTED]

**Goal**: Refresh `docs/development/NAMING_CONVENTION_DEVIATION.md` against measured values, add
the evidence-backed `unusedArguments` grandfathering rationale, and correct the stale numeric and
status claims in `ci.yml` and `check-module-invariants.sh`.

**Tasks**:
- [ ] **`docs/development/NAMING_CONVENTION_DEVIATION.md`**:
  - [ ] Rewrite the "Outcome" table against post-burndown measured values. It currently asserts
        `defsWithUnderscore` after = 0 while the pre-task live count was 33, `unusedArguments` =
        124 (live 217), and `docBlame` = 39 (live 51). Record the values measured at the end of
        Phase 7, not the ones quoted here.
  - [ ] Correct the "How to re-audit" section: it states "CI runs `lean-action` with
        `lint: false`". CI now sets `lint: true` and `lake lint` gates.
  - [ ] Note that `defsWithUnderscore` reopened after being declared CLOSED, and that this task
        re-closed it — the document's own "What would reopen this" section is the right home.
  - [ ] Add the `unusedArguments` permanent-grandfathering rationale, with the measurement as
        evidence: 207/217 (95.4%) have *only* instance-implicit arguments unused, dominated by
        `[DecidableEq sig.preds]` ×130, `[Fintype sig.preds]` ×122, `[Nontrivial D]` ×41,
        `[IsDualClosed C]` ×23, `[IsOrderedAddMonoid D]` ×8; concentrated 167/217 in
        `Metalogic.WeakCanonical`. These are typeclass parameters retained for signature
        uniformity across families sharing one interface; the linter's advice to delete them is
        wrong for such a family.
  - [ ] Record the 10 non-instance `unusedArguments` findings as a named future item (they are
        genuine dead hypotheses, but removing them is a signature change with call-site fallout,
        deliberately out of scope here — see Non-Goals).
  - [ ] Extend the existing "The surviving exemptions, and why they are not a new suppression
        file" section to cover the new in-source exemptions added in Phases 6 and 7
        (`@[nolint docBlame]` ×3 on `where`-helpers, `@[nolint structureInType]` ×1).
- [ ] **`.github/workflows/ci.yml`**: re-derive anchors with
      `grep -n "307\|dupNamespace" .github/workflows/ci.yml`, then correct "grandfathers the 307
      pre-existing findings" -> 217, and the "dupNamespace … 14 pre-existing warnings in
      ChronicleTypes.lean" note -> 0.
- [ ] **`scripts/check-module-invariants.sh`**: re-derive anchors with
      `grep -n "307\|same 14\|Validated against" scripts/check-module-invariants.sh` — **the
      report's `:434`/`:1395`/`:1416-1421` are already stale; at plan time they read `:435`,
      `:1497`, and `:1509-1523`**. Correct both "grandfathers the 307 findings" occurrences -> 217;
      update the C16 header summary's category list (the batch now grandfathers only
      `unusedArguments`); and reword the dupNamespace validation comment, whose anchor ("finds
      exactly the same 14 declarations") disappears with this work. Record in its place that
      `lake env lean <file>` re-elaborates one file against existing oleans in ~2 s, runs the real
      `dupNamespace` linter, writes no oleans, and is therefore a cheap real-linter cross-check —
      distinct from the ~10-minute `lake lint --builtin-only --lint-only .dupNamespace` full-rebuild
      path the surrounding comment is actually about.

**Timing**: 1.25 hours

**Depends on**: 7

**Verification Tier**: prose

**Scope Hypothesis**: seven stale claims across `ci.yml` (2) and `check-module-invariants.sh` (4),
plus the `NAMING_CONVENTION_DEVIATION.md` Outcome table and re-audit section. Confirm by grepping
each file for the literal stale strings before editing; if a grep returns a count other than the
one asserted here, the hypothesis is falsified and the true set governs.

**Files to modify**:
- `docs/development/NAMING_CONVENTION_DEVIATION.md` - Outcome table, re-audit section,
  `unusedArguments` rationale, surviving-exemptions section
- `.github/workflows/ci.yml` - 2 comment corrections
- `scripts/check-module-invariants.sh` - 4 comment corrections (header summary, two "307"
  occurrences, dupNamespace validation note)

**Verification**:
- Diff read-through confirming every changed hunk in `ci.yml` and `check-module-invariants.sh`
  lies inside a `#` comment — no executable line changed. This is the `prose` tier's obligation
  and its stated blind spot; a hunk that crosses out of a comment escalates the phase to `local`
  and requires re-running the script.
- `grep -rn "307" .github/workflows/ci.yml scripts/check-module-invariants.sh` returns nothing.
- `bash scripts/check-module-invariants.sh --no-build` exits with its usual status (the fast
  structural pass proves the edits did not break the script's own syntax).
- `specs/reviews/review-2026-09-07.md` is confirmed **unmodified** — it is a dated historical
  record, deliberately left stale.

---

### Phase 9: Acceptance gate [NOT STARTED]

**Goal**: Prove every acceptance criterion from the task description in one clean pass, on a tree
with all prior phases landed.

**Tasks**:
- [ ] Run the full guarded build from a clean state.
- [ ] Run the complete gate set and record each result.
- [ ] If any gate fails, do not paper over it — reopen the owning phase.

**Timing**: 0.75 hours

**Depends on**: 8

**Verification Tier**: full

**Scope Hypothesis**: `nolints.json` at exactly 217 entries, all `unusedArguments` — a 90-entry
(29%) reduction from 307. Confirm with `jq 'length'` and `jq -r '.[][0]' | sort -u`; the criterion
is "shrinks by at least the categories the recorded policy commits to", so a count above 217 that
is still all-`unusedArguments` would need investigating rather than accepting.

**Files to modify**: none (verification only)

**Verification**:
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached) exits 0.
- `lake lint` exits 0.
- `lake exe runLinter FormalSystem` exits 0.
- `jq 'length' scripts/nolints.json` = 217; `jq -r '.[][0]' scripts/nolints.json | sort -u` prints
  only `unusedArguments`.
- `lake env lean FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` prints zero
  `dupNamespace` warnings.
- `bash scripts/check-module-invariants.sh` reports `PASS C16 dupNamespace: zero declaration(s) …`
  and `PASS C16 env_linter batch … has no un-nolisted finding`.
- `grep -rn "length_range_map" FormalSystem/ Tests/` returns nothing.

## Lean Challenge Statements

This is a linter-hygiene and documentation task: the `- **Goals**:` bullets above name **zero new
Lean declarations**, so the identifier set pinned by this section is empty and no ```lean fenced
block is present. Every Lean-file edit in this plan is a rename, a docstring, an attribute, a
declaration relocation, or a lemma deletion. No theorem statement or proof term is introduced, and
the one deletion (`length_range_map`) removes a lemma whose body is literally `by simp` and which
duplicates two Mathlib simp lemmas. No `sorry` and no new axiom is introduced at any phase.

## Testing & Validation

- [ ] `lake build` exits 0 (guarded, detached) after each of Phases 1, 2, 4, 6, and 9.
- [ ] `lake lint` exits 0 at Phase 9.
- [ ] `lake exe runLinter FormalSystem` exits 0 after every phase that edits `nolints.json`
      (1, 4, 6, 7) and at Phase 9.
- [ ] `lake env lean <file>` reports zero diagnostics for each directly edited Lean file.
- [ ] `scripts/nolints.json` = 217 entries, all `unusedArguments`.
- [ ] `dupNamespace` = 0, confirmed independently by the real linter (`lake env lean`) and by
      C16's textual scanner.
- [ ] `simpNF` = 0 and no `length_range_map` reference survives.
- [ ] `bash scripts/check-module-invariants.sh` passes both C16 halves.
- [ ] `lake exe runLinter --update` was never run (verifiable from the command log and from the
      fact that `nolints.json` diffs are per-category removals, not wholesale rewrites).

## Artifacts & Outputs

- `specs/539_linter_debt_burndown_nolints_dupnamespace/plans/01_linter-debt-burndown.md` (this file)
- `specs/539_linter_debt_burndown_nolints_dupnamespace/summaries/01_linter-debt-burndown-summary.md`
- `scripts/nolints.json` reduced 307 -> 217
- `docs/development/NAMING_CONVENTION_DEVIATION.md` refreshed and extended with the recorded policy
- `.github/workflows/ci.yml` and `scripts/check-module-invariants.sh` comment corrections
- Lean source edits across `FormalSystem/BaseLanguage/`, `FormalSystem/Metalogic/`,
  `FormalSystem/Automation/`, `FormalSystem/Theorems/`, `FormalSystem/Semantics/`,
  `FormalSystem/StarLanguage/`

## Rollback/Contingency

Every phase is independently committable and independently revertible; the commit-per-green-substep
mandate means a failed phase never leaves a half-applied tree committed.

- **Per-phase revert**: `git revert <phase commit>` restores both the Lean edits and the matching
  `nolints.json` rows, since each phase commits them together. The categories are mutually
  independent, so reverting one leaves the others green.
- **Phase 2 is the highest-risk single edit** and lands on its own commit specifically so it can
  be reverted without disturbing the rename phases. If the full build reveals a downstream
  `open …Chronicle` breakage that the in-phase contingency cannot resolve cleanly, revert Phase 2
  alone; Phases 1 and 3-9 remain valid and the `dupNamespace` goal moves to a follow-up task.
- **Never reset a dirty tree**: if a rollback is needed mid-phase, run
  `bash .claude/scripts/git-snapshot.sh 539` first, then the destructive command.
- **`nolints.json` is fully recoverable** from git at any point; it is never regenerated with
  `--update`, so no revert can silently re-grandfather a regression.
