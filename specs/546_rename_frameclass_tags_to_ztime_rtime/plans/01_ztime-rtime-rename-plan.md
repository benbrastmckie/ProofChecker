# Implementation Plan: Rename FrameClass tags to ZTime/RTime

- **Task**: 546 - Rename frameclass tags to ztime rtime
- **Status**: [IMPLEMENTING]
- **Effort**: 13.5 hours
- **Dependencies**: None
- **Research Inputs**: specs/546_rename_frameclass_tags_to_ztime_rtime/reports/01_frameclass-ztime-rtime-rename.md
- **Artifacts**: plans/01_ztime-rtime-rename-plan.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

Rename the two `FrameClass` constructors `.Discrete`/`.Dedekind` to `.ZTime`/`.RTime`, the two
frame predicates `TaskFrame.IsSuccArchDiscrete`/`IsDedekind` to `IsZTime`/`IsRTime`, and every
derived identifier that names the *frame class* (validity predicates, soundness/completeness
statements, tableau rule sets, string literals), while leaving the *bare order conditions*
(`IsDiscrete`, `IsDense`, `IsComplete`, `ValidComplete`), the axiom constructors
(`discrete_symm_fwd`, ...), the ~560-occurrence Dedekind-INF/SUP API, and the discrete-order
construction lemma families untouched. Execution is strictly leaf-first so every phase ends on a
green `lake build`; the one unavoidable atomic pass (the constructors themselves) is isolated in
Phase 5 and declared `atomic-batch`. No semantics or proof content changes: the definition of
done is `lake build` + `lake build BimodalTest` +
`scripts/check-module-invariants.sh` + `scripts/typst-sync-check.sh` all green, with the sorry
inventory unchanged at zero.

### Research Integration

The research report is integrated in full and drives the phase decomposition:

- The **two-senses** finding (frame class vs. bare order condition / Dedekind cuts) is the
  central constraint. A global `s/Dedekind/RTime/g` would destroy the Dedekind-INF/SUP API
  (measured 560 occurrences under `FormalSystem/`, non-Boneyard). Every rename phase therefore
  carries an explicit KEEP-list guard in its verification.
- The **leaf-first execution order** (Tier 3 -> Tier 2 -> Tier 1 satellites -> Tier 1
  predicates -> Tier 1 constructors -> literals -> prose) is adopted verbatim as the phase
  spine, because a Tier-1-first ordering has no green intermediate state.
- The **coupled non-Lean artifacts** finding (C14 baselines, `typst-status-counts.sh`,
  `typst/generated/`, round-trip parsers, `nolints.json`) is the identified silent-failure
  surface; each coupling is pinned to the phase that breaks it rather than deferred to a
  cleanup pass.
- The **safe mechanical substitution** (`s/\.Discrete\b/.ZTime/g`, `s/\.Dedekind\b/.RTime/g`,
  applied outside `Boneyard/` and after string literals are separated out) is adopted for
  Phase 5.
- Verified independently while planning: 81 live `.lean` files match `\.(Discrete|Dedekind)\b`
  outside Boneyard; `IsSuccArchDiscrete` in 9 files; `IsDedekind` in 8; `scripts/nolints.json`
  exists and carries the two `decidableValidDiscrete*` `docBlame` entries at lines 58 and 60;
  `scripts/typst-status-counts.sh` greps `'=> \.Discrete'` and `'=> \.Dedekind'` inside the
  `Axiom.minFrameClass` awk window; `check-module-invariants.sh` carries the ten affected
  fully-qualified names in both the baseline block (lines 167, 828, 849-851, 862, 867-868, 871,
  873) and the probe block (177, 886, 907-909, 920, 925-926, 929, 931).

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied as a `roadmap_path` for this dispatch, so no roadmap phases
are added. It does exist and mentions the affected identifiers (`completeness_discrete`,
`completeness_dedekind`, `ValidDiscrete`, `decidableValidDiscreteFamily`,
`countermodel_discrete`, `notStrongCompletenessDiscrete`) in its prose. Those mentions go stale
under this rename; Phase 8 updates the ones that name renamed declarations, and leaves the ones
that name KEEP-list declarations (`countermodel_discrete`,
`build_discrete_chronicle_over_non_archimedean_block_carrier...`) alone. This plan does not
otherwise modify ROADMAP.md structure or item status.

### Naming scheme (authoritative for every phase)

One scheme, three casings, applied by grammatical position:

| Position | Old | New | Example |
|----------|-----|-----|---------|
| PascalCase (types, constructors, `Prop`-valued defs) | `Discrete` / `Dedekind` | `ZTime` / `RTime` | `ValidDedekind` -> `ValidRTime` |
| lowerCamel (segment naming a PascalCase def) | `discrete` / `dedekind` | `zTime` / `rTime` | `validDiscrete_iff_check` -> `validZTime_iff_check` |
| snake_case (lemma-name segment) | `discrete` / `dedekind` | `ztime` / `rtime` | `soundness_dedekind` -> `soundness_rtime` |
| String literals emitted for a class | `"Discrete"` / `"Dedekind"` | `"ZTime"` / `"RTime"` | `MachineAppendixExport.lean:120-121` |
| String literals parsed as CLI input | `"discrete"` / `"dedekind"` | `"ztime"` / `"rtime"` (legacy accepted, see Phase 6) | `DatasetExport.lean:573-574` |

### Planner decisions on the report's open questions

1. **Module and file names: DEFER.** `Metalogic/DedekindNonCompactness.lean`,
   `DiscreteNonCompactness.lean`, `BXCanonical/CompletenessDedekind.lean`,
   `Theorems/DedekindDerived.lean`, `Theorems/DiscreteUnfolding.lean`,
   `BXCanonical/DiscreteCarrierProbe.lean` keep their current names. Renaming them churns import
   lines tree-wide and invalidates `#leansrc("Metalogic.BXCanonical.CompletenessDedekind", ...)`
   at `typst/FormalFoundations.typ:1278,1495` plus `check-module-invariants.sh:816`, for zero
   semantic gain. Phase 8 records the residual file-name/identifier inconsistency explicitly
   rather than leaving it undiscussed. `Kamp/DedekindINF.lean` and `Kamp/DedekindINFDense.lean`
   are correctly named for the INF/SUP sense and are never renamed.
2. **`layerReynoldsDedekind`: KEEP.** It labels the Reynolds axiom family, which genuinely
   encodes definable Dedekind completeness, not the frame class. Keeping it also avoids a
   machine-appendix regeneration whose only content is a label change.
3. **CLI compatibility: emit new, accept both.** The four parser sites emit only `"ztime"`/
   `"rtime"` (and `"ZTime"`/`"RTime"` where PascalCase), but continue to accept the legacy
   `"discrete"`/`"dedekind"` spellings as deprecated input aliases, so existing
   `lake exe dataset_generator --frame-class discrete` invocations and any committed dataset
   rows keep working. Round-trip remains single-valued because emission is single-valued. If
   Phase 6 finds that a parser site has no persisted or documented external input (i.e. the
   alias protects nothing), the implementer may drop the alias for that site and record the
   drop as a Reasoned Exclusion.

### KEEP-list guard (run in every rename phase)

After each phase's edits, confirm none of the following moved:

```
git diff --name-only | grep -q 'FormalSystem/Boneyard/' && echo 'VIOLATION: Boneyard touched'
grep -rEc 'HasDedekind|HasFaithfulDedekind|HasGuardedDedekind|HasDenseDedekind' \
  FormalSystem --include=*.lean | grep -v Boneyard | awk -F: '{s+=$2} END {print s}'   # expect 560
grep -rE '\bTaskFrame\.(IsDiscrete|IsDense|IsComplete)\b' FormalSystem --include=*.lean | wc -l  # unchanged
grep -rE 'Axiom\.discrete_(box_necessity|propagate_(fwd|bwd)|symm_(fwd|bwd))' \
  FormalSystem --include=*.lean | wc -l                                               # unchanged
grep -rE '\bValidComplete\b|\bdiscreteEmbed\b|\blayerReynoldsDedekind\b' \
  FormalSystem --include=*.lean | wc -l                                               # unchanged
```

## Goals & Non-Goals

**Goals**:
- `FrameClass.Discrete` -> `FrameClass.ZTime`, `FrameClass.Dedekind` -> `FrameClass.RTime`.
- `TaskFrame.IsSuccArchDiscrete` -> `IsZTime`, `TaskFrame.IsDedekind` -> `IsRTime`, with their
  satellite lemmas.
- Every derived identifier naming the class renamed under one recorded scheme.
- Every coupled non-Lean artifact (C14 baselines and probes, `typst-status-counts.sh`,
  `typst/generated/status.typ`, `typst/generated/machine-appendix.{jsonl,typ}`,
  `scripts/nolints.json`, typst backtick spans) moved in the same phase that breaks it.
- `FrameClass.Sat` / `FrameProperty` / `Validity` / `BLValidity` naming-deviation prose replaced
  by plain statements of what each tag denotes.
- All gates green; sorry inventory unchanged at zero; no semantics or proof content changed.

**Non-Goals**:
- Renaming module or file names (deferred; see decision 1).
- Renaming the bare order conditions, the axiom constructors, the Dedekind-INF/SUP API, the
  discrete-order construction lemma families, or `layerReynoldsDedekind`.
- Editing `FormalSystem/Boneyard/**` (27 matching files, uncompiled and frozen).
- Regenerating `scripts/nolints.json` wholesale (hand-edit the two affected entries only).
- Any change to proof terms, tactic scripts, or statement content beyond identifier spelling.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A broad `s/Dedekind/.../g` destroys the 560-occurrence Dedekind-INF/SUP API | H | M | Only word-boundary-anchored, dot-anchored substitutions (`\.Dedekind\b`); KEEP-list guard run after every phase; the guard's 560 count is an exact expected value |
| `typst-status-counts.sh` silently returns 0 after the constructor rename | H | H | Phase 5 updates the two grep patterns in the same commit as the constructors; Phase 5 verification asserts `discrete-only-count`/`dedekind-only-count` are still 3/3 after regeneration |
| `check-module-invariants.sh` C14 fails because only one of the two blocks was updated | M | H | Phases 1-2 update baseline and probe lines as a matched pair, with a post-edit assertion that the two blocks name the same set of declarations |
| `scripts/nolints.json` goes stale, C16 reports two new `docBlame` findings | M | M | Phase 3 hand-edits lines 58 and 60 in the same commit as `decidableValidDiscrete*`; never regenerate the file |
| Tests break undetected (`lake build` default target excludes `BimodalTest`) | M | H | Every phase that touches Tests, and the final gate, run `lake build BimodalTest` explicitly |
| Phase 5's atomic pass leaves the tree red across many files | M | H | Declared `Commit Mode: atomic-batch`; the whole file set is one objective, intermediate per-file states are expected red and are not committed |
| Long Lean builds exhaust the dispatch | M | M | Run builds detached and guarded per `context/project/lean4/operations/long-builds.md` |
| Renaming a name that the paper anchors (C15) depend on | M | L | Phase 9 runs the full `check-module-invariants.sh`; C15 regressions surface there and are fixed forward |
| Accidental Boneyard edits falsify the historical archive | L | M | KEEP-list guard's first line fails the phase if any Boneyard path appears in the diff |

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

Phases within the same wave can execute in parallel. This plan is fully sequential: each phase
renames identifiers that later phases' files reference, and concurrent `lake build` runs in one
checkout contend for the same build artifacts.

---

### Phase 1: Tier 3a — Metalogic class-level statements and C14 baselines [COMPLETED]

**Goal**: Rename the self-contained metalogical statement families whose bodies still refer to
the unrenamed constructors, and move `check-module-invariants.sh`'s C14 baseline and probe lines
with them.

**Tasks**:
- [x] Rename the `Metalogic/SetConsequence.lean` block: `StrongCompletenessDiscrete`,
      `StrongCompletenessDedekind`, `CompactDiscrete`, `CompactDedekind`,
      `SatisfiableDiscreteSet`, `SatisfiableDedekindSet`, `SetSemanticConsequenceDiscrete`,
      `SetSemanticConsequenceDedekind`, `ModelExistenceDedekind`.
- [x] Rename `SemanticConsequenceDiscrete`/`Dedekind`, `semantic_deduction_discrete`/`dedekind`.
- [x] Rename the soundness family: `soundness_discrete{,_valid,_consequence}`,
      `soundness_dedekind{,_valid,_consequence}`, `axiom_discrete_valid`, `axiom_dedekind_valid`.
- [x] Rename the completeness family: `completeness_discrete`, `completeness_dedekind{,_engine,
      _of_engine}`, `consequence_completeness_discrete`,
      `consequence_completeness_dedekind{,_of_engine}`, and the `BXCanonical.` variants.
- [x] Rename the non-compactness family: `notCompactDiscrete`, `notCompactDedekind`,
      `notStrongCompletenessDiscrete`, `notStrongCompletenessDedekind`,
      `modelExistenceDedekind_refuted`.
- [x] *(deviation: added — `not_derivable_nil_bot_discrete` -> `not_derivable_nil_bot_ztime`, a class-naming soundness-family lemma in `Metalogic/Soundness.lean` not enumerated in the plan; renamed here with the rest of the soundness family.)*
- [x] Update `scripts/check-module-invariants.sh` C14 **baseline** lines 167, 828, 849, 850, 851,
      862, 867, 868, 871, 873 and **probe** lines 177, 886, 907, 908, 909, 920, 925, 926, 929,
      931 as a matched pair, plus the prose at 746, 759, 816, 819-820, 943, 1414. *(deviation: altered — baseline/probe lines 871/873 and 929/931 name `tmCompleteDiscrete_iff_forwardDiscrete` / `tmCompleteDedekind_iff_forwardDedekind`, which Phase 2 renames; moving them here would have broken C14 in this phase, so they are deferred to Phase 2. Prose lines 816 and 1414 name module/file names (`DiscreteNonCompactness.lean`, `MonoDiscrete.lean`) and `countermodel_discrete`, all on the KEEP list, so they were left unchanged.)*
- [x] Run the KEEP-list guard.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts ten C14-affected fully-qualified names across the
twenty enumerated baseline/probe lines. Confirm at implementation time with
`grep -nE 'completeness_(discrete|dedekind)|notStrongCompleteness|modelExistenceDedekind|tmComplete(Discrete|Dedekind)|soundness_discrete' scripts/check-module-invariants.sh`
and reconcile against the line list above before editing; if the counts differ, the line
numbers have drifted and the grep output is authoritative.

**Files to modify**:
- `FormalSystem/Metalogic/SetConsequence.lean` - rename the nine class-level statements
- `FormalSystem/Metalogic/**` (soundness, completeness, non-compactness modules) - rename the
  derived families and their call sites
- `scripts/check-module-invariants.sh` - C14 baselines, probes, and prose

**Verification**:
- `lake build` green (detached, per long-builds.md)
- `bash scripts/check-module-invariants.sh` C14 passes
- Baseline and probe blocks name the identical declaration set (diff the two extracted lists)
- KEEP-list guard clean

---

### Phase 2: Tier 3b — BL, Star, Conservativity, and tableau class families [COMPLETED]

**Goal**: Rename the remaining Tier 3 identifier families, which live outside `Metalogic/`'s
soundness/completeness core.

**Tasks**:
- [x] BL family: `bl_soundness_discrete{,_valid,_succ,_succ_valid}`,
      `bl_soundness_dedekind{,_valid}`, `bl_not_derivable_nil_bot_discrete`,
      `bl_derivable_valid_and_swap_valid_discreteSucc`.
- [x] Star family: `star_soundness_discrete`/`dedekind`, `star_of_tm_discrete`/`dedekind`,
      `star_backward_discrete`/`dedekind`, `forward_star_discrete`/`dedekind`,
      `starDerivable_ofFormula_iff_discrete`/`dedekind`.
- [x] Conservativity family: `TMCompleteDiscrete`, `ForwardDiscrete`,
      `tmCompleteDiscrete_iff_forwardDiscrete`, `tmCompleteDedekind_iff_forwardDedekind`,
      `tmCompleteDiscrete_refuted`, `tmFrag_complete_discrete`/`dedekind`,
      `tmFrag_z1_discrete`, `tm_lt_tmFrag_discrete`.
- [x] Tableau rule sets: `discreteRules`/`dedekindRules` in `Decidability/Tableau.lean`. *(deviation: altered — renamed to `zTimeRules`/`rTimeRules` per the lowerCamel row of the naming scheme.)*
- [x] Satisfiability-subset family: `sat_discrete_{,s}subset_mod_axiomSet`,
      `sat_dedekind_{,s}subset_mod_axiomSet`, `mod_axiomSet_dedekind_subset_sat_dense`.
      Leave `mod_axiomSet_discrete_subset_isDiscrete` alone (KEEP list — names the bare
      condition on its right-hand side).
- [x] Run the KEEP-list guard.
- [x] *(deviation: added — `scripts/check-module-invariants.sh` C14 baseline lines 871/873 and probe lines 929/931, deferred here from Phase 1, moved to `tmCompleteZTime_iff_forwardZTime` / `tmCompleteRTime_iff_forwardRTime` in the same commit as the declarations.)*

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts five identifier families enumerated from the research
report's Tier 3 list. Confirm completeness at implementation time by re-running
`grep -rnE '\b(bl_soundness|star_soundness|star_of_tm|star_backward|forward_star|starDerivable_ofFormula_iff|tmFrag_complete|sat_(discrete|dedekind))_' FormalSystem Tests --include=*.lean | grep -v Boneyard`
and confirming every hit is either renamed or on the KEEP list.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/**` - TMComplete/Forward/tmFrag families
- `FormalSystem/Metalogic/Conservativity/Star/**` - star families
- `FormalSystem/Metalogic/Decidability/Tableau.lean` - `discreteRules`/`dedekindRules`
- BL soundness modules under `FormalSystem/Metalogic/Conservativity/`

**Verification**:
- `lake build` green
- `bash scripts/check-module-invariants.sh` still green (C14 names from Phase 1 unchanged here)
- KEEP-list guard clean

---

### Phase 3: Tier 2 — validity predicates and `nolints.json` [NOT STARTED]

**Goal**: Rename the validity-predicate layer and the decidability instances, and hand-update
the two grandfathered `docBlame` entries so C16 does not regress.

**Tasks**:
- [ ] `Semantics/Validity.lean`: `ValidDiscrete` -> `ValidZTime`, `ValidDedekind` -> `ValidRTime`.
      Leave `ValidComplete` alone (KEEP list).
- [ ] `Semantics/BLValidity.lean`: `BLValidDiscrete`, `BLValidDedekind`, `BLValidDiscreteSucc`.
- [ ] `Semantics/StarValidity.lean`: `StarValidDiscrete`, `StarValidDedekind`.
- [ ] `Metalogic/Decidability/Verified/Decidable.lean`: `carrierDiscrete`, `carrierDedekind`.
- [ ] Rename the dependent lemma family: `validDiscrete_iff_validIn_discrete`,
      `validDedekind_iff_validIn_dedekind`, `valid_implies_valid_discrete`,
      `valid_implies_validDedekind`, `validDedekind_of_validComplete`, `isValid_validDiscrete`,
      `isValid_validDedekind`, `validDiscrete_iff_check`, `validDiscrete_iff_checkFamily`,
      `validDiscrete_iff_validInt`, `truthAt_of_validDiscrete`,
      `not_validDiscrete_of_hasOpen_int`, `not_validDiscrete_of_satAtState`,
      `not_validDedekind_of_hasOpen`, `blValidDiscrete_iff_validDiscrete_tr`,
      `blValidDiscrete_z1`, `blValid_implies_blValidDiscrete`, `blValid_implies_blValidDedekind`,
      `blValid_implies_blValidDiscreteSucc`, `decidableValidDiscrete`,
      `decidableValidDiscreteFamily`.
- [ ] Hand-edit `scripts/nolints.json` lines 58 and 60 to the new fully-qualified names. Do NOT
      regenerate the file.
- [ ] Run the KEEP-list guard.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: The research report measures `ValidDiscrete` at 135 lines in 26 files and
`ValidDedekind` at 103 lines in 24 files. Confirm before editing with
`grep -rcE '\bValid(Discrete|Dedekind)\b' FormalSystem Tests --include=*.lean | grep -v Boneyard | grep -v ':0'`
and confirm afterwards that the same count now matches `\bValid(ZTime|RTime)\b` and that
`\bValidComplete\b` is unchanged.

**Files to modify**:
- `FormalSystem/Semantics/Validity.lean`, `BLValidity.lean`, `StarValidity.lean`
- `FormalSystem/Metalogic/Decidability/Verified/Decidable.lean`
- ~26 call-site files under `FormalSystem/` and `Tests/`
- `scripts/nolints.json` - the two `decidableValidDiscrete*` `docBlame` entries

**Verification**:
- `lake build` green
- `lake build BimodalTest` green (Tests reference the validity predicates)
- `bash scripts/check-module-invariants.sh` C16 (`lake exe runLinter`) reports no new findings
- KEEP-list guard clean

---

### Phase 4: Tier 1 satellites and frame predicates [NOT STARTED]

**Goal**: Rename the two frame predicates and their satellite lemmas — the last step before the
constructors themselves.

**Tasks**:
- [ ] `Semantics/FrameProperty.lean:161`: `TaskFrame.IsSuccArchDiscrete` -> `TaskFrame.IsZTime`.
- [ ] `Semantics/FrameProperty.lean:212`: `TaskFrame.IsDedekind` -> `TaskFrame.IsRTime`.
- [ ] Satellites: `isSuccArchDiscrete_of_instances` -> `isZTime_of_instances`,
      `IsSuccArchDiscrete.elim` -> `IsZTime.elim`, `isDense_of_isDedekind` ->
      `isDense_of_isRTime`, `isComplete_of_isDedekind` -> `isComplete_of_isRTime`.
- [ ] Update the `FrameClass.Sat` monotonicity proof at
      `Semantics/FrameClassValidity.lean:198`, which consumes `isDense_of_isDedekind` as the
      `Dense <= Dedekind` projection.
- [ ] Update the comment mention in `scripts/boneyard-import-waivers.txt:48`
      (`IsSuccArchDiscrete / IsDedekind`).
- [ ] Run the KEEP-list guard, paying particular attention to `TaskFrame.IsDiscrete` being
      untouched.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: interface

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserted footprint is 9 files for `IsSuccArchDiscrete` and 8 for
`IsDedekind` (independently confirmed while planning). Re-confirm with
`grep -rl 'IsSuccArchDiscrete' FormalSystem Tests --include=*.lean | grep -v Boneyard` and the
`\bIsDedekind\b` equivalent before editing; a materially larger set means the KEEP-list boundary
was drawn wrong and must be re-checked before proceeding.

**Files to modify**:
- `FormalSystem/Semantics/FrameProperty.lean` - the two predicates and their satellites
- `FormalSystem/Semantics/FrameClassValidity.lean` - `Sat` interpretation and monotonicity proof
- ~15 further call-site files
- `scripts/boneyard-import-waivers.txt` - comment mention

**Verification**:
- `lake build` green
- `grep -rE '\bIs(SuccArchDiscrete|Dedekind)\b' FormalSystem Tests --include=*.lean | grep -v Boneyard`
  returns nothing
- `grep -rE '\bTaskFrame\.IsDiscrete\b'` count unchanged
- KEEP-list guard clean

---

### Phase 5: Tier 1 constructors — the atomic pass [NOT STARTED]

**Goal**: Rename `FrameClass.Discrete` -> `FrameClass.ZTime` and `FrameClass.Dedekind` ->
`FrameClass.RTime` across the whole live tree in one pass, and move
`scripts/typst-status-counts.sh`'s grep patterns with them.

**Tasks**:
- [ ] Edit `ProofSystem/Axioms.lean:529` — the `inductive FrameClass | Base | Dense | Discrete |
      Dedekind` declaration — plus the `LE` instance at :536-543, the eight order-shape
      `example`s, and `Axiom.minFrameClass`.
- [ ] Apply `s/\.Discrete\b/.ZTime/g` and `s/\.Dedekind\b/.RTime/g` to every live `.lean` file
      (`FormalSystem/` excluding `Boneyard/`, plus `Tests/`). String literals
      (`"Discrete"`/`"Dedekind"`, no leading dot) are deliberately untouched by this sed and are
      handled in Phase 6.
- [ ] Update `scripts/typst-status-counts.sh:52-53`: the greps `'=> \.Discrete'` and
      `'=> \.Dedekind'` become `'=> \.ZTime'` and `'=> \.RTime'`.
- [ ] Run the KEEP-list guard.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The research report measures 245 bare `.Discrete`, 167 bare `.Dedekind`,
280 `FrameClass.Discrete`, 193 `FrameClass.Dedekind`, over 81 live files (file count confirmed
while planning). Before the sed, re-run the qualifier survey the report relied on —
`grep -rhoE '[A-Za-z_.]*\.(Discrete|Dedekind)\b' FormalSystem Tests --include=*.lean | grep -v Boneyard | sort -u` —
and confirm the only qualified form is `FrameClass.`; any other qualifier means the
word-boundary sed is unsafe and the phase must stop and re-scope.

**Files to modify**:
- `FormalSystem/ProofSystem/Axioms.lean` - the inductive, `LE` instance, examples,
  `Axiom.minFrameClass`
- All 81 live `.lean` files matching `\.(Discrete|Dedekind)\b` outside `Boneyard/`
- `scripts/typst-status-counts.sh` - the two grep patterns

**Verification**:
- `lake build` green
- `lake build BimodalTest` green
- `grep -rE '\.(Discrete|Dedekind)\b' FormalSystem Tests --include=*.lean | grep -v Boneyard`
  returns nothing
- `bash scripts/typst-status-counts.sh` produces `discrete-only-count = 3` /
  `dedekind-only-count = 3` (or their renamed equivalents) — a `0` means the grep patterns were
  not moved
- `bash scripts/check-module-invariants.sh` green
- KEEP-list guard clean

---

### Phase 6: String literals, round-trip parsers, Tests, generated artifacts [NOT STARTED]

**Goal**: Move the class-naming string literals and their matched parsers, then regenerate the
two committed generated artifacts so the byte-for-byte typst checks pass.

**Tasks**:
- [ ] `Automation/MachineAppendixExport.lean:120-121` - emit `"ZTime"`/`"RTime"`.
- [ ] `Automation/ProofStepExtractor.lean:207-208` and `Tests/BimodalTest/TableauConformance.lean:807-808`
      - tag-to-string direction.
- [ ] `Automation/DatasetExport.lean:584-585` - tag-to-string; `:573-574` - string-to-tag,
      accepting `"ztime"`/`"rtime"` plus the legacy `"discrete"`/`"dedekind"` aliases; update the
      `:505` docstring listing accepted values.
- [ ] `Automation/ProofFirstExporter.lean:104`, `Automation/TableauBridge.lean:307`,
      `Automation/TraceExporter.lean:197` - same accept-both treatment.
- [ ] Rename `discreteRows`/`dedekindRows` in `Tests/BimodalTest/TableauConformance.lean`.
- [ ] Leave the axiom-name string literals in `Automation/{AxiomNames,BenchmarkAnchors,
      DatasetGenerator,ForwardProofGenerator,ProofStepExport,ProofStepExtractor,
      MachineAppendixExport}.lean` alone where they spell an *axiom* name (KEEP list); change
      them only where they spell a *class* (e.g. `fc := .Discrete` sites already handled by
      Phase 5).
- [ ] Regenerate `typst/generated/status.typ` via `scripts/typst-status-counts.sh`.
- [ ] Regenerate `typst/generated/machine-appendix.{jsonl,typ}` via
      `scripts/typst-machine-appendix.sh`.
- [ ] Run the KEEP-list guard.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: Asserted here are eight round-trip parser/emitter sites in matched pairs.
Confirm at implementation time with
`grep -rnE '"(discrete|dedekind|Discrete|Dedekind)"' FormalSystem Tests --include=*.lean | grep -v Boneyard`
and classify every hit as class-naming (change) or axiom-naming (keep) before editing. Any site
whose legacy input alias protects no persisted or documented input may have its alias dropped,
recorded as a Reasoned Exclusion.

**Files to modify**:
- `FormalSystem/Automation/{MachineAppendixExport,ProofStepExtractor,DatasetExport,
  ProofFirstExporter,TableauBridge,TraceExporter}.lean`
- `Tests/BimodalTest/TableauConformance.lean`
- `typst/generated/status.typ`, `typst/generated/machine-appendix.jsonl`,
  `typst/generated/machine-appendix.typ` - regenerated, not hand-edited

**Verification**:
- `lake build` and `lake build BimodalTest` green
- `bash scripts/typst-sync-check.sh` Check 2 (status.typ byte-for-byte) and Check 3
  (machine appendix) pass
- Round-trip smoke test: `lake exe dataset_generator --frame-class ztime` and
  `--frame-class discrete` both accepted; emitted `frame_class` field reads `ZTime`
- KEEP-list guard clean

---

### Phase 7: Lean docstring rewrite [NOT STARTED]

**Goal**: Replace the naming-deviation prose — which exists only to say "the tag does not mean
what its name says" — with plain statements of what each tag denotes.

**Tasks**:
- [ ] `Semantics/FrameClassValidity.lean:33-35` - interpretation-of-record table rows become
      `.ZTime | TaskFrame.IsZTime` and `.RTime | TaskFrame.IsRTime`. Keep the "Two of these are
      the *narrowed* member of a split pair" paragraph at :37-40; it remains true of `IsZTime`
      vs the bare `IsDiscrete`.
- [ ] `Semantics/FrameClassValidity.lean:42-46` - delete the "**Naming deviation of record**"
      passage; replace with one line stating that `.RTime` is the paper's `TM_r` / R-time class,
      dense and complete, exactly `R` by Holder.
- [ ] `Semantics/FrameClassValidity.lean:100-110` - keep the two `**not**` bullets' substance
      (the tags are the *narrowed* predicates, not the bare clauses); drop the second bullet's
      closing "the paper calls this property Complete, this tree calls it Dedekind" sentence.
- [ ] Mirror sites: `Semantics/FrameProperty.lean:28-91` and :176-215 (the `IsDedekind`
      docstring's closing "'Dedekind complete' is the standard and unambiguous name" paragraph),
      `Semantics/Validity.lean:617-622, :682, :736, :751-756, :804-813`,
      `Semantics/BLValidity.lean:211-265`,
      `Semantics/Correspondence/Indicator.lean:52,163`,
      `ProofSystem/Axioms.lean:500-528` (the long `FrameClass` docstring).
- [ ] Confirm no docstring edit crosses out of a `/-- ... -/` region.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Nine docstring sites are asserted, cited by line range from the research
report. Line numbers will have drifted after Phases 1-6; locate each by its quoted prose
(`Naming deviation of record`, `standard and unambiguous name`, the `**not**` bullets) rather
than by line number, and confirm the site count before editing.

**Files to modify**:
- `FormalSystem/Semantics/FrameClassValidity.lean` - three passages
- `FormalSystem/Semantics/FrameProperty.lean` - two docstrings
- `FormalSystem/Semantics/Validity.lean` - five passages
- `FormalSystem/Semantics/BLValidity.lean` - one block
- `FormalSystem/Semantics/Correspondence/Indicator.lean` - two lines
- `FormalSystem/ProofSystem/Axioms.lean` - the `FrameClass` docstring

**Verification**:
- Per-file `lake build` of each edited module (Lean doc comments compile; a mis-terminated
  `/-- -/` breaks the file)
- `lake build` green at phase close
- `git diff` read-through confirming every changed hunk lies inside a doc-comment region
- No `Dedekind`/`Discrete` remains in these docstrings except where it names a KEEP-list notion

---

### Phase 8: Typst prose, docs, and the naming-convention record [NOT STARTED]

**Goal**: Move every remaining prose reference — typst backtick spans (which are gated by
`typst-sync-check.sh` Check 1), repository docs, and the naming-convention deviation record.

**Tasks**:
- [ ] `typst/FormalFoundations.typ:421-422` - `#leansrc("Semantics.FrameProperty",
      "TaskFrame.IsSuccArchDiscrete")` and `"TaskFrame.IsDedekind"` -> the `IsZTime`/`IsRTime`
      forms. Leave :1278 and :1495 alone (they name the *module*
      `Metalogic.BXCanonical.CompletenessDedekind`, which is not renamed — decision 1).
- [ ] `typst/chapters/03-proof-theory.typ` lines 14, 161, 203-242, 366 - backticked `Discrete`,
      `Dedekind` class spans, and the `#discrete-only-count`/`#dedekind-only-count` consumers if
      Phase 6 renamed the emitted variables.
- [ ] `typst/chapters/06-notes.typ:104` - backticked `soundness_discrete`, `soundness_dedekind`.
- [ ] `typst/chapters/ax-machine-appendix.typ:25`, `p4-dual-verification.typ:26`,
      `p2-decidability-practice.typ:31`.
- [ ] Docs sweep: `docs/project-info/known-limitations.md` (29 lines),
      `docs/user-guide/architecture.md` (24), `README.md` (23),
      `docs/reference/API_REFERENCE.md` (19), `docs/reference/axiom-reference.md` (15),
      `docs/project-info/implementation-status.md` (8), `docs/reference/operators.md` (5),
      `docs/research/BIMODAL_LOGIC.md` (4), `docs/development/MODULE_ORGANIZATION.md` (3), and
      one line each in `docs/research/competitive-landscape.md`, `docs/project-info/README.md`,
      `docs/project-info/FEATURE_REGISTRY.md`, `docs/architecture/BFMCS_ARCHITECTURE.md`.
- [ ] `specs/ROADMAP.md` - update mentions that name renamed declarations
      (`completeness_discrete`, `completeness_dedekind`, `consequence_completeness_dedekind`,
      `ValidDiscrete`, `decidableValidDiscreteFamily`, `notStrongCompletenessDiscrete`,
      `validDiscrete_iff_checkFamily`). Leave KEEP-list mentions
      (`countermodel_discrete`, `build_discrete_chronicle_over_non_archimedean_block_carrier...`,
      "Reynolds Dedekind") unchanged. Do not alter item checkboxes or structure.
- [ ] `docs/development/NAMING_CONVENTION_DEVIATION.md` - add the z/d/r scheme table from this
      plan's Overview, state the surviving deviation (the *classes* take z/d/r names while the
      *conditions* keep the paper's `Discrete`/`Dense`/`Complete` names), and record the
      deferred module/file-name inconsistency from decision 1 explicitly.

**Timing**: 1.5 hours

**Depends on**: 7

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The docs line counts above are the research report's measurements and are
pre-rename. Re-measure with
`grep -rcE '\b(Discrete|Dedekind)\b' docs README.md typst --include=*.md --include=*.typ | grep -v ':0'`
before editing, and classify each remaining hit as class-naming (change) or condition/INF-SUP/
module-naming (keep). A residual count is expected and correct, not a failure.

**Files to modify**:
- `typst/FormalFoundations.typ`, `typst/chapters/*.typ` - backtick spans and `#leansrc` calls
- 13 docs files plus `README.md`
- `specs/ROADMAP.md` - prose mentions of renamed declarations only
- `docs/development/NAMING_CONVENTION_DEVIATION.md` - the new scheme record

**Verification**:
- `bash scripts/typst-sync-check.sh` all three checks pass (Check 1 resolves every backtick span
  against live Lean source)
- `git diff` read-through confirming every hunk is prose or a reference span, not code
- No renamed identifier's old spelling survives in docs except where it names a KEEP-list notion

---

### Phase 9: Final verification gate [NOT STARTED]

**Goal**: Run the complete gate set and confirm no regression in axioms, sorries, linter
findings, or paper anchors.

**Tasks**:
- [ ] `lake build` (FormalSystem default target), detached per long-builds.md.
- [ ] `lake build BimodalTest` (or `lake test`) — the default target does not compile `Tests/`.
- [ ] `bash scripts/check-module-invariants.sh` in full; confirm C3 (sorry inventory zero),
      C11 (Boneyard imports resolve), C14 (axiom baselines), C15 (paper anchors), C16
      (`runLinter` vs `nolints.json`) all pass.
- [ ] `bash scripts/typst-sync-check.sh` — all three checks.
- [ ] Final KEEP-list guard, plus a whole-tree assertion that no live `.lean` file outside
      `Boneyard/` still contains `\.(Discrete|Dedekind)\b`, `IsSuccArchDiscrete`, `IsDedekind`,
      `ValidDiscrete`, `ValidDedekind`, `soundness_discrete`, or `soundness_dedekind`.
- [ ] Confirm `git diff --stat` touches no `FormalSystem/Boneyard/` path.

**Timing**: 1 hour

**Depends on**: 8

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- None expected. Any edit here is a fix-forward repair of a gate failure and must be recorded in
  the implementation summary.

**Verification**:
- All five gates green
- Sorry count unchanged at zero for non-Boneyard `FormalSystem/`
- `runLinter` reports no new findings relative to the pre-task baseline

---

## Testing & Validation

- [ ] `lake build` green (FormalSystem)
- [ ] `lake build BimodalTest` green (Tests are not in the default target)
- [ ] `scripts/check-module-invariants.sh` green, with C3, C14, C15, C16 specifically confirmed
- [ ] `scripts/typst-sync-check.sh` green, all three checks
- [ ] `scripts/typst-status-counts.sh` still yields 3 / 3 for the two class-only axiom counts
- [ ] Sorry inventory unchanged at zero across non-Boneyard `FormalSystem/`
- [ ] `runLinter` reports no new `docBlame` findings (i.e. `nolints.json` was updated, not
      regenerated)
- [ ] `lake exe dataset_generator --frame-class ztime` and `--frame-class discrete` both accepted
- [ ] KEEP-list guard clean: Dedekind-INF/SUP API at 560 occurrences, bare conditions, axiom
      constructors, discrete-order construction lemmas, and `layerReynoldsDedekind` all unmoved
- [ ] No `FormalSystem/Boneyard/` path appears in the task's cumulative diff

## Artifacts & Outputs

- `specs/546_rename_frameclass_tags_to_ztime_rtime/plans/01_ztime-rtime-rename-plan.md` (this file)
- `specs/546_rename_frameclass_tags_to_ztime_rtime/summaries/NN_ztime-rtime-rename-summary.md`
- Renamed declarations across ~81 live `.lean` files under `FormalSystem/` and `Tests/`
- Updated `scripts/check-module-invariants.sh`, `scripts/typst-status-counts.sh`,
  `scripts/nolints.json`, `scripts/boneyard-import-waivers.txt`
- Regenerated `typst/generated/status.typ` and `typst/generated/machine-appendix.{jsonl,typ}`
- Updated `typst/**/*.typ` prose, 13 docs files, `README.md`, `specs/ROADMAP.md`
- New scheme record in `docs/development/NAMING_CONVENTION_DEVIATION.md`

## Rollback/Contingency

Every phase ends on a green `lake build` and is committed independently, so rollback is
`git revert` of the phase commits in reverse order — no phase depends on a later one to compile.

Phase 5 is the one exception: it is a declared `atomic-batch`, so its intermediate per-file
states are expected red and are never committed. If Phase 5 cannot be brought green, revert its
single commit (or discard the uncommitted batch after taking a snapshot with
`bash .claude/scripts/git-snapshot.sh 546`) and re-scope — do not attempt a partial constructor
rename, which leaves the tree unbuildable.

If a gate regresses in Phase 9, fix forward: correct the source to resolve the failure. Never
discard uncommitted changes to reach a passing build, and never regenerate `scripts/nolints.json`
to make a linter regression disappear — the script's own comment forbids it.
