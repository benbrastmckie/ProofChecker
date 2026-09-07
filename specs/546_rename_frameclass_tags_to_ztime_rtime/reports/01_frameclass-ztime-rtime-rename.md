# Research: Renaming `FrameClass.Discrete`/`.Dedekind` to `.ZTime`/`.RTime`

## Summary

The rename is mechanically tractable but **not** a global search-and-replace. The words
`Discrete` and `Dedekind` are each used in this tree in **two unrelated senses**, and only one
of them is in scope:

| Sense | Example | Action |
|-------|---------|--------|
| The **frame class** / the logic over it | `FrameClass.Dedekind`, `ValidDedekind`, `CompactDedekind` | **RENAME** |
| The bare **order condition** or a genuinely different notion | `TaskFrame.IsDiscrete`, `HasDedekindINF`, `Axiom.discrete_symm_fwd` | **KEEP** |

A naive `s/Dedekind/RTime/g` would destroy a ~500-occurrence Dedekind-INF/SUP API
(`HasDedekindINF`, `HasFaithfulDedekindSUP`, `HasGuardedDedekind*`, ...) that has nothing to do
with the frame class. Likewise `s/discrete/ztime/g` would rename five *axiom* constructors
(`discrete_symm_fwd`, `discrete_propagate_bwd`, ...) whose names refer to the DF correspondent,
which the task explicitly says to keep.

**Measured edit surface (in-scope tokens only):** 1,424 lines across **109 live files**
(FormalSystem excluding Boneyard, plus Tests), plus 3 shell scripts, 8 typst files, 13 docs,
and 2 generated artifacts. 27 Boneyard files also match and are recommended out of scope.

## Naming scheme (recommended)

One scheme, three casings, applied by grammatical position — matching what the tree already
does with `Discrete`/`discrete`:

| Position | Old | New | Example |
|----------|-----|-----|---------|
| PascalCase (types, constructors, `Prop`-valued defs) | `Discrete` / `Dedekind` | `ZTime` / `RTime` | `ValidDedekind` -> `ValidRTime` |
| lowerCamel (lemma-name segment referring to a PascalCase def) | `discrete` / `dedekind` | `zTime` / `rTime` | `validDiscrete_iff_check` -> `validZTime_iff_check` |
| snake_case (lemma-name segment) | `discrete` / `dedekind` | `ztime` / `rtime` | `soundness_dedekind` -> `soundness_rtime` |

This is the scheme the task description itself proposes (`soundness_ztime`, `ValidZTime`,
`TMCompleteZTime`); nothing found in the codebase argues against it.

Record it in `docs/development/NAMING_CONVENTION_DEVIATION.md`, which currently contains **no**
`Discrete`/`Dedekind` rows at all — the deviation it will record is the inverse of today's:
today the tree deviates from the paper by calling the dense-and-complete class `Dedekind`; after
the rename the tree matches the paper's `TM_r`/R-time convention, and the surviving deviation to
record is that the *conditions* keep the paper's names (`Discrete`, `Dense`, `Complete`) while
the *classes* take the z/d/r names.

## In-scope inventory

### Tier 1 — core definitions (4 declarations, 3 files)

| Old | New | Site |
|-----|-----|------|
| `FrameClass.Discrete` | `FrameClass.ZTime` | `ProofSystem/Axioms.lean:529` (+ `LE` instance :536-543, 8 order-shape `example`s, `Axiom.minFrameClass`) |
| `FrameClass.Dedekind` | `FrameClass.RTime` | same |
| `TaskFrame.IsSuccArchDiscrete` | `TaskFrame.IsZTime` | `Semantics/FrameProperty.lean:161` |
| `TaskFrame.IsDedekind` | `TaskFrame.IsRTime` | `Semantics/FrameProperty.lean:212` |

Satellite lemmas at the same sites:

| Old | New |
|-----|-----|
| `isSuccArchDiscrete_of_instances` | `isZTime_of_instances` |
| `IsSuccArchDiscrete.elim` | `IsZTime.elim` |
| `isDense_of_isDedekind` | `isDense_of_isRTime` |
| `isComplete_of_isDedekind` | `isComplete_of_isRTime` |

Note `isDense_of_isDedekind` is consumed by `FrameClass.Sat`'s monotonicity proof
(`FrameClassValidity.lean:198`) — the `Dense <= Dedekind` projection.

### Tier 2 — validity predicates and their lemma families

`ValidDiscrete`, `ValidDedekind` (`Semantics/Validity.lean`); `BLValidDiscrete`,
`BLValidDedekind`, `BLValidDiscreteSucc` (`Semantics/BLValidity.lean`); `StarValidDiscrete`,
`StarValidDedekind` (`Semantics/StarValidity.lean`); `carrierDiscrete`, `carrierDedekind`
(`Decidability/Verified/Decidable.lean` — `carrierDedekind` is literally
`DenselyOrdered D /\ (LUB clause)`, i.e. `IsRTime` in carrier form).

Dependent lemmas: `validDiscrete_iff_validIn_discrete`, `validDedekind_iff_validIn_dedekind`,
`valid_implies_valid_discrete`, `valid_implies_validDedekind`, `validDedekind_of_validComplete`,
`isValid_validDiscrete`, `isValid_validDedekind`, `validDiscrete_iff_check`,
`validDiscrete_iff_checkFamily`, `validDiscrete_iff_validInt`, `truthAt_of_validDiscrete`,
`not_validDiscrete_of_hasOpen_int`, `not_validDiscrete_of_satAtState`,
`not_validDedekind_of_hasOpen`, `blValidDiscrete_iff_validDiscrete_tr`, `blValidDiscrete_z1`,
`blValid_implies_blValidDiscrete`, `blValid_implies_blValidDedekind`,
`blValid_implies_blValidDiscreteSucc`, `decidableValidDiscrete`, `decidableValidDiscreteFamily`.

**`ValidComplete` stays.** It is the density-free `ValidOnFrames TaskFrame.IsComplete`, keyed to
the *bare* Complete clause, and is deliberately not a soundness target
(`Semantics/Validity.lean`). Renaming it would re-introduce exactly the confusion this task
removes.

### Tier 3 — metalogical statements over the class

Clean block in `Metalogic/SetConsequence.lean` (every one is literally `X FrameClass.Dedekind`):
`StrongCompletenessDiscrete`, `StrongCompletenessDedekind`, `CompactDiscrete`, `CompactDedekind`,
`SatisfiableDiscreteSet`, `SatisfiableDedekindSet`, `SetSemanticConsequenceDiscrete`,
`SetSemanticConsequenceDedekind`, `ModelExistenceDedekind`.

Elsewhere: `SemanticConsequenceDiscrete`/`Dedekind`, `semantic_deduction_discrete`/`dedekind`,
`soundness_discrete{,_valid,_consequence}`, `soundness_dedekind{,_valid,_consequence}`,
`completeness_discrete`, `completeness_dedekind{,_engine,_of_engine}`,
`consequence_completeness_discrete`, `consequence_completeness_dedekind{,_of_engine}`,
`axiom_discrete_valid`, `axiom_dedekind_valid`, `notCompactDiscrete`, `notCompactDedekind`,
`notStrongCompletenessDiscrete`, `notStrongCompletenessDedekind`, `modelExistenceDedekind_refuted`,
`TMCompleteDiscrete`, `ForwardDiscrete`, `tmCompleteDiscrete_iff_forwardDiscrete`,
`tmCompleteDedekind_iff_forwardDedekind`, `tmCompleteDiscrete_refuted`,
`bl_soundness_discrete{,_valid,_succ,_succ_valid}`, `bl_soundness_dedekind{,_valid}`,
`bl_not_derivable_nil_bot_discrete`, `bl_derivable_valid_and_swap_valid_discreteSucc`,
`star_soundness_discrete`/`dedekind`, `star_of_tm_discrete`/`dedekind`,
`star_backward_discrete`/`dedekind`, `forward_star_discrete`/`dedekind`,
`starDerivable_ofFormula_iff_discrete`/`dedekind`, `tmFrag_complete_discrete`/`dedekind`,
`tmFrag_z1_discrete`, `tm_lt_tmFrag_discrete`, `discreteRules`/`dedekindRules`
(`Decidability/Tableau.lean` — the per-class tableau rule sets; `dedekindRules` is
`[.priorUGap, .priorSGap, .sepRule]`), `sat_discrete_{,s}subset_mod_axiomSet`,
`sat_dedekind_{,s}subset_mod_axiomSet`, `mod_axiomSet_dedekind_subset_sat_dense`.

Tests-side: `discreteRows`, `dedekindRows` in `Tests/BimodalTest/TableauConformance.lean`.

## Explicit KEEP list (do NOT rename)

1. **Bare conditions**: `TaskFrame.IsDiscrete`, `TaskFrame.IsComplete`, `TaskFrame.IsDense`,
   `ValidComplete`, `validOn_df_iff_isDiscrete`, `validOn_nextTop_iff_isDiscrete`,
   `galoisClosed_isDiscrete`, `mod_axiomSet_discrete_subset_isDiscrete`.
2. **Axiom names and their soundness lemmas**: `Axiom.discrete_box_necessity`,
   `discrete_propagate_fwd`/`_bwd`, `discrete_symm_fwd`/`_bwd`, plus `*_valid` and
   `*_swap_valid` variants. Verified: `discrete_symm_fwd_swap_valid` is stated at
   `ValidIn FrameClass.Base` — it names the axiom, not the class. The matching string literals
   in `Automation/{AxiomNames,BenchmarkAnchors,DatasetGenerator,ForwardProofGenerator,ProofStepExport,ProofStepExtractor,MachineAppendixExport}.lean`
   keep their spelling too. `Axiom.minFrameClass` confirms only `prior_UZ`, `prior_SZ`, `z1` are
   `.Discrete` and only `prior_U_gap`, `prior_S_gap`, `sep` are `.Dedekind`.
3. **The entire Dedekind-INF/SUP API** (~500 occurrences): `HasDedekindINF`, `HasDedekindSUP`,
   `HasFaithfulDedekind{INF,SUP}`, `HasGuardedDedekind{INF,SUP}`, `HasDenseDedekind{INF,SUP}`,
   every `*.toHas*` bridge, `prior_hasDedekind*`, `hasDedekind*_fails_*`,
   `canonExpand_hasFaithfulDedekind*`, `orderIsoRealOfDedekindDenseSeparable`,
   `prop42_contentful_of_dedekind`, `prop42_faithful_covers_what_dedekind_excludes`,
   `dedekind_box_dense_mem`, `MR_dedekind_shape_at_pR`. These are Dedekind cuts/completeness of
   *sets*, not the frame class.
4. **Discrete-order construction lemmas** (the ChronicleToCountermodel / GroupModel / Kamp
   families): `discreteEmbed`, `DiscreteF`, `SuccDiscreteF`, `discreteFmcs`, `discreteZero`,
   `succDiscreteFmcs`, `rootedSuccDiscreteFmcs`, `shiftedSuccDiscreteFmcs`, `cantorBfmcsDiscrete`,
   `box_stable_in_*_discrete_*`, `discrete_embed_*`, `discrete_f_*`, `discrete_rank_*`,
   `discrete_extended_*`, `discrete_extendPoint_*`, `discrete_inClosedInterval_*`,
   `discrete_no_gaps`, `no_gaps_discrete*`, `discrete_to_carrier*`, `discrete_game_*`,
   `discrete_ghr93_*`, `discrete_nf_*`, `discrete_muSig_*`, `discrete_stavi_*`,
   `kEquiv_monoDiscrete_*`, `chronicleDiscrete{Succ,Pred}`, `complete_duration_discrete_or_dense`,
   `countermodel_discrete*`, `DiscreteStructure`, `DiscreteHypothesis`,
   `filtered_model_exists_discrete`, `discrete_base_truth_lemma`.
   Verified: `discreteEmbed` takes `(fc : FrameClass)` as a *parameter* — "discrete" there is the
   N-indexed chain, not the tag.
5. **`layerReynoldsDedekind : String := "Reynolds Dedekind"`** — a layer label for the Reynolds
   axiom family, which genuinely encodes *definable Dedekind completeness*. Judgment call; the
   report recommends keeping it, but it is exported into the machine appendix, so if the planner
   decides otherwise the typst appendix must be regenerated.
6. **`FormalSystem/Boneyard/**`** (27 matching files). The archive is uncompiled and frozen;
   `check-module-invariants.sh` C11 checks only that its *imports* resolve, never identifier
   names, and B0/C3/C15 all exclude it by path. Renaming inside it would falsify a historical
   record for no build benefit.

## Coupled non-Lean artifacts (the real failure mode)

These are the parts a Lean-only rename will silently break.

### `scripts/check-module-invariants.sh` — C14 axiom baselines (blocking)

Hardcodes **fully qualified declaration names** twice each: once in the expected-output baseline
block and once in the `#print axioms` probe block. Affected lines:

- Baselines: 167, 828, 849, 850, 851, 862, 867, 868, 871, 873
- Probes: 177, 886, 907, 908, 909, 920, 925, 926, 929, 931
- Prose: 746, 759, 816, 819-820, 943, 1414

Names involved: `BXCanonical.completeness_discrete`, `completeness_dedekind`,
`consequence_completeness_discrete`, `completeness_discrete`, `soundness_discrete_consequence`,
`notStrongCompletenessDiscrete`, `notStrongCompletenessDedekind`, `modelExistenceDedekind_refuted`,
`tmCompleteDiscrete_iff_forwardDiscrete`, `tmCompleteDedekind_iff_forwardDedekind`. Each must be
updated in **both** blocks, or C14 fails.

### `scripts/typst-status-counts.sh` + `typst/generated/status.typ` (blocking)

Lines 52-53 grep `Axiom.minFrameClass`'s body for the literal strings `=> \.Discrete` and
`=> \.Dedekind`. After the rename both return **0**, silently. The emitted variables
`#let discrete-only-count = 3` / `#let dedekind-only-count = 3` in
`typst/generated/status.typ` are consumed by `typst/chapters/03-proof-theory.typ` as
`#discrete-only-count` / `#dedekind-only-count`. Check 2 of `scripts/typst-sync-check.sh`
compares a regenerated `status.typ` byte-for-byte against the committed one, so script,
generated file, and consumer must move together.

### `scripts/typst-sync-check.sh` Check 1 — backtick name resolution

Every backticked span in `typst/**/*.typ` must resolve against live Lean source. Affected:
- `typst/FormalFoundations.typ:421-422` — `#leansrc("Semantics.FrameProperty", "TaskFrame.IsSuccArchDiscrete")` and `"TaskFrame.IsDedekind"` (direct Tier-1 hits)
- `typst/chapters/03-proof-theory.typ` lines 14, 161, 203-242, 366 — backticked `Discrete`, `Dedekind`, `Base`, `Dense`
- `typst/chapters/06-notes.typ:104` — backticked `soundness_discrete`, `soundness_dedekind`
- `typst/chapters/ax-machine-appendix.typ:25`, `p4-dual-verification.typ:26`, `p2-decidability-practice.typ:31`
- `typst/FormalFoundations.typ:1278,1495` reference the *module* `Metalogic.BXCanonical.CompletenessDedekind` (unaffected if modules are not renamed — see Open Question)

### `typst/generated/machine-appendix.{jsonl,typ}`

`Automation/MachineAppendixExport.lean:120-121` emits `| .Discrete => "Discrete"` /
`| .Dedekind => "Dedekind"` into the `frame_class` field. Renaming the string literals requires
regenerating both files via `scripts/typst-machine-appendix.sh`, which Check 3 of
`typst-sync-check.sh` validates.

### Round-trip string parsers (must change in matched pairs)

| File | Direction |
|------|-----------|
| `Automation/DatasetExport.lean:573-574` | parse `"discrete"`/`"dedekind"` -> tag |
| `Automation/DatasetExport.lean:584-585` | tag -> `"Discrete"`/`"Dedekind"` |
| `Automation/ProofFirstExporter.lean:104` | parse `"discrete"` -> tag |
| `Automation/ProofStepExtractor.lean:207-208` | tag -> string |
| `Automation/TableauBridge.lean:307` | parse `"Discrete"` -> tag |
| `Automation/TraceExporter.lean:197` | parse `"Discrete"` -> tag |
| `Automation/MachineAppendixExport.lean:120-121` | tag -> string |
| `Tests/BimodalTest/TableauConformance.lean:807-808` | tag -> string |

Also `DatasetExport.lean:505` docstring names the accepted values. These are the CLI surface for
`lake exe dataset_generator`, `proof_first_generator`, `tableau_bridge`, `trace_exporter`; any
data file or invocation passing `--frame-class discrete` changes meaning.

### `scripts/nolints.json`

Contains `FormalSystem.Metalogic.Decidability.decidableValidDiscrete` and
`decidableValidDiscreteFamily` (lines 58, 60) as `docBlame` grandfather entries. If those two are
renamed, the entries go stale and C16 (`lake exe runLinter`) reports two **new** findings. Update
the entries by hand — do **not** regenerate `nolints.json`, which the script's own comment
forbids as a way to make a regression disappear.

### Docs (non-blocking but in scope)

`docs/project-info/known-limitations.md` (29), `docs/user-guide/architecture.md` (24),
`README.md` (23), `docs/reference/API_REFERENCE.md` (19), `docs/reference/axiom-reference.md` (15),
`docs/project-info/implementation-status.md` (8), `docs/reference/operators.md` (5),
`docs/research/BIMODAL_LOGIC.md` (4), `docs/development/MODULE_ORGANIZATION.md` (3), plus one line
each in `docs/research/competitive-landscape.md`, `docs/project-info/README.md`,
`docs/project-info/FEATURE_REGISTRY.md`, `docs/architecture/BFMCS_ARCHITECTURE.md`.
`scripts/boneyard-import-waivers.txt:48` mentions `IsSuccArchDiscrete / IsDedekind` in a comment.

## Docstring rewrite at `FrameClass.Sat`

`Semantics/FrameClassValidity.lean` currently carries three passages whose entire content is
"the tag does not mean what its name says":

- **:33-35** interpretation-of-record table -> rows become `.ZTime | TaskFrame.IsZTime` and
  `.RTime | TaskFrame.IsRTime`; the "Two of these are the *narrowed* member of a split pair"
  paragraph (:37-40) survives as a statement about `IsZTime` vs the bare `IsDiscrete`, which is
  still true and still worth saying.
- **:42-46** "**Naming deviation of record**" -> delete. Its subject (the tree calling the
  paper's Complete class `Dedekind`) ceases to exist; replace with a one-line statement that
  `.RTime` is the paper's `TM_r` / R-time class, dense and complete, exactly `R` by Holder.
- **:100-110** the two `**not**` bullets -> keep the substance (the tags are the *narrowed*
  predicates, not the bare clauses) but drop the second bullet's closing "the paper calls this
  property Complete, this tree calls it Dedekind" sentence.

Mirror sites carrying the same deviation prose: `Semantics/FrameProperty.lean:28-91` and
:176-215 (the `IsDedekind` docstring ends "'Dedekind complete' is the standard and unambiguous
name ... so it is what the dense-and-complete class is called here"), `Semantics/Validity.lean`
:617-622, :682, :736, :751-756, :804-813, `Semantics/BLValidity.lean:211-265`,
`Semantics/Correspondence/Indicator.lean:52,163`, and the long `FrameClass` docstring at
`ProofSystem/Axioms.lean:500-528`.

## Recommended execution order

The rename has **no green intermediate state** if Tier 1 is done first — changing the
constructors breaks all 109 files at once. Go **leaf-first** instead, so every phase ends on a
green `lake build`:

1. **Tier 3 families, one at a time.** Each is a self-contained identifier rename whose
   definition body is untouched (`CompactDedekind := Compact FrameClass.Dedekind` still
   type-checks as `CompactRTime := Compact FrameClass.Dedekind`). Build green after each.
   Update `check-module-invariants.sh` C14 baselines + probes in the same commit as the
   `Metalogic` names they quote.
2. **Tier 2 validity predicates.** Same property. Update `nolints.json` with
   `decidableValidDiscrete`.
3. **Tier 1 satellites**, then **Tier 1 predicates** (`IsSuccArchDiscrete` -> `IsZTime`,
   `IsDedekind` -> `IsRTime`) — 9 and 8 files respectively, still small.
4. **Tier 1 constructors** — the single atomic pass across all remaining files.
5. **String literals + round-trip parsers + Tests**, then regenerate
   `typst/generated/status.typ` and `machine-appendix.{jsonl,typ}`.
6. **Docstrings and docs prose.**

### Safe mechanical substitution for step 4

Verified against a qualifier survey of every `X.Discrete` / `X.Dedekind` occurrence in the tree:
the only qualified form is `FrameClass.Discrete`/`FrameClass.Dedekind`; every other apparent hit
(`FormalSystem.Metalogic.DiscreteNonCompactness`, `Kamp.DedekindINF`, `Theorems.DedekindDerived`,
...) is a longer module identifier that a trailing word boundary excludes. So

```
s/\.Discrete\b/.ZTime/g
s/\.Dedekind\b/.RTime/g
```

is safe for both the qualified and the anonymous-constructor forms (245 bare `.Discrete`, 167
bare `.Dedekind`, 280 `FrameClass.Discrete`, 193 `FrameClass.Dedekind`) — **provided** it is
applied only to files outside `FormalSystem/Boneyard/` and after step 5's string literals are
handled separately (the literals `"Discrete"`/`"Dedekind"` have no leading dot, so they are not
touched by this sed).

## Verification

`lake build` alone is **not sufficient**: the lakefile's `@[default_target]` is
`lean_lib FormalSystem` with `roots := #[FormalSystem]`, so `Tests/` (the separate
`lean_lib BimodalTest`) is not compiled. Boneyard is likewise never compiled.

Required gates:
1. `lake build` (FormalSystem)
2. `lake build BimodalTest` — or `lake test`; otherwise the 4 Tests files and
   `TableauConformance.lean`'s `#eval` blocks break undetected
3. `scripts/check-module-invariants.sh` — C14 (axiom baselines), C15 (paper anchors),
   C16 (`runLinter` vs `nolints.json`) are the three that this rename can regress
4. `scripts/typst-sync-check.sh` — all three checks
5. Sorry count unchanged (C3 asserts a structural sorry inventory of ZERO across non-Boneyard
   `FormalSystem/`)

Run builds detached and guarded per `context/project/lean4/operations/long-builds.md`.

## Open questions for the planner

1. **Module and file names.** `Metalogic/DedekindNonCompactness.lean`,
   `Metalogic/DiscreteNonCompactness.lean`, `Metalogic/BXCanonical/CompletenessDedekind.lean`,
   `Theorems/DedekindDerived.lean`, `Theorems/DiscreteUnfolding.lean`,
   `Metalogic/BXCanonical/DiscreteCarrierProbe.lean` are named after the frame class and would be
   inconsistent after an identifier-only rename. **Recommendation: defer.** Renaming them churns
   import lines tree-wide, invalidates `#leansrc("Metalogic.BXCanonical.CompletenessDedekind", ...)`
   at `typst/FormalFoundations.typ:1278,1495`, three `nolints.json` entries, and
   `check-module-invariants.sh:816`, for zero semantic gain. Note the residual inconsistency
   explicitly in the naming doc rather than leaving it undiscussed.
   (`Kamp/DedekindINF.lean` and `Kamp/DedekindINFDense.lean` are correctly named for the INF/SUP
   sense and should never be renamed.)
2. **`layerReynoldsDedekind`** — keep as an axiom-layer label, or rename? Report recommends keep;
   it names the Reynolds definable-completeness axioms, not the class.
3. **CLI compatibility.** Should `--frame-class discrete` remain an accepted *input* alias
   alongside `ztime` in `DatasetExport`/`ProofFirstExporter`/`TableauBridge`/`TraceExporter`?
   Accepting both costs 4 lines and protects existing data-generation invocations; emitting only
   the new name keeps the round-trip single-valued.
