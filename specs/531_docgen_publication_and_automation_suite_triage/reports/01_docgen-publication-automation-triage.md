# Research Report: Task #531

**Task**: 531 - docgen publication and automation suite triage
**Started**: 2026-09-07T14:08:00Z
**Completed**: 2026-09-07T15:05:00Z
**Effort**: L (four independent workstreams; item 5 and item 6/7 are separable)
**Dependencies**: 529, 530 (both completed; 530 pre-empted a large share of this task's scope)
**Sources/Inputs**:
- Codebase (`FormalSystem/`, `Tests/`, `scripts/`, `docs/`, `.github/workflows/`), measured directly
- `specs/reviews/2026-09-01-lean-engineering/{E-docs,G-ecosystem,D-tactics}.md` (findings E-08, G-09/10/11/14/16, D-02/D-14/D-17)
- `specs/530_*/summaries/01_documentation-single-source-of-truth-summary.md`
- `leanprover-community/docgen-action` `action.yml` and `README.md` (fetched, VERIFIED)
- lean-lsp MCP: not used (no proof-state question arose; every claim here is textual/structural)

**Artifacts**:
- `specs/531_docgen_publication_and_automation_suite_triage/reports/01_docgen-publication-automation-triage.md`

**Standards**: report-format.md, subagent-return.md

---

## Executive Summary

- **Roughly half the dispatch's WORK list is already done by task 530.** `references.bib` (13
  entries), `CITATION.cff`, `docs/ARCHITECTURE.md` and the "Verifying the main theorems" README
  section all exist; the broken `lake build :docs` recipe at `docs/README.md` was already fixed —
  in the *opposite* direction, by asserting that no doc-gen4 target exists. Implementing item (1)
  therefore requires **rewriting** `docs/README.md:272-278`, not just adding a workflow.
- **The MainResults.lean anti-drift requirement is already satisfied by a different mechanism.**
  C14 pins 101 declaration axiom-sets and C2 pins 4 (105 total, exactly as `README.md:351`
  claims). Every declaration the dispatch names for `MainResults.lean` — soundness ×4,
  completeness ×4, consequence completeness ×4, `strongCompletenessBase`/`Dense`,
  `compactBase`/`Dense`, both non-compactness refutations, `galoisClosed_mod`,
  `kampPriorExpressiveCompleteness`, `sound_of_isValid` — is **already pinned**. `MainResults.lean`
  should be a *navigation* artefact whose declaration set is asserted to be a subset of the C14
  pins, not a second baseline.
- **`docgen-action`'s `homepage` input defaults to `docs`, and this repo's `docs/` is not a Jekyll
  site.** The action expects `jekyll new docs` output and writes API docs to `docs/docs/`. Adopting
  it unchanged would collide with a 100+ file hand-maintained markdown tree. Use
  `build-page: false`, or point `homepage:` at a new folder. The action supplies doc-gen4 itself —
  **no `require «doc-gen4»` in `lakefile.lean` is needed**, which is strictly better than E-08's
  recommendation because `lake build` stays free of the dependency.
- **The automation triage has a stronger evidence base than the review recorded.** The
  `SearchConfig` weight fields are **write-only** — `Commands.lean:157` says so in source
  ("weights remain unused"). `temporal_search`, `propositional_search` and `tm_auto` therefore
  differ from `modal_search` in **documentation only**, and their docstrings make three false
  behavioural claims that doc-gen4 would publish. The `TMLogic` Aesop rule set (285 + ~35 lines)
  has **zero consumers**. Seven `Normalization.lean` tactics have zero library and zero test uses.
- **The nested-namespace-shadowing census reproduces at 17 pairs / 16 base names**, and the
  dispatch's "SEPARATE AND MORE SERIOUS FINDING" **is not a defect**: `mem_knownTimes_of_mem` at
  `CountermodelExtraction.lean:415` is `private`, so no two live declarations share a
  fully-qualified name anywhere in the tree except twelve `main` entry points that are never
  co-imported. Item (7)'s framing should be corrected before planning.
- **The Uppercase_x rename is only ~30% mechanical.** 107 live names match, but ~55 are
  operator-letter prefixes (`F_`, `P_`, `G_`, `H_`) naming the paper's tense operators, where
  dot-namespacing would invent namespaces that do not exist. The dispatch's two flagship examples
  (`CanonicalTask_backward_comp`, `Succ_implies_CanonicalR`) live **only in Boneyard** and are
  already out of scope.

---

## Context & Scope

Task 531 is WAVE 5 of the 2026-09-01 Lean engineering review: publish the API documentation, adopt
the repository furniture mature Lean libraries carry, and triage the bespoke automation suite by
evidence. Research scope was to establish the **current measured state** of each of the dispatch's
seven work items, because the dispatch text was authored before dependencies 529 and 530 landed and
several of its anchors are now stale.

Constraints observed: zero-debt policy (no `sorry`-deferral or axiom-introduction is recommended
anywhere below); no writes outside `specs/`; the blocked MCP tools
(`lean_diagnostic_messages`, `lean_file_outline`) were not called.

Everything below is re-derivable. Line numbers were read at 2026-09-07 against the working tree at
`921a97db2`.

---

## Findings

### Codebase Patterns

#### 1. Publication packaging: what 530 already landed

| Recipe step (G-ecosystem §8) | Status | Evidence |
|---|---|---|
| 1. Linter root `FormalSystem/Init.lean` + `checkInitImports` | **DONE** | `FormalSystem/Init.lean`; `scripts/CheckInitImports.lean`; `lean_exe checkInitImports` in `lakefile.lean` |
| 2. Turn CI on with `lint: true` | **DONE** | `.github/workflows/ci.yml` — `build: true`, `test: true`, `lint: true`, `use-mathlib-cache: true` |
| 3. `references.bib` | **PARTIAL** | File exists, 13 entries. Prose citations **not** converted to keys (see below) |
| 4. doc-gen4 on Pages | **NOT DONE** | `.github/workflows/` contains only `ci.yml`; `grep -i doc-gen lake-manifest.json` → 0 |
| 5. Main-results page + axiom audit | **NOT DONE (file)** / **DONE (mechanism)** | No `MainResults.lean` anywhere in the tree; but C2+C14 pin 105 axiom sets |
| 6. `CITATION.cff` | **DONE** | Root `CITATION.cff`, cff-version 1.2.0, includes the JPL paper as a reference |
| 7. Clean `lakefile.lean` task-number docstrings | **DONE** | No task-number citations remain in `lakefile.lean` |

Supporting facts:
- `.gitignore:32-34` already ignores `doc/` and `_site/`, anticipating a docs build.
- `git remote` is `git@github.com:benbrastmckie/BimodalLogic.git`.
- Root carries one stray artefact, `Scratch434.lean.tmp` (0 bytes, dated 2026-08-07), whose name is
  a task-number reference in a deliverable path. Delete it as part of packaging.

#### 2. `docs/README.md` now asserts the opposite of what item (1) requires

`docs/README.md:272-278` reads, in full:

> There is **no** generated API documentation target. `doc-gen4` is not a dependency of this
> project — it appears in neither `lakefile.lean` nor `lake-manifest.json` — so `lake build :docs`
> does not exist and does not work. […] Adding `doc-gen4` would be a real change to the build
> graph, not a documentation fix.

E-08 offered two exits ("add doc-gen4" or "delete the broken recipe"); 530 took the second. Task 531
takes the first. This section must be **replaced**, and C12/C13 (markdown path and link resolution
across `docs/` + `README.md`) must still pass afterwards.

#### 3. `docgen-action` inputs, verified against `action.yml`

| Input | Default | Relevance here |
|---|---|---|
| `api-docs` | `true` | Already the wanted value |
| `blueprint` | `false` | Already the wanted value |
| `build-page` | `true` | **Must be reconsidered — see below** |
| `deploy` | `true` | Deploys to Pages itself; no separate deploy job needed |
| `homepage` | `docs` | **Collides with this repo's `docs/`** |
| `references` | `references.bib` | Already the wanted value; the file already exists |
| `build-args` | `--log-level=warning` | Passed through to `leanprover/lean-action` |
| `lake-package-directory` | `.` | Correct as-is |
| `ruby-version` | `3.4` | Jekyll only |
| `use-github-cache` | `true` | Correct as-is |

Required workflow permissions: `contents: read`, `pages: write`, `id-token: write`. Pages source
must be set to **GitHub Actions** in repository settings (a manual, one-time step the workflow
cannot perform).

**The `homepage`/`docs` collision is the single non-obvious integration risk.** The action's README
instructs "Run `jekyll new docs` in your project folder and commit the resulting `docs` folder […]
the API documentation is placed in a `docs` subdirectory within it (i.e. `docs/docs/`)." This
repository's `docs/` is a hand-maintained tree of ~100 markdown files across
`architecture/`, `development/`, `installation/`, `papers/`, `project-info/`, `reference/`,
`research/`, `training/`, `user-guide/`, with no `_config.yml`. Two workable resolutions:
`build-page: false` (API docs only, simplest, no Jekyll), or `homepage: website` with a real Jekyll
site in a new folder. The first is recommended; the second is the upgrade path if a landing page is
later wanted.

**The action supplies doc-gen4 itself** (its step 7 generates API docs; the README never asks the
repository to declare it). So E-08's `require «doc-gen4» from git … @ "v4.33.0-rc1"` is **not
required and not recommended** — adding it would put doc-gen4 into `lake-manifest.json` and every
contributor's `lake build`. The toolchain (`leanprover/lean4:v4.33.0-rc1`) is comfortably past the
v4.28.0 floor the action's README mentions.

#### 4. `references.bib` is present but disconnected

`references.bib` holds 13 keys: `brastmckie2026construction`, `brastmckie2026bimodallogic`,
`burgess1982`, `kamp1968`, `reynolds1992`, `reynolds1994`, `gabbay1994`, `blackburn2002`,
`prior1967`, `doets1987`, `venema1993`, `xu1988`, `cmiel2021`.

Measured demand: scanning the 12 lines following every `## References` heading in live-scope
`.lean` files yields **190 prose citation occurrences** across 20 distinct works:

| Work | Occurrences | Bib key present? |
|---|---|---|
| Rabinovich 2014 | 71 | **NO** |
| Reynolds 1992 | 24 | yes |
| Reynolds 1994 | 18 | yes |
| Doets 1989 | 17 | **NO** (bib has `doets1987`) |
| Goldblatt 1992 | 14 | **NO** |
| Burgess 1984 | 13 | **NO** (bib has `burgess1982`) |
| Burgess 1982 | 9 | yes |
| Doets 1987 | 6 | yes |
| Xu 1988 | 3 | yes |
| Reynolds 1996 | 3 | **NO** |
| Doets 1987/1989 | 3 | partial |
| Burgess 1982/84 | 2 | partial |
| Verbrugge 2007, Venema 2001, Reynolds 2003, Fisher–Ladner 1979 | 1 each | **NO** |
| Venema 1993, Kamp 1968, Gabbay–Hodkinson–Reynolds 1994, BdRV 2002 | 1 each | yes |

227 `.lean` files carry a `## References` section. The single most-cited work in the tree
(**Rabinovich 2014, 71 occurrences**) has no bib entry at all. Item (2) is therefore two jobs:
**add ~9 missing entries**, then convert prose to keys.

Sample of the current form, for the planner's edit shape:
`ProofSystem/Axioms.lean:82-84` — `* Burgess 1982/84: Until-Since temporal logic axiomatization` /
`* Xu 1988: …` / `* Venema 1993: …`.

#### 5. MainResults.lean: the mechanism already exists

`scripts/check-module-invariants.sh` compiles a scratch file against the built library and diffs
`#print axioms` output against a frozen baseline, twice:
- **C2** (`:515-556`): 4 declarations — `BXCanonical.completeness`, `…completeness_dense`,
  `…completeness_ztime`, `…Chronicle.countermodel_dense`.
- **C14** (`:1316-1441`): **101** declarations.

Total 105, matching `README.md:351` exactly. Every declaration the dispatch names for
`MainResults.lean` is in that set, verified name-by-name:
`soundness`, `soundness_base/_dense/_ztime/_rtime`, `completeness_base/_dense/_ztime/_rtime`,
`consequence_completeness_base/_dense/_ztime/_rtime`, `strongCompletenessBase`,
`strongCompletenessDense`, `compactBase`, `compactDense`, `notCompactZTime`, `notCompactRTime`,
`notStrongCompletenessZTime`, `notStrongCompletenessRTime`, `galoisClosed_mod` (and four siblings),
`kampPriorExpressiveCompleteness`, `Decidability.sound_of_isValid`.

**Consequence for the plan**: do not add a third axiom baseline. `MainResults.lean` earns its place
as a single readable page — one `#check`/restatement + `#print axioms` per headline result, in the
shape `DiscreteNonCompactness.lean:292-312` and `DedekindNonCompactness.lean:473-490` already use
(`#print axioms notCompactZTime` at `:301`, `#print axioms notCompactRTime` at `:503`, each followed
by a docstring recording the verbatim output). The **anti-drift wiring that is genuinely missing** is
a check asserting *every declaration named in `MainResults.lean` appears in the C14/C2 baseline* —
so the page cannot advertise a result whose axiom set is unpinned. That is a ~15-line addition to
the existing script, not a new baseline.

There are already **71** `#print axioms` occurrences in live scope, so the idiom is established.

#### 6. Automation-suite triage: measured usage

Live-scope tactic inventory. "lib" excludes `FormalSystem/Automation/**` and `Boneyard`; counts
below are token occurrences on non-comment lines, refined by hand where a token is ambiguous.

| Tactic | Declared at | lib uses | test uses | Verdict |
|---|---|---|---|---|
| `modal_search` | `Tactics/Commands.lean:115,124` | **3** (all `Examples/BimodalProofs.lean:219,223,231`) | 83 | Keep — pedagogical entry point |
| `propDecide` | `Tactics/PropDecide.lean` | **12** (all `Metalogic/Algebraic/BooleanStructure.lean`) | 14 | Keep — promotion by 528 landed |
| `modal_t` | `Tactics/Helpers.lean:126` | 3 | 9 | Keep (small, cheap) |
| `deduction` / `deduction n` | `Tactics/Deduction.lean:112,117` | **0** (every apparent hit is prose) | 14 | Trial — see blocker below |
| `undischarge` | `Tactics/Deduction.lean` | **0** | 2 | Trial with `deduction` |
| `apply_axiom` | `Tactics/Helpers.lean:109` | **0** | 26 | Test-only |
| `assumption_search` | `Tactics/Helpers.lean:165` | **0** | 16 | Test-only |
| `tm_auto` | `Tactics/Commands.lean:318` | **0** | 65 | **Retire** — alias for `modal_search` |
| `temporal_search` | `Tactics/Commands.lean:196,200` | 2 (prose) | 16 | **Retire** — behaviourally identical to `modal_search` |
| `propositional_search` | `Tactics/Commands.lean:258,262` | 1 (prose) | 24 | **Retire** — behaviourally identical |
| `modal_k_tactic` | `Tactics/Helpers.lean:370` | 0 | 1 | Retire |
| `temporal_k_tactic` | `Tactics/Helpers.lean:390` | 0 | 1 | Retire |
| `modal_4_tactic` | `Tactics/Helpers.lean:412` | 0 | 8 | **Retire** |
| `modal_b_tactic` | `Tactics/Helpers.lean:464` | 0 | 7 | **Retire** |
| `modalNorm` | `Normalization.lean:188` | **0** | **0** | **Retire** |
| `propNorm` | `Normalization.lean:192` | **0** | **0** | **Retire** |
| `modalOpNorm` | `Normalization.lean:196` | **0** | **0** | **Retire** |
| `temporalNorm` | `Normalization.lean:201` | **0** | **0** | **Retire** |
| `modalNormAt` | `Normalization.lean:210` | **0** | **0** | **Retire** |
| `modalNormAll` | `Normalization.lean:216` | **0** | **0** | **Retire** |
| `modalFold` | `Normalization.lean:832` | **0** | **0** | **Retire** |

Three measurements that strengthen D-02 beyond what the review recorded:

**(a) The `modal_search` call site at `FormalSystem/FormalSystem.lean` is not a call site.**
The dispatch cites `FormalSystem.lean:64`. The real occurrence is
`FormalSystem/FormalSystem.lean:69`, inside a fenced ` ```lean ` block in the module docstring. The
same is true of `Automation.lean:56-66`. **The entire `Automation/Tactics/` suite has exactly three
compiled call sites in `FormalSystem/`, all in `Examples/`, all `modal_search`** — zero outside
pedagogical code.

**(b) `SearchConfig`'s weight machinery is write-only, and three docstrings lie because of it.**
`Tactics/Commands.lean:25-41` declares `axiomWeight`, `assumptionWeight`, `mpWeight`,
`modalKWeight`, `temporalKWeight`; `applyParams` (`:140-144`) accepts them from tactic syntax; and
`runModalSearch` (`:149-165`) reads only `depth` and `visitLimit`, with the in-source comment at
`:157` stating outright: *"weights remain unused"*. `ProofSearch/Core.lean:289-291,849-851` has its
own, separate, actually-read weights structure with different defaults. Consequences:
- `SearchConfig.temporal` (`:46-48`) and `SearchConfig.propositional` (`:51-54`) differ from
  `SearchConfig.default` **only in unread fields**, so `temporal_search`, `propositional_search` and
  `tm_auto` are behaviourally identical to `modal_search`.
- `Commands.lean:182-183` ("Prioritizes temporal K rules over modal K rules") and `:255`
  ("Disables modal K and temporal K rules (modalKWeight = 0, temporalKWeight = 0)") are **false
  claims in publication-facing docstrings**. doc-gen4 would publish them.

This resolves an apparent contradiction in the dispatch, which asks to retire "the SearchConfig
weight machinery" while keeping `modal_search` (which uses `SearchConfig`). The clean cut is: keep
`SearchConfig` with `depth` and `visitLimit`; delete the five weight fields, the two presets, and
their `applyParams` cases.

**(c) The `TMLogic` Aesop rule set has zero consumers.** `AesopRuleSet.lean:31` declares it;
`AesopRules.lean` (285 lines) registers rules into it. The only `aesop (rule_sets := [TMLogic])`
occurrence in the tree is `AesopRules.lean:61`, inside a docstring example, and
`AesopRules.lean:52-53` says `-- DEPRECATED: tm_auto no longer uses Aesop`. `Automation.lean:37`
confirms: "`tm_auto`: Alias for `modal_search` (previously Aesop-powered, now uses modal_search)".
So `AesopRules.lean` + `AesopRuleSet.lean` are entirely dead — a stronger claim than D-02 makes.

**(d) `deduction`'s non-adoption has a documented technical cause, not just neglect.**
`Tactics/Deduction.lean:32-38`: "`deductionTheorem` is `noncomputable` […] any `def`/`example` whose
proof term is produced by `deduction` or `undischarge` must be marked `noncomputable`. […] For
`Prop`-valued derivability statements, use `Derivable.deduction` instead — `Prop` proofs never need
the marker." `deductionTheorem` has 167 term-level uses in live scope and `Derivable.deduction` has
8. `Metalogic/Core/DeductionTheorem.lean` is 472 lines. The tactic form only helps
`DerivationTree`-valued (`Type`-valued) goals, and infects each with `noncomputable`. **The trial
should be time-boxed and is likely to conclude "no".**

**(e) `Helpers.lean`'s three-way split does not fall on clean line boundaries.**
1,210 lines. Actual structure:
- user tactics: `apply_axiom` :109, `modal_t` :126, `assumption_search` :165, predicate helpers
  `isBoxFormula` :211 / `isFutureFormula` :238 / `extractFromBox` :266 / `extractFromFuture` :294,
  factory `mkOperatorKTactic` :323, `modal_k_tactic` :370, `temporal_k_tactic` :390,
  `modal_4_tactic` :412, `modal_b_tactic` :464;
- reusable plumbing: `extractDerivationGoal` :524, `formulaHead` :655, `lemmaConclusionHead` :665,
  `isNilContext` :677, `buildContextExpr` :978;
- search engine: `tryAxiomMatch` :545, `tryLemmaMatchCore` :709, `tryLemmaMatch` :803,
  `tryAssumptionMatch` :818, `extractImplicationAntecedent` :850, `matchImplicationConsequent` :860,
  `extractContextFormulas` :874, `tryModusPonens` :894, `extractUnboxedContext` :951,
  `extractUnfuturedContext` :965, `tryModalK` :1001, `tryTemporalK` :1059, `searchProof` :1132.

The plumbing and search ranges **interleave** across :524-:1102, so a split must move declarations,
not cut at line numbers. The review's stated ranges (109-515 / 516-1000 / 545-1210) overlap and
cannot be used as-is.

Only three files import `Helpers.lean`: `Commands.lean`, `PropDecide.lean`, `Deduction.lean`.
Correcting the review: **`Deduction.lean` uses nothing from `Helpers.lean`** — not
`extractDerivationGoal`, not `isNilContext`, nothing. Its import is a candidate dead import.
`PropDecide.lean` uses exactly two (`extractDerivationGoal` :127, `isNilContext` :134,:148);
`Commands.lean` uses those two plus `searchProof`.

**(f) READMEs and the tactic reference are stale in three places, not two.** Both
`FormalSystem/Automation/README.md` (125 lines) and `FormalSystem/Automation/Tactics/README.md`
(38 lines) carry `<!-- BEGIN GENERATED: inventory -->` blocks, so their *tables* regenerate via
`bash scripts/check-module-invariants.sh --emit-inventory`. Their **prose** does not:
`Tactics/README.md:5-6` and `:26` still present `tm_auto` as a headline tactic. Item (5) also missed
`docs/reference/tactic-reference.md` (176 lines), which documents `temporal_search` (`:77`) and
`tm_auto` (`:89`) and is linked from `README.md:296` — it must be regenerated too.

**(g) Retiring to `Boneyard/` has a convention hazard.** `FormalSystem/Boneyard/README.md` states
the whole tree is **event-first** (pre-dating the guard-first `untl`/`snce` migration), is **not
compiled**, and carries a blanket resurrection warning; `BundleDeadHalf/` is the single documented
guard-first exception. Retired tactic files are guard-first live code. They need their own
documented exception subdirectory, or the banner becomes false. Boneyard is currently 164 files /
90,890 lines.

#### 7. Naming: three separate populations, only one mechanical

**Uppercase_x names.** Live scope (`FormalSystem/` + `Tests/`, Boneyard excluded, docstrings and
comments excluded): **107** declarations — 102 `theorem`, 5 `def`; 105 in `FormalSystem/`, 2 in
`Tests/`. The review's 98 is close but the composition matters far more than the count:

| Class | Approx. count | Dot-namespacing appropriate? |
|---|---|---|
| Tense-operator letter prefixes: `F_`, `P_`, `G_`, `H_`, `FF_`, `HF…` (e.g. `F_until_equiv_valid`, `G_iff_mcs`, `H_ex_falso_strengthen`, `P_top_mem_deferralClosure`) | ~55 | **No.** `F`/`P`/`G`/`H` are the paper's operators, not namespaces. `F.until_equiv_valid` would invent a namespace that does not exist |
| Genuine type/def prefixes with an existing declaration of that name: `R3Maximal_*` (`ChronicleTypes.lean:442`), `BurgessR3Maximal_*` (`:532`), `SubformulaClosure_*` (`SubformulaClosure.lean:65`), `BranchOrder_*` (`BranchOrder.lean:350`), `SetConsistent_of_subset` (`MaximalConsistent.lean:96`), `Fib_*` (`TaskFrame.lean:269`), `RefinedFilteredTaskFrame_*`, `FiniteFilteredTaskFrame_*` | ~30 | **Yes** — these are the real targets |
| Kamp-bridge construction prefixes: `CAggPtX_`, `CAggPtT_`, `CAggInt_`, `CAggOd_`, `CAggOdSwap_`, `CExtFut_`, `CExtPast_`, `A_diag_`, `A_past_`, `A_future_`, `MR_`, `O_zero_` | ~22 | **Case-by-case** — depends on whether the prefix names a `def` in that file |

The dispatch's two flagship examples do not exist in live scope:
`CanonicalTask_backward_comp` is only at `FormalSystem/Boneyard/BundleDeadHalf/CanonicalTaskRelation.lean:264`,
`Succ_implies_CanonicalR` only at `FormalSystem/Boneyard/BundleDeadHalf/SuccRelation.lean:96`.
Tasks 519/520 evidently already removed the live ones. `Fib_eq_singleton`
(`Semantics/TaskFrame.lean:1312`) *is* live and *is* a genuine candidate.

**`lemma` → `theorem`.** The review's 141/142 counts **include Boneyard**. Decomposition:

| Scope | `lemma` | `theorem` |
|---|---|---|
| Live (`FormalSystem/` + `Tests/`, Boneyard excluded) | **88** | 5,647 |
| `FormalSystem/Boneyard/` | 54 | 1,704 |
| Total | 142 | 7,351 |

So the acceptance criterion "lemma count 0" means **88 renames in live scope**, not 141. Top files:
`Syntax/SubformulaClosure/IteratedTemporal.lean` (21), `Metalogic/Core/MaximalConsistent.lean` (8),
`Metalogic/Bundle/WitnessSeed.lean` (8), `Metalogic/Bundle/TemporalContent.lean` (6),
`Decidability/Verified/Termination/MintBound.lean` (5), `Metalogic/Core/MCSProperties.lean` (4).

Two measured consequences the review did not record, both arguing the rename is more than cosmetic:
- **C17's dead-declaration census is blind to `lemma`.** Its declaration regex
  (`check-module-invariants.sh:2003`) is
  `(structure|inductive|def|abbrev|theorem|instance|class)` — no `lemma`. Same at `:1864`
  (the dupNamespace scanner). C15 (`:1547`) and C19 (`:2246`) *do* include it. So 88 live
  declarations are invisible to two checks today; renaming brings them into the census, and the
  plan should **expect new dead-declaration candidates to surface** as a result.
- **`lemma` is the worst-documented keyword in the tree.** C19's own comment
  (`:2222-2227`) records per-keyword docstring rates: `class` 16.3%, `instance` 57.6%,
  **`lemma` 55.6%**, against a 92.32% refined aggregate. Publishing doc-gen4 output exposes that.

**Nested-namespace shadowing.** A full reproducible scan (public, bare, non-dot-qualified
declarations; docstrings and comments excluded; Boneyard excluded) finds **17 outer-shadows-inner
pairs across 16 base names**, closely matching the dispatch's "~16":

| Base name | Outer | Inner |
|---|---|---|
| `completeness_dense` | `FormalSystem.Metalogic` — `StrongCompleteness.lean:989` | `…BXCanonical` — `BXCanonical/Completeness.lean:263` |
| `completeness_ztime` | `FormalSystem.Metalogic` — `StrongCompleteness.lean:1107` | `…BXCanonical` — `BXCanonical/Completeness.lean:306` |
| `F_until_equiv_valid` | `FormalSystem.Metalogic` — `Soundness.lean:385` | `…SoundnessLemmas` — `SoundnessLemmas/FrameClassVariants.lean:670` |
| `P_since_equiv_valid` | `…Metalogic` — `Soundness.lean:395` | `…SoundnessLemmas` — `FrameClassVariants.lean:683` |
| `temp_linearity_valid` | `…Metalogic` — `Soundness.lean:328` | `…SoundnessLemmas` — `FrameClassVariants.lean:599` |
| `temp_linearity_past_valid` | `…Metalogic` — `Soundness.lean:347` | `…SoundnessLemmas` — `FrameClassVariants.lean:634` |
| `temporal_truth_and` | `…WeakCanonical` — `StaviConnectives.lean:469` | `…WeakCanonical.Kamp` — `Kamp/Translation.lean:61` |
| `temporal_truth_neg` | `…WeakCanonical` — `StaviConnectives.lean:462` | `…WeakCanonical.Kamp` — `Kamp/Translation.lean:47` |
| `insertEnv` | `…WeakCanonical` — `MonadicFO.lean:360` | `…WeakCanonical.Kamp` — `Kamp/NfDepth0Generalized.lean:48` |
| `realOrder` | `…Metalogic` — `DedekindNonCompactness.lean:322` | `…Metalogic.Independence` — `Independence/RealTranslationFrame.lean:99` |
| `pastKDist` | `FormalSystem.Theorems` — `GeneralizedNecessitation.lean:114` | `…Theorems.Perpetuity` — `Perpetuity/Principles.lean:664` |
| `allAxiomNames` | `FormalSystem.Automation` — `AxiomNames.lean:33` | `…Automation.ProofStepExport` — `ProofStepExport.lean:1526` |
| `mem_knownTimes_of_mem` | `…Decidability` — `Verified/Termination/MintBound.lean:1344` | `…Decidability.Verified.Bridge` — `Bridge/BoxSaturation.lean:261` |
| `mem_knownWorlds_of_mem` | `…Decidability` — `MintBound.lean:2469` | `…Verified.Bridge` — `Bridge/BoxSaturation.lean:255` |
| `isValid` ×2 | `…Decidability` — `DecisionProcedure.lean:323` | `…Decidability.DecisionResult` — `DecisionProcedure.lean:97`; `…Decidability.ExpandedTableau` — `Saturation.lean:82` |
| `DiversityReport` | `FormalSystem.Automation` — `FormulaEnumerator.lean:1003` | `…Automation.DatasetValidator` — `DatasetValidator.lean:260` |

Corrections to the dispatch, all evidence-backed:
- **`completeness_discrete` does not exist.** The name is `completeness_ztime`. The dispatch's
  anchors `StrongCompleteness.lean:1101` / `BXCanonical/Completeness.lean:296` are also off by a
  few lines. Likewise `:987`/`:255` for `completeness_dense` → `:989`/`:263`.
- **`hasBox`, `isNeg`, `isTop` are not genuine cases.** Every colliding side is `private`
  (`FormulaEnumerator.lean:2017,597,592`; `InterestingnessMetrics.lean:117,112`), so name mangling
  prevents any shadowing. Drop them from item (7)(b).
- **Two cases the dispatch missed**: `DiversityReport`, and `isValid` — the latter notable because
  task 178's own realignment note warns readers against confusing
  `DecisionProcedure.isValid` with a semantic-side `IsValid`; this shadowing is that confusion made
  mechanical.
- **`allAxiomNames` is a documented, deliberate duplication, not an accident.**
  `ProofStepExport.lean:1522-1524` explains: the module is a `lean_exe` root that deliberately does
  not import `AxiomNames.lean`. Both lists currently hold exactly the same 45 names in the same
  order (verified by diff). The right response is a machine check that the two agree, not a rename.

**The "SEPARATE AND MORE SERIOUS FINDING" is not a defect.** The dispatch claims
`mem_knownTimes_of_mem` appears twice under the same fully-qualified namespace. It does not:
`CountermodelExtraction.lean:415` is `private theorem`, so its real name is mangled.
A repo-wide scan for *any* two live declarations sharing an identical fully-qualified name (with
`private` correctly excluded, and with an identifier regex that handles `?`/`τ`/unicode suffixes)
returns **exactly one family**: twelve `def main` entry points, one per `lean_exe` root
(`BenchmarkAnchors.lean:480`, `BenchmarkOracle.lean:265`, `DatasetExport.lean:958`,
`DatasetValidator.lean:596`, `EnumBenchmark.lean:202`, `FormulaMutator.lean:1143`,
`MachineAppendixExport.lean:497`, `ProofFirstExporter.lean:138`, `ProofStepExport.lean:1658`,
`TableauBridge.lean:647`, `TableauProofStepPipeline.lean:694`, `TraceExporter.lean:263`). None is
imported by `FormalSystem/Automation.lean` (which imports `DatasetExporter`, a different module), so
no two are ever in one import closure. **Benign.** Item (7)'s "check this first" framing should be
retired: the class does not exist.

**The `completeness_dense`/`completeness_ztime` shadowing already has a recorded decision against
renaming.** `StrongCompleteness.lean:126-133` carries a section headed "A note on the
`completeness_dense` / `completeness_ztime` short names" concluding: *"This is harmless — the
shadowing and shadowed forms have identical types, so re-pointing any call site from one to the
other would be semantically inert — and every out-of-file occurrence of either short name in this
tree is docstring prose rather than a call site."* Restated at `:983-985` and `:1101-1103`.
The dispatch's rename recommendation runs against this. The reconciliation is that the note
evaluates only *semantic* harm, and there is a second, **tooling** harm it does not consider: see
the C17 point below. Renaming the inner declarations is still justified — on tooling grounds, not
on the grounds the note already rejected — and the plan should say so explicitly rather than
silently contradicting a documented decision.

#### 8. The guard, and the machinery it should reuse

C17's own header comment (`check-module-invariants.sh:1974-1976`) confirms the dispatch's premise
verbatim: the census keys on "the BASE identifier (the last dot-segment of its name)", and is
"blind […] to same-named declarations in different namespaces (a shared base name like `mk` or
`toString` will never register as dead, which is the safe direction of error for a census that must
never gate)". So each of the 17 shadowing pairs permanently masks both its members from the
dead-declaration report. That is the tooling harm the `StrongCompleteness.lean` note does not weigh.

**C16 already contains the exact machinery the new guard needs.** Its `dupNamespace` textual scanner
(`:1846-1870`) already walks `namespace`/`end` stacks and matches declarations per file, and
currently reports 0 findings. The new invariant should extend that scanner rather than add a third
copy of the walk, and must:
1. add `lemma` to its declaration regex (currently missing, as noted above);
2. use an identifier character class that survives `?`, `'`, `τ` and other unicode suffixes —
   a naive `[A-Za-z0-9_'.]*` truncates `asAnd?` to `asAnd` and manufactures ~30 false positives;
3. exclude `private` declarations (name-mangled, cannot collide or shadow);
4. skip declarations inside `/- … -/` and `/-! … -/` blocks (docstring code fences otherwise
   register as declarations);
5. **not** flag structure-member namesakes — `Syntax.Atom.beq_refl` vs `Syntax.Formula.beq_refl`,
   and the `toJson`/`display`/`empty`/`size`/`insert`/`mono`/`lift` families — which the
   outer-shadows-inner test in the scan above already excludes by construction, since neither
   namespace is a prefix of the other.

`docs/theorem-index.md` (191 lines, 52 rows) already uses fully-qualified names throughout, exactly
because `completeness_dense` alone does not identify a row — the dispatch's supporting claim, confirmed.

#### 9. NOTATION.md and ORGANISATION.md: partly pre-empted, and G-16 is half-adopted

`ORGANISATION.md` and `NOTATION.md` do not exist at the root, but two documents already hold most of
their content:
- `docs/ARCHITECTURE.md` (126 lines; sections "The layer diagram", "Layer 0 in full",
  "The three completeness routes", "The archive", "Verifying this page") — this **is** G-09's
  ORGANISATION.md content, written by task 530.
- `docs/development/MODULE_ORGANIZATION.md` (416 lines) — the full directory/namespace specification.
- `docs/theorem-index.md:26-46` — a "Notation and naming" table mapping paper terms to Lean
  identifiers.

The layering claim checks out: `FormalSystem/Semantics/FrameClassValidity.lean:8` is the **single**
`import FormalSystem.ProofSystem.*` anywhere under `Semantics/` — the one documented
`Semantics → ProofSystem` edge, confirmed by grep.

**G-16's premise is imprecise and its recommendation is half-implemented.** The repo carries **15**
`notation` declarations in live scope, not four ⊨-shaped relations:
- **12 derivability notations, all already carrying a per-language/per-frame-class tag** — exactly
  the CSLib `TM[...]` idiom: `Γ ⊢[fc] φ` / `⊢[fc] φ` (`ProofSystem/Derivation.lean:346,351`),
  `Γ ⊢ φ` / `⊢ φ` (`:356,361`, Base-class abbreviations), `G |-![fc] p` and three siblings
  (`ProofSystem/Derivable.lean:77,82,87,92`), `Γ ⊢ᴮᴸ[fc] φ` / `⊢ᴮᴸ[fc] φ`
  (`BaseLanguage/Derivation.lean:162,165`), `Γ ⊢⋆[fc] φ` / `⊢⋆[fc] φ`
  (`StarLanguage/Derivation.lean:165,168`).
- **2 validity notations, both untagged**: `Γ ⊨ φ` (`Semantics/Validity.lean:122`) and `⊨ φ` (`:414`).
- 1 scoped quotient bracket (`Algebraic/LindenbaumQuotient.lean:130`).

And the asymmetry is **already a recorded decision**: `Semantics/Validity.lean:239-242` states that
"a `TruthAt` notation was dropped because it conflicts with the `⊨` validity notation in this file;
a subscripted variant […] used instead, and dot-notation (`F.ValidOn φ`) reads as the paper's
`⊨_F φ` does." Meanwhile the semantic side carries **seven** validity predicates
(`ValidOnFrames` :359, `ValidIn` :370, `Valid` :408, `ValidDense` :593, `ValidZTime` :638,
`ValidComplete` :696, `ValidRTime` :729) plus `SemanticConsequence`/`SemanticConsequenceIn`/
`ConsequenceOnFrames`, and `Semantics/StarValidity.lean` mirrors the whole family for `StarFormula`.

So NOTATION.md's real job is to **document the tag convention that already exists on the ⊢ side, the
seven-predicate ⊨ family that deliberately has no tags, and the recorded reason** — not to introduce
a new `TM[...]` notation over an explicit prior decision not to.

### External Resources

- `leanprover-community/docgen-action` `action.yml` — full input table reproduced above (VERIFIED
  by direct fetch). Permissions `contents: read` / `pages: write` / `id-token: write`; the action
  deploys to Pages itself (`deploy: true` by default), so no separate `actions/deploy-pages` job.
- `docgen-action` README (VERIFIED) — instructs `jekyll new docs`; API docs land at `docs/docs/`;
  notes Lean toolchains ≥ v4.28.0 carry a needed fix (this repo is v4.33.0-rc1); does not require
  the repository to declare doc-gen4 itself.
- `teorth/pfr` and `leanprover/cslib` layouts are cited in `G-ecosystem.md` §8 and G-09 as
  already-fetched-and-VERIFIED by the original review; not re-fetched here.
- Lean/Mathlib pins re-derived from the tree: `lean-toolchain` = `leanprover/lean4:v4.33.0-rc1`;
  `lakefile.lean` requires mathlib4 at tag `v4.33.0-rc1`.

### Recommendations

All of the following reach the acceptance criteria with **zero `sorry`, zero new axioms, and no
deferral**. Nothing here requires a proof to be left incomplete; the only Lean file added
(`MainResults.lean`) contains restatements of already-proved theorems plus `#print axioms`
commands, so it cannot introduce debt.

1. **Publish via `docgen-action`, not via a lakefile dependency.** Add
   `.github/workflows/docs.yml` with `permissions: {contents: read, id-token: write, pages: write}`
   and a single `uses: leanprover-community/docgen-action@main` step with
   `api-docs: true`, `blueprint: false`, `references: references.bib`, and **`build-page: false`**
   (resolving the `homepage: docs` collision). Set Pages source to GitHub Actions manually. Then
   rewrite `docs/README.md:272-278` and add the site link to `README.md` above `## Documentation`.
   Re-run C12/C13 afterwards.

2. **Finish `references.bib` before publishing.** Add the ~9 missing entries — `rabinovich2014`
   (71 citations, the most-cited work in the tree), `doets1989`, `goldblatt1992`, `burgess1984`,
   `reynolds1996`, `reynolds2003`, `verbrugge2007`, `venema2001`, `fisherLadner1979` — then convert
   `## References` prose to `[Key]` citations. Sequence this **before** item 1's first deploy so
   the published references page is complete on first sight.

3. **Write `FormalSystem/MainResults.lean` as a navigation page, and guard it by subset, not by a
   new baseline.** Restate the headline results (soundness ×4, weak completeness ×4, consequence
   completeness ×4, `strongCompletenessBase`/`Dense`, `compactBase`/`Dense`, both non-compactness
   refutations, the Galois closure family, `kampPriorExpressiveCompleteness`, `sound_of_isValid`),
   each followed by `#print axioms` with output recorded in the `DiscreteNonCompactness.lean:292-312`
   style. Add one check to `check-module-invariants.sh` asserting **every declaration named in
   `MainResults.lean` appears in the C2 or C14 baseline**. Hand the file to task 178 as the artefact
   its examples cite.

4. **Write `NOTATION.md`; make `ORGANISATION.md` a pointer, not a duplicate.** `docs/ARCHITECTURE.md`
   already covers the layering and the single `Semantics → ProofSystem` edge; a root
   `ORGANISATION.md` should be a short root-level entry point that links it and
   `docs/development/MODULE_ORGANIZATION.md`, not a third copy (C18 gates paragraph duplication
   across top-level READMEs). `NOTATION.md` should inventory the 15 notation declarations, document
   the frame-class tag convention already carried by all 12 derivability notations, and record the
   `Validity.lean:239-242` decision explaining why the ⊨ side is untagged. **Do not introduce a new
   `TM[...]` ⊨ notation** — it contradicts a documented prior decision and G-16's "four ⊨-shaped
   relations" premise is wrong.

5. **Automation triage, in evidence order.** (a) Retire to `Boneyard/` in one batch:
   `tm_auto`, `temporal_search`, `propositional_search`, `modal_4_tactic`, `modal_b_tactic`,
   `modal_k_tactic`, `temporal_k_tactic`, all seven `Normalization.lean` tactics, and
   `AesopRules.lean` + `AesopRuleSet.lean` (zero consumers). Create a guard-first exception
   subdirectory with its own README, as `BundleDeadHalf/` does, so `Boneyard/README.md`'s
   event-first banner stays true. (b) Strip `SearchConfig` to `depth` + `visitLimit`, deleting the
   five unread weight fields, the two presets, their `applyParams` cases, and the three false
   docstring claims at `Commands.lean:182-183` and `:255`. (c) Keep `modal_search` and say in the
   README that it is the pedagogical entry point, not library infrastructure — three call sites,
   all in `Examples/`. (d) Time-box the `deduction`/`undischarge` trial and expect it to fail:
   the `noncomputable` infection documented at `Deduction.lean:32-38` is the reason it was never
   adopted. (e) Split `Helpers.lean` by moving declarations (the ranges interleave), and drop
   `Deduction.lean`'s unused `import … Helpers`. (f) Regenerate the two README inventory blocks
   with `--emit-inventory`, fix their prose, and regenerate `docs/reference/tactic-reference.md`.

6. **Adjudicate the Uppercase_x renames rather than applying a rule.** Rename only the ~30
   type-prefix names whose prefix is a real declaration (`R3Maximal_*`, `BurgessR3Maximal_*`,
   `SubformulaClosure_*`, `BranchOrder_*`, `SetConsistent_of_subset`, `Fib_*`,
   `RefinedFilteredTaskFrame_*`, `FiniteFilteredTaskFrame_*`). **Leave the ~55 tense-operator
   names alone** — `F`/`P`/`G`/`H` are operators, not namespaces. Adjudicate the ~22 Kamp-bridge
   names case-by-case. Convert all **88** live `lemma` declarations to `theorem`, and expect new
   C17 dead-declaration candidates to appear because C17's regex currently cannot see them.

7. **Correct item (7) before planning it.** There is no fully-qualified-name duplication to fix.
   Rename the inner members of the shadowing pairs to Mathlib's `conclusion_of_hypothesis` form
   (`BXCanonical.derivable_of_validDense`, `…derivable_of_validZTime`, and analogues for the four
   `SoundnessLemmas` and two `Kamp` pairs), keeping the outer four-member
   `completeness_base/_dense/_ztime/_rtime` family intact. Justify it on the **C17 masking** ground,
   explicitly acknowledging that `StrongCompleteness.lean:126-133` already dismissed the *semantic*
   ground. Handle `insertEnv`, `pastKDist`, `realOrder`, `DiversityReport`, `isValid`,
   `mem_knownTimes_of_mem` and `mem_knownWorlds_of_mem` individually; replace `allAxiomNames` with a
   consistency check rather than a rename; drop `hasBox`/`isNeg`/`isTop` (all `private`). Extend
   C16's existing `dupNamespace` scanner with the five corrections listed in Finding 8.

---

## Decisions

- **doc-gen4 is delivered by `docgen-action`, not by `require «doc-gen4»` in `lakefile.lean`.**
  The action supplies it, so `lake build` and `lake-manifest.json` stay unchanged. This diverges
  from E-08's literal recommendation, on the evidence of the action's own `action.yml`/README.
- **`build-page: false`** is the default recommendation, because the action's `homepage` default
  (`docs`) collides with this repo's non-Jekyll `docs/` tree.
- **`MainResults.lean` does not get its own axiom baseline.** C2+C14 already pin all 105 relevant
  declarations; a subset assertion is the correct guard.
- **`ORGANISATION.md` is a pointer, not new prose**, because `docs/ARCHITECTURE.md` and
  `docs/development/MODULE_ORGANIZATION.md` already carry the content and C18 gates duplication.
- **No new `TM[...]` ⊨ notation.** `Validity.lean:239-242` records a deliberate decision against a
  subscripted validity notation; the ⊢ side already has the tag convention G-16 asks for.
- **The claimed fully-qualified-name duplication is closed as "not a defect"**, on the evidence that
  `CountermodelExtraction.lean:415` is `private` and a corrected repo-wide scan finds only the
  twelve never-co-imported `main` entry points.
- **The tense-operator Uppercase_x names are out of scope for renaming**, so "98 renamed" cannot be
  an acceptance criterion; "the ~30 type-prefix names renamed" can.
- Research did **not** run `lake build`. Every claim above is textual/structural and re-derivable
  with `grep`/`python3`; the build-dependent checks (C2, C14, C16) were read, not executed.

---

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| Publishing doc-gen4 output exposes the three false `Commands.lean` docstrings and the whole retired suite to a referee | **Sequence item (5) before item (1)'s first deploy**, or at minimum fix the three docstrings first |
| `build-page: true` (the default) Jekyll-builds the existing 100-file `docs/` tree | Set `build-page: false` explicitly; do not rely on the default |
| Rewriting `docs/README.md:272-278` breaks C12/C13 link resolution | Run `bash scripts/check-module-invariants.sh --no-build` after the edit; both checks are structural and run without a build |
| Retiring guard-first tactic files into an event-first Boneyard falsifies `Boneyard/README.md`'s blanket banner | Create a documented guard-first subdirectory, following `BundleDeadHalf/`'s precedent |
| Renaming `BXCanonical.completeness_dense`/`_ztime` contradicts a documented decision at `StrongCompleteness.lean:126-133` | State the C17-masking justification explicitly in the plan and update that note in the same commit, so the tree does not carry two opposed decisions |
| `lemma` → `theorem` surfaces new C17 dead-declaration candidates and moves the C19 aggregate | Both checks are reporting-only (no `ENFORCE_C17`/`ENFORCE_C19`), so neither can fail the build; record the before/after numbers |
| A mechanical Uppercase_x rename over the ~55 tense-operator names would damage the naming that mirrors the paper | Adjudicate by class, per Recommendation 6; do not write a blanket rename script |
| The `deduction` tactic trial consumes effort and yields nothing | Time-box it; the `noncomputable` blocker is documented in-source and is a legitimate "no" |
| Missing `references.bib` keys cause doc-gen4 citation misses | Add the ~9 entries first; `rabinovich2014` alone accounts for 71 of 190 prose citations |
| `check-module-invariants.sh` gains a fourth namespace-walking scanner | Extend C16's existing `dupNamespace` walker instead of adding a copy |

---

## Tactic Survey Results

Tactics were surveyed as *artefacts under triage* (their declaration and usage census is in
Finding 6) rather than as candidate proof automation for an open goal. No proof goal in this task
required closing, so the `lean_multi_attempt` / `lean_hammer_premise` portfolio pass was not
applicable.

| Goal | Tactic | Result | Premises/Config |
|------|--------|--------|-----------------|
| — (no open proof goal in scope) | — | Not applicable | Survey was of the repo's *own* declared tactics; see Finding 6 |

The one substantive tactic-behaviour result is recorded in Finding 6(b): `modal_search`,
`temporal_search`, `propositional_search` and `tm_auto` are **behaviourally identical**, because the
`SearchConfig` fields that would distinguish them are never read (`Commands.lean:157`, in source:
"weights remain unused").

---

## Context Extension Recommendations

- **Topic**: doc-gen4 / `docgen-action` integration for a repo with a pre-existing non-Jekyll `docs/`
  **Gap**: no context file covers the `homepage` default collision, `build-page: false`, or the fact
  that the action supplies doc-gen4 so no lakefile `require` is needed. This cost real research time
  and is a recurring Lean-publication question.
  **Recommendation**: create `context/project/lean4/operations/docgen-publication.md`.

- **Topic**: measuring live scope in this repository
  **Gap**: several review findings (141 `lemma`, 7,031 `theorem`, 98 Uppercase_x) silently include
  `FormalSystem/Boneyard/` (164 files, 90,890 lines, not compiled), while every invariant check
  excludes it. Any count quoted without a stated scope is ambiguous by a factor of ~1.6 for
  `lemma`.
  **Recommendation**: add a "Live scope vs. Boneyard" subsection to
  `context/project/lean4/` naming/measurement guidance, pointing at
  `scripts/lib/live_walk.py` as the canonical walker.

- **Topic**: `private` and Lean 4 name mangling
  **Gap**: the dispatch escalated a `private`-resolved namesake to "a different and stronger
  problem than shadowing". A short note that `private` declarations are name-mangled and therefore
  cannot collide would have prevented that.
  **Recommendation**: add to `context/project/lean4/domain/` naming notes.

---

## Appendix

### Commands used (all re-runnable from the repository root)

```bash
# packaging state
cat lakefile.lean lean-toolchain; grep -i doc-gen lake-manifest.json
ls CITATION.cff references.bib FormalSystem/Init.lean .github/workflows/

# axiom-set pins
awk "/read -r -d '' C14_BASELINE/,/^C14BASE$/" scripts/check-module-invariants.sh \
  | grep -c 'depends on axioms'          # -> 101
awk "/read -r -d '' AXIOM_BASELINE/,/^BASELINE$/" scripts/check-module-invariants.sh \
  | grep -c 'depends on axioms'          # -> 4   (101 + 4 = 105)

# prose citation census
grep -rhn -A12 '## References' --include=*.lean FormalSystem/ | grep -v Boneyard \
  | grep -oE '\b[A-Z][a-zA-Z-]+(–[A-Z][a-zA-Z]+)? [0-9]{4}[a-z/0-9]*' | sort | uniq -c | sort -rn

# lemma / theorem, live vs Boneyard
grep -rnE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private |protected |noncomputable |scoped |local )*lemma " \
  --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard | wc -l     # -> 88

# SearchConfig weights are write-only
grep -rn 'axiomWeight\|mpWeight\|modalKWeight' --include=*.lean FormalSystem/ | grep -v Boneyard
sed -n '149,165p' FormalSystem/Automation/Tactics/Commands.lean          # ":157  weights remain unused"

# TMLogic rule set consumers
grep -rn 'TMLogic' --include=*.lean FormalSystem/ Tests/ | grep -v Boneyard | grep -v '@\[aesop'
```

The Uppercase_x census, the duplicate-fully-qualified-name scan and the outer-shadows-inner scan
were run as short `python3` scripts that (i) exclude `Boneyard`, (ii) track `namespace`/`end`
stacks, (iii) skip `/- … -/` blocks and `--` lines, (iv) exclude `private`, and (v) use an
identifier class tolerant of `?`, `'` and unicode suffixes. Omitting (iii)-(v) manufactures ~30
false positives (`asAnd?` truncating to `asAnd`; prose words `and`/`the`/`with`/`of` matching the
declaration regex inside docstrings) — the likely origin of some claims in the dispatch text.

### Documentation read

`docs/README.md`, `docs/ARCHITECTURE.md`, `docs/theorem-index.md`,
`docs/development/MODULE_ORGANIZATION.md`, `docs/development/DIRECTORY_README_STANDARD.md`,
`docs/reference/tactic-reference.md`, `FormalSystem/Boneyard/README.md`,
`FormalSystem/Automation/README.md`, `FormalSystem/Automation/Tactics/README.md`,
`scripts/check-module-invariants.sh` (C2, C6, C14, C16, C17, C19 sections),
`specs/530_*/summaries/01_documentation-single-source-of-truth-summary.md`.

## Tags

doc-gen4 · github-pages · references-bib · main-results · automation-triage · naming · shadowing
