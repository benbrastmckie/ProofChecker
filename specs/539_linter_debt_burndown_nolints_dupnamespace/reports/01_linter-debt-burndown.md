# Research Report: Linter Debt Burndown (nolints.json, dupNamespace)

- **Task**: 539 - Draw down the linter debt recorded rather than fixed by the CI/linter-gates work
- **Started**: 2026-09-07T00:00:00Z
- **Completed**: 2026-09-07T00:00:00Z
- **Effort**: ~2 hours research; implementation estimated 1-2 days (see phase sizing)
- **Dependencies**: None
- **Sources/Inputs**:
  - Codebase: `scripts/nolints.json`, `scripts/check-module-invariants.sh`, `.github/workflows/ci.yml`, `lakefile.lean`
  - Lean sources: `FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`, `FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean`, `FormalSystem/Automation/Tactics/Commands.lean`, `FormalSystem/Automation/Tactics/Helpers.lean`, `FormalSystem/Automation/ProofSearch/Core.lean`
  - Toolchain sources: `.lake/packages/batteries/scripts/runLinter.lean`, `.lake/packages/mathlib/Mathlib/Tactic/Linter/Lint.lean`, `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean`, `.lake/packages/mathlib/Mathlib/Tactic/Linter/TacticDocumentation.lean`
  - Project policy doc: `docs/development/NAMING_CONVENTION_DEVIATION.md`
  - Live measurement: `lake lint`, `lake exe runLinter FormalSystem`, `lake env lean <file>`, the C16 textual scanner extracted from `check-module-invariants.sh`
  - lean-lsp MCP (`lean_run_code`) for namespace-resolution experiments
- **Artifacts**:
  - `specs/539_linter_debt_burndown_nolints_dupnamespace/reports/01_linter-debt-burndown.md`
- **Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Both concrete fixes were prototyped end-to-end and verified during research, then reverted.**
  The simpNF fix (delete the redundant `length_range_map`, rewrite its 5 use sites) and the
  dupNamespace fix (move `structure Chronicle` up into `FormalSystem.Metalogic.BXCanonical`)
  each elaborate with **zero errors and zero warnings**, and the dupNamespace count drops from
  14 to 0 under both the real Mathlib linter and C16's textual scanner.
- **A cheap real-linter verification route exists that the C16 comment block does not know
  about.** `lake env lean <file>` re-elaborates one file against existing oleans in **~2
  seconds** and emits genuine `dupNamespace` warnings (`linter.dupNamespace` defaults to `true`).
  The ~10-minute full-rebuild cost documented at `scripts/check-module-invariants.sh:1416-1421`
  applies only to `lake lint --builtin-only --lint-only .dupNamespace`, not to this route.
- **The recommended dupNamespace fix is reference-transparent.** Moving the structure one
  namespace up (rather than renaming it) leaves every `Chronicle`, `Chronicle.cN`, `χ.f/g/dom`,
  `⟨…⟩`, and `extends Chronicle` reference resolving to the same thing. Only 10 lines of
  ChronicleTypes.lean change (1 structure relocation + 9 `def Chronicle.cN` -> `def cN`).
  Burgess's vocabulary is preserved, which a rename would sacrifice.
- **The nolints policy has hard evidence behind it: 207 of 217 `unusedArguments` findings
  (95.4%) have *only* instance-implicit arguments unused** — 130 `[DecidableEq sig.preds]`, 122
  `[Fintype sig.preds]`, 41 `[Nontrivial D]`. That category should be permanently grandfathered
  with a written rationale, not burned down.
- **`docs/development/NAMING_CONVENTION_DEVIATION.md` is materially stale and is the right home
  for the recorded policy.** It declares `defsWithUnderscore` **CLOSED at 0**; the live count is
  **33**. It also tabulates `unusedArguments = 124` (live: 217) and `docBlame = 39` (live: 51),
  and states "CI runs `lean-action` with `lint: false`" (CI now sets `lint: true`).
- **`defsWithUnderscore` (33) is a genuine regression against the project's own settled rule**
  and is cheap to burn down: ~141 token occurrences total across 33 declarations, most with 1-2
  call sites, the largest 16.
- **Recommended burn-down**: simpNF 1->0, dupNamespace 14->0, defsWithUnderscore 33->0,
  tacticDocs 4->0, docBlame 51->0 (48 by docstring, 3 by in-source `@[nolint]`),
  structureInType 1 kept as an in-source documented exemption. `nolints.json` shrinks
  **307 -> 217**, carrying only `unusedArguments`.

## Context & Scope

Three deliverables from the task description:

1. Fix the single `simpNF` finding.
2. Fix the 14 `dupNamespace` findings in `ChronicleTypes.lean`.
3. Decide and record a policy for the remaining `nolints.json` entries.

All measurements below were taken on a green, fully cached tree (`lake build` exit 0, 2591
jobs). Every experiment that modified a source file was reverted; `git status --porcelain` shows
no Lean or script file modified by this research.

**Constraint honoured throughout**: no approach recommended here introduces a `sorry` or a new
axiom. Every proposed change is a naming/documentation/deletion change with a compile-verified
or mechanically-checkable outcome.

## Findings

### Measured baseline (live, not quoted)

`lake exe runLinter FormalSystem` with `scripts/nolints.json` temporarily replaced by `[]`
reports:

```
-- Found 307 errors in 11005 declarations (plus 18696 automatically generated ones)
   in FormalSystem with 14 linters
```

matching `nolints.json` exactly, category by category:

| Linter | Count | Provider |
|---|---|---|
| `unusedArguments` | 217 | Batteries `@[env_linter]` |
| `docBlame` | 51 | Batteries `@[env_linter]` |
| `defsWithUnderscore` | 33 | Mathlib `Mathlib/Tactic/Linter/Style.lean:553` |
| `tacticDocs` | 4 | Mathlib `Mathlib/Tactic/Linter/TacticDocumentation.lean:31` |
| `simpNF` | 1 | Batteries `@[env_linter]` |
| `structureInType` | 1 | Batteries `@[env_linter]` |

With the real `nolints.json` in place, `lake lint` exits 0 in **8 seconds** (post-build). The
verification loop is therefore cheap; build invalidation, not linting, is the cost driver.

`dupNamespace` is separate: 14 findings, all in `ChronicleTypes.lean`, confirmed by both the C16
textual scanner and the real linter (see next finding).

### `lake env lean <file>` runs the real dupNamespace linter in ~2 seconds

`linter.dupNamespace` is a *syntax* linter registered via `addLinter`
(`Mathlib/Tactic/Linter/Lint.lean:79-114`) with `defValue := true`. It therefore fires during
ordinary elaboration of any file that transitively imports Mathlib's linter module — which
`ChronicleTypes.lean` does.

Measured: `lake env lean FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean`
finishes in 2.0-2.2 s and prints exactly 14 warnings:

```
ChronicleTypes.lean:548:10: warning: The namespace `Chronicle` is duplicated in the
  declaration `FormalSystem.Metalogic.BXCanonical.Chronicle.Chronicle`.
```

…plus `.mk`, `.f`, `.g`, `.dom`, and `.c0` `.c1` `.c2` `.c2'` `.c3` `.c4` `.c4'` `.c5` `.c5'`
(1 + 1 + 3 + 9 = 14). This is bit-for-bit the same set the C16 textual approximation reports,
independently confirming the scanner's fidelity claim.

This does **not** contradict the comment at `scripts/check-module-invariants.sh:1416-1421`: that
comment is about `lake lint --builtin-only --lint-only .dupNamespace`, which forces Lake to
rebuild the whole default target under changed linter options. `lake env lean` reuses the
existing oleans of the file's imports and writes none, so it neither costs a rebuild nor
perturbs the build cache.

### Deliverable 1 — simpNF: `length_range_map` [prototyped, verified, reverted]

`FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean:97-99`:

```lean
@[simp]
theorem length_range_map {α : Type*} (n : ℕ) (g : ℕ → α) :
    ((List.range n).map g).length = n := by simp
```

The proof body is literally `by simp` — `List.length_map` and `List.length_range` are both simp
lemmas, so the statement is a redundant duplicate and simpNF's "simp can prove this" is correct.

Five use sites, all inside this one file (verified by repo-wide grep; no other module, and no
Boneyard file, references it):

| Line | Current | Replacement |
|---|---|---|
| 229 | `simp only [Periodic.cyc, length_range_map]` | `simp only [Periodic.cyc, List.length_map, List.length_range]` |
| 267 | same | same |
| 420 | `rw [hbD, length_range_map]` | `rw [hbD]; simp` |
| 421 | `rw [hmD, length_range_map]` | `rw [hmD]; simp` |
| 422 | `rw [hfD, length_range_map]` | `rw [hfD]; simp` |

**Verified**: with the theorem deleted and those five sites rewritten,
`lake env lean FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean` exits 0 with **zero
diagnostic output** (baseline for the unmodified file is also zero). File restored afterwards.

Deleting the lemma is preferred over merely dropping `@[simp]`: dropping the attribute silences
simpNF but leaves a lemma that duplicates two Mathlib simp lemmas, and would still need
justification in review.

### Deliverable 2 — dupNamespace: relocate `structure Chronicle` [prototyped, verified, reverted]

**Current shape** (`ChronicleTypes.lean:65`, `:548`, `:871`): `namespace
FormalSystem.Metalogic.BXCanonical.Chronicle` opens at 65 and closes at 871; `structure
Chronicle` is declared at 548 inside it, so the structure, its `.mk`, its three projections, and
the nine `def Chronicle.cN` at 559-652 all land at `…BXCanonical.Chronicle.Chronicle.*`.

Three options were considered. **Option C is recommended.**

| Option | Change | Sites touched | Preserves "Chronicle" name | Verdict |
|---|---|---|---|---|
| A. rename the structure (`Chronicle` -> `Chron`) | structure + ~50 type-annotation sites | ~50, in 3 files | no | rejected: sacrifices Burgess's term |
| B. rename the namespace segment | ~20 `namespace`/`end`/`open` lines, but changes the fully-qualified name of every declaration in 13 files | large blast radius | yes | rejected: gratuitous churn |
| **C. move the structure up into `FormalSystem.Metalogic.BXCanonical`** | 1 relocation + 9 `def Chronicle.cN` -> `def cN` | **10 lines, 1 file** | yes | **recommended** |

Option C makes `…BXCanonical.Chronicle` the *structure's own* namespace — the standard
Lean/Mathlib idiom — so the existing `namespace …BXCanonical.Chronicle` blocks in 13 files
become that structure's namespace rather than a sibling of it.

**Why it is reference-transparent** (each case confirmed with `lean_run_code` on a minimal
model, then on the real file):

- `Chronicle` used bare inside `namespace …BXCanonical.Chronicle`: before, resolves to
  `…Chronicle.Chronicle`; after, name resolution walks up one level and finds
  `…BXCanonical.Chronicle`. Same referent, no edit.
- `χ.c0` / `χ.f` / `χ.g` / `χ.dom` dot notation: resolves against the structure's own namespace
  in both shapes. No edit at any of the ~50 sites.
- Explicit `Chronicle.c0` from inside the namespace: after the move, `Chronicle` names the
  structure and `Chronicle.c0` is `…BXCanonical.Chronicle.c0`. Resolves. No edit.
- Anonymous constructor `⟨f, g, dom⟩`, structure-instance `{ f := …, g := …, dom := … }`, and
  `structure ValidChronicle extends Chronicle` with its `toChronicle` projection: all verified
  working under Option C.
- `Chronicle.nextTop`, `Chronicle.liftBase`, `Chronicle.mcs_to_base`, `Chronicle.cantorBfmcsDense`
  and the ~80 similar references in `Completeness.lean`, `CompletenessDedekind.lean`,
  `CanonicalModel.lean` are namespace-qualified references from the sibling namespace
  `FormalSystem.Metalogic.BXCanonical`. After the move they resolve through the structure's
  namespace instead of a plain namespace — same fully-qualified target, no edit.

**Collision audit**: no declaration anywhere in the 540 declarations of the
`…BXCanonical.Chronicle` namespace is named `f`, `g`, `dom`, `mk`, `c0`…`c5'`, or
`toChronicle`, so nothing shadows or is shadowed by the structure's generated names.

**Blast-radius audit**: zero bare `Chronicle` *type* uses exist outside
`FormalSystem/Metalogic/BXCanonical/Chronicle/` (the nine matches outside that directory are all
prose in comments/docstrings). `FormalSystem/Boneyard/DenseChronicle/DenseCounterexampleElimination.lean`
does use `Chronicle` as a type, but Boneyard is not part of the build (zero Boneyard oleans in
`.lake/build`). No markdown, typst, script, or manifest file references `Chronicle.c0`,
`Chronicle.mk`, or `structure Chronicle`. `nolints.json` contains exactly one entry in this
namespace (`…Chronicle.chronicleMonadic_expressiveCompleteness`), which the move does not touch.

**Verified**: with Option C applied,
`lake env lean FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` exits 0 in 2.0 s
with **zero errors and zero dupNamespace warnings** (from 14), and the C16 textual scanner
reports `PASS C16 dupNamespace: zero declaration(s)`. File restored afterwards.

**One residual risk, currently unrealized**: a file that only does `open
FormalSystem.Metalogic.BXCanonical.Chronicle` (not `namespace`) and uses bare `Chronicle` as a
type would break, because `open X.Chronicle` brings the *contents* of that namespace into scope,
not the namespace-name itself. With `autoImplicit := false` (set in `lakefile.lean`) this is a
hard "unknown identifier" error, not a silent auto-bound implicit. Three files use that `open`
form (`WeakCanonical/ChronicleExtraction.lean:42`, `IntegerModel/ReynoldsBridge.lean:62`,
`GroupModel/GroupableCompanion.lean:68`, plus `GroupModel/CountermodelBase.lean:69`); none
currently uses `Chronicle` as a type. The full-tree `lake build` is the gate that would catch a
regression here.

### Deliverable 3 — the nolints categories, one by one

#### `unusedArguments` (217) — permanently grandfather

Parsed from the full 307-finding dump:

- **207 of 217 (95.4%)** have *only* instance-implicit (`[...]`) arguments unused.
- 2 are mixed; 8 have no instance argument at all.
- Dominant types: `[DecidableEq sig.preds]` ×130, `[Fintype sig.preds]` ×122,
  `[Nontrivial D]` ×41, `[IsDualClosed C]` ×23, `[IsOrderedAddMonoid D]` ×8.
- Concentration: 167/217 in `FormalSystem.Metalogic.WeakCanonical`, 21 in
  `FormalSystem.Semantics.TaskFrame`, 21 in `FormalSystem.Metalogic.Decidability`.

These are typeclass parameters retained for signature uniformity across families of
declarations that share one interface. Removing them would change public signatures across the
largest subsystem in the tree for no semantic gain, and the linter's own advice
(delete the argument) is wrong for a uniform-interface family. This is the paradigm case for
grandfathering with a written rationale.

The 10 non-instance findings — `branchTruthAt_untl`/`branchTruthAt_snce` (4 unused hypotheses
each, `Bridge/IntTruth.lean:856,869`), `regionFrame`/`regionHistory`
(`Bridge/RegionFrame.lean:163,306`), `StepD.badComp_isBadInterval` (`NoGaps.lean:931`),
`ghr93_strategy_compose.compose_wc`/`_right` (`EFGames/Composition.lean:236,450`),
`exists_singleton_class_between`/`kEquiv_classBlock`/`goodDense_unionClasses`
(`RealModel/DoetsTheorem.lean:1923,1972,2025`) — are genuine dead hypotheses in theorem
statements. Removing them is a real cleanup but a signature change with call-site fallout;
recommend recording them as a named future item rather than folding them into this task.

#### `docBlame` (51) — burn down to 0

Breakdown by fix shape:

| Shape | Count | Fix |
|---|---|---|
| structure field projections (`ProofStep.*` ×9, `RuleProfile.*` ×7, `OperatorDistribution.*` ×6, `EnrichedCountermodel.*` ×5, `DecideCacheKey.*` ×2, `TheoremEntry.*` ×2, `MinCyc.*` ×2) | 33 | add `/-- … -/` above each field |
| `QZStructure` + `.interp` / `.toMonadic` / `.toOrdered` | 4 | add docstrings |
| tactic-syntax declarations (`modalSearchParam`, `tacticModal_search__1`, `tacticPropositional_search__1`, `tacticTemporal_search__1`, `tacticTm_auto_`) | 5 | add docstrings to the `syntax` commands (also clears `tacticDocs`) |
| `where`-clause auto-helpers (`bestFirstSearch.searchLoop`, `iddfsSearch.iterate`, `PriorityQueue.insert.insertSorted`) | 3 | in-source `attribute [nolint docBlame] …` — a `where` helper cannot carry a docstring |
| plain defs (`decidableValidZTime`, `decidableValidZTimeFamily`, `goodGroupable`, `nextConj`, `noBlockingTriple`, `IsContempEquivDenseCD`) | 6 | add docstrings |

**Verified**: `attribute [nolint docBlame] bestFirst.loop` on a `where`-generated name is
accepted by Lean (`lean_run_code`), so the 3-entry residue can move out of the central JSON into
in-source exemptions.

#### `tacticDocs` (4) — burn down to 0, jointly with docBlame

`FormalSystem/Automation/Tactics/Commands.lean` declares each search tactic twice — a bare-`num`
form and a named-parameter form (`:115` and `:119` for `modal_search`; `:191` and `:192` for
`temporal_search`). Only the first of each pair inherits the preceding `/-- … -/`; the second
gets the auto-disambiguated name `tacticModal_search__1` and no docstring. Adding a docstring
to the second `syntax` command of each pair clears both the `tacticDocs` finding and its
`docBlame` twin.

#### `defsWithUnderscore` (33) — burn down to 0

The Mathlib linter (`Style.lean:553`, predicate `isBadNameWithUnderscore` at `:535`) flags
declarations that are `isDefinition` (i.e. `def`/`instance`, never `theorem`) whose name contains
`_`. The project's *own settled rule*, recorded in `docs/development/NAMING_CONVENTION_DEVIATION.md`,
is that data-producing declarations — explicitly including all `DerivationTree`-valued results —
take lowerCamelCase. All 33 live entries violate that rule; the document itself asserts the
category was driven to 0 and closed. This is a regression against a documented convention, not a
standing deviation, which is the strongest possible case for burn-down.

Sizing (token occurrences across `FormalSystem/` + `Tests/`, including the declaration itself):
**141 total across 33 declarations**; median 2; largest `co_derived` (16), `someFuture_mono`
(13), `frame_condition` (12), `notGNot_imp_F` (11).

Two need a different treatment: `instSuccOrderLexProdRatInt_formalSystem` and
`instPredOrderLexProdRatInt_formalSystem` (0 references) are Lean-generated names for the
anonymous instances at `WeakCanonical/GroupModel/RamseyFactorization.lean:174,188`. The fix is
to give those instances explicit lowerCamelCase names. (Mathlib's linter whitelists a
`_mathlib` suffix but not the analogous `_formalSystem`, so no whitelist route exists.)

#### `structureInType` (1) — keep, as an in-source documented exemption

`FormalSystem.Automation.MembershipWitness` (`Automation/ProofSearch/Core.lean:219`) is
`structure … : Type where proof : φ ∈ Γ` — a `Type`-valued structure with a single `Prop` field.
The `Type` universe is load-bearing: `findMembershipWitness` returns `Option
(MembershipWitness Γ φ)` and the proof-search layer eliminates it in data position, which a
`Prop`-valued structure could not support (large elimination). This is the same argument the
naming document already makes for `DerivationTree`, so it belongs in the same policy record.
Move it from `nolints.json` to `@[nolint structureInType]` at the declaration with that reason
stated at the site.

#### Resulting shape of `scripts/nolints.json`

| Category | Now | After |
|---|---|---|
| `unusedArguments` | 217 | 217 (grandfathered, documented) |
| `docBlame` | 51 | 0 |
| `defsWithUnderscore` | 33 | 0 |
| `tacticDocs` | 4 | 0 |
| `simpNF` | 1 | 0 |
| `structureInType` | 1 | 0 (moved to in-source `@[nolint]`) |
| **total** | **307** | **217** |

This satisfies the acceptance criterion "`nolints.json` shrinks by at least the categories the
recorded policy commits to" with a 90-entry (29%) reduction.

### Regenerating `nolints.json` safely

`--update` rewrites the file wholesale from the *current* findings
(`.lake/packages/batteries/scripts/runLinter.lean:154-157`): it drops entries that no longer fire
**and grandfathers every new finding**, including a genuine regression. It writes to the literal
path `scripts/nolints.json` relative to CWD (`:133`), so it must be run from the repo root, and
it sorts by `(linter, declName)`, so diffs are deterministic.

The safer route, which yields the same file with a reviewable diff and no blanket-grandfather
risk:

```bash
# after fixing category X, remove exactly that category by hand
jq 'map(select(.[0] == "X" | not))' scripts/nolints.json > /tmp/n.json && mv /tmp/n.json scripts/nolints.json
lake exe runLinter FormalSystem   # must exit 0
```

(The `| not` form is required per the repo's jq-escaping rule.) Exit 0 proves both that the
category is genuinely fixed and that no new finding appeared. Verified: the `jq` filter above
takes the file from 307 to 274 entries when applied to `defsWithUnderscore`.

### Documentation and comment claims that go stale with this work

| Location | Stale claim | Correction |
|---|---|---|
| `.github/workflows/ci.yml:28` | "grandfathers the 307 pre-existing findings" | 217 |
| `.github/workflows/ci.yml:31` | "dupNamespace … 14 pre-existing warnings in ChronicleTypes.lean" | 0 |
| `scripts/check-module-invariants.sh:434` | "grandfathers the 307 findings" | 217 |
| `scripts/check-module-invariants.sh:1395` | "grandfathers the 307 findings" | 217 |
| `scripts/check-module-invariants.sh:1416-1421` | "Validated against ChronicleTypes.lean: finds exactly the same 14 declarations" | validation anchor disappears; reword, and record that `lake env lean <file>` is a ~2 s real-linter cross-check |
| `scripts/check-module-invariants.sh:28-30` | C16 header summary naming the grandfathered batch | update category list |
| `docs/development/NAMING_CONVENTION_DEVIATION.md` "Outcome" table | `defsWithUnderscore` after = 0 (live 33); `unusedArguments` 124 (live 217); `docBlame` 39 (live 51) | refresh to measured values |
| `docs/development/NAMING_CONVENTION_DEVIATION.md` "How to re-audit" | "CI runs `lean-action` with `lint: false`" | CI sets `lint: true` (`ci.yml:34`); `lake lint` now gates |

The `specs/reviews/review-2026-09-07.md:68` row (`nolints.json … 307`) is a dated review
artifact under `specs/` and should be left as the historical record it is.

## Decisions

- **simpNF**: delete `length_range_map` rather than dropping its `@[simp]`. Deleting removes a
  duplicate of two Mathlib simp lemmas; dropping the attribute only hides the finding.
- **dupNamespace**: Option C (relocate the structure into `FormalSystem.Metalogic.BXCanonical`)
  over renaming the structure or the namespace. It is the smallest edit (10 lines, 1 file), the
  only one that keeps Burgess's term "Chronicle" for the type, and it is reference-transparent
  at every call site.
- **`unusedArguments`**: permanently grandfathered, with the 95.4%-instance-argument measurement
  as the written justification.
- **Every other category**: burned down to zero, with the two irreducible residues
  (`structureInType` ×1, `where`-helper `docBlame` ×3) migrated from `nolints.json` to in-source
  `@[nolint]` attributes carrying a per-site reason — following the mechanism argument already
  made in `NAMING_CONVENTION_DEVIATION.md` ("The surviving exemptions, and why they are not a
  new suppression file").
- **`nolints.json` regeneration**: per-category `jq` removal plus a green `lake exe runLinter`,
  not `lake exe runLinter --update`.
- **Policy home**: `docs/development/NAMING_CONVENTION_DEVIATION.md`, refreshed and extended,
  rather than a new document. It already carries the architectural root cause, the in-source-vs-
  central-JSON argument, and the re-audit warnings that this policy needs.

## Recommendations

Suggested phase decomposition, each phase independently verifiable and independently
committable:

1. **simpNF (1 file, ~10 lines).** Delete `length_range_map`; rewrite 5 use sites; drop the
   `simpNF` row from `nolints.json`. Verify: `lake env lean …/Extraction.lean` clean, then
   `lake build` + `lake exe runLinter FormalSystem` exit 0.
2. **dupNamespace (1 file, ~10 lines).** Apply Option C. Verify: `lake env lean
   …/ChronicleTypes.lean` reports 0 warnings; full `lake build` green (this is the gate for the
   13 downstream files in the namespace); C16 textual scan reports PASS.
3. **`defsWithUnderscore` (33 renames, ~141 sites).** Rename to lowerCamelCase per the settled
   rule; name the two anonymous instances explicitly. Drop the category from `nolints.json`.
   Largest single group is the 20 `FormalSystem.BaseLanguage.*` entries, which are 2 sites each.
4. **`docBlame` + `tacticDocs` (~48 docstrings + 3 in-source `@[nolint]`).** Field projections
   first (33, purely mechanical), then the 5 tactic-syntax docstrings (which clear `tacticDocs`
   too), then the 6 plain defs. Drop both categories from `nolints.json`.
5. **`structureInType`.** Move to `@[nolint structureInType]` on `MembershipWitness` with the
   large-elimination reason stated at the site; drop the row.
6. **Policy + comment refresh.** Rewrite the `NAMING_CONVENTION_DEVIATION.md` Outcome table and
   re-audit section against measured values; add the `unusedArguments` grandfathering rationale;
   correct the seven stale numeric claims in `ci.yml` and `check-module-invariants.sh`.

Phase ordering note: phases 3 and 4 both invalidate large olean subtrees, so each should end
with one full `lake build` rather than interleaving. Phase 2 must precede nothing in particular
but is the highest-risk single edit and benefits from landing on its own commit.

Every `lake build` must be detached and guarded per
`context/project/lean4/operations/long-builds.md`:
`bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` under
`Bash(run_in_background: true)`.

## Risks & Mitigations

- **Option C breaks a downstream file that uses `open …Chronicle` + bare `Chronicle`.** No such
  site exists today (audited). Mitigation: the full `lake build` in phase 2 is the gate; the fix
  if it ever fires is to add `open FormalSystem.Metalogic.BXCanonical` to the affected file.
- **`--update` silently grandfathers a regression.** Mitigation: the per-category `jq` +
  green-`runLinter` protocol above; never run `--update` as part of this task.
- **Rebuild cost dominates.** Phases 3-4 touch modules deep in the import graph; a docstring-only
  edit invalidates every transitive dependent. Mitigation: batch each category into one build;
  use `lake env lean <file>` for per-file pre-checks (2-3 s) before paying for a full build.
- **A concurrent session edits the same files.** Observed during this research: another agent
  transiently modified `scripts/check-module-invariants.sh` and seven `README.md` files, shifting
  line numbers by ~50. Mitigation: re-derive line anchors with `grep -n` immediately before
  editing rather than trusting the numbers in this report verbatim; all line numbers here were
  re-verified against a clean `HEAD` tree at the end of research.
- **`docBlame` on `where`-helpers cannot be fixed by documentation.** Confirmed. Mitigation: the
  in-source `@[nolint docBlame]` route, verified to compile.

## Tactic Survey Results

- Not applicable. This task contains no proof obligations — every change is a rename, a
  docstring, a declaration relocation, or a lemma deletion. The one tactic-level change (the five
  `length_range_map` use sites) was verified by direct elaboration rather than by tactic search;
  `simp only [Periodic.cyc, List.length_map, List.length_range]` and `rw [h…]; simp` both
  succeed, and the file elaborates with zero diagnostics.

## Context Extension Recommendations

- **Topic**: cheap per-file Lean linter verification.
- **Gap**: `.claude/context/project/lean4/` documents blocked MCP tools and long-build handling
  but does not record that `lake env lean <file>` re-elaborates a single file against existing
  oleans in seconds, runs all default-on syntax linters (`dupNamespace` among them), and writes
  no oleans — making it a zero-cost pre-check before paying for a guarded full build.
- **Recommendation**: add this to `.claude/context/project/lean4/operations/` alongside
  `long-builds.md`, as the complementary "cheap check" to that file's "expensive check".

## Appendix

### Commands used

- `lake exe runLinter FormalSystem` — 307-finding baseline (with `scripts/nolints.json`
  temporarily `[]`), and exit-0 confirmation with the real file.
- `lake lint` — 8 s, exit 0, `Default modules: #[FormalSystem]`.
- `lake env lean <file>` — 2.0-3.3 s per file; real `dupNamespace` output; used to verify both
  prototypes.
- `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached) — green,
  2591 jobs.
- C16's `dupNamespace` scanner, extracted from `scripts/check-module-invariants.sh` lines
  1443-…`PYEOF` and run standalone against both the current tree (14) and the Option C prototype
  (0).
- `mcp__lean-lsp__lean_run_code` — four minimal-model experiments confirming Option C's name
  resolution, the `open`-only failure mode, and `attribute [nolint docBlame]` on a `where`
  helper.

### Key toolchain references

- `.lake/packages/batteries/scripts/runLinter.lean:133` (nolints path), `:154-157`
  (`--update` semantics), `:169-176` (filtering, exit code).
- `.lake/packages/mathlib/Mathlib/Tactic/Linter/Lint.lean:79-114` (`dupNamespace`, default-on).
- `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean:535-566` (`isBadNameWithUnderscore`,
  `defsWithUnderscore`).
- `.lake/packages/mathlib/Mathlib/Tactic/Linter/TacticDocumentation.lean:31-56` (`tacticDocs`).
