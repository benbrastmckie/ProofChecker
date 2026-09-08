# Research Report: ProofStepExport repair and out-of-closure `lean_exe` root gating

- **Task**: 555 - fix_proofstepexport_and_manifest_out_of_closure_roots
- **Started**: 2026-09-08T00:30:21Z
- **Completed**: 2026-09-08T01:42:00Z
- **Effort**: ~70 minutes (measurement-heavy; every claim below was executed, not inferred)
- **Dependencies**: None upstream. Downstream: tasks 557 (rename burndown) and 558 (gate hardening) both depend on this one.
- **Sources/Inputs**:
  - `FormalSystem/Automation/ProofStepExport.lean`, `FormalSystem/Theorems/ContextualProofs.lean`, `FormalSystem/Theorems.lean`
  - `lakefile.lean`, `.github/workflows/ci.yml`, `scripts/check-module-invariants.sh`, `scripts/module-invariants-manifest.txt`, `scripts/nolints.json`
  - `docs/development/MODULE_INVARIANTS.md`, `docs/development/NAMING_CONVENTION_DEVIATION.md`
  - `.lake/packages/batteries/scripts/runLinter.lean`, `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean`
  - Executed: `lake build`, `lake env lean`, `lake exe runLinter`, `lake exe proof_extractor`
- **Artifacts**:
  - `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/reports/01_proofstepexport-out-of-closure-gate.md`
  - `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/verified-repair.patch` (end-to-end verified; `git apply --check` clean)
- **Standards**: report-format.md, subagent-return.md

## Executive Summary

- The three reported `Application type mismatch` errors reproduce exactly (1479:83, 1496:83, 1497:74) and the diagnosis in the task description is correct.
- **The three-line repair is not sufficient, and the task description's WORK item (1) understates the job by two orders of magnitude.** Repairing only those three sites makes **873 further errors** surface (`don't know how to synthesize implicit argument 'fc'`, across 583 source lines). The three mismatches were *masking* them: Lean suppresses unassigned-metavariable reporting for a declaration that has already logged an error.
- A minimal, mechanical, **end-to-end verified** repair exists: **77 changed lines**, after which the module elaborates with **zero errors**, `lake exe proof_extractor` links, runs, and processes **487/487 theorems emitting 12,077 proof steps**. The patch is saved as an artifact.
- **`scripts/module-invariants-manifest.txt` is the wrong mechanism and would actively fail.** C6's reachability walk already seeds itself from every `root :=` in `lakefile.lean`, so every `lean_exe` root is *reachable* by C6's own definition; adding `ProofStepExport` there trips C6's `stale_manifest` branch (`manifest entr(y/ies) name a REACHABLE module ... delete the lines`). The gate set must be *extended*, not the manifest.
- The predicted linter exposure is **65, not 66**, and — critically — **it does not happen at all** under a compile-only gate. It is triggered only by widening the *lint* closure, which is task 558's job. Recommend 555 stays compile-only so every commit stays green.

## Context & Scope

Scope was: (a) diagnose and verify a repair for `ProofStepExport.lean`; (b) map exactly which Lake targets are and are not compile-checked today, and by what; (c) determine the correct gate mechanism and its negative test; (d) measure the downstream lint exposure so tasks 555/557/558 can be sequenced without a red CI window.

Constraint honoured throughout: no `sorry`, no axiom, no deferral. The repair recommended below is complete and verified, not staged.

All builds were run detached through `.claude/scripts/lake-build-guard.sh`. Note for implementers: the guard takes the lake *subcommand* directly (`-- build ...`, `-- exe ...`); passing `-- lake build ...` is rejected.

## Findings

### Codebase Patterns

#### F1 — The three errors reproduce byte-for-byte

`lake build FormalSystem.Automation.ProofStepExport` fails with exactly three `error:` lines, at `1496:83`, `1497:74`, `1479:83`, each `Application type mismatch: The argument s/r has type Formula but is expected to have type FrameClass`. `FormalSystem.Theorems.ContextualProofs` itself builds fine (target 1430/1431); only the exe root fails.

Root cause confirmed: each `_weakened` declaration in `ContextualProofs.lean` begins `{fc : FrameClass}`, so under `@` the first positional slot is `fc`, and the trailing `s` / `r` lands there.

#### F2 — Two repairs for those three sites both elaborate; one matches house idiom

Both `@b_combinator_weakened .Base (A := p) (B := q) (C := r) s` and `b_combinator_weakened (fc := .Base) (A := p) ... s` elaborate to the correct type. The first matches the idiom already used ~16 times in the same file (`mkEntry "bCombinator" (@bCombinator .Base (A := p) (B := q) (C := r))`) and is the recommended form.

#### F3 — The masked second wave: 873 errors, 583 lines

This is the load-bearing finding. With only the three sites repaired:

| Source state | `lake env lean` errors |
|---|---|
| as committed | 3 (`Application type mismatch`) |
| three sites repaired | **873** (`don't know how to synthesize implicit argument 'fc'`) across 583 lines |

Independently corroborated by a minimal probe outside the file: a two-line `mkEntry`-shaped helper applied to `identity_weakened p q` reproduces the same `don't know how to synthesize implicit argument 'fc'`. So the 873 are genuine, not an artifact of the harness.

Mechanism: `mkEntry` (line 114) takes `{fc : FrameClass}` and uses it only inside a closure (`frameClassToString fc`), so `fc` appears in neither the argument type nor the result type of a registry entry whose theorem is frame-class-generic. Nothing constrains it, and it is left unassigned. `lake env lean` also caps at `maxErrors=100` by default — the true count needs `-DmaxErrors=100000`.

#### F4 — Verified 77-line repair (zero errors, executable runs)

Saved as `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/verified-repair.patch` (`git apply --check` clean against the current working tree). Three mechanical rules:

1. Insert `.Base` positionally after `@` at lines 1479, 1496, 1497 (F2).
2. Rename `mkEntry` -> `mkEntryAt`, changing `{fc : FrameClass}` to an explicit `(fc : FrameClass)` second parameter; add a new `mkEntry (name) {Γ φ} (tree : DerivationTree .Base Γ φ) := mkEntryAt name .Base tree`. The `.Base` in the *argument type* is what pins `fc` by unification at the ~455 generic sites, with no per-site edit.
3. Rewrite the **31** entries that genuinely are not Base to `mkEntryAt "<name>" .ZTime` / `.Dense`. They are listed in the Appendix. All 31 already pin `(fc := .ZTime)` / `(fc := .Dense)` inside the tree, so this is a faithful transcription, not a semantic change.

Verified outcomes after applying: `lake env lean -DmaxErrors=100000` reports **0 errors**; `lake exe proof_extractor` exits 0 with `Theorems processed: 487/487`, `Total proof steps: 12077`, `Axiom coverage: 42/45`, `Rule coverage: 7/7`. The working tree was restored to its committed state afterwards (md5 verified).

Watch item for the implementer: an intermediate experiment (a file with a syntax error) produced `maximum recursion depth reached in the code generator`. The verified patch does not, but the 488-element list is close enough to that boundary that the real `lake build` (which emits C, unlike a bare `lake env lean`) must be re-run rather than assumed.

#### F5 — Exact gate topology (measured, not assumed)

`@[default_target]` sits on `lean_lib FormalSystem` only. Reachability from the two library roots:

- `FormalSystem` closure: 458 modules. `BimodalTest` closure: 509 modules.
- **11 `FormalSystem.Automation.*` `lean_exe` roots plus `CheckInitImports` are outside both**: `DatasetExport`, `ProofStepExport`, `EnumBenchmark`, `BenchmarkAnchors`, `BenchmarkOracle`, `FormulaMutator`, `TableauBridge`, `TableauProofStepPipeline`, `TraceExporter`, `ProofFirstExporter`, `MachineAppendixExport`, `CheckInitImports`. (`DatasetValidator` is inside the *test* closure.)
- **13 modules are reachable only through an exe root**: those 11, plus `FormalSystem.Automation.AxiomNames` and `FormalSystem.Theorems.ContextualProofs`.
- `FormalSystem/Theorems.lean` aggregates 11 siblings but **not** `ContextualProofs` — that is the sole reason `ContextualProofs` is outside the library closure. C8 checks aggregator *existence*, not aggregator *completeness*, so nothing flags it.

#### F6 — The manifest cannot hold these entries

`scripts/check-module-invariants.sh` (reachability block, ~line 784) seeds its walk with `["FormalSystem", "BimodalTest"]` **plus every `root := \`X`** scraped from `lakefile.lean`. Consequently:

- Every `lean_exe` root is already classified *reachable*, so C6 never lists it as unmanifested — which is precisely why `ProofStepExport` has been failing invisibly.
- Adding it to `scripts/module-invariants-manifest.txt` triggers the `stale_manifest` branch: `FAIL C6 ... manifest entr(y/ies) name a REACHABLE module; 'lake build' already guards these -- delete the lines`. The manifest's own header states the same contract.

So the task title's "manifest out-of-closure roots" phrasing must be read as *bring under a gate*, not *add to that file*. The `broken:` prefix convention in the manifest is likewise not applicable: it is for modules that are unreachable **and** known-broken, and would only record the rot rather than fix it.

#### F7 — Only ProofStepExport is broken

`lake build` over the other eleven out-of-closure exe root modules exits 0 with no `error:` line. The new gate therefore lands green on day one; there is no hidden second failure to burn down first.

#### F8 — "Continuous" needs CI, and `@[default_target]` is ruled out on cost

`.github/workflows/ci.yml` runs `leanprover/lean-action@v1` with `build`/`test`/`lint`. It does **not** run `scripts/check-module-invariants.sh` (grep over the repo confirms the script is referenced only from `README.md`, `docs/`, and `scripts/readme-inventory.sh`). A check-only fix is therefore a local gate, not a continuous one.

The tempting native fix — marking the `lean_exe` targets `@[default_target]` so plain `lake build` covers them — is ruled out on measured cost: linked binaries in `.lake/build/bin/` are **240-310 MB each** (`checkInitImports` 239 MB, `dataset_generator` 311 MB). Twelve of those on every CI build is several GB of link output and a large time cost, to buy elaboration coverage that a module-target build gives for free. It would also silently widen `lake lint` (see F10), coupling two decisions that should stay separate.

### External Resources

#### F9 — How the linter's scope is actually determined

From `.lake/packages/batteries/scripts/runLinter.lean`: `runLinterOnModule` does `importModules #[module, Batteries.Tactic.Lint]` then `getDeclsInPackage module.getRoot`. So the lint surface is *the import closure of the named module*, filtered to the `FormalSystem` root namespace. With no module argument, `resolveDefaultRootModules` walks `workspace.root.defaultTargets` — which today is `lean_lib FormalSystem` alone.

Consequence: compiling a module does **not** lint it. Only importing it into a linted root does.

#### F10 — Measured lint exposure: 65, not 66, and only if the lint closure widens

- Baseline today: `lake exe runLinter FormalSystem` -> `-- Linting passed for FormalSystem.` (exit 0). `scripts/nolints.json` holds 217 entries, all `unusedArguments`; no `ContextualProofs` entry exists.
- `lake exe runLinter FormalSystem.Theorems.ContextualProofs` -> `Found 65 errors ... with 14 linters`, all `defsWithUnderscore`, all in `ContextualProofs.lean`.
- The file has 66 `def`s. The 66th, `mp_chain_2`, is exempt by rule, not by luck: `Mathlib/Tactic/Linter/Style.lean`'s `isBadNameWithUnderscore` returns `false` for a last component ending `_1`, `_2`, or `_mathlib`. `mp_chain_2_weak` *is* flagged, which is the same rule seen from the other side.

#### F11 — The full debt behind the exe-root wall is 158, not 65

Running `runLinter` against each out-of-closure exe root (all findings are in modules outside the `FormalSystem` closure, since that root lints clean):

| Module | `defsWithUnderscore` | `docBlame` | Total |
|---|---|---|---|
| `Automation.DatasetExport` | 20 | 12 | 32 |
| `Automation.MachineAppendixExport` | 0 | 16 | 16 |
| `Automation.FormulaMutator` | 0 | 14 | 14 |
| `Automation.TableauBridge` | 0 | 12 | 12 |
| `Automation.BenchmarkOracle` | 0 | 9 | 9 |
| `Automation.TraceExporter` | 0 | 5 | 5 |
| `Automation.EnumBenchmark` | 0 | 4 | 4 |
| `Automation.DatasetValidator` | 0 | 1 | 1 |
| `Automation.BenchmarkAnchors`, `Automation.TableauProofStepPipeline`, `Automation.ProofFirstExporter`, `Automation.AxiomNames` | 0 | 0 | 0 |
| **exe-root subtotal** | **20** | **73** | **93** |
| `Theorems.ContextualProofs` | 65 | 0 | 65 |
| **total** | **85** | **73** | **158** |

`DatasetExport`'s 20 are structure projections (`DatasetRecord.formula_str`, `frame_class`, `pattern_key`, ...) whose names are the emitted JSON field names — renaming them is a data-format change, not a cosmetic one. That is materially harder than `ContextualProofs`' 65 and is in **neither** task 557's nor task 558's declared `file_scope`.

### Recommendations

Priority order. Every step below is sorry-free and axiom-free; nothing here defers work into a placeholder.

1. **Apply the verified repair to `ProofStepExport.lean`** (F4). Use the saved patch or re-derive it from the three rules. Then re-run the real `lake build FormalSystem.Automation.ProofStepExport` (not just `lake env lean`) to exercise C emission, and `lake exe proof_extractor --output <tmp>` to confirm 487/487.
2. **Add a new invariant to `scripts/check-module-invariants.sh` — do not touch the manifest** (F6). Shape: scrape `root := \`X` from `lakefile.lean` exactly as the C6 reachability block already does, and run `lake build <X>` for each. Self-maintaining: a newly added `lean_exe` is covered the day it is declared, with no list to forget. Skip cleanly under `--no-build`, as C1/C2/C6/C16/C24 do, and add it to the `--no-build` list in the script header and in `docs/development/MODULE_INVARIANTS.md`.
3. **Add a CI step so the gate is genuinely continuous** (F8). One `lake build <exe root modules>` step in `.github/workflows/ci.yml` after the lean-action step. Elaboration only, cached against the same build the action already produced; no linking. Note `.github/workflows/ci.yml` is outside task 555's recorded `file_scope` — `file_scope` is descriptive, not enforced, but the plan should name the addition explicitly rather than let it arrive unannounced.
4. **Write the mandated negative test** (`docs/development/MODULE_INVARIANTS.md` requires one for any new or widened invariant, and cites C15/C24 as precedent). Concretely: reintroduce a one-character break in a *different* out-of-closure root (`TraceExporter` is the smallest at 5 known lint findings and 0 build errors), observe `FAIL` and a non-zero script exit, restore, observe `PASS`. Record the observation in `MODULE_INVARIANTS.md` in the same voice as the C15/C24 paragraphs. Do not use `ProofStepExport` for this test — it is the module being repaired, so a failure there proves nothing about the gate.
5. **Keep task 555 compile-only; do not widen the lint closure here.** This is the "explicitly stage the exposure" branch the task description asks for, and the dependency graph already implies it (557 depends on 555; 558 depends on 555 and 557). Under a compile-only gate the linter's scope is unchanged (F9), so `lake lint` and CI stay green at every commit, and no `nolints.json` grandfathering is needed — which matters, because `NAMING_CONVENTION_DEVIATION.md` records that grandfathering `defsWithUnderscore` into that file is exactly the silent-drift failure the project already suffered once and deliberately reversed.
6. **Flag the scoping gap to the orchestrator rather than absorbing it.** Task 558 ("close defsWithUnderscore gate evasion routes") will widen the lint closure. At that point the 93 exe-root findings (F11) become failures, and they are in no current task's `file_scope`. Recommend `/spawn` off 555 or 558 for the exe-root lint burndown, with `DatasetExport`'s 20 JSON-field projections called out as the hard sub-case.

## Decisions

- **Repair via a `mkEntry` / `mkEntryAt` split, not 455 per-site edits.** Both reach zero errors; the split is 77 changed lines against ~470, keeps the common case unannotated, and makes the non-Base entries visually distinct at the call site. Verified end-to-end before recommending.
- **`.Base` is the correct frame class for the 455 generic entries.** They are frame-class-generic theorems; `.Base` is the weakest class and is what the 16 sites that already pin a class explicitly use. It is also what `frameClassToString` will now emit for them — previously nothing was emitted, because the module never compiled.
- **Reject the manifest route outright** rather than presenting it as an option, because C6 fails on it by construction (F6).
- **Reject `@[default_target]` on the `lean_exe` targets** on measured link cost (F8).
- **Report 65, not 66**, for the `ContextualProofs` exposure, with the exempting rule cited (F10). The task description's 66 counted `def`s, not linter findings.
- No `user_decision` is set. Every choice above is settled by measurement, by an existing gate's own contract, or by the recorded task dependency order; none is a matter of taste or an external cost.

## Risks & Mitigations

- **Risk**: the repaired 488-element registry sits near the code generator's recursion limit; `lake env lean` does not emit C, so a bare elaboration check under-tests it. **Mitigation**: verification step 1 above runs the real `lake build` and the linked executable; both were already observed green during this research.
- **Risk**: a future `lean_exe` root is added and forgotten. **Mitigation**: recommendation 2 derives the root list from `lakefile.lean` at run time, so there is no list to forget. This is strictly better than the manifest, which requires a human to add a line.
- **Risk**: recommendation 3 slows CI. **Mitigation**: module targets, not exe targets — elaboration only, sharing the cache with the build the action already ran. Eleven modules whose transitive dependencies are all already built.
- **Risk**: the negative test is performed on the module under repair and proves nothing. **Mitigation**: explicitly use a different out-of-closure root (recommendation 4).
- **Risk**: 558 lands and CI goes red on the 93 exe-root findings nobody scoped. **Mitigation**: recommendation 6; surface it now, before 557 starts.
- **Risk**: the saved patch goes stale if `ProofStepExport.lean` is touched before implementation. **Mitigation**: the patch is a convenience; the three rules in F4 are the durable form and can be re-derived mechanically.

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task is a term-level elaboration and build-graph problem; no proof goals were opened, so the LeanHammer portfolio has nothing to act on.

## Context Extension Recommendations

- **Topic**: Lean error masking — unassigned implicit metavariables are not reported for a declaration that already logged an error.
  **Gap**: Nothing in `.claude/context/project/lean4/` warns that an error count from a failing module is a *lower bound*, so a "three errors, three-line fix" reading is the natural and wrong one. This task would have been mis-sized without the experiment in F3.
  **Recommendation**: add a short entry to `.claude/context/project/lean4/patterns/` describing the masking behaviour and the two mitigations used here — repair-then-re-measure on a scratch copy, and `-DmaxErrors=100000` to defeat the default 100-error cap.
- **Topic**: `lake-build-guard.sh` argument shape.
  **Gap**: `.claude/context/project/lean4/operations/long-builds.md` shows `-- <lake args>`, which reads as though the word `lake` belongs there; it does not, and the guard rejects it.
  **Recommendation**: change the canonical invocation's placeholder to `-- <lake subcommand and args>` with a worked `-- build <module>` example.

## Appendix

### The 31 non-Base registry entries (recommendation 1, rule 3)

`.ZTime`: `discrete_symm_fwd_axiom`, `discrete_symm_bwd_axiom`, `discrete_propagate_fwd_axiom`, `discrete_propagate_bwd_axiom`, `discrete_box_necessity_axiom`, `prior_UZ_axiom`, `prior_UZ_axiom_q`, `prior_SZ_axiom`, `prior_SZ_axiom_q`, `z1_axiom`, `z1_axiom_q`, `G_discrete_symm_fwd_axiom`, `G_discrete_symm_bwd_axiom`, `G_discrete_propagate_fwd_axiom`, `G_discrete_propagate_bwd_axiom`, `G_discrete_box_necessity_axiom`, `G_prior_UZ_axiom`, `G_prior_SZ_axiom`, `G_z1_axiom`, `H_discrete_symm_fwd_axiom`, `H_prior_UZ_axiom`, `GG_discrete_symm_fwd_axiom`, `GG_prior_UZ_axiom`, `GG_z1_axiom`.

`.Dense`: `density_axiom`, `density_axiom_q`, `dense_indicator_axiom`, `G_density_axiom`, `G_dense_indicator_axiom`, `H_density_axiom`, `GG_density_axiom`.

Caution for a scripted rewrite: `peirce_axiom_rs` is Base but sits immediately above the `.ZTime` block, so a naive "next `mkEntry` starts the next entry" chunker mis-classifies it. This was observed and corrected during verification.

### Commands used for the measurements

```
bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build <module>
lake env lean -DmaxErrors=100000 <file>          # true error count, defeats the 100-error cap
lake exe runLinter <module>                       # lint surface = that module's import closure
bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- exe proof_extractor -- --output <path>
```

### References

- C6 reachability and manifest semantics: `scripts/check-module-invariants.sh`, reachability / C6 block (~lines 784-865); contract restated in `scripts/module-invariants-manifest.txt`'s header.
- Negative-test mandate and its C15/C24 precedents: `docs/development/MODULE_INVARIANTS.md`.
- `defsWithUnderscore` exemption rule: `.lake/packages/mathlib/Mathlib/Tactic/Linter/Style.lean`, `isBadNameWithUnderscore`.
- Lint scope resolution: `.lake/packages/batteries/scripts/runLinter.lean`, `resolveDefaultRootModules` and `runLinterOnModule`.
- Grandfathering stance this report avoids reopening: `docs/development/NAMING_CONVENTION_DEVIATION.md`, "What would reopen this".
