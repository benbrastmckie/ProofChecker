# Research Report: Task #550

**Task**: 550 - Decompose `MintBound.lean` for publication legibility
**Started**: 2026-09-07T18:39:00-07:00
**Completed**: 2026-09-07T19:05:00-07:00
**Effort**: ~0.5 hours
**Dependencies**: 549 (completed), 554 (completed) — both resolved before this dispatch
**Sources/Inputs**: - Codebase measurement (`MintBound.lean`, `lakefile.lean`, `docs/development/MODULE_INVARIANTS.md`, existing multi-module precedents), task 549 summary, `git log` on the target file
**Artifacts**: - specs/550_decompose_mintbound_for_publication_legibility/reports/01_decompose-mintbound-publication-legibility.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The file is now 15,684 lines, not 15,759, and the ratio to the next-largest live file is 3.08x, not 2.5x.** Task 554 landed the retirement of the nine vacuous `_run` termini (commit `973c4a39e`) between this task's creation and this dispatch. The next-largest live file is `WeakCanonical/EFGames/GapDetection.lean` at 5,090 lines. Both dependencies (549, 554) are `completed`, so the collision this task was gated on is gone.
- **Composition is measured, not estimated.** 7,682 lines (49.0%) are Lean code; 3,935 (25.1%) are `/--` declaration docstrings; 3,127 (19.9%) are `/-!` section prose; 894 are blank; 47 are line comments. **45% of the file is prose.** It carries 751 declarations across 30 top-level sections. The C9 register is lines 14,777–15,684: **908 lines, zero declarations, 100% prose**, sitting at the very end of the file.
- **The organizing principle must be file order, not theme.** The section labels (A/A2/A3…, B/B2…, C1…C12, D1…D5) already encode a four-block thematic scheme — and the physical order interleaves them (A, A2, B, A3, B2, B3, A4, …; C11 and C12 sit *after* D1 and D2). A dependency-graph measurement shows the thematic grouping is **cyclic**: A↔B (11 and 17 edges each way), C↔D (C11→D1, C12→D2 against D2→C7, D2→C3, …). File order is the only acyclic cut. Confirming this: the reference analysis found **zero** forward references to later-declared names — file order *is* the dependency order.
- **The blocking technical constraint is `private` visibility, and the repo has already paid for it once.** `private` in Lean 4 is module-scoped. 16 private declarations are consumed across the proposed module boundaries (`pickBranches`, `pick_branches_eq`, `pickOrd`, `pick_ord_eq`, `pick_stage_source`, `pickOrd_mono`, `fwp`, `rm_bn`, `mfp`, `mfq`, `mwE/mwG/mwP/mwQ`, `pickBranches_time_dichotomy`, `pickBranches_knownTimes_subset`). **In-repo proof of the constraint**: `MintBound.lean:6001-6003` declares `pick_split'` with the docstring "The `.split` counterpart of `Fuel.lean`'s `pick_split`, which is `private` there" — an existing duplicated proof that exists *only* because a private name did not cross a module boundary. `pick_splitOrdered'` (`:815`) is the same story.
- **Recommended: 18 modules under `MintBound/`, with `MintBound.lean` retained as the aggregator.** Max module 1,815 lines, median ~750. Import DAG depth 12 with real parallel branches (`TimeCensus` ∥ `Terminus`/`ClosureResidual`; `LabelHeadroom` ∥ the `SigmaFixed` chain; `BoxFree` ∥ `MintPaysAssembly`), so incremental rebuild cost drops sharply. Full per-module budget and minimal import list in Findings.
- **A sorry-free, axiom-free path exists and is mechanical.** No proof is re-run, no statement changes, no declaration is renamed. The only interface change is dropping the `private` modifier from 16 declarations — names, statements and proofs preserved byte-for-byte.

## Context & Scope

Researched: the actual composition of `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` at HEAD (`55e07f1de`), the constraints any split must satisfy (Lean visibility, Lake target reachability, the repo's own module invariants), the existing decomposition precedents in this tree, and whether a decomposition can preserve the public interface exactly.

Not researched, and deliberately out of scope: whether any declaration should be *removed*. The dispatch says decomposition, not cull, and task 549 already settled the one disposition question that was open.

Measurement method: a comment-state-machine classifier over the file (tracking `/-!`, `/--`, `/-` nesting so that prose is never miscounted as code), a declaration extractor keyed on the `theorem|lemma|def|abbrev|instance|structure|inductive|class` head with modifier stripping, and a whole-file name-reference cross-product to build the section- and module-level dependency graphs. All figures below are outputs of that measurement, not estimates.

## Findings

### Codebase Patterns

**Composition of the file (measured).**

| Line class | Lines | Share |
|---|---:|---:|
| Lean code | 7,682 | 49.0% |
| `/--` declaration docstrings | 3,935 | 25.1% |
| `/-!` section/module prose | 3,127 | 19.9% |
| Blank | 894 | 5.7% |
| `--` line comments | 47 | 0.3% |
| **Total** | **15,684** | |

751 declarations (659 public, 92 `private`). One namespace (`FormalSystem.Metalogic.Decidability`, `:57`–`:15684`), one `open` (`:59`), 22 per-declaration `set_option maxHeartbeats` lines, and five `section … end` blocks carrying `attribute [local simp]` — all five fully contained inside a single top-level section, none straddling a proposed cut.

**Line budget by top-level section, in physical order.** (`code`/`doc`/`prose` are the three content classes; `decls` is declarations.)

| Lines | Span | code | doc | prose | decls | Section |
|---:|---|---:|---:|---:|---:|---|
| 60 | 1–60 | 3 | 0 | 47 | 0 | preamble (license, imports, module docstring) |
| 149 | 61–209 | 77 | 44 | 11 | 14 | A. renaming and irreflexivity invariant |
| 43 | 210–252 | 16 | 22 | 1 | 2 | A2. `applyRule` preserves `IrreflOrd` |
| 144 | 253–396 | 113 | 14 | 5 | 11 | B. reachability transport stack |
| 220 | 397–616 | 148 | 38 | 13 | 17 | A3. `densityRule` and ordering-times |
| 190 | 617–806 | 138 | 27 | 5 | 10 | B2. witness preservation, identification arm |
| 96 | 807–902 | 70 | 6 | 7 | 4 | B3. non-deletion at engine level |
| 51 | 903–953 | 38 | 3 | 6 | 3 | A4. pick bridges |
| 115 | 954–1068 | 79 | 19 | 6 | 5 | A5. engine-level `IrreflOrd` |
| 239 | 1069–1307 | 153 | 39 | 33 | 9 | A6. `OrdTimesLeMaxTime` at branching shapes |
| 401 | 1308–1708 | 226 | 99 | 43 | 24 | A7. `OrdTimesKnown` |
| 100 | 1709–1808 | 41 | 37 | 14 | 7 | A8. the run invariant |
| 72 | 1809–1880 | 46 | 14 | 7 | 4 | B4. `witnessPresent` monotonicity |
| 191 | 1881–2071 | 110 | 55 | 18 | 7 | B5. engine-level growth |
| 92 | 2072–2163 | 29 | 29 | 27 | 6 | C1. the world dimension |
| 793 | 2164–2956 | 593 | 112 | 45 | 37 | C2. fresh-world discipline |
| 316 | 2957–3272 | 138 | 93 | 69 | 15 | C3. the mint potential |
| 193 | 3273–3465 | 119 | 24 | 41 | 7 | C4. the once-only bound |
| 165 | 3466–3630 | 80 | 27 | 42 | 15 | C5. the counting chain |
| 256 | 3631–3886 | 135 | 77 | 33 | 10 | C6. the fuel induction |
| **1,243** | 3887–5129 | 579 | 408 | 167 | 73 | C7. the measure and its figure |
| 259 | 5130–5388 | 106 | 85 | 59 | 7 | C8. terminus at `buildTableauAt` |
| **1,147** | 5389–6535 | 634 | 307 | 151 | 57 | C10. repaired closure residual |
| 683 | 6536–7218 | 351 | 155 | 137 | 33 | D1. the minting census |
| **3,944** | 7219–11162 | 1,942 | 1,153 | 614 | 207 | **D2. `MintPaysForTime`: the verdict** |
| 415 | 11163–11577 | 199 | 137 | 51 | 32 | C11. clause 1's label dimension |
| **1,335** | 11578–12912 | 547 | 408 | 269 | 68 | C12. post-blocking settlement residual |
| 686 | 12913–13598 | 411 | 155 | 79 | 37 | D3. residual at a nonempty universe |
| 530 | 13599–14128 | 202 | 168 | 139 | 14 | D4. the label residual, replaced |
| 648 | 14129–14776 | 358 | 180 | 82 | 19 | D5. engine-level assembly |
| **908** | 14777–15684 | **1** | **0** | **906** | **0** | **C9. the do-not-re-attempt register** |

Two observations the table makes unavoidable. First, **D2 alone (3,944 lines) is 78% of the next-largest live file in the repository** — it is not a section, it is a module that never got extracted. Second, **C9 is 908 lines of pure prose with a single line of code and zero declarations**, physically last. It is the single cheapest and highest-value extraction available.

**The C9 register's own header is already wrong.** Line 14,779 reads "Twenty-four statements that look like the natural next lemma"; the register carries **25** numbered entries. The count drifted when task 463 appended entry 25. That is precisely the class of defect a 15,684-line file hides and a 908-line file does not.

**Existing decomposition precedent in this tree, to be matched exactly.** `FormalSystem/Metalogic/Decidability/BiLasso.lean` is a 15-line aggregator of `BiLasso/*.lean` submodules with a `## Submodules` prose index; `WeakCanonical/Kamp/NfMultiAnchorBridge/` is 27,749 lines over 37 files behind a single aggregator. The convention is settled: `X.lean` beside `X/`, aggregator holds the imports and the reader-facing map.

**Gates a split must satisfy** (from `docs/development/MODULE_INVARIANTS.md`):

| Check | Bearing on this task |
|---|---|
| **C8** | "Every Lean-bearing subdirectory has exactly one sibling aggregator `X.lean` beside `X/`" — **mandates** keeping `MintBound.lean` as the aggregator. This is not merely convenient; omitting it fails the gate. |
| C4 | Every `import FormalSystem.*` resolves — catches a half-finished move. |
| C6 | Unreachable live modules must be listed in `scripts/module-invariants-manifest.txt`. Every new module is imported by the aggregator, so none becomes unreachable and the manifest needs no entry. |
| C1, C2, C3, C14 | Build green, `#print axioms` baseline unchanged for the flagship theorems, sorry count unchanged, documented counts still agree. A pure relocation touches none of these — which is the point of doing it as a pure relocation. |
| C9 (the *invariant*, unrelated to the C9 *register*) | Zero task-number citations under `FormalSystem/`. New module docstrings must cite declaration names, never task numbers. |

`lakefile.lean` uses `roots := #[FormalSystem]`, so new modules enter the build only via the import graph — the aggregator's imports are what make them live. `lake exe checkInitImports` (reporting-only, not gated) wants every `FormalSystem` module to transitively import `FormalSystem.Init`; a docstring-only `Register.lean` with no imports would be the sole new violation, which one `import` line prevents.

**Downstream surface is a single edge.** The only non-test, non-`specs/` importer of `MintBound` is `FormalSystem/Metalogic/Decidability.lean:23`. `MintBound.lean` itself imports exactly one module (`…Termination.Fuel`). Retaining `MintBound.lean` as an aggregator that re-exports every part therefore preserves the downstream interface **exactly and automatically** — `Decidability.lean` needs no edit, and every one of the 659 public declarations remains reachable by the same name from the same import.

### External Resources

No Mathlib search was warranted: this task adds no mathematics. `lean_leansearch`/`lean_loogle`/`lean_state_search` were not called, and no search-tool rate limit or MCP failure occurred. The relevant external fact is a Lean 4 language semantic, corroborated in-repo below rather than taken on authority.

**Lean 4 `private` is module-scoped.** A `private` declaration is accessible only within the file that declares it; it survives into the `.olean` under a mangled `_private.<Module>.<n>.<name>` form that is not reachable by its plain name from an importing module. **The repository already demonstrates this and already paid for it**:

- `MintBound.lean:6001-6003` — `/-- The `.split` counterpart of `Fuel.lean`'s `pick_split`, which is `private` there. Same statement… -/ private theorem pick_split'`
- `Fuel.lean:1676` — `private theorem pick_split`
- The same pattern for `pick_splitOrdered'` (`MintBound.lean:815`) against `Fuel.lean:1702`.

Two proofs in this tree exist solely because a private name could not cross a module boundary. A decomposition that ignores this constraint does not produce a build error at the cut — it produces a temptation to duplicate proofs, which is the failure mode already on record here.

### Recommendations

**Organizing principle: file order, cut at section boundaries, with the C9 register extracted.** Justified against the two alternatives the dispatch names:

- *By development layer (the A/B/C/D block scheme)* — **rejected, and rejected on measurement rather than taste.** The section-level dependency graph is cyclic under that grouping: B→A carries 30 edges while A5→B3 and A8→B3 go back the other way; D→C carries hundreds of edges (D2→C7 alone is 65) while C11→D1 and C12→D2 go back. Realizing the thematic grouping would require reordering declarations, which means re-elaborating every proof in a file that costs 5–25 minutes per pass, with no way to verify the reordering is faithful short of a full green build. High cost, high risk, no legibility gain over the alternative.
- *By frame class* — **rejected.** Frame class (`.Base`/`.Dense`/`.RTime`/`.ZTime`) is a *parameter* of most statements here, not a partition of them. The measurement finds no section that is frame-class-homogeneous.
- *Register-vs-live* — **adopted, and then extended.** The dispatch is right that C9 is the strongest extraction candidate: 908 lines, zero declarations, and — per task 549's own diagnosis — the reason a reader met nine vacuous headline theorems 3,100 lines away from the register entry that invalidated them. But register-vs-live alone yields a 908-line file and a 14,776-line file, which does not solve the stated problem. The register extraction is **step one**; the file-order cut of the remaining 14,776 lines is what actually delivers reviewability.

**Proposed decomposition: 18 modules, `MintBound.lean` retained as aggregator.** Every boundary falls on an existing `/-!` prose header, so no declaration is split and no `section … end` block is straddled. Minimal imports are the transitive reduction of the measured reference graph — not a linear chain.

| Module (`…/Termination/MintBound/`) | Span | Lines | code | decls | Minimal imports |
|---|---|---:|---:|---:|---|
| `Invariants.lean` | 1–1068 | 1,068 | 682 | 63 | (`Fuel` only) |
| `OrderingTimes.lean` | 1069–2071 | 1,003 | 576 | 51 | `Invariants` |
| `MintPotential.lean` | 2072–3886 | 1,815 | 1,094 | 90 | `OrderingTimes` |
| `Measure.lean` | 3887–5129 | 1,243 | 579 | 73 | `MintPotential` |
| `Terminus.lean` | 5130–5388 | 259 | 106 | 7 | `Measure` |
| `ClosureResidual.lean` | 5389–6535 | 1,147 | 634 | 57 | `Terminus` |
| `TimeCensus.lean` | 6536–7218 | 683 | 351 | 33 | `MintPotential` |
| `TimeReuse.lean` | 7219–7974 | 756 | 218 | 46 | `Measure` |
| `MonotoneIssuance.lean` | 7975–8466 | 492 | 169 | 24 | `ClosureResidual`, `TimeReuse` |
| `OrientedGate.lean` | 8467–9450 | 984 | 435 | 55 | `MonotoneIssuance` |
| `FourComponent.lean` | 9451–10204 | 754 | 487 | 26 | `TimeCensus`, `OrientedGate` |
| `SigmaFixed.lean` | 10205–11162 | 958 | 633 | 56 | `FourComponent` |
| `LabelHeadroom.lean` | 11163–11577 | 415 | 199 | 32 | `ClosureResidual`, `TimeCensus` |
| `PostBlocking.lean` | 11578–12912 | 1,335 | 547 | 68 | `SigmaFixed` |
| `UntlSnceFree.lean` | 12913–13598 | 686 | 411 | 37 | `SigmaFixed` |
| `BoxFree.lean` | 13599–14128 | 530 | 202 | 14 | `UntlSnceFree` |
| `MintPaysAssembly.lean` | 14129–14776 | 648 | 358 | 19 | `UntlSnceFree` |
| `Register.lean` | 14777–15684 | 908 | 1 | 0 | (`Fuel`, for graph hygiene only) |
| **Total** | | **15,684** | **7,682** | **751** | |

Max 1,815 lines, median ~750, import-DAG depth 12. The five D2 sub-cuts (`TimeReuse`, `MonotoneIssuance`, `OrientedGate`, `FourComponent`, `SigmaFixed`) fall on the section's own existing `###`/`####` headers at 7,975 / 8,467 / 9,451 / 10,205; their heading levels want promoting to `#` when they become module docstrings.

**The 16 private declarations that must lose the `private` modifier.** Names, statements and proofs unchanged — only the modifier is dropped, and only for these:

| Private name | Declared in | Consumed from |
|---|---|---|
| `pickOrd`, `pick_ord_eq` | `Invariants` | `OrderingTimes`, `MintPaysAssembly` |
| `pickBranches`, `pick_branches_eq` | `OrderingTimes` | `MintPotential`, `TimeCensus`, `LabelHeadroom`, `UntlSnceFree`, `BoxFree`, `MintPaysAssembly` |
| `pick_stage_source` | `OrderingTimes` | `TimeCensus`, `LabelHeadroom` |
| `pickOrd_mono` | `OrderingTimes` | `MintPaysAssembly` |
| `mfp`, `mfq` | `Measure` | `PostBlocking` |
| `fwp`, `rm_bn` | `ClosureResidual` | `LabelHeadroom` |
| `mwE`, `mwG`, `mwP`, `mwQ` | `TimeReuse` | `OrientedGate`, `SigmaFixed` |
| `pickBranches_time_dichotomy` | `TimeCensus` | `MintPaysAssembly` |
| `pickBranches_knownTimes_subset` | `UntlSnceFree` | `MintPaysAssembly` |

The remaining 76 private declarations stay private, because every consumer lands in the same module under this partition. Widening 16 of 92 is the minimum the cut requires; a coarser partition would widen fewer but leave larger modules, and a finer one would widen more.

**Execution shape.** Additive and verifiable, per the dispatch:

1. Create `MintBound/` and move contiguous line ranges out, bottom-up (`Register` first — it has no dependents at all, so it is the free one), each move a pure `sed`-range extraction plus a license header, module docstring and import block.
2. `MintBound.lean` shrinks to the BiLasso-shaped aggregator: license header, 18 imports, and a `## Submodules` prose map. Its current 47-line module docstring (`:9`–`:56`) is already exactly that map and largely survives as-is.
3. Drop `private` on the 16 named declarations at the moment their module is created.
4. **One** full `lake build` at the end, guarded and detached per `context/project/lean4/operations/long-builds.md` — never per-file. Then `bash scripts/check-module-invariants.sh` for C4/C6/C8.
5. Update `Termination/README.md`'s module table (its `MintBound.lean | 14770` row is already stale against 15,684) and add `MintBound/README.md` matching the directory-README convention.

**Sorry-free and axiom-free by construction.** No proof is re-run against a changed context, no statement is altered, no `sorry` is introduced anywhere, and no axiom is added. The `#print axioms` baseline that C2 and C14 assert is untouched because the *proof terms* are untouched. This is the strongest available answer to the zero-debt requirement: the task does not merely avoid `sorry`, it has no proof obligation at all.

**Zero-cost bonus worth stating.** The file is currently one serial compilation unit at `maxHeartbeats 4000000`. After the split, editing `MintPaysAssembly` recompiles 648 lines rather than 15,684, and the DAG's parallel branches (`TimeCensus` ∥ `Terminus`/`ClosureResidual`, `LabelHeadroom` ∥ `SigmaFixed`, `BoxFree` ∥ `MintPaysAssembly`) let Lake overlap work that is serial today. The dispatch's "expect expensive builds" warning applies to *this* task's verification pass; it stops applying to every task afterwards.

## Decisions

- **File order is the organizing principle**, with register-vs-live as the first cut. Decided against the thematic A/B/C/D grouping on a measured cycle (A↔B, C↔D), not on preference.
- **`MintBound.lean` is retained, not deleted.** Invariant C8 requires the sibling aggregator, and retaining it is also what preserves the downstream interface without editing `Decidability.lean`.
- **The C9 register becomes `MintBound/Register.lean`, a Lean module, not a markdown file.** A Lean module keeps it in the module namespace where a reader browsing the directory finds it, satisfies C8/C6 with no manifest exception, and costs essentially nothing to compile (one code line). The markdown alternative removes it from the compile graph entirely, which is marginally cheaper and materially worse for discoverability. Noted as a reversible choice.
- **`private` is dropped, never renamed.** The constraint "preserve every existing declaration name" is honored exactly; visibility widens for 16 names and nothing else moves.
- **The premise figures are corrected rather than repeated**: 15,684 lines (not 15,759), 3.08x the next-largest live file (not 2.5x), 25 register entries (not 24, and the file's own header says 24).

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| A `private` consumer is missed and the build breaks late, after a 5–25 minute pass. | The 16-name table above is derived from a whole-file reference cross-product, not from reading. Before the expensive pass, re-run that extraction against the split tree as a static check — it costs seconds and catches the error class outright. |
| The measured reference graph over-approximates (a name matched inside a string or a docstring) and an import is added that is not needed. | Harmless in direction: a spurious edge adds an unnecessary import, never a missing one. The classifier already excludes docstring and prose lines from bodies, so the residual risk is a redundant import, not a broken build. |
| Heading levels inside extracted D2 parts (`###`/`####`) read wrong as module docstrings. | Promote to `#`/`##` during extraction. Cosmetic, caught by reading the four new files. |
| `Register.lean` with no imports is flagged by `lake exe checkInitImports`. | Give it one import. Reporting-only tool, but there is no reason to add the sole new violation. |
| `Termination/README.md` and a new `MintBound/README.md` drift from the module table. | Both are written in the same pass as the split, from the table in this report. The existing stale row (14,770 vs 15,684) is evidence this drifts if left to a later pass. |
| A concurrent task claims `MintBound.lean` mid-split. | Both blocking dependencies (549, 554) are `completed` as of this dispatch; `git log` shows 554's commit `973c4a39e` already landed. The `file_scope` serialization edge is clear. |

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task relocates existing proof terms without re-elaborating any goal; there is no proof obligation for a tactic to discharge, and `lean_multi_attempt` / `lean_hammer_premise` have nothing to attempt against.

## Context Extension Recommendations

- **Topic**: Lean 4 module-splitting mechanics — `private` visibility as the binding constraint, section-boundary cutting, and the aggregator-plus-directory convention.
- **Gap**: The lean4 context has `operations/long-builds.md` and MCP tool guidance but nothing on decomposing an oversized module. This repo has now hit the problem at least twice (the `pick_split'`/`pick_splitOrdered'` duplication in `MintBound.lean` is the scar tissue from the first time) and has three worked precedents (`BiLasso/`, `NfMultiAnchorBridge/`, and this task).
- **Recommendation**: add `agent-system/extensions/lean/context/project/lean4/patterns/module-decomposition.md` — **the source store, never `.claude/**` directly** (see `.claude/rules/source-store-deploy-boundary.md`). It should carry: the reference-graph extraction recipe used here, the `private` cross-boundary check, the "file order is dependency order — verify zero forward references" assertion, invariant C8's aggregator requirement, and the batch-verify-once build discipline.

## Appendix

**Measurement scripts** (run against HEAD `55e07f1de`; all reproducible in seconds, no build required):

- Comment-state-machine line classifier over `/-!`, `/--`, `/-` nesting → the composition table.
- Declaration extractor on `^(private |protected |noncomputable |@[…])*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+NAME` → 751 declarations, 92 private.
- Whole-file name cross-product restricted to code lines → the section- and module-level dependency graphs, the transitive reduction giving minimal imports, and the 16 cross-boundary private uses.
- `find FormalSystem Tests -name '*.lean' -not -path '*Boneyard*' | xargs wc -l | sort -rn` → the 15,684 / 5,090 ratio.

**Primary references**

- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — `:57` namespace open, `:59` `open`, `:815` `pick_splitOrdered'`, `:6001-6003` `pick_split'` and its `private`-crossing docstring, `:14777-15684` the C9 register, `:14779` the "Twenty-four" miscount.
- `FormalSystem/Metalogic/Decidability/Verified/Termination/Fuel.lean:1676`, `:1702` — the private originals.
- `FormalSystem/Metalogic/Decidability/Decidability.lean` → `FormalSystem/Metalogic/Decidability.lean:23` — the sole live importer.
- `FormalSystem/Metalogic/Decidability/BiLasso.lean` — the aggregator pattern to match.
- `FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/` — 27,749 lines over 37 modules; the scale precedent.
- `docs/development/MODULE_INVARIANTS.md` — checks C1–C15, C8 in particular.
- `lakefile.lean` — `lean_lib FormalSystem` with `roots := #[FormalSystem]`.
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md` — the retirement that landed as 554 and changed this file's line count.
- `git log` on the target file: `973c4a39e` (554 phase 3, the retirement), `ca538d090` (554 phase 2, the widening lemmas).
