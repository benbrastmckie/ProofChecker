# Implementation Summary: Task #550

- **Task**: 550 - Decompose `MintBound.lean` for publication legibility
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T18:35:00Z
- **Completed**: 2026-09-07T19:45:00Z
- **Effort**: ~1.2 hours wall clock (six full `lake build` passes dominate; edits are minutes)
- **Dependencies**: 549 (completed), 554 (completed)
- **Artifacts**: plans/01_decompose-mintbound-publication-legibility.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` was a single
15,684-line file — 3.08x the next-largest live file in the tree — that interleaved live results
with a register of refuted approaches, so a reader could not tell locally which of the two they
were reading. It is now eighteen modules under `MintBound/`, cut at section boundaries that
already existed, with `MintBound.lean` retained as a 121-line aggregator that declares nothing.
The decomposition is a pure relocation: all 751 declaration names and all proof terms are
preserved, `Decidability.lean` has a zero-line diff across the whole task, and the only semantic
change anywhere is that sixteen declarations lost a `private` modifier they could not keep across
a module boundary.

## What Changed

- `.../Termination/MintBound.lean` — reduced from 15,684 lines to a 121-line aggregator: license,
  18 imports, and a `## Submodules` map. Zero declarations, no `namespace`, no `open`.
- `.../Termination/MintBound/Register.lean` — new, 915 lines, **zero declarations**. The C9
  do-not-re-attempt register, all 25 entries verbatim. This is the extraction the task existed
  for: the record of what did not work no longer sits inside the module carrying what did.
- `.../Termination/MintBound/{Invariants,OrderingTimes,MintPotential}.lean` — new, 1021/1016/1828
  lines, 63/51/90 declarations. The foundation: the renaming and `IrreflOrd`, the ordering-times
  invariants, and `mintPotential` with the fuel induction.
- `.../Termination/MintBound/{Measure,Terminus,ClosureResidual,TimeCensus}.lean` — new,
  1258/272/1161/696 lines, 73/7/57/33 declarations. The measure, the terminus at `buildTableauAt`,
  the repaired closure residual, and the minting census.
- `.../Termination/MintBound/{TimeReuse,MonotoneIssuance,OrientedGate,FourComponent,SigmaFixed}.lean`
  — new, 773/505/997/768/971 lines, 46/24/55/26/56 declarations. D2, the single largest section at
  3,944 lines, broken at its own existing sub-headers.
- `.../Termination/MintBound/{LabelHeadroom,PostBlocking,UntlSnceFree,BoxFree,MintPaysAssembly}.lean`
  — new, 428/1348/699/543/659 lines, 32/68/37/14/19 declarations. The tail, through the
  engine-level assembly `mintPaysForTimeFixed_of_not_dense`.
- Sixteen declarations de-privatized in place before any extraction: `pickOrd`, `pick_ord_eq`,
  `pickBranches`, `pick_branches_eq`, `pick_stage_source`, `pickOrd_mono`, `mfp`, `mfq`, `fwp`,
  `rm_bn`, `pickBranches_time_dichotomy`, `mwE`, `mwG`, `mwP`, `mwQ`,
  `pickBranches_knownTimes_subset`. `private` count 92 -> 76, and by no more.
- Seven docstrings added (`mfp`, `mfq`, `fwp`, `mwE`, `mwG`, `mwP`, `mwQ`) — see Decisions.
- Five prose repairs in docstrings, all same-line so no line number shifted during extraction:
  three stale `MintBound.lean:NNN` self-citations replaced by the declaration names they meant,
  one `Task 433` citation replaced by `PostBlockingSettlesRun`, and the register header's
  "Twenty-four statements" corrected to "Twenty-five" (the register carries 25 numbered entries).
  Three further same-line repairs replaced cross-module deictics with the module names they now
  point at.
- `.../Termination/MintBound/README.md` — new. 18-row module table, the import DAG with its
  parallel branches, and the convention distinguishing the register from the in-place refutations
  that live modules state and prove.
- `.../Termination/README.md` — the `MintBound.lean` row (stale at 14,770 against an actual
  15,684) rewritten for the aggregator, plus a `## MintBound/` section.
- `README.md`, `FormalSystem/Metalogic/README.md` — generated inventory blocks regenerated.

## Decisions

- **De-privatization was done first, in the unsplit file, with its own build gate.** That makes it
  the only semantic change in the task, so every later build failure would have been unambiguously
  an extraction error. It also avoided reproducing the `pick_split'` failure mode — duplicating a
  declaration rather than widening its visibility — which this file already pays for once.
- **The cut is at existing `/-!` section boundaries in file order.** File order was verified to be
  an acyclic dependency order by a static import-closure check (added beyond the plan) that found
  zero cross-module references outside the referencing module's import closure, before any build.
- **`docBlame`'s 7 new findings were fixed, not grandfathered.** De-privatizing seven witness atoms
  exposed them to a linter that does not see `private` declarations. `runLinter --update` would
  have silently grandfathered a real regression; each got a one-line docstring instead.
- **The C9 register's content was not touched.** Only the header's demonstrably wrong count was
  corrected. No entry was altered, condensed, or dropped.

## Plan Deviations

- **Phase 1** altered: the plan's "five `attribute [local simp]` blocks" measured as three
  (`:4696`, `:5870`, `:11471`); all three sit inside contained sections, so the conclusion holds.
- **Phase 2** altered: the plan's build-guard argument vector
  (`lake-build-guard.sh build ... -- FormalSystem`) is rejected by the guard, which requires a
  recognized lake subcommand first after `--` and exits 77 without building. Corrected to
  `-- build FormalSystem`, with the exit code captured directly rather than through a pipe that
  would mask it. A first attempt did mask it and reported a false pass.
- **Phase 3** altered: three checks were added beyond the plan's (a)/(b)/(c) — an import-closure
  check, a line-multiset provenance audit, and an axiom-set diff. Prose hygiene not in the plan
  was also required: three `MintBound.lean:NNN` self-citations would have gone out of range once
  the aggregator shrank to 121 lines, failing invariant C20 tier 1 (gated, repo-wide).
- **Phase 5** altered: three module docstrings opened on a deictic with no referent after the cut
  ("Phase 1's gate above", "The subsection above", "nothing below it is assumed anywhere above")
  and were repaired to name the module. Body-level "above"/"below" deictics that now cross a
  module boundary were deliberately NOT swept — see Follow-ups.
- **Phase 7** altered: run after Phase 6 rather than overlapped with Phase 4. There is no second
  agent here, so the overlap bought nothing, and deferring guaranteed every path the READMEs cite
  already resolved.
- **Phase 8** altered, twice. `lake exe checkInitImports` does flag `Register.lean`, contrary to
  the plan — but it already flagged `Fuel.lean`, `TimeTypeBound.lean`, `SubformulaProperty.lean`
  and the pre-split `MintBound.lean`, so all 18 modules inherit the status structurally and no new
  kind of violation appears (total 435 -> 453; the executable is not wired into CI or the
  invariant gate). And the aggregator is 121 lines, not the asserted "under 100": the 18-entry
  `## Submodules` map plus the A/B/C/D overview does not fit, and the overview is the file's
  orientation.

## Verification

- Build: Success. `lake build FormalSystem` green at all six gates (Phases 2, 3, 4, 5, 6, 8), each
  run detached through `lake-build-guard.sh`. Final gate: 2,610 jobs, exit 0.
- Sorry count: 0 (`lean-sorry-census.sh` on `Termination/`; C3 confirms zero structural sorries
  across `FormalSystem/`).
- Vacuous count: 0.
- Axiom count: unchanged. No `axiom` declaration added; the 41-row `#print axioms` record captured
  at the Phase 2 gate is byte-identical at every later gate. C2 confirms all four flagship axiom
  sets match their recorded baseline.
- `scripts/check-module-invariants.sh`: **exit 0** — every gated invariant passes, including C1,
  C2, C3, C4, C5, C6, C8, C9, C12, C13, C14, C15, C16, C18, C19, C20, C21, C22, C23 and INV. Two
  of these (INV and C9) were FAILING before this task began and are now green.
- Declaration-name set: 751 names, all unique, byte-identical to the pre-split baseline.
- Cross-boundary `private` use: empty. Missing-import violations: 0.
- Provenance audit: exactly 26 pre-split lines are absent from the split tree — 18 promoted module
  headings, 6 sub-headings promoted inside those same docstrings, and 2 aggregator-docstring lines
  deliberately rewritten. Every declaration and every proof line is accounted for.
- `FormalSystem/Metalogic/Decidability.lean`: zero-line diff across the whole task.
- Files verified: Yes.

## Impacts

- The file is reviewable. Largest module is `MintPotential.lean` at 1,828 lines, against 15,684
  before; the median module is ~770 lines.
- A reader can now tell locally whether they are reading a live result or a refuted approach:
  `Register.lean` is the only module with zero declarations and holds the whole register.
  `MintBound/README.md` records that live modules also state in-place refutations, and why those
  are load-bearing rather than register material.
- Sixteen declarations are now public. Nothing outside `MintBound/` consumes them today, but
  `Fuel.lean`'s `pick_split'` / `pick_splitOrdered'` duplicates are now removable — deliberately
  left alone, as a separate decision.
- The public interface is unchanged: the aggregator re-exports everything, so no downstream
  importer was edited.

## Follow-ups

- Body-level "above"/"below" deictics inside module bodies that now cross a module boundary were
  not swept. Only the five Phase 5 module docstrings were checked and repaired. A sweep across all
  18 modules is a legibility follow-up, not a correctness one.
- `Fuel.lean`'s `pick_split'` and `pick_splitOrdered'` duplicate now-public declarations and could
  be retired. Explicitly a Non-Goal here.
- `specs/ROADMAP.md` references `MintBound.lean` at lines 148, 158, 296, 327 and 339, including a
  claim that the C9 register carries "24 entries". It carries 25, and the register now lives in
  `MintBound/Register.lean`. ROADMAP.md was consulted read-only and not modified, since
  `roadmap_flag` was not set on this dispatch.
- `lake exe checkInitImports` reports 453 modules that do not transitively import
  `FormalSystem.Init`, `Fuel.lean` and the whole `Termination/` directory among them. Long
  standing, ungated, and untouched here.

## References

- `specs/550_decompose_mintbound_for_publication_legibility/plans/01_decompose-mintbound-publication-legibility.md`
- `specs/550_decompose_mintbound_for_publication_legibility/reports/01_decompose-mintbound-publication-legibility.md`
- `specs/550_decompose_mintbound_for_publication_legibility/handoffs/` — per-phase handoffs
- `docs/development/MODULE_INVARIANTS.md` — the invariant set the final gate runs
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound/README.md`
