# Implementation Summary: Task #554

- **Task**: 554 - Retire the nine vacuous `_run` theorems in `MintBound.lean`, land the two un-`At` widening lemmas, and amend C9 register entries 24/25 for the corrected count
- **Status**: [COMPLETED]
- **Started**: 2026-09-07
- **Completed**: 2026-09-07
- **Effort**: ~4 hours
- **Dependencies**: None outstanding (463 complete, 549 complete)
- **Artifacts**: plans/01_retire-vacuous-run-theorems.md, summaries/01_retire-vacuous-run-theorems-summary.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Nine `buildTableauAt_isSome_*_run` theorems in `MintBound.lean` read as headline results — the
tableau construction succeeds — while establishing nothing, because each carried a hypothesis the
same file refutes. All nine are deleted and replaced by a single named retirement record, in the
house pattern `Correctness.lean:192-234` already uses for its own retired pair and ADR-007
sanctions. The two already-proved un-`At` widening lemmas are landed, six collateral prose sites
are repaired, and three C9 register entries are amended for the corrected count of nine and the
frame-class split.

## What Changed

`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — the sole file modified
(15,759 -> 15,684 lines; 371 lines changed, 156 insertions against 231 deletions):

- **Landed two theorems**, transplanted from `specs/549_.../probes/Widen.lean` rather than
  re-derived: `one_le_mintAwareFuel` (beside `one_le_mintAwareFuelAt`) and
  `postBlockingSettlesRun_mintAwareFuel_false` (beside `postBlockingSettlesRun_terminusFuel_false`).
  The prime was dropped from the first — the un-`At` figure is the primary one, so a primed name
  read backwards — and `FrameClass.Base` was written fully qualified as
  `FormalSystem.ProofSystem.FrameClass.Base`, since this file opens only `FormalSystem.Syntax`.
  Both are kernel-checked at `[propext, Classical.choice, Quot.sound]` (the first needs only
  `[propext, Quot.sound]`).
- **Retired the nine**, deleting one contiguous 202-line span (the block prose plus all nine
  declarations) and installing a 58-line retirement record in its place. The record names all nine
  so they stay greppable in-file, gives the refutation that reaches each, states the frame-class
  split unflattened, enumerates the keep set, and records the zero-dependent removal cost.
- **Repaired six collateral prose sites** — three of which no prior artifact enumerated — plus
  orphan-consumer notes on `buildTableauAt_isSome_of_settlesRun` (4 consumers -> 0) and
  `postBlockingSettlesRun_of_postBlockingSettles` (1 -> 0), both deliberately kept.
- **Amended C9 register entries 23, 24 and 25**, including both of the dispatch's named amendments.

## Decisions

- **Delete the theorem, keep the record.** The dispatch offered a retire-vs-annotate binary; the
  plan's research found a third disposition already sanctioned twice in this repository. It
  dominates both options, so no `user_decision` was raised.
- **The count correction is larger than the dispatch stated, and in a second dimension.** The nine
  split four/four/one by fuel figure, not six-at-`mintAwareFuelAt`. Four of them
  (`_of_budget_run`, `_at_seed_run`, `_of_budget_at_run`, `_at_seed_at_run`) were stated at the
  un-`At` `mintAwareFuel`, for which the file carried no refutation at all before this task. The
  Phase 2 lemmas are therefore load-bearing rather than tidying: without them the vacuity claim
  reached only half the retired set. Recorded in entry 24 and entry 25's amendment (a).
- **The frame-class split is genuinely non-uniform.** `postBlockingSettlesRun_false_dense` /
  `_rtime` are stated at every positive fuel, so `.Dense`/`.RTime` vacuity covers both figures for
  the eight; `postBlockingSettles_fuel_zero_false` is universally quantified in the frame class, so
  `buildTableauAt_isSome_of_budget_of_run` alone is unconditionally vacuous at all four. Stated
  that way in the record, in site D, and in entry 25's amendment (b).

## Plan Deviations

- **Phase 5 count gate altered.** The plan's gate (``\bnine\b`` hits confined to three regions) is
  not runnable: the file carries roughly thirty pre-existing unrelated uses of "nine" (nine rules,
  nine mint sites, nine `hlab` carriers). The runnable substitute used instead is
  ``grep 'five `_run`'`` returning empty plus a diff read-through. No unrelated "nine" site was
  edited, and none of the six false-positive sites the plan fenced was touched.
- **Phase 4 exit gate altered.** The plan required every surviving nine-name hit to sit inside the
  retirement record. Two deliberate hits sit outside it — site E's docstring and entry 25's
  amendment (b) — each naming a retired theorem *as retired* and pointing at the record, which
  satisfies the gate's intent that no prose name a retired theorem as live.
- **Plan's build command corrected.** It reads `lake-build-guard.sh build ... -- lake build`, which
  the guard rejects (exit 77, unrecognized lake subcommand `lake`). The correct form is `-- build`.
- **Net line delta** is -141 for the deletion and -75 overall, against the plan's ~-165 estimate.
  The difference is the prose *added* by Phases 4 and 5, not a span-boundary divergence: the removed
  span was 202 lines and contained all nine declarations and nothing after them, confirmed by the
  post-deletion grep.
- **Phase 3 was applied twice.** A concurrent session on another task ran a destructive git
  operation (`git reset --hard` plus `git clean -fd`) against the shared working tree, discarding
  the uncommitted Phase 3 deletion and, later, the untracked summary and handoff files. The source
  work was re-applied from the same anchored scripts and committed immediately; both source commits
  survive in history and the final state was verified from scratch. See Follow-ups.

## Verification

- Build: Success — full `lake build`, 2592 jobs, exit 0, zero errors, the same job count as the
  pre-edit baseline. Run detached through `lake-build-guard.sh` with `--no-share`, so the result is
  a genuine build and not a replayed one.
- Sorry count: 0 outside `FormalSystem/Boneyard/` (160 total, all Boneyard) — unchanged from
  baseline. No `sorry` was introduced.
- Vacuous count: 0 in this task's edits. The repo-wide grep reports one pre-existing hit,
  `FormalSystem/Examples/TemporalStructures.lean:496` (`int_domain_universal ... := trivial`),
  which predates this task (task 523) and lies outside its single modified file.
- Axiom count: 0 real `axiom` declarations outside `Boneyard/` — the eight `^axiom ` grep hits are
  docstring prose lines that begin mid-sentence with the word. The 41 `#print axioms` obligations
  `MainResults.lean` emits are byte-identical to the pre-edit baseline (`diff` reports no change),
  so `#print axioms` is unchanged for every surviving `Decidability` result.
- Regression check: `probes/DepTrace2.lean` still reports
  `constants from MintBound reached by decide: 0`. Per the dispatch, `probes/RevDep.lean` was
  deliberately not run as a gate — it reports 0 trivially once the names stop resolving.
- Gates: the nine-name grep returns only prose naming them as retired; ``grep 'five `_run`'``
  returns empty; all nine keep-set names still `#check` clean.
- Tests: N/A — no test changes; `Tests/BimodalTest/` builds as part of the full build.
- Files verified: Yes

## Impacts

- Nine declarations leave the library's public surface. No consumer is affected: the task 549
  whole-environment reverse-dependency scan found zero dependents outside the nine themselves, and
  `FormalSystem.Metalogic.Decidability.decide` reaches zero constants from this file.
- `buildTableauAt_isSome_of_settlesRun` and `postBlockingSettlesRun_of_postBlockingSettles` are now
  consumer-free. Both are deliberately retained — C9 entry 23 names them — and each now carries a
  note saying its consumers were the retired termini.
- `buildTableauAt_isSome_of_budget_fixed_seedRun` is now the only terminus in the file stated at a
  narrowed post-blocking residual, which its docstring records.
- The register's vacuity claim now covers both fuel figures rather than only the `At` one.

## Follow-ups

- **Concurrent-session hazard worth acting on.** Another orchestrated session running against this
  same working tree ran `git reset --hard` and `git clean -fd`, twice destroying this task's
  uncommitted and untracked work. Nothing was permanently lost here, but multi-task orchestration
  on a shared tree has no protection against this today.
- The `.Dense` and `.RTime` refutations at the un-`At` figure are each a four-line composition and
  were left undone as out of scope; the `.Base` refutation already decides the predicate.
- Widening the seed narrowing to the rest of the family now means restating landed termini rather
  than repairing surviving ones — site E's docstring records this so the deferral is not misread.
- `MintBound.lean` remains a 15,684-line single file; decomposition is a separate task.

## References

- `specs/554_retire_nine_vacuous_run_theorems/plans/01_retire-vacuous-run-theorems.md`
- `specs/554_retire_nine_vacuous_run_theorems/reports/01_retire-nine-vacuous-run-theorems.md`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean`, `probes/DepTrace2.lean`
