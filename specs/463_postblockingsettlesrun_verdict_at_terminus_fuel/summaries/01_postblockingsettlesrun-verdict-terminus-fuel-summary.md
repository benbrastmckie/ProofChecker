# Implementation Summary: Task #463

- **Task**: 463 - Decide `PostBlockingSettlesRun fc (mintAwareFuelAt U.card Tmax mintBudget D β)` at the terminus's own fuel figure
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T14:47:05-07:00
- **Completed**: 2026-09-07T16:25:00-07:00
- **Effort**: ~1.6 hours wall (dominated by build serialization against concurrent full `lake build`s, not by proof work)
- **Dependencies**: 462 — `file_scope` serialization on `MintBound.lean` only; no mathematical dependency, and none was needed
- **Artifacts**: plans/01_postblockingsettlesrun-verdict-terminus-fuel.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The refute-first gate this task exists to run returned a binary verdict, and the verdict is
**FALSE**. `PostBlockingSettlesRun fc fuel` is refuted at every `fuel ≥ 1`, hence at the terminus's
own figure `mintAwareFuelAt U.card Tmax mintBudget D β` for **all** parameter values, at
`FrameClass.Base`, `.Dense` and `.RTime`. The refutation is a kernel proof — sorry-free, axiom-free
beyond `propext`/`Classical.choice`/`Quot.sound`, additive only, full `lake build` green.

This is a first-class deliverable, not a shortfall. The dispatch asked for a decision in either
direction and got one: `postBlockingSettlesRun_terminusFuel_false` is literally the negation of the
`hpb` hypothesis carried by the repaired terminus `buildTableauAt_isSome_of_budget_fixed_run` under
`fc := .Base`. The terminus and its five `_run` siblings are therefore **vacuous** at those three
frame classes — not merely unproved. Nothing is withdrawn; the minimal further narrowing that closes
this refutation is landed and named (`PostBlockingSettlesSeedRun`), carried as a hypothesis and
explicitly **not** claimed true.

## What Changed

All work is additive, in one file:
`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`.

**The witness and its five obligations** (Phase 2), in the existing `PostBlockingSettlesRefutation`
section:

- `pbrWitnessBranch`, `pbrWitnessOrd`, `pbrDoctoredTracker` — three `private def`s. The branch is
  29 formulas: the engine's own verbatim open exit from `seedBranch (p → q)` at `.Base` (11
  formulas, chain `2 < 0 < 1 < 3`), plus an 18-formula augmentation supplying world-1 machinery, the
  two `negPos` conclusions that exit left outstanding, and the witness `T(p untl q)@⟨9,4⟩`. The
  tracker parks one `q`-eventuality at world 7, time 0.
- `pbrWitness_findClosure_none` — the branch is open at every frame class (`cases fc <;> rfl`).
- `pbrWitness_expandOnceNoFresh_saturated` — the label-free pass reports `.saturated` (`rfl`).
- `pbrWitness_saturateBlocked_self` — the post-blocking pass hands the branch back at **every**
  fuel, via the existing `saturateBlocked_eq_self_of_noFresh_saturated`, reused verbatim.
- `pbrWitness_expandBranchWithFuel_eq` — the doctored run returns the witness open at every positive
  fuel (`rw [expandBranchWithFuel]; norm_num; rfl`).
- `pbrWitness_settlement_fails` — landed in the **sharper** `= some (T(p untl q)@⟨9,4⟩)` form the
  plan flagged as a strengthening of its pinned `≠ none` statement.

**The verdict** (Phase 3):

- `postBlockingSettlesRun_false_succ_of` — a `private` assembly lemma taking the three
  class-specific `rfl` facts as hypotheses, so the argument is stated once rather than three times.
- `postBlockingSettlesRun_false_succ` — `¬ PostBlockingSettlesRun .Base (n + 1)`.
- `one_le_mintAwareFuelAt` — the fuel figure is always at least one, unconditionally, off
  `mintPathBound`'s trailing `+ 1` through `fuelFigure_pos`.
- `postBlockingSettlesRun_terminusFuel_false` — **the dispatch's literal question, answered**:
  `¬ PostBlockingSettlesRun .Base (mintAwareFuelAt U.card Tmax mintBudget D β)`, for every `U`,
  `Tmax`, `mintBudget`, `D`, `β`.

**The frame-class record** (Phase 4): six further obligations plus
`postBlockingSettlesRun_false_dense` and `postBlockingSettlesRun_false_rtime`, and a prose note
scoping `.ZTime` explicitly.

**The named narrowing** (Phase 5): `PostBlockingSettlesSeedRun` (a public `def`),
`postBlockingSettlesSeedRun_of_postBlockingSettlesRun` (the direction lemma),
`buildTableauAt_isSome_of_settlesSeedRun` (the bridge, which typechecked verbatim — the phase's
pre-declared fallback was **not** needed), and `buildTableauAt_isSome_of_budget_fixed_seedRun` (the
representative terminus restated).

**The register and its amendments** (Phase 6): C9 register entry 25, plus in-place corrections to
three prose sites that this task made false — entry 24's "nothing in this file decides it in either
direction" clause, the `PostBlockingSettlesRun` docstring, and the non-vacuity subsection's "What
the probe did not find" paragraph. No statement or proof term was edited.

## Decisions

- **The defect is a *second* over-quantification, in a different argument than task 433 repaired.**
  Task 433 narrowed `(ob, oOrd, fuel)` to run-produced pairs but left `expandBranchWithFuel`'s
  `EventualityTracker` argument universally quantified. That argument is the only input the engine's
  blocked-set computation and the settlement test's recomputed `armTracker` do not share, and
  blocking is monotone in pending entries at the ancestor, so a doctored tracker yields a strictly
  larger blocked set: the engine skips a time the settlement test still inspects.
- **Stated as a fact about the predicate, not softened to a caveat.** No engine run threads this
  tracker, and it does not need to: the predicate as written quantifies over it, so the predicate as
  written is false — the same form of statement register entry 22 makes about the `fuel = 0`
  degeneracy. The finding is that the narrowing was incomplete, and the completion is named.
- **Kernel proof, not `#guard_msgs` measurement.** The doctored run returns the witness at its
  *first* step, so one `rw` through the equation lemma reaches the `.saturated` arm. This is
  precisely the cost entry 24 records as prohibitive in the positive direction, and it does not
  apply in the negative one. Entry 25 records the technique as reusable.
- **`PostBlockingSettlesSeedRun` is carried, never discharged.** Its docstring and entry 25 both
  carry the second, structurally independent and **unprobed** refutation route against it
  (`saturateBlocked` may extend `ob`, and `expandOnceNoFresh` ignores blocking, so it can unblock a
  time carrying work it itself skips), together with the cheapest probe for that route.
- **Assembly factored rather than triplicated** (`postBlockingSettlesRun_false_succ_of`), so the
  `.Dense` and `.RTime` verdicts differ from `.Base` only in their three `rfl` inputs.

## Plan Deviations

- **Phase 2, "Build after each obligation lands; commit each green obligation"** altered: one module
  build and one commit for the phase. Another session was running concurrent full `lake build`s that
  repeatedly invalidated the dependency oleans (`SubformulaProperty`, `TimeTypeBound`, `Fuel`),
  making each build cost 5-25 minutes rather than seconds. All five obligations were verified
  together by the single green module build.
- **Phase 3, "Land `postBlockingSettlesRun_false_succ`"** altered: the assembly is factored through
  a new `private theorem postBlockingSettlesRun_false_succ_of` so Phase 4 reuses it.
- **Phase 3 / Phase 5, "Commit each green theorem/declaration"** altered: phases 4, 5 and 6 were
  landed as one declared atomic batch, verified by a single green module build and one commit, for
  the same build-cost reason.
- **Phase 4, the optional `.ZTime` strengthening** skipped: it is explicitly plan-optional with a
  20-minute time-box, and each in-file build cost 20-25 minutes under the concurrent-build load. The
  scoped `.ZTime` note was landed instead, naming `priorUZ`/`priorSZ` and the four labels so the
  measurement is re-runnable. Refuting at one frame class already refutes the predicate.
- **Phase 6 Scope Hypothesis corrected**: it asserted four amendment sites; there are **three**. The
  `:12155` section preamble carries no openness claim about `PostBlockingSettlesRun`, so there was
  nothing to amend there. The grep confirmed it, and all three real sites were amended.
- **Phase 5's pre-declared fallback was not needed** — the bridge typechecked verbatim, so the
  terminus restatement landed rather than being deferred to entry 25 as an open item.
- **Phase 2's readability aside**: the three witness `def`s inline their formula shapes
  (`Formula.imp .bot .bot` etc.) rather than introducing new abbreviations, keeping the phase at
  exactly the three `private def`s the plan names and reusing the file's existing `mfp`/`mfq`.

## Verification

- **Build**: Success — full `lake build`, 2592 jobs, zero errors, no new warnings. Each phase was
  additionally gated by a green `lake build` of the module itself. Every build ran detached via
  `Bash(run_in_background: true)` through `.claude/scripts/lake-build-guard.sh`.
- **Sorry count**: 0. The single `+sorry` token in the diff is the phrase "no `sorry`" inside C9
  entry 25's prose; there is no proof placeholder.
- **Vacuous count**: 0 attributable to this task. The repo-wide scan's one hit,
  `FormalSystem/Examples/TemporalStructures.lean:496`, is pre-existing, semantically genuine, and
  outside this task's two-file diff.
- **Axiom count**: 0 new `axiom` declarations. `#print axioms` on all 19 new declarations reports
  nothing beyond `propext`, `Classical.choice`, `Quot.sound` — six of them need only `propext`.
- **Phase 1 gate**: PASS. The research witness reproduced against the current tree with zero errors
  and `#print axioms` = `[propext, Classical.choice, Quot.sound]` before anything was transcribed.
- **Additive only**: `git diff` over the three task commits shows `MintBound.lean` and the plan file
  as the only files changed, 560 insertions. No declaration was withdrawn; the Phase 6 edits are
  docstring and module-comment prose only.
- **`PostBlockingRunProbe` `#guard_msgs` block**: still passes unchanged — a `#guard_msgs` mismatch
  is a build error, and the module built green.
- **Frozen files — a finding, recorded rather than glossed**: `Fuel.lean` is byte-identical to its
  Phase 1 baseline. `Saturation.lean` and `Tableau.lean` are **not**: their md5s moved from
  `c65e8389…`/`3125482505…` to `4519852f…`/`494d9c3e…`. This task did not touch them. The drift is
  commit `5167fd5d3` ("task 531 phase 2: convert prose citations to bib keys"), which landed
  concurrently and changed exactly one module-docstring bibliography line in each file
  (`* Gore, R. (1999). …` → `* [gore1999]`). No declaration, definition or proof term moved, so the
  public interface this task consumed is unchanged and the frozen-file contract is substantively
  intact.
- **Plan compliance**: all 14 committed identifiers from the plan's Goals list are present in
  `MintBound.lean`.
- **Tests**: N/A (no test-suite change; the library build covers `Tests/` through `lake build`).
- **Files verified**: Yes.

## Impacts

- **The repaired terminus is now known to rest on a false hypothesis at three frame classes.**
  `buildTableauAt_isSome_of_budget_fixed_run` and its five `_run` siblings are vacuous at `.Base`,
  `.Dense` and `.RTime`. They are retained verbatim, but no reader should take them as delivering
  `buildTableauAt … .isSome` there.
- **A non-vacuous replacement chain exists.** `buildTableauAt_isSome_of_budget_fixed_seedRun` is the
  representative terminus at `PostBlockingSettlesSeedRun`, reached through
  `buildTableauAt_isSome_of_settlesSeedRun`, with the fuel expression reused byte for byte.
- **Register entry 24 is corrected rather than superseded**, and entry 25 closes the positive
  direction at any positive figure, so a future dispatch will not re-attempt it.
- **A reusable technique is recorded**: a kernel refutation about a well-founded-recursive engine
  function is cheap exactly when the witness is returned before the first recursive call, even where
  a kernel proof about the same function is prohibitive.

## Follow-ups

- **`PostBlockingSettlesSeedRun` is undecided and must not be assumed true.** The unprobed second
  refutation route is recorded verbatim in its docstring and in entry 25, with the cheapest probe
  named: for engine exits `ob`, does `blockedTimes satBr satOrd fc (armTracker satBr)` ever lose a
  time that `blockedTimes ob oOrd fc (armTracker ob)` held?
- **`.ZTime` is uncovered by this witness** — `priorUZ`/`priorSZ` stay applicable at `⟨0,0⟩`,
  `⟨0,1⟩`, `⟨1,0⟩`, `⟨1,1⟩`. Completing it is mechanical and buys record tidiness only.
- **Widening the seed-run restatement to the remaining five `_run` termini** was deliberately
  deferred; one representative was landed.

## References

- `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/plans/01_postblockingsettlesrun-verdict-terminus-fuel.md`
- `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_postblockingsettlesrun-verdict-terminus-fuel.md`
- `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_verified-refutation-witness.lean`
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — C9 register entry 25
- `specs/433_discharge_postblockingsettles_residual/plans/01_postblockingsettles-refute-or-prove.md` — the stylistic precedent for a refute-first binary gate
