# Implementation Plan: Decide `PostBlockingSettlesRun` at the terminus's own fuel figure

- **Task**: 463 - Decide `PostBlockingSettlesRun fc (mintAwareFuelAt U.card Tmax mintBudget D β)` at the terminus's own fuel figure
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours
- **Dependencies**: 462 — `file_scope` SERIALIZATION edge only (both tasks edit `MintBound.lean`). No mathematical dependency; nothing below reads the minting measure.
- **Research Inputs**: `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_postblockingsettlesrun-verdict-terminus-fuel.md`
- **Artifacts**: plans/01_postblockingsettlesrun-verdict-terminus-fuel.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

The refute-first gate this task exists to run has **already returned a verdict, and it is FALSE**:
research found and machine-checked (sorry-free, axiom-free, against the built `MintBound.olean`) a
refutation of `PostBlockingSettlesRun fc fuel` at every `fuel ≥ 1`, hence at the terminus's own
figure `mintAwareFuelAt U.card Tmax mintBudget D β` for all parameter values. This plan therefore
does **not** re-run the search; it (1) re-confirms the verdict against the current tree as a hard
gate, (2) transcribes the verified witness and its five obligations into `MintBound.lean`, (3) lands
the terminus-fuel instantiation that answers the dispatch's literal question, (4) states the vacuity
consequence for the six `_run` termini, (5) names — as a carried hypothesis, never a discharge — the
minimal further narrowing `PostBlockingSettlesSeedRun`, and (6) records C9 register entry 25 and
amends entry 24, whose current text ("nothing in this file decides it in either direction") this
task makes false.

Work is **additive only** in `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`.
Nothing is withdrawn. `Saturation.lean`, `Tableau.lean` and `Fuel.lean` are md5-pinned FROZEN and
are read through their public interface only. Definition of done: `lake build` green, zero `sorry`,
`#print axioms` on every new theorem reporting no axiom beyond `propext, Classical.choice,
Quot.sound`, and the C9 register truthful about what was and was not decided.

### Research Integration

Five findings from `reports/01_postblockingsettlesrun-verdict-terminus-fuel.md` drive the structure
below and were re-grounded against the tree during planning:

1. **The defect is a *second* over-quantification, in a different argument than task 433 repaired.**
   Task 433 narrowed `(ob, oOrd, fuel)` to run-produced pairs but left `expandBranchWithFuel`'s
   `EventualityTracker` argument `tr` universally quantified (`MintBound.lean:11961`, confirmed:
   the binder list is `∀ (b ob) (ord oOrd) (tr) (ap oAp) (mb bu) (satBr satOrd)`). The tracker is
   the **only** input the engine's blocked-set computation and the settlement test's recomputed
   `armTracker` (`Saturation.lean:711`) do not share, and blocking is monotone in pending entries
   at the ancestor, so a doctored `tr` yields a strictly larger blocked set than `armTracker` — the
   engine skips a time the settlement test still inspects.
2. **The refutation is cheap at the kernel, not a `#guard_msgs` measurement.** The witness is
   returned at the *first* step, so `rw [expandBranchWithFuel]; norm_num; rfl` unfolds the equation
   lemma **once** and the `.saturated` arm closes it. This is exactly the cost register entry 24
   records as prohibitive for the *positive* direction, and it does not apply here. This is the
   single most important fact in the report: it converts what entry 24 calls a measurement into a
   theorem.
3. **`saturateBlocked` cannot repair it at any fuel.** `expandOnceNoFresh` (`Tableau.lean:2335`)
   skips label-minting candidates, so the existing
   `saturateBlocked_eq_self_of_noFresh_saturated` (`MintBound.lean:11653`, signature confirmed:
   `(hcl : findClosure b fc = none) (hsat : expandOnceNoFresh b ord fc = (.saturated, ord')) (fuel)`)
   hands the branch back at **every** fuel. Reused verbatim, not rebuilt.
4. **The fuel figure is always positive.** `mintPathBound` ends `+ 1` (`MintBound.lean:4976`,
   confirmed), so `1 ≤ mintPathBoundAt` (`:9858`) by `omega`, and `fuelFigure_pos` (`:3688`,
   `{D β N} (hN : 1 ≤ N) : 1 ≤ fuelFigure D β N`) lifts it to `mintAwareFuelAt` (`:9864`)
   unconditionally. That is what carries the `n+1` refutation to the terminus's own figure.
5. **The narrowing that closes this refutation is named but NOT claimed true.** Fixing the four
   arguments `buildTableauAt` always supplies at defaults (`tr := .empty`, `ap := {}`, `bu := 0`,
   `ord := .empty`) kills this witness (checked: at `tr := .empty` the same branch's
   `expandOnceUnblocked` is `.extended`, not `.saturated`). The report also names a **second,
   structurally independent and unprobed** refutation route against that narrowing (the
   "`saturateBlocked` extends `ob` and thereby unblocks a time" route). Both facts must land
   together; the second is what keeps this from being a weakening dressed as a repair.

### Prior Plan Reference

No prior plan for this task. The stylistic precedent consumed is
`specs/433_discharge_postblockingsettles_residual/plans/01_postblockingsettles-refute-or-prove.md`
— a refute-first binary gate on the *unnarrowed* predicate. Two calibration lessons taken from it:
its 13-hour actual for a gate that had to *find* its witness, versus this task's 9.5-hour estimate
for a gate whose witness is already verified; and its practice of stating the direction lemma
explicitly alongside every narrowing (`postBlockingSettlesRun_of_postBlockingSettles`,
`MintBound.lean:12220`), which Phase 5 reproduces. No phase is copied from it.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied in this dispatch's delegation context (`roadmap_path` absent,
`roadmap_flag` not set), so no roadmap consultation was performed and no roadmap phases are added.

## Goals & Non-Goals

**Goals** (the committed identifier set; see `## Lean Challenge Statements` for exact signatures):

- `pbrWitness_findClosure_none`
- `pbrWitness_expandOnceNoFresh_saturated`
- `pbrWitness_saturateBlocked_self`
- `pbrWitness_expandBranchWithFuel_eq`
- `pbrWitness_settlement_fails`
- `postBlockingSettlesRun_false_succ`
- `one_le_mintAwareFuelAt`
- `postBlockingSettlesRun_terminusFuel_false`
- `postBlockingSettlesRun_false_dense`
- `postBlockingSettlesRun_false_rtime`
- `PostBlockingSettlesSeedRun`
- `postBlockingSettlesSeedRun_of_postBlockingSettlesRun`
- `buildTableauAt_isSome_of_settlesSeedRun`
- `buildTableauAt_isSome_of_budget_fixed_seedRun`

**Non-Goals**:

- **Refuting at `.ZTime`.** Refuting at one frame class already refutes the predicate; `.ZTime`
  completes the *record*, not the verdict. Research measured `priorUZ`/`priorSZ` still applicable on
  the witness at `⟨0,0⟩ ⟨0,1⟩ ⟨1,0⟩ ⟨1,1⟩` at that class. Phase 4 may add it opportunistically as a
  plan-unanticipated strengthening (flagged in the summary); its absence is not a shortfall.
- **Proving `PostBlockingSettlesSeedRun`.** It is landed as a carried hypothesis with its bridge and
  direction lemma, and the C9 entry must say in terms that it is *not* shown true — the report names
  an independent unprobed refutation route against it.
- **Restating all six `_run` termini at `PostBlockingSettlesSeedRun`.** One representative
  (`buildTableauAt_isSome_of_budget_fixed_seedRun`, off `buildTableauAt_isSome_of_budget_fixed_run`
  at `:12438`) is landed. Widening to the family is deliberately deferred.
- **Withdrawing anything.** `PostBlockingSettles`, `PostBlockingSettlesAt`,
  `PostBlockingSettlesRun`, and every landed terminus are retained verbatim.
- **Any edit outside `MintBound.lean`.**

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Research's witness no longer reproduces against the current tree (e.g. task 462 landed and perturbed something) | H | L | Phase 1 is a hard gate: reproduce the scratch file *before* transcribing. Failure re-opens the gate rather than being worked around. Baseline md5s recorded in Phase 1 so a frozen-file drift is distinguishable from a `MintBound.lean` drift. |
| A 29-formula `rfl` is slow or blows a heartbeat/maxRecDepth inside the real file (scratch-file timings need not transfer) | M | M | Measured well under existing per-declaration cost at three classes. Escalation ladder, in order: `decide` on the Bool-valued halves; `set_option maxRecDepth`; shrink the witness's `S` component (nothing in the argument needs `F(p → q)`'s propositional residue — it is inherited for authenticity, not necessity). |
| `mfp`/`mfq` are `private` (`MintBound.lean:4634-4635`) and the witness is placed outside their visibility | L | L | Placement is inside the same file and namespace, in the existing `PostBlockingSettlesRefutation` section, where `multBranch`/`multSettledBranch` already name them. |
| Phase 5's bridge `buildTableauAt_isSome_of_settlesSeedRun` does not typecheck verbatim | M | L | Report checked that `buildTableauAt` supplies exactly the four defaults the narrowing fixes. Fallback if it does not: land the `def` and the direction lemma only, skip the terminus restatement, and record the failure in entry 25 as a named open item — do **not** loosen the narrowing to make a bridge appear. |
| The refutation is dismissed as "a tracker no engine threads" | H | M | State it the way entry 22 states the `fuel = 0` degeneracy: the predicate **as written** quantifies over `tr`, so the predicate as written is false. The finding is that task 433's narrowing was incomplete, and the completion is named. Phase 6 must not soften this to a caveat. |
| Overclaiming that `PostBlockingSettlesSeedRun` is true | H | M | Phase 6 gate: entry 25 must carry the unprobed second refutation route verbatim, and name the cheapest probe for it (does `blockedTimes satBr satOrd fc (armTracker satBr)` ever lose a time that `blockedTimes ob oOrd fc (armTracker ob)` held?). A Phase 6 checklist item fails the phase if that paragraph is absent. |
| Serialization collision with task 462 on `MintBound.lean` | M | M | Both tasks are additive and in different sections. Phase 1 records `git log -1` on the file; Phase 7 re-checks it and rebases the additions rather than the reverse if 462 landed mid-flight. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4, 5 | 3 |
| 5 | 6 | 4, 5 |
| 6 | 7 | 6 |

Phases within the same wave can execute in parallel. Phases 4 and 5 are the only genuinely
independent pair (both depend on 3 alone and touch disjoint declarations), but they must still be
run one at a time: every phase writes to the single file `MintBound.lean`, so the `file_scope`
serialization that makes 462 a dependency applies internally as well. Execute this plan
sequentially, 1 through 7.

---

### Phase 1: Reproduce the verdict — the refute-first gate, re-run [COMPLETED]

**Goal**: Confirm, against the tree as it stands right now, that the research's witness still
refutes `PostBlockingSettlesRun FrameClass.Base (n+1)` sorry-free and axiom-free. Nothing is
transcribed until this passes.

**Tasks**:
- [x] Record the baseline: `md5sum` on the three frozen files, and `git log -1 --oneline` on
      `MintBound.lean`. Expected frozen baselines as of planning:
      `Saturation.lean = c65e8389dfd8dac422e1af3f981fb5bc`,
      `Tableau.lean = 3125482505a8cea20f9ab3e288747adf`,
      `Fuel.lean = d24100ffd267563995913ed633b04d12`.
      *(completed: all three md5s match the planning baselines byte for byte;
      `git log -1 --oneline` on `MintBound.lean` = `79bd1794f`, and the file is clean in the
      working tree.)*
- [ ] Write the report's Appendix source verbatim to a scratch file outside the library tree
      (use the session scratchpad, not `FormalSystem/`).
- [ ] `lake build FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound` to ensure the
      `.olean` the scratch file imports is current.
- [ ] `lake env lean <scratch>` — expect zero errors, zero warnings about `sorry`.
- [ ] `#print axioms Probe463.postBlockingSettlesRun_false_Base` — expect exactly
      `[propext, Classical.choice, Quot.sound]`.
- [ ] **GATE, binary and recorded**: PASS -> verdict is FALSE, proceed to Phase 2. FAIL -> stop,
      do not transcribe; record which of the five obligations broke and what the tree changed,
      and re-open the gate as a `[BLOCKED]` phase with that evidence. A failure here is a real
      outcome, not an error to route around.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- None in the repository. Scratch file only.

**Verification**:
- Scratch file elaborates with zero errors under `lake env lean`.
- `#print axioms` output matches exactly.
- The three frozen md5s are unchanged from the baselines above; if any differs, that is itself
  the gate's finding and must be recorded before proceeding.

---

### Phase 2: Land the witness data and its five obligations at `.Base` [COMPLETED]

**Goal**: Transcribe the verified witness into the existing `PostBlockingSettlesRefutation` section
of `MintBound.lean` as private data plus five named, individually-provable obligations.

**Tasks**:
- [x] Add three `private def`s beside the existing witness data in the
      `PostBlockingSettlesRefutation` section (after the non-vacuity subsection at `:12479`, before
      `section PostBlockingRunProbe` at `:12521`): `pbrWitnessBranch` (the 29-formula `AUG ++ S`),
      `pbrWitnessOrd` (`{ constraints := [(3,4),(1,3),(2,0),(0,1)] }`, chain `2<0<1<3<4`), and
      `pbrDoctoredTracker` (`{ pending := [{ formula := mfq, label := ⟨7,0⟩, isUntil := true }] }`).
      Reuse the file's existing `mfp`/`mfq` (`:4634-4635`) rather than introducing new atoms.
- [x] Each def carries a docstring stating *why* its shape is load-bearing: `S` is the verbatim open
      exit the engine produces from `seedBranch (p → q)` (authenticity — the ancestor times are
      engine-saturated, not hand-asserted); `AUG` supplies world-1 machinery, the two `negPos`
      conclusions the exit left outstanding, and the witness `T(p untl q)@⟨9,4⟩`; the doctored entry
      is parked at an unused world so `fulfillEventualities` (`Saturation.lean:308`) never discharges
      it.
- [x] Land `pbrWitness_findClosure_none` (`cases fc <;> rfl`).
- [x] Land `pbrWitness_expandOnceNoFresh_saturated` at `.Base` (`rfl`).
- [x] Land `pbrWitness_saturateBlocked_self` via
      `saturateBlocked_eq_self_of_noFresh_saturated` applied to the previous two — universal in
      `fuel`, no induction.
- [x] Land `pbrWitness_expandBranchWithFuel_eq` (`rw [expandBranchWithFuel]; norm_num; rfl`). Its
      docstring MUST record that this is a **one-step** unfold reaching the `.saturated` arm
      immediately, and that this is precisely why the refutation is a kernel proof where entry 24
      records the positive direction as prohibitive.
- [x] Land `pbrWitness_settlement_fails` (`rfl`) — the settlement test reports
      `T(p untl q)@⟨9,4⟩` outstanding.
- [x] Build after each obligation lands; commit each green obligation. *(deviation: altered — one module build and one commit for the whole phase, not one per obligation: another session was running concurrent full `lake build`s that repeatedly invalidated the dependency oleans, making each build cost 5-25 minutes rather than seconds. All five obligations were verified together by the single green `lake build` of the module.)*

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: The witness is asserted to be 29 formulas (`AUG` 18 + `S` 11) with a
5-element ordering, and all five obligations are asserted to close by `rfl` (one by a single `rw`)
at `.Base`. Confirm at implementation time by (a) `#eval pbrWitnessBranch.length` reporting 29 and
(b) each obligation elaborating with the stated tactic and no fallback from the Risks ladder — if a
fallback is used, say which and why in the summary rather than silently substituting a tactic.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — additive: three
  `private def`s and five theorems inside `section PostBlockingSettlesRefutation`.

**Verification**:
- `lake build FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound` green.
- No `sorry`; each new theorem passes `#print axioms` with no axiom beyond the three standard ones.
- No existing declaration edited or removed (`git diff` shows additions only in this phase).

---

### Phase 3: The refutation, and the verdict at the terminus's own fuel figure [COMPLETED]

**Goal**: Assemble the obligations into `¬ PostBlockingSettlesRun .Base (n+1)`, prove the fuel
figure is always positive, and land the theorem that answers the dispatch's literal question.

**Tasks**:
- [x] Land `postBlockingSettlesRun_false_succ`: instantiate the hypothesis at the witness *(deviation: altered — the assembly is factored through a new `private theorem postBlockingSettlesRun_false_succ_of`, which takes the three class-specific `rfl` facts as hypotheses, so Phase 4's `.Dense`/`.RTime` verdicts reuse it instead of triplicating the argument.)*
      (`h W W ordW ordW trBad {} {} 100 0 W ordW`), rewrite by `pbrWitness_settlement_fails`,
      close by `absurd _ (by simp)`.
- [x] Land `one_le_mintAwareFuelAt`: `1 ≤ mintPathBoundAt Ucard Tmax mintBudget` by
      `simp only [mintPathBoundAt, mintPathBound]; omega` (the `+ 1` at the end of `mintPathBound`,
      `:4976`), then `fuelFigure_pos`.
- [x] Land `postBlockingSettlesRun_terminusFuel_false`, stated with `(U : Finset SignedFormula)` and
      `U.card` so it reads literally as the terminus's own hypothesis. Convert the figure to
      successor form via `Nat.exists_eq_succ_of_ne_zero` (or `Nat.succ_pred_eq_of_pos`) off
      `one_le_mintAwareFuelAt`, then apply `postBlockingSettlesRun_false_succ`.
- [x] Docstring on `postBlockingSettlesRun_terminusFuel_false` states the consequence in one
      sentence and without hedging: `buildTableauAt_isSome_of_budget_fixed_run` (`:12438`) and its
      five `_run` siblings carry a hypothesis that is **false** at `.Base` — they are vacuous there,
      not merely unproved. This is the analogue of `postBlockingExitSettled_false` and sits beside
      it in spirit.
- [x] Commit each green theorem. *(deviation: altered — one commit for the phase, one module build; see the Phase 2 note on concurrent-build cost.)*

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — additive: three
  theorems.

**Verification**:
- `lake build ...MintBound` green; `#print axioms postBlockingSettlesRun_terminusFuel_false` reports
  no axiom beyond `propext, Classical.choice, Quot.sound`.
- The statement of `postBlockingSettlesRun_terminusFuel_false` is syntactically the negation of the
  `hpb` hypothesis of `buildTableauAt_isSome_of_budget_fixed_run` under `fc := .Base` — check by
  reading the two side by side, not by assertion.

---

### Phase 4: Extend to `.Dense` and `.RTime`; record `.ZTime` as a scoped sub-case [IN PROGRESS]

**Goal**: Complete the frame-class record for the classes research verified, and record `.ZTime`
honestly rather than leaving it implicit.

**Tasks**:
- [ ] Land `postBlockingSettlesRun_false_dense` and `postBlockingSettlesRun_false_rtime` by
      re-running the Phase 2 obligations at those classes (research verified both
      `expandOnceUnblocked` and `expandOnceNoFresh` close by `rfl` there) and reassembling.
- [ ] Add a short prose note in the section recording that `.ZTime` is **not** covered by this
      witness, naming the measured reason: `priorUZ`/`priorSZ` remain applicable to
      `T(⊤ untl ⊤)` / `T(⊤ snce ⊤)` at `⟨0,0⟩ ⟨0,1⟩ ⟨1,0⟩ ⟨1,1⟩`. State plainly that this is
      completeness of the record, not of the verdict — the predicate is already refuted.
- [ ] **Optional, opportunistic**: if adding those two rules' conclusions to `pbrWitnessBranch`
      leaves the three verified classes' `rfl`s intact and closes `.ZTime` too, land
      `postBlockingSettlesRun_false_ztime` as well. This is a plan-unanticipated strengthening and
      MUST be flagged as such in the implementation summary. Time-box it to 20 minutes; if the
      augmentation perturbs any of the three verified classes, revert it and keep the scoped note.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: Asserts that the Phase 2 obligations close by the same tactics at exactly two
further frame classes (`.Dense`, `.RTime`) and not at `.ZTime`. Confirm by elaborating each; if
`.ZTime` unexpectedly closes without augmentation, say so — that contradicts the report's
measurement and is worth recording.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — additive: two (or
  three) theorems plus a prose note.

**Verification**:
- `lake build ...MintBound` green.
- The `.ZTime` note names the two rule identifiers and the four labels, so a future reader can
  re-run the measurement without re-deriving it.

---

### Phase 5: Name the minimal further narrowing — carried, not discharged [NOT STARTED]

**Goal**: Land `PostBlockingSettlesSeedRun`, its direction lemma, its bridge, and one restated
terminus, so the repaired chain is non-vacuous again — while stating in the same breath that the
narrowing is **not** shown true.

**Tasks**:
- [ ] Land `def PostBlockingSettlesSeedRun`: `PostBlockingSettlesRun` with the four arguments
      `buildTableauAt` always supplies at defaults fixed — `ord := TimeOrdering.empty`,
      `tr := EventualityTracker.empty`, `ap := {}`, `bu := 0` — leaving `b`, `ob`, `oOrd`, `oAp`,
      `mb`, `satBr`, `satOrd` quantified.
- [ ] Docstring MUST carry three things, in this order: (i) what it fixes and why exactly those four
      (the consuming site instantiates them, so quantifying over them was over-quantification, not
      generality); (ii) that it kills the Phase 2 witness, with the checked reason — at
      `tr := .empty` the same branch's `expandOnceUnblocked` is `.extended`, not `.saturated`;
      (iii) that this is **not** a proof of the narrowing, naming the independent unprobed
      refutation route (`saturateBlocked` may extend `ob`, and `expandOnceNoFresh` ignores blocking
      entirely, so it can do label-free work at a blocked time and thereby *unblock* a time carrying
      label-minting work it itself skips).
- [ ] Land `postBlockingSettlesSeedRun_of_postBlockingSettlesRun` — the direction lemma, in the
      same idiom as `postBlockingSettlesRun_of_postBlockingSettles` (`:12220`): the seed form is the
      **weaker** predicate, so every theorem restated against it is a strengthening.
- [ ] Land `buildTableauAt_isSome_of_settlesSeedRun` by copying the proof skeleton of
      `buildTableauAt_isSome_of_settlesRun` (`:12197`) with the narrowed hypothesis. Research
      checked this survives verbatim because `buildTableauAt` passes exactly those defaults.
- [ ] Land `buildTableauAt_isSome_of_budget_fixed_seedRun` — `buildTableauAt_isSome_of_budget_fixed_run`
      (`:12438`) with `hpb` at the seed-run predicate; the fuel expression is reused byte for byte.
- [ ] **Fallback, pre-declared**: if the bridge does not typecheck, land the `def` and the direction
      lemma only, skip the terminus restatement, and carry the failure into entry 25 as a named open
      item. Do NOT loosen the narrowing until a bridge appears — that is the exact failure mode
      register entry 23 exists to prevent.
- [ ] Commit each green declaration.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — additive: one `def`
  and three theorems.

**Verification**:
- Full `lake build` green (this phase adds a public `def` that downstream may resolve against, so
  the module-only build is not sufficient).
- `buildTableauAt_isSome_of_budget_fixed_seedRun` elaborates with no `sorry` and its hypothesis list
  differs from its `_run` original in exactly one entry.
- The `PostBlockingSettlesSeedRun` docstring contains all three required elements; absent any one,
  the phase is not complete.

---

### Phase 6: C9 register entry 25, and the amendments task 463 makes necessary [NOT STARTED]

**Goal**: Record the verdict in the do-not-re-attempt register, and correct every place in the file
that currently asserts the question is open — those statements become false with Phase 3.

**Tasks**:
- [ ] Add **C9 register entry 25** after entry 24 (`:15224`), in the register's established voice:
      the verdict (FALSE, machine-checked, at `.Base`/`.Dense`/`.RTime` and at the terminus's own
      figure for all parameters); the mechanism (the tracker argument was the surviving
      over-quantification; blocking is monotone in pending entries at the ancestor, so a doctored
      `tr` gives a strictly larger blocked set than the settlement test's `armTracker`); what it
      does **not** say (it is not a claim that the engine ever threads such a tracker — the
      predicate as written quantifies over it, so the predicate as written is false, exactly as
      entry 22's `fuel = 0` degeneracy is stated); the named next narrowing
      `PostBlockingSettlesSeedRun` **with** the unprobed second refutation route and the cheapest
      probe for it; and the do-not-re-attempt instruction (do not re-attempt the unnarrowed forms,
      the output-branch bridge, or an `ArmSettlement` discharge).
- [ ] **Amend entry 24 in place.** Its current text — "whether it holds at the terminus's own fuel
      figure is open; nothing in this file decides it in either direction" — is made false by Phase
      3. Rewrite that clause to point at entry 25 and at
      `postBlockingSettlesRun_terminusFuel_false`. Preserve the rest of entry 24 (its non-vacuity
      and probe-reach paragraphs remain accurate).
- [ ] **Amend the `PostBlockingSettlesRun` docstring** (`:11961` region): the clause "Whether the
      predicate holds at the terminus's fuel figure is open; nothing here decides it in either
      direction, and it is a hypothesis everywhere it appears" is now false. Replace with the
      verdict and a pointer to `postBlockingSettlesRun_terminusFuel_false`.
- [ ] **Amend the non-vacuity subsection** (`:12479` region), whose "What the probe did not find"
      paragraph reads as evidence toward truth. Add, without deleting the existing honest text, that
      the residual is now **refuted** and that the probe's non-finding was a fact about the probe's
      reach — precisely as that paragraph itself warned.
- [ ] Sweep the section preamble at `:12155` for any further "nothing here decides it" language and
      amend it the same way.
- [ ] Grep the whole file for residual claims of openness about `PostBlockingSettlesRun` before
      declaring the phase done.

**Timing**: 1.5 hours

**Depends on**: 4, 5

**Verification Tier**: local

**Scope Hypothesis**: Asserts exactly four amendment sites (entry 24, the `PostBlockingSettlesRun`
docstring, the non-vacuity subsection, the section preamble) plus one new entry. Confirm at
implementation time with `grep -n "in either direction\|is open\|not yet decided" MintBound.lean`
scoped to the `PostBlockingSettlesRefutation` section and the C9 register; if the grep finds a fifth
site, amend it and say so — the list here is a hypothesis, not a boundary.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — new C9 entry 25;
  in-place prose amendments to four sites. These are Lean docstrings and module comments, which
  elaborate, so this is not a `prose`-tier edit.

**Verification**:
- `lake build ...MintBound` green (docstring edits can break elaboration).
- Entry 25 contains the unprobed-second-route paragraph and the cheapest-probe sentence. **If that
  paragraph is absent the phase fails**, regardless of everything else being present.
- Grep confirms no surviving "nothing decides it in either direction" claim about
  `PostBlockingSettlesRun`.

---

### Phase 7: Final gate and handoff [NOT STARTED]

**Goal**: Run the complete gate set, confirm the frozen-file and additive-only contracts held, and
hand off with the verdict stated plainly.

**Tasks**:
- [ ] Full `lake build` from a clean-enough state; zero errors, zero warnings introduced.
- [ ] `grep -rn "sorry" MintBound.lean` scoped to the diff — zero new occurrences.
- [ ] `#print axioms` on every new theorem in the Goals list; each reports no axiom beyond
      `propext, Classical.choice, Quot.sound`.
- [ ] Re-`md5sum` the three frozen files against the Phase 1 baselines — must be byte-identical.
- [ ] `git diff --stat` confirms `MintBound.lean` is the only file changed, and `git diff` confirms
      no existing declaration was withdrawn (docstring amendments in Phase 6 are the only in-place
      edits, and they touch no statement or proof term).
- [ ] Re-check `git log -1` on `MintBound.lean` against the Phase 1 record; if task 462 landed
      mid-flight, rebase these additions onto it rather than the reverse.
- [ ] Write the summary stating the binary verdict FALSE as a **first-class deliverable**, not as a
      shortfall: what was proved, at which frame classes, what `.ZTime` status is, what the named
      next narrowing is, and what remains unprobed about it.

**Timing**: 1 hour

**Depends on**: 6

**Verification Tier**: full

**Files to modify**:
- None (verification and summary only).

**Verification**:
- Full `lake build` green.
- All three frozen md5s unchanged.
- Summary names the verdict and does not describe it as a failure.

---

## Lean Challenge Statements

```lean
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound

namespace FormalSystem.Metalogic.Decidability

open FormalSystem.Syntax FormalSystem.ProofSystem

/-- Placeholder witness data; the real definitions land in Phase 2. -/
private def pbrWitnessBranch : Branch := []
private def pbrWitnessOrd : TimeOrdering := TimeOrdering.empty
private def pbrDoctoredTracker : EventualityTracker := EventualityTracker.empty

theorem pbrWitness_findClosure_none (fc : FrameClass) :
    findClosure pbrWitnessBranch fc = none := sorry

theorem pbrWitness_expandOnceNoFresh_saturated :
    expandOnceNoFresh pbrWitnessBranch pbrWitnessOrd FrameClass.Base
      = (ExpansionResult.saturated, pbrWitnessOrd) := sorry

theorem pbrWitness_saturateBlocked_self (fuel : Nat) :
    saturateBlocked pbrWitnessBranch fuel pbrWitnessOrd FrameClass.Base
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd)) := sorry

theorem pbrWitness_expandBranchWithFuel_eq (n : Nat) :
    expandBranchWithFuel pbrWitnessBranch (n + 1) pbrWitnessOrd FrameClass.Base
        pbrDoctoredTracker {} 100 0
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd, {})) := sorry

theorem pbrWitness_settlement_fails :
    findUnexpandedUnblockedWith pbrWitnessBranch pbrWitnessOrd FrameClass.Base
        (blockedTimes pbrWitnessBranch pbrWitnessOrd FrameClass.Base
          (armTracker pbrWitnessBranch))
      ≠ none := sorry

theorem postBlockingSettlesRun_false_succ (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base (n + 1) := sorry

theorem one_le_mintAwareFuelAt (Ucard Tmax mintBudget D β : Nat) :
    1 ≤ mintAwareFuelAt Ucard Tmax mintBudget D β := sorry

theorem postBlockingSettlesRun_terminusFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base
        (mintAwareFuelAt U.card Tmax mintBudget D β) := sorry

theorem postBlockingSettlesRun_false_dense (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Dense (n + 1) := sorry

theorem postBlockingSettlesRun_false_rtime (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.RTime (n + 1) := sorry

/-- The named minimal further narrowing: the residual with the four arguments `buildTableauAt`
always supplies at their defaults fixed. Carried as a hypothesis, never discharged. -/
def PostBlockingSettlesSeedRun (fc : FrameClass) (fuel : Nat) : Prop :=
  ∀ (b ob : Branch) (oOrd : TimeOrdering) (oAp : AppliedSet) (mb : Nat)
    (satBr : Branch) (satOrd : TimeOrdering),
    expandBranchWithFuel b fuel TimeOrdering.empty fc EventualityTracker.empty {} mb 0
      = some (.inr (ob, oOrd, oAp)) →
    saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) →
    findUnexpandedUnblockedWith satBr satOrd fc
      (blockedTimes satBr satOrd fc (armTracker satBr)) = none

theorem postBlockingSettlesSeedRun_of_postBlockingSettlesRun
    {fc : FrameClass} {fuel : Nat} (h : PostBlockingSettlesRun fc fuel) :
    PostBlockingSettlesSeedRun fc fuel := sorry

theorem buildTableauAt_isSome_of_settlesSeedRun {phi : Formula} {fuel : Nat}
    {fc : FrameClass} {maxBranches : Nat}
    (hpb : PostBlockingSettlesSeedRun fc fuel)
    (hexp : (expandBranchWithFuel [SignedFormula.neg phi Label.initial] fuel TimeOrdering.empty fc
      (maxBranches := maxBranches)).isSome = true) :
    (buildTableauAt phi fuel fc maxBranches).isSome = true := sorry

theorem buildTableauAt_isSome_of_budget_fixed_seedRun
    {fc : FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U Tmax) (harm : ArmSettlement fc)
    (hpb : PostBlockingSettlesSeedRun fc (mintAwareFuelAt U.card Tmax mintBudget D β))
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget D β) fc maxBranches).isSome
      = true := sorry

end FormalSystem.Metalogic.Decidability
```

Two authoring notes on the block above, so the implementer is not misled by it:

- `pbrWitness_settlement_fails` is pinned in the weaker `≠ none` form here because the exact
  witness formula reported (`SignedFormula.pos (Formula.untl mfp mfq) ⟨9,4⟩`) is what makes the
  refutation *readable*, and Phase 2 should land the sharper `= some ...` equality. Landing the
  equality is a strengthening of the pinned statement, not a deviation.
- The three `private def` placeholders exist only so the block type-checks standalone. Their real
  bodies land in Phase 2 and are not pinned here.

## Testing & Validation

- [ ] Full `lake build` green with zero new warnings.
- [ ] Zero `sorry` in the diff.
- [ ] `#print axioms` on all fourteen committed identifiers reports nothing beyond
      `propext, Classical.choice, Quot.sound`.
- [ ] The three frozen files (`Saturation.lean`, `Tableau.lean`, `Fuel.lean`) are byte-identical to
      their Phase 1 md5 baselines.
- [ ] `git diff` shows `MintBound.lean` as the only changed file, with no declaration withdrawn.
- [ ] The existing `PostBlockingRunProbe` `#guard_msgs` block still passes unchanged — the
      refutation must not perturb the measurements entry 24 rests on.
- [ ] C9 entry 25 exists, entry 24's "in either direction" clause is amended, and no surviving
      claim of openness about `PostBlockingSettlesRun` remains in the file.

## Artifacts & Outputs

- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — additive: three
  private witness `def`s, one public `def` (`PostBlockingSettlesSeedRun`), thirteen theorems, C9
  register entry 25, and four in-place docstring/prose amendments.
- `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/summaries/01_*-summary.md` — the
  implementation summary, stating the binary verdict FALSE as a first-class deliverable.
- No new file is created in the library tree; the Phase 1 scratch file is not committed.

## Rollback/Contingency

Every phase is a self-contained additive block committed on green, so rollback is
`git revert` of the offending phase commit — no phase depends on a *partial* predecessor, only on a
complete one.

- **Phase 1 gate FAILS** (witness no longer reproduces): stop. Do not transcribe, do not repair the
  witness opportunistically. Record which obligation broke and what changed in the tree, mark the
  phase `[BLOCKED]`, and return the re-opened gate as the outcome. The verdict then genuinely is
  "undecided by the means available", and the dispatch explicitly requires saying so with evidence
  rather than guessing.
- **A `rfl` proves too expensive in-file**: walk the Risks-table escalation ladder in order
  (`decide` on Bool halves -> `maxRecDepth` -> shrink `S`). If none works, land the obligations at
  the shrunk witness and record the change; do not fall back to `#guard_msgs` measurement, since a
  kernel proof is the entire qualitative gain over entry 24.
- **Phase 5's bridge fails**: land the `def` and direction lemma only (pre-declared fallback in that
  phase), and record it in entry 25. Phases 1-4 and 6 stand on their own; the verdict does not
  depend on Phase 5.
- **Task 462 lands mid-flight and conflicts**: both tasks are additive and sit in different sections
  of the file; rebase these additions onto 462's, re-run the Phase 7 gate, and never resolve a
  conflict by discarding 462's work.
