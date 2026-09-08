# Implementation Plan: Task #554

- **Task**: 554 - Retire the nine vacuous `_run` theorems in `MintBound.lean`, land the two un-`At` widening lemmas, and amend C9 register entries 24/25 for the corrected count
- **Status**: [COMPLETED]
- **Effort**: 5 hours
- **Dependencies**: None outstanding (463 complete, 549 complete)
- **Research Inputs**: `specs/554_retire_nine_vacuous_run_theorems/reports/01_retire-nine-vacuous-run-theorems.md`
- **Artifacts**: plans/01_retire-vacuous-run-theorems.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Nine `buildTableauAt_isSome_*_run` theorems in `MintBound.lean` read as headline results while
establishing nothing — each carries a hypothesis refuted elsewhere in the same file. A prior
dependency trace machine-verified zero reverse-dependents anywhere in the environment, making
removal cost-free. This plan retires all nine and replaces them with a named retirement record
following this repository's own established house pattern, lands the two already-proved un-`At`
widening lemmas that close the register's vacuity claim over the un-`At` fuel figure, repairs six
collateral prose sites (three of which no prior artifact enumerates), and amends the C9 register
for the corrected count of nine and the row-2 frame-class split. Done means: the nine no longer
resolve as declarations, a green full build, no `sorry`, no axiom additions, and the dependency
probe still reporting zero constants from this file reached by the decision procedure.

### Research Integration

The research report drove five plan decisions that would otherwise have been guessed:

1. **Delete span verified at HEAD.** One contiguous region `MintBound.lean:12288-12487`, the nine
   at `12312, 12331, 12347, 12369, 12386, 12407, 12425, 12449, 12468`. Re-confirmed live during
   planning: the file is still 15,759 lines and every declaration line still holds, though HEAD has
   since moved to `a3996b32e`. **The names, not the numbers, are the anchor** — the prior trace
   found research line numbers stale once already.
2. **A third disposition dominates the dispatch's retire-vs-annotate binary.** Research located an
   in-repo precedent: `Correctness.lean:192-234` carries a "Retired as vacuous" prose record where
   two deleted theorems stood, a shape sanctioned by `ADR-007-Decidability-One-Directional.md:51-53`
   with the discipline that the record lives once and everything else points at it. Delete the
   *theorem*, keep the *record*. This satisfies the publication criterion the dispatch names while
   satisfying the register's own stated principle that the sequence of findings stay legible. Both
   dispatch options are dominated, so no `user_decision` is raised — the codebase has already
   answered this question, twice.
3. **The amend set is six sites, not one.** The 549 summary names one rewrite site (`:5194-5195`).
   Research found five more. Site E (`:12939`) is the highest-risk: it sits inside a *surviving*
   keep-set theorem's docstring and becomes flatly false on deletion. Phase 4 exists solely because
   this inventory is larger than the dispatch implies.
4. **Verbatim paste of the widening lemmas will not compile, and may fail silently.**
   `MintBound.lean` opens only `FormalSystem.Syntax`, never `FormalSystem.ProofSystem`;
   `probes/Widen.lean` opens the latter and writes bare `FrameClass.Base`. The file already carries
   a comment at `:12980-12982` recording exactly this bug class biting once before, silently rather
   than as a compile error. Phase 2 mandates the qualified form.
5. **There is a second, unrelated "nine" in this file.** `:14282` and C9 entry 21 at `:15388` both
   say "the nine `hlab` carriers" — a disjoint set, entirely out of scope. Any count-correction
   pass driven by grepping for "nine" will hit them. Phase 5 fences them explicitly.

### Prior Plan Reference

No prior plan. This is round 1 for task 554.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only (no `roadmap_path` or `roadmap_flag` was passed; this is
alignment context only, and ROADMAP.md is not modified by this plan). The relevant item is the
**Tombstoned Routes** section at `ROADMAP.md:322-328`, which names the C9 register inside
`MintBound.lean` as the authoritative itemised list of refuted routes and records its size as "24
entries as of 2026-08-25". This task amends entries 23, 24 and 25 of exactly that register. The
work sits under Phase 2 (Decidability and the Tableau Engine), which at `ROADMAP.md:148` points
readers at the C9 register as the record of what the termination front has and has not delivered —
so correcting a nine-way undercount there improves the accuracy of a surface the roadmap actively
directs readers to. No roadmap checkbox is completed by this task; it is a correctness repair to a
referenced artifact, not the discharge of a roadmap deliverable.

## Goals & Non-Goals

**Goals**:

- Remove the nine vacuous restated termini from the library's public surface, replacing them with a
  single retirement record that keeps all nine names greppable in-file.
- Land `one_le_mintAwareFuel` in `MintBound.lean`.
- Land `postBlockingSettlesRun_mintAwareFuel_false` in `MintBound.lean`.
- Leave no prose anywhere in the file that names a retired theorem as live, forward-references the
  deleted block, or repeats the six-count undercount.
- Amend C9 entries 23, 24 and 25 so the register states the corrected count of nine, records the
  widened vacuity claim over both fuel figures, and splits out the row that is unconditionally
  vacuous at all four frame classes.
- Finish with a green full build, zero `sorry`, zero axiom additions, and an unchanged
  `#print axioms` for every surviving Decidability result.

**Non-Goals**:

- The `.ZTime` strengthening. Its only justification was the DEPENDS-at-`.ZTime` branch, which the
  trace ruled out. Explicitly out of scope by dispatch mandate.
- `docs/theorem-index.md:113`. Confirmed correct on a ten-of-ten column check; the NO-DEPENDENCY
  branch mandates leaving it alone.
- Any decomposition of `MintBound.lean`. That is a separate task.
- The `.Dense` and `.RTime` refutations at the un-`At` fuel figure. Each is a four-line composition
  and each is scope creep against a dispatch that names exactly two lemmas. Named here only so a
  reader does not mistake their absence for an oversight.
- The nine unrelated `hlab` carriers at `:14282` and C9 entry 21 (`:15388`), and the false-positive
  count sites at `:15316`, `:15350`, `:14286`, `:15391`.
- C9 entry 22, which concerns the unrestricted predicate as literally stated and is untouched by
  anything here.
- Adding a retiring-vacuous-theorems context file to the source store. Research recommends it; it
  belongs in a separate meta task, not here.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Line numbers drift between plan and execution (already happened once on this file's trace) | M | M | Every site below is given by **name and quoted text**, not only by number. Re-locate by the quoted string; treat every line number as a hint. Phase 1 re-confirms the anchor set before any edit. |
| Site E (`:12939`) missed, leaving a false sentence inside a surviving theorem's docstring | H | M | Called out as the single highest-risk omission. Phase 4 carries a mechanical `grep` exit gate that catches it; Phase 6 re-runs the same gate independently. |
| Widening lemma paste resolves `FrameClass.Base` to a different namespace **silently** | H | M | Phase 2 mandates the fully qualified `FormalSystem.ProofSystem.FrameClass.Base`, matching sibling `postBlockingSettlesRun_terminusFuel_false` exactly. The file records this exact failure at `:12980-12982` as having been silent, not a compile error. |
| Count-correction pass edits the unrelated nine `hlab` carriers | M | M | Fenced in Non-Goals and repeated as a Phase 5 exclusion list with all six false-positive sites named. |
| Foreground `lake build` livelocks the implementation | H | H if attempted | Every build in this plan is detached + guarded per `.claude/context/project/lean4/operations/long-builds.md`. This is mandatory, not advisory, on this repository. |
| `probes/RevDep.lean` re-run read as a regression failure | L | H | It will `logError` on unresolved names once the nine are gone. **That failure is the expected outcome.** `probes/DepTrace2.lean` is the meaningful check. Stated in Phase 6 so the implementer does not chase it. |
| Retirement record drifts into re-proving or re-deriving content | M | L | The record is prose only. Phase 3's tier is `interface` precisely because its sole compile-surface effect is symbol removal. |
| Concurrent write collision on `MintBound.lean` | L | L | Verified at planning time: 463 and 549 are complete; task 547 is `implementing` with a 21-path `file_scope` that does not include this file. Phase 1 re-checks `git status` before editing. |
| A `sorry` appears during implementation | H | Very L | There is no open proof obligation anywhere in scope — the two lemmas are already kernel-checked at `[propext, Classical.choice, Quot.sound]`. A `sorry` would indicate work outside scope, most likely the excluded `.ZTime` strengthening. Correct response: stop and re-read Non-Goals, never defer the `sorry`. |

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

Phases within the same wave can execute in parallel. **Every wave here holds exactly one phase**:
all six phases write to the same 15,759-line file, so there is no parallel dispatch available
regardless of logical independence. Phases 4 and 5 are logically independent of one another but are
serialized by that shared-file constraint. This table is deliberately degenerate, not accidentally
so.

---

### Phase 1: Baseline capture and regression anchors [COMPLETED]

**Goal**: Establish that the tree is green and the probe baseline holds *before* any edit, and
re-confirm every anchor this plan depends on, so a later failure is attributable to this task's
edits rather than to inherited state.

**Tasks**:
- [ ] `git status --short` — confirm `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` is unmodified and no concurrent session holds it.
- [ ] Launch the baseline full build **detached and guarded**, under `Bash(run_in_background: true)`:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build`.
      Do the anchor confirmations below while it runs; do not block on it.
- [ ] Confirm the nine declarations resolve **by name** with `grep -n "^theorem buildTableauAt_isSome.*_run\b"`. Expect exactly nine hits.
- [ ] Confirm the delete span's boundaries by quoted text, not number: it opens at the section
      comment `/-! #### The termini, restated at the narrowed residual` and closes on the last proof
      line before the blank pair preceding `/-! #### Non-vacuity of the narrowed residual`.
- [ ] Record the full pre-edit reference inventory: `grep -n` for all nine names across the file, and
      `grep -n "five \`_run\`"`, `grep -n "\bnine\b"`. Save the counts; Phase 6 diffs against them.
- [ ] Confirm the two landing sites for Phase 2 exist by name: `one_le_mintAwareFuelAt` and
      `postBlockingSettlesRun_terminusFuel_false`.
- [ ] When the detached build reports, confirm green. Then run
      `lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace2.lean`
      and record that it prints `constants from MintBound reached by decide: 0`.
- [ ] Commit nothing — this phase writes no source. Record findings in the progress file.

**Timing**: 0.75 hours (mostly wall-clock on the detached build; agent-active time ~15 minutes)

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: This plan asserts nine theorems in one contiguous 200-line span, six
collateral prose sites, and two lemmas to land. Confirm at implementation time by the `grep -n`
inventory above: exactly nine `^theorem buildTableauAt_isSome.*_run` hits, and the six prose sites
of Phase 4 each located by their quoted text. If the count is not nine, or a quoted string does not
match, **stop and report** rather than proceeding on the number in this plan — the file has changed
under the research.

**Files to modify**:
- None. Read-only baseline.

**Verification**:
- Detached guarded `lake build` exits green.
- `DepTrace2.lean` prints `constants from MintBound reached by decide: 0`.
- Exactly nine `_run` theorem declarations found by name.

---

### Phase 2: Land the two un-`At` widening lemmas [COMPLETED]

**Goal**: Close the register's vacuity claim over the un-`At` `mintAwareFuel` figure, not only
`mintAwareFuelAt`, by transplanting two already-proved lemmas from the probe file into
`MintBound.lean` beside their `At`-siblings.

**Tasks**:
- [ ] Insert `one_le_mintAwareFuel` immediately after `one_le_mintAwareFuelAt`. Transplant the body
      from `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean` verbatim;
      do **not** re-derive the proof.
- [ ] **Drop the prime.** The probe calls it `one_le_mintAwareFuel'`, but a primed name conventionally
      marks a *variant of* an unprimed original, and here the un-`At` figure is the primary one —
      the prime reads backwards. Research verified no `one_le_mintAwareFuel` exists in
      `FormalSystem/` to collide with, and zero references to the primed name exist outside the
      probe file, so the rename is free.
- [ ] Insert `postBlockingSettlesRun_mintAwareFuel_false` immediately after
      `postBlockingSettlesRun_terminusFuel_false`, updating its internal call from
      `one_le_mintAwareFuel'` to `one_le_mintAwareFuel`.
- [ ] **Qualify the frame class.** Write `FormalSystem.ProofSystem.FrameClass.Base`, not bare
      `FrameClass.Base`. This file opens only `FormalSystem.Syntax`; the probe opens
      `FormalSystem.ProofSystem` and the bare form does not mean here what it means there. Match
      sibling `postBlockingSettlesRun_terminusFuel_false`'s spelling exactly. Prior silent instance
      of this bug class recorded in-file at `:12980-12982`.
- [ ] Give each a one-line docstring in the file's house style, naming it as the un-`At` counterpart
      of its sibling.
- [ ] Scoped build, detached and guarded:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound`
- [ ] Commit on green.

**Timing**: 0.75 hours (agent-active ~20 minutes; remainder is scoped-build wall clock)

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: Exactly two lemmas are asserted to need landing, both already proved. Confirm
at implementation time by reading `probes/Widen.lean` and checking it declares exactly these two
theorems; if it carries more, the extra ones are out of scope by the dispatch's "two lemmas"
wording and must not be landed without saying so.

Justification: both edits are purely additive declarations inside one module. No existing signature
changes, so nothing outside the module can break. The tier's blind spot — behavior visible to other
modules through unchanged signatures — cannot apply to a declaration that did not previously exist.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` - add two theorems beside their `At`-siblings

**Verification**:
- Scoped module build green.
- Both new names resolve; neither is primed.
- `grep -n "FrameClass.Base" ` on the new lemma shows the fully qualified form.
- No `sorry`, no `axiom` introduced.

---

### Phase 3: Retire the nine and install the retirement record [COMPLETED]

**Goal**: Delete the nine vacuous theorems and the block prose that introduces them, and put a
named retirement record in their place — following `Correctness.lean:192-234` and the ADR-007
discipline that the record lives once with pointers rather than copies elsewhere.

**Tasks**:
- [ ] Delete the contiguous span: the block prose section comment through the last proof line of
      `buildTableauAt_isSome_at_seed_fixed_run`. Re-locate by the quoted anchors from Phase 1, not
      by line number. Collapse the surrounding double blank lines to a single blank-line pair.
- [ ] Write the retirement record in its place, headed
      `/-! #### The termini restated at the narrowed residual — retired as vacuous`. Five parts, in
      this order (per the `Correctness.lean` precedent):
      1. **What stood here** — all nine names in full, so they stay greppable in-file and a reader
         arriving from `git log` or an external citation finds them. External artifacts under
         `specs/433_*`, `specs/463_*` and `specs/549_*` all cite them by name.
      2. **Why they were vacuous** — each carried a hypothesis refuted at the fuel figure it was
         stated at, naming `postBlockingSettlesRun_terminusFuel_false`,
         `postBlockingSettlesRun_mintAwareFuel_false` (landed in Phase 2), and
         `postBlockingSettles_fuel_zero_false` as the refutations.
      3. **The frame-class split, unflattened** — eight of the nine established vacuous at `.Base`,
         `.Dense` and `.RTime`, and undecided-but-equally-undelivering with zero dependents at
         `.ZTime`; `buildTableauAt_isSome_of_budget_of_run` alone carried the unrestricted
         `PostBlockingSettles` and is unconditionally vacuous at **all four** classes. **Do not
         flatten these into one claim** — this is a dispatch-level precision requirement.
      4. **What survives and why** — the `PostBlockingSettlesRun` predicate itself, the whole
         refutation apparatus, the bridge, and the live `PostBlockingSettlesSeedRun` successor line.
      5. **Cost of removal** — zero reverse-dependents, machine-verified across the whole
         environment.
- [ ] Expected shape: roughly 25-35 lines of prose replacing ~200 lines, a net removal of ~165 lines
      and, critically, of nine declarations from the public surface.
- [ ] Scoped build plus enumerated one-hop dependents, detached and guarded (see Verification Tier).
- [ ] Commit on green.

**Timing**: 1.25 hours

**Depends on**: 2

Phase 2 must land first: the retirement record names `postBlockingSettlesRun_mintAwareFuel_false`
as one of the refutations, and a record that forward-references a lemma not yet in the file would
reproduce, in miniature, the exact defect this task exists to remove.

**Verification Tier**: interface

Justification: this phase removes nine exported symbols. That is an externally visible surface
change, which puts it above `local` by the tie-break rule even though research machine-verified
zero reverse-dependents. The direct dependent set is small and enumerable, so `interface` — not
`full` — is the right ceiling here; the residual transitive risk is covered by the Phase 6 gate.

**Enumerated direct dependents** (every file importing this module, verified at planning time):
`FormalSystem/Metalogic/Decidability.lean`, and under `Tests/BimodalTest/`:
`UntlSnceCopyProbe.lean`, `RayRegionProbe.lean`, `TableauConformance.lean`,
`TemporalWitnessProbe.lean`, `RegionGateProbe.lean`, `BoxSpreadProbe.lean`.

**Scope Hypothesis**: The span is asserted to be contiguous, to contain exactly the nine and their
block prose, and to contain all four of the internal cross-references among the nine. Confirm at
implementation time by re-running the nine-name `grep -n` immediately after the deletion: every
surviving hit must be inside the new retirement record. Any hit outside it means the span boundary
was wrong.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` - delete the nine plus block prose; insert the retirement record

**Verification**:
- Scoped build of the module plus the seven enumerated dependents, green.
- `grep -n` for all nine names returns hits only inside the retirement record.
- The keep set is intact: the predicate, the refutation apparatus, the bridge, and the
  `PostBlockingSettlesSeedRun` line all still resolve.

---

### Phase 4: Repair the six collateral prose sites [COMPLETED]

**Goal**: Leave no prose in the file that names a retired theorem as live, forward-references the
deleted block, or asserts something the deletion made false. Three of these six sites appear in no
prior artifact.

**Tasks**:
- [ ] **Site A** (`~:5194-5195`, named in the 549 summary): the sentence asserting that
      `buildTableauAt_isSome_of_budget_run` "and its siblings are the termini stated at it", with
      `buildTableauAt_isSome_of_budget_of_run` certifying the strengthening. **Rewrite, do not
      excise** — the surrounding claim about `postBlockingSettlesRun_of_postBlockingSettles` fixing
      the direction stays true and is worth keeping. Re-point to the retirement record.
- [ ] **Site B** (`~:12172-12173`, *not in any prior artifact*): inside the §C12 intro prose, "the
      restatements below are additive siblings carrying `ArmSettlement` … together with the narrowed
      residual". After deletion there are no restatements below; the sentence forward-references
      nothing. Rewrite to point at the retirement record.
- [ ] **Site C** (`~:12208`, *not in any prior artifact*): inside the `PostBlockingSettlesRun`
      docstring, "it is a false hypothesis at those three classes, so the termini carrying it are
      vacuous there". Historically true; after deletion no terminus in the file carries it. Recast
      in the past tense with a pointer to the retirement record.
- [ ] **Site D** (`~:12740-12741`): "`buildTableauAt_isSome_of_budget_fixed_run` and its five `_run`
      siblings carry `PostBlockingSettlesRun fc (mintAwareFuelAt …)`". Names a retired theorem
      **and** carries the six-count undercount. Rewrite for the retired set of nine, and widen the
      fuel figure from `mintAwareFuelAt` alone to both figures — this sentence must move in step
      with C9 entry 25's amendment (a) in Phase 5, or the file contradicts its own register.
- [ ] **Site E** (`~:12939`, *not in any prior artifact — highest-risk omission*): inside the
      docstring of `buildTableauAt_isSome_of_budget_fixed_seedRun`, an explicit **keep**-set item:
      "the other five `_run` termini are left as they stand, and widening to them is deliberately
      deferred rather than forgotten". After deletion this is flatly false — nothing is left
      standing — *and* it under-counts. Missing this leaves a false statement inside a surviving
      headline theorem, which is precisely the defect class this task exists to remove.
- [ ] **Orphaned-but-kept notes** (no build impact; readability only): add a one-clause docstring note
      to `buildTableauAt_isSome_of_settlesRun` (the bridge, `~:12260`, consumers 4 → 0) and to
      `postBlockingSettlesRun_of_postBlockingSettles` (`~:12228`, consumers 1 → 0), of the shape
      "retained as the record of the narrowing; its consumers were retired — see the retirement
      record". Both are correctly in the keep set: both are named by C9 entry 23 and by prose at
      `~:5192` and `~:12891`.
- [ ] Run the exit gate below. Every surviving hit for the nine names must be inside the retirement
      record — nowhere else.
- [ ] Commit on green.

**Exit gate** (mechanical, run before closing the phase):
```
grep -n "buildTableauAt_isSome_of_budget_run\|buildTableauAt_isSome_of_budget_of_run\|\
buildTableauAt_isSome_at_seed_run\|buildTableauAt_isSome_of_budget_at_run\|\
buildTableauAt_isSome_at_seed_at_run\|buildTableauAt_isSome_of_budget_selfGuarded_run\|\
buildTableauAt_isSome_at_seed_selfGuarded_run\|buildTableauAt_isSome_of_budget_fixed_run\|\
buildTableauAt_isSome_at_seed_fixed_run" \
  FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean
```

**Timing**: 0.75 hours

**Depends on**: 3

**Verification Tier**: prose

Justification: every edit here is confined to `/-- … -/` docstrings and `/-! … -/` section comments.
Lean performs no name resolution inside either, so none of these sites is a compile obligation —
research confirmed this is why the deletion could not break elaboration in the first place. The
tier's stated blind spot (an edit crossing out of a comment boundary) is exactly what the
diff-read-through covers, and Phase 6's full build catches it regardless.

**Scope Hypothesis**: Six sites asserted, three of them unattested in prior artifacts. Confirm by
locating each one by its **quoted text** above rather than its line number, then by the exit gate:
after the six edits, zero hits for the nine names outside the retirement record. A quoted string
that does not match means the file moved under the research — stop and re-locate, do not guess.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` - six prose rewrites plus two orphan-note docstrings

**Verification**:
- Diff read-through confirms every changed hunk lies inside a comment or docstring region.
- Exit gate: all nine-name hits inside the retirement record only.
- Site E specifically confirmed edited (it is the one most likely to be skipped).

---

### Phase 5: Amend the C9 register and correct the count [COMPLETED]

**Goal**: Bring the C9 register into agreement with the file: the corrected count of nine, the
widened vacuity claim over both fuel figures, and the row that falls outside the `.ZTime` caveat
entirely.

**Tasks**:
- [ ] **Entry 23** (`~:15649-15652`, site F): "the restated termini name `ArmSettlement` instead of
      manufacturing it from a refuted predicate" — present tense describing a now-deleted block.
      Recast to past tense; point at the retirement record.
- [ ] **Entry 24** (`~:15661`): correct the count to **nine**, not six, and re-point its description
      of the restated termini from live theorems to the retirement record. Preserve the entry's own
      stated principle that a superseded clause "is corrected rather than deleted so the sequence of
      findings stays legible" — this amendment is an instance of that principle, not an exception
      to it.
- [ ] **Entry 25, amendment (a)** (`~:15696`): the sentence "that figure is always at least one
      (`one_le_mintAwareFuelAt`, off `mintPathBound`'s trailing `+ 1` through `fuelFigure_pos`)".
      Widen it: both fuel figures now have positivity lemmas and both are refuted at `.Base`. Name
      `one_le_mintAwareFuel` alongside `one_le_mintAwareFuelAt`, and
      `postBlockingSettlesRun_mintAwareFuel_false` alongside its `At`-sibling. Site D in Phase 4 is
      the in-file counterpart and must already agree.
- [ ] **Entry 25, amendment (b)** (`~:15749-15757`, the closing `.ZTime` paragraph): it currently
      reads as a uniform caveat over the whole block. Split out
      `buildTableauAt_isSome_of_budget_of_run`: it carries the unrestricted `PostBlockingSettles`
      and is refuted by `postBlockingSettles_fuel_zero_false` at **all four** frame classes, so the
      `.ZTime` caveat does not apply to it at all. It currently reads as one of a uniform block; it
      is not.
- [ ] **Entry 22 stays untouched.** It concerns `PostBlockingSettles` as literally stated; nothing
      here changes it.
- [ ] Run the count gate: `grep -n "five \`_run\`"` must return **empty**. `grep -n "\bnine\b"` hits
      must be confined to the retirement record, the amended entries, and the two pre-existing
      `hlab`-carrier sites.
- [ ] **Do not edit** — verified false positives for the count correction: the nine `hlab` carriers
      at `~:14282` and C9 entry 21 at `~:15388` (a disjoint set, no `_run` theorem takes an `hlab`
      argument); "the six restated termini" at `~:15350` and "the two seed-level termini" at
      `~:15316` (both refer to the `MintPaysForTimeStable` chain); and the generic
      `PostBlockingSettles`-or-`PostBlockingSettlesRun` termini clauses at `~:14286` and `~:15391`,
      which stay true after deletion because the landed `PostBlockingSettles` termini survive.
- [ ] Commit on green.

**Timing**: 0.75 hours

**Depends on**: 4

Serialized behind Phase 4 by the shared-file constraint, and substantively because site D's in-file
sentence and entry 25's amendment (a) must land in agreement.

**Verification Tier**: prose

Justification: the C9 register is a `/-! … -/` section comment. Zero compile surface.

**Scope Hypothesis**: Four register entries asserted as needing amendment (23, 24, 25a, 25b) and
one asserted as needing none (22), against six named false-positive sites that must not be edited.
Confirm by the count gate above plus a read of entry 22 to verify it makes no claim this task
falsifies. If entry 22 turns out to name a retired theorem, amend it and record the deviation.

**Files to modify**:
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` - C9 entries 23, 24, 25

**Verification**:
- Diff read-through confirms all hunks inside the register's section comment.
- `grep -n "five \`_run\`"` empty.
- `grep -n "\bnine\b"` hits confined to the expected three regions.
- No edit landed on any of the six named false-positive sites.

---

### Phase 6: Full verification gate [COMPLETED]

**Goal**: Discharge the dispatch's acceptance criteria end to end, and confirm the meaningful
regression check rather than the trivially-passing one.

**Tasks**:
- [ ] Full build, **detached and guarded**, under `Bash(run_in_background: true)`:
      `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- lake build`.
      A foreground `lake build` on this repository will livelock, not merely time out.
- [ ] `lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace2.lean`
      must still report `constants from MintBound reached by decide: 0`. **This is the meaningful
      regression check.**
- [ ] **Do not run `probes/RevDep.lean` as a gate.** It will report 0 trivially once the names stop
      resolving, and worse, will `logError` on the unresolved names. Expect it to fail loudly; that
      failure is the *expected* outcome, not a regression. It is evidence of neither success nor
      failure here.
- [ ] `#print axioms` unchanged for every surviving Decidability result — `MainResults.lean` already
      emits these as build-time obligations, so a green full build is the check.
- [ ] Zero-debt confirmation: no `sorry` in tactic or term position anywhere in `FormalSystem/`
      outside `Boneyard/`; zero real `axiom` declarations in `FormalSystem/`. Both were baselined
      clean by research.
- [ ] Re-run both grep gates from Phases 4 and 5 independently of the phases that authored them.
- [ ] Confirm the net line delta is a removal of roughly 165 lines from `MintBound.lean` and that
      nine declarations have left the public surface.
- [ ] Final commit. **Commit-message precision is a dispatch-level requirement**: state that eight of
      the nine are established vacuous at `.Base`, `.Dense` and `.RTime` and undecided-but-equally-
      undelivering with zero dependents at `.ZTime`, and that
      `buildTableauAt_isSome_of_budget_of_run` is unconditionally vacuous at all four. Do not flatten
      these into one claim.

**Timing**: 0.75 hours (mostly wall-clock on the detached build)

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: This phase asserts a net removal of roughly 165 lines and the departure of
nine declarations from the public surface. Confirm mechanically with `git diff --stat` on the file
and by the nine-name grep gate; the ~165 figure is an estimate derived from a ~200-line deletion
against a ~25-35 line record, so treat a materially different delta as a signal that the span
boundary or the record's length diverged from plan, not as a failure in itself.

**Files to modify**:
- None. Verification only.

**Verification**:
- Full `lake build` green.
- `DepTrace2.lean` prints `constants from MintBound reached by decide: 0`.
- Both grep gates pass.
- No `sorry`, no axiom additions.

---

## Lean Challenge Statements

```lean
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound

namespace FormalSystem.Metalogic.Decidability

theorem one_le_mintAwareFuel (Ucard Tmax mintBudget D β : Nat) :
    1 ≤ mintAwareFuel Ucard Tmax mintBudget D β := sorry

theorem postBlockingSettlesRun_mintAwareFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.Base
        (mintAwareFuel U.card Tmax mintBudget D β) := sorry

end FormalSystem.Metalogic.Decidability
```

Both statements are transplants of already-proved, kernel-checked results from
`specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean`
(axioms `[propext, Classical.choice, Quot.sound]`). The two deviations from the probe file are
deliberate and load-bearing: the prime is dropped from `one_le_mintAwareFuel`, and
`FrameClass.Base` is fully qualified because `MintBound.lean` does not open
`FormalSystem.ProofSystem`. No other declaration in this task carries a proof obligation — every
remaining edit is a deletion or a prose rewrite.

## Testing & Validation

- [ ] Full `lake build` green, run detached and guarded.
- [ ] `probes/DepTrace2.lean` reports `constants from MintBound reached by decide: 0`.
- [ ] Both new lemmas resolve, unprimed, with the qualified frame class.
- [ ] Nine-name grep gate: every hit inside the retirement record, none outside it.
- [ ] Count gate: `grep -n "five \`_run\`"` empty; `\bnine\b` hits confined to the retirement record,
      the amended C9 entries, and the two pre-existing `hlab`-carrier sites.
- [ ] Keep set intact: the `PostBlockingSettlesRun` predicate, the refutation apparatus, the bridge,
      and the `PostBlockingSettlesSeedRun` successor line all still resolve.
- [ ] Zero `sorry` in tactic or term position outside `Boneyard/`; zero real `axiom` declarations in
      `FormalSystem/`.
- [ ] `docs/theorem-index.md` untouched; no `.ZTime` strengthening attempted.

## Artifacts & Outputs

- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — nine declarations
  removed, a retirement record installed, two lemmas landed, six prose sites repaired, three C9
  entries amended. Net ~165 lines removed.
- `specs/554_retire_nine_vacuous_run_theorems/summaries/01_*-summary.md` — execution summary.
- Commits: one per green phase (Phases 2-5), plus the final verification commit.

## Rollback/Contingency

**Rollback**: every phase commits independently and all edits are confined to one file. Revert the
phase's commit; the tree returns to a green state, since no phase commits red. Nothing outside
`MintBound.lean` is touched, so there is no cross-file rollback ordering to get right.

**Contingency — if the retirement record shape is rejected**: the dispatch's Section 7 fallback
remains available — keep all nine and add a vacuity notice at each declaration site naming the
refutation by name and the frame classes at which vacuity is established. That fallback is strictly
worse on the publication criterion than the retirement record and strictly better than the status
quo. If it is chosen, execute it in place of Phase 3 and still execute Phases 2, 4 and 5 (the
widening lemmas, the prose repair, and the register amendments are independent of the delete-vs-
annotate choice). This plan does not raise it as a `user_decision`: research established that the
repository has already answered the retire-vs-annotate question twice, at `Correctness.lean:192`
and in ADR-007, and the retirement record dominates both dispatch options.

**Contingency — if a `sorry` becomes tempting**: stop. There is no open proof obligation in scope.
A `sorry` indicates work outside this task's boundary, most likely the explicitly excluded `.ZTime`
strengthening. Re-read Non-Goals; do not defer the `sorry`.

**Contingency — if the full build fails at Phase 6**: the failure cannot come from symbol removal
(zero reverse-dependents, machine-verified) and cannot come from prose (no compile surface). Look
first at Phase 2's two additions — specifically at whether `FrameClass.Base` resolved as intended.
The file records that exact failure at `:12980-12982` as having been **silent**, so a green build
alone does not clear it; confirm the qualified spelling by reading the landed source.
