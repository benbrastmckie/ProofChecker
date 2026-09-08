# Implementation Plan: Task #549

- **Task**: 549 - Trace whether `FormalSystem.Metalogic.Decidability.decide` depends on the six now-vacuous `_run` theorems, and correct the affected status claims if it does
- **Status**: [IMPLEMENTING]
- **Effort**: 3.75 hours
- **Dependencies**: 463 (mathematical premise + `file_scope` serialization edge on `MintBound.lean`)
- **Research Inputs**: `specs/549_trace_decide_dependency_on_vacuous_run_theorems/reports/01_trace-decide-dependency-vacuous-run.md`
- **Artifacts**: plans/01_decide-dependency-verdict-disposition.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Research has already executed the mechanical trace this task exists to perform and returned a
**NO DEPENDENCY** verdict: `Decidability.decide` reaches zero constants from
`Verified/Termination/MintBound.lean`, and a whole-environment reverse-dependency scan finds zero
dependents of the vacuous `_run` block anywhere in `FormalSystem`. Implementation therefore does
not re-litigate the question — it (a) **re-runs the probes and captures their verbatim output as
committed evidence**, so the deliverable is a reproducible machine check rather than prose
quoting a machine check, (b) **adjudicates `docs/theorem-index.md:113` against the actual
`#print axioms` output** and confirms the NO-DEPENDENCY branch's mandated no-edit, and (c) writes
the **verdict + disposition deliverable** with follow-up task briefs precise enough to execute
without re-deriving anything.

The expected end state is a repository with **zero modifications outside `specs/**`**. That is the
correct outcome of this task's binary verdict, not a shortfall: the dispatch's NO-DEPENDENCY
branch explicitly forbids touching `docs/theorem-index.md`, and the CONSTRAINTS section forbids
touching `FormalSystem/**` on either branch. Definition of done: probe evidence captured and
reproducing the verdict, index row adjudicated as accurate and left untouched, disposition
(RETIRE) recorded with what-moves/what-stays enumerated, follow-up work named, `lake build` green.

### Research Integration

Findings carried in verbatim, not re-derived:

- **Verdict**: `decide`, `decideAuto`, `decideBlocking`, `isValid`, `isSatisfiable` and
  `sound_of_isValid` each close over 294-1338 constants with **zero** hits among the nine `_run`
  theorems, `PostBlockingSettlesRun`, `PostBlockingSettles`, and the bridge; the module-level count
  is `constants from MintBound reached by decide: 0`. Structural, not incidental:
  `DecisionProcedure.lean`'s 75-module import closure contains zero `Verified/`/`Termination/`
  modules, and `DecisionProcedure` is module 3724 against `MintBound`'s 3755.
- **Root cause of the separation**: `decide` calls `buildTableau` at a literal `tableauFuel :=
  1000`; every one of the nine concludes about `buildTableauAt … .isSome` at a derived
  `mintAwareFuel*` figure. `decide` returns `.fuelExhausted` as an *answer*, so it makes no
  totality claim a fuel bound could underwrite.
- **Upward correction to the premise**: the vacuous set is **nine**, not six. Rows 1-4 use the
  un-`At` `mintAwareFuel` figure that 463's refutation was never instantiated at (now
  kernel-checked in `probes/Widen.lean`, axioms `pcq`), and row 9
  (`buildTableauAt_isSome_of_budget_of_run`) carries `PostBlockingSettles`, refuted at **all four**
  frame classes including `.ZTime`.
- **Disposition selected by the verdict**: RETIRE the nine (`MintBound.lean:12312-12488`), plus the
  block prose at `:12290-12309` and the forward reference at `:5194-5195`; keep the predicate, the
  whole refutation apparatus, the `PostBlockingSettlesSeedRun` successor line, and C9 entries 22/24/25.
- **Excluded**: the `.ZTime` strengthening recipe in `MintBound.lean`'s scoped note. Its only
  justification was the DEPENDS-at-`.ZTime` branch, which the trace rules out.

### Prior Plan Reference

No prior plan. This is round 1 (`artifact_number: 1`).

### Roadmap Alignment

No `roadmap_path` was supplied in the delegation context, so no roadmap phases are added (Stage 2.6
inactive) and `specs/ROADMAP.md` is **not** edited by this plan. For orientation only: the work sits
under ROADMAP Phase 2 (Decidability and the Tableau Engine — the largest open front), whose current
state already records the `buildTableau_isSome`-family situation, and it feeds ROADMAP Phase 5
(Publication and Documentation), which is the reason the disposition deliverable exists at all.
Recording a retired open question and a vacuity count correction is Phase 2/Phase 5 hygiene; the
follow-up retirement task named in Phase 4 is the item a roadmap update would eventually cite.

## Goals & Non-Goals

**Goals**:
- Reproduce the mechanical dependency trace at implementation time and commit its **verbatim
  output** as evidence under `specs/549_.../probes/`, so the verdict rests on a re-runnable
  artifact rather than on quoted prose.
- Adjudicate `docs/theorem-index.md:113` (and the adjacent `:114` `sound_of_isValid` row) against
  actual `#print axioms` output, and record the NO-DEPENDENCY branch's mandated **no edit**.
- Deliver the disposition recommendation (RETIRE the nine) with the keep/delete boundary
  enumerated and the "do not execute the `.ZTime` strengthening" instruction stated plainly.
- Name the follow-up work — the MintBound retirement task and the register count amendment — as
  ready-to-execute briefs, with the `463` serialization edge and `file_scope` spelled out.
- Prove the read-only constraint was honoured: zero modifications outside `specs/**`, `lake build`
  green, no `sorry`, no axiom additions.

**Non-Goals**:
- **Editing anything under `FormalSystem/**`.** This includes the two lemmas
  (`one_le_mintAwareFuel`, `postBlockingSettlesRun_mintAwareFuel_false`) that `probes/Widen.lean`
  already proves and that the disposition recommends landing: they belong to the follow-up task,
  because `MintBound.lean` is owned by task 463 and the two tasks would collide.
- **Editing `docs/theorem-index.md`.** Permitted only on the DEPENDS branch, which is excluded.
- **Executing the retirement.** Recommend and justify; do not delete a single theorem here.
- **Executing the `.ZTime` witness strengthening** described in `MintBound.lean`'s scoped note.
- Editing `specs/ROADMAP.md`, or amending C9 register entry 25 in place (that entry lives in
  `MintBound.lean`).
- Adding `context/project/lean4/patterns/dependency-tracing.md` (the research report's context
  extension recommendation) — named as follow-up only; a `.claude/**` write would also have to go
  to the `agent-system/extensions/**` source store, which is out of this task's scope.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Task 463 has landed edits to `MintBound.lean` since the research run, moving or renaming declarations, so a probe fails to resolve a name | M | M | Probes resolve **names**, not line numbers, and `DepTrace.lean` asserts existence of every target and suspect before tracing. A resolution failure is a signal to re-derive the name from the current file, never to assume the closure result still holds. Record the HEAD sha alongside the captured output. |
| `lake build` comes back red for reasons this task did not cause (concurrent 463 work in the tree) | M | M | Capture `git status --short` and HEAD **before** building. If red, attribute the failure by file: if no failing module is one this task touched (it touches none), record the baseline as pre-existing, do not repair, and surface it — repair belongs to whoever owns the file. |
| Temptation to "just land" the six-line `Widen.lean` result into `MintBound.lean` since it is proved and cheap | H | M | Explicit Non-Goal above, restated in Phase 4's brief. The cost is not proof difficulty, it is a write collision with an in-flight task on a 15,700-line file. |
| The task is read as producing nothing because no repository file changes | M | M | Phase 5 states the retired open question as a first-class result and carries the count correction (six -> nine), which is new knowledge no other artifact holds. |
| Probe re-run is expensive (`RevDep.lean` imports the `FormalSystem` root aggregator) | L | M | Elaborate against existing oleans with `lake env lean`; run the six probes sequentially and capture output incrementally so a timeout loses at most one probe's result. |
| The verdict is later invalidated by someone importing `Verified/Termination/MintBound` into the `DecisionProcedure` line | M | L | Record the module-ordering fact (`DecisionProcedure` 3724 < `MintBound` 3755) as a cheap regression check and retain the probes as re-runnable templates; the durable fix is the follow-up retirement. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 4 | 1 |
| 3 | 5 | 1, 2, 3, 4 |
| 4 | 6 | 5 |

Phases within the same wave can execute in parallel.

---

### Phase 1: Reproduce and capture the mechanical trace evidence [COMPLETED]

**Goal**: Turn the research report's quoted probe results into a committed, verbatim,
re-runnable evidence log, and confirm the verdict still reproduces against the current tree.

**Tasks**:
- [x] Record the baseline: `git rev-parse HEAD`, `git status --short`, and
      `git log -1 --format=%h -- FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`.
- [x] Re-run each probe from the repo root, capturing stdout+stderr verbatim:
      `lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/{Exists,Ax,DepTrace,DepTrace2,RevDep,Widen}.lean`.
- [x] Write `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md`:
      HEAD sha, one section per probe with the exact command and its unedited output, and a one-line
      reading of what each output establishes.
- [x] Confirm the four load-bearing numbers reproduce: zero suspect hits for all six traced
      targets; `constants from MintBound reached by decide: 0`; `direct reverse-dependents … : 0`;
      `Widen.lean` axioms `[propext, Classical.choice, Quot.sound]` with no `sorry`.
- [x] If any probe fails to resolve a declaration name, stop and re-derive that name from the
      current `MintBound.lean` before continuing; do not edit `MintBound.lean` to make a probe pass.

**Timing**: 0.75 hours

**Depends on**: none

**Verification Tier**: `local`

**Scope Hypothesis**: This phase asserts **six** probe files under `probes/` and **nine** vacuous
`_run` theorems at `MintBound.lean:12312-12488`. Both are hypotheses from research, not facts:
confirm the file count with `ls specs/549_.../probes/` and the theorem count with a fresh
`grep -n "_run" MintBound.lean` over the stated line range before quoting either figure in an
artifact. Line numbers in particular are known-stale once already (463's report said `:12199` for
a terminus now at `:12449`).

**Files to modify**:
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md` - new; verbatim probe output + HEAD sha.

**Verification**:
- `probe-evidence.md` exists, is non-empty, and contains one command+output section per probe.
- All four load-bearing numbers appear in the captured output, not merely in the summary prose.
- `git status --short` shows no change outside `specs/**`.

---

### Phase 2: Read-only compliance baseline [COMPLETED]

**Goal**: Establish, mechanically, that the task's read-only constraint holds — and give Phase 6 a
baseline to re-check against.

**Tasks**:
- [x] Capture `git status --porcelain` and confirm zero entries under `FormalSystem/`, `docs/`,
      `latex/`, `typst/`, `Tests/`.
- [x] Confirm `docs/theorem-index.md` is byte-identical to HEAD (`git diff --quiet -- docs/theorem-index.md`).
- [x] Note any pre-existing dirty paths (e.g. `specs/events.jsonl`, `.claude-extensions.json`) so a
      later diff is not misattributed to this task.
- [x] Append the baseline to `probes/probe-evidence.md` (or a sibling section) so it is committed.

**Timing**: 0.25 hours

**Depends on**: none

**Verification Tier**: `prose`

**Files to modify**:
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md` - append baseline section.

**Verification**:
- `git diff --quiet -- docs/theorem-index.md FormalSystem/` exits 0.
- Baseline section committed with the pre-existing dirty paths named.

---

### Phase 3: Adjudicate the `docs/theorem-index.md` decidability rows [COMPLETED]

**Goal**: Check the `decide` row (and its `sound_of_isValid` neighbour) column by column against
observed fact, and record the mandated no-edit decision with its justification.

**Tasks**:
- [x] Read the two rows in the `### Decidability` table (`docs/theorem-index.md:113-114`) and
      enumerate their five substantive columns: statement, Lean name, file, frame class, axioms.
- [x] Check each column against evidence: Lean name resolves (`Exists.lean`); file path matches
      the declaration site (`DecisionProcedure.lean:176`, `Correctness.lean`); axioms column
      `pcq pinned:C14` matches the captured `#print axioms` output; the statement wording claims
      nothing about totality at a derived fuel figure that the `_isSome` family would underwrite.
- [x] Record explicitly that `decide` returns `.fuelExhausted` as an answer, so no totality claim
      exists for a vacuous fuel bound to have propped up — the durable reason the exposure could
      not have existed, independent of the current import graph.
- [x] Conclude: **no edit**, per the dispatch's NO-DEPENDENCY branch. Write the adjudication as a
      section for Phase 5's deliverable; do not touch `docs/theorem-index.md`.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: `prose`

**Scope Hypothesis**: The plan asserts the target row is at `docs/theorem-index.md:113` and that
the relevant table has exactly two decidability rows. Confirm by locating the `### Decidability`
heading and reading the table at implementation time rather than trusting the line number; report
the actual line if it has moved.

**Files to modify**:
- None. (`docs/theorem-index.md` is read-only on this branch.)

**Verification**:
- `git diff --quiet -- docs/theorem-index.md` exits 0 at phase end.
- Every one of the five columns has a recorded verdict backed by a named piece of evidence.

---

### Phase 4: Author the follow-up task briefs [COMPLETED]

**Goal**: Name the deferred work precisely enough that a follow-up task executes it without
re-deriving this task's reasoning — the dispatch's "named, not attempted here" requirement.

**Tasks**:
- [x] Brief A — **Retire the nine `_run` theorems**. Include: the delete set (the nine at
      `MintBound.lean:12312-12488`, the block prose at `:12290-12309`, the forward reference at
      `:5194-5195`); the explicit keep set (`PostBlockingSettlesRun` and its bridge, the whole
      refutation apparatus, the `PostBlockingSettlesSeedRun` successor line, C9 entries 22/24/25);
      `file_scope: FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`;
      dependency on 463 as a serialization edge; and the commit-message note that rows 1-8 are not
      *established* vacuous at `.ZTime` but are equally undelivering there with zero dependents,
      while row 9 is unconditionally vacuous at all four classes.
- [x] Brief A, amendment (a) — land `one_le_mintAwareFuel` and
      `postBlockingSettlesRun_mintAwareFuel_false` (already proved, six lines, in
      `probes/Widen.lean`) so the register's vacuity claim covers the un-`At` figure, and correct
      "its five `_run` siblings" to the true count.
- [x] Brief A, amendment (b) — record row 9 separately in the register: it is vacuous via
      `postBlockingSettles_fuel_zero_false` at all four classes, so entry 25's `.ZTime` caveat does
      not apply to it.
- [x] Brief B — optional, low priority: add `context/project/lean4/patterns/dependency-tracing.md`
      to the **`agent-system/extensions/**` source store** (never `.claude/**` directly), carrying
      the closure-traversal recipe, the module-index variant, the reverse-dependency scan, and the
      warning that `#print axioms` is not a dependency tracer.
- [x] Do **not** create the tasks here. Record each brief with a ready-to-paste one-line
      description so `/task` can create it in a single step.

**Timing**: 0.5 hours

**Depends on**: 1

**Verification Tier**: `prose`

**Files to modify**:
- None yet; briefs are drafted for inclusion in Phase 5's deliverable.

**Verification**:
- Each brief names its file scope, its dependency edge, and its acceptance criterion.
- Brief A distinguishes delete-set from keep-set explicitly, with no item in both.
- No new entries appear in `specs/state.json` or `specs/TODO.md` from this phase.

---

### Phase 5: Write the verdict and disposition deliverable [COMPLETED]

**Goal**: Produce the durable record — the binary verdict, its evidence, the count correction, the
disposition recommendation, and the follow-up briefs — as this task's summary artifact.

**Tasks**:
- [x] Write `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md`.
- [x] Section 1 — **VERDICT: NO DEPENDENCY**, stated as a retired open question, with the evidence
      named (forward closure, module-level count, reverse-dependency scan, import closure, module
      ordering) and each item pointing at its section of `probes/probe-evidence.md`.
- [x] Section 2 — the count correction: the vacuous set is nine, not six; rows 1-4 via the un-`At`
      figure (kernel-checked here), row 9 via `PostBlockingSettles` at all four classes. State this
      as an upward correction to task 463's premise, with the reason 463 undercounted.
- [x] Section 3 — the index adjudication from Phase 3 and the recorded **no edit** to
      `docs/theorem-index.md:113`.
- [x] Section 4 — **DISPOSITION: RETIRE the nine**, with the keep/delete boundary, the publication
      argument (a headline-shaped theorem whose hypothesis is unsatisfiable, with the refutation
      ~3,300 lines downstream), and why the other two dispositions are excluded.
- [x] Section 5 — the explicit instruction **not** to execute the `.ZTime` strengthening, and why.
- [x] Section 6 — the follow-up briefs from Phase 4.
- [x] Section 7 — the fallback, flagged as an explicit user choice and not a default: if deletion
      is unwanted, mark vacuity in each of the nine docstrings, cross-referencing
      `postBlockingSettlesRun_terminusFuel_false` by name.
- [x] State the read-only outcome plainly: zero modifications outside `specs/**`, by design.

**Timing**: 1.0 hours

**Depends on**: 1, 2, 3, 4

**Verification Tier**: `prose`

**Files to modify**:
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md` - new; the task's deliverable.

**Verification**:
- All seven sections present; every factual claim traces to a section of `probes/probe-evidence.md`
  or to a named source line.
- The verdict is stated in the first section, unhedged.
- No claim in the deliverable rests on prose-reading rather than a machine check.

---

### Phase 6: Final gate — build green, read-only re-audit [IN PROGRESS]

**Goal**: Discharge the dispatch's build constraint and prove the tree is unchanged.

**Tasks**:
- [ ] Run `lake build` from the repo root; capture the exit status and the tail of the output.
- [ ] If red, attribute by failing module against Phase 2's baseline: this task modifies no Lean
      file, so any failure is pre-existing or concurrent. Record it, do not repair it, and name the
      owner.
- [ ] Confirm zero `sorry` and zero axiom additions attributable to this task (nothing under
      `FormalSystem/**` changed; `probes/*.lean` are not part of the library build).
- [ ] Re-run the Phase 2 read-only audit: `git status --porcelain` shows changes only under
      `specs/549_trace_decide_dependency_on_vacuous_run_theorems/**` plus the pre-existing dirty
      paths recorded in Phase 2.
- [ ] Append the build result and final audit to `probes/probe-evidence.md`.

**Timing**: 0.75 hours

**Depends on**: 5

**Verification Tier**: `full`

**Files to modify**:
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md` - append build + final audit.

**Verification**:
- `lake build` exit status recorded (green, or red with per-module attribution to a pre-existing cause).
- `git diff --quiet -- FormalSystem/ docs/` exits 0.
- No `sorry` and no axiom additions introduced.

---

## Lean Challenge Statements

**None.** This task proves no new theorem and is read-only with respect to `FormalSystem/**`; the
`- **Goals**:` bullets above name no Lean identifiers to land, so the identifier set this section
must match is empty. The one Lean result produced in support of the verdict
(`postBlockingSettlesRun_mintAwareFuel_false`) already exists, kernel-checked, in
`specs/549_.../probes/Widen.lean` and is deliberately **not** landed into the library here — it is
deferred to the follow-up retirement task, which owns `MintBound.lean`.

## Testing & Validation

- [ ] All six probes elaborate cleanly with `lake env lean` and reproduce the four load-bearing
      numbers (zero suspect hits x 6 targets; MintBound-reach 0; reverse-dependents 0; `Widen.lean`
      axioms `[propext, Classical.choice, Quot.sound]`).
- [ ] `#print axioms` output for `decide` and `sound_of_isValid` matches the `pcq pinned:C14`
      column in `docs/theorem-index.md`.
- [ ] `git diff --quiet -- docs/theorem-index.md` and `git diff --quiet -- FormalSystem/` both exit 0.
- [ ] `lake build` green (or a red result attributed, per module, to a pre-existing/concurrent cause).
- [ ] No `sorry` and no axiom additions.
- [ ] Deliverable contains all seven sections and states the verdict unhedged.

## Artifacts & Outputs

- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md` — verbatim
  probe output, HEAD sha, read-only baseline, final build result.
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md`
  — the verdict, the count correction, the index adjudication, the RETIRE disposition, the
  `.ZTime` exclusion, the follow-up briefs, the fallback option.
- **No repository file outside `specs/**` is created, modified, or deleted.** This is the intended
  end state of the NO-DEPENDENCY branch.

## Rollback/Contingency

Rollback is trivial and total: every write lands under
`specs/549_trace_decide_dependency_on_vacuous_run_theorems/`, so reverting the task's commits
restores the tree exactly. No Lean source, no `docs/` file, and no build artifact is touched, so
there is nothing to rebuild after a revert.

Contingencies:
- **A probe fails to resolve a name** (463 renamed or moved a declaration): re-derive the name from
  the current `MintBound.lean`, update the probe under `probes/`, re-run, and note the drift in
  `probe-evidence.md`. Never edit `MintBound.lean`.
- **A probe reproduces a *different* number** (a non-zero hit anywhere): stop. The verdict flips to
  DEPENDS and the plan's branch is wrong — record the hit, mark the phase `[BLOCKED]`, and escalate
  rather than editing `docs/theorem-index.md` on a single unreviewed result.
- **`lake build` red from concurrent 463 work**: record with per-module attribution against the
  Phase 2 baseline, mark Phase 6 `[PARTIAL]`, and surface the ownership; do not repair a file this
  task is forbidden to touch.
