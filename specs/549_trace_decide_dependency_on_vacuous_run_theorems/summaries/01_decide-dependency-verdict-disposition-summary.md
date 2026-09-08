# Implementation Summary: Task #549

- **Task**: 549 - Trace whether `FormalSystem.Metalogic.Decidability.decide` depends on the six now-vacuous `_run` theorems, and correct the affected status claims if it does
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T17:00:00-07:00
- **Completed**: 2026-09-07T17:20:00-07:00
- **Effort**: ~0.4 hours
- **Dependencies**: 463 (mathematical premise + `file_scope` serialization edge on `MintBound.lean`)
- **Artifacts**: plans/01_decide-dependency-verdict-disposition.md, probes/probe-evidence.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The open question is retired. A mechanical dependency trace — six probes, re-run at HEAD
`2dc42ca11` and captured verbatim in `probes/probe-evidence.md` — establishes that
`FormalSystem.Metalogic.Decidability.decide` reaches **zero** constants from
`Verified/Termination/MintBound.lean`, and that the vacuous `_run` block has **zero**
reverse-dependents anywhere in `FormalSystem`. `docs/theorem-index.md:113` is therefore accurate
as written and is left untouched, per the dispatch's NO-DEPENDENCY branch. Two things beyond the
verdict: the vacuous set is **nine**, not six (an upward correction to the premise, now
kernel-checked), and the recommended disposition is **RETIRE**, with the keep/delete boundary
enumerated below.

The task is read-only with respect to `FormalSystem/**` and `docs/**` by design, and that
constraint held: zero modifications outside `specs/**`.

---

## Section 1 — VERDICT: NO DEPENDENCY

**`decide`'s totality and correctness arguments do not route through any of the vacuous `_run`
theorems. The status row at `docs/theorem-index.md:113` is not overstated, indirectly or
otherwise.** Stated unhedged, as a retired open question rather than a null result.

Five independent pieces of machine evidence, each pointing at its section of
`probes/probe-evidence.md`:

| # | Evidence | Observation | Probe |
|---|----------|-------------|-------|
| 1 | Forward transitive closure, six entry points | `hits = []` for `decide`, `decideAuto`, `decideBlocking`, `isValid`, `isSatisfiable`, `sound_of_isValid`, against all nine `_run` theorems + `PostBlockingSettlesRun` + `PostBlockingSettles` + the `buildTableauAt_isSome_of_settlesRun` bridge. Closures 294-1338 constants. | Probe 3 (`DepTrace`) |
| 2 | Module-level reach | `constants from MintBound reached by decide: 0` | Probe 4 (`DepTrace2`) |
| 3 | Whole-environment reverse-dependency scan | `direct reverse-dependents across the whole FormalSystem env: 0` — under `import FormalSystem`, the root aggregator | Probe 5 (`RevDep`) |
| 4 | Module ordering | `DecisionProcedure` module idx `3724` < `MintBound` idx `3755` | Probe 4 |
| 5 | Name resolution | All twelve suspects and all six targets resolve; `DepTrace` `logError`s otherwise and emitted none | Probes 1, 3 |

**Why the separation is structural, not incidental.** `decide` (`DecisionProcedure.lean:176`)
calls `buildTableau φ_n tableauFuel fc` at a literal default `tableauFuel := 1000`, and on `none`
returns `.fuelExhausted` (`:199-200`). Every one of the nine concludes about
`buildTableauAt … .isSome` at a *derived* `mintAwareFuel`/`mintAwareFuelAt` figure. Probe 4
confirms both halves of the gap directly: `decide reaches buildTableauAt? false`,
`decide reaches mintAwareFuel? false`, `decide reaches mintAwareFuelAt? false`. The nine are
stated about a function `decide` never calls, at a fuel figure `decide` never computes.

**The durable reason, independent of today's import graph.** `decide` makes **no totality claim**
for a fuel bound to underwrite. Its own docstring says so in as many words
(`DecisionProcedure.lean:337-339`):

> `.fuelExhausted` is one of the four constructors it may return. No theorem rules
> `.fuelExhausted` out, and this docstring does not claim one does.

Fuel exhaustion is an *answer*, not a failure mode the library has promised to exclude. Even if a
future import were added, there is no claim on the `decide` side for a vacuous `_isSome` result to
prop up. This is the fact that makes the verdict robust rather than a snapshot of module ordering.

**A caution recorded for reuse.** `#print axioms` is not a dependency tracer. Probe 2 shows
`decide`, `sound_of_isValid`, **and the vacuous terminus itself** all reporting
`[propext, Classical.choice, Quot.sound]`. A `pcq` reading answers "is it sound?", never "what
does it rest on?". The forward-closure and reverse-scan probes (3-5) are what actually decide this
task's question; an axiom check alone would have been uninformative in both directions.

---

## Section 2 — Count correction: the vacuous set is NINE, not six

The dispatch's premise named "the terminus and its five siblings". The true figure is nine, and
the undercount has two distinct causes.

**The nine**, all in `MintBound.lean`, contiguous at `:12312-12487`:

| # | Name | Line | Fuel figure | Refuted hypothesis |
|---|------|------|-------------|--------------------|
| 1 | `buildTableauAt_isSome_of_budget_run` | 12312 | `mintAwareFuel` (un-`At`) | `PostBlockingSettlesRun` |
| 2 | `buildTableauAt_isSome_of_budget_of_run` | 12331 | `mintAwareFuel` (un-`At`) | **`PostBlockingSettles`** |
| 3 | `buildTableauAt_isSome_at_seed_run` | 12347 | `mintAwareFuel` (un-`At`) | `PostBlockingSettlesRun` |
| 4 | `buildTableauAt_isSome_of_budget_at_run` | 12369 | `mintAwareFuel` (un-`At`) | `PostBlockingSettlesRun` |
| 5 | `buildTableauAt_isSome_at_seed_at_run` | 12386 | `mintAwareFuelAt` | `PostBlockingSettlesRun` |
| 6 | `buildTableauAt_isSome_of_budget_selfGuarded_run` | 12407 | `mintAwareFuelAt` | `PostBlockingSettlesRun` |
| 7 | `buildTableauAt_isSome_at_seed_selfGuarded_run` | 12425 | `mintAwareFuelAt` | `PostBlockingSettlesRun` |
| 8 | `buildTableauAt_isSome_of_budget_fixed_run` (the terminus) | 12449 | `mintAwareFuelAt` | `PostBlockingSettlesRun` |
| 9 | `buildTableauAt_isSome_at_seed_fixed_run` | 12468 | `mintAwareFuelAt` | `PostBlockingSettlesRun` |

**Cause (a) — the un-`At` figure was never instantiated.** Task 463's
`postBlockingSettlesRun_terminusFuel_false` (`:12751`) refutes `PostBlockingSettlesRun` at the
`mintAwareFuelAt` figure. Rows 1-4 use the un-`At` `mintAwareFuel`, which 463 never covered. That
gap is now closed and **kernel-checked** in `probes/Widen.lean` (axioms `pcq`, no `sorry`):
`one_le_mintAwareFuel'` gives positivity of the un-`At` figure by the same
`fuelFigure_pos`/`mintPathBound` route, and `postBlockingSettlesRun_mintAwareFuel_false` then
applies `postBlockingSettlesRun_false_succ`. Six lines. Rows 1-4 are vacuous at `.Base` on the
same footing as the rest.

**Cause (b) — row 2 is a different and stronger case.**
`buildTableauAt_isSome_of_budget_of_run` carries `hpb : PostBlockingSettles fc`, the *unrestricted*
predicate, not the narrowed residual. `PostBlockingSettles` is refuted by
`postBlockingSettles_fuel_zero_false` (`:11636`) at **every frame class, including `.ZTime`**. So
row 2 is unconditionally vacuous at all four classes, while rows 1 and 3-9 are established vacuous
at `.Base`, `.Dense` and `.RTime` (via `postBlockingSettlesRun_false_succ` and its `_dense`/`_rtime`
variants at `:12823`/`:12829`) and are undecided — though equally undelivering, having zero
dependents — at `.ZTime`. That distinction should not be blurred, and C9 entry 25's `.ZTime`
caveat does not apply to row 2.

**Not in the set.** `MintBound.lean` carries **13** `_run`-suffixed declarations in total. Four
are unrelated and are explicitly NOT part of any delete set: `labelFinset_card_le_of_seed_run`
(`:2927`), `maxTime_monotone_along_run` (`:8316`), `nextTime_monotone_along_run` (`:8338`),
`saturateBlocked_multBranch_one_run` (`:12127`). The last of these is load-bearing for the
non-vacuity argument about the *pass* and must survive any retirement.

---

## Section 3 — Index adjudication: `docs/theorem-index.md:113-114`, NO EDIT

The two rows under `### Decidability` (heading at `:109`) were checked column by column against
observed fact. The plan's line numbers held: `:113` is the `decide` row, `:114` the
`sound_of_isValid` row.

**Row `:113` — `decide`**

| Column | Claim | Evidence | Verdict |
|--------|-------|----------|---------|
| Statement | "The tableau decision procedure" | Descriptive; asserts no totality, no completeness, no fuel bound | ACCURATE — and the wording is what protects it. It claims `decide` *is* the procedure, not that it always returns a verdict |
| Lean name | `FormalSystem.Metalogic.Decidability.decide` | Resolves in the environment (Probe 1) | ACCURATE |
| File | `.../Decidability/DecisionProcedure.lean` | `def decide` at `:176` | ACCURATE |
| Frame class | Base | `(fc : FrameClass := .Base)` in the signature (`:177`) | ACCURATE |
| Axioms | `pcq pinned:C14` | `#print axioms` -> `[propext, Classical.choice, Quot.sound]` (Probe 2) | ACCURATE |

**Row `:114` — `sound_of_isValid`**

| Column | Claim | Evidence | Verdict |
|--------|-------|----------|---------|
| Statement | "a valid verdict yields validity" | A conditional on the verdict, not a claim that a verdict is reached | ACCURATE |
| Lean name | `...Decidability.sound_of_isValid` | Resolves; closure 294 consts, `hits = []` (Probe 3) | ACCURATE |
| File | `.../Decidability/Correctness.lean` | `theorem sound_of_isValid` at `:107` | ACCURATE |
| Frame class | Base | consistent with the row above | ACCURATE |
| Axioms | `pcq pinned:C14` | `#print axioms` -> `pcq` (Probe 2) | ACCURATE |

**Decision: NO EDIT.** Ten of ten substantive columns check out. `docs/theorem-index.md` is
byte-identical to HEAD (`git diff --quiet -- docs/theorem-index.md` exits 0). The dispatch's
NO-DEPENDENCY branch mandates leaving the row untouched, and there is independently nothing to
correct: the row's statement column never made a totality claim, and `decide` never had one to
make.

---

## Section 4 — DISPOSITION: RETIRE the nine

The trace selects the first of the three dispositions. NO DEPENDENCY anywhere -> **retire**.

**Why retire rather than annotate.** The nine read as headline results — "the tableau
construction succeeds at the mint-aware fuel bound" — while establishing nothing, because their
hypothesis is unsatisfiable. In a publication-facing library that is worse than absent. A reader
meeting `buildTableauAt_isSome_of_budget_fixed_run` at `:12449` gets no local signal that `hpb` can
never be supplied; the refutation is ~300 lines further on at `:12751` and the register entry is
~3,100 lines away at `:15692`. Retirement is also unusually cheap here: Probe 5 puts the
reverse-dependent count at exactly zero across the whole environment, so nothing breaks.

**Why the other two dispositions are excluded.** Both are DEPENDS branches. "Mark vacuity at the
declaration site" is the DEPENDS-at-`.Base`/`.Dense`/`.RTime` remedy and presupposes a dependent
worth preserving the theorems for; there is none. "Complete `.ZTime`" is the DEPENDS-at-`.ZTime`
remedy and presupposes the fourth frame class is load-bearing; the trace shows nothing is
load-bearing on any of them, at any class.

**DELETE set** (all in `MintBound.lean`; line numbers verified at HEAD `2dc42ca11` and known to
drift):
- The nine theorems and their docstrings, `:12311-12487`.
- The block prose `/-! #### The termini, restated at the narrowed residual`, `:12288-12309`. It
  exists solely to introduce the nine and asserts "every restatement is a strengthening of its
  landed original", which is true but pointless once the strengthenings are gone.
- The forward reference at `:5194-5195`, inside the `PostBlockingSettles` docstring
  ("`buildTableauAt_isSome_of_budget_run` and its siblings are the termini stated at it, and
  `buildTableauAt_isSome_of_budget_of_run` certifies the strengthening") — rewrite, do not simply
  excise, since the surrounding sentence about `postBlockingSettlesRun_of_postBlockingSettles`
  fixing the direction stays true and is worth keeping.

**KEEP set** (explicitly out of scope for deletion; no item appears in both lists):
- `PostBlockingSettlesRun` and `PostBlockingSettles` themselves, and
  `postBlockingSettlesRun_of_postBlockingSettles`.
- The entire refutation apparatus: `postBlockingSettles_fuel_zero_false` (`:11636`),
  `postBlockingSettlesRun_false_succ_of` (`:12696`), `postBlockingSettlesRun_false_succ` (`:12721`),
  `postBlockingSettlesRun_terminusFuel_false` (`:12751`), and the `_dense`/`_rtime` variants
  (`:12823`, `:12829`).
- The `PostBlockingSettlesSeedRun` successor line.
- C9 register entries 22, 24 and 25 (`:15551`, `:15661`, `:15692`) — amended, not removed; see
  Brief A.
- The `/-! #### Non-vacuity of the narrowed residual` section (`:12490-12533`). It documents the
  measurement history of the *predicate*, and it already carries its own honest self-correction at
  `:12527-12533` ("And that warning was the right one: the residual is now refuted"). It survives
  the nine.
- `saturateBlocked_multBranch_one_run` (`:12127`) and
  `multBranch_one_length_lt_multSettledBranch` (`:12537`), which that section depends on.
- The three other unrelated `_run` declarations at `:2927`, `:8316`, `:8338`.

---

## Section 5 — Do NOT execute the `.ZTime` strengthening

`MintBound.lean`'s scoped note records a mechanical recipe for completing the `.ZTime` case: add
the `priorUZ`/`priorSZ` conclusions to the witness at `<0,0>`, `<0,1>`, `<1,0>`, `<1,1>`, then
re-run the same three `rfl` obligations at `.ZTime`. **Do not do it.**

Its only justification was the DEPENDS-at-`.ZTime` branch — the possibility that the fourth frame
class turned out to be load-bearing after all. The trace rules that out: zero dependents at any
frame class (Probe 5), zero reach from `decide` (Probes 3-4). Executing it would mean spending
expensive build time strengthening a refutation of a hypothesis carried only by theorems the
disposition recommends deleting. In the RETIRE branch it is polish on code that is then removed.

The deliberate consequence, stated rather than hidden: rows 1 and 3-9 remain *undecided* at
`.ZTime`. They are not thereby useful there — they have zero dependents at `.ZTime` as at every
other class — but "undecided at `.ZTime`" is the honest description, and any commit message or
register amendment must say that rather than claiming vacuity at all four. Row 2 is the exception:
it is unconditionally vacuous at all four via `postBlockingSettles_fuel_zero_false`.

---

## Section 6 — Follow-up briefs

Not created as tasks here, per the dispatch's "named, not attempted". Each is a ready-to-paste
`/task` description.

### Brief A — Retire the nine vacuous `_run` theorems

> Retire the nine vacuous `buildTableauAt_isSome_*_run` theorems in MintBound.lean (delete set,
> keep set and evidence in specs/549_.../summaries/01_decide-dependency-verdict-disposition-summary.md
> Section 4), land the two un-`At` widening lemmas from specs/549_.../probes/Widen.lean, and amend
> C9 register entries 24/25 for the corrected count of nine and row 2's all-four-class vacuity.

- **`file_scope`**: `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`
- **Dependency**: 463 — a `file_scope` serialization edge on the same 15,759-line file. Must not
  run concurrently with it.
- **Type**: `lean4`
- **Acceptance**: the nine are gone; `lake build` green; `#print axioms` unchanged for every
  surviving `Decidability` result; a re-run of `probes/RevDep.lean` naturally reports 0 because
  the suspect names no longer resolve — so the meaningful regression check is that
  `probes/DepTrace2.lean` still reports `constants from MintBound reached by decide: 0`.
- **Commit-message accuracy note**: rows 1 and 3-9 are established vacuous at `.Base`, `.Dense`
  and `.RTime` only, and are *undecided but equally undelivering, with zero dependents*, at
  `.ZTime`. Row 2 (`buildTableauAt_isSome_of_budget_of_run`) is unconditionally vacuous at all
  four. Do not flatten these into one claim.

**Amendment (a) — land the widening.** Move `one_le_mintAwareFuel'` and
`postBlockingSettlesRun_mintAwareFuel_false` from `probes/Widen.lean` into `MintBound.lean` (six
lines, already proved, axioms `pcq`) so the register's vacuity claim covers the un-`At`
`mintAwareFuel` figure and not only `mintAwareFuelAt`. Correct "its five `_run` siblings" to the
true count of nine wherever it appears. *This was deliberately not done in task 549* — not because
it is hard, but because `MintBound.lean` is owned by an in-flight task and the two would collide.

**Amendment (b) — record row 2 separately.** `buildTableauAt_isSome_of_budget_of_run` is vacuous
via `postBlockingSettles_fuel_zero_false` at all four frame classes, so entry 25's `.ZTime` caveat
does not apply to it. It currently reads as one of a uniform block; it is not.

### Brief B — Dependency-tracing recipe for the lean4 context (optional, low priority)

> Add a dependency-tracing recipe to the lean4 extension context: environment closure traversal,
> the module-index variant, the whole-environment reverse-dependency scan, and the warning that
> `#print axioms` is not a dependency tracer.

- **`file_scope`**: `agent-system/extensions/lean/context/project/lean4/patterns/dependency-tracing.md`
  — the **source store**, never `.claude/**` directly (`.claude/` is a regenerated deploy artifact;
  see `.claude/rules/source-store-deploy-boundary.md`).
- **Dependency**: none.
- **Type**: `meta`
- **Acceptance**: the four probe shapes in `specs/549_.../probes/` are reproduced as reusable
  templates, with the `#print axioms` caveat from Section 1 stated explicitly.

---

## Section 7 — Fallback if deletion is unwanted (an explicit user choice, not a default)

Recorded because the RETIRE recommendation removes nine named theorems from a publication-facing
library, and that is a call a human may want to make. **This is not the recommendation.** If the
nine are to be kept:

Add to each of the nine docstrings a vacuity notice at the declaration site, naming the refutation
by name — `postBlockingSettlesRun_terminusFuel_false` for rows 1 and 3-9, and
`postBlockingSettles_fuel_zero_false` for row 2 — stating the frame classes at which vacuity is
*established* (`.Base`, `.Dense`, `.RTime` for the former; all four for the latter) and that the
theorem is consequently unusable as a premise. The point of the notice is locality: the reader must
not have to travel 300 or 3,100 lines to learn that the hypothesis is unsatisfiable.

This fallback is strictly worse than retirement on the publication criterion — a reader still
meets nine headline-shaped results that deliver nothing — but it is strictly better than the
status quo, and it preserves the option of a later `.ZTime` completion.

---

## What Changed

- `specs/549_.../probes/probe-evidence.md` — created; verbatim output of six probes, HEAD sha,
  scope-hypothesis checks, load-bearing-number reproduction table, read-only baseline, final build
  result.
- `specs/549_.../probes/out/*.out` — created; raw unedited stdout+stderr per probe.
- `specs/549_.../summaries/01_...-summary.md` — created; this deliverable.
- `specs/549_.../handoffs/*.md` — created; phase checkpoints.
- **No file outside `specs/**` was created, modified, or deleted.** No Lean source, no
  `docs/theorem-index.md`. This is the intended end state of the NO-DEPENDENCY branch, not a
  shortfall.

## Decisions

- **NO EDIT to `docs/theorem-index.md`** — mandated by the NO-DEPENDENCY branch and independently
  correct on a ten-column check (Section 3).
- **RETIRE, not annotate** — selected by the trace result; the other two dispositions are DEPENDS
  branches (Section 4).
- **`.ZTime` strengthening explicitly excluded** — its only justification was the branch the trace
  ruled out (Section 5).
- **The `Widen.lean` widening was not landed into `MintBound.lean`** despite being proved and six
  lines long — a write collision with in-flight task 463 on a shared 15,759-line file, not proof
  difficulty. Deferred to Brief A amendment (a).
- **The count correction (six -> nine) is reported as a premise correction**, with the two distinct
  causes separated rather than merged (Section 2).

## Plan Deviations

- None (implementation followed plan). Three factual refinements were made where the plan flagged
  its own figures as hypotheses to check rather than facts to trust, exactly as its
  `Scope Hypothesis` blocks instruct:
  - Delete-set line range refined from `:12312-12488` to `:12311-12487` (the terminus docstring
    opens at `:12311`; the last theorem body ends at `:12487`).
  - Block-prose range refined from `:12290-12309` to `:12288-12309`.
  - `docs/theorem-index.md:113-114` confirmed unmoved; `MintBound.lean` terminus confirmed moved
    from 463's `:12199` to `:12449`.

## Verification

- Build: **Success** — `Build completed successfully (2592 jobs).`, exit 0. Run guarded and
  detached with `--no-share`, so this is a genuine build, not a replayed result (no
  `lake-build-guard: REPLAY:` marker). Zero `error:`, zero `warning:`, zero
  `declaration uses 'sorry'` lines in the output.
- Sorry count: **0** attributable to this task. Repo-wide baseline is `sorry_count: 160`, all
  under `FormalSystem/Boneyard/` (legacy quarantine, not a build target) and all pre-existing;
  zero outside `Boneyard/`. This task modified no Lean file.
- Vacuous count: **0** attributable. One repo-wide single-line pattern match,
  `Examples/TemporalStructures.lean:496` (`int_domain_universal … := trivial`), is an honest proof
  — the `Int` history's domain predicate genuinely holds everywhere — and is pre-existing.
- Axiom count: **0 added**, and the repo-wide count of actual `axiom` declarations in
  `FormalSystem/` is **0**. The twelve `^axiom ` grep hits are all false positives: wrapped prose
  lines in docstrings and READMEs beginning with the word "axiom". `probes/*.lean` are standalone
  `lake env lean` scripts, not members of any lakefile target, so they add nothing to the
  library's axiom or `sorry` surface.
- Tests: N/A (no Lean source changed). The build itself independently re-confirmed the axiom
  column: `MainResults.lean:254` emits `sound_of_isValid depends on axioms: [propext,
  Classical.choice, Quot.sound]` as a build-time obligation.
- Files verified: Yes — `git diff --quiet -- FormalSystem/` and `git diff --quiet -- docs/` both
  exit 0.

## Impacts

- An open question on the correctness of the project's decidability status claims is retired with
  machine evidence, rather than left as an unexamined risk into publication.
- The vacuity count in the C9 register is now known to be understated by three, with the gap
  kernel-checked rather than conjectured.
- The retirement of the nine is unblocked and shown to be zero-risk (zero reverse-dependents),
  which is the expensive fact a retirement task would otherwise have had to establish for itself.
- The `.ZTime` strengthening is retired as unnecessary, saving the build time the plan flagged as
  a coin-flip cost.
- Six reusable dependency-trace probes are committed and re-runnable in 14 seconds against warm
  oleans.

## Follow-ups

- Brief A — retire the nine, land the widening, amend C9 entries 24/25 (Section 6). Blocked on 463.
- Brief B — dependency-tracing recipe for the lean4 extension source store (Section 6). Optional.
- Section 7's annotate-in-place fallback remains available if a human prefers not to delete.

## References

- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/plans/01_decide-dependency-verdict-disposition.md`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/reports/01_trace-decide-dependency-vacuous-run.md`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/probe-evidence.md` and `probes/out/*.out`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/{Exists,Ax,DepTrace,DepTrace2,RevDep,Widen}.lean`
- `docs/theorem-index.md:109-114`
- `FormalSystem/Metalogic/Decidability/DecisionProcedure.lean:176-200`, `:337-339`
- `FormalSystem/Metalogic/Decidability/Correctness.lean:107`
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean:5194-5195`, `:11636`, `:12288-12309`, `:12311-12487`, `:12490-12533`, `:12751`, `:15551`, `:15661`, `:15692`
