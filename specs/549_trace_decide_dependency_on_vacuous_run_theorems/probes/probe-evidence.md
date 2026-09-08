# Probe Evidence: Task #549 dependency trace

Verbatim, re-runnable machine evidence for the binary verdict of task 549. Every number quoted
in `summaries/01_decide-dependency-verdict-disposition-summary.md` traces to a section here.

## Provenance

- **HEAD at capture**: `2dc42ca11713f4795cb1d38cf23a82e9ea7b7781`
- **Last commit touching `MintBound.lean`**: `2cbe7d66f` (2026-09-07) —
  `task 463 phase 4-6: frame-class record, the named narrowing, and C9 entry 25`
- **Capture date**: 2026-09-07
- **Toolchain**: repo `lean-toolchain` pin (Lean v4.33.0-rc1, Mathlib tag `v4.33.0-rc1`)
- **Invocation form**: `lake env lean <probe>` from the repo root, elaborating against existing
  `.olean` artifacts. All six probes exited `0`; total wall time 14s (17:00:37 -> 17:00:51).
- **`sorry`/`admit` in probe sources**: none (`grep -n "sorry\|admit" probes/*.lean` -> no match).
- **`error` in probe output**: none (`grep -in error probes/out/*.out` -> no match). This matters
  for `DepTrace.lean` specifically, which `logError`s on any suspect or target name that fails to
  resolve — a silent clean bill of health from a typo is therefore ruled out.

Raw, unedited stdout+stderr for each probe is also retained as a separate file under
`probes/out/{Exists,Ax,DepTrace,DepTrace2,RevDep,Widen}.out`; the blocks below reproduce those
files byte for byte.

## Scope hypotheses checked before quoting (Phase 1 requirement)

| Hypothesis (from plan) | Check | Result |
|---|---|---|
| Six probe files under `probes/` | `ls probes/*.lean` | CONFIRMED — `Exists`, `Ax`, `DepTrace`, `DepTrace2`, `RevDep`, `Widen` |
| Nine vacuous `_run` theorems at `MintBound.lean:12312-12488` | `grep -n '^theorem .*_run\b'` | CONFIRMED — nine `buildTableauAt_isSome_*_run` at `12312, 12331, 12347, 12369, 12386, 12407, 12425, 12449, 12468`; terminus `buildTableauAt_isSome_of_budget_fixed_run` at `:12449` |
| `docs/theorem-index.md:113` is the `decide` row | `awk NR==113` | CONFIRMED — `:113` = `decide`, `:114` = `sound_of_isValid`, under `### Decidability` at `:109` |

`MintBound.lean` is 15,759 lines and carries **13** `_run`-suffixed declarations in total. Four
are unrelated to the vacuous block and are NOT part of any delete set:
`labelFinset_card_le_of_seed_run` (`:2927`), `maxTime_monotone_along_run` (`:8316`),
`nextTime_monotone_along_run` (`:8338`), `saturateBlocked_multBranch_one_run` (`:12127`).
The vacuous set is the nine contiguous `buildTableauAt_isSome_*_run` theorems only.

Task 463's report cited the terminus at `:12199`; it is now at `:12449`. Line numbers in this
file are known-stale on contact — every probe here resolves **names**, never line numbers.

---

## Probe 1 — `Exists.lean`: The suspect and target names resolve under the root aggregator

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Exists.lean
```

**Output (verbatim, unedited)**

```
FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_fixed_run exists under `import FormalSystem`: true
FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_run exists under `import FormalSystem`: true
FormalSystem.Metalogic.Decidability.decide exists under `import FormalSystem`: true
```

**What this establishes**: Establishes that the trace is being run against real, present declarations. A trace over a misspelled name returns a vacuously clean result; this rules that failure mode out for the terminus, one sibling, and the target `decide`.

---

## Probe 2 — `Ax.lean`: Kernel axiom dependencies of the two indexed decidability results

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Ax.lean
```

**Output (verbatim, unedited)**

```
'FormalSystem.Metalogic.Decidability.decide' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Decidability.sound_of_isValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_fixed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

**What this establishes**: Both `decide` and `sound_of_isValid` depend on exactly `[propext, Classical.choice, Quot.sound]` — the `pcq` set. No `sorryAx`, no project-local axiom. This is the observed fact that the `Axioms` column of `docs/theorem-index.md:113-114` (`pcq pinned:C14`) is adjudicated against in Section 3 of the summary. Note the third line: the vacuous terminus *also* reports `pcq` — `#print axioms` is a soundness check, not a dependency tracer, and cannot by itself answer this task's question. That is why probes 3-5 exist.

---

## Probe 3 — `DepTrace.lean`: Forward transitive constant closure: six targets against twelve suspects

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace.lean
```

**Output (verbatim, unedited)**

```
FormalSystem.Metalogic.Decidability.decide: closure = 1252 consts; hits = []
FormalSystem.Metalogic.Decidability.decideAuto: closure = 1338 consts; hits = []
FormalSystem.Metalogic.Decidability.decideBlocking: closure = 1260 consts; hits = []
FormalSystem.Metalogic.Decidability.isValid: closure = 1259 consts; hits = []
FormalSystem.Metalogic.Decidability.isSatisfiable: closure = 1260 consts; hits = []
FormalSystem.Metalogic.Decidability.sound_of_isValid: closure = 294 consts; hits = []
```

**What this establishes**: THE LOAD-BEARING PROBE. Full transitive closure over the value *and* type of every reachable declaration, from each of the six decision-procedure entry points, intersected against the nine `_run` theorems plus `PostBlockingSettlesRun`, `PostBlockingSettles`, and the `buildTableauAt_isSome_of_settlesRun` bridge. Every target: `hits = []`. Closures range 294-1338 constants, so the traversal is doing real work rather than terminating early.

---

## Probe 4 — `DepTrace2.lean`: Module-level reach and the engine-function breakdown

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace2.lean
```

**Output (verbatim, unedited)**

```
decide reaches FormalSystem.Metalogic.Decidability.buildTableauAt? false  (exists: true)
decide reaches FormalSystem.Metalogic.Decidability.buildTableau? true  (exists: true)
decide reaches FormalSystem.Metalogic.Decidability.expandBranchWithFuel? true  (exists: true)
decide reaches FormalSystem.Metalogic.Decidability.saturateBlocked? true  (exists: true)
decide reaches FormalSystem.Metalogic.Decidability.mintAwareFuelAt? false  (exists: true)
decide reaches FormalSystem.Metalogic.Decidability.mintAwareFuel? false  (exists: true)
constants from MintBound reached by decide: 0
DecisionProcedure module idx: some (3724), MintBound idx: 3755
```

**What this establishes**: Strengthens probe 3 from "not these twelve names" to "not this module at all": `constants from MintBound reached by decide: 0`. The engine breakdown gives the mechanism — `decide` reaches `buildTableau` but NOT `buildTableauAt`, and reaches neither `mintAwareFuel` nor `mintAwareFuelAt`. The nine vacuous theorems all conclude about `buildTableauAt … .isSome` at a derived `mintAwareFuel*` figure, so they are stated about a function and a fuel figure `decide` never touches. The module indices (`DecisionProcedure` 3724 < `MintBound` 3755) show the separation is structural: `MintBound` is elaborated strictly after `DecisionProcedure`, so no dependency in this direction is even expressible without a new import.

---

## Probe 5 — `RevDep.lean`: Whole-environment reverse-dependency scan of the nine

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/RevDep.lean
```

**Output (verbatim, unedited)**

```
direct reverse-dependents across the whole FormalSystem env: 0
```

**What this establishes**: The converse direction, and the broadest check of the six: it iterates every non-internal constant in the entire `FormalSystem` environment (under `import FormalSystem`, the root aggregator) and reports any that names one of the nine in its type or value. Zero. The nine have no dependents anywhere in the library — not just none on the `decide` path. This is what makes the RETIRE disposition cheap.

---

## Probe 6 — `Widen.lean`: The count correction, kernel-checked

**Command**

```
$ lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean
```

**Output (verbatim, unedited)**

```
'FormalSystem.Metalogic.Decidability.postBlockingSettlesRun_mintAwareFuel_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

**What this establishes**: Task 463's refutation was instantiated at the `mintAwareFuelAt` figure. Rows 1-4 of the nine use the un-`At` `mintAwareFuel` figure, which 463 never covered. `Widen.lean` closes that gap in six lines: `one_le_mintAwareFuel'` gives positivity of the un-`At` figure by the same `fuelFigure_pos`/`mintPathBound` route, and `postBlockingSettlesRun_mintAwareFuel_false` then refutes `PostBlockingSettlesRun` there via `postBlockingSettlesRun_false_succ`. Axioms `pcq`, no `sorry` — so the widening is machine-checked, not asserted. **This result is deliberately NOT landed into `MintBound.lean`** (see the summary's Non-Goals and Brief A amendment (a)).

---

## The four load-bearing numbers — reproduction check

The plan names four numbers whose reproduction is the condition for the NO-DEPENDENCY branch.
All four reproduce against HEAD `2dc42ca11`, and each appears in the captured output above rather
than only in this table's prose.

| # | Number | Expected (research) | Observed (this capture) | Source block |
|---|--------|---------------------|-------------------------|--------------|
| 1 | Suspect hits, all six traced targets | 0 | `hits = []` on all six lines | Probe 3 |
| 2 | Constants from `MintBound` reached by `decide` | 0 | `constants from MintBound reached by decide: 0` | Probe 4 |
| 3 | Direct reverse-dependents of the nine, whole env | 0 | `direct reverse-dependents across the whole FormalSystem env: 0` | Probe 5 |
| 4 | `Widen.lean` axioms | `[propext, Classical.choice, Quot.sound]` | `[propext, Classical.choice, Quot.sound]` | Probe 6 |

No probe reproduced a *different* number, so the plan's DEPENDS-branch contingency
("a non-zero hit anywhere -> stop, flip the verdict, mark `[BLOCKED]`") was not triggered.

The closure sizes did shift slightly from the research run (research reported 294-1338; this
capture reports `decide` 1252, `decideAuto` 1338, `decideBlocking` 1260, `isValid` 1259,
`isSatisfiable` 1260, `sound_of_isValid` 294) — consistent with ordinary library churn between
runs. The load-bearing quantity is the intersection, which is empty in both runs.

---

## Read-only compliance baseline (Phase 2)

Captured **before** any write by this task, so a later diff cannot be misattributed to it.

**HEAD**: `2dc42ca11713f4795cb1d38cf23a82e9ea7b7781`

**`git status --short` at task start**

```
 M .claude-extensions.json
 D specs/433_discharge_postblockingsettles_residual/.return-meta.json
 D specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/.return-meta.json
 M specs/549_trace_decide_dependency_on_vacuous_run_theorems/.return-meta.json
 M specs/549_trace_decide_dependency_on_vacuous_run_theorems/plans/01_decide-dependency-verdict-disposition.md
 M specs/TODO.md
 M specs/events.jsonl
 M specs/state.json
```

**Pre-existing dirty paths not owned by this task** (named so Phase 6's re-audit does not charge
them to task 549): `.claude-extensions.json`, `specs/433_.../.return-meta.json` (deleted),
`specs/463_.../.return-meta.json` (deleted), `specs/TODO.md`, `specs/events.jsonl`,
`specs/state.json`. The two `specs/549_...` entries are this dispatch's own orchestration writes
(early metadata, plan phase markers).

**Protected-tree checks**

| Check | Command | Result |
|-------|---------|--------|
| No `FormalSystem/` modification | `git diff --quiet -- FormalSystem/` | exit 0 (CLEAN) |
| No `docs/theorem-index.md` modification | `git diff --quiet -- docs/theorem-index.md` | exit 0 (CLEAN) |
| Zero entries under `FormalSystem/`, `docs/`, `latex/`, `typst/`, `Tests/` in porcelain | `git status --porcelain` | CONFIRMED — none of the eight entries is under any of those roots |

The probe files under `probes/*.lean` are standalone scripts run with `lake env lean`. They are
not members of any `lakefile` target and are never compiled by `lake build`, so they add nothing
to the library's axiom or `sorry` surface.
