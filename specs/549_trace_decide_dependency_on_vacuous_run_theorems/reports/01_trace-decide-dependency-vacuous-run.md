# Research Report: Task #549

**Task**: 549 - Trace whether `FormalSystem.Metalogic.Decidability.decide` depends on the six now-vacuous `_run` theorems, and correct the affected status claims if it does.
**Started**: 2026-09-07T15:47:58Z
**Completed**: 2026-09-07T16:12:00Z
**Effort**: ~25 min (4 Lean environment probes, 1 import-closure computation, 2 repo-wide greps)
**Dependencies**: 463 (its FALSE verdict on `PostBlockingSettlesRun` is this task's premise; also a `file_scope` serialization edge on `MintBound.lean`)
**Sources/Inputs**:
- Codebase (`FormalSystem/Metalogic/Decidability/**`, `docs/theorem-index.md`)
- Task 463 report `specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_postblockingsettlesrun-verdict-terminus-fuel.md`
- C9 register entry 25, `MintBound.lean:15692-15757`
- Four purpose-built Lean environment probes (kernel-level, listed in the Appendix)
**Artifacts**:
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/reports/01_trace-decide-dependency-vacuous-run.md`
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace.lean` (forward closure, 6 targets x 12 suspects)
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace2.lean` (module-level reach count)
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/RevDep.lean` (whole-environment reverse-dependency scan)
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean` (widens the vacuity from 6 to 8, kernel-checked)
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Ax.lean`, `.../Exists.lean` (axiom + existence controls)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **VERDICT: NO DEPENDENCY.** `FormalSystem.Metalogic.Decidability.decide` reaches **zero**
  constants from `Verified/Termination/MintBound.lean` — not the nine `_run` theorems, not the
  settlement predicates, not even `buildTableauAt` or `mintAwareFuelAt`. The row at
  `docs/theorem-index.md:113` is **untouched**. This is a real result: the open question is retired.
- The clearance is structural and therefore not fragile. `DecisionProcedure.lean` does not import
  `MintBound.lean` even transitively (75-module import closure, zero `Verified/Termination`
  modules), so the vacuous statements are not merely unused by `decide` — they are *unavailable*
  to it. The same holds for `sound_of_isValid`, `decideAuto`, `decideBlocking`, `isValid`,
  `isSatisfiable`.
- A whole-environment reverse-dependency scan under `import FormalSystem` finds **zero**
  dependents of the nine `_run` theorems outside the nine themselves. Nothing in the library
  rests on them; no documented claim anywhere is indirectly overstated through them.
- **Correction to the premise, upward.** The vacuous set is **eight**, not six, and a ninth is
  vacuous at *all four* frame classes. Task 463's "and its five `_run` siblings" undercounts:
  the four `mintAwareFuel` (un-`At`) siblings are equally refutable, which this task proved in the
  kernel (`postBlockingSettlesRun_mintAwareFuel_false`, `Widen.lean`, axioms `pcq` only).
- **DISPOSITION: RETIRE the nine.** The NO-DEPENDENCY branch selects it, and the reverse-dep scan
  makes it cost-free — nothing breaks. Section "Disposition Recommendation" names exactly what
  moves with them and what must *not*.
- The `.ZTime` strengthening described in `MintBound.lean`'s scoped note should **not** be
  executed. Its only justification was the DEPENDS-at-`.ZTime` branch, which the trace excludes.

## Context & Scope

**Researched**: whether `decide`'s totality or correctness argument routes through any of the
`_run` theorems that task 463 rendered vacuous by refuting `PostBlockingSettlesRun` at every
positive fuel at `.Base`, `.Dense` and `.RTime`.

**Method constraint from the dispatch**: "trace mechanically rather than by reading prose."
Honoured — every claim below is either a Lean environment computation or a `grep` over the tree.
No step of the verdict rests on reading a docstring.

**Read-only constraint**: honoured. Nothing under `FormalSystem/**` was edited; the probe files
live under `specs/549_.../probes/` and are not part of the library build. `docs/theorem-index.md`
was not edited, because the NO-DEPENDENCY branch forbids it.

**Note on stale line numbers**: task 463's report cites the terminus at `MintBound.lean:12199`.
The file has since grown; the terminus is now at **:12449** and `PostBlockingSettlesRun` at
**:12211**. All line numbers in this report are current as of commit `96c5c4a28`.

## Findings

### Codebase Patterns

#### 1. The vacuous set, enumerated precisely (and it is nine, not six)

Nine `_run` theorems sit in the restatement block `MintBound.lean:12312-12488`. Eight carry
`PostBlockingSettlesRun` directly; the ninth carries the strictly stronger, separately refuted
`PostBlockingSettles`.

| # | Theorem (all in `FormalSystem.Metalogic.Decidability`) | Line | Settlement hypothesis | Vacuous at |
|---|---|---|---|---|
| 1 | `buildTableauAt_isSome_of_budget_run` | 12312 | `PostBlockingSettlesRun fc (mintAwareFuel …)` | `.Base`, `.Dense`, `.RTime` |
| 2 | `buildTableauAt_isSome_at_seed_run` | 12347 | `PostBlockingSettlesRun fc (mintAwareFuel …)` | `.Base`, `.Dense`, `.RTime` |
| 3 | `buildTableauAt_isSome_of_budget_at_run` | 12369 | `PostBlockingSettlesRun fc (mintAwareFuel …)` | `.Base`, `.Dense`, `.RTime` |
| 4 | `buildTableauAt_isSome_at_seed_at_run` | 12386 | `PostBlockingSettlesRun fc (mintAwareFuel …)` | `.Base`, `.Dense`, `.RTime` |
| 5 | `buildTableauAt_isSome_of_budget_selfGuarded_run` | 12407 | `PostBlockingSettlesRun fc (mintAwareFuelAt …)` | `.Base`, `.Dense`, `.RTime` |
| 6 | `buildTableauAt_isSome_at_seed_selfGuarded_run` | 12425 | `PostBlockingSettlesRun fc (mintAwareFuelAt …)` | `.Base`, `.Dense`, `.RTime` |
| 7 | `buildTableauAt_isSome_of_budget_fixed_run` (**the terminus**) | 12449 | `PostBlockingSettlesRun fc (mintAwareFuelAt …)` | `.Base`, `.Dense`, `.RTime` |
| 8 | `buildTableauAt_isSome_at_seed_fixed_run` | 12468 | `PostBlockingSettlesRun fc (mintAwareFuelAt …)` | `.Base`, `.Dense`, `.RTime` |
| 9 | `buildTableauAt_isSome_of_budget_of_run` ("strengthening certificate") | 12331 | `PostBlockingSettles fc` | **all four classes** |

Rows 5-8 are the six-minus-two that task 463 had in view (`mintAwareFuelAt`, covered by
`one_le_mintAwareFuelAt` at :12730 feeding `postBlockingSettlesRun_terminusFuel_false` at :12751).

Rows 1-4 were **missed by 463's count**. Their fuel figure is `mintAwareFuel`, not
`mintAwareFuelAt`, and no `one_le_mintAwareFuel` lemma is landed — so the refutation was never
instantiated there. It goes through by exactly the same route: `mintPathBound` (:4976) ends in
`+ 1`, hence is positive, hence `fuelFigure_pos` (:3688) gives `1 ≤ mintAwareFuel …`, hence
`postBlockingSettlesRun_false_succ` (:12721) applies. Kernel-checked in `Widen.lean`:

```lean
theorem postBlockingSettlesRun_mintAwareFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base
        (mintAwareFuel U.card Tmax mintBudget D β)
```
`#print axioms` -> `[propext, Classical.choice, Quot.sound]`. No `sorry`.

Row 9 is the *most* vacuous of the lot and is worth stating separately: it carries the
unrestricted `PostBlockingSettles fc`, which `postBlockingSettles_fuel_zero_false` (:11636)
refutes at **every** frame class `fc`, `.ZTime` included, with no fuel-positivity side condition.
The "strengthening certificate" — whose stated job is to show the exchange loses nothing a caller
could ever have had — is therefore itself an implication from a false antecedent at all four
classes.

Not in the vacuous set, and explicitly cleared: `saturateBlocked_multBranch_one_run` (:12127),
`labelFinset_card_le_of_seed_run` (:2927), `maxTime_monotone_along_run` (:8316),
`nextTime_monotone_along_run` (:8338). These carry no settlement hypothesis.

#### 2. `decide` cannot reach them — the import closure already settles it

Transitive `import` closure of `FormalSystem/Metalogic/Decidability/DecisionProcedure.lean`:
**75 modules, of which zero are under `Verified/` or `Termination/`.** `MintBound.lean` enters
the library only through the aggregator `FormalSystem/Metalogic/Decidability.lean:23`, which is
*downstream* of `DecisionProcedure` (line 13), not upstream.

Module indices in the compiled environment confirm the ordering: `DecisionProcedure` is module
3724, `MintBound` is module 3755. A constant in a later module cannot occur in an earlier
module's declaration.

#### 3. The kernel-level forward trace, which is the actual deliverable

`DepTrace.lean` imports `FormalSystem.Metalogic.Decidability` (which pulls in *both*
`DecisionProcedure` and `MintBound`, so both sides are present in one environment), then computes
the transitive closure of used constants over the **type and value** of every reachable
declaration. Existence of all 6 targets and all 12 suspects was asserted first, so a typo could
not have produced a false clean bill of health.

| Target | Closure size | Hits among the 12 suspects |
|---|---|---|
| `Decidability.decide` | 1252 consts | **[]** |
| `Decidability.decideAuto` | 1338 consts | **[]** |
| `Decidability.decideBlocking` | 1260 consts | **[]** |
| `Decidability.isValid` | 1259 consts | **[]** |
| `Decidability.isSatisfiable` | 1260 consts | **[]** |
| `Decidability.sound_of_isValid` | 294 consts | **[]** |

Suspect list = the nine `_run` theorems above, plus `PostBlockingSettlesRun`,
`PostBlockingSettles`, and the bridge `buildTableauAt_isSome_of_settlesRun`.

`DepTrace2.lean` sharpens this from "no hits on a list" to a module-level statement:

```
constants from MintBound reached by decide: 0
```

Zero. Not "none of the nine" — none of the ~1,900 constants the module declares.

#### 4. Why `decide` was never in the neighbourhood: it uses a different engine entry point

`DepTrace2.lean` also reports which engine functions `decide` actually reaches:

| Constant | Reached by `decide`? |
|---|---|
| `buildTableau` | **yes** |
| `expandBranchWithFuel` | yes |
| `saturateBlocked` | yes |
| `buildTableauAt` | **no** |
| `mintAwareFuel` / `mintAwareFuelAt` | **no** |

Every one of the nine vacuous theorems concludes about `buildTableauAt … .isSome`. `decide`
(`DecisionProcedure.lean:176`) calls `buildTableau φ_n tableauFuel fc` — the un-`At` entry point,
at a caller-supplied literal `tableauFuel := 1000`, never at a derived `mintAwareFuel*` figure.
The two layers are about different functions at different fuel figures. The dispatch's weak prior
("a termination-side vacuity is likelier to break a fuel-bound argument than a correctness
argument") turns out to understate the separation: there is no shared subject matter at all.

#### 5. `decide` makes no totality claim that a fuel bound could underwrite

This is the reason the exposure could never have existed, and it is worth recording because it is
the durable fact, not an accident of the current import graph. `decide` is a plain total Lean
`def` whose return type `DecisionResult φ` has **`.fuelExhausted` and `.extractionFailed`
constructors**. Fuel exhaustion is an *answer*, not a gap:

```lean
match buildTableau φ_n tableauFuel fc with
| none => .fuelExhausted
| some tableau => …
```

There is nothing here for `buildTableauAt_isSome_*` to discharge. The entire point of the
`_isSome` family is to prove the `none` arm unreachable at a derived fuel figure — a claim
`decide`'s row never makes and `decide`'s type never asserts.

`#print axioms FormalSystem.Metalogic.Decidability.decide` ->
`[propext, Classical.choice, Quot.sound]`, so the row's `pcq pinned:C14` axiom column is also
accurate. Same for `sound_of_isValid`.

#### 6. Whole-environment reverse-dependency scan: nothing anywhere uses them

`RevDep.lean` imports `FormalSystem` (the root aggregator) and scans **every** non-internal
constant in the environment for a direct reference to any of the nine, over type and value:

```
direct reverse-dependents across the whole FormalSystem env: 0
```

The only uses of the nine are *among the nine* (rows 2 and 9 discharge via row 1; row 4 via row 3;
row 6 via row 5; row 8 via row 7), which the scan excludes by construction. The block is a closed
island.

### External Resources

No Mathlib search was required. The question is entirely internal to this library: the tools used
were the Lean `Environment` API (`Environment.find?`, `Expr.getUsedConstants`,
`Environment.getModuleIdxFor?`, `Environment.header.moduleNames`) driven from `run_cmd`. No
LeanSearch / Loogle / LeanFinder / state-search call was made, and none would have helped.

### Recommendations

1. **Leave `docs/theorem-index.md:113` exactly as it is.** No edit, on either the statement column
   or the axioms column. Both are accurate.
2. **Do not execute the `.ZTime` strengthening.** Its scoped note in `MintBound.lean` is a recipe
   for a branch this trace has excluded. Executing it would spend build time completing a witness
   for a predicate that is about to be retired.
3. **Retire the nine** (details below), as a separate task — this one is read-only.
4. **Amend the count in the register.** C9 entry 25 and task 463's report say "five siblings";
   the correct figure is eight direct carriers plus the `PostBlockingSettles` certificate. A
   published register that undercounts its own vacuity is a worse defect than the vacuity.
5. **Zero-sorry throughout.** Every claim in this report is kernel-checked with axioms
   `[propext, Classical.choice, Quot.sound]`. No approach recommended here requires a `sorry` or a
   new axiom; the retirement is a deletion, which cannot introduce either.

## Disposition Recommendation

**RETIRE the nine `_run` theorems** (`MintBound.lean:12312-12488`).

**Why the trace selects this branch.** The dispatch conditions RETIRE on "NO DEPENDENCY
anywhere". `RevDep.lean` establishes exactly that, at the strongest available scope: not "`decide`
doesn't use them" but "no constant in the entire `FormalSystem` environment uses them". The
publication argument in the dispatch then applies in full: a reader meeting
`buildTableauAt_isSome_of_budget_fixed_run` at :12449 reads a headline result — "the tableau
construction succeeds at the derived budget" — with no local signal that its hypothesis is
unsatisfiable at three of four frame classes, the refutation sitting ~3,300 lines downstream at
:12751 and its register entry ~3,250 lines beyond that at :15692.

**What moves with them, and what must not.** The distinction matters: the *theorems* are empty,
the *machinery around them* is not.

Delete (the nine, plus what becomes orphaned):
- Rows 1-9 of the table above, `MintBound.lean:12312-12488`.
- The block's introductory prose at :12290-12309 ("It costs no figure", the strengthening
  narrative) and the forward reference at :5194-5195, both of which describe only the nine.
- Nothing else. The scan says nothing else points at them.

Keep — these are live results, and deleting them would destroy the evidence for the deletion:
- `PostBlockingSettlesRun` (:12211) itself, `postBlockingSettlesRun_of_postBlockingSettles`
  (:12230), and `buildTableauAt_isSome_of_settlesRun` (the bridge, :12262).
- The whole refutation apparatus: `postBlockingSettlesRun_false_succ` (:12721),
  `postBlockingSettlesRun_terminusFuel_false` (:12751), `postBlockingSettlesRun_false_dense`
  (:12822), `postBlockingSettlesRun_false_rtime` (:12828), `one_le_mintAwareFuelAt` (:12730),
  and the `pbrWitnessBranch` / `pbrDoctoredTracker` witness machinery.
- The live successor line: `PostBlockingSettlesSeedRun` (:12881),
  `postBlockingSettlesSeedRun_of_postBlockingSettlesRun` (:12897),
  `buildTableauAt_isSome_of_settlesSeedRun` (:12908),
  `buildTableauAt_isSome_of_budget_fixed_seedRun` (:12941). This is the narrowing that replaces
  the retired block and is *not* known vacuous.
- C9 register entries 22, 24 and 25.

**Two amendments the retirement should carry.**

(a) *Widen entry 25's count.* Land `one_le_mintAwareFuel` and
`postBlockingSettlesRun_mintAwareFuel_false` (both proved in `Widen.lean`, six lines total,
kernel-checked) so the register's vacuity claim covers the un-`At` figure too, then correct
"its five `_run` siblings" to the true count. Without this, a future reader restating a theorem
at `mintAwareFuel` has no landed refutation to consult and may repeat the error.

(b) *Record row 9 separately.* `buildTableauAt_isSome_of_budget_of_run` is vacuous at **all four**
classes via `postBlockingSettles_fuel_zero_false`, `.ZTime` included. Entry 25's `.ZTime` caveat
("at `.ZTime` the witness leaves `priorUZ`/`priorSZ` applicable … completing that class is
mechanical") is about the `PostBlockingSettlesRun` witness only and does not apply to row 9.

**Why not the other two dispositions.** DEPENDS-at-`.Base`/`.Dense`/`.RTime` (mark vacuity at the
declaration site) and DEPENDS-at-`.ZTime` (complete the witness) both presuppose a dependent that
needs the statements to survive in some form. There is no dependent. Marking vacuity at the
declaration site is strictly worse than deletion here: it preserves nine headline-shaped theorems
that establish nothing, each now carrying a paragraph explaining why it establishes nothing, in a
file that is already 15,700 lines.

**If the user prefers not to delete**, the fallback is disposition (b) — a vacuity marker in each
of the nine docstrings, cross-referencing `postBlockingSettlesRun_terminusFuel_false` by name and
line. This is the safe-but-inferior option and should be an explicit choice, not a default.

## Decisions

- **D1**: Treated the dispatch's "six" as a figure to verify rather than consume, since the
  dispatch itself asked for precise enumeration. Verifying it found the undercount. Recorded as an
  upward correction to the premise rather than silently adopting the larger number.
- **D2**: Used a kernel-level `Environment` traversal rather than `lean_references` on each of the
  nine. `lean_references` reports *syntactic* references in open files; the closure traversal
  reports what the elaborated proof terms actually contain, which is what "depends on" means. Both
  were run in effect (grep = the syntactic check, `RevDep.lean` = the semantic one) and agree.
- **D3**: Widened the target set beyond `decide` to `decideAuto`, `decideBlocking`, `isValid`,
  `isSatisfiable` and `sound_of_isValid`. The dispatch asked only about `decide`, but a NO verdict
  on `decide` alone would leave the neighbouring index row (`:114`, `sound_of_isValid`) untraced
  for the sake of one extra line of probe code.
- **D4**: Did not edit `docs/theorem-index.md`. The NO-DEPENDENCY branch of the dispatch's binary
  verdict explicitly forbids it.
- **D5**: Did not run a full `lake build`. Nothing under `FormalSystem/**` was modified, so the
  build state is unchanged; the probes were elaborated individually against the existing oleans
  via `lake env lean`, which is the stronger check for this purpose (it type-checks the probe
  against the real compiled environment).

## Risks & Mitigations

- **Risk**: The closure traversal misses a dependency routed through a compiler-generated
  auxiliary (equation lemma, `_unsafe_rec`, structure projection) that `getUsedConstants` on the
  main declaration does not expose.
  **Mitigation**: The module-level count in `DepTrace2.lean` is immune to this — it asks how many
  constants *from `MintBound`'s module index* appear anywhere in `decide`'s closure, and the
  answer is 0. Backed independently by the import closure (§2): a module not in the import graph
  contributes no constants by any route, generated or not.
- **Risk**: The verdict is read as permanent. It is not — it is a fact about the current import
  graph, and someone could later import `Verified/Termination/MintBound` into the
  `DecisionProcedure` line.
  **Mitigation**: Retiring the nine removes the hazard at the source. Until then, the ordering
  fact (`DecisionProcedure` = module 3724 < `MintBound` = 3755) is a cheap regression check; the
  probes are retained in `specs/549_.../probes/` and are re-runnable in one command.
- **Risk**: Retirement deletes something that is non-vacuous at `.ZTime` for rows 1-8. At `.ZTime`
  the `PostBlockingSettlesRun` refutation witness fails its first obligation, so those eight are
  *not established* vacuous there.
  **Mitigation**: Nor are they established non-vacuous — nobody has shown `PostBlockingSettlesRun
  .ZTime fuel` holds at any positive fuel, and entry 25 records the positive direction as
  prohibitive. Combined with zero dependents, the eight deliver nothing at `.ZTime` either. Row 9
  is unconditionally vacuous at `.ZTime` regardless. Whoever executes the retirement should state
  this in the commit message rather than let it pass silently.
- **Risk**: The follow-up retirement task collides with task 463 on `MintBound.lean`.
  **Mitigation**: Serialize behind 463, exactly as this task was. The retirement must be its own
  task with `file_scope` on `MintBound.lean`; it is named here, not attempted.

## Tactic Survey Results

Not applicable in the usual sense — no proof goal was under construction. The one proof obligation
that arose (widening the vacuity to the un-`At` figure) was discharged first-try by transcribing
the existing `postBlockingSettlesRun_terminusFuel_false` proof skeleton, so no tactic search was
needed.

| Goal | Tactic | Result | Premises/Config |
|------|--------|--------|-----------------|
| `1 ≤ mintAwareFuel Ucard Tmax mintBudget D β` | `fuelFigure_pos (by simp only [mintPathBound]; omega)` | success | reused verbatim from `one_le_mintAwareFuelAt` (:12730) |
| `¬ PostBlockingSettlesRun .Base (mintAwareFuel …)` | `obtain … Nat.exists_eq_succ_of_ne_zero; rw [hn]; exact postBlockingSettlesRun_false_succ n` | success | reused verbatim from `postBlockingSettlesRun_terminusFuel_false` (:12751) |

## Context Extension Recommendations

- **Topic**: Kernel-level dependency tracing as a repeatable operation.
- **Gap**: `context/project/lean4/` documents the lean-lsp MCP tools but has no recipe for the
  question "does declaration X transitively depend on declaration Y?". `#print axioms` cannot
  answer it (it reports axioms, not declarations), and `lean_references` answers only the
  syntactic version. This task had to write the traversal from scratch, and it is the third
  vacuity/dependency question this repository has faced.
- **Recommendation**: Add `context/project/lean4/patterns/dependency-tracing.md` carrying the
  `run_cmd` + `Expr.getUsedConstants` closure recipe, the module-index variant (the one that is
  robust against compiler-generated auxiliaries), the whole-environment reverse-dependency scan,
  and the standing warning that `#print axioms` is not a dependency tracer. The four probe files
  in `specs/549_.../probes/` are ready-made templates.

## Appendix

### Probe commands (all re-runnable from the repo root)

```
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace.lean
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/DepTrace2.lean
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/RevDep.lean
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Widen.lean
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Ax.lean
lake env lean specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/Exists.lean
```

### Greps run

- `grep -rn "<each of the nine names>" --include=*.lean .` -> occurrences confined to
  `MintBound.lean` (declaration sites, four intra-block discharges, and prose).
- `grep -rn "buildTableauAt\|isSome_of_budget\|PostBlockingSettles" docs/ README.md` -> **zero
  hits**, independently confirming the dispatch's "context already established" line at the level
  of the underlying function and predicate, not just the `_run` suffix.
- `grep -rn "Termination.MintBound" --include=*.lean .` -> importers are the aggregator
  `FormalSystem/Metalogic/Decidability.lean`, six `Tests/BimodalTest/*Probe.lean` files (prose
  references only), and prior-task scratch files under `specs/`.

### Import-closure computation

Python transitive walk over `import FormalSystem.*` lines starting from
`FormalSystem.Metalogic.Decidability.DecisionProcedure`: 75 modules reached, zero matching
`MintBound` or `Termination`.

### Key source locations (current line numbers)

- `PostBlockingSettlesRun` — `MintBound.lean:12211`
- The bridge `buildTableauAt_isSome_of_settlesRun` — `:12262`
- The nine `_run` restatements — `:12312-12488` (terminus at `:12449`)
- `one_le_mintAwareFuelAt` / `postBlockingSettlesRun_terminusFuel_false` — `:12730` / `:12751`
- `postBlockingSettlesRun_false_succ` — `:12721`; `_false_dense` / `_false_rtime` — `:12822` / `:12828`
- `postBlockingSettles_fuel_zero_false` — `:11636`
- `PostBlockingSettlesSeedRun` and successors — `:12881`, `:12897`, `:12908`, `:12941`
- C9 register entry 25 — `:15692-15757`
- `mintPathBound` / `mintAwareFuel` / `mintPathBoundAt` / `mintAwareFuelAt` / `fuelFigure_pos`
  — `:4976` / `:4983` / `:9858` / `:9864` / `:3688`
- `decide` — `DecisionProcedure.lean:176`; the index row — `docs/theorem-index.md:113`
