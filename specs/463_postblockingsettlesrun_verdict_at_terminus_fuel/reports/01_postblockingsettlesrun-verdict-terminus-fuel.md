# Research Report: Task #463

**Task**: 463 - Decide `PostBlockingSettlesRun fc (mintAwareFuelAt U.card Tmax mintBudget D beta)` at the terminus's own fuel figure
**Started**: 2026-09-07T00:00:00Z
**Completed**: 2026-09-07T00:00:00Z
**Effort**: research complete; implementation ~1 phase (transcribe a verified witness, add C9 entry)
**Dependencies**: 462 (file_scope serialization on MintBound.lean only; no mathematical dependency)
**Sources/Inputs**: - Codebase (MintBound.lean, Saturation.lean, Tableau.lean, SignedFormula.lean), lean-lsp/`lake env lean` executable probes, no external literature source
**Artifacts**: - specs/463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_postblockingsettlesrun-verdict-terminus-fuel.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **VERDICT: FALSE.** `PostBlockingSettlesRun fc fuel` is refutable at **every** `fuel >= 1`, hence
  at the terminus's own figure `mintAwareFuelAt U.card Tmax mintBudget D beta` for **all** parameter
  values (that figure is always `>= 1`; see "The fuel figure is always positive" below).
- The refutation is **already machine-checked, sorry-free and axiom-free** in a scratch file against
  the built `MintBound.olean`. `#print axioms` on the refutation theorem reports exactly
  `[propext, Classical.choice, Quot.sound]`. Verified at `FrameClass.Base`, `.Dense` and `.RTime`;
  `.ZTime` needs two extra witness formulas (diagnosed below, mechanical).
- **The defect is a *second* over-quantification, in a different argument than the one task 433
  repaired.** `PostBlockingSettlesRun` narrowed `(ob, oOrd, fuel)` to run-produced pairs but left
  `expandBranchWithFuel`'s **`EventualityTracker` argument `tr`** universally quantified. A tracker
  no run ever threads makes `expandBranchWithFuel` report `.saturated` on a branch that the
  settlement test — which recomputes its blocked set with `armTracker`, seeded from `empty` — still
  reports outstanding work on. The tracker is the *only* input the two blocked-set computations do
  not share, and it is provably load-bearing here: with `tr := EventualityTracker.empty` the same
  witness does **not** refute anything (checked).
- **Consequence, stated plainly.** `buildTableauAt_isSome_of_budget_fixed_run` (:12199) and its five
  `_run` siblings carry a hypothesis that is **false** at `fc = .Base`, `.Dense` and `.RTime`. They
  are vacuous there, not merely unproved.
- **Recommended next step (minimal further narrowing, non-vacuous, bridge-preserving):** fix the four
  arguments the terminus itself always instantiates at their defaults —
  `tr := EventualityTracker.empty`, `ap := {}`, `bu := 0`, `ord := TimeOrdering.empty` — leaving
  `b`, `ob`, `oOrd`, `oAp`, `mb`, `satBr`, `satOrd` quantified. `buildTableauAt_isSome_of_settlesRun`
  survives that narrowing verbatim, because `buildTableauAt` passes exactly those defaults.
- **Honest caveat, recorded rather than glossed:** that narrowing closes *this* refutation. It is
  **not** shown to make the predicate true. A second, structurally independent gap is named below
  ("The gap the narrowing does not obviously close") and is unprobed.

## Context & Scope

Researched: whether `PostBlockingSettlesRun fc (mintAwareFuelAt U.card Tmax mintBudget D beta)`
(MintBound.lean:11961) is provable, refutable, or undecided by available means, as a refute-first
binary gate in the style of tasks 432/433/436.

Consumed without re-derivation, per the dispatch:

- `PostBlockingSettles fc` (:5200) is refuted (`postBlockingSettles_fuel_zero_false` :11636,
  `postBlockingSettles_fuel_gap_false` :11734, `postBlockingSettles_gap_at_every_fuel` :11706).
- `PostBlockingSettlesAt fc` (:11539) holds outright (`postBlockingSettlesAt_holds` :11721); the
  bridge from `saturateBlocked ... = some (.inr _)` to its antecedents does not go through.
- Task 433 proved the only typechecking output-branch bridge carries a refutable hypothesis
  (`postBlockingExitSettled_false` :12013). Not re-attempted.

Constraints honoured: no `ArmSettlement` discharge; no edits to Saturation.lean / Tableau.lean /
Fuel.lean (read-only, public interface only); nothing from the C9 register re-attempted; no `sorry`,
no new axiom, no vacuous discharge.

## Findings

### Codebase Patterns

**The predicate, and which of its binders are free.** `PostBlockingSettlesRun` (:11961) quantifies

```
forall (b ob : Branch) (ord oOrd : TimeOrdering) (tr : EventualityTracker) (ap oAp : AppliedSet)
       (mb bu : Nat) (satBr : Branch) (satOrd : TimeOrdering),
  expandBranchWithFuel b fuel ord fc tr ap mb bu = some (.inr (ob, oOrd, oAp)) ->
  saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) ->
  findUnexpandedUnblockedWith satBr satOrd fc (blockedTimes satBr satOrd fc (armTracker satBr)) = none
```

Task 433's narrowing restricted `(ob, oOrd)` to pairs a run at *this* fuel returned open. It did not
restrict `tr`, `ap`, `mb`, `bu`, `b` or `ord`. Of those, `ap` is inert (Tableau.lean:2947
`expandOnceUnblockedWithApplied` is deprecated in substance and *ignores* its applied set) and
`mb`/`bu` only gate a `none` result. **`tr` is not inert.**

**Why `tr` is the exact lever.** The two blocked-set computations that must agree are

- `blockedTimes b ord fc tracker'` inside `expandOnceUnblocked` (Tableau.lean:2284), where
  `tracker' = fulfillEventualities b (registerEventualities b tr)` (Saturation.lean:816);
- `blockedTimes satBr satOrd fc (armTracker satBr)`, with
  `armTracker b = fulfillEventualities b (registerEventualities b EventualityTracker.empty)`
  (Saturation.lean:711).

They share `b`, `ord`, `fc`. They differ **only** in the tracker seed. And blocking is *monotone in
pending entries at the ancestor*: `isTemporallyBlockedSaturated` (Tableau.lean:2117) conjoins
`allEventualitiesFulfilledOrDuplicated tracker t t_anc` (SignedFormula.lean:834), which asks that
every eventuality pending at `t` have **some** pending entry with the same event formula, same
`isUntil`, at time `t_anc`. Adding a pending entry at `t_anc` therefore makes blocking fire *more*
often. Since `tracker' ⊇ armTracker b` always, a doctored `tr` yields a **strictly larger** blocked
set — the engine skips a time the settlement test still inspects.

Two further facts make the exploit reachable:

- `fulfillEventualities` (Saturation.lean:308) discharges `e` only when `T e.formula` occurs at
  `e.label.world` at a time `!= e.label.time`. A doctored entry parked at an otherwise-unused world
  is never discharged.
- `Branch.timeType` (SignedFormula.lean, `isSubsetBlocked` :649) **ignores the world component**, so
  the subset half of blocking can be satisfied across worlds while fulfillment (world-sensitive)
  is not.

**Why `saturateBlocked` cannot repair it.** `expandOnceNoFresh` (Tableau.lean:2335) skips any
candidate whose rule mints a fresh label or lengthens the ordering. `untlPos` mints a time, so the
witness formula is invisible to the post-blocking pass, and `saturateBlocked_eq_self_of_noFresh_saturated`
(:11653) then hands the branch straight back **at every fuel**. This is the same mechanism as
`postBlockingSettles_fuel_gap_false`, reused rather than rebuilt.

### External Resources

None consulted. The verdict is decided entirely from the repository's own definitions; no Mathlib
lemma, no LeanSearch/Loogle/LeanFinder query, and no literature source was needed or used.

### Recommendations

**1. Land the refutation (a sorry-free path exists and is already verified).**

The witness is a 29-formula branch `W`, a 5-time ordering `ordW`, and a one-entry doctored tracker
`trBad`. Full source is in the Appendix; it compiles today against the built `MintBound.olean`.

The five obligations and how each discharges:

| Obligation | Proof |
|---|---|
| `findClosure W fc = none` | `cases fc <;> rfl` |
| `expandOnceNoFresh W ordW fc = (.saturated, ordW)` | `rfl` |
| `saturateBlocked W f ordW fc = some (.inr (W, ordW))`, every `f` | existing `saturateBlocked_eq_self_of_noFresh_saturated` |
| `expandBranchWithFuel W (n+1) ordW fc trBad {} 100 0 = some (.inr (W, ordW, {}))` | `rw [expandBranchWithFuel]; norm_num; rfl` — **one** unfold, no recursive call on this path |
| `findUnexpandedUnblockedWith W ordW fc (blockedTimes W ordW fc (armTracker W)) = some (T(p untl q)@<9,4>)` | `rfl` |

giving

```
theorem postBlockingSettlesRun_false_Base (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base (n+1)
```

`#print axioms` -> `[propext, Classical.choice, Quot.sound]`. No `sorry`.

The `expandBranchWithFuel` obligation is worth flagging as the one register entry 24 called out as
expensive ("well-founded recursion, does not reduce definitionally"). It is cheap **here** precisely
because the witness is returned at the *first* step: `rw [expandBranchWithFuel]` unfolds once and the
`.saturated` arm closes it. No engine step is transcribed, and no equation lemma is unfolded per
step. This is what makes the refutation a kernel proof rather than a `#guard_msgs` measurement — a
qualitative improvement over what entry 24 records as available.

**2. Instantiate at the terminus's own figure.** `mintPathBound` (:4976) ends `+ 1`, so
`mintPathBoundAt >= 1` (:9858), so `fuelFigure_pos` (:3688) gives
`1 <= mintAwareFuelAt Ucard Tmax mintBudget D beta` unconditionally. Write it as
`Nat.exists_eq_succ_of_ne_zero` / `Nat.succ_pred_eq_of_pos` to land

```
theorem postBlockingSettlesRun_terminusFuel_false (U.card Tmax mintBudget D beta : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base (mintAwareFuelAt U.card Tmax mintBudget D beta)
```

which is the dispatch's literal question, answered.

**3. State the consequence for the terminus, additively.** `buildTableauAt_isSome_of_budget_fixed_run`
(:12199) and its five `_run` siblings are vacuous at `.Base`/`.Dense`/`.RTime`. Land that as a
corollary rather than leaving a reader to infer it — this is the analogue of
`postBlockingExitSettled_false` and belongs beside it.

**4. Cover `.ZTime`, or scope it explicitly.** At `.ZTime` the witness leaves `priorUZ`/`priorSZ`
applicable to `T(top untl top)` / `T(top snce top)` at `<0,0>`, `<0,1>`, `<1,0>`, `<1,1>` (measured).
Either add those rules' conclusions to `W` and re-run the same five `rfl`s, or land the refutation at
the three verified classes and record `.ZTime` as an explicit sub-case. Refuting at one frame class
already refutes the predicate; `.ZTime` is completeness of the record, not of the verdict.

**5. Name the minimal further narrowing — and do not claim it is true.** The bridge
`buildTableauAt_isSome_of_settlesRun` (:12197) instantiates the residual from `buildTableauAt`'s own
call, which supplies `tracker`, `applied`, `branchesUsed` at their **defaults** and
`ord = TimeOrdering.empty`. So

```
def PostBlockingSettlesSeedRun (fc) (fuel) : Prop :=
  forall (b ob : Branch) (oOrd : TimeOrdering) (oAp : AppliedSet) (mb : Nat)
         (satBr : Branch) (satOrd : TimeOrdering),
    expandBranchWithFuel b fuel TimeOrdering.empty fc EventualityTracker.empty {} mb 0
      = some (.inr (ob, oOrd, oAp)) -> ...
```

keeps the bridge working verbatim and kills this refutation (checked: with
`tr := EventualityTracker.empty` the witness's `expandOnceUnblocked` is `.extended`, not
`.saturated`, and a real run from `W` at the empty tracker reaches an exit whose settlement test
does **not** fail). It should be landed as the *named* next narrowing, carried as a hypothesis,
**not** as a discharge.

### Decisions

- **Refute rather than prove.** The refutation was found and machine-checked before any proof
  attempt was mounted, so no proof attempt was mounted. The gate's binary verdict is FALSE.
- **Attack the tracker, not the branch.** Two other attack surfaces were analysed and set aside:
  `ap` is provably inert (deprecated-in-substance `expandOnceUnblockedWithApplied`), and the
  "`saturateBlocked` unblocks a time by extending the branch" route (see below) was left unprobed
  once the tracker route closed.
- **Build the witness from a real engine exit, then augment.** `W = AUG ++ S` where `S` is the
  verbatim open exit `expandBranchWithFuel (seedBranch (p -> q)) 40 ... FrameClass.Base` produces
  (obtained by `#eval`, times `2 < 0 < 1 < 3`, blocked `[3,2]`). This keeps the saturation
  obligations honest — the ancestor times really are engine-saturated, not hand-asserted — and made
  the seriality/`negPos` obligations converge in three iterations.
- **Do not use `#guard_msgs` measurement where a kernel proof is available.** Register entry 24
  records the probes as measurements; every claim in the recommended deliverable is a theorem.

### Risks & Mitigations

- **Risk: the refutation is dismissed as "a tracker no engine threads".** Mitigation: state it the
  way entry 22's `fuel = 0` degeneracy is stated — the predicate *as written* quantifies over it,
  so the predicate as written is false; the finding is that the narrowing was incomplete, and the
  completion is named. Do not weaken this to a caveat.
- **Risk: `rfl` on a 29-formula branch is slow or brittle across frame classes.** Measured: all five
  obligations elaborate in well under the file's existing per-declaration cost at `.Base`, `.Dense`
  and `.RTime`. Mitigation if it regresses: `decide` on the Bool-valued halves, or shrink `S`
  (nothing in the argument needs `F(p -> q)`'s propositional residue — it is inherited from the
  engine exit for authenticity, not necessity).
- **Risk: adding the witness perturbs neighbouring declarations.** Mitigation: the change is purely
  additive — new `private def`s and theorems in the existing `PostBlockingSettlesRefutation` section,
  nothing withdrawn, no frozen file touched.
- **Risk: overclaiming that the seed-run narrowing is true.** Mitigation: the report and the C9 entry
  must both carry the gap below.

#### The gap the narrowing does not obviously close

With `tr := EventualityTracker.empty` and `satBr = ob` the two blocked sets coincide, so this
refutation dies. But `saturateBlocked` may **extend** `ob`, and `expandOnceNoFresh` ignores blocking
entirely — so it can do label-free work at a *blocked* time, and the formulas it adds can break
`isSubsetBlocked` (or `timeSaturated` at the ancestor) and thereby **unblock** a time carrying
label-minting work that `expandOnceNoFresh` itself skips. The settlement test on `satBr` would then
report it. This is a second, independent refutation route that does not need a doctored tracker at
all. It was not probed. Any future claim that `PostBlockingSettlesSeedRun` holds must gate on it
first; the cheapest probe is a sweep reporting, for engine exits `ob`, whether
`blockedTimes satBr satOrd fc (armTracker satBr)` ever loses a time that
`blockedTimes ob oOrd fc (armTracker ob)` held.

## Tactic Survey Results

Tactic candidates were exercised directly against the five witness obligations (not via
`lean_multi_attempt`, since the obligations sit in a scratch file with a fresh namespace and a
one-step `rw` was the load-bearing question).

| Goal | Tactic | Result | Premises/Config |
|------|--------|--------|-----------------|
| `findClosure W fc = none` (all fc) | `cases fc <;> rfl` | success | none |
| `(expandOnceUnblocked W ordW fc trW).1 = .saturated` | `rfl` | success | Base, Dense, RTime |
| `(expandOnceUnblocked W ordW .ZTime trW).1 = .saturated` | `rfl` | fail (statement false) | `priorUZ`/`priorSZ` outstanding |
| `expandOnceNoFresh W ordW fc = (.saturated, ordW)` | `rfl` | success | Base, Dense, RTime |
| `expandBranchWithFuel W (n+1) ordW fc trBad {} 100 0 = some (.inr (W, ordW, {}))` | `rw [expandBranchWithFuel]; norm_num; rfl` | success | one unfold only |
| `findUnexpandedUnblockedWith W ordW fc (blockedTimes ...) = some _` | `rfl` | success | none |
| `saturateBlocked W f ordW fc = some (.inr (W, ordW))` | `exact saturateBlocked_eq_self_of_noFresh_saturated _ _ _` | success | existing lemma, universal in fuel |
| whole refutation | `intro h; ... ; exact absurd this (by simp)` | success | axioms: propext, Classical.choice, Quot.sound |

`aesop`, `omega`, `decide` and `simp`-only variants were not needed: every obligation is a closed
computation on concrete data, so `rfl` dominates, and the single non-`rfl` step is the deliberate
one-step `rw` through `expandBranchWithFuel`'s equation lemma.

## Context Extension Recommendations

- **Topic**: "Refuting an over-quantified engine-run predicate by doctoring an inert-looking argument"
- **Gap**: The C9 register documents *which* predicates were over-quantified and how they were
  narrowed, but there is no reusable statement of the general shape: *every* argument of an engine
  entry point that the consuming site instantiates at a default is an over-quantification surface,
  and the cheapest refutation is usually a one-step unfold at the entry point's `.saturated` arm.
  This is now the third instance (entry 22 fuel, entry 23 output branch, this one tracker).
- **Recommendation**: add `context/project/lean4/patterns/engine-predicate-quantification.md`
  recording the pattern, the "one-step unfold at the saturated arm" proof technique (which makes a
  kernel refutation cheap where a kernel *proof* about the same function is prohibitive), and the
  checklist "for each binder, does the consuming site instantiate it at a default?".

## Appendix

### Verified witness source

Verified against the built `MintBound.olean` with
`lake env lean <file>`; zero errors, zero `sorry`.

```lean
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound
namespace Probe463
open FormalSystem.Syntax FormalSystem.Metalogic.Decidability FormalSystem.ProofSystem

def p   : Formula := .atom (Atom.mkBase "p")
def q   : Formula := .atom (Atom.mkBase "q")
def tt  : Formula := .imp .bot .bot
def su  : Formula := .untl tt tt        -- seriality's future witness shape
def ss  : Formula := .snce tt tt        -- seriality's past witness shape
def puq : Formula := .untl p q          -- guard p (/= top), event q: registers an eventuality

/-- Verbatim open exit of `expandBranchWithFuel (seedBranch (p -> q)) 40 ... .Base`.
    Times chain 2 < 0 < 1 < 3; engine-reported blocked set [3,2]. -/
def S : Branch :=
  [ SignedFormula.pos tt ⟨0,3⟩
  , SignedFormula.pos su ⟨0,1⟩, SignedFormula.pos ss ⟨0,1⟩
  , SignedFormula.pos tt ⟨0,2⟩
  , SignedFormula.neg .bot ⟨0,1⟩, SignedFormula.pos tt ⟨0,1⟩
  , SignedFormula.pos su ⟨0,0⟩, SignedFormula.pos ss ⟨0,0⟩
  , SignedFormula.pos p ⟨0,0⟩, SignedFormula.neg q ⟨0,0⟩
  , SignedFormula.neg (.imp p q) ⟨0,0⟩ ]

/-- World-1 machinery (so `puq` sits in type(0) *expanded and fulfilled*), the two `negPos`
    conclusions the engine exit left outstanding at its blocked times, and the witness itself
    at world 9, time 4. -/
def AUG : Branch :=
  [ SignedFormula.neg .bot ⟨0,2⟩, SignedFormula.neg .bot ⟨0,3⟩
  , SignedFormula.pos puq ⟨1,0⟩, SignedFormula.pos q ⟨1,0⟩
  , SignedFormula.pos su ⟨1,0⟩,  SignedFormula.pos ss ⟨1,0⟩
  , SignedFormula.pos q ⟨1,1⟩,   SignedFormula.pos tt ⟨1,1⟩
  , SignedFormula.pos su ⟨1,1⟩,  SignedFormula.pos ss ⟨1,1⟩
  , SignedFormula.pos tt ⟨1,2⟩,  SignedFormula.neg .bot ⟨1,2⟩
  , SignedFormula.pos tt ⟨1,3⟩,  SignedFormula.neg .bot ⟨1,3⟩
  , SignedFormula.pos tt ⟨1,0⟩,  SignedFormula.neg .bot ⟨1,0⟩
  , SignedFormula.neg .bot ⟨1,1⟩
  , SignedFormula.pos puq ⟨9,4⟩ ]

def W    : Branch      := AUG ++ S                                   -- 29 formulas
def ordW : TimeOrdering := { constraints := [(3,4),(1,3),(2,0),(0,1)] }  -- chain 2<0<1<3<4

/-- The doctored tracker: one pending `q`-eventuality parked at time 0 in an unused world,
    so `fulfillEventualities` never discharges it and the duplication guard at t_anc = 0
    is satisfied for the pending `q`-eventuality at time 4. -/
def trBad : EventualityTracker :=
  { pending := [ { formula := q, label := ⟨7,0⟩, isUntil := true } ] }

def trW := fulfillEventualities W (registerEventualities W trBad)

theorem findClosure_W (fc : FrameClass) : findClosure W fc = none := by cases fc <;> rfl

theorem expandOnceUnblocked_W_sat :
    (expandOnceUnblocked W ordW FrameClass.Base trW).1 = ExpansionResult.saturated := by rfl

theorem expandOnceNoFresh_W_sat :
    expandOnceNoFresh W ordW FrameClass.Base = (ExpansionResult.saturated, ordW) := by rfl

theorem ebwf_W (n : Nat) :
    expandBranchWithFuel W (n+1) ordW FrameClass.Base trBad {} 100 0
      = some (.inr (W, ordW, {})) := by
  rw [expandBranchWithFuel]; norm_num; rfl

theorem settle_W_fails :
    findUnexpandedUnblockedWith W ordW FrameClass.Base
        (blockedTimes W ordW FrameClass.Base (armTracker W))
      = some (SignedFormula.pos puq ⟨9,4⟩) := by rfl

theorem postBlockingSettlesRun_false_Base (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base (n+1) := by
  intro h
  have hsb : saturateBlocked W (n+1) ordW FrameClass.Base = some (.inr (W, ordW)) :=
    saturateBlocked_eq_self_of_noFresh_saturated (findClosure_W _) expandOnceNoFresh_W_sat _
  have := h W W ordW ordW trBad {} {} 100 0 W ordW (ebwf_W n) hsb
  rw [settle_W_fails] at this
  exact absurd this (by simp)

-- Dense / RTime: the same two `rfl`s go through unchanged.
theorem eoU_D  : (expandOnceUnblocked W ordW FrameClass.Dense trW).1 = ExpansionResult.saturated := by rfl
theorem eoU_R  : (expandOnceUnblocked W ordW FrameClass.RTime trW).1 = ExpansionResult.saturated := by rfl
theorem eoNF_D : expandOnceNoFresh W ordW FrameClass.Dense = (ExpansionResult.saturated, ordW) := by rfl
theorem eoNF_R : expandOnceNoFresh W ordW FrameClass.RTime = (ExpansionResult.saturated, ordW) := by rfl

end Probe463
```

### Measurements taken (all by `lake env lean` against the built library)

| Quantity | Value |
|---|---|
| `blockedTimes W ordW .Base (armTracker W)` | `[2, 3, 1]` |
| `blockedTimes W ordW .Base trW` | `[2, 3, 1, 4]` — strictly larger, at time 4 |
| `(armTracker W).pending` | `[{q, ⟨9,4⟩, isUntil}]` — exactly one, at time 4 |
| settlement test on `W` under `armTracker W` | `some (T(p untl q) @ ⟨9,4⟩)` — **fails** |
| `expandOnceUnblocked W ordW .Base trW` | `.saturated` |
| `expandOnceUnblocked W ordW .Base (empty-seeded)` | `.extended` — tracker is load-bearing |
| `expandBranchWithFuel W f ordW .Base trBad {} 100 0`, `f ∈ {1,2,3,50}` | `some (.inr (W, …))`, all f |
| `saturateBlocked W f ordW .Base`, `f ∈ {0,1,2,50}` | `some (.inr (W, ordW))`, all f |
| genuine run `expandBranchWithFuel W 40 ordW .Base empty {} 50000 0` | open exit, settlement test **passes** |
| `.ZTime` outstanding rules on `W` | `priorUZ`, `priorSZ` at ⟨0,0⟩ ⟨0,1⟩ ⟨1,0⟩ ⟨1,1⟩ |
| `#print axioms postBlockingSettlesRun_false_Base` | `[propext, Classical.choice, Quot.sound]` |

### Key source locations

- `PostBlockingSettlesRun` — MintBound.lean:11961
- `buildTableauAt_isSome_of_settlesRun` (the bridge) — MintBound.lean:12197
- `buildTableauAt_isSome_of_budget_fixed_run` (the terminus) — MintBound.lean:12199
- `saturateBlocked_eq_self_of_noFresh_saturated` — MintBound.lean:11653
- `mintAwareFuelAt` / `mintPathBoundAt` / `fuelFigure` / `fuelFigure_pos` — :9864 / :9858 / :3677 / :3688
- `expandBranchWithFuel` — Saturation.lean:816; `armTracker` — :711; `resolveOpenArm` — :736
- `registerEventualities` / `fulfillEventualities` — Saturation.lean:283 / :308
- `isTemporallyBlockedSaturated` / `blockedTimes` / `findUnexpandedUnblockedWith` /
  `expandOnceUnblocked` / `expandOnceNoFresh` — Tableau.lean:2117 / :2178 / :2189 / :2284 / :2335
- `expandOnceUnblockedWithApplied` (applied set is inert) — Tableau.lean:2947
- `allEventualitiesFulfilledOrDuplicated` / `isSubsetBlocked` / `timeType` — SignedFormula.lean:834 / :649
- C9 register entry 24 — MintBound.lean:15224 (recommend a new entry 25 for this verdict)
