# Implementation Summary: Task #561

- **Task**: 561 - Store/recall and the characterization theorem for the deterministic task frames
- **Status**: [COMPLETED]
- **Started**: 2026-09-08
- **Completed**: 2026-09-08
- **Effort**: ~1 agent run (plan estimate: 21 h core + 2 h optional)
- **Dependencies**: None
- **Artifacts**: plans/01_store-recall-deterministic-characterization.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Built `FormalSystem/StarLanguage/` — the repository's **L⋆ = L⁺ + the manuscript's time
store/recall operators** — and used it to land the characterization theorem for the deterministic
task frames that the `⊡`-only language could not reach. Fourteen of the plan's fifteen phases
landed with `lake build` green and no new `sorry`: the biconditional bridge lemma, the new formula
type and its semantics over the manuscript's points `(τ, x, v⃗)`, both halves of
`app:deterministic-future`, the discrimination footnote, Theorem C's `Det-pm` half, and the
forward-determinism separating frame `F^N`. Phase 15 (`Det-m` with a world register) was declared
optional at plan time and is closed with a reasoned exclusion.

**One recorded Challenge statement turned out to be false and is excluded with a machine-checked
refutation** — see `## Plan Deviations`.

## What Changed

New Lean modules (2,160 lines):

- `FormalSystem/StarLanguage/Formula.lean` — `StarFormula`, the nine-constructor inductive for
  L⋆; the derived operators with `PlusFormula`'s right-hand sides; the embedding `ofPlus` with
  `ofPlus_injective`, `ofPlus_ne_timeStore`, `ofPlus_ne_timeRecall` and the `rfl` commutation pins
- `FormalSystem/StarLanguage.lean`, `FormalSystem/StarLanguage/README.md` — the component
  aggregator and its README, carrying the paper-label correspondence table
- `FormalSystem/Semantics/DeterministicBridge.lean` — `TaskFrame.SingletonClasses`,
  `singletonClasses_of_deterministic` (choice-free), `deterministic_of_singletonClasses` (the
  (⇐) half of `lem:deterministic-singleton`, via `thm:extension`; ZFC),
  `deterministic_iff_singletonClasses`
- `FormalSystem/Semantics/StarTruth.lean` — `StarTruthAt` over `(τ, x, v⃗)` with
  `def:BLstar-semantics`'s two register clauses; the `StarTruth.*` clause lemmas;
  `starTruthAt_ofPlus`; the transport layer `star_truth_congr_ext`, `update_shift_comm`,
  `starTruthAt_timeShift` (vector **shifted**, never dropped)
- `FormalSystem/Semantics/StarValidity.lean` — `TaskFrame.StarValidOn` and the
  `StarValidOnFrames`/`StarValidIn`/`StarValid` family with binder adapters;
  `starValidOn_ofPlus`; `settledDisj`, `sentDet` (`sent:det`), `sentDet_unfold` (the paper's
  `(∗)` chain), and the reusable refutation packaging `not_starValidOn_sentDet`
- `FormalSystem/Semantics/StarDeterminism.lean` — `star_congr_of_deterministic` (the L⋆ collapse
  engine), `settledDisj_of_deterministic`, `sentDet_of_deterministic`
  (`app:deterministic-future`, positive half), `detPM`, `detPM_unfold`,
  `detPM_of_deterministic`, `deterministic_of_detPM`, `deterministic_starDefinable`
  (**Theorem C, `Det-pm` half**)
- `FormalSystem/Semantics/StarNonValidities.lean` — `refute_sentDet`
  (`app:deterministic-future`, negative half) over `NF`, the manuscript's own reused
  countermodel; `not_starValid_sentDet`
- `FormalSystem/Metalogic/Independence/StarDiscrimination.lean` — `driftLinear`, `driftModel`,
  `fzero_refutes_sentDet`, `f1_sentDet`, `sentDet_discriminates`,
  `star_discriminates_where_plus_cannot` (the live-text footnote)
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` — `fnRel`, `FN` with all
  six `FrameOver` obligations, `fn_forwardDeterministic`, `fn_not_deterministic`,
  `states_eq_of_forwardDeterministic`, `fn_sentDet_atom`, `fn_separates`,
  `fn_forwardDeterministic_not_singletonClasses`, `fnZeroHist`, `fnRampHist`,
  `fn_refutes_sentDet_somePast`, `not_forall_fn_sentDet`

Modified Lean modules:

- `FormalSystem/Semantics/TaskFrame.lean` — `TaskFrame.saturation_of_fib_finite`, the
  finite-**fibres** *Saturation* helper (plus one `Mathlib.Data.Set.Card` import and two
  docstring list lines)
- `FormalSystem/Semantics/FrameProperty.lean` — `TaskFrame.ForwardDeterministic`,
  `forwardDeterministic_iff`, `forwardDeterministic_of_deterministic`
- `FormalSystem/Semantics.lean`, `FormalSystem/Metalogic/Independence.lean`,
  `FormalSystem/FormalSystem.lean` — aggregator imports

Documentation:

- `FormalSystem/StarLanguage/README.md` (new) — the paper-label correspondence table: every
  `\label` this task touches mapped to a Lean name or to an explicit, reasoned exclusion
- `FormalSystem/PlusLanguage/README.md`, `FormalSystem/Semantics/README.md`,
  `FormalSystem/Metalogic/Independence/README.md`, `FormalSystem/README.md`, `README.md` —
  updated for the built (no longer reserved) L⋆
- `specs/paper-definitions-of-record.md` — one new `KNOWN-ANCHORS` row (`sent:det`) and two rows
  corrected: `app:deterministic-future`'s "the Lean formalization of it is future work" and
  `def:BLstar-semantics`'s "the store/recall clauses, which no module here implements" were both
  false once Phases 3 and 6 landed

## Decisions

- **`\Future` in `sent:det` is the *universal* future, not the existential one.** The dispatch
  wrote it as `F` and the plan's task list said `someFuture`; the plan's own Scope Hypothesis
  directed a manuscript check. The manuscript preamble defines `\Future` as a **boxed** `F`, and
  `app:deterministic-future`'s `(∗)` chain reads "for all `y > x`". `sentDet` therefore uses
  `allFuture`, which is also what the plan's pinned `sentDet_unfold` Challenge statement already
  required.
- **The bridge lemma is stated pointwise on states on *both* sides.** Weaker as a conclusion and
  therefore stronger as a hypothesis, so `deterministic_iff_singletonClasses` is strictly
  stronger than the history-equality form — and it avoids needing history extensionality at a
  general frame.
- **`StarFormula` is a separate inductive.** Adding registers to `PlusFormula` would invalidate
  `stab_state_only`, on which the landed atomization/conservativity route rests. Breaking that
  invariant is the point of L⋆, and it must be broken in a separate type.
- **The refutation packaging lives at the abstract frame.** `not_starValidOn_sentDet`
  (`StarValidity.lean`) takes a base world, two later-disagreeing worlds of its stability class,
  and returns the refutation; both concrete refutation sites (`NF`, `F°`) and the `F^N`
  counter-example use it, so the register arithmetic is done once.
- **`F^N`'s relation is written in a sign-symmetric `max`-form**, so the converse convention is
  literally `Or.comm` rather than a case split repeated at every obligation.
- **No proof system for L⋆.** `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are reserved
  and unbuilt, as the plan's Non-Goals require; every deliverable here is semantic.

## Plan Deviations

- **Phase 13** closed `[COMPLETED WITH EXCLUSIONS]`. The plan's `## Lean Challenge Statements`
  pinned `fn_sentDet (φ : StarFormula) : FN.StarValidOn (sentDet φ)` — the **schematic** form.
  That statement is **false**, and the tree now contains the refutation:
  `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet`
  (`Metalogic/Independence/ForwardDeterministicFrame.lean`). Forward determinism settles the
  future and says nothing about the past, so a past-looking instance (`P p`) distinguishes two
  possible worlds of the same stability class at a *future* time; `F^N`'s own witnesses
  `fnZeroHist ≡ 0` and `fnRampHist n = max(0, −n)` agree at `0` and differ at every negative
  time. What landed instead is `fn_sentDet_atom (p : Atom)`, the sentence-letter form — which is
  what the ground-truth source actually claims (the PossibleWorlds determinism-axiom-correspondence
  report's Theorem A runs the singleton valuation `|p| = {τ(y)}` and is stated at the
  sentence-letter level throughout). **Nothing in the ground truth is contradicted; the plan
  generalised it one step too far.** Per `.claude/rules/plan-compliance.md` this is raised rather
  than laundered: the recorded statement is not weakened under the same name — it is disproved,
  under a different name, with the disproof in the tree, and `fn_sentDet_atom` carries the
  correct claim. **The user may wish to confirm this reading before the plan's Challenge section
  is treated as settled.**
- **Phase 15** closed `[COMPLETED WITH EXCLUSIONS]`: `Det-m` and the world registers were
  declared optional and last at plan time (dispatch deliverable 7), excluded from the plan's
  Goals and Challenge sets, and are recorded as explicit exclusions in the correspondence table.
- **Phase 5** altered: `allFuture`, not `someFuture` — see Decisions; the phase's own Scope
  Hypothesis provided for exactly this.
- **Phase 4** altered: `starTruthAt_timeShift` drops the pinned Challenge statement's unused
  totality hypothesis `hσ : σ.IsTotal`, which **strengthens** the lemma. `plusTruthAt_timeShift`,
  the lemma it restates, likewise takes none.
- **Phase 1** altered: the paper's Step 1 (deriving `⇒_0 = id` from *Limit* plus `lem:nullity`)
  is not transcribed — `FrameOver.nullity_identity` is a structure field and closes the `x = 0`
  branch outright. Recorded at the site, as the plan directed.
- **Phase 12** landed with no exclusion: the `saturation` obligation that task 536 flagged as
  possibly blocked was discharged by the new `TaskFrame.saturation_of_fib_finite`, so the
  `[COMPLETED WITH EXCLUSIONS]` escape the dispatch authorized was not needed.

## Verification

- Build: **Success** — full `lake build` green (guarded, detached), and
  `bash scripts/check-module-invariants.sh` exits 0 with **C1, C2, C3, C4, C5, C6, C8, C9, C10,
  C11, C12, C13, C14, C15, C16, C18, C19, C20, C21, C22, C23, C24, C25, C26 and INV all PASS**
  (the plan named C2/C3/C14 plus C15/C24/C26; every one of those is green)
- Sorry count: **0** in the new and modified modules; C3 reports the structural inventory as ZERO
  across `FormalSystem/` (Boneyard excluded)
- Vacuous count: **0** (the single repo-wide grep hit,
  `Examples/TemporalStructures.lean:496 int_domain_universal … := trivial`, is pre-existing and
  is a genuine proof of a `True`-valued domain predicate, not a placeholder)
- Axiom count: **0** new `axiom` declarations
- Tests: N/A — no test-suite additions; every result is a theorem in the library. `lake build
  BimodalTest` is green (C1)
- Files verified: Yes

### Axiom pins, measured

`#print axioms`, run against the built tree:

| Declaration | Axioms |
|---|---|
| `states_eq_of_deterministic` | `[propext]` — **the choice-free pin is intact**, `PlusDeterminism.lean` byte-untouched |
| `singletonClasses_of_deterministic` | `[propext]` |
| `deterministic_of_singletonClasses` | `[propext, Classical.choice, Quot.sound]` — ZFC, as documented |
| `deterministic_iff_singletonClasses` | `[propext, Classical.choice, Quot.sound]` |
| `starTruthAt_ofPlus` | `[propext]` |
| `starTruthAt_timeShift`, `sentDet_unfold`, `sentDet_of_deterministic`, `refute_sentDet` | `[propext, Classical.choice, Quot.sound]` |
| `detPM_of_deterministic`, `deterministic_of_detPM`, `deterministic_starDefinable` | `[propext, Classical.choice, Quot.sound]` — ZFC, as documented; no choice-free pin claimed |
| `TaskFrame.saturation_of_fib_finite` | `[propext, Classical.choice, Quot.sound]` — as its docstring records |
| `fzero_refutes_sentDet`, `f1_sentDet`, `fn_forwardDeterministic`, `fn_not_deterministic`, `fn_sentDet_atom`, `fn_refutes_sentDet_somePast` | `[propext, Classical.choice, Quot.sound]` |

Every `#print axioms` figure asserted in a new docstring matches the measured value; C14 confirms
this mechanically.

### Plan-compliance spot-check: FAILED on one name, deliberately

The mechanical Goals-name grep reports two misses:

- `FN` — a **grep artifact**: it is declared `@[reducible] def FN : TaskFrame`, and the check's
  pattern requires the line to begin with `def`. `FN` is present and used.
- `fn_sentDet` — **genuinely absent, by decision.** The recorded statement is false and is
  disproved in the tree (`fn_refutes_sentDet_somePast`, `not_forall_fn_sentDet`); the correct
  sentence-letter form landed as `fn_sentDet_atom`. See `## Plan Deviations`.

This is why the returned metadata carries `compliance_check: "failed"` and
`status: "partial"` with `requires_user_review: true`, even though every substantive gate above
is green: the agent's verification contract treats a missing Goals-named declaration as
review-worthy, and this one genuinely is. The phase-heading status of Phases 13 and 15 is
`[COMPLETED WITH EXCLUSIONS]` — both satisfy all five conditions of the admission test in
`context/standards/status-markers.md` (decision not abandonment; tightly scoped to one enumerated
item; documented reason; evidenced by a Lean-checked refutation and by the plan's own optional
declaration; no residual work).

## Impacts

- `FormalSystem/StarLanguage/` is a new top-level language component, wired into
  `FormalSystem.FormalSystem`. The `L⋆` row of the four-language table in `README.md` is no
  longer "not yet built".
- `deterministic_iff_singletonClasses` makes `lem:deterministic-singleton` available as a
  biconditional to any consumer; `PlusDeterminism.lean` is byte-untouched, so its choice-free
  `[propext]` pin is visibly intact.
- `TaskFrame.saturation_of_fib_finite` is a general frame-construction helper: it reaches
  infinite carriers with finite fibres, which neither `saturation_of_finite` (finite carrier) nor
  `saturation_of_fib_subsingleton` (subsingleton fibres) does.
- `TaskFrame.ForwardDeterministic` names a class the tree previously only discussed in
  `Deterministic`'s docstring, and `FN` witnesses that the two differ.

## Follow-ups

- **Confirm the Phase 13 exclusion.** The plan's pinned schematic `fn_sentDet` is disproved in
  the tree; if the intent was the sentence-letter statement all along, the Challenge section
  should be corrected by a plan revision rather than left as-is.
- `Det-m` and the world registers (`↑_M`/`↓_M`) remain unbuilt, as does any proof system for L⋆.
- The single-`p` strengthening of `deterministic_starDefinable` (validity at one fixed letter
  being equivalent to the family) is not established and is deliberately not claimed.

## References

- `specs/561_store_recall_deterministic_frame_characterization/plans/01_store-recall-deterministic-characterization.md`
- `FormalSystem/StarLanguage/README.md` — the paper-label correspondence table
- `specs/archive/536_stability_deterministic_collapse_store_recall/reports/02_correspondence-record-and-store-recall-recommendation.md`
- `/home/benjamin/Philosophy/Papers/PossibleWorlds/specs/105_characterize_deterministic_task_frames/reports/02_determinism-axiom-correspondence.md`
- JPL manuscript `possible_worlds.tex`: `def:BLstar-semantics`, `lem:deterministic-singleton`,
  `sent:det`, `app:deterministic-future`, `app:drift`, `cor:no-characterization`,
  `thm:extension`
