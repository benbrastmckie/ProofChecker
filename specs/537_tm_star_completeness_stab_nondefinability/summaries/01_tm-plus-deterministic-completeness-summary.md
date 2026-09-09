# Implementation Summary: Task #537

- **Task**: 537 - tm_star_completeness_stab_nondefinability
- **Status**: [COMPLETED]
- **Started**: 2026-09-08
- **Completed**: 2026-09-08
- **Effort**: ~14 hours (planned 26)
- **Dependencies**: 533 (landed), 535 (archived, ground truth), 536 (landed), 562 (completed)
- **Artifacts**: plans/01_tm-plus-deterministic-completeness.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The mechanical TM⁺ metatheory is landed, sorry-free, at all four frame classes: deterministic
completeness of TM⁺ + *Determined* together with the coincidence corollary the manuscript needs;
the non-definability of the stability modal `⊡` over L; the underivability of both pasting
schemata from the naive `⊡`-set; and the conservativity corollaries that `⊡` permits. General
(nondeterministic) TM⁺ completeness is stated nowhere and is discharged with `sorry` nowhere; it
is recorded as **open** in three READMEs and the theorem index, citing Reynolds (2003) and
Zanardo (1991) as the nearest literature.

All four mandatory deliverables landed. The optional fifth (compactness of TM⁺) is closed as a
reasoned exclusion.

## What Changed

**New — the deterministic subtree `FormalSystem/Metalogic/Deterministic/`**

- `Validity.lean` — `DetSat`, `ValidDetIn`, `PlusValidDetIn`, `DeterminedValid`, `DeterminedSat`,
  `PlusValidDeterminedIn`; `deterministic_determinedValid` (536's collapse repackaged, never
  re-derived) and `determinedValid_not_deterministic`, the **strictness** of the inclusion.
- `Engines.lean` — `derivable_of_validDetBase/Dense/ZTime/RTime` and the uniform
  `derivable_of_validDet`: the four TM completeness engines with the validity hypothesis narrowed
  to the deterministic frames of the class.
- `Erasure.lean` — `erasePlus`, `erasePlus_ofFormula`, `erasePlus_swapTemporal`, the pointwise
  **semantic** collapse `plusTruthAt_erasePlus_of_deterministic`, and the equivalidity corollary.
- `System.lean` — `DetAxiom` (`ofPlus` + `determined`), `DetDerivationTree` (the same seven rules),
  `DetDerivable`, and the embeddings `ofPlus` / `ofTM` / `ofTMSubst`. The live `PlusAxiom` is
  untouched.
- `Soundness.lean` — `detSoundness` over the *Determined*-valid frames (the strictly larger
  class), `detSoundnessDet`, `detSoundnessIn`, and consistency `det_not_derivable_nil_bot`.
- `Collapse.lean` — the Prop-level rule layer, six propositional theorems imported from
  `Theorems/` by the substitution transfer, the four congruence rules, `detStabIff`, and the
  **syntactic** collapse `detDerivable_iff_erasePlus` with its transport.
- `Completeness.lean` — `detCompletenessBase/Dense/ZTime/RTime`, the uniform `detCompleteness`,
  the coincidence corollary `logicDeterministicEqDeterminedValid`, the intermediate-class
  transfers, and the `⊡ = identity` row.
- `README.md`, and the subtree aggregator `FormalSystem/Metalogic/Deterministic.lean`.

**New — `FormalSystem/PlusLanguage/Substitution.lean`**

`substPlus`, `substPlus_atom`, `substPlus_swapTemporal`, `PlusAxiom.ofTMSubst` (45 arms),
`PlusDerivationTree.ofTMSubst`, `plusDerivable_substPlus`: the lever that makes every TM theorem
*schema* available at arbitrary `PlusFormula` arguments, so no propositional layer had to be
rebuilt over `PlusFormula`.

**New — `FormalSystem/Metalogic/Independence/`**

- `StabUndefinable.lean` — `stabNotDefinable`: no `Formula` is equivalent to `⊡Fp` over all task
  models, by a `TruthCorr` between two models realizing the same atom profiles.
- `NaiveSystem.lean` — `NaiveDerivable` as a predicate on the existing derivation trees.
- `CoarsenedModels.lean` — the coarsened-state semantics, its three structural ports, the
  atomization transfer, the six naive `⊡` validities, and naive soundness `naive_cValid`.
- `PastingIndependence.lean` — `pasteNotNaiveDerivable`, `untlPasteNotNaiveDerivable`.

**New — `FormalSystem/Metalogic/Conservativity/Plus/Corollaries.lean`**

The composed fragment rows per class, the derived logic of the defined modals, and
`detDerivable_ofFormula_iff` — TM⁺ + *Determined* is conservative over TM.

**Modified — the shared engine files**

`Algebraic/FlowFrame.lean` (+`multiFamTaskFrameGen_deterministic`, `bundleFlowFrame_deterministic`),
`WeakCanonical/IntegerModel/ReynoldsBridge.lean` (+`multiFamTaskFrame_deterministic`,
`zTaskFrameV2_deterministic`), and the four countermodel producers in
`BXCanonical/{Completeness,CompletenessDedekind}.lean`,
`WeakCanonical/GroupModel/CountermodelBase.lean`, `ReynoldsBridge.lean`, each widened with one
additive existential binder exposing its frame's determinism. `BXCanonical/Completeness.lean`
also gained the extracted `ztimeNextTop`.

**Modified — documentation**

`FormalSystem/Metalogic/Conservativity/Plus/README.md`, `FormalSystem/Metalogic/README.md`,
`FormalSystem/Metalogic/Independence/README.md`, `docs/theorem-index.md`, plus the regenerated
inventory blocks in `FormalSystem/README.md`, `README.md` and
`FormalSystem/Metalogic/Conservativity/README.md`.

## Decisions

- **The determinism lemmas are hosted beside their frames**, not in a new `Deterministic/Frames.lean`
  as the plan assigned them: the four countermodel producers that consume them sit *below*
  `Metalogic/Deterministic/` in the import order, so a collector module there could not have been
  imported by them.
- **`Determined` is added as a separate axiom inductive**, never as a `PlusAxiom` constructor
  (it is refuted at `.Base`) and never carried in the context (all three of necessitation,
  temporal necessitation and temporal duality are empty-context rules).
- **Only the propositional glue needed the substitution transfer.** `□`, `U` and `S` congruence
  are built directly from `PlusAxiom.modal_k_dist`, `.left_mono_until_G`, `.right_mono_until`,
  `.left_mono_since_H`, `.right_mono_since`, which are already stated at arbitrary `PlusFormula`
  arguments — that is precisely what re-declaring the TM schemata over `PlusFormula` bought.
- **The pasting-independence argument had to leave the standard semantics.** PS and US are valid
  on *every* task frame, because *Compositionality* makes the splice of two total histories
  through a common state a total history; so no ordinary model can witness underivability. The
  coarsened-state semantics removes exactly that common state and nothing else.
- **Soundness of the extended system is stated at the larger class on purpose.** Soundness over
  the *Determined*-valid frames plus completeness over the deterministic frames is what forces
  the two logics to coincide; stating soundness at the smaller class would not.

## Plan Deviations

- **Phase 2** altered: the two determinism lemmas are hosted in `Algebraic/FlowFrame.lean` and
  `WeakCanonical/IntegerModel/ReynoldsBridge.lean` rather than in a new `Deterministic/Frames.lean`
  (import order, as above). Scope hypothesis reconciled: four producers as asserted, but **four**
  destructuring call sites, not five — `BXCanonical/DiscreteCarrierProbe.lean` mentions
  `countermodel_discrete` only in prose.
- **Phase 3** altered: the `.ZTime` dense-branch derivation was first extracted from
  `derivable_of_validZTime` as the named `BXCanonical.ztimeNextTop`, so the two engines cite one
  derivation instead of duplicating ten steps.
- **Phase 5** deferred one item: the congruence audit was folded into Phase 8, where the
  induction's goals name the schemata it actually demands — which is the ordering Phase 8's own
  Scope Hypothesis prescribes.
- **Phase 8** altered: only the propositional glue went through the substitution transfer (see
  Decisions). Scope hypothesis confirmed: four congruence rules plus `detStabIff` closed all seven
  constructors, with six imported propositional theorems and no new TM-side schema.
- **Phase 10** altered: `M₁` is `Semantics/PlusNonValidities.lean`'s existing `NF`/`natHist`/
  `natModel` reused verbatim, and `M₂` is `multiFamTaskFrameGen` at family index `ℤ → ℕ`, so
  neither frame had to be built and no `FrameOver` obligation had to be re-discharged.
- **Phase 12** altered: the refuting frame is `multiFamTaskFrameGen (TemporalOrder.of ℤ) Unit`
  with coarsening `|·|`, again avoiding a new frame construction.
- **Phase 13** altered: `plus_of_tmMinus_*` and `plusDerivable_ofFormula_iff_*` are already named
  per class in `Forward.lean`, so the four `tmFragIffPlus*` are the composed rows actually added;
  and FS (`F⟐φ⁺ → ⟐Fφ⁺`, a one-line `untl_paste` instance) was delivered in place of GS, which
  needs contraposition infrastructure over `PlusFormula` this phase's budget did not cover — GS
  is cited semantically as `Semantics.stab_allFuture_plusValid` instead.
- **Phase 15** closed as `[COMPLETED WITH EXCLUSIONS]`; it is explicitly optional and its plan
  entry names that as the expected outcome.

## Verification

- Build: Success — full `lake build` clean, 2629 jobs, zero errors.
- Sorry count: 0 (C3: "structural sorry inventory is ZERO across FormalSystem/").
- Vacuous count: 0.
- Axiom count: 0 new axioms; `grep -rn "^axiom " FormalSystem/` unchanged.
- `#print axioms` for `detCompletenessBase/Dense/ZTime/RTime` and
  `logicDeterministicEqDeterminedValid` reports exactly `[propext, Classical.choice, Quot.sound]`.
- The four pre-existing engines (`completeness`, `derivable_of_validDense`,
  `derivable_of_validZTime`, `completeness_rtime_engine`) report the same axiom sets as before the
  countermodel-producer widening.
- `bash scripts/check-module-invariants.sh` — C2, C3 and C14 pass, along with every other check.
- `grep -rn "task [0-9]" FormalSystem/ docs/` finds no new occurrence (C9 passes).
- The live `PlusAxiom` inductive has exactly the constructors it had before this task.
- No declaration states general (nondeterministic) TM⁺ completeness, at any class.
- Files verified: Yes.

## Impacts

- **Tasks 559/560** (general TM⁺ completeness over the all-histories semantics) now have their
  baseline: any nondeterministic result must specialize to `detCompleteness*` when the frame is
  deterministic, and `detDerivable_iff_derivable_erasePlus` records that specialization
  explicitly. The PS/US underivability record tells that construction which pasting principles it
  must realize.
- **The manuscript** gains the axiomatization sentence its appendix lacked:
  `logicDeterministicEqDeterminedValid` says the logic of the deterministic frames and the logic
  of the *Determined*-valid frames coincide, and TM⁺ + *Determined* axiomatizes both — without
  ever describing *Determined* as characterizing determinism.
- **`PlusLanguage/Substitution.lean`** is reusable well beyond this task: every TM theorem schema
  is now available at arbitrary L⁺ arguments, which is what any further TM⁺ proof theory will
  need.
- **Territory note**: task 560 will edit the same `Conservativity/Plus` README rows and tree; the
  metatheory-row tables added here are the surface it should update rather than duplicate.

## Follow-ups

- Compactness of TM⁺ at Base and Dense (deliverable 5) is not attempted — see Phase 15's
  `#### Reasoned Exclusions` record in the plan.
- GS (`⊡Gφ⁺ → G⊡φ⁺`) is available semantically (`Semantics.stab_allFuture_plusValid`) but not as
  a derived TM⁺ theorem; deriving it needs contraposition over `PlusFormula`, which the
  substitution transfer now makes cheap for whoever wants it.
- General TM⁺ completeness and TM⁺ decidability remain open, and are recorded as such.

## References

- `specs/537_tm_star_completeness_stab_nondefinability/plans/01_tm-plus-deterministic-completeness.md`
- `specs/archive/535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md`
- `FormalSystem/Metalogic/Deterministic/README.md`
- `FormalSystem/Metalogic/Conservativity/Plus/README.md`
- `docs/theorem-index.md`
