# Implementation Summary: Bundle Temporal Duality Discipline

- **Task**: 527 - WAVE 4 (canonical-model infrastructure): replace textual future/past mirroring
  in `Metalogic/Bundle/` with derived duals, bundle the truth lemma's coherence hypotheses, and
  put the limit-MCS construction on Mathlib's `Filter` API
- **Status**: All 10 phases completed (2 with recorded, evidenced exclusions); the task's
  numeric line-reduction acceptance criterion is reported, not self-declared pass/fail (see
  below) — that decision is left to the user, as directed.
- **Plan**: `plans/01_bundle-temporal-duality-discipline.md`

## What Was Done

**Group A (Phases 1-4)**:
- `BFMCS.CanonicalCoherence` bundles the truth lemma's three coherence hypotheses;
  `bundleFlow_truth_lemma` / `bundleFlow_completeness_from_neg_membership` bind one argument
  instead of three, with the previously-unused `_h_rtc` binder gone.
- `TemporalCoherence.lean`'s dead-reachability set pruned: 13 of 15 named declarations deleted;
  2 (`BFMCS.BackwardUntilSinceCoherent`, `BFMCS.ForwardUntilSinceCoherent`) turned out to be live
  (consumed by `ChronicleMonadicBridge.lean`) and were kept, recorded as a Reasoned Exclusion.
- `WitnessSeed.lean`'s four witness-seed consistency proofs collapsed to a shared future-side
  core (`allFuture_neg_of_gseed_inconsistent`) plus a past-side core
  (`allPast_neg_of_hseed_inconsistent`) whose `bot`-derivation branch is obtained from the
  future core's by `Formula.swapTemporal` + `DerivationTree.temporal_duality` +
  `Formula.swap_temporal_involution`, not a second hand proof. `UntilWitnessSeed` (byte-identical
  duplicate of `ForwardTemporalWitnessSeed`) and `since_witness_seed_consistent` (dead) deleted.
- `multiFamTaskFrame` is now a one-line definitional specialization of
  `Algebraic.multiFamTaskFrameGen`, not a second hand-written `FrameOver` construction.

**Group B (Phases 5-6)**: the `swapTemporal` duality technique's boundary was mapped precisely.
It applies cleanly to *closed* syntactic facts (no free MCS/family) — the Phase 3 core is the
worked example. It does **not** apply directly to statements relative to a fixed, arbitrary MCS
or `FMCS` family without a general MCS-image-transport lemma that does not exist in this tree and
was judged disproportionate to build for the four remaining mirror pairs surveyed (all recorded
as Reasoned Exclusions with per-pair evidence). The discipline, its worked example, and its
boundary are recorded in `Bundle/README.md`'s new "Temporal Duality Discipline" section.

**Group C (Phases 7-10)**: `LimitMCS.lean`'s `limitSetBelow` moved onto Mathlib's `Filter` API
(`Filter.comap Rat.cast (nhdsWithin r (Set.Iio r))`), then a `TemporalSide` parameter (`below`/
`above`) was introduced so `limitFilter`, `limitSet`, `limitSet_consistent`, `limitUltrafilter`
and `limitMCS` are each stated once. `limitFilterBelow`, `limitSetBelow` and `limitMCSBelow`
(and all of their supporting theorem *statements*) are unchanged thin specializations at
`.below` — confirmed by zero source changes across the ~57 external references (seven files,
five under `BXCanonical/Chronicle/`) since the phase that introduced `mem_limitSetBelow` as the
sole unfolding lemma. `limitFilterAbove` and `limitMCSAbove` — previously missing — now exist and
typecheck. Five dead `LimitMCSCoherence.lean` lemmas were Boneyarded; the dead Zorn/Lindenbaum
construction was deleted. `limitUltrafilterBelow` was found load-bearing (not dead, contrary to
the plan's own flagged uncertainty) and kept. `FMCS`/`BFMCS` were found to already elaborate as
`(D) [Preorder D] (fc := .Base)` via pre-existing `variable` auto-binding — no source reorder was
needed or possible.

## Line-Reduction Criterion — Reported, Not Resolved

Measured: `Bundle/*.lean + Bundle.lean + Algebraic/FlowFrame.lean` = **3,697 lines**, against the
Phase 1 baseline of **4,082 lines** — a reduction of **385 lines**.

| Option (from the plan) | Outcome |
|---|---|
| A: restate as 550-830 lines | Not met (385 < 550) |
| B: hold "at least 800 lines" as a hard gate | Not met (385 < 800) |
| C: drop the numeric criterion, gate on structural criteria only | All structural criteria met (see plan's Phase 10 section for the full checklist) |

The shortfall relative to the plan's own re-baselined range traces to two deliberate,
documented scope decisions (Phase 5's four Reasoned Exclusions and Phase 8's `LimitMCSCoherence`
exclusion): the `swapTemporal` technique's boundary and the MCS/FMCS-image-transport
infrastructure it would need to cross were judged, each time, disproportionate to the size of
the pairs that would benefit — a risk/effort trade-off, not an oversight. Building that
transport infrastructure was the single largest lever available to close the gap toward the
550-830 range; it remains available as follow-on work if the user chooses Option A or B.

## Structural Acceptance Criteria (all met)

- Zero unused hypotheses on `bundleFlow_truth_lemma`.
- One frame-construction site for the `ℤ` multi-family frame (`multiFamTaskFrame` specializes
  `multiFamTaskFrameGen`).
- Every consumer theorem outside the named files unchanged in statement — confirmed by reading
  the full `git diff` across all 12 out-of-`file_scope` files touched.
- `lake build` green (full project + `Tests/BimodalTest/`).
- C2 axiom baseline unchanged, verified after every phase, never re-baselined.
- Zero `sorry` introduced.
- `limitFilterAbove` / `limitMCSAbove` exist and typecheck.

## `file_scope` Addition

12 files outside the declared `file_scope` were touched, all with only argument-packing,
`mem_limitSetBelow`-routing (proof-body-internal), or prose changes — no theorem statement
changed in any of them:

- `FormalSystem/Boneyard/LimitMCSCoherenceDeadCases/{LimitMCSCoherenceDeadCases.lean,README.md}`
  (new)
- `FormalSystem/Metalogic/BXCanonical/Chronicle/{ChronicleGuardAccumulation,
  ChronicleLimitGuardAbove,ChronicleLimitGuardWitness,ChronicleRealExtension}.lean`
- `FormalSystem/Metalogic/BXCanonical/Chronicle/{ChronicleToCountermodel,
  ChronicleToCountermodelBasic}.lean`
- `FormalSystem/Metalogic/BXCanonical/{Completeness,CompletenessDedekind,
  DiscreteCarrierProbe}.lean`
- `FormalSystem/Metalogic/StrongCompleteness.lean`

## Reasoned Exclusions (full evidence in the plan file's per-phase sections)

1. **Phase 2**: `BFMCS.BackwardUntilSinceCoherent` / `BFMCS.ForwardUntilSinceCoherent` kept —
   live consumers in `ChronicleMonadicBridge.lean`.
2. **Phase 5**: four mirror pairs (`TemporalContent.lean`, `TemporalCoherence.lean`'s backward-H
   pair, `WitnessSeed.lean`'s two helper pairs) left as pre-existing hand proofs — M/`fam`-
   relative statements outside the `swapTemporal` technique's reach without new transport
   infrastructure.
3. **Phase 7**: `limitSetAbove` and its two support lemmas temporarily kept hand-rolled (resolved
   in Phase 8, once `limitSet_consistent` made them genuinely dead).
4. **Phase 8**: `limitUltrafilterBelow` kept (load-bearing, not dead); `LimitMCSCoherence.lean`'s
   four live `limitMCSBelow_*` theorems left `Below`-specific (no `above` instantiation is
   consumed anywhere).
5. **Phase 9**: bounded, explicitly-optional call-site simplification skipped (zero structural
   value, conserved effort for Phase 10).

## Verification

- `lake build` green throughout (checked after every phase).
- `bash scripts/check-module-invariants.sh` ALL CHECKS PASSED at task-final `HEAD`, full run
  (not `--no-build`).
- C2 axiom baseline unchanged across all ten phases.
- Zero `sorry` introduced.
- `Tests/BimodalTest/` green.

## Plan Deviations

All deviations are Reasoned Exclusions, recorded above and in full detail in the plan file's
per-phase sections (Phases 2, 5, 7, 8, 9). No deviation left a phase incomplete or a proof
obligation unfulfilled by a vacuous placeholder.
