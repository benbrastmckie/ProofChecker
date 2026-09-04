# Implementation Summary: L and L⋆ metatheory and conservative extension over L⁺

- **Task**: 533 - l_and_lstar_metatheory_conservative_extension
- **Status**: [COMPLETED]
- **Started**: 2026-09-03T18:00:00Z
- **Completed**: 2026-09-03T19:10:00Z
- **Effort**: ~1.2 hours wall-clock (16 leaf phases, 15 scoped commits)
- **Dependencies**: 535 (binding ⊡-axiom set; its report and compiled probes were the transcription source)
- **Artifacts**: plans/01_l-lstar-metatheory-conservative-extension.md, handoffs/phase-*-handoff-*.md (one per phase)
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Landed the metatheory for the two extension directions of the L⁺ tree, exactly as scoped by the
amendment: for **L ⊂ L⁺**, the H/G-fragment logic `TMFrag` with transferred soundness,
completeness at all four classes, Base/Dense compactness, and the strict inclusion
`TM ⊊ TMFrag` at Discrete; for **L⁺ ⊂ L⋆** (L⁺ plus the stability modal `⊡`), the syntax
`StarFormula`/`ofFormula`, native semantics, the closed proof system `StarAxiom` (45 TM⁺ schemata
re-declared over `StarFormula` + {SK, ST, S4, S5, MS, AS, PS, US}), soundness of TM⋆ at all four
classes with TD discharged semantically, semantic conservativity, and **proof-theoretic
conservativity of TM⋆ over TM⁺ in both directions** at all four classes — the forward direction
from TM⋆ soundness plus the existing completeness engines, with no TM⋆ completeness. 3,547 new
lines of Lean across 15 new modules, all sorry-free; no landed file was modified except four
aggregators/docstrings.

## What Changed

- **L side** (`Metalogic/Conservativity/Fragment.lean`, `FragmentCompactness.lean`): `TMFrag`,
  `tmFrag_sound`, `tmFrag_complete` (+4 rows), `tmFrag_iff_blValidIn`, `tm_le_tmFrag`,
  `tmFrag_z1_discrete`, `tm_lt_tmFrag_discrete`, `tmComplete_iff_tmFrag_le_tm`; `BLCompact` in
  the **consequence form** (mirror of `Compact`), `blCompact_of_compact` via the list pullback
  `exists_preimage_list`, `blCompactBase`, `blCompactDense`.
- **L⋆ syntax** (`StarLanguage/Formula.lean`, `Axioms.lean`, `Derivation.lean`, aggregator,
  README): `StarFormula` (7 constructors, `Countable`/`Infinite`/`Denumerable`), derived
  operators with `Formula`'s RHS verbatim (15 `rfl` pins), `swapTemporal` + push-throughs,
  `IsPureFuture`/`IsPurePast` + swap exchange + closure lemmas, `ofFormula` (injective,
  `ne_stab`, commutes with `swapTemporal`), `ofCtx`; `StarAxiom` (53 constructors) +
  `minFrameClass`; `StarDerivationTree` (7 rules) with `lift`/`height`/`ofWeakeningNil`,
  `StarDerivable`, `⊢⋆[fc]`, `stab_necessitation` (derived), `StarAxiom.ofPlus` (45 `rfl`-shaped
  arms), `minFrameClass_ofPlus`, `StarDerivationTree.ofPlus`, `starDerivable_of_derivable` +
  4 rows.
- **L⋆ semantics** (`Semantics/StarTruth.lean`, `StarValidity.lean`, `StarPasting.lean`,
  `StarNonValidities.lean`, wired into `Semantics.lean` and `Semantics/README.md`): `SameStateAt`,
  `StarTruthAt`, `StarTruth.*_iff` clause lemmas, A1-A5, B1-B3, E0-E2 (`starTruthAt_timeShift`,
  `stab_state_only`); `StarValidOnFrames` primitive, `StarValidIn`, `StarValid`, per-class
  abbreviations, mono + adapters, `starTruthAt_ofFormula`, `starValidIn_ofFormula_iff` (generic
  `fc`); `paste` and its agreement lemmas, `truth_congr_agreeFrom/UpTo`, PS/US/FS/GS, the two new
  past mirrors `paste_valid'` and `snce_dstab_valid` (SS), six `*_starValid` packagings; the five
  refutations D1-D5 on `natFrame` over ℤ.
- **L⋆ soundness and conservativity** (`Metalogic/Conservativity/Star/Atomization.lean`,
  `AxiomValidity.lean`, `StarSoundness.lean`, `Forward.lean`, aggregator `Star.lean`, wired into
  `Conservativity.lean`): `Encoding` (+`nonempty`, `swap`), `atomize` (+11 push-throughs,
  `atomize_swapTemporal`), `TaskModel.atomModel`, `starTruthAt_iff_atomize`,
  `starValidIn_of_plus`/`starValidIn_swap_of_plus` (acceptance: `□⊡p → □G⊡p`);
  `starAxiom_validIn_min`/`starAxiom_swap_validIn_min` (53 explicit arms each, no wildcard) +
  lifted forms; `star_derivable_valid_and_swap_validIn` (companion recursion),
  `star_soundness_validIn`, `star_soundness_in`, four rows, `star_not_derivable_nil_bot`;
  `forward_star` (+4 rows), `starDerivable_ofFormula_iff` (+4 rows), `star_of_tm` (+4 rows),
  `tmFrag_iff_star`.
- **Documentation**: `StarLanguage/README.md` (modules, invariant, extension recipe),
  `Metalogic.lean` docstring (H/G-fragment and Star rows; the deterministic-countermodel fact
  with `multiFamTaskFrameGen`/`zTaskFrameV2` cited by name), `README.md` (L/L⋆ results table
  and TM⋆ open problems citing Reynolds 2003 and Zanardo 1991), `FormalSystem/README.md` and
  `docs/development/MODULE_ORGANIZATION.md` (StarLanguage rows), `FormalSystem/FormalSystem.lean`
  root import of `StarLanguage`.

## Decisions

- Conjunction/disjunction on `StarFormula` are named `and`/`or` (as on `Formula`), not
  `conj`/`disj`; the clause lemma is `StarTruth.and_iff`.
- `ofCtx` is `List.map ofFormula Γ` (`Γ.map` resolves to the `Formula`-only `Context.map`).
- `BLCompact` landed in the consequence form (no fallback to model-existence was needed).
- The SS mirror `snce_dstab_valid` closed by the literal role exchange (paste `ρ` up to `y` with
  `τ` after `y`); the `TruthAntiIso` contingency was not needed, and TD is discharged purely by
  the companion recursion + per-constructor swap-validity.
- `Encoding` is built from `Denumerable.eqv` on both sides (no explicit `Nat`-encoding needed);
  `TaskModel.atomModel`'s valuation is existential, so the transfer lemma's `stab` case is
  `stab_state_only` with no extension theorem.
- `star_soundness_in` (context form) is a direct induction mirroring `soundness_in`; no deduction
  lemma was needed.
- The paper anchor `app:non-deterministic` cited by the dependency's report does not exist in the
  paper; `StarNonValidities.lean` cites `app:deterministic` (whose second half is the
  non-deterministic refutation), which the anchor record lists as LIVE-UNPINNED (C15).
- Builds ran through `lake-build-guard.sh` detached; the invariants script's own C1 (an unguarded
  `lake build`) was replaced by guarded builds of the default target and `BimodalTest`, followed
  by `check-module-invariants.sh --no-build` for the structural checks and a manual
  `#print axioms` pass (the four C2 flagship theorems unchanged).

## Plan Deviations

- Phase 2, derived operators: *altered* — `and`/`or` naming (matching `Formula`) instead of
  `conj`/`disj`; `strongRelease`/`strongTrigger` not mirrored (no axiom mentions them);
  `and`/`or`/`kPlus`/`kMinus`/`dstab` push-through lemmas added instead. Annotated inline in the
  plan.
- Phase 5.4: *added* `star_not_derivable_nil_bot` (Base consistency, mirroring
  `bl_not_derivable_nil_bot_discrete`'s witness) beyond the plan's list.
- Phase 7: C1 executed as two guarded builds plus `--no-build` (see Decisions).

## Impacts

- Root reachability: `StarLanguage` is imported by `FormalSystem/FormalSystem.lean`; the four
  `Semantics/Star*.lean` modules by `Semantics.lean`; `Conservativity/{Fragment,
  FragmentCompactness,Star}.lean` by `Conservativity.lean`.
- No landed theorem was modified; `ProofSystem.Axiom`'s documented count (45) is untouched
  (`StarAxiom` is a new inductive with 53 constructors).
- Extension discipline for `StarAxiom`: exactly three dispatch points (`minFrameClass` and the
  two `*_validIn_min` lemmas, no wildcard arms), recorded in `StarLanguage/README.md`.
- Downstream: a TM⋆ completeness attempt (separate task) inherits the exact `DerivationTree`
  shape and the deterministic-countermodel caveat recorded in `Metalogic.lean`.

## Verification

- `lake build` (guarded, full) green after every wiring phase and at the end; `lake build
  BimodalTest` green.
- `#print axioms` — `tmFrag_iff_blValidIn`, `star_soundness_validIn`,
  `starDerivable_ofFormula_iff`, `tm_lt_tmFrag_discrete`, `blCompactBase`, `blCompactDense`,
  `star_of_tm`, `tmFrag_iff_star`: `[propext, Classical.choice, Quot.sound]`;
  `starValidIn_ofFormula_iff`: `[propext]`; `starDerivable_of_derivable`: `[propext, Quot.sound]`.
  The four C2 flagship theorems: unchanged baseline.
- `scripts/check-module-invariants.sh --no-build`: B0, C3 (zero structural sorry), C4, C5, C6,
  C8, C9, C10, C11, C12, C13, C14 pass; C15 passes after the anchor correction.
- Sorry census (`lean-sorry-census.sh FormalSystem/`): only `Boneyard/` hits. Vacuous-definition
  grep: one pre-existing hit (`Examples/TemporalStructures.lean:496`, a genuinely-`True` domain
  fact), none introduced. `^axiom` line count: 8 before and after (docstring prose, no
  `axiom` declarations added).
- Negative checks: no asserted `Forward fc` statement under `Conservativity/Star/` or
  `Fragment*.lean`; no "exactly"/"iff … deterministic" wording in `StarNonValidities.lean`; no
  task-number citations under `FormalSystem/`.

## Follow-ups

- TM⋆ completeness (all-histories semantics) and decidability remain open; the README and
  `Metalogic.lean` record them without promises. A deterministic-class completeness of TM⋆ +
  *Determined* is the honest partial result a follow-up could deliver.
- Optional `docs/` note "adding a language extension" (BaseLanguage + StarLanguage pattern,
  atomization, companion recursion) was not written in this dispatch.
- The 535 report's `app:non-deterministic` citation should be read as `app:deterministic`
  (second half) wherever it is reused.

## References

- `specs/533_l_and_lstar_metatheory_conservative_extension/plans/01_l-lstar-metatheory-conservative-extension.md`
- `specs/533_l_and_lstar_metatheory_conservative_extension/reports/01_l-lstar-metatheory-conservative-extension.md`
- `specs/535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md`
- `specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean`
- `FormalSystem/StarLanguage/README.md`, `FormalSystem/Metalogic/Conservativity/Star.lean`
