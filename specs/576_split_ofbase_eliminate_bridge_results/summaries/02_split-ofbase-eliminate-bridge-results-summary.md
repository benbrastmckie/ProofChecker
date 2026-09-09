# Implementation Summary: Task #576

- **Task**: 576 - Split the ofBase monolith and eliminate the ofPlus-restricted bridge results from TM-star
- **Status**: [COMPLETED]
- **Started**: 2026-09-09T13:39:30Z
- **Completed**: 2026-09-09T14:55:00Z
- **Effort**: ~1.3 hours wall clock, 13 phases
- **Dependencies**: Task 574 (landed), Task 575 (landed)
- **Artifacts**: plans/01_split-ofbase-eliminate-bridge-results.md, reports/01_ofbase-split-schema-measurement.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`StarAxiom.ofBase` — one constructor carrying the entire TM⁺ schema block into TM⋆ at `ofPlus`
instances only — is gone. The 53 TM⁺ schemata are now declared directly over `StarFormula`, one
mirror constructor each, with `modal_future` alone under a `RecallFree` (`↓ⁱ`-free) side
condition; validity and swap-validity are re-proved for every new arm. `stabNecessitationOfPlus`
is deleted and replaced by the unrestricted `stabNecessitation`, and the embedding survives as
the *derived* function `StarAxiom.ofPlusAxiom` rather than as a primitive arm.

## What Changed

### The measurement (deliverable 1 — the gate)

Re-established **by machine-checked proof**, not trusted from the report. `PlusAxiom` has **53**
constructors, not 45 (the task description undercounts by the eight `⊡` schemata, one of which,
`box_stab`, is the schema the headline bridge result hangs on). All eight probe files under
`specs/576_split_ofbase_eliminate_bridge_results/.probes/` are green under `lake env lean` with
no `sorry`; `.probes/08_measurement-closure.lean` was written this round to close the 17 schemata
the prior round had argued by mirror rather than proved. The full 53-row verdict table is
recorded in the plan file under Phase 1.

**Verdict: 52 of 53 are schematic over `StarFormula` with no new side condition; `modal_future`
alone needs one.** The prior count is confirmed rather than corrected. `paste`/`untl_paste` carry
side conditions, but those *mirror* conditions `PlusAxiom.paste`/`untl_paste` already carry, so
they are not exceptions.

### Files

- `FormalSystem/StarLanguage/Formula.lean` — `RecallFree`, `StarIsPureFuture`, `StarIsPurePast`
  (three inductives); `RecallFree.swapTemporal`, `StarIsPureFuture.swapTemporal`,
  `StarIsPurePast.swapTemporal`; `recallFree_ofPlus`, `starIsPureFuture_ofPlus`,
  `starIsPurePast_ofPlus`; `StarFormula.swap_temporal_kPlus`/`kMinus`; four properness pins.
- `FormalSystem/StarLanguage/Axioms.lean` — **53 mirror constructors** added, `ofBase`
  **deleted**; 8 explicit `minFrameClass` arms (2 `.Dense`, 3 `.ZTime`, 3 `.RTime`) matching
  `PlusAxiom.minFrameClass` exactly; per-constructor routing pins; module docstring rewritten
  end to end. The inductive now has 70 constructors = 53 mirror + 16 register.
- `FormalSystem/StarLanguage/Derivation.lean` — `stabNecessitation` added at every
  `ψ : StarFormula`, `stabNecessitationOfPlus` **deleted** (never both); the MF acceptance
  `example` retargeted from "reaches TM⋆ through the embedding and only there" to the
  non-embedded witness `□↑¹p → □G↑¹p`; a new pin exercising the rule at `↓ⁱφ`.
- `FormalSystem/StarLanguage/Embedding.lean` — `StarAxiom.ofPlusAxiom` (53-arm dispatch) and
  `StarAxiom.minFrameClass_ofPlusAxiom` (one named `cases` lemma) added,
  `StarAxiom.minFrameClass_ofBase` deleted, `ofPlusTree`'s `axiom` case rewritten.
- `FormalSystem/Metalogic/Conservativity/Star/StarPasting.lean` — **new**:
  `star_truth_congr_agreeFrom`/`agreeUpTo`, `star_paste_valid`, `star_untl_paste_valid`, plus
  `star_paste_valid'` and `star_snce_paste_valid` (the two duals). Reuses
  `Semantics/PlusPasting.lean`'s formula-independent construction read-only.
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` — 53 named `starValid_*`
  lemmas, 11 named `starValid_*_swap` duals, `starKPlus_iff`/`starKMinus_iff`,
  `recallFree_vector_irrelevant`; both dispatch lemmas now carry **70 arms each and remain
  wildcard-free**; the two `ofBase` arms deleted.
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — the conservativity
  re-verification recorded as a docstring section plus a pinned `example`.
- Prose sweep: `StarLanguage/README.md`, `StarLanguage.lean`,
  `Semantics/StarNonValidities.lean`, `Metalogic/Conservativity/Star.lean`,
  `Metalogic/Conservativity.lean`, `Metalogic/Soundness.lean`, `Metalogic/README.md`,
  `Metalogic/Conservativity/Star/README.md`, `docs/theorem-index.md`, `README.md`.

## Decisions

- **The side condition is `RecallFree`, not register-freedom.** `□↑¹p → □G↑¹p` is sound, and
  `↑¹p` is not an `ofPlus` image (`ofPlus_ne_timeStore`), so a register-free condition would have
  discarded a proved widening. `↑ⁱ` writes the *current* time, which the time shift moves along
  with everything else; only `↓ⁱ` reads a time the shift does not move. Both boundaries are
  pinned as `example`s in `Formula.lean`.
- **No residual embedding arm.** Deliverable 4's conditional never fired: the list of schemata
  that cannot be stated schematically over `StarFormula` is empty. The embedding returns as a
  *derived function*, which is what makes the retirement structural rather than a rename.
- **Frame-class agreement proved, not asserted.** `minFrameClass_ofPlusAxiom` is one
  `cases ax <;> rfl` over all 53 arms, so a routing mismatch — which would silently break
  backward conservativity — is a named failure at a single site.
- **Add first, delete last.** `ofBase` was kept as a temporary in-task scaffold through the seven
  group phases, each landing its constructors, `minFrameClass` arms and both dispatch arms in one
  green commit, and deleted in a single atomic batch in Phase 11. The alternative (delete then
  supply) leaves the build red across the whole interval, because `minFrameClass` and both
  dispatch lemmas are wildcard-free by design.
- **No L⋆ atomization and no uniform substitution**, anywhere. Atomization rests on
  `stab_state_only`, the invariant `StarFormula` exists to break; uniform substitution is unsound
  here because `PlusAxiom.atom_stab` already makes TM⁺ non-substitution-closed. Every schematic
  arm is a fresh direct proof against `StarTruthAt`. The prohibition is now recorded in
  `StarLanguage/README.md`'s invariant list — the shortcut a future contributor facing 53 arms is
  most likely to reach for.

## Plan Deviations

- **Phase 8 / Phase 9 Scope Hypotheses, duality half — corrected by measurement.** The plan
  asserted every group was swap-closed. Eleven schemata have **no** dual constructor in
  `StarAxiom`: `discrete_propagate_fwd`/`_bwd`, `discrete_box_necessity`, `dense_indicator`,
  `density`, `z1`, `sep`, `modal_future`, `paste`, `untl_paste`. This is not a grouping defect —
  the L level has exactly the same shape, carrying a dedicated `*_swap_valid` lemma per such
  schema in `SoundnessLemmas/FrameClassVariants.lean` and `Metalogic/Soundness.lean`. Eleven
  named `starValid_*_swap` lemmas supply the duals: the five closed ones by `ofPlus` transport
  from `plusAxiom_swap_validIn_min`, `density`/`z1` directly, `sep` through
  `SoundnessLemmas.sep_order_mirror` (so the ~130-line nested-interval argument is written once,
  not mirrored by hand), `modal_future` through `RecallFree.swapTemporal`. No statement was
  weakened and no later phase's work was consumed.
- **Phase 10 altered**: the plan's "the swap arms pair PS↔US" is wrong — PS's dual is PS with the
  conjuncts exchanged and US's dual is SS, exactly as `Semantics/PlusPasting.lean` already has
  it. Two lemmas (`star_paste_valid'`, `star_snce_paste_valid`) were added to Phase 3's
  `StarPasting.lean` during Phase 10 to supply them.
- **Phase 11 deferred one checklist item**: the "no live `ofBase` hits" grep was met for all
  **code** at the end of Phase 11 (with `lake build` and `lake build BimodalTest` green); the
  residual prose hits were cleared in Phase 13, which is that phase's declared documentation
  sweep. Splitting them kept Phase 11's atomic batch confined to declarations.
- **Phase 13 partially skipped one item**: no new rows were added to `docs/theorem-index.md`. The
  re-anchoring half — the load-bearing half — is done: no row named a deleted declaration, and
  the section's prose now describes the re-declared axiom set. New rows were not added because
  (a) the page states its own invariant that it admits no unpinned row, and pinning one means
  editing the `C14_BASELINE` heredoc inside `scripts/check-module-invariants.sh` — outside this
  task's territory and the very baseline the hard constraints direct me not to alter beyond a
  rename; and (b) the page's granularity is metatheory rows, finer than which `ofPlusAxiom`,
  `minFrameClass_ofPlusAxiom` and `stabNecessitation` sit. None of the metatheory rows changed.

## Verification

- Build: **Success** — `lake build` green (2649 jobs); `lake build BimodalTest` green (2700 jobs)
- Sorry count: **0** in the live tree (`lean-sorry-census.sh` reports `sorry_count: 0`; the only
  `sorry` occurrences under `FormalSystem/` are in `FormalSystem/Boneyard/`, the archived tree
  outside the build closure, and are untouched by this task)
- Vacuous count: **0 new** — the single scan hit,
  `FormalSystem/Examples/TemporalStructures.lean:496`, is pre-existing at the task's base commit
  and is a genuine proof (`intTimeHistory.domain t` reduces to `True`), not a placeholder
- Axiom count: **unchanged, 11 → 11** (`grep -c "^axiom "` at `010da8a04` and at HEAD agree). No
  C2/C14 pinned name or axiom set was changed; no baseline file was touched
- `bash scripts/check-module-invariants.sh`: exit 0, with C2/C3/C9/C14/C15/C24/C26 green
- Tests: `lake build BimodalTest` green
- Files verified: Yes

### Structural checks

- `inductive StarAxiom` has **70** constructors = 53 mirror + 16 register, and **no `ofBase`**
- `starAxiom_validIn_min` and `starAxiom_swap_validIn_min` have **70 arms each**, both
  **wildcard-free** (`grep -nE "^\s+\| _ =>"` returns nothing)
- `grep -rn "ofBase\|stabNecessitationOfPlus" --include=*.lean --include=*.md FormalSystem/ docs/ README.md`
  returns **no hits**
- `modal_future` is the sole constructor carrying a `RecallFree` hypothesis; `paste`/`untl_paste`
  are the sole constructors carrying purity hypotheses
- `refute_modal_future` is unchanged and still refutes MF at `↓¹p → p`
- Zero task-number citations under `FormalSystem/` (C9 green)
- `git diff --stat` shows no change to `FormalSystem/PlusLanguage/Axioms.lean`,
  `FormalSystem/Metalogic/SoundnessLemmas/**` or `FormalSystem/Semantics/PlusPasting.lean`;
  `Metalogic/Soundness.lean`'s only change is one prose line in its module docstring

## Impacts

- **TM⋆ is strictly stronger at register-carrying formulas, and provably no stronger at embedded
  ones.** `⊢⋆ □↑¹p → □G↑¹p` and `⊢⋆ ⊡ψ` from `⊢⋆ ψ` at arbitrary `ψ` are now derivable; both are
  pinned as `example`s in `Derivation.lean`.
- **All three conservativity results build unchanged** — `starDerivable_ofFormula_iff`,
  `starConservative_of_plusComplete`, `plusIncomplete_of_starNonconservative`. No direction
  breaks, and the reason is structural rather than lucky: every direction is established
  semantically and never pattern-matches `StarAxiom`; soundness survives because every new schema
  is proved valid at its own minimum frame class; and conservativity is a claim about *embedded*
  formulas, while the widening lies entirely outside that image. This is now recorded in
  `Conservativity/Star/Forward.lean`'s own docstring rather than only in a task artifact.
- **The restriction survey (deliverable 7) found nothing left to widen.** Two widenings
  (`stabNecessitationOfPlus` → `stabNecessitation`; the MF acceptance `example`), four deaths
  (`ofBase`, its two pins, `minFrameClass_ofBase`, the two `ofBase` dispatch arms). Everything
  still mentioning `ofPlus` is a statement *about the embedding* — `ofPlusTree`,
  `starDerivable_of_plusDerivable`, the conservativity statements, the truth-transfer lemmas —
  where removing `ofPlus` would not weaken a restriction but destroy the statement. The full
  per-result table is in the plan file under Phase 12.
- Task 577's forced research round is now unblocked per the cycle-4 sequencing decision: 576 is
  complete, so 577 will be researched against the post-split axiom set rather than the one this
  task replaced.

## Follow-ups

- **`docs/theorem-index.md` rows** for `StarAxiom.ofPlusAxiom`, `minFrameClass_ofPlusAxiom` and
  `stabNecessitation`, if the page's granularity is ever widened to admit them. Requires matching
  `C14_BASELINE` entries in `scripts/check-module-invariants.sh`.
- **The `star_truth_norm` simp set and relocation of the K± clause lemmas** to
  `Semantics/StarTruth.lean` (report D3). `starKPlus_iff`/`starKMinus_iff` currently live in
  `Conservativity/Star/StarAxiomValidity.lean`, following the precedent `starTruth_iff_iff`
  already set there. The L⋆ arms spell out clause lemmas that the L-level arms get from
  `truth_norm`; a simp set would shorten them measurably.
- **A predicate-level `SoundnessLemmas/` library for the L⋆ schemata** (report D1). It is
  measurably why `sep`, `z1` and `prior_UZ` transcribe in one-line bodies; the remaining arms
  would benefit.
- **The order-dual swap-arm refactor** (report D2): eleven swap duals are currently hand-written
  where a carrier-dualisation route (the `sep_order_mirror` pattern) might generate them.

## References

- `specs/576_split_ofbase_eliminate_bridge_results/plans/01_split-ofbase-eliminate-bridge-results.md`
  — the plan, now carrying Phase 1's 53-row measurement table and Phase 12's restriction survey
- `specs/576_split_ofbase_eliminate_bridge_results/reports/01_ofbase-split-schema-measurement.md`
  — the research report this plan was built on
- `specs/576_split_ofbase_eliminate_bridge_results/.probes/01`–`08` — the eight probe files, all
  green, that establish the 53-row verdict
