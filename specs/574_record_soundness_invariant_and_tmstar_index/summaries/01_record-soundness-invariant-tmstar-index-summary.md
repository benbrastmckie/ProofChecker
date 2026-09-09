# Implementation Summary: Task #574

- **Task**: 574 - Record the load-bearing soundness invariant and close the TM-star documentation gaps
- **Status**: [COMPLETED]
- **Started**: 2026-09-09T05:04:00Z
- **Completed**: 2026-09-09T06:05:00Z
- **Effort**: ~1 hour
- **Dependencies**: None
- **Artifacts**: plans/01_record-soundness-invariant-tmstar-index.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

All six plan phases closed. The time-shift invariant is now audited and recorded where a language-extension author reads first; the two `StarValidIn` binder-shape adapters have moved to the module whose docstring advertises them; and `docs/theorem-index.md` carries a machine-pinned TM⋆ section plus an explicit OPEN record for TM⋆ completeness. `lake build` is green, `bash scripts/check-module-invariants.sh` exits 0 with `ALL CHECKS PASSED`, and the tree's axiom set is byte-identical to its pre-task state.

**The audit corrected the description's central claim, in the direction the plan anticipated.** `modal_future_valid` is *not* the sole consumer of time-shift homogeneity. It is one of **two declarations**, both belonging to the **one schema** `Axiom.modal_future`.

## What Changed

- `FormalSystem/Metalogic/Soundness.lean` — module docstring only. New `## The time-shift consumer set` section: the enumerated consumer set with paths, why the set's size matters to a language extension, `refute_modal_future` as the realized consequence, and the list of languages that inherit MF by transfer rather than by re-proof. The `**Key Techniques**` bullet was rewritten from "Time-shift invariance (MF, TF)" to "(MF, and TF through it)", since TF is not a separate `Axiom` constructor. No proof, `theorem`, `def` or `import` line touched.
- `FormalSystem/Metalogic/README.md` — one paragraph under `### Soundness — Soundness.lean` naming the two declarations and pointing at the `Soundness.lean` docstring as the authority.
- `FormalSystem/StarLanguage/README.md` — the `ofBase` rationale paragraph annotated: its existing "MF is the only schema" claim is now marked as audited, cross-referenced, and given the one-schema/two-declaration split.
- `FormalSystem/Semantics/StarValidity.lean` — `StarValidIn.of_forall_total` and `StarValidIn.apply_total` added to the `### Binder-shape adapters` block, mirroring `PlusValidIn.of_forall_total` / `.apply_total` line for line; bodies are the one-line delegations, no `sorry`.
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` — the local `starValidIn_of_forall_total` / `starValidIn_apply_total` and their section header deleted, fourteen call sites repointed to the dotted names, a `## References` bullet added naming the adapters' new home.
- `FormalSystem/StarLanguage/Axioms.lean`, `FormalSystem/StarLanguage/Derivation.lean`, `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — `Paper: — (formalization-native; …)` lines added inside existing `/-- … -/` blocks on `StarAxiom`, `StarDerivationTree`, `starConservative_of_plusComplete` and `plusIncomplete_of_starNonconservative`. Docstring-only; no declaration, statement or proof line touched.
- `docs/theorem-index.md` — a `### TM⋆ over L⋆ — the store/recall language` section with five machine-pinned rows; an L⋆/TM⋆ `Notation and naming` row; the refutations section retitled `## Statuses that are refutations, not gaps, and one status that is a gap` and given a bullet recording TM⋆ completeness as OPEN, with its entanglement with TM⁺ completeness spelled out through `starConservative_of_plusComplete` / `plusIncomplete_of_starNonconservative`.
- `scripts/check-module-invariants.sh` — five measured lines appended to `C14BASE` and five matching `#print axioms` lines to `C14LEAN`, same order; the STRICT-SUBSET comment updated from seven entries to eight; a new comment paragraph recording why `StarAxiom` is absent; `inductive` added to C15's second-assertion `DECL` alternation.
- `scripts/module-invariants-allowlist.txt` — two entries so C5 stops reading `FormalSystem.StarLanguage.StarAxiom` / `…StarDerivationTree` as module paths.
- `FormalSystem/Metalogic/Conservativity/Star/README.md`, `FormalSystem/Metalogic/Conservativity/Plus/README.md`, `FormalSystem/Metalogic/README.md`, `README.md` — regenerated inventory blocks (`--emit-inventory`), whose line counts this task's docstring edits moved.

## Decisions

- **The recorded invariant states both a schema count and a declaration count**, because they differ and both are load-bearing. One schema (MF) and two declarations (`modal_future_valid` for MF's validity; `mf_swap_valid`, the `temporal_duality` companion, for its dual and therefore for TF). `StarLanguage/Axioms.lean` and `StarNonValidities.lean` already said "the only schema", so the pre-existing prose was right at its own level and needed annotation rather than correction.
- **`minusTruthAt_timeShift` was classed as a non-consumer** despite living in a soundness module and calling the lemma directly. It restates time-shift homogeneity at `MinusTruthAt` by rewriting through `truthAt_tr`; it proves no axiom valid and currently has no consumer. The docstring records it explicitly rather than silently, so the classification is auditable.
- **`StarAxiom` gets no ledger row.** See Reasoned Exclusions in the plan and the Follow-ups section below.
- **C15's `DECL` alternation was widened rather than the `StarDerivationTree` row dropped.** This closed a real latent gate defect, not merely a missing allowlist entry: before the change the alternation read `theorem|lemma|def|abbrev|instance`, so C15's second assertion could not anchor a ledger row naming a **type** at all, and any future `inductive` row would have failed identically with `no such declaration`. The widening was tested in isolation against the same 75 rows: the narrow regex fails on exactly that one row, the wide regex passes all 75, and no other outcome changes — so the gap caused false failures, it did not permit false passes.
- **Regenerated inventory blocks were committed as generated**, even though the generator rewrites whole blocks and therefore also absorbed a concurrent session's in-flight line counts. A partially hand-edited generated block would be wrong by construction; the generated one is correct at generation time.

## Plan Deviations

- **Phase 1**: the conditional "if the count is greater than one" item — the count is greater than one at the declaration level but not at the schema level, so the docstring records both readings rather than a single number.
- **Phase 2**: prose edits stayed outside the generated blocks as required, but Phase 1's docstring addition changed `Soundness.lean`'s line count, so the generated inventory blocks had to be regenerated.
- **Phase 3**: no import cycle appeared, so the documented fallback branch was not taken. `StarSoundness.lean`'s `## Main Results` list never named the adapters and its docstring carried no prose siting them locally, so a `## References` bullet was added instead of editing Main Results.
- **Phase 4**: exactly one declaration was dropped for un-pinnability, `FormalSystem.StarLanguage.StarAxiom`. The plan predicted both `inductive`s would drop out; `StarDerivationTree` in fact measured `[propext]` and is pinned.
- **Phase 5**: five ledger rows, not six. Closed as `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` table.

## Verification

- Build: Success — `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build`, exit 0, "Build completed successfully (2648 jobs)".
- Sorry count: 0 in live scope. Every `sorry` under `FormalSystem/` is in `FormalSystem/Boneyard/` (archived, pre-existing); every live-scope grep hit is the word "sorry-free" in prose. This task's diff adds no `sorry`.
- Vacuous count: 0 introduced. One pre-existing tree-wide hit, `int_domain_universal` in `FormalSystem/Examples/TemporalStructures.lean`, is untouched by this task and is a genuine trivial proof of a true proposition.
- Axiom count: unchanged. `diff` of the 11 `^axiom ` lines under `FormalSystem/**.lean` at the pre-task commit against the current tree is empty — the axiom set is byte-identical.
- Tests: Passed — `PASS C1 lake build BimodalTest exits 0`.
- `bash scripts/check-module-invariants.sh`: `ALL CHECKS PASSED`, exit 0. `PASS C1` (both), `PASS C2`, `PASS C5` (6 allowlisted), `PASS INV`, `PASS C9` (zero task-number citations under `FormalSystem/`, `lakefile.lean`, `README.md`, `scripts/`), `PASS C14` (both), `PASS C15` (both; 58 anchors, all 75 rows anchored at their declaration), `PASS C20` (both tiers), `PASS C21`.
- C14 baseline integrity: `git diff` over the whole task shows four removed lines in `scripts/check-module-invariants.sh`, all of them comment prose or the `DECL` regex line being rewritten. No pre-existing `depends on axioms` baseline line was altered. Both heredocs list 106 declarations in identical order (`diff` clean).
- `bash .claude/scripts/check-task-references.sh`: `PASS: 0 unexempted task-reference occurrences across 4 tree(s)`.
- `grep -rn 'starValidIn_of_forall_total\|starValidIn_apply_total' FormalSystem Tests docs scripts`: empty.
- Files verified: Yes.

## The audit, in full

Direct consumers of `Semantics.TimeShift.timeShift_preserves_truth`, live tree, `FormalSystem/Boneyard/` excluded:

| Consumer | File | Class |
|---|---|---|
| `modal_future_valid` | `Metalogic/Soundness.lean` | schema validity |
| `mf_swap_valid` | `Metalogic/SoundnessLemmas/FrameClassVariants.lean` | schema validity (the dual; carries TF) |
| `minusTruthAt_timeShift` | `Metalogic/Conservativity/MinusLanguageSoundness.lean` | soundness module, but a restatement of the lemma, not a schema-validity proof; no consumer |
| `timeShift_preserves_truth_total`, `exists_shifted_history`, `box_const` | `Semantics/Truth.lean` | the lemma's own home module |
| `reverse_repr` | `Semantics/ShiftSet.lean` | shift-set machinery |
| `truthAt_allFuture_of_box`, `truthAt_allPast_of_box`, `forall_truthAt_time_invariant` | `Metalogic/Decidability/Verified/Decidable.lean` | decidability |
| `boxOracle_sound` | `Metalogic/Decidability/BiLasso/BoxOracle.lean` | decidability |
| `truthAt_box_iff`, `truthAt_regionHistory_offset` | `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean` | decidability bridge |

No other object language re-proves MF from time shift: L⁻ discharges it proof-theoretically (`MinusLanguage/AxiomDischarge.lean`, `dischargeModalFuture`), L⁺ transfers it (`Conservativity/Plus/Atomization.lean`'s `plusValidIn_of_tm` / `plusValidIn_swap_of_tm`, applied in `Plus/AxiomValidity.lean`), the coarsened independence models transfer it (`Independence/CoarsenedModels.lean`, `cValid_of_tm`), and L⋆ does not have it (`refute_modal_future`). `timeShift_preserves_truth_total` has no consumer anywhere in the live tree.

## Impacts

- A language-extension author now finds, in the first module they read for soundness, the exact question the extension has to answer — *does the extended point of evaluation shift rigidly with the history?* — plus the enumerated set that would have to grow if the answer is no, and the worked case (L⋆) where it is no.
- `StarValidIn.of_forall_total` / `.apply_total` are available to every module importing `FormalSystem.Semantics.StarValidity`, not only to `StarSoundness.lean`, and the L⁺/L⋆ adapter APIs are now shaped identically.
- Five TM⋆ headline results are machine-pinned by C14, so the new ledger rows go red on any change to their axiom dependencies rather than silently drifting.
- C15's second assertion now covers `inductive` declarations, so a type can carry a ledger row.

## Follow-ups

- **`FormalSystem.StarLanguage.StarAxiom` has no ledger row, and cannot get one under the current mechanism.** `#print axioms` reports it as `does not depend on any axioms`, a line C14's `grep 'depends on axioms'` filter drops, so the exact-string comparison can assert nothing about it; C2 applies the identical filter. Fabricating a baseline line would be a hard C14 failure. Pinning axiom-free declarations would require extending the C14 pipeline to retain the `does not depend on any axioms` form on both sides — a deliberate change to what the check asserts, well outside this task's "add names only" constraint. `StarAxiom` stays discoverable from the ledger through the L⋆/TM⋆ notation row and the new section's prose lead-in.
- **A concurrent session was editing this working tree throughout.** A set of this task's uncommitted README prose edits was silently lost once and had to be reapplied; every subsequent green sub-step was committed immediately. The regenerated inventory blocks and the root `README.md` totals in this task's commits therefore also reflect that session's in-flight line counts, and will be regenerated again at its own phase close.

## References

- `specs/574_record_soundness_invariant_and_tmstar_index/plans/01_record-soundness-invariant-tmstar-index.md`
- `specs/574_record_soundness_invariant_and_tmstar_index/handoffs/phase-1-handoff-20260909_050918.md` — the audit, in the form it was recorded at Phase 1 close
- `specs/574_record_soundness_invariant_and_tmstar_index/handoffs/phase-4-handoff-20260909_053246.md` — the raw `#print axioms` measurement
- `specs/574_record_soundness_invariant_and_tmstar_index/handoffs/phase-5-handoff-20260909_055017.md` — the ledger rows and the exclusion
