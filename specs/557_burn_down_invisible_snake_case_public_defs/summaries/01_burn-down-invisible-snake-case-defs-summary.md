# Implementation Summary: Task #557

- **Task**: 557 - burn_down_invisible_snake_case_public_defs
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T09:00:00-07:00
- **Completed**: 2026-09-08T09:45:00-07:00
- **Effort**: ~14 hours planned; one dispatch, dominated by three full-tree Lean rebuilds
- **Dependencies**: 555 (completed)
- **Artifacts**: plans/01_burn-down-invisible-snake-case-defs.md, worklists/01_rename-worklist.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`docs/development/NAMING_CONVENTION_DEVIATION.md` declared `defsWithUnderscore` closed at 0 "by
genuine conformance" and `lake exe runLinter FormalSystem` agreed, while a textual scan of the
same tree found 174 snake_case `def`s outside `Boneyard/` — each invisible to that linter by one
of four independent mechanisms. All 174 were renamed to lowerCamelCase (plus 4 documentation
examples, 178 identifiers total), the one in-source `nolint defsWithUnderscore` outside
`UserTactics.lean` was deleted, every citation was updated, and the document's now-false closure
claim and burndown table were corrected. Every declaration kept its exact signature; only
identifiers changed.

## What Changed

**Renames, by phase (178 identifiers across 24 declaring files):**

- `FormalSystem/Theorems/ContextualProofs.lean` — 66 public `def`s renamed
  (`identity_in_ctx` -> `identityInCtx`, `box_4_ctx` -> `box4Ctx`, `until_F_ctx` -> `untilFCtx`,
  …), with ~107 call sites updated in `FormalSystem/Automation/ProofStepExport.lean`.
- `FormalSystem/Theorems/Perpetuity/Principles.lean` — `perpetuity_1`/`perpetuity_2` ->
  `perpetuity1`/`perpetuity2` (matching their already-renamed siblings `perpetuity3`-`perpetuity5`),
  plus the private `double_negation` -> `doubleNegation`.
- `FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean` — `sp_derivable_dense` /
  `sp_derivable_rtime` -> `spDerivableDense` / `spDerivableRTime`; the
  `attribute [nolint defsWithUnderscore]` line deleted and its `### Naming exemption` docstring
  section rewritten as `### Why these two are `def`s, and why they are not restated`.
- `FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean` — the public
  `nf_order_0_1` -> `nfOrder01`, plus 11 private renames.
- 103 `private def`s renamed across 20 files, the largest clusters being
  `BXCanonical/Chronicle/PointInsertion.lean` (20), `Metalogic/Decidability/Saturation.lean` (17),
  `EFGames/StaviCompleteness.lean` (11), `Theorems/TemporalDerived.lean` (10) and
  `IntegerModel/GoodStructuresModelSurgery.lean` (9).
- `FormalSystem/Syntax.lean` — 4 module-docstring example names (`necessity_p`, `future_q`,
  `possibly_p`, `always_p`) renamed for documentation consistency; not declarations.

**Citation updates (edited but declaring nothing renamed):**

- Lean: `Theorems.lean`, `FormalSystem.lean` (`#check` lines), `BaseLanguage/Axioms.lean`,
  `Examples/BimodalProofs.lean`, `Automation/FormulaEnumerator.lean`,
  `Automation/ProofStepExport.lean`, `Conservativity/TMCompletenessReduction.lean`,
  `Bundle/WitnessSeed.lean`, `Kamp/NfMultiAnchorBridge/InteriorGateGeneralK.lean` and
  `AggregateHookDischarge.lean`, `Tests/BimodalTest/Theorems/PerpetuityTest.lean`.
- Markdown/typesetting: `docs/development/NAMING_CONVENTION_DEVIATION.md` (rewritten, below),
  `LEAN_STYLE_GUIDE.md`, `NONCOMPUTABLE_GUIDE.md`, `TESTING_STANDARDS.md`,
  `docs/project-info/tactic-registry.md`, `docs/reference/operators.md`,
  `docs/user-guide/{architecture,examples,tactic-development,tutorial}.md`,
  `docs/research/{NONCOMPUTABLE,DEDUCTION_THEOREM_NECESSITY}.md`,
  `FormalSystem/Metalogic/{Conservativity,Bundle}/README.md`, `typst/SYNC-MAP.md`,
  `typst/chapters/{00-introduction,05-theorems,p4-dual-verification}.typ`,
  `latex/BimodalDemo.tex`.
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/plans/01_hg-completeness-dense-dedekind.md`
  — Goals bullets and the `## Lean Challenge Statements` block updated together so the two
  identifier sets still agree, with the original nolint divergence note kept verbatim and a
  resolution sentence appended.

**Document correction** — `docs/development/NAMING_CONVENTION_DEVIATION.md`: the `## defsWithUnderscore`
heading and its closure claim now name the instrument and its four blind spots
(out-of-closure modules; the upstream `_1`/`_2`/`_mathlib` heuristic; in-source `nolint`
attributes, which produce no finding at all; and `private` declarations, which no `env_linter`
can observe because `runLinter` reads a package by importing it — an upstream property Mathlib
shares, not a decision by this repository). The burndown table's `defsWithUnderscore` row gained a
four-state re-measurement table, the "What would reopen this" section records the third reopening
and why it differed in kind from the second (every standing gate stayed green throughout), and the
surviving-exemptions inventory records that the `DenseObstructionTransfer.lean` attribute is gone.

## Decisions

- **Mechanical name derivation, one documented exception.** Split on `_`; lowercase the first
  character of the first segment; upper-case the first character of every later alphabetic
  segment; keep digit segments adjacent. The single deviation, taken from the plan, is
  `sp_derivable_rtime` -> `spDerivableRTime` (not `spDerivableRtime`), following the
  `ZTime`/`RTime` scheme's lowerCamel row.
- **One genuine collision, resolved by a longer name.** Eight target names produced grep hits;
  seven were shown non-genuine by namespace/import-closure evidence (recorded in the worklist).
  The real one: `ctx_mp` -> `ctxMp` would collide with `Combinators.ctxMp`, a public `def` with a
  byte-identical signature and body that `TemporalDerived.lean` both imports (line 9) and opens
  (line 94). Renamed `ctxMpLocal` instead. Deduplicating the two identical declarations was
  deliberately not attempted — that is a semantic change, not a rename.
- **String literals are never rewritten.** The rename tool skips Lean string-literal spans, so
  `mkEntry "perpetuity_1"`, `mkEntry "perpetuity_2"` and `mkEntry "ctx_mp"` — dataset labels, not
  identifiers — survive unchanged. Proven by a byte-identical `proof_extractor` result.
- **No signature was restated.** In particular the `DerivationTree`-valued declarations were not
  moved to `BaseLanguage.Derivable`: `Nonempty`-of-data under the same name is strictly weaker,
  which `context/contracts/plan-compliance.md` Statement Fidelity forbids.
- **Fixtures were not exempted.** `probe_p`, `p_test`, `q_atom`, `mt_p`, `fa_p` and the rest were
  renamed like everything else; no declaration site stated a reason to exempt, so there are no
  Reasoned Exclusions anywhere in this task.

## Plan Deviations

- **Phase 1** altered: the public scan measures **75**, not the Scope Hypothesis's 71 — the four
  extras are `FormalSystem/Syntax.lean`'s module-docstring examples, exactly as the phase's own
  last task anticipated, so the real elaborated-declaration count is still 71 and the frozen total
  is 178 rather than 174.
- **Phase 1** altered: 8 of 178 target names produced collision-probe hits; 7 were non-genuine,
  and the one real collision (`ctxMp`) was resolved as `ctxMpLocal`.
- **Phase 3** altered: the measured `docs/` fanout is 9 files, not the 4 enumerated, and 6 further
  deliverables outside `docs/` (`typst/SYNC-MAP.md`, three `typst/chapters/*.typ`,
  `latex/BimodalDemo.tex`, `FormalSystem/Theorems/Perpetuity/README.md`) also cite the
  identifiers. All were updated, since Phase 10's sweep permits no survivor outside `specs/` and
  the `mkEntry` labels.
- **Phase 4** altered: the `Conservativity/README.md` row sits inside a
  `<!-- BEGIN GENERATED: inventory -->` block whose Lines column went stale when the docstring
  rewrite shortened the file by one line, so it was regenerated with
  `bash scripts/check-module-invariants.sh --emit-inventory` rather than hand-edited. That also
  refreshed derived totals in `FormalSystem/Metalogic/README.md` and the repo-root `README.md`.
- **Phase 6** added: `FormalSystem/Syntax.lean`'s four docstring example names were renamed here,
  since Phase 1 put them on the worklist but no phase owned them.
- **Phase 6** added: renaming shortened many `#eval … -- comment` lines; trailing-comment
  alignment was restored in `DatasetGenerator.lean` (45 lines), `Formula.lean` (20) and
  `Normalization.lean` (1). Whitespace inside comments only.
- **Phase 6** altered: no fixture was excluded; there are no Reasoned Exclusions.
- **Phase 7** added: `kv_body` -> `kvBody` is cited by name from
  `Kamp/NfMultiAnchorBridge/InteriorGateGeneralK.lean` (31 docstring/comment citations) and
  `AggregateHookDischarge.lean` (2). Both updated; comment-only, and neither file is in the
  phase's declared file set.
- **Phase 8** added: `past_tf_deriv` -> `pastTfDeriv` is cited from a comment in
  `Bundle/WitnessSeed.lean:167`, updated for accuracy.
- **Phase 10** added: the repo-wide sweep found 12 further stale citations the phase list did not
  anticipate — `deduction_with_mem` in `docs/development/NONCOMPUTABLE_GUIDE.md` (5),
  `docs/research/NONCOMPUTABLE.md` (1) and `docs/research/DEDUCTION_THEOREM_NECESSITY.md` (1);
  `past_tf_deriv` / `allFuture_bot_imp_neg_deriv` / `allPast_bot_imp_neg_deriv` in
  `FormalSystem/Metalogic/Bundle/README.md` (4); and `always_p` in `docs/user-guide/tutorial.md`
  (1). All updated.

**Seven files carried renames while absent from the task's declared `file_scope`**:
`Chronicle/CounterexampleElimination.lean`, `Chronicle/ChronicleMonadicBridge.lean`,
`Bundle/WitnessSeed.lean`, `IntegerModel/ShiftAndGlue.lean`,
`Kamp/NfMultiAnchorBridge/SubBracket2.lean`, `Kamp/NfMultiAnchorBridge/CarrierKv.lean`,
`Theorems/GeneralizedNecessitation.lean`. `file_scope` is descriptive, not enforced; recorded here
rather than left implicit.

## Verification

Every command below was run at the final gate, on the post-rename tree.

| Gate | Baseline (Phase 1) | Final | Result |
|---|---|---|---|
| `lake build` (full, guarded + detached) | green | `Build completed successfully (2615 jobs)`, exit 0, 0 errors | PASS |
| Public scan, `FormalSystem/` less `Boneyard/` | **75** | **0** (empty) | PASS |
| Private scan, `FormalSystem/` less `Boneyard/` | **103** | **0** (empty) | PASS |
| `lake exe runLinter FormalSystem` | 0 findings | 0 findings — now agreeing with the scans instead of contradicting them by 174 | PASS |
| `lake exe runLinter FormalSystem.Theorems.ContextualProofs` | 65 findings | 0 findings | PASS |
| `grep -rn "nolint defsWithUnderscore" FormalSystem/` | 2 sites | 1 site — only `UserTactics.lean:270`'s documented tactic-token block | PASS |
| `bash scripts/check-module-invariants.sh` | ALL CHECKS PASSED | **ALL CHECKS PASSED**, 0 FAIL; C16, C17/C23 (Uppercase_x + outer-shadows-inner), C24 and C25 (all 13 `lean_exe` roots compile) each green | PASS |
| `lake exe proof_extractor` | 487 registry / 487/487 processed / 12,077 steps | byte-identical; `data/proof_steps.jsonl` unchanged in git | PASS |
| `#print axioms spDerivableDense` / `spDerivableRTime` | `[propext]` (recorded by 545) | `[propext]` for both | PASS |
| Sorry census (`FormalSystem/`) | 162 lines, 2 outside `Boneyard/` | identical set, modulo line numbers | PASS |
| Axioms (`^axiom ` in `FormalSystem/`) | 11 | 11 | PASS |
| Vacuous single-line definitions | 1 (pre-existing) | 1 | PASS |
| `bash scripts/check-metalogic-cycles.sh` | — | PASS (exactly 1 directory-level cycle, as expected) | PASS |
| `bash scripts/check-copyright-headers.sh` | — | exit 0 | PASS |
| `bash scripts/readme-lint.sh` | — | RESULT: PASS | PASS |

- Build: Success (full `lake build`, 2615 jobs, exit 0)
- Sorry count: 0 new (census identical to baseline; the 2 non-`Boneyard/` entries are pre-existing)
- Vacuous count: 0 new (1 pre-existing, unchanged)
- Axiom count: 11, unchanged
- Tests: `BimodalTest` builds green (`PerpetuityTest.lean` cites two renamed declarations)
- Files verified: Yes

**Permitted survivors of the repo-wide old-name sweep**, recorded explicitly: three `mkEntry`
string labels in `Automation/ProofStepExport.lean` (lines 295, 304, 1381 — dataset field values,
not identifiers), four deliberate historical mentions in
`docs/development/NAMING_CONVENTION_DEVIATION.md` (which documents what each blind spot hid), and
everything under `specs/`, where historical artifacts legitimately keep the old names. Nothing
else outside `Boneyard/` still names a renamed declaration.

## Impacts

- A fresh textual scan now agrees with `runLinter` instead of contradicting it by 174. Two
  independent instruments back the "closed" claim, which is what closure has to mean for a
  category with this many invisibility routes.
- `NAMING_CONVENTION_DEVIATION.md` is measurably true again, and its blind-spot inventory is the
  standing warning that a finding-counting gate cannot detect a violation the linter never sees.
- The dataset contract is untouched: `data/proof_steps.jsonl` is byte-identical, so downstream
  consumers of the exported labels are unaffected.
- Task 558 (the gate that makes a fourth reopening fail a check) now has a clean tree to build
  its negative tests against, and this task's document edits deliberately stop short of the new
  four-routes section that 558 owns.

## Follow-ups

- `Theorems/Combinators.lean`'s `ctxMp` / `thmIn` are byte-identical duplicates of what were the
  private `ctx_mp` / `ctx_thm` in `Theorems/TemporalDerived.lean` (now `ctxMpLocal` / `ctxThm`).
  Deduplicating them is a semantic change and was out of scope here; it is a clean, small
  follow-up.
- Task 558 remains the durable fix: none of the four evasion routes produces a finding, so no
  finding-counting gate can catch a fourth reopening. This task closed the debt, not the hole.

## References

- `specs/557_burn_down_invisible_snake_case_public_defs/plans/01_burn-down-invisible-snake-case-defs.md`
- `specs/557_burn_down_invisible_snake_case_public_defs/worklists/01_rename-worklist.md` — the
  frozen 178-declaration worklist, its collision-probe evidence table, and the Phase 1 baselines
- `specs/555_fix_proofstepexport_and_manifest_out_of_closure_roots/plans/01_proofstepexport-repair-exe-root-gate.md`
  — invariant C25, the only gate that sees `ContextualProofs.lean`
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/plans/01_hg-completeness-dense-dedekind.md`
  — the originating Challenge block, updated here with its divergence note retained
- `docs/development/NAMING_CONVENTION_DEVIATION.md` — the corrected closure record
