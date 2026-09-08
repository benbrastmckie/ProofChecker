# Implementation Summary: Task #545

- **Task**: 545 - Decide whether TM_d (Dense) and TM_dc (Dedekind) are weakly complete
- **Status**: [COMPLETED]
- **Started**: 2026-09-07
- **Completed**: 2026-09-08
- **Effort**: ~6 hours
- **Dependencies**: 544
- **Artifacts**: plans/01_hg-completeness-dense-dedekind.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The two open H/G rows are now **recorded, evidenced, and scoped** rather than left implicit.
`.Dense` is **open but expected complete, with no obstruction found** — machine-checked evidence
that both closed rows' separating witnesses fail to transfer to it. `.RTime` is **open with its
obstruction named at declaration granularity**. Neither verdict could honestly be upgraded to a
completeness theorem inside this round, so none was stated: no theorem anywhere in the diff
concludes in `TMComplete _` or `Forward _`, and the `Conservativity.lean` prohibition was honoured
in full. What did land is the whole de-risking round, sorry-free: the two BL-semantics lemmas the
route needs, the machine-checked non-transfer of both witnesses, and the single reusable
chain-bundle interface any future canonical-model work will consume.

## What Changed

- `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` — added
  `blTruthAt_timeShift` (time-homogeneity of `BLTruthAt`, the BL mirror of
  `TimeShift.timeShift_preserves_truth`) and `bl_box_universal` (`□` is the **universal** modality
  over the whole model: history-blind by definition, time-blind by `Truth.box_const`). Both are
  corollaries of `truthAt_tr`, not fresh inductions. Module docstring extended. +62 lines.
- `FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean` — **new**, 287 lines.
  `sp_derivable_dense` and `sp_derivable_rtime`: the `.Base` witness `Sp` is a *theorem* of both
  open systems, because its right disjunct's inner formula is `Axiom.dn`. `not_blValidDense_z1`:
  the `.ZTime` witness `Z1` is *not* dense-valid, refuted on a fresh ℚ flow model
  (`qD`/`qF`/`qTM`/`qτ` plus `q_atom_iff`, `q_gp_iff_p`, `q_G_Gp_imp_p`, `q_F_Gp`, `q_not_Gp`,
  `q_not_true_at_zero`).
- `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean` — **new**, 250 lines. `chainSat`
  (Kripke satisfaction on a disjoint union of `D`-chains, `□` universal over both coordinates),
  `chainBundle_truth_lemma` (BL truth along a translate history matches it pointwise),
  `not_blValidIn_of_not_chainSat` (the transfer corollary) and its ℚ/ℝ instantiations
  `not_blValidDense_of_not_chainSat`, `not_blValidRTime_of_not_chainSat`.
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — module docstring only,
  +117 lines: the **canonical four-row status table** with the `.Dense` and `.RTime` verdicts, what
  a positive `.Dense` answer still needs, the named `.RTime` obstruction, and an explicit note on
  what the prohibition does and does not forbid.
- `FormalSystem/Metalogic/Conservativity.lean` — two import lines.
- `FormalSystem/Metalogic/Conservativity/README.md`, `FormalSystem/Metalogic/README.md`,
  `README.md` — module rows, key-results entries, a pointer to the canonical table, and
  regenerated inventory blocks.

### The verdicts

**`.Dense` (TM_d) — open, expected complete, no obstruction found.** Both closed rows are closed by
a *dichotomy witness*: a schema valid over the class because the class splits into two subclasses
H/G can tell apart. `FrameClass.Dense` does not split that way, and both existing witnesses are
now provably unavailable — `Sp` is a TM_d theorem, `Z1` is not dense-valid. This is evidence, not
proof; it says nothing about some third witness. The transfer half of the completeness route is
closed (`not_blValidIn_of_not_chainSat`), and the frame construction was already generic in
`Metalogic/Algebraic/FlowFrame.lean`. What remains is the canonical model: a BL-MCS layer over
`BLFormula` (`Metalogic/Core/` is `Formula`-only and does not transfer), canonicity for the eleven
Base axioms plus `DN`, bulldozing, and ℚ-realization via `Order.iso_of_countable_dense`. Borrowing
`BXCanonical/Chronicle/` is circular — it would require the contrapositive of the very forward
conservativity being proved.

**`.RTime` (TM_dc) — open, obstruction named.** The abstract Doets layer (`DoetsD1`/`DoetsD2`,
`doets_theorem_dense`) and its suppliers (`no_gaps_dense_prior`, `reynolds_theorem5`) are genuinely
generic and reusable. The gap is one level down: every existing discharge of the semantic side
conditions consumes a BL⁺-only axiom — `chronicleMonadic_semanticPriorU` consumes
`Axiom.prior_U_gap`, `…semanticPriorS` consumes `Axiom.prior_S_gap`, `…semanticSep` consumes
`Axiom.sep`; D1 needs the first two, D2 all three. None is expressible in `BLFormula`, which has
only `atom | bot | imp | box | allPast | allFuture`. So the row reduces to discharging
`SemanticPriorU`/`SemanticPriorS`/`SemanticSepOpen` (or weaker H/G-sufficient replacements for
D1/D2) from `CO` alone, on which nothing in this tree or in Mathlib bears. Two things compound it:
`CO` is not Sahlqvist, so the `.Dense` canonicity route does not carry over; and `sep` is named for
**separability**, which leaves a **negative** `.RTime` verdict genuinely live.

## Decisions

- **`□` is the universal modality, and `chainSat`'s box clause therefore carries no time
  argument.** This is the pivot of the whole round: BL over task frames is not a product logic in
  the hard sense, so the Kripke target is an indexed family of chains with a universal box, and a
  valuation-only truth lemma is possible at all.
- **No completeness or forward-conservativity theorem stated anywhere**, and no `sorry` used to
  approximate one. The `.Dense` verdict is recorded as *expected, unproved*, never as established.
- **The ℚ countermodel is a fresh model, not a variant of `Z1Countermodel.lean`'s.** That model
  lives at `ℚ ×ₗ ℤ`, which is not densely ordered. Density is used exactly once, in `q_gp_iff_p`,
  where the discrete model used a lexicographic successor instead.
- **`bl_box_universal` + `multiFamGen_total_eq_range` for the box case** of the truth lemma, per
  the plan. A shorter route existed (quantify the base point directly, using
  `multiFamGen_total_eq` and a `q'.2 - t` shift) and was tried first; the plan's route is both
  cleaner and the one the plan specified, so it is what landed.
- **`sp_derivable_*` keep the plan's exact `DerivationTree`-valued signatures.** A `Prop`-valued
  restatement at `BaseLanguage.Derivable` was written, built green, and reverted — it weakens the
  recorded Challenge statement from data to `Nonempty`-of-data. See Plan Deviations.

## Plan Deviations

- **Phase 1** altered: `blTruthAt_timeShift` and `bl_box_universal` landed immediately after
  `truthAt_trCtx` rather than between `truthAt_tr` and `truthAt_trCtx`, keeping the bridge and its
  context-level corollary adjacent. The F4 derivation chain went through as written, as a two-way
  `rw` rather than a `.symm`/`trans` composition. The report's verbatim `bl_box_universal` names
  `WorldHistory F`, which does not exist in this checkout; `ConvexHistory F` was substituted and
  the vestigial `σ₀` binder dropped, exactly as the plan's risk row anticipated.
- **Phase 2** altered: there is no `DerivationTree` frame-class weakening lemma in the tree, so
  `sp_derivable_rtime` restates the `.Dense` derivation at `.RTime` with
  `show FrameClass.Dense ≤ FrameClass.RTime from trivial` rather than transporting along a lift.
- **Phase 2** added: `attribute [nolint defsWithUnderscore] sp_derivable_dense sp_derivable_rtime`,
  with an in-source justification. **This is the one item worth a reviewer's eye.** The two
  Challenge signatures are `DerivationTree`-valued, hence `def`s, and `check-module-invariants.sh`'s
  C16 `env_linter` gate rejects snake_case `def` names. Three options were weighed: rename to
  camelCase (breaks the plan's fixed names and the citations to them), restate at
  `BaseLanguage.Derivable` (builds green, but weakens the recorded Challenge statement from data to
  `Prop` — the precise move `plan-compliance.md`'s Statement Fidelity section exists to catch), or
  keep the signatures and take a documented per-declaration exemption. The third was chosen: it
  preserves the contract exactly and the suppression is a naming-convention one, fully visible at
  the site. If a reviewer prefers camelCase names, that is a one-line rename plus three citation
  updates.
- **Phase 4** resolved a flagged risk rather than deviating: the plan allowed leaving the ℝ
  instantiation as a noted gap if `FrameClass.Sat .RTime` did not close in ~40 lines. It closed in
  one — `Real.exists_isLUB`, the same term `Metalogic/DedekindNonCompactness.lean` already uses —
  so `not_blValidRTime_of_not_chainSat` landed. Cost: one new Mathlib import,
  `Mathlib.Algebra.Order.Archimedean.Real.Basic`.
- **Phase 4** altered: both instantiations need an explicit `(fc := …)` ascription, since
  `BLValidDense`/`BLValidRTime` are `def`s rather than `abbrev`s and do not determine the tag
  metavariable in time to elaborate the `hSat` argument.
- **Phase 6** scope reconciliation: the plan's "8 new declarations" refers to the eight headline
  results, all of which landed with their planned names. The realised diff carries **19**
  declarations, the extra eleven being the ℚ countermodel scaffolding (`qD`, `qF`, `qTM`, `qτ`,
  `qτ_total`, six `q_*` lemmas) that Phase 2's own task list called for and that the plan's own
  ~170-line scope hypothesis budgeted. No phase drifted; the count line simply counted headline
  results, not scaffolding.

## Verification

- Build: **Success** — full `lake build`, 2614 jobs, exit 0.
- Sorry count: **0**. Every `sorry` occurrence in the five touched files is prose inside a
  docstring quoting the prohibition; `check-module-invariants.sh` C3 confirms the structural sorry
  inventory is zero across `FormalSystem/` (`Boneyard/` excluded, unchanged by this task).
- Vacuous count: **0** — no `:= True`/`Unit`/`trivial` placeholder anywhere in the diff.
- Axiom count: **unchanged**; no `axiom` declaration added.
- Prohibition audit: `git diff -U0 e23388918^ HEAD -- 'FormalSystem/**/*.lean' | grep -E "^\+" |
  grep -nE "(theorem|lemma)[^:]*:.*(TMComplete|Forward)"` → **empty**. No theorem or lemma in the
  diff concludes in `TMComplete _`, `Forward _`, or any of their four named specializations.
- Axiom audit, all 17 new declarations:
  - `[propext]` — `sp_derivable_dense`, `sp_derivable_rtime`, `chainSat`
  - `[propext, Classical.choice, Quot.sound]` — `blTruthAt_timeShift`, `bl_box_universal`,
    `not_blValidDense_z1`, `chainBundle_truth_lemma`, `not_blValidIn_of_not_chainSat`,
    `not_blValidDense_of_not_chainSat`, `not_blValidRTime_of_not_chainSat`, `qτ_total`,
    `q_atom_iff`, `q_gp_iff_p`, `q_G_Gp_imp_p`, `q_F_Gp`, `q_not_Gp`, `q_not_true_at_zero`

    All within the tree's standard set; nothing exotic.
- Repo gates: `check-metalogic-cycles.sh` PASS (exactly 1 directory-level cycle, unchanged);
  `check-module-invariants.sh` **ALL CHECKS PASSED**, with **no** new
  `module-invariants-manifest.txt` entry owed (both new modules are reachable via the
  `Conservativity.lean` aggregator, confirmed rather than assumed);
  `check-copyright-headers.sh` 0 nonconforming; `readme-lint.sh` PASS;
  `check-task-references.sh` PASS, 0 unexempted occurrences.
- `chainSat`'s `box` clause verified by inspection to carry no time argument.
- Tests: N/A (no `BimodalTest` changes; C1 `lake build BimodalTest` passes as part of the
  invariant check).
- Files verified: Yes.

## Impacts

- `not_blValidIn_of_not_chainSat` and its two instantiations are now the standing interface for
  refuting base-language validity at any frame class the flow frames satisfy. Any future
  canonical-model or refutation-probe work at `.Dense` or `.RTime` consumes it instead of
  re-deriving a transfer step.
- `bl_box_universal` is reusable well beyond this task: it is the machine-checked statement that
  BL's `□` over task frames is the universal modality, which fixes the Kripke target for any
  future completeness, definability, or expressivity work on the base language.
- `TMCompletenessReduction.lean`'s docstring is now the single canonical location for the four-row
  status. Previously that status was spread across `Metalogic.lean`, `Conservativity.lean`,
  `Fragment.lean` and an archived report.
- `check-module-invariants.sh` C16 now carries two grandfathered-by-attribute names. Anyone adding
  further `DerivationTree`-valued `def`s in this namespace will hit the same gate.

## Follow-ups

Three follow-up briefs, **in this order deliberately**. (a) precedes (b) because it is the cheaper
path to a *complete* outcome, and because a positive `.RTime` result is not the prior the
`sep`-is-separability signal supports.

**(a) The Dedekind refutation probe.** Is there an H/G formula valid on ℝ but refuted on a
Dedekind-complete non-separable dense unbounded chain (the double long line is the natural first
candidate)? A yes settles the `.RTime` row **negatively** and completely, at a fraction of the cost
of the positive route. The interface it consumes already exists:
`not_blValidRTime_of_not_chainSat`. Scope: build the candidate chain as a `TemporalOrder`, exhibit
the valuation, refute `chainSat` at a point. No canonical model, no MCS layer, no literature
ingest. Estimated small-to-medium.

**(b) The Dense canonical model.** The positive `.Dense` route, estimated 2 500–4 000 lines, with
per-phase sorry-free milestones: BL-MCS layer over `BLFormula` → canonical frame → canonicity per
axiom (eleven Base plus `DN`) → bulldozing → ℚ realization via `Order.iso_of_countable_dense`.
`TMComplete FrameClass.Dense` is stated **only in the last phase**, and only when it is proved.
The transfer step is already closed and must not be rebuilt.

**(c) The Dedekind positive route.** Gated on two things: ingesting Burgess or
Gabbay–Hodkinson–Reynolds first (the claim that `CO` axiomatizes the H/G logic of ℝ is
medium-confidence here and unverified against source), and on (b) landing, since the two share the
BL-MCS layer. `CO` is not Sahlqvist, so this needs a Bull/Burgess-style step-by-step or
Dedekind-completion construction rather than the canonicity argument of (b).

**One reviewer decision, non-blocking**: the `nolint defsWithUnderscore` exemption described under
Plan Deviations. Keeping it preserves the plan's exact Challenge signatures; removing it means
renaming `sp_derivable_dense`/`sp_derivable_rtime` to camelCase and updating three citations.

## References

- `specs/545_hg_completeness_dense_and_dedekind_verdicts/plans/01_hg-completeness-dense-dedekind.md`
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/reports/01_hg-completeness-dense-dedekind.md`
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/handoffs/phase-3-handoff-20260908.md`
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — the canonical four-row
  status table this summary's verdicts are recorded in
- `FormalSystem/Metalogic/Conservativity.lean` — the standing forward-conservativity prohibition
