# Implementation Summary: Task #553

- **Task**: 553 - Decide convex history layer collapse (reframed: develop the categorical
  correlate of convex histories and the alternative consequence relations)
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T16:32Z
- **Completed**: 2026-09-08T17:12Z
- **Effort**: ~4.5 hours
- **Dependencies**: 552 (`align_history_vocabulary_with_paper`) — satisfied
- **Artifacts**: plans/01_convex-correlate-and-consequence-study.md,
  reports/01_convex-correlate-and-consequence.md, probes/01–04 + 2 scan scripts
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Executed all seven phases of the study plan. The deliverable is a research report answering the
task's questions (a)–(e) and the two the User focus adds — what the alternative consequence
relations are and what logics they give, and what the paper's `app:Structure` and this repository
have to teach each other — backed by four sorry-free Lean probes compiled against the live tree.
No file under `FormalSystem/` was modified; the verdict is **DEVELOP-AND-RETARGET**, with eight
follow-on task specifications and a paste-ready revised task description.

## What Changed

Nothing under `FormalSystem/`. All artifacts are confined to this task's directory.

- `specs/553_decide_convex_history_layer_collapse/reports/01_convex-correlate-and-consequence.md`
  — the study, §0 through §7 (~700 lines).
- `probes/01_bounded-index-diagnosis.lean` — `refute_modal_t_at_bounded_index`: the T-schema is
  FALSE at a bounded convex index off its domain, and holds on it. `tense_sees_outside_domain`,
  `atom_false_outside_domain`, `someFuture_top_true_at_bounded`.
- `probes/02_alternative-consequence.lean` — C1/C2/C3/C4 as Lean definitions.
  `refute_C3_someFuture_top` / `valid_C1_someFuture_top` (the `F⊤` separation),
  `truthC3_box_indep`, `pointHist` + `pointHist_isInterval`, `c3_box_someFuture_top_unsat`,
  `c3_modal_t/4/b/5_collapse`, `validC3_imp_validC4`, `refute_C2_modal_t`.
- `probes/03_axiom-survival.lean` — `germ_untl_false`, `c3_box_untl_unsat`, `c3_nec`,
  `c3_valid_imp_germ_valid`; six machine-checked axiom FAILURES (`serial_future`, `serial_past`,
  `discrete_symm_fwd`, `discrete_symm_bwd`, `discrete_propagate_fwd`, `discrete_box_necessity`)
  and twelve machine-checked SURVIVALS; **`truthC3_timeShift`** (C3 truth is invariant under
  index translation — the C3 analogue of `app:auto_existence`) and `c3_modal_future`.
- `probes/04_presheaf-skeleton.lean` — `Beh F l` (sections with domain exactly `[0, l]`),
  `restrict` along `Tr p`, **presheaf functoriality** (`restrict_id`, `restrict_comp`), the
  **Germs clause** `Beh(F)(0) ≅ W` (`germ_ofGerm`, `ofGerm_germ`), and `glue_seam` — the
  composition step of `app:gluing` at the interval site.
- `probes/scan-ungated-convex-binders.py`, `probes/scan-istotal-code-vs-doc.py` — the evidence
  scripts behind the report's §2.4 and §6.1 figures.

## Decisions

- **Verdict: DEVELOP-AND-RETARGET** (§7.1) — retarget the semantics to a total-by-construction
  index while growing the convex layer into the interval-site/presheaf apparatus and adding C3/C4
  as named second definitions. Argued from four findings, not adopted by default; the plan's
  fourth option was added because the description's three-way enum could not express it.
- **Machine-check `connect_future` rather than `temp_linearity`**, as the plan's Phase 4 permits
  ("one of the pair"); `temp_linearity` is audited by argument.
- **Deliver `app:gluing` as its composition step `glue_seam`** rather than the full glued
  section: the assembly plus the two restriction identities did not fit Phase 5's budget.
- **Do not create the follow-on tasks.** Creating them requires editing `specs/state.json`, which
  the plan's Non-Goals forbid. The specifications in §7.3 are the deliverable.

## Plan Deviations

- **Phase 5**, probe task altered: functoriality and Germs delivered as planned; the Scope
  Hypothesis's budget-permitting two-piece gluing was delivered as its composition step
  `glue_seam` only, with the section assembly and restriction identities handed to the §7.3
  follow-on task B. Annotated inline on the plan checklist item.
- One measurement in §1.3 was **corrected mid-study**: the dependent-`.states` count was first
  recorded as 249 using a loose grep that admits empty tokens; the correct figure is 133, of
  which only 64 are at the convex layer. §1.3, §1.6 and §6.1 carry the corrected number and say
  so.

## Verification

- Build: **Success** — `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build`
  exited 0, "Build completed successfully (2615 jobs)". A first attempt failed on
  `FormalSystem/Semantics/ShiftSet.lean:513: Unknown constant 'smokeProbeUnlisted'`; that file is
  511 lines and clean in git, and the probe name belongs to a concurrent task's
  inject-and-restore negative test. Re-run after that task restored the file: green.
- Probes: all four compile with `lake env lean`, exit 0, sorry-free (re-verified after the build).
- Sorry count (live tree, excluding `Boneyard/`): **0**. Total including `Boneyard/`: 160, all
  pre-existing and excluded from the build.
- Vacuous count: the grep heuristic returns **1** —
  `FormalSystem/Examples/TemporalStructures.lean:496`, `int_domain_universal … := trivial`. That
  is a genuine theorem (the history's domain *is* `fun _ => True`), not a placeholder; it is
  pre-existing from task 552 and untouched here. **0 genuine vacuous definitions.**
- Axiom count (live tree): **10**, unchanged — this task added none.
- `git status --short FormalSystem/`: empty. `specs/state.json`, `specs/TODO.md`,
  `specs/ROADMAP.md` unmodified by this task (the state.json/TODO.md diff in the tree belongs to
  task 558's concurrent status sync).
- Plan compliance: the only name extractable from the plan's `**Goals**` block is `TruthAt`,
  which is present in `FormalSystem/Semantics/Truth.lean`. The check is not otherwise meaningful
  for a research-only task that deliberately adds no library declaration.
- Files verified: Yes.

## Impacts

- The report's §7.1 verdict and §7.3 task specifications are executable without re-deriving the
  study; §6.1's per-obligation-class costing is the input a retarget plan needs.
- Probe 04 is a ready-to-promote skeleton for the behavior presheaf: functoriality and the Germs
  clause are proved and only need a home in the library.
- Probes 02 and 03 are a ready-to-promote C3/C4 semantics with 18 machine-checked axiom verdicts.
- §5.2 records two findings that run from this repository to the paper's category theory: that
  separatedness of `Beh(F)` is strictly stronger than the validity of *Determined* (witnessed by
  the repository's own drift-frame countermodel), and that the free-category presentation of
  `Path(F)` does not transfer to the logic (witnessed by `BiLasso/Annotation.lean`'s refutation).

## Follow-ups

- Eight follow-on task specifications in §7.3 (A–H), not created — creating them requires editing
  `specs/state.json`, which this task may not do.
- A proposed revised `description` for task 553 in §7.2, not applied.
- One **non-blocking user decision** (§7.4, item 4): whether C3's `□` should range over all
  convex histories through `x` (the paper's footnote, germs included — which makes `□(φ U ψ)`
  unsatisfiable) or over a cut-back range. Recommendation: keep the footnote's reading as the
  primary C3 and add the restricted variant as a named alternative.
- Seven items explicitly not settled, enumerated in §7.4.

## References

- `specs/553_decide_convex_history_layer_collapse/plans/01_convex-correlate-and-consequence-study.md`
- `specs/553_decide_convex_history_layer_collapse/reports/01_convex-correlate-and-consequence.md`
- `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` — `app:Structure`
  (`% TODO: review in full`) and the alternative-semantics footnote at line 1102
- `FormalSystem/ProofSystem/Axioms.lean` — the 45 `Axiom` constructors audited in §4
