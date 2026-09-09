# Implementation Summary: Task #575

- **Task**: 575 - Lift the state-locality fragment to L-plus and retire the atom-restricted stability lemma
- **Status**: [COMPLETED]
- **Started**: 2026-09-09T12:04:32Z
- **Completed**: 2026-09-09T13:05:00Z
- **Effort**: ~1 hour
- **Dependencies**: None
- **Artifacts**: plans/01_plus-state-locality-fragment.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

L⁺ now has the state-locality fragment L⋆ already had, built natively rather than borrowed:
`PlusFormula.StateLocal` by structural recursion over all seven constructors, the semantic
property `IsPlusStateLocal`, the seven-case soundness induction, two countermodel exclusions, and
the headline `φ ↔ ⊡φ`. The atom-restricted `stab_atom_of_atom` is deleted and both of its proof
consumers now run through the general `stab_of_stateLocal`. The three previously incompatible
shapes of the concept across the tower are related explicitly, including a proved biconditional
transfer along `ofPlus`.

## What Changed

- `FormalSystem/Semantics/PlusStateLocal.lean` — **new**. `PlusFormula.StateLocal` (7 arms), 7
  `@[simp]` clause lemmas, `not_stateLocal_someFuture`/`_somePast`, the closure lemmas
  `StateLocal.neg`/`.and`/`.or`; `IsPlusStateLocal`; `isPlusStateLocal_box` (`Iff.rfl`),
  `isPlusStateLocal_stab` (discharged from `stab_congr_sameState`),
  `isPlusStateLocal_of_stateLocal` (7 cases); `not_isPlusStateLocal_someFuture` and
  `not_isPlusStateLocal_somePast` on `NF`/`natModel`; `plusStateLocal_stab_iff`,
  `plusStateLocal_plusValid_iff_stab`, `stab_of_stateLocal`.
- `FormalSystem/Semantics/StateLocalTransfer.lean` — **new**. `stateLocal_ofPlus_iff`:
  `(ofPlus φ).StateLocal ↔ φ.StateLocal`, a biconditional, seven definitional cases.
- `FormalSystem/Semantics/PlusTruth.lean` — `stab_atom_of_atom` **deleted**; Main Results bullet
  redirected. `stab_state_only` is byte-identical.
- `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean` — imports the fragment module;
  both `atom_stab` arms now read `stab_of_stateLocal (stateLocal_atom p) M τ hτ t`, binding the
  `τ.IsTotal` they previously discarded as `_`.
- `FormalSystem/Semantics/PlusNonValidities.lean`,
  `FormalSystem/Semantics/StarNonValidities.lean`,
  `FormalSystem/Metalogic/Independence/StabUndefinable.lean`,
  `FormalSystem/PlusLanguage/Axioms.lean` — prose references retargeted (six sites in all).
- `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`, `docs/theorem-index.md`,
  `README.md`, `FormalSystem/README.md` — registration, module-index bullets, three index rows,
  regenerated inventory blocks.

## Decisions

- **`box` is state-local for L⁺, unconditionally** — settled by proof, not by analogy. It is
  `Iff.rfl`: the `box` clause quantifies over every total history and never mentions `τ`. No
  exclusion, no countermodel. Same for `stab`.
- `isPlusStateLocal_stab` is **discharged from `stab_congr_sameState`** rather than re-derived.
  That proof dependency is itself one of the three relations the task asked for, landed as code
  rather than prose.
- The `ofPlus` transfer lives in its own module. Proving it inside `PlusStateLocal.lean` would
  have made `Conservativity/Plus/AxiomValidity.lean` — which must import the fragment — depend on
  the whole L⋆ tower, inverting the L → L⁺ → L⋆ layering. `PlusStateLocal.lean` contains no
  `StarLanguage` reference.
- `IsPlusStateLocal`'s hypotheses were deliberately **not** weakened from `IsTotal` to
  `domain t`, so it differs from `IsStateLocal` in exactly one respect (the register vector).
  Recorded in the definition's docstring as a deferral.

## Plan Deviations

- **Phase 3** — the conditional task "if Phase 2 excluded `box`, add its countermodel here too"
  was skipped: Phase 2 proved `box` state-local, so there is no countermodel to add.
- **Phase 4** — the plan's scratch-`example` confirmation that `stab_of_stateLocal` typechecks at
  `stateLocal_atom p` was replaced by Phase 5's two real `AxiomValidity.lean` call sites: the same
  check against the actual consumers rather than a throwaway.
- **Phase 5** — the scan found a sixth prose reference the plan did not enumerate,
  `Conservativity/Plus/AxiomValidity.lean:32`. Per the phase's Scope Hypothesis the actual hit set
  governs, so it was updated too.
- **Phase 7** — the conditional "record the specific obstruction" task was skipped: the induction
  closed as a biconditional in all seven cases, so there is no obstruction.

## Verification

- Build: **Success** — `lake build` exits 0, 2648 jobs, run twice (once with `--no-share` to
  force a real build rather than a replay).
- Sorry count: **0** in this task's files; the repository-wide census reports hits only under
  `FormalSystem/Boneyard/` (archived, excluded by the gate's C3, which passes).
- Vacuous count: **0**.
- Axiom count: **0 new axioms**. Measured per declaration: `isPlusStateLocal_of_stateLocal`
  `[propext]`; `plusStateLocal_plusValid_iff_stab` `[propext, Classical.choice, Quot.sound]`;
  `stateLocal_ofPlus_iff` `[]` (axiom-free). Each value is what the `docs/theorem-index.md` row
  records.
- Gate: **`bash scripts/check-module-invariants.sh` exits 0**, zero failures, on a serialized
  run with the build included (C1-C26 and INV). An earlier run of the same gate failed C1, C5
  and C15; all three were concurrency artefacts, described in the note below.
- Residue: `grep -rn "stab_atom_of_atom" --include=*.lean --include=*.md .` returns hits only
  under `specs/`.
- Atomization route: `stab_state_only`'s statement is unchanged (`git diff` on `PlusTruth.lean`
  shows only the deletion and the docstring bullet); `Atomization.lean` still consumes it at
  `:198` and builds.
- Territory: `git diff --stat` shows no change under `FormalSystem/StarLanguage/` or to
  `FormalSystem/Semantics/StarStateLocal.lean` from this task.
- Every `False` arm of `PlusFormula.StateLocal` (`untl`, `snce`) has a matching
  `not_isPlusStateLocal_*` theorem.
- Zero task-number citations under `FormalSystem/` (gate C9 passes).

### Concurrency incident (recorded, not hidden)

Task 574 was implementing in the same working tree throughout. Two consequences:

1. Two of my `lake build` runs failed with `no such file or directory` and with three unrelated
   modules "logging failures" (`Automation.InterestingnessMetrics`,
   `WeakCanonical.BackAndForth`, `Decidability.Verified.Bridge.TemporalGate`). Both were races
   between concurrent `lake` processes on one `.lake` directory — the first self-inflicted, by my
   running `check-module-invariants.sh` alongside a guarded build. A clean serialized rebuild is
   green, and none of the three modules imports anything this task touched. The same gate run also
   failed C5 and C15 on `FormalSystem.StarLanguage.StarAxiom`/`StarDerivationTree` rows in
   `docs/theorem-index.md` — task 574's uncommitted rows, zero occurrences in `HEAD`, five in the
   working tree — which passed once that agent landed its allowlist entries and declaration
   anchors.
2. `bash .claude/scripts/git-snapshot.sh 575`, run before the destructive Phase 5, stashed and
   reverted **task 574's uncommitted work**, because the tree was clean of mine but dirty with
   theirs. Restored from `stash@{0}` (kept, not dropped): `.claude-extensions.json`, task 574's
   `.return-meta.json`, and 7 lost `specs/events.jsonl` lines (merged by `event_id`, no
   duplicates). Task 574's plan file and `specs/state.json`/`TODO.md` in the tree are *newer* than
   the stash and were left alone; its README work survived in commit `f0f8aba9c`. One residue
   remains for task 574 to fix, flagged rather than edited from here: its plan's **Phase 2 heading
   still reads `[NOT STARTED]`** although its Phase 2 commit landed.

## Impacts

- `stab_of_stateLocal` is now the semantic witness for TM⁺'s AS axiom, and it covers every
  Boolean combination of atoms, `□`-formulas and `⊡`-formulas at arbitrary arguments — not just
  atoms. Any future consumer needing `φ → ⊡φ` has it without a new lemma.
- `stateLocal_ofPlus_iff` makes the two fragments one concept: the L⁺ fragment is exactly the
  `ofPlus`-preimage of the L⋆ one, so a result proved on either side transfers.
- The `PlusFormula.StateLocal` clause lemmas are `@[simp]`, mirroring their L⋆ twins.

## Follow-ups

- `cValid_atom_stab` (`Metalogic/Independence/CoarsenedModels.lean`) remains atom-restricted. It
  is **not** covered by anything landed here: `CTruthAt`'s `stab` clause quantifies over
  `SameUnder K` (π-agreement), strictly weaker than `SameStateAt`, and its atom case rests on
  `CoarseModel.atom_inv`. Widening it means a parallel coarsened soundness induction (`atom` from
  `atom_inv`, `stab` from `c_stab_congr_sameUnder`, `box` from the history-free clause) — new
  mathematics in a module outside this task's territory. Full reasoning in the plan's Phase 6
  `#### Reasoned Exclusions`.
- The `PlusAxiom.atom_stab` **constructor** stays atom-restricted by design; widening it would
  change TM⁺ and every soundness/completeness proof over it.
- The fragment is sufficient, not complete: `Fp → Fp` is semantically state-local yet
  syntactically rejected. Recorded in the module docstring as a design choice.
- Task 574's plan Phase 2 marker, per the concurrency note above.

## References

- `specs/575_plus_state_locality_fragment/plans/01_plus-state-locality-fragment.md` — the plan,
  now carrying Phase 6's `#### Reasoned Exclusions` record
- `specs/575_plus_state_locality_fragment/handoffs/` — seven per-phase handoffs
- `FormalSystem/Semantics/StarStateLocal.lean` — the L⋆ twin mirrored arm for arm
- `specs/572_tense_free_stability_and_schematic_separation/plans/01_tense-free-stability-schematic-separation.md`
  — the prior round's classification vocabulary, reused by Phase 6
