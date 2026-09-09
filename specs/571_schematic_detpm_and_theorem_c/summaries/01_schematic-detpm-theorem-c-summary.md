# Implementation Summary: Schematic `Det-pm` and Theorem C in its strongest form

- **Task**: 571 - Remove the atom restriction from Det-pm and state Theorem C in its strongest form
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T23:18:38Z
- **Completed**: 2026-09-08T23:59:00Z
- **Effort**: ~40 minutes
- **Dependencies**: None
- **Artifacts**: plans/01_schematic-detpm-theorem-c.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

`FormalSystem/Semantics/StarDeterminism.lean` carried the atom restriction in the **definition**
(`detPM (p : Atom)`), not merely in a theorem. The definition is now schematic in
`φ : StarFormula`, the (⇐) direction `detPM_of_deterministic` is schematic with it, the (⇒)
direction `deterministic_of_detPM` is held at the atomic fragment where it is strongest, and
`deterministic_starDefinable` is now a three-way equivalence hinged on `F.Deterministic`. The
module's choice-asymmetry prose was rewritten to state the asymmetry structurally, against
re-measured `#print axioms` values.

## What Changed

- `FormalSystem/Semantics/StarDeterminism.lean`
  - `detPM (φ : StarFormula) : StarFormula := .timeStore 1 (StarFormula.always (.timeStore 2
    (.timeRecall 1 (settledDisj φ))))` — `detPM (StarFormula.atom p)` is definitionally the
    former atom instance, which is why `deterministic_of_detPM`'s proof body compiled unchanged
    against the atomic hypothesis with no bridging lemma.
  - `detPM_unfold` widened to `(φ : StarFormula)`; proof body unchanged.
  - `detPM_of_deterministic (hD : F.Deterministic) (φ : StarFormula) : F.StarValidOn (detPM φ)`
    — consumes `settledDisj_of_deterministic` exactly as `sentDet_of_deterministic` does, reaching
    `states_eq_of_deterministic` through `star_truth_congr_ext` (via
    `star_congr_of_deterministic`) with no extension-theorem step.
  - `deterministic_of_detPM (h : ∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p)))` — held
    at atoms, byte-identical proof body, confirmed by `git diff`.
  - `deterministic_starDefinable (F : TaskFrame) :
    ((∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p))) ↔ F.Deterministic) ∧
    (F.Deterministic ↔ ∀ φ : StarFormula, F.StarValidOn (detPM φ))` — the three-way statement,
    with a docstring saying plainly that the atomic fragment already **forces** determinism while
    determinism **delivers** the full schema, and that this is not an appeal to uniform
    substitution.
  - Module docstring: numbered opener, `## Main Definitions`, `## Main Results`, the rewritten
    `## The single sentence letter is not uniform substitution` section (drift-frame
    counterexample `p → ⊡p` / `Fp → ⊡Fp` intact), and the rewritten `## Choice dependence`
    section.
- `FormalSystem/StarLanguage/README.md` — the Theorem C paper-label correspondence row now names
  the three-way statement and marks `detPM` schematic; still marked report-level.
- `FormalSystem/Semantics/README.md` — the `StarDeterminism.lean` inventory row records `detPM`
  as schematic, `deterministic_of_detPM`'s hypothesis at atoms, and the three-way equivalence.
- `README.md` (repo root) — regenerated `Live lines` figure in the generated inventory block
  (289,384 → 289,434), the fix the invariants gate itself prescribes.

## Decisions

- **Conjunction of two biconditionals, not `List.TFAE`.** The plan pinned this shape; its first
  conjunct is literally the pre-change `deterministic_starDefinable` after the type-forced
  retype, so the name is extended rather than weakened, and `.1` / `.2` give callers the two
  halves directly. `TFAE` has zero precedent under `FormalSystem/`.
- **The choice asymmetry is written structurally, never as an axiom-set difference.** All five
  measured declarations report the same axiom set, so any prose implying a `#print axioms`
  difference would be false. The section names which lemmas each direction routes through
  instead.
- **Four prose sites confirmed to need no edit** rather than touched: `FormalSystem/StarLanguage.lean:29`,
  `FormalSystem/Metalogic/Independence/README.md` result 7,
  `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`'s `fn_separates` docstring,
  and `FormalSystem/StarLanguage/README.md`'s "Where the L⋆ semantics lives" row (no declaration
  name moved). None asserts an atom restriction or the two-way shape.

## Plan Deviations

- None (implementation followed plan). The four "confirm, adjust only if stale" items in Phase 4
  are annotated in the plan as confirmed-needing-no-edit, which is the outcome those items
  provide for.

## Verification

- Build: Success — `lake build` exits 0 (2638 jobs); `lake build BimodalTest` exits 0 (2689 jobs).
  Every build ran detached through `.claude/scripts/lake-build-guard.sh`.
- Sorry count: 0 in every modified file; `C3  structural sorry inventory is ZERO across
  FormalSystem/ (Boneyard/ excluded)` PASS.
- Vacuous count: 0.
- Axiom count: 13 `^axiom ` declarations under `FormalSystem/`, unchanged from the pre-change tree.
- `bash scripts/check-module-invariants.sh` exits 0 — **ALL CHECKS PASSED**, 0 FAIL lines. The
  named checks: `C1 lake build exits 0` PASS, `C1 lake build BimodalTest exits 0` PASS,
  `C2 all four flagship axiom sets match baseline` PASS (no baseline edit was needed — the C2 and
  C14 baselines contain no `detPM`/`starDefinable`/`sentDet`/`settledDisj` name),
  `C3` PASS, `C9 zero task-number citations under FormalSystem/, lakefile.lean, README.md,
  scripts/` PASS, both `C14` lines PASS.
- `bash scripts/readme-lint.sh FormalSystem/StarLanguage FormalSystem/Semantics` — RESULT: PASS,
  no new finding (the two stale-date notices are in untouched directories).
- Measured axiom sets, re-measured after the change via `lake env lean` on a scratch
  `import FormalSystem` file:

  | Declaration | `#print axioms` (measured, post-change) |
  |---|---|
  | `FormalSystem.Semantics.settledDisj_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
  | `FormalSystem.Semantics.sentDet_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
  | `FormalSystem.Semantics.detPM_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
  | `FormalSystem.Semantics.deterministic_of_detPM` | `[propext, Classical.choice, Quot.sound]` |
  | `FormalSystem.Semantics.deterministic_starDefinable` | `[propext, Classical.choice, Quot.sound]` |

  Identical to the plan's pre-change baseline. The file asserts exactly two `[propext, …]`
  figures — in `## Choice dependence` and in `sentDet_of_deterministic`'s docstring — and both
  equal this measured value verbatim.
- Scope hypothesis closed: `grep -rn "detPM" --include='*.lean' FormalSystem/ Tests/` returns
  `FormalSystem/Semantics/StarDeterminism.lean` (the declarations) and one docstring line at
  `FormalSystem/StarLanguage.lean`; no Lean call site outside `StarDeterminism.lean`.
- Files verified: Yes.

## Impacts

- Downstream callers can now instantiate `Det-pm` at any `StarFormula`, not only at an atom, and
  `deterministic_starDefinable.1` / `.2` expose the two halves of the equivalence directly.
- The definability statement is now in the sharpest form the development supports, which is the
  sentence the paper should carry: the atomic fragment and the full schema define the same frame
  class.
- The converse's hypothesis is unchanged in strength, so no existing consumer of
  `deterministic_of_detPM` needs a stronger premise.

## Follow-ups

- The `Det-m` (world-register) half of Theorem C remains excluded, as recorded in
  `FormalSystem/StarLanguage/README.md`'s correspondence table.
- A single-fixed-letter strengthening of the converse is still not established, and no such claim
  is made anywhere in the module.

## References

- `specs/571_schematic_detpm_and_theorem_c/plans/01_schematic-detpm-theorem-c.md`
- `specs/571_schematic_detpm_and_theorem_c/handoffs/` — per-phase handoffs
- `FormalSystem/Semantics/StarDeterminism.lean`
- The PossibleWorlds determinism-axiom-correspondence report, §4 and §4.1
