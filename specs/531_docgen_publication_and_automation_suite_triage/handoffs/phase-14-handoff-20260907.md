# Task 531 handoff — after phases 1-16, awaiting one verification build

## Immediate next action

Run `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build` (detached, via
`Bash(run_in_background: true)`), then `lake test`, then
`bash scripts/check-module-invariants.sh`. Every phase except 17 is applied; the only thing
missing is a green full build over the applied state.

**A concurrent interactive session shares this working tree** and holds the build lock for long
stretches. It owns `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`
(actively edited, md5-pinned) and freezes `Saturation.lean`, `Tableau.lean`, `Fuel.lean`. Do not
edit those, do not fix errors reported in them, and do not raise the build timeout to outwait
them. A guard exit of 75 is a lock-wait timeout, not a failure: re-queue.

## State

Committed: phases 1, 2, 3, 4 (commits `cf230b310`, `5167fd5d3`, `3cd8b2f77`, `3e2d86c23`) and
phases 10, 15, 16 (`07333dca5`).

Applied but uncommitted, awaiting the build: phases 5, 6, 7, 8, 9, 11, 12, 13, 14.

`bash scripts/check-module-invariants.sh --no-build` is green except one C9 finding in
`MintBound.lean`, which belongs to the concurrent session.

## What each uncommitted phase did

- **5** — retired 13 tactic declarations and the two `TMLogic` Aesop modules to
  `FormalSystem/Boneyard/RetiredTactics/` (new, guard-first, with its own README and an entry in
  the archive's exception list). All had zero invocations outside their own defining files.
- **6** — replaced `Tactics/Helpers.lean` (1,210 lines) with `Tactics/{UserTactics,Meta,Search}.lean`
  (275 + 99 + 657). `Deduction.lean` had **no imports of its own** and inherited everything
  through `Helpers`; it now imports `ProofSystem`, `Metalogic.Core.DeductionTheorem` and `Lean`
  directly. That was the one real error the first build caught.
- **7** — verdict recorded in `Tactics/Deduction.lean`: adoption in
  `Metalogic/Core/DeductionTheorem.lean` DECLINED, on **circularity** rather than the expected
  `noncomputable` cost. Every candidate goal there is in one of the four case lemmas that
  `deductionTheorem` itself dispatches to.
- **8** — regenerated the automation inventories and rewrote the prose around them;
  `docs/reference/tactic-reference.md` rewritten; the four remaining `Automation/` prose
  citations converted to bib keys.
- **9** — `FormalSystem/MainResults.lean`: 27 headline results, each `#check`ed and followed by
  `#print axioms`, wired into `FormalSystem.lean`. No aliasing declarations, deliberately — see
  the file's own docstring.
- **11** — 8 shadowing renames (2 `BXCanonical`, 4 `SoundnessLemmas`, 2 `Kamp`) plus
  `Independence.realOrder`, `Perpetuity.pastKDist`, `DatasetValidator.DiversityReport`. 17 pairs
  down to 6, all recorded exceptions. New C22 check asserts the two `allAxiomNames` lists agree.
- **12** — 57 `lemma` → `theorem`. Live `lemma` declaration count is now **0**.
- **13** — 51 Uppercase_x names dot-namespaced; 54 remain, all in the two recorded leave-alone
  classes.
- **14** — C23, three naming-regression assertions, implemented by extending C16's namespace
  walker. Each verified to fail on a deliberate violation and to leave structure-member
  namesakes alone.

## Then: phase 17

Record the acceptance criteria one by one with their commands and output, write
`summaries/01_docgen-publication-automation-triage-summary.md`, and hand `MainResults.lean` to
the decidability-examples task as the artefact its examples should cite.

## Corrected dispatch premises to record in the summary

No lakefile `require`; no third axiom baseline; no `TM[...]` notation; no
fully-qualified-name duplication to fix; 51 (not 98) Uppercase_x renames; 57 (not 141) `lemma`
conversions, because both review figures counted `Boneyard/` and docstring prose.
