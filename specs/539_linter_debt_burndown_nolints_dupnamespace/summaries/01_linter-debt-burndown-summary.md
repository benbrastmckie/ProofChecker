# Implementation Summary: Task #539

- **Task**: 539 - Draw down the linter debt that the CI/linter-gates work recorded rather than fixed
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T12:28:00Z
- **Completed**: 2026-09-07T15:05:00Z
- **Effort**: ~2.6 hours (dominated by six guarded full `lake build` runs)
- **Dependencies**: None
- **Artifacts**: plans/01_linter-debt-burndown.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

All nine plan phases closed. `scripts/nolints.json` fell from 307 grandfathered findings to 217,
a 90-entry (29%) reduction achieved entirely by genuine conformance — five of the six linter
categories were fixed outright and their rows removed with per-category `jq` filters, each removal
proved by a green `lake exe runLinter FormalSystem`. `dupNamespace` went from 14 findings to 0 by
relocating `structure Chronicle` out of its same-named namespace. The one surviving category,
`unusedArguments` (217), is now permanently grandfathered with a written, measured rationale.
`lake exe runLinter --update` was never run at any point.

## What Changed

**Lean sources**

- `FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean` — deleted the redundant
  `@[simp] theorem length_range_map` (its body was literally `by simp`, duplicating
  `List.length_map` + `List.length_range`); rewrote its 5 use sites onto the Mathlib lemmas.
  simpNF 1 -> 0.
- `FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean` — closed the
  `…BXCanonical.Chronicle` namespace immediately before `structure Chronicle`, declared the
  structure in the parent `…BXCanonical`, reopened the child namespace after it, and renamed the
  nine `def Chronicle.cN` to `def cN`. The reopened namespace re-declares its five `open`s, which
  a namespace close would otherwise have dropped for the rest of the file. dupNamespace 14 -> 0,
  with **zero downstream edits** — the 13 files opening that namespace all still compile
  unchanged, confirming the plan's scope hypothesis.
- 33 `defsWithUnderscore` declarations renamed to lowerCamelCase across `BaseLanguage/`,
  `Metalogic/`, `Theorems/`, `Semantics/`, `StarLanguage/` — 20 in `FormalSystem.BaseLanguage`
  (`discharge_*` -> `discharge*`, `notGNot_imp_F` -> `notGNotImpF`, …), 13 elsewhere
  (`co_derived` -> `coDerived`, `someFuture_mono` -> `someFutureMono`,
  `frame_condition` -> `frameCondition` — a `TemporalCarrier` *structure field*, so 12 projection
  and instance sites moved with it, …). 140 token occurrences updated across 28 files.
- `FormalSystem/Metalogic/WeakCanonical/GroupModel/RamseyFactorization.lean` — named the two
  anonymous instances `succOrderLexProdRatInt` / `predOrderLexProdRatInt`, retiring the
  Lean-generated `inst…_formalSystem` names that no whitelist route could reach.
- 51 `docBlame` findings cleared: 48 by docstring (33 structure fields across `ProofStep`,
  `RuleProfile`, `OperatorDistribution`, `EnrichedCountermodel`, `DecideCacheKey`,
  `TheoremEntry`, `MinCyc`; plus `QZStructure` and its three companions, 6 plain defs, and
  `IsContempEquivDenseCD`), 3 by in-source `attribute [nolint docBlame]` on `let rec`
  auxiliaries (`PriorityQueue.insert.insertSorted`, `bestFirstSearch.searchLoop`,
  `iddfsSearch.iterate`) — declarations Lean synthesizes, with no source position at which a
  docstring could attach.
- `FormalSystem/Automation/Tactics/Commands.lean` — docstrings on the second `syntax` command of
  each tactic pair plus `modalSearchParam`; this cleared all 4 `tacticDocs` findings as a side
  effect, exactly as the plan predicted.
- `FormalSystem/Automation/ProofSearch/Core.lean` — `@[nolint structureInType]` on
  `MembershipWitness` with the large-elimination reason stated at the site.

**Policy and documentation**

- `docs/development/NAMING_CONVENTION_DEVIATION.md` — Outcome table rewritten against measured
  post-burndown values (the old one asserted `defsWithUnderscore` = 0 while 33 were live, and
  `unusedArguments` = 124 against a live 217); new `unusedArguments` grandfathering section with
  the evidence; the 10 non-instance findings recorded as a named future item; "How to re-audit"
  corrected for `lint: true`; the surviving-exemptions section extended to the four new in-source
  attributes; and a new "it has already reopened once" record under "What would reopen this".
- `.github/workflows/ci.yml`, `scripts/check-module-invariants.sh` — comment-only corrections
  (307 -> 217, dupNamespace 14 -> 0, C16 category list, and the dupNamespace validation note
  replaced with the `lake env lean <file>` cheap-cross-check route).
- `scripts/nolints.json` — 307 -> 217 rows in five per-category `jq` removals.

## Decisions

- **`open` re-declaration in the Chronicle sandwich.** Closing a namespace ends every `open`
  scoped inside it. The relocation therefore re-declares the file's five `open`s after reopening
  `…BXCanonical.Chronicle`, and declares `open FormalSystem.Syntax` around the structure itself.
  Without this the file would not have elaborated past the structure.
- **`frame_condition` is a structure field, not a plain def.** The plan listed it among the 13
  renames without flagging that; it was renamed as a field, carrying 12 sites in
  `Verified/Bridge/Carrier.lean` with it.
- **Markdown references renamed too.** `co_derived` and friends appear in `FormalSystem/**/README.md`,
  `docs/project-info/known-limitations.md` and `docs/reference/API_REFERENCE.md`; leaving them
  would have left the documentation naming declarations that no longer exist.

## Plan Deviations

- None (implementation followed plan).

## Verification

- Build: **Success** — `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build`
  (detached, guarded), 2591 jobs, exit 0. Run after Phases 1, 2, 4, 6, 7 and 9 as the plan
  requires; Phase 3 used its `interface`-tier scoped build of `BaseLanguage.AxiomDischarge` +
  `Metalogic.Conservativity` (2312 jobs, exit 0).
- `lake lint`: exit 0.
- `lake exe runLinter FormalSystem`: exit 0 after every phase that edited `nolints.json`
  (1, 4, 6, 7) and at Phase 9.
- `scripts/nolints.json`: `jq 'length'` = **217**; `jq -r '.[][0]' | sort -u` prints only
  **`unusedArguments`**.
- `dupNamespace`: **0**, confirmed independently by the real linter
  (`lake env lean …/ChronicleTypes.lean`, zero warnings) and by C16's textual scanner.
- `bash scripts/check-module-invariants.sh`: **ALL CHECKS PASSED**, with both C16 halves green —
  `PASS C16 env_linter batch … has no un-nolisted finding` and
  `PASS C16 dupNamespace: zero declaration(s) …`.
- `grep -rn "length_range_map" FormalSystem/ Tests/`: no references.
- Sorry count in scope: **0** — no `sorry` term appears on any added line across the nine commits
  (the four `+`-lines matching the word are pre-existing "sorry-free" prose carried along by a
  rename). Repo-wide `sorry_count` is 160, unchanged from the pre-task baseline and confined to
  `FormalSystem/Boneyard/`.
- Vacuous count: **0** new (the one repo-wide match, `int_domain_universal` in
  `Examples/TemporalStructures.lean`, predates this work).
- Axiom count: **10**, unchanged from the pre-task baseline.
- `lake exe runLinter --update`: **never run**. Verifiable from the `nolints.json` diffs, which
  are five per-category removals, not wholesale rewrites.

## Impacts

- CI's `lake lint` gate now grandfathers 90 fewer findings, so a regression in `simpNF`,
  `docBlame`, `defsWithUnderscore`, `tacticDocs` or `structureInType` fails the build instead of
  being silently absorbed.
- `…BXCanonical.Chronicle` is now the `Chronicle` structure's own namespace, the standard
  Lean/Mathlib shape. `Chronicle.mk`, `Chronicle.f`/`.g`/`.dom` and `Chronicle.cN` are no longer
  double-namespaced; dot notation, anonymous constructors and `extends Chronicle` are unaffected.
- 33 renamed declarations are an API change for anything outside this repository that referenced
  them by name.
- Four in-source `@[nolint]` attributes now carry their reason at the declaration, where a diff
  reviewer sees it, rather than in a central JSON list.

## Follow-ups

- The 10 non-instance `unusedArguments` findings are genuine dead hypotheses
  (`branchTruthAt_untl`/`_snce`, `regionFrame`/`regionHistory`, `StepD.badComp_isBadInterval`,
  `ghr93_strategy_compose.compose_wc`/`_right`, `exists_singleton_class_between`,
  `kEquiv_classBlock`, `goodDense_unionClasses`). Removing them is a signature change with
  call-site fallout — recorded as a named future item in `NAMING_CONVENTION_DEVIATION.md`,
  deliberately out of scope here.
- Concurrent sessions were active in this repository throughout. Two consequences worth knowing:
  a concurrent commit swept in edits to three `FormalSystem/**/README.md` files this work made,
  and a concurrent `lake build` twice left the olean tree transiently incomplete, which surfaced
  as spurious `runLinter` "object file does not exist" failures until the tree was rebuilt.

## References

- `specs/539_linter_debt_burndown_nolints_dupnamespace/plans/01_linter-debt-burndown.md`
- `specs/539_linter_debt_burndown_nolints_dupnamespace/reports/01_linter-debt-burndown.md`
- `docs/development/NAMING_CONVENTION_DEVIATION.md`
- `scripts/nolints.json`
