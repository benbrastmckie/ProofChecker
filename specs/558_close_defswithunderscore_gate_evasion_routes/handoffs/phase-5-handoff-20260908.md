# Phase 5 handoff — the four deliberate negative tests

## Immediate next action
Phase 6: append the four-routes section to `docs/development/NAMING_CONVENTION_DEVIATION.md`,
add C26 rows to `docs/development/MODULE_INVARIANTS.md`, then close on a full green gate.

## Sites, with closure status confirmed before use
- **Out of closure**: `FormalSystem/Theorems/ContextualProofs.lean` — its only importer is
  `FormalSystem/Automation/ProofStepExport.lean`, a `lean_exe` root. Re-measured, not assumed.
- **In closure**: `FormalSystem/Examples/TemporalStructures.lean` — imported by
  `FormalSystem/Examples.lean`, which is inside the 458-module `FormalSystem` root closure.
  Used for routes 3 and 4 so the "C16 still passes" contrast is not vacuous.

## The four cycles

### Route (1) — out-of-closure module. Full run.
Seed: `def negative_test_route_one : Nat := 0` in `ContextualProofs.lean`.
```
FAIL  C26  1 snake_case `def`/`abbrev` name(s) in the live tree
            FormalSystem/Theorems/ContextualProofs.lean:475: negative_test_route_one
```
Script exit **1**. In the SAME run: `PASS C1 lake build exits 0`, `PASS C16 env_linter batch ...
has no un-nolisted finding`, `PASS C25 all 13 lean_exe root module(s) ... compile` — every
build- and linter-based gate green on a real violation.
Restored -> `PASS C26 zero snake_case ... names`, `ALL CHECKS PASSED`, exit **0**.

**This route also found a bug in the check written in Phase 4.** The first run reported the
widened sweep unchanged at 179 findings even with the seed in place, while the same
`lake exe runLinter FormalSystem.Automation.ProofStepExport` run by hand a moment later reported
it. Cause: `lake exe runLinter <Module>` builds the runLinter EXECUTABLE, not the module it is
handed — the module is read back from its `.olean`, and an out-of-closure root's olean is stale
at that point in the script by construction. Fixed by building each root before linting it; the
re-run then reported **180 findings across 11 roots**, up from 179 across 10. Without the
negative test the widened sweep would have shipped silently linting the previous state of
exactly the modules it exists to cover.

### Route (2) — in-source suppression. `--no-build` (the assertion is purely textual).
Seed: `attribute [nolint docBlame] FormalSystem.Semantics.negativeTestRouteTwo` in
`FormalSystem/Semantics/ShiftSet.lean`.
```
FAIL  C26  1 in-source `nolint` attribute(s) not on scripts/nolint-attribute-allowlist.txt
            FormalSystem/Semantics/ShiftSet.lean:513: docBlame:FormalSystem.Semantics.negativeTestRouteTwo
```
Script exit **1**, with half one still printing `PASS C26` in the same run — neither half masks
the other. Restored -> both halves `PASS`, `ALL CHECKS PASSED`, exit **0**.

A separate probe confirmed the stale-entry branch: adding an allow-list row matching nothing
produced `INFO C26  1 allow-list entr(y/ies) match nothing in the tree`.

### Route (3) — the upstream `_1` heuristic. Full run. Attribute-decorated seed.
Seed: `@[inline] def negativeTestRoute_1 : Nat := 0` in `TemporalStructures.lean` — camelCase
apart from the `_1`, so the route is isolated, and decorated so the scanner's regex is exercised
beyond the plain-line case.
```
FAIL  C26  1 snake_case `def`/`abbrev` name(s) in the live tree
            FormalSystem/Examples/TemporalStructures.lean:507: negativeTestRoute_1
```
Script exit **1**. **In the same run, `PASS C16 env_linter batch ... has no un-nolisted
finding`** — `runLinter FormalSystem` reported zero on a module confirmed inside its own closure,
because Mathlib's name test skips a last component of that shape. `PASS C1` in the same run.
Restored -> `PASS C26`, `ALL CHECKS PASSED`, exit **0**.

### Route (4) — private declaration. Full run.
Seed: `private def negative_test_route_four : Nat := 0` in `TemporalStructures.lean`.
```
FAIL  C26  1 snake_case `def`/`abbrev` name(s) in the live tree
            FormalSystem/Examples/TemporalStructures.lean:507: private negative_test_route_four
```
Script exit **1**. **In the same run, `PASS C16 env_linter batch ... has no un-nolisted
finding`** and `PASS C1` — the declaration is inside the linted closure and still invisible to
the env_linter, because a non-public declaration is not exported to an importing module.
Restored -> `PASS C26`, `ALL CHECKS PASSED`, exit **0**.

## Residue
`git status --short` after all four restores shows no modification under `FormalSystem/` or
`scripts/`. Every seed was reverted from a byte-identical backup taken before it was applied.

## Deviations
The restore-and-re-PASS half of routes 2, 3 and 4 was observed under `--no-build`; the FAIL half
of routes 1, 3 and 4 was a full run, which is where the C1/C16/C25 contrast lives. Phase 6 closes
on a full run with a build.
