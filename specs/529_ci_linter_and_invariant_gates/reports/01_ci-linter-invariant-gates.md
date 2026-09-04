# Research Report: CI, linter and invariant gates

- **Task**: 529 - WAVE 5 (publication infrastructure): turn on tests and Mathlib environment
  linters in CI, and close the review's gaps in `check-module-invariants.sh`
- **Started**: 2026-09-04T06:25:00Z
- **Completed**: 2026-09-04T06:35:00Z
- **Effort**: M (per review sizing: "Wave 5 — publication infrastructure (three tasks, M)")
- **Dependencies**: None for the mechanical wiring below. `simpNF` going live is soft-blocked on
  D-01 (the ten-pair global simp loop in `Automation/Normalization.lean`) per D-15's own
  "Depends on" line — see Finding 0 below, which reports this dependency is very likely already
  satisfied.
- **Sources/Inputs**: `specs/reviews/2026-09-01-lean-engineering/{D-tactics,E-docs,G-ecosystem}.md`,
  `specs/reviews/review-2026-09-01-lean-engineering.md` (H8 synthesis + Wave-5 task description),
  `.github/workflows/ci.yml`, `lakefile.lean`, `scripts/check-module-invariants.sh`,
  `scripts/readme-lint.sh`, local `.lake/packages/{mathlib,batteries,importGraph}` (installed at
  the pinned `v4.33.0-rc1` / resolved commits), `gh api` fetches of `leanprover/lean-action`
  (README, `action.yml`, `scripts/config.sh`, `scripts/lake_lint.sh`) and `leanprover/cslib`
  (`Cslib/Init.lean`, `scripts/CheckInitImports.lean`, `lakefile.toml`, `CONTRIBUTING.md`), and a
  live `lake check-lint` sandbox test against a temporary edit of `lakefile.lean` (reverted, no
  net changes).
- **Artifacts**: this report
- **Standards**: report-format.md, return-metadata-file.md

## Executive Summary

- **All nine MEASURED STATE claims verified**, with one correction: `test: false`/`lint: false`
  and the `[ci]` push-gate in `ci.yml` are exact; `#lint`/`runLinter`/`assert_not_exists` occur
  zero times repo-wide; no `Init.lean` exists under `FormalSystem/`; C9's traversal is
  `FormalSystem` only (line 536, confirmed 9/9 task citations in `lakefile.lean` slip through);
  C14's regex is exactly `\b(14|21|42|44)[[:space:]]+(axiom|constructor)` (lines 731, 738) and
  both stale documents (`implementation-status.md:36`, `examples.md:579`) interpose a word
  exactly as described; `readme-lint.sh` Check 4 (lines ~135-146) greps for the phrase but never
  computes or compares a `git log` date. **Correction**: `Automation/Normalization.lean` now
  carries only **2** `@[simp]` occurrences (not ten pairs) — the global simp loop D-15 names as a
  hard blocker on `simpNF` appears to already be resolved by intervening work; see Finding 0.
- **The review's sketched linter-wiring mechanism is superseded by a much simpler, verified
  native one.** Rather than writing a bespoke `FormalSystem.RunLinter` file (`import
  FormalSystem` + `#lint`) and a new `lean_exe`, Lake 5.0's native `lintDriver` package field
  plumbs directly to `batteries/runLinter` — the exact executable Mathlib's own `lakefile.lean`
  and CSLib's own `lakefile.toml` both point at, with **zero new Lean files**. I verified this
  live: adding `lintDriver := "batteries/runLinter"` to `package Logos where` alone makes `lake
  check-lint` return exit 0 (currently exits 1). See Findings 1-2.
- **`lean-action`'s `lint: true` literally runs `lake lint`, gated by `lake check-lint`.** If
  `lint: true` is flipped before `lintDriver` is configured, the CI job **hard-fails** at the gate
  check (`lean_action/scripts/config.sh`: `lake check-lint` failing prints `::error::` and exits
  1) — this is not a soft skip. `lintDriver` must land in the same change as `lint: true`.
- **G-08's `Init.lean` recommendation is CSLib-shaped, not Mathlib-shaped, and is a different
  concern from the `lintDriver`/`simpNF` wiring.** Mathlib's own `linter.checkInitImports` is an
  internal Mathlib self-test (parses `Mathlib.lean`, not reusable downstream — CSLib explicitly
  disables it, `weak.linter.checkInitImports = false`). CSLib's actual downstream pattern —
  `Cslib/Init.lean` + `scripts/CheckInitImports.lean`, using the `ImportGraph` package's
  `env.importGraph.transitiveClosure` — is directly portable: `ImportGraph` is already an
  **inherited transitive dependency** of BimodalLogic via `mathlib` (confirmed in
  `lake-manifest.json`), so no new `require` line is needed, only a new script. Confirmed that
  every `FormalSystem/*.lean` file except exactly one (`Automation/AxiomNames.lean`, zero
  imports) already imports at least one `Mathlib.*` module and therefore transitively imports
  `Mathlib.Init` already — the syntax-linter half of G-08 is thus largely a **codification and
  enforcement** gap, not a "linters aren't running at all" gap. See Finding 3.
- G-15's `assert_not_exists` targets are precise and narrow: `FrameClassValidity.lean` is the
  *only* `Semantics/` file importing anything from `ProofSystem/` (imports `ProofSystem.Axioms`
  only, not `ProofSystem.Derivation`/`Derivable`), so the invariant to encode in the "lower"
  files is stronger than the review's prose states — see Finding 4.
- D-18's traversal widening and docstring rewrite are mechanical and fully scoped: exactly 9 task
  citations in `lakefile.lean` (0 in `README.md`, 0 in `scripts/*.sh`), naming tasks 210, 205 (×2),
  206, 246, 242, 277, 279, 316. See Finding 5.

## Context & Scope

Task 529 is the "CI, linter and invariant gates" task named in Wave 5 of
`review-2026-09-01-lean-engineering.md`'s programme, covering findings D-15, D-16, D-18, E-06,
E-09, E-13, G-08, G-15, and the infrastructure half of synthesis finding H8. The task is
research-only: verify every MEASURED STATE claim in the delegation, and investigate doc-gen4/
Mathlib linter integration mechanics so planning has concrete, verified wiring rather than the
review's sketch. No files were modified (one `lakefile.lean` edit was made, tested, and reverted
during Finding 2's verification — `git diff --stat lakefile.lean` confirms no residual change).

## Findings

### Finding 0: D-01 (the global simp loop) appears already fixed — re-verify before flipping `simpNF` to blocking

D-15's own text states `simpNF` is dependent on D-01 landing first ("fix the loop before turning
`simpNF` on, or it fails immediately"). D-01's anchor was ten mutually-inverse `@[simp]` `rfl`
pairs in `Automation/Normalization.lean` (e.g. `neg_unfold`/`neg_fold`). As of this research pass,
`grep -c "@\[simp\]" FormalSystem/Automation/Normalization.lean` returns **2**, not ten pairs, and
one of the two remaining is `normalizeFormula_id : normalizeFormula φ = φ` at line 1207 — a single
idempotence lemma, not a mutually-inverse pair. This strongly suggests the simp set was already
detangled by an intervening task (state.json shows tasks 528, 533, 535, 536 completed since the
review). **I did not run a full `lake build` + `#lint`/`simp` smoke test to confirm** (out of
budget for a research-only pass with no build cache warmed); the planning phase should re-run the
`lean_multi_attempt`-style smoke test the review used (`simp` on `a.neg = a.neg` in
`Metalogic/Decidability/DecisionProcedure.lean`) before committing to `simpNF` as blocking, per
the file's own `ENFORCE_C*` convention (never flip a flag to enforced without the tree actually
satisfying it).

### Finding 1: CI wiring — `test: true` + `lint: true` is a two-line change, but `lint: true` requires `lintDriver` first or the job hard-fails

Verified via `gh api repos/leanprover/lean-action/contents/{README.md,action.yml,scripts/config.sh,scripts/lake_lint.sh}`:

- `lint: true` makes `lean-action` run `lake check-lint` as a **gate**, not a soft probe:
  ```bash
  # scripts/config.sh, LINT=true branch
  if ! lake check-lint; then
      echo "::error::lake check-lint failed: could not find a lint driver"
      exit 1
  fi
  ```
  This differs from `auto-config` mode, where a missing lint driver silently skips linting. An
  explicit `lint: true` with no configured driver **fails the CI job**, not skips it. Currently
  `lake check-lint` in this repo exits 1 (verified live, see Finding 2) — so `lint: true` cannot
  land in `ci.yml` before `lintDriver` lands in `lakefile.lean`, and both should be in the same
  commit/phase.
- On success, `lean-action` runs `eval "lake lint $LINT_ARGS"` (`scripts/lake_lint.sh`) — a plain
  `lake lint` invocation, no special flags needed by default.
- Removing the `if:` block's `contains(github.event.head_commit.message, '[ci]')` clause (and the
  `workflow_dispatch`/`pull_request` OR-conditions around it) is a pure deletion — `ci.yml`'s
  `on:` block already lists `push: branches: ["main"]` and `pull_request: branches: ["main"]`
  independently of the job-level `if:`, so removing the whole `if:` key (lines currently ~9-13)
  restores "run on every push and PR" without touching the `on:` triggers.
- `lakefile.lean:5` already declares `testDriver := "BimodalTest"`, matching the `lean_lib
  BimodalTest` target (`srcDir := "Tests"`, `roots := #[\`BimodalTest]`) at lines 20-21 — `test:
  true` requires no lakefile change at all, only the `ci.yml` flip.
- `lean-action`'s `lint-status`/`test-status` outputs (`SUCCESS`/`FAILURE`/`""`) are already
  echoed by the existing "Report results" step, which references
  `steps.lean-action.outputs.test-status` — that step needs no change, but could add
  `${{ steps.lean-action.outputs.lint-status }}` for symmetry.

### Finding 2: The linter driver — native `lintDriver`, not a hand-rolled `RunLinter.lean`

The review's sketch (`lean_exe runLinter` + `FormalSystem/RunLinter.lean` containing `import
FormalSystem` + `#lint`) describes the *pre-Lake-native* pattern. The actual mechanism, confirmed
three independent ways, is simpler:

1. **Lake 5.0 (installed: `5.0.0-src+62eed1d`, Lean `4.33.0-rc1`) has a native `lintDriver`
   package field**, parallel to the already-used `testDriver`:
   ```
   lake lint --help
   > By default, runs the package's configured lint driver.
   > A lint driver can be configured by either setting the `lintDriver` package
   > configuration option or by tagging a script or executable `@[lint_driver]`.
   > A definition in a dependency can be used as a lint driver by using the
   > `<pkg>/<name>` syntax for the 'lintDriver' configuration option.
   ```
2. **Mathlib's own `lakefile.lean:52`** sets `lintDriver := "batteries/runLinter"` — Mathlib does
   not define its own `#lint`-driving executable; it points at Batteries'. **CSLib's
   `lakefile.toml`** does the same: `lintDriver = "batteries/runLinter"`. Batteries defines the
   executable once, at `.lake/packages/batteries/lakefile.toml`:
   ```toml
   lintDriver = "runLinter"
   [[lean_exe]]
   name = "runLinter"
   srcDir = "scripts"
   supportInterpreter = true
   ```
   and `scripts/runLinter.lean` (full source read) imports `Batteries.Tactic.Lint`, resolves the
   modules to lint from the Lake workspace's default targets when none are given
   (`resolveDefaultRootModules`), builds them if needed, and runs `lintCore decls linters` where
   `linters := getChecks (slow := true) …` — this is the classic `#lint` check family:
   `simpNF`, `dupNamespace`, `docBlame`, `unusedArguments`, etc. (all defined in
   `Batteries.Tactic.Lint.*`, transitively available since Mathlib depends on Batteries).
3. **I verified this works for BimodalLogic with a live, reverted test**:
   ```bash
   $ sed -i 's/testDriver := "BimodalTest"/testDriver := "BimodalTest"\n  lintDriver := "batteries\/runLinter"/' lakefile.lean
   $ lake check-lint; echo "exit=$?"
   exit=0
   $ # reverted; git diff --stat lakefile.lean shows no residual change
   ```
   `batteries` is already a resolved package name in `lake-manifest.json` (a mathlib dependency,
   `inherited: true`), so `"batteries/runLinter"` resolves with **no new `require` line and no new
   `.lean` file** — just one line added to `package Logos where` in `lakefile.lean`.
4. **Module scope**: `runLinter`'s default-target resolution (`resolveDefaultRootModules`) reads
   `workspace.root.defaultTargets`. `lakefile.lean`'s `lean_lib FormalSystem` already carries
   `@[default_target]`, so `lake lint` with no arguments would lint (at least) `FormalSystem` by
   default; `lintCore` internally calls `getDeclsInPackage module.getRoot`, which scopes to
   declarations whose defining module's root package matches — the planning phase should verify
   whether this pulls in `BimodalTest` too (it is a second `lean_lib`, not marked
   `@[default_target]`) or needs an explicit `lake lint FormalSystem` module argument; either way
   this is a one-line `lint-args` tweak in `ci.yml`, not a wiring change.
5. **Reporting-vs-blocking split**: the review's `ENFORCE_C*` boolean-flag convention
   (`check-module-invariants.sh:69-78`) is the right home for a phased rollout — but note
   `lake lint`'s own `--linters`/`--lint-only` flags (seen in `lake lint --help`'s output above)
   already provide a native narrowing mechanism (`--lint-only .simpNF,.dupNamespace`) that could
   be used directly in `ci.yml`'s `lint-args` input for an initial blocking subset, with the full
   check suite added to `check-module-invariants.sh` as a separate, non-CI-blocking `C16` that
   shells out to `lake lint` (or `lake exe runLinter`, invoked directly with no `lintDriver`
   indirection) and greps its output for the enforced-subset linter names. Either shape
   (`lint-args` narrowing in CI, or a separate reporting/enforcing split in the invariants
   script) satisfies the delegation's "simpNF + dupNamespace blocking, rest reporting-only" ask;
   the planning phase should pick one rather than building both.

### Finding 3: G-08's linter-root ask is a CSLib-shaped downstream pattern, distinct from `lintDriver`

Two different things are both called "the linter" in this task and should not be conflated in the
plan:

- **Environment/`#lint` linters** (`simpNF`, `dupNamespace`, `docBlame`, `unusedArguments`, …) —
  wired via `lintDriver` / `lake lint`, covered fully by Finding 2. No `Init.lean` is needed for
  this half.
- **Syntax linters** (`Mathlib.Tactic.Linter.Style`, `UnusedTactic`, `FlexibleLinter`, etc.) —
  these activate automatically as `lake build` warnings once a file transitively imports
  `Mathlib.Init` (Mathlib's own comment: "it is imported by virtually *all* Mathlib files").
  I confirmed **every `FormalSystem/*.lean` file except exactly one**
  (`FormalSystem/Automation/AxiomNames.lean`, which has zero imports at all) already imports at
  least one `Mathlib.*` module, and therefore already transitively imports `Mathlib.Init` and
  already has these syntax linters active as (uncounted, unenforced) build warnings.
  `Mathlib.Init` itself explicitly documents `linter.checkInitImports` as
  `-- disabled, not relevant downstream` (`.lake/packages/mathlib/Mathlib/Init.lean:83`), and it
  is a **text linter** run via `lake exe lint-style` that parses `Mathlib.lean` specifically — it
  is Mathlib's own internal self-test, not a reusable downstream mechanism. CSLib confirms this by
  explicitly disabling it (`weak.linter.checkInitImports = false` in `lakefile.toml`) and instead
  shipping its own analogous downstream mechanism:
  - `Cslib/Init.lean` (full source read): a thin root file, `public import
    Cslib.Foundations.Lint.Basic` + `public import Mathlib.Init` + `public import
    Mathlib.Tactic.Common` + `public import Cslib.Tactic.GrindAttrs` — the canonical place to pin
    default-active linter/tactic imports for the downstream project.
  - `scripts/CheckInitImports.lean` (full source read): builds `CoreM.withImportModules
    #[\`Cslib]`, computes `env.importGraph.transitiveClosure`, filters for modules whose root is
    `Cslib` and whose transitive-import set does **not** contain `Cslib.Init`, diffs against a
    short `exceptions` list (files that would create a cycle by importing `Cslib.Init`, i.e.
    `Cslib.Init` itself and its own direct imports), and reports/exits nonzero on any violation.
  - Wired as `[[lean_exe]] name = "checkInitImports"` / `srcDir = "scripts"` / `root =
    "CheckInitImports"` in `lakefile.toml`, run via `lake exe checkInitImports`
    (`CONTRIBUTING.md:116`).
  - **`ImportGraph` is already an inherited transitive dependency of BimodalLogic** (confirmed:
    `lake-manifest.json` lists `"name": "importGraph", ... "inherited": true`, pulled in because
    Mathlib itself imports `ImportGraph.Tools` from `Mathlib/Init.lean:37`). So a
    `FormalSystem/Init.lean` + `scripts/CheckInitImports.lean` pair can be built with **zero new
    `require` lines** — a direct, near-verbatim port of CSLib's two files, changing only the
    root name (`FormalSystem` for `Cslib`) and the exceptions list (BimodalLogic's analogue of
    `Cslib.Foundations.Lint.Basic`/`Cslib.Tactic.GrindAttrs` — likely just `FormalSystem.Init`
    itself, since BimodalLogic has no local linter/tactic-attribute files that `Init.lean` would
    need to import and that would need a cycle exception).
  - The `weak.linter.mathlibStandardSet = true` / `weak.linter.flexible = true` lines in CSLib's
    `[leanOptions]` are the actual "linter set" activation for syntax linters beyond what
    `Mathlib.Init` enables by default; BimodalLogic's `lakefile.lean` DSL equivalent is the
    existing `theoryLeanOptions : Array LeanOption` array (currently `pp.unicode.fun`,
    `autoImplicit`) applied to both `lean_lib` targets — this is the natural place to add
    equivalent `weak.linter.*` entries if the plan phase wants to opt into more than
    `Mathlib.Init`'s defaults, though this is not strictly required by G-08's finding text.

### Finding 4: G-15's `assert_not_exists` targets, precisely

Verified the import graph directly rather than trusting the review's prose summary:

- `FormalSystem/Semantics/FrameClassValidity.lean` is confirmed the **only** file under
  `FormalSystem/Semantics/` importing anything from `FormalSystem/ProofSystem/` (`grep -rln
  "import FormalSystem.ProofSystem" FormalSystem/Semantics/` returns exactly this one file), and
  it imports **only** `FormalSystem.ProofSystem.Axioms` (line 8) — not
  `FormalSystem.ProofSystem.Derivation` or `.Derivable`. `ProofSystem.Axioms.lean` declares
  `inductive Axiom : Formula → Type` (line 111), `inductive FrameClass` (line 529), and `def
  Axiom.minFrameClass` (line 598). `ProofSystem/Derivation.lean` declares `inductive
  DerivationTree` (line 91) and `ProofSystem/Derivable.lean` declares `def Derivable` (line 69) —
  neither is reachable from any `Semantics/` file today.
- `assert_not_exists` command syntax, confirmed against Mathlib usage (`Mathlib/Order/
  Antichain.lean:28: assert_not_exists CompleteLattice`, `Mathlib/Data/Real/Basic.lean:31:
  assert_not_exists Finset Module Submonoid FloorRing`): a bare command taking one or more
  space-separated fully-qualified declaration names, conventionally placed right after the
  `import` block (before or after the module docstring; Mathlib does both).
- Recommended placement, following Mathlib's convention of asserting at the "root" of a hierarchy
  that a heavier downstream concept has not leaked in: add `assert_not_exists
  FormalSystem.ProofSystem.Axiom FormalSystem.ProofSystem.DerivationTree` (and optionally
  `.Derivable`, `.FrameClass` — `FrameClass` is more debatable since `TaskFrame`/`Truth` files may
  legitimately need a semantic notion of frame class that happens to share a name with
  `ProofSystem.Axioms.lean`'s inductive; the plan should check whether `Semantics/` already has
  its own `FrameClass`-shaped type before asserting against that specific name) to the "lower"
  files that do not currently import `ProofSystem` at all and whose docstrings already argue this
  in prose: `TaskFrame.lean`, `Truth.lean`, `WorldHistory.lean`, `FrameProperty.lean`, and
  `BLTruth.lean`/`BLValidity.lean` (the base-language twins). `Validity.lean` and
  `Correspondence/Galois.lean` should **not** carry the assertion — they already transitively
  import `FrameClassValidity.lean` and therefore `ProofSystem.Axioms` legitimately; the assertion
  belongs strictly below the one documented seam, not above it.

### Finding 5: D-18 traversal widening — exact scope

- `grep -niE '\b(tasks?[[:space:]]+#?[0-9]+|task-[0-9]+)\b' lakefile.lean | wc -l` → **9**,
  matching the review's count exactly. All 9 are in `lean_exe` docstrings, citing tasks 210, 205
  (×2, `benchmark_anchors` and `benchmark_oracle`), 206, 246, 242, 277, 279, 316.
- Same grep against `README.md` → **0**; against every `scripts/*.sh` → **0**. So widening C9's
  `find`/`grep` scope to include `lakefile.lean` and `scripts/` adds exactly the 9 `lakefile.lean`
  hits with no new `scripts/` findings today (the check should still cover `scripts/` per the
  delegation, since it is a standing invariant, not a one-off count).
- C9's current implementation (`check-module-invariants.sh:536-548`) is a single `grep -rniE
  --include='*.lean' --include='*.md' … FormalSystem 2>/dev/null`. Widening it to also scan
  `lakefile.lean` and `scripts/*.sh` (excluding `specs/**`, which is already the rule's own
  documented exemption) is a one-line change to the `grep` target list, e.g. replacing the bare
  `FormalSystem` positional argument with `FormalSystem lakefile.lean README.md scripts` (README.md
  is already 0 hits but is explicitly named in the delegation, so should be included for
  future-proofing) plus an `--include='*.sh'` add for the `scripts/` half.
- Rewrite guidance: the 9 docstrings currently read like `"... (Task 210)."` /
  `"... (Task 205)."`; the fix is to state what the executable *produces* — the file text already
  mostly does this before the trailing task citation (e.g. `"Dataset generator executable for ML
  training data."`), so the mechanical fix is deleting the trailing `` (Task NNN)`` parenthetical
  from each of the 9 docstrings, which the D-18 anchors list names individually.

### Finding 6: E-09 regex widening — exact fix

Current (lines ~731-733 and ~738-741):
```bash
STALE_AXIOMS=$(grep -rniE --include='*.md' \
  '\b(14|21|42|44)[[:space:]]+(axiom|constructor)' docs README.md 2>/dev/null || true)
STALE_AXIOMS_LEAN=$(grep -rniE --include='*.lean' \
  '\b(14|21|42|44)[[:space:]]+(axiom|constructor)' FormalSystem 2>/dev/null \
  | grep -v '/Boneyard/' | grep -i 'axiom' || true)
```
Confirmed misses: `docs/project-info/implementation-status.md:36` — `"All 21 TM axiom schemas
organized into base (17), dense (1), and discrete (3) layers"`; `docs/user-guide/examples.md:579`
— `"Modal K distribution is one of the 14 TM axiom schemas."`. The delegation's proposed pattern
`\b(14|21|42|44)[[:space:]]+([A-Za-z⁺+]+[[:space:]]+)?(axiom|constructor|schema)` matches both
(the `TM` interposed word, and `schema`/`schemas` as an accepted terminal word alongside
`axiom`/`constructor`) — verified by hand against both quoted strings. Both the markdown
(`STALE_AXIOMS`) and Lean-docstring (`STALE_AXIOMS_LEAN`) branches use the identical core pattern
and should both be updated for consistency, though only the markdown branch currently has a
confirmed hit.

### Finding 7: E-06 readme-lint.sh Check 4 — feasible, mirrors an existing working command

`readme-lint.sh` Check 4 (confirmed, full script read) currently only checks
`grep -qi "last verified\|last updated" "$readme"` — presence, never a date comparison. Adding a
comparison is mechanically straightforward and already has a working reference command in the
codebase: `FormalSystem/README.md` itself ends with `*Last verified: 2026-08-25 — ...*`, and
`git log -1 --format=%cs -- FormalSystem/README.md` returns a `YYYY-MM-DD` string directly
comparable via string `<` (ISO8601 sorts lexicographically). The fix is to extract the stamp date
with a `grep -oP` capture on the existing `last verified\|last updated` line, extract the
directory's last-change date via `git log -1 --format=%cs -- "$dir"`, and `warn` (not `err`, per
the delegation's "report, not gate") when the stamp predates the directory date. This should stay
in the existing Check 4 block (report-only, matching `readme-lint.sh`'s documented "what is gated
vs. merely reported" policy) rather than becoming a new gated check.

### Finding 8: D-16 (reporting-only C17) and E-13 (C18) — method is already fully specified, no new research needed

D-16's dead-declaration census method (tokenised base-identifier occurrence count across all
`.lean` and prose files, excluding the declaring line) and E-13's whitespace-normalized paragraph
duplication check (across `README.md`, `FormalSystem/README.md`, `Metalogic/README.md`,
`Metalogic.lean`) are both already fully specified by the review text with concrete anchors; no
further mechanism research was needed for these two. Two scoping notes for planning:
- E-13's own text calls its proposed check "C16"; that label collides with this task's H8-driven
  `simpNF`/linter check, which the delegation already renumbers to C16. The delegation's mapping
  (C17 = D-16 dead-declaration scan, C18 = E-13 paragraph duplication) is internally consistent
  and should be followed as given, rather than the review's original E-13 "C16" label.
- The docstring-coverage floor (delegation item 8) has two different measured baselines in the
  review that should be reconciled during planning, not treated as interchangeable: D-15 cites
  "**91.8%**" for "the core scope" (source: A-soundness or C-frames finding, not independently
  re-derived here), while G-12 measured "647 of 8,982" (~92.8%) repo-wide using a different
  heuristic (a `/-- -/` doc-comment in the three lines immediately above a
  `theorem`/`def`/`structure`/`inductive`/`class`/`abbrev`/`instance` line, explicitly noted as an
  over-reporting upper bound for declarations documented via an enclosing `/-! -/` section
  comment). A 90% floor is safely below both, so the specific number is not blocking, but the
  scope (core scope only, vs. repo-wide including Automation/Examples) and method (G-12's
  three-line heuristic is the only one with a reproducible script anchor named in the review)
  should be picked explicitly in the plan.

## Decisions

- Treat the linter wiring as **two separable halves** — `lintDriver`/`lake lint` (environment
  linters: `simpNF`, `dupNamespace`, `docBlame`, …) and `FormalSystem/Init.lean` +
  `CheckInitImports.lean` (syntax linters + import-graph enforcement) — since they use unrelated
  mechanisms, unrelated upstream precedents (Mathlib/CSLib both use `lintDriver :=
  "batteries/runLinter"`; only CSLib has the `Init.lean`+`CheckInitImports` pattern), and can land
  independently.
- Recommend **against** writing a bespoke `lean_exe runLinter` / `FormalSystem.RunLinter.lean`
  file, since `lintDriver := "batteries/runLinter"` is verified to work with zero new files and is
  the pattern both Mathlib and CSLib actually use today (the review's sketch describes an older or
  hypothetical pattern that is no longer how either upstream project wires this).
- Recommend the plan phase re-run a `simp`-loop smoke test before deciding whether `simpNF` starts
  blocking or reporting-only, since Finding 0 suggests D-01 is already fixed but this was not
  fully re-verified with a build in this research pass.

## Risks & Mitigations

- **Risk**: flipping `lint: true` in `ci.yml` before `lintDriver` lands in `lakefile.lean` hard-
  fails CI on every push/PR (Finding 1's `lake check-lint` gate). **Mitigation**: sequence the
  plan so both land in the same phase/commit, and locally run `lake check-lint` as an acceptance
  check before touching `ci.yml`.
- **Risk**: `lake lint`'s default module scope may not include `BimodalTest` (only
  `@[default_target]`-marked `FormalSystem` is guaranteed picked up by
  `resolveDefaultRootModules`). **Mitigation**: the plan should explicitly decide and test the
  `lint-args`/module-argument scope rather than assuming defaults are sufficient.
- **Risk**: turning on `simpNF` while D-01's fix is unconfirmed could reintroduce a build hang in
  CI. **Mitigation**: Finding 0's re-verification step, before flipping any `ENFORCE_C16` flag to
  1 or making `lake lint` blocking in CI.
- **Risk**: an over-broad `assert_not_exists FormalSystem.ProofSystem.FrameClass` could false-
  positive if `Semantics/` independently defines an unrelated same-named concept. **Mitigation**:
  Finding 4 flags this explicitly; verify no local `FrameClass`-named declaration exists under
  `Semantics/` before asserting against that specific name, or use the fully-qualified name only
  (which `assert_not_exists` requires anyway, so an unrelated local `FrameClass` under a different
  namespace would not collide).

## Appendix

### Verified command transcript (linter driver)

```
$ lake check-lint; echo "exit=$?"      # before change
exit=1
$ # add: lintDriver := "batteries/runLinter"  to  package Logos where
$ lake check-lint; echo "exit=$?"      # after change
exit=0
$ # reverted; git diff --stat lakefile.lean confirms no residual change
```

### Sources consulted (external, via `gh api`)

- `leanprover/lean-action`: `README.md`, `action.yml`, `scripts/config.sh`, `scripts/lake_lint.sh`
- `leanprover/cslib`: `Cslib/Init.lean`, `scripts/CheckInitImports.lean`, `lakefile.toml`,
  `CONTRIBUTING.md`

### Sources consulted (local, pinned to this repo's `v4.33.0-rc1` resolution)

- `.lake/packages/mathlib/Mathlib/Init.lean`, `.lake/packages/mathlib/lakefile.lean`,
  `.lake/packages/mathlib/scripts/lint-style.lean`
- `.lake/packages/batteries/lakefile.toml`, `.lake/packages/batteries/scripts/runLinter.lean`
- `lake-manifest.json` (dependency resolution for `batteries`, `importGraph`)
