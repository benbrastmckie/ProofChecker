# Research Report: FormalSystem.Init Transitive Import Adoption

**Task**: 541 - FormalSystem Init transitive import adoption
**Started**: 2026-09-08
**Completed**: 2026-09-08
**Effort**: Medium (small edit surface, large rebuild surface)
**Dependencies**: None
**Sources/Inputs**: - Codebase (`FormalSystem/`, `scripts/`, `lakefile.lean`, `docs/development/MODULE_INVARIANTS.md`), pinned Mathlib source under `.lake/packages/`, `lake exe checkInitImports` (live run), a validated static import-graph model
**Artifacts**: - specs/541_formalsystem_init_transitive_import_adoption/reports/01_init-transitive-import-adoption.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The measured count in the task description is stale: it is 457, not 434.** A live
  `lake exe checkInitImports` run reports `error: 457 module(s) do not (transitively) import
  FormalSystem.Init`. A second, independent static import-graph model reproduces the *exact same
  457-name list* (byte-identical under `LC_ALL=C sort`), so both the number and the identity of
  every module are confirmed by two methods.
- **The rewrite is 11 file edits, not 434 (or 457) import lines.** Restricted to the modules the
  check actually sees, the `FormalSystem`-internal import DAG has exactly **11 minimal elements** —
  modules with zero `FormalSystem.*` imports of any kind. Adding `import FormalSystem.Init` to
  those 11 and nothing else drives the missing count to **0**, simulated on the graph model that
  was validated against the executable. This set is also *minimal*: each of the 11 has no other
  `FormalSystem` import through which Init could arrive, so every one of them is necessary.
- **One of the 11 is an architectural conflict.** `FormalSystem/ForMathlib/Order/PFilter.lean` is
  governed by a documented rule ("Nothing under `FormalSystem/ForMathlib/` imports
  `FormalSystem.*`"). Recommended variant: **10 leaf edits + the aggregator
  `FormalSystem/ForMathlib.lean`** (which sits *beside* the directory, not under it) **+ a second
  `exceptions` entry for `FormalSystem.ForMathlib.Order.PFilter`**. Simulated: also 0 missing.
- **Flipping the check to gating requires a code fix, not just a wiring change.**
  `CheckInitImports.lean` ends with `return diff.length.toUInt32`, and a process exit status is
  masked to 8 bits: today 457 exits as **201**. A count that is an exact multiple of 256 would
  exit **0** and the gate would silently pass. It must return `1`.
- **`FormalSystem/Automation/AxiomNames.lean` needs no treatment for the check as scoped.** It is
  outside the root closure the check imports, so it never appears in the diff. The description's
  note that it "will need explicit treatment" is only true if the plan chooses to *widen* the
  check's scope, which is a separate decision (see Decisions).
- **Recommended approach reaches the acceptance criteria with no `sorry`, no new axiom, and no
  deferral.** The whole change is import lines, one `exceptions` entry, one return-value fix, one
  new gated check block, and two docstring corrections.

## Context & Scope

Researched: how many `FormalSystem` modules currently lack a transitive `FormalSystem.Init`
import, which files must actually change to fix that, whether an import cycle is possible, what
flipping `CheckInitImports` from reporting-only to gating requires, and how a new check is wired
into `scripts/check-module-invariants.sh`.

Constraints observed: the zero-debt policy (no `sorry`, no new axioms, no deferral); the
`--no-build` mode of the invariants harness; the documented `ForMathlib` dependency rule; the
`.claude/context/project/lean4/operations/long-builds.md` detach-and-guard contract for every
`lake` invocation (all builds in this research ran detached through
`.claude/scripts/lake-build-guard.sh`).

Out of scope for this report: the `Tests/BimodalTest` library (the check imports only the
`FormalSystem` root and never sees it), and the 168 archived `FormalSystem/Boneyard/` modules
(also outside the root closure, and never built).

## Findings

### Codebase Patterns

**Measured ground truth (both methods agree).**

| Quantity | Value | How measured |
|---|---|---|
| `.lean` files under `FormalSystem/` (+ root `FormalSystem.lean`) | 651 | `find` |
| Modules in the check's graph (root closure of `FormalSystem`) | 457 | `lake exe checkInitImports`, reproduced statically |
| Of those, missing `FormalSystem.Init` transitively | **457** (all of them) | both methods, identical name lists |
| Modules outside the root closure | 194 (168 Boneyard + 26 other) | static model |
| `.olean` files actually built under `.lake/build` | 496 | `find` |
| Minimal elements of the internal DAG (the leaves to edit) | **11** | static model |
| `lake exe checkInitImports` wall time (warm) | 4.2 s | `time` |

`FormalSystem.Init` is currently **not reachable from the `FormalSystem` root at all** — nothing
imports it — which is why every single module in the closure is reported. Its `.olean` exists
(built as a lake-library member), so a downstream file can import it without a fresh dependency
build.

**The 11 minimal elements, with the fan-out each one covers** (fan-out = the module itself plus
every reachable module that transitively depends on it):

| # | Module | File | Import lines today | Covers |
|---|---|---|---|---|
| 1 | `FormalSystem.Syntax.Atom` | `FormalSystem/Syntax/Atom.lean` | 7–12 | 426 |
| 2 | `FormalSystem.Automation.TruthNormAttr` | `FormalSystem/Automation/TruthNormAttr.lean` | 7 | 424 |
| 3 | `FormalSystem.Semantics.TemporalOrder` | `FormalSystem/Semantics/TemporalOrder.lean` | 7–10 | 238 |
| 4 | `FormalSystem.Metalogic.WeakCanonical.MonadicFO` | `FormalSystem/Metalogic/WeakCanonical/MonadicFO.lean` | 7–12 | 199 |
| 5 | `FormalSystem.Automation.LemmaDB` | `FormalSystem/Automation/LemmaDB.lean` | 7 | 187 |
| 6 | `FormalSystem.Semantics.Ultraproduct.IndexFilter` | `FormalSystem/Semantics/Ultraproduct/IndexFilter.lean` | 7 | 160 |
| 7 | `FormalSystem.Metalogic.SoundnessLemmas.DiscreteOrder` | `FormalSystem/Metalogic/SoundnessLemmas/DiscreteOrder.lean` | 7–9 | 38 |
| 8 | `FormalSystem.Metalogic.WeakCanonical.RealModel.OrderIsoReal` | `FormalSystem/Metalogic/WeakCanonical/RealModel/OrderIsoReal.lean` | 42–46 | 24 |
| 9 | `FormalSystem.Metalogic.Decidability.BiLasso.Periodic` | `FormalSystem/Metalogic/Decidability/BiLasso/Periodic.lean` | 7–8 | 19 |
| 10 | `FormalSystem.Automation.NormalizationAttr` | `FormalSystem/Automation/NormalizationAttr.lean` | 7 | 17 |
| 11 | `FormalSystem.ForMathlib.Order.PFilter` | `FormalSystem/ForMathlib/Order/PFilter.lean` | 7–8 | 8 |

Note `OrderIsoReal.lean`, whose import block starts at line 42 rather than 7 — a plan that
hard-codes "insert after line 8" would corrupt that file. Insert *after the last existing
`import` line* in each file instead.

**Why 11 is both sufficient and minimal.** Sufficiency: the internal graph is a finite DAG, so
every non-leaf module reaches a minimal element by following any chain of `FormalSystem` imports;
giving each minimal element Init therefore gives every module Init. Verified by simulation on the
validated model: 0 missing. Minimality: each of the 11 has *no* `FormalSystem` import, so a direct
import is the only route by which Init could arrive.

**No import cycle is possible.** `FormalSystem/Init.lean` imports exactly `Mathlib.Init` and
`Mathlib.Tactic.Common` — nothing under `FormalSystem.*`. A module importing `FormalSystem.Init`
therefore cannot create a back-edge into itself. The acceptance criterion "confirm no import cycle
is introduced" is satisfied structurally, and is additionally re-asserted by C1 (`lake build`) and
by `scripts/check-metalogic-cycles.sh`, which asserts the Metalogic directory-level cycle count is
exactly 1 (the documented `BXCanonical` ↔ `WeakCanonical` pair) and would fail on any other count.

**The `ForMathlib` conflict.** `FormalSystem/ForMathlib.lean` states the rule verbatim:

> **Nothing under `FormalSystem/ForMathlib/` imports `FormalSystem.*`.** The import direction is
> strictly `Mathlib → ForMathlib → FormalSystem.* → downstream`.

`.claude/CLAUDE.md` repeats it ("imports nothing from `FormalSystem.*`"). The rule is *documented
but not mechanically enforced* — `grep ForMathlib scripts/check-module-invariants.sh` returns
nothing. The subtree is currently a single file, `Order/PFilter.lean`. Three simulated variants:

| Variant | Edits | Result |
|---|---|---|
| A: Init in all 11 leaves | 11 files | 0 missing — but violates the ForMathlib rule |
| B: Init in 10 leaves, PFilter added to `exceptions` | 10 files + 1 exception | **1 still missing**: `FormalSystem.ForMathlib` (the aggregator) |
| **C (recommended)**: Init in 10 leaves + in `FormalSystem/ForMathlib.lean`, PFilter added to `exceptions` | 11 files + 1 exception | **0 missing**, rule preserved |

Variant C works because `FormalSystem/ForMathlib.lean` is the sibling aggregator *beside* the
directory, not a file *under* it, so importing `FormalSystem.Init` there is outside the rule's
stated scope — and the aggregator is already `FormalSystem`-facing by construction (it exists only
to re-export into this repo's tree).

**`exceptions` is the sanctioned escape hatch.** `scripts/CheckInitImports.lean` already carries
`def exceptions : List Name` documented as "Modules with technical constraints preventing a
`FormalSystem.Init` import", currently holding one entry (`FormalSystem.Init` itself). Adding
`FormalSystem.ForMathlib.Order.PFilter` with a one-line rationale comment is exactly the mechanism
CSLib provides for this case. Note the existing `FormalSystem.Init` entry is already correct and
needs no change: `env.importGraph.transitiveClosure` does not make a module its own import, so
`Init` lands in `noInitGraph` and is removed by `exceptions` once it becomes reachable.

**The gating defect.** `CheckInitImports.lean`'s `main` ends:

```lean
    return diff.length.toUInt32
```

A POSIX exit status is 8 bits. The live run returned **201** — which is `457 mod 256`, not a
meaningful code. Any count that is an exact multiple of 256 exits 0. This is harmless while the
check is reporting-only and no caller inspects the status; it is a silent-pass hole the moment the
check gates. The fix is to return a constant (`return 1` on a non-empty diff, `0` otherwise). This
is a deliberate, documented deviation from the near-verbatim CSLib port and should be commented as
such at the site.

**How `check-module-invariants.sh` wires a check.** The script (2700+ lines) follows one shape
everywhere, and a new check should copy it exactly:

1. A row in the `# Checks:` header block (currently B0, C1–C23, C9D, INV).
2. A row in the `# Companion files:` header block if a new data file is introduced (none needed here).
3. An `ENFORCE_C<n>=${ENFORCE_C<n>:-1}` declaration in the flags block near line 497, with an
   end-of-line comment saying enforced or not-yet-enforced.
4. A block with a `# ---` banner, a prose rationale, and `pass` / `fail` / `soft` / `note` / `info`
   helper calls — `soft` when the flag is 0, `fail` when it is 1.
5. Build-requiring checks are wrapped in `if [ "$RUN_BUILD" -eq 1 ]; then ... else info C<n>
   "skipped (--no-build)"; fi`. `C16` (`lake exe runLinter FormalSystem`) is the closest template:
   it is a `lake exe` invocation whose stdout/stderr is captured to a `mktemp` log, with `tail`ed
   lines emitted as `note`s on failure.

The next free identifier is **C24**. The check must sit inside the `RUN_BUILD` guard because
`CoreM.withImportModules` needs the built `.olean`s.

Because the harness's own `C1` step already runs `lake build`, C24's marginal cost is the 4.2 s
measured above.

**Documentation surfaces that will go stale in the same change** (C14 is a live tripwire for
exactly this class of drift):

- `FormalSystem/Init.lean` docstring: *"Rewriting the tree so every module actually imports
  `FormalSystem.Init` is an explicit follow-up, not done here."* — becomes false.
- `scripts/CheckInitImports.lean` docstring: *"Reporting-only: not wired into
  `check-module-invariants.sh`, and the ~430-file import rewrite … is an explicit follow-up"* —
  becomes false, and the "~430-file" figure is both stale (457) and wrong in kind (11 files).
- `docs/development/MODULE_INVARIANTS.md`: its "What It Checks" table currently stops at C15/C9D
  and is *already* missing C16–C23. Adding a C24 row is in scope; back-filling C16–C23 is a
  judgement call for the planner (see Decisions).
- `docs/development/MODULE_INVARIANTS.md` §"Adding a Check" mandates a **deliberate negative
  test** for a newly-gated check (the C15 precedent: prove the gate fails before trusting it).
  This should be an explicit acceptance step, not an afterthought.

**Not currently wired to CI.** `.github/workflows/ci.yml` runs `lean-action` with
`build/test/lint`; it does not invoke `scripts/check-module-invariants.sh` at all. So "wire into
`check-module-invariants.sh`" is the whole of the gating requirement — no workflow edit is implied,
and adding one would be scope creep.

### External Resources

**Pinned toolchain.** `lean-toolchain` and `lakefile.lean` pin Lean v4.33.0-rc1 / Mathlib tag
`v4.33.0-rc1` (resolved `79d0395a`), as `CLAUDE.md` records.

**`Mathlib.Init` at this pin uses the new module system.** Its header is `module` followed by
`public import ...` lines (37 of them), not plain `import`. Two consequences worth recording:

- Any tooling or script that greps for `^import` when reasoning about Mathlib's own graph will
  silently see zero imports. (This bit the first pass of this research; the corrected regex is
  `^(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?`.)
- `FormalSystem/Init.lean` is a *plain* (non-`module`) file importing a `module` file, which is
  supported and is what the current tree already does successfully.

**What `FormalSystem.Init` actually costs.** Its transitive closure over the pinned package set is
**1582 modules** (Mathlib + Batteries + Aesop + Qq + Plausible + ImportGraph + LeanSearchClient +
Cli). Per-leaf marginal additions:

| Leaf | Upstream modules today | After Init | Added |
|---|---|---|---|
| `Automation.LemmaDB` | 0 | 1582 | 1582 |
| `Automation.NormalizationAttr` | 0 | 1582 | 1582 |
| `Automation.TruthNormAttr` | 0 | 1582 | 1582 |
| `Syntax.Atom` | 483 | 1583 | 1100 |
| `Semantics.TemporalOrder` | 458 | 1582 | 1124 |
| `Semantics.Ultraproduct.IndexFilter` | 628 | 1582 | 954 |
| `Metalogic.SoundnessLemmas.DiscreteOrder` | 413 | 1582 | 1169 |
| `Metalogic.WeakCanonical.MonadicFO` | 845 | 1585 | 740 |
| `Metalogic.WeakCanonical.RealModel.OrderIsoReal` | 817 | 1588 | 771 |
| `Metalogic.Decidability.BiLasso.Periodic` | 1488 | 1582 | 94 |
| `ForMathlib.Order.PFilter` | 540 | 1587 | 1047 |

The three `Automation` attribute modules are the notable ones: they currently import only `Lean`
and would go from a Mathlib-free environment to the full 1582. Under variant C, `PFilter.lean` is
untouched and keeps its 540.

**Mathlib runs the equivalent check as a linter, not an executable.**
`.lake/packages/mathlib/scripts/lint-style.lean` registers `linter.checkInitImports`
(`defValue := false`), and `Mathlib/Init.lean` explicitly excludes it from the downstream-facing
linter set with the comment `-- linter.checkInitImports -- disabled, not relevant downstream`.
CSLib instead ships the standalone `lean_exe`, which is the shape this repo already ported. **No
change recommended** — the ported executable is the right mechanism for a downstream project, and
switching to the linter route would mean re-deriving a Mathlib-internal script that Mathlib itself
declares not-for-downstream.

**Related mechanism worth knowing about, not adopting here.** `Mathlib/Init.lean` registers
`linter.mathlibStandardSet` and documents that downstream projects can turn the whole Mathlib
syntax-linter set on with `set_option linter.mathlibStandardSet true` or the
`weak.linter.mathlibStandardSet` lakefile option. That is the natural *next* lever once every
module imports Init — but it is a behaviour change with its own warning burden and belongs in its
own task, not this one. Recording it here so the "why does Init exist" question has an answer that
does not immediately invite scope creep.

**A clarification the plan should not get wrong.** `set_option` in a `.lean` file is file-local; it
does not propagate to importers. `FormalSystem/Init.lean` cannot *set* repo-wide options — it can
only make linters and tactics *available* by importing them. Repo-wide option setting is the
lakefile's `theoryLeanOptions` (`pp.unicode.fun`, `autoImplicit := false`), which already applies
to both `lean_lib`s. Init is the import carrier; the lakefile is the option setter. Any plan phase
phrased as "Init.lean will set the linter options" is based on a false premise.

**Empirical linter-impact probe.** Two representative downstream files
(`FormalSystem/Syntax/Formula.lean`, `FormalSystem/ProofSystem/Axioms.lean`) were copied to a
scratch directory, given an added `import FormalSystem.Init`, and elaborated with
`lake env lean` against the existing `.olean`s. Output was **byte-identical to the baseline in both
cases** — no new warnings, no new errors. This is consistent with Mathlib's syntax linters
defaulting to off unless a linter set or option turns them on. It is a spot check on two files, not
a proof over 457, but it moves the "adoption floods the build with warnings" risk from *likely* to
*unlikely*.

### Recommendations

1. **Adopt variant C.** Add `import FormalSystem.Init` to the 10 non-`ForMathlib` minimal elements
   plus `FormalSystem/ForMathlib.lean`; add `FormalSystem.ForMathlib.Order.PFilter` to
   `exceptions` in `scripts/CheckInitImports.lean` with a comment naming the upstreaming rule as
   the technical constraint. Insert each new import *after the last existing `import` line* in the
   file (never at a fixed line number — `OrderIsoReal.lean` starts its imports at line 42).
2. **Fix the exit status before wiring the gate.** Replace `return diff.length.toUInt32` with a
   constant-`1`-on-failure return, and comment the deviation from the CSLib original.
3. **Update the two docstrings in the same change** (`FormalSystem/Init.lean`,
   `scripts/CheckInitImports.lean`). Both currently assert the deferral this task removes; C14
   exists to catch exactly this kind of stale in-tree claim.
4. **Wire as C24**, inside the `RUN_BUILD` guard, following the C16 template
   (`mktemp` log, `pass`/`fail`, `note`-ed tail on failure), with `ENFORCE_C24=${ENFORCE_C24:-1}`
   declared in the flags block. It ships *enforced* (no soft period), because the debt is cleared
   in the same change — the documented C12/C13/C14/C15 precedent.
5. **Run the mandated negative test.** Temporarily remove one leaf's Init import (or add a scratch
   leaf module without it), confirm `FAIL C24` and a non-zero script exit, restore, confirm
   `ALL CHECKS PASSED`. `docs/development/MODULE_INVARIANTS.md` §"Adding a Check" requires this;
   a gate that has never been observed to fail is not evidence of anything.
6. **Sequence the edits low-fan-out first.** Do `NormalizationAttr` (17) and
   `BiLasso.Periodic` (19) first and build; that exercises the mechanism against ~36 modules
   instead of the whole tree, and surfaces any surprise cheaply. Then the mid-tier, then
   `Syntax.Atom` (426) and `TruthNormAttr` (424) last, since those two invalidate essentially
   everything.
7. **Budget for a full rebuild and route every build through the guard.** All 457 modules will
   re-elaborate. Every `lake build` must be `Bash(run_in_background: true)` through
   `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- ...`, per
   `context/project/lean4/operations/long-builds.md`. The guard already reported *"memory pressure
   detected"* on this machine during research, so serialization is not optional here.
8. **Do not widen the check's scope in this task.** Leave the 26 non-Boneyard and 168 Boneyard
   out-of-closure modules alone (see Decisions).

## Decisions

- **D1 — The authoritative count is 457.** The task description's 434 is superseded. Both the
  executable and an independent static model agree on 457 and on the identical name list. Any plan
  or summary quoting 434 as current state will be wrong; quote it only as the historical figure
  recorded when the mechanism landed.
- **D2 — Variant C over variant A.** Preserving the documented `ForMathlib` upstreaming rule is
  worth one `exceptions` entry. Variant A would silently invalidate a rule stated in two places
  (`FormalSystem/ForMathlib.lean` and `.claude/CLAUDE.md`) and make the one file in the tree that
  is meant to be deletable-on-upstream depend on a repo-local module.
- **D3 — `AxiomNames.lean` gets no import.** It is outside the closure the check imports, so it
  cannot fail the check. Adding `import FormalSystem.Init` there would take a deliberately
  Mathlib-free leaf (shared by two `lean_exe` roots precisely because it is minimal, per its own
  docstring and C22) to 1582 upstream modules for zero gate benefit. Record this as an explicit
  decision, since the task description anticipated the opposite.
- **D4 — The check's scope stays the root closure.** Widening `withImportModules` to cover the
  26 out-of-closure live modules (mostly `lean_exe` roots) and/or the archive is a separate design
  question with its own cost, and CSLib/Mathlib both scope their equivalent check to the library
  root. Doing it here would turn a bounded task into an open one.
- **D5 — C24 ships enforced, no `ENFORCE_C24=0` soft period.** The debt is cleared by the same
  change, matching the C12/C13/C14/C15 precedent that the harness documentation records. The flag
  still exists (named and defaulted in the script) because the harness's own documentation
  requires flags to live there rather than on the command line.
- **D6 — Back-filling C16–C23 into `docs/development/MODULE_INVARIANTS.md` is left to the
  planner.** The table is already 8 checks stale. Adding only a C24 row is correct-and-minimal;
  back-filling is a real improvement but is unrelated documentation debt and would enlarge the
  change. Flagged, not decided.

## Risks & Mitigations

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | **Full-tree rebuild.** Editing `Syntax.Atom` (426 dependents) and `TruthNormAttr` (424) invalidates nearly every `.olean`; Lean hashes whole files, so even the docstring edits contribute. | High (time) | Detach + guard every build per `long-builds.md`. Sequence low-fan-out leaves first (Recommendation 6) so a mistake is caught before the expensive invalidation. Commit at each green sub-step. |
| R2 | **Exit-code truncation makes the gate a no-op at count ≡ 0 mod 256.** | High (correctness of the gate itself) | Return a constant; then run the mandated negative test to observe a real `FAIL C24`. |
| R3 | **New linter warnings across 457 modules** once Mathlib's syntax linters become importable everywhere. | Low, measured | Two-file `lake env lean` probe showed byte-identical output. Confirm on the first low-fan-out build; if warnings do appear, they are visible in `lake build` output and are addressed in-tree, never by reverting the import. |
| R4 | **`ForMathlib` rule violated** by the naive 11-leaf edit. | Medium (architectural) | Variant C. |
| R5 | **C14 documentation tripwire fires** on the two now-false docstrings. | Medium, certain if ignored | Update `FormalSystem/Init.lean` and `scripts/CheckInitImports.lean` in the same change; both currently assert the deferral in prose. |
| R6 | **Hard-coded line numbers corrupt `OrderIsoReal.lean`**, whose imports start at line 42. | Medium | Insert after the last `import` line, matched by content, in every file. |
| R7 | **Memory pressure**: the guard already warned during this research. | Medium | `lake-build-guard.sh` serialization; do not run concurrent builds from other sessions during the rebuild. |
| R8 | **Three `Lean`-only attribute modules gain 1582 upstream modules**, changing their elaboration environment. | Low | They are attribute and environment-extension declarations whose dependents already import Mathlib; verify with the low-fan-out-first build order and `lake build`. |

No approach considered here requires a `sorry`, a new axiom, or any deferral: the entire change is
import lines, one exception entry, one return value, one check block, and docstring corrections.
The task is fully completable to the zero-debt standard.

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task contains no proof obligations — the work
  is import-graph and build-tooling only, with no goal state to close.

## Context Extension Recommendations

- **Topic**: Import-graph reasoning for Lean repositories under the new module system.
  **Gap**: `.claude/context/project/lean4/` has no guidance on computing or reasoning about a
  project's import DAG, and nothing warns that a `^import` regex silently returns nothing on
  Mathlib's `module` / `public import` files at this pin — a trap this research fell into once
  before catching it by cross-validation.
  **Recommendation**: add `context/project/lean4/patterns/import-graph-analysis.md` covering the
  correct import regex, the "edit the minimal elements, not every module" principle, and the
  practice of cross-validating a static model against `lake exe` / `ImportGraph` ground truth.
- **Topic**: Exit-status truncation when a Lean `main` returns a count.
  **Gap**: nothing in the Lean context warns that `return n.toUInt32` from `main` is masked to 8
  bits, which turns a count-returning checker into a silently-passing gate at multiples of 256.
  **Recommendation**: a short entry under `context/project/lean4/patterns/` (or an addition to the
  MCP/tooling guide) stating that any `lean_exe` intended to gate must return a constant.

## Appendix

### Commands run

```bash
lake exe checkInitImports                                  # ground truth: 457, exit 201
bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- exe checkInitImports
lake env lean <scratch copy with added Init import>        # linter-impact probe
find FormalSystem -name '*.lean' | wc -l                   # 651
find .lake/build/lib/lean/FormalSystem -name '*.olean' | wc -l   # 496
```

Plus a Python import-graph model (comment-stripped header parse over `FormalSystem/**/*.lean` and
`.lake/packages/*/**/*.lean`) used to compute the closure, the minimal elements, the three
adoption variants, and the per-leaf upstream-module counts. Its 457-name output was diffed against
the executable's under `LC_ALL=C sort` and found identical.

### Key files

- `FormalSystem/Init.lean` — the root to be adopted (imports `Mathlib.Init`, `Mathlib.Tactic.Common`)
- `scripts/CheckInitImports.lean` — the checker (`exceptions` list; the `toUInt32` return)
- `scripts/check-module-invariants.sh` — the harness (flags block near line 497; C16 template near line 1906)
- `lakefile.lean` — `lean_exe checkInitImports`, `theoryLeanOptions`
- `FormalSystem/ForMathlib.lean` — the dependency rule
- `docs/development/MODULE_INVARIANTS.md` — check table and §"Adding a Check" (negative-test mandate)
- `.claude/context/project/lean4/operations/long-builds.md` — detach-and-guard build contract

### The 11 minimal elements

Listed with fan-out in the Codebase Patterns table above. Under variant C, edits 1–10 apply and
`FormalSystem/ForMathlib/Order/PFilter.lean` is replaced by `FormalSystem/ForMathlib.lean` plus an
`exceptions` entry.
