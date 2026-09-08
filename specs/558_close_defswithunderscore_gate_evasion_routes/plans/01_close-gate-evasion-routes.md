# Implementation Plan: Close `defsWithUnderscore` Gate Evasion Routes

- **Task**: 558 - Close the three (now four) evasion routes that let `defsWithUnderscore` reopen invisibly
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours
- **Dependencies**: 555 (completed), 557 (completed)
- **Research Inputs**: None (no research report; planned directly from the task specification plus live codebase measurement — see "Opening Measurement" below)
- **Artifacts**: plans/01_close-gate-evasion-routes.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

`docs/development/NAMING_CONVENTION_DEVIATION.md` already names four mechanisms by which a
`defsWithUnderscore` violation is invisible to `lake exe runLinter FormalSystem`, to CI's
`lake lint`, to `scripts/nolints.json`'s baseline diff, and to C16. The renames themselves are
done — the sibling burndown task landed them and both instruments now agree at zero. What does
not yet exist is a **standing gate**: nothing in `scripts/check-module-invariants.sh` would fail
if any of the four routes were exercised again. This plan adds one new invariant, **C26**, that
closes all four, plus the deliberate negative test per route that
`docs/development/MODULE_INVARIANTS.md` mandates before a new check is accepted.

The mechanism is a repo-local **textual** scan over `FormalSystem/` (excluding `Boneyard/`),
modelled directly on the existing C23 namespace-walk scanner in the same script. Textual scope is
what closes routes (1) and (4) simultaneously: a scan that walks the *tree* never consults the
import closure, so an out-of-closure module and a `private` declaration are as visible to it as
any other line of source. A second half of C26 inventories in-source `nolint` attributes against
an explicit allow-list file, closing route (2). Not inheriting Mathlib's
`isBadNameWithUnderscore` heuristic closes route (3).

### Research Integration

No research report exists for this task and none was requested. The task description is itself a
specification: it names the defect, the four routes, the deliverable, the document-ownership
split against the sibling task, and the acceptance bar. What it does **not** carry is a current
measurement — its counts predate the sibling burndown — so this plan opens with a measurement
phase rather than a research phase, and every count below is marked as a hypothesis to confirm.

### Opening Measurement (taken during planning, on the current tree)

These readings were taken live while planning and are the reason several of the task
description's numbers are restated as hypotheses rather than facts:

| Reading | Task description | Measured now | Note |
|---|---|---|---|
| `lake exe runLinter FormalSystem` | reports 0 | exit 0, `-- Linting passed for FormalSystem.` | unchanged |
| Public snake_case `def`/`abbrev` outside `Boneyard/` | 71 | **0** | the sibling burndown landed |
| `private` snake_case `def`/`abbrev` outside `Boneyard/` | 47 | **0** | the sibling burndown landed |
| `perpetuity_1`, `perpetuity_2`, `nf_order_0_1` as declarations | 3 live | **0** — the strings survive only as `mkEntry` labels in `FormalSystem/Automation/ProofStepExport.lean` | route (3) is real but currently unexercised |
| `private def weaken_under_imp` | live | **absent** | renamed by the sibling task |
| In-source `nolint` attribute sites outside `Boneyard/` | "seven in `UserTactics.lean` + three docBlame + one structureInType" | **4 attribute sites covering 7 declarations** | see Phase 1 |
| Public snake_case `instance` declarations in closure | not mentioned | **23**, and `runLinter` is green on all of them | see the Prop-instance hypothesis below |
| `scripts/nolints.json` | clean of `defsWithUnderscore` | 217 entries, **all** `unusedArguments` | unchanged |

**The consequence for this plan is favourable**: the tree is clean, so C26 can ship *enforced*
from its first run, on the C24/C25 precedent recorded in `MODULE_INVARIANTS.md`, with no
`ENFORCE_` soft window — provided the check's exemption set is right. Getting the exemption set
right is what Phase 1 exists for.

**The 23-instance finding is the sharpest design constraint.** All 23 public snake_case
`instance` declarations that a naive textual scan flags (`bundleFamilies_nonempty`,
`mcsToPFilter_isProper`, `limitDomSubtype_countable`, …) are almost certainly `Prop`-valued
instances, which Lean records as `thmInfo` rather than `defnInfo`, which is exactly why
`defsWithUnderscore`'s `isDefinition` guard never fires on them — and snake_case is the *correct*
Mathlib convention for them. A textual check that does not exempt them starts life red on 23
conformant names.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch and no roadmap consultation was requested.

## Goals & Non-Goals

**Goals**:
- One new invariant `C26` in `scripts/check-module-invariants.sh` whose failure is exit-code
  affecting, covering all four evasion routes.
- A route-(2) allow-list companion file, `scripts/nolint-attribute-allowlist.txt`, following the
  established companion-file convention (permanent documented exemptions, stale entries reported).
- A decision, recorded in the script's own header comment, on whether the `runLinter` target is
  widened beyond the single `FormalSystem` root — sharing one mechanism with the completed
  out-of-closure-roots work rather than inventing a second.
- Four deliberate negative tests, one per route, each observing **both** a `FAIL C26` line **and**
  a non-zero script exit, then a restore and a re-observed `PASS` with exit 0.
- An appended section in `docs/development/NAMING_CONVENTION_DEVIATION.md` naming the four routes
  and the gate that now closes each.
- New C26 rows in `docs/development/MODULE_INVARIANTS.md`'s check table and companion-file
  section.

**Non-Goals**:
- Renaming any declaration. The burndown is the sibling task's, already complete.
- Editing `NAMING_CONVENTION_DEVIATION.md`'s burndown table or its "closed at 0" claim. That
  document's existing content is the sibling task's output and is already correct; this task
  **appends only**.
- Regenerating `scripts/nolints.json`, or running `lake exe runLinter --update` for any reason.
- Fixing the upstream Mathlib heuristic or the upstream `env_linter` visibility model. Route (4)
  is an upstream property; the repo-local check is the answer, not a Mathlib patch.
- Widening C23 or C16's existing assertions. C26 is a new check, on the C12-was-not-a-widening-of-C5
  precedent recorded in `MODULE_INVARIANTS.md`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| C26 ships red on the 23 conformant `Prop`-valued snake_case instances | H | H if unaddressed | Phase 1 confirms the `thmInfo` hypothesis by elaboration, then Phase 2 exempts `instance` declarations wholesale with the reason recorded at the exemption site; the residual (a non-`Prop` instance out of closure) is named as a documented residual rather than silently ignored |
| A naive textual scan flags legitimate trailing-underscore names (`MonadicFormula.true_`, `false_` — `true`/`false` are keywords) | M | H | Flag only an underscore that is **not** trailing on the last name component; strip a `_root_.` prefix before analysis. Two measured names depend on this |
| Widening `runLinter` to `BimodalTest` and the thirteen `lean_exe` roots surfaces a wall of pre-existing findings, turning the gate red on work this task does not own | H | M | Phase 4 **measures before deciding**: if the widened target is not already clean, it ships behind an `ENFORCE_` flag reporting a count, exactly as `ENFORCE_C9_DOCS` does, rather than being abandoned or force-passed |
| A check that prints `FAIL` while handing the shell exit 0 — the recorded C24 failure mode | H | M | Every negative test asserts the shell's `$?` as well as the printed line; the plan's acceptance bar says "both", and Phase 5's checklist repeats it per route |
| Writing the docs sections trips the very checks they document — `MODULE_INVARIANTS.md` records that C12/C14/C15 all fired on that page while it was being written | M | H | Phase 6 describes violation *shapes*, never literals: no spelled-out unresolvable anchor, no bare count in the C14 tripwire shape, no hypothetical slash path. Run `--no-build` after each doc edit, not once at the end |
| A task-number citation in the appended docs prose | M | M | `no-task-references-in-deliverables.md` binds `docs/`, and C9D counts it (soft). Cite the sibling work by what it did, never by number |
| The textual scanner's declaration regex misses attribute-heavy or multi-line declarations, so the gate quietly under-reports | M | M | Phase 5's negative tests are the proof of life; additionally seed one violation in an attribute-decorated position during Phase 5 route (3) |
| Concurrent edits to `scripts/check-module-invariants.sh` | M | L | Every phase that touches the script is serialized (see the wave table); no two phases hold it at once |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

Phases within the same wave can execute in parallel. This plan is deliberately fully serial:
phases 2, 3 and 4 all edit `scripts/check-module-invariants.sh`, so parallel dispatch would put
two writers on one file. Phase 5 (negative tests) must observe the finished check, and Phase 6
documents what phases 2-5 actually built.

---

### Phase 1: Baseline measurement and exemption-set lock [COMPLETED]

**Goal**: Replace every inherited count with a measured one, and settle the three design
questions C26's exemption set turns on, before a line of the check is written.

**Tasks**:
- [x] Re-measure, on the current tree excluding `Boneyard/`: public snake_case `def`/`abbrev`
      declarations; `private` snake_case `def`/`abbrev` declarations; names hidden behind the
      upstream `_1`/`_2`/`_mathlib`/trailing-underscore heuristic; snake_case `instance`
      declarations. Record each count and its file distribution.
- [x] **Confirm or refute the Prop-instance hypothesis.** Take at least three of the measured
      snake_case `instance` declarations and establish, by elaboration rather than by reading,
      whether the constant Lean records is a definition or a theorem — e.g. a scratch module that
      `import`s `FormalSystem` and reports `isDefinition` for each name, run with `lake env lean`
      against the existing oleans. The answer decides whether `instance` is exempt from C26.
- [x] Inventory every in-source `nolint` attribute outside `Boneyard/`: the attribute site
      (`@[nolint X]` and `attribute [nolint X] a b c` forms both), the linter named, and every
      declaration it covers. Record the exact list; this becomes the allow-list's seed content.
      Check `Tests/` as well as `FormalSystem/` and record whether the check's scope should
      include it.
- [x] Confirm what `runLinter` can and cannot be pointed at: whether
      `lake exe runLinter <ModuleName>` accepts a `lean_exe` root module and the `BimodalTest`
      library root, and what each reports today. This is the input to Phase 4's decision and
      costs nothing to establish now.
- [x] Record the next free check ID by reading the script's existing `ENFORCE_C*` block
      (expected `C26`; confirm no collision).
- [x] Write the findings into the phase's commit message and carry them forward — later phases
      cite these numbers rather than re-deriving them.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

Local tier does not cover: whether the check about to be written actually fails on a violation —
that is Phase 5's job — nor whether the full gate stays green, which Phase 6 asserts.

**Scope Hypothesis**: The counts asserted in "Opening Measurement" above (0 public snake_case
defs, 0 private snake_case defs, 4 nolint attribute sites covering 7 declarations, 23 snake_case
instances, next ID `C26`) are planning-time readings from a scanner written in minutes, not
facts. Confirm each by re-measuring; where a reading differs, the measured value wins and the
plan's phase content adjusts around it. The Prop-instance claim in particular is an inference
from Lean's treatment of `Prop`-valued instances and MUST be confirmed by elaboration before
Phase 2 exempts anything on its strength.

**Files to modify**:
- None. This phase produces measurements, not edits. Scratch probes belong in a temporary
  directory and must not be left in the tree.

**Verification**:
- Every row of the Opening Measurement table has a re-measured value recorded.
- The Prop-instance question is answered by an elaboration result, quoted, not by reasoning.
- The nolint inventory is complete and exact — attribute site, linter, covered declarations.
- `git status --short` shows a clean tree (no scratch files left behind).

---

### Phase 2: C26 half one — the tree-wide snake_case scan (routes 1, 3, 4) [NOT STARTED]

**Goal**: Add the repo-local textual check that sees what `runLinter` structurally cannot:
out-of-closure modules, `private` declarations, and names the upstream heuristic skips.

**Tasks**:
- [ ] Add an `ENFORCE_C26` variable to the script's `ENFORCE_*` block, with the header comment
      the neighbouring flags all carry: what the check asserts, why it exists, and — following
      the C24/C25 precedent — why it ships enforced with no soft window.
- [ ] Implement the scanner as a Python heredoc in the C23 style, reusing that block's proven
      namespace/comment/`section`/`end` walk rather than writing a fourth independent scanner.
      Do **not** merge it into C23's pass: C23 asserts three different things and merging would
      make one failure mask another.
- [ ] Scope: every `*.lean` file under `FormalSystem/`, with `Boneyard/` excluded by the same
      directory filter every other traversal uses. This scope is what closes route (1) — no
      import closure is consulted at any point.
- [ ] Declaration kinds: `def`, `abbrev`, and (subject to Phase 1's answer) `instance`. `theorem`
      and `lemma` are out of scope — the upstream linter's `isDefinition` guard excludes them and
      snake_case is the correct convention for propositions.
- [ ] Visibility: `private` declarations are **in** scope. This is route (4), and it is the one
      thing an `env_linter` can never do.
- [ ] Naming rule, deliberately **not** inheriting `isBadNameWithUnderscore`: strip a leading
      `_root_.`, take the last dot-component, and flag it if it contains an underscore that is not
      in trailing position. This flags a name ending `_1`/`_2`/`_mathlib` (route 3) while leaving
      keyword-disambiguating trailing-underscore names alone. Record the two measured
      trailing-underscore names at the exemption site as the evidence for that carve-out.
- [ ] Exemptions: apply Phase 1's answer on `instance`. Whatever is exempted gets its reason
      written at the site in the C23 style — the script's existing exemption comments are the
      length and specificity bar, and "the linter does not flag it" is not a reason.
- [ ] Failure output: a `FAIL C26` line naming the count, then up to ten `path:line: name` rows,
      then a `... and N more` line. Exit non-zero from the heredoc and wire the status into
      `FAILURES` exactly as the C23 block does.
- [ ] The check must run under `--no-build` — it needs no build, like C23's textual half.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

Local tier does not cover: whether the check fires on a real violation (Phase 5), nor its
interaction with a full build (Phase 6's final gate).

**Scope Hypothesis**: "Reusing C23's namespace walk is sufficient" is a hypothesis about the
existing scanner's fidelity, not a fact. Confirm it by checking the new scan's output against
Phase 1's independent measurement: the two must agree on the current tree (both empty). If they
disagree, the walk needs the correction and the discrepancy is recorded, not smoothed over.

**Files to modify**:
- `scripts/check-module-invariants.sh` — new `ENFORCE_C26` flag, new C26 header comment block,
  new Python scanner heredoc plus its exit-status wiring.

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` prints a `PASS C26` line for this half.
- Script exit is 0 on the clean tree.
- The new scan's count agrees with Phase 1's independent measurement.
- No existing check's output changed.

---

### Phase 3: C26 half two — the in-source `nolint` attribute inventory (route 2) [NOT STARTED]

**Goal**: Make an in-source suppression a reviewable line in a file rather than the absence of a
finding, which is what makes route (2) invisible to all four existing instruments at once.

**Tasks**:
- [ ] Create `scripts/nolint-attribute-allowlist.txt`, seeded from Phase 1's exact inventory. One
      entry per covered declaration, each carrying the linter name and the reason, following the
      shape and tone of `scripts/module-invariants-allowlist.txt` and
      `scripts/boneyard-import-waivers.txt`. Comment lines and blank lines ignored.
- [ ] Add the C26 second-half scan: walk the same live `*.lean` file set, match both attribute
      forms (`@[nolint X]` immediately preceding a declaration, and
      `attribute [nolint X] a b c` covering a list, possibly spanning lines), resolve the covered
      declaration name(s), and fail on any not present in the allow-list.
- [ ] Report allow-list entries that no longer match anything as an `INFO` line, on the C5/C11
      model, so the file cannot silently rot into a dumping ground.
- [ ] Write the allow-list's admission bar into `MODULE_INVARIANTS.md` in Phase 6 and into the
      file's own header now: an entry is a **permanent documented exemption with a reason at the
      site**, never a backlog row. Phrase it so "I do not want to fix this" is visibly
      inadmissible, as the existing companion files do.
- [ ] Fold this half's failure into the same C26 exit status as Phase 2's half, so one check ID
      carries both and neither can mask the other in the printed output.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

Local tier does not cover: the negative test proving the inventory actually fails on an
unlisted attribute (Phase 5), nor the full gate (Phase 6).

**Scope Hypothesis**: The allow-list is asserted to hold exactly the declarations Phase 1
inventoried — expected to be seven across four attribute sites, but Phase 1's measurement is
authoritative. Confirm that the seeded file and the live scan agree at zero unlisted and zero
stale before closing the phase; a mismatch means the attribute-form matcher is wrong, not that
the file needs another row.

**Files to modify**:
- `scripts/nolint-attribute-allowlist.txt` — new file, seeded and documented.
- `scripts/check-module-invariants.sh` — C26's second-half scan and its wiring.

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` reports zero unlisted attributes and zero
  stale allow-list entries.
- Script exit is 0.
- Every seeded allow-list entry carries a linter name and a reason.

---

### Phase 4: The `runLinter` target decision (route 1's second half) [NOT STARTED]

**Goal**: Answer the question the task description poses explicitly — whether the linter target
is widened beyond the single `FormalSystem` root — with a measurement and a recorded decision,
sharing the root-scraping mechanism the completed out-of-closure-roots work already built rather
than inventing a second.

**Tasks**:
- [ ] Reuse C25's existing `lakefile.lean` root scraper — do not write a second one. Extend or
      parameterize it if `lean_lib` roots are needed alongside `lean_exe` roots, keeping one
      scraping site.
- [ ] **Measure first**: run the env_linter batch against each additional root (`BimodalTest`
      and each `lean_exe` root module) and record what each reports today, plus the wall-clock
      cost with the tree already built by C1.
- [ ] Decide and record, in the script's C16 header comment:
      - If every additional root is already clean, widen C16's invocation to iterate the scraped
        root list and ship it enforced.
      - If additional roots carry pre-existing findings, ship the widening **reporting-only**
        behind its own `ENFORCE_` flag that prints the count at every gate — the
        `ENFORCE_C9_DOCS` pattern, which exists precisely so debt is visible rather than either
        force-passed or blocking.
      - If the cost is prohibitive, record that as the decision with the measured number, and
        state plainly that route (1) is carried by C26's tree-wide textual scope alone — which is
        already true and sufficient for the naming invariant.
- [ ] Whichever branch is taken, write the reason and the measurement into the comment. A future
      reader must be able to see that the question was answered, not skipped.
- [ ] Never flip an existing `ENFORCE_` flag to 0 to accommodate this widening.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: "Thirteen `lean_exe` roots plus `BimodalTest`" is read off the current
`lakefile.lean` and off `MODULE_INVARIANTS.md`'s C25 row; the scraper's live output at run time
is authoritative. The claim that widening is affordable is a hypothesis with no measurement
behind it at planning time — Phase 4's first task is to produce that measurement, and the
decision follows the number rather than the plan's expectation.

**Files to modify**:
- `scripts/check-module-invariants.sh` — C16 header comment (the decision and its measurement),
  and the C16 invocation plus any new `ENFORCE_` flag if the widening ships.

**Verification**:
- `bash scripts/check-module-invariants.sh` (with build) completes and the C16 line reflects the
  decision taken.
- Script exit is 0.
- The decision, the measured findings per additional root, and the wall-clock cost are all
  present in the script comment.

---

### Phase 5: The four deliberate negative tests [NOT STARTED]

**Goal**: Prove each of the four routes independently fails the gate when exercised and passes
after restore. `MODULE_INVARIANTS.md` mandates this before a check is accepted, and records that
a check which silently passes on everything is worse than no check.

**Tasks**:
- [ ] **Route (1), out-of-closure module**: introduce one snake_case `def` in
      `FormalSystem/Theorems/ContextualProofs.lean` — a module imported only by a `lean_exe` root,
      so nothing in the `FormalSystem` library closure elaborates it. Observe `FAIL C26` **and**
      a non-zero script exit. Restore; observe `PASS` and exit 0.
- [ ] **Route (2), in-source suppression**: attach a `nolint` attribute to a declaration that is
      not on `scripts/nolint-attribute-allowlist.txt`. Observe `FAIL C26` and a non-zero exit.
      Restore; observe `PASS` and exit 0.
- [ ] **Route (3), the `_1`/`_2` heuristic**: introduce a public snake_case `def` whose last name
      component ends in `_1`, in a module confirmed to be **inside** the linted closure. Observe
      `FAIL C26` and a non-zero exit — **and in the same run, observe that C16 still reports
      PASS**. That contrast is the whole point of the check, and it is the same observation
      `MODULE_INVARIANTS.md` calls the sharpest part of C25's negative test. Restore; observe
      `PASS` and exit 0.
- [ ] **Route (4), private declaration**: introduce a `private def` with an internal underscore in
      a module confirmed to be inside the linted closure. Observe `FAIL C26` and a non-zero exit,
      and again observe C16 still PASSing in the same run. Restore; observe `PASS` and exit 0.
- [ ] Place at least one of the four seeds in an attribute-decorated or otherwise
      non-plain-line position, so the scanner's regex is exercised beyond the easy case.
- [ ] For every one of the four: record the exact `FAIL` line text, the shell exit status, and
      the restored `PASS` line. Assert the exit status explicitly — the recorded C24 history is a
      check that printed a failure while handing the shell a 0.
- [ ] Confirm `git status --short` is clean after all four restores; no seed may survive.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: per-substep — each route's FAIL/restore/PASS cycle ending green is its own
sub-step. The seeded intermediate states are never committed.

**Scope Hypothesis**: The named negative-test sites (`ContextualProofs.lean` as the
out-of-closure module; some in-closure module for routes 3 and 4) are asserted on the basis that
`ContextualProofs.lean`'s only importer is a `lean_exe` root, measured at planning time. Confirm
both the out-of-closure and the in-closure status of every chosen site before running the test —
a negative test on a site whose closure status is assumed rather than checked proves nothing
about the route it claims to exercise. For routes 3 and 4 specifically, pick a site whose
in-closure status is confirmed, or the "C16 still passes" contrast is vacuous.

**Files to modify**:
- `FormalSystem/Theorems/ContextualProofs.lean` — temporary seed, restored.
- One or more in-closure modules — temporary seeds, restored.
- No permanent change to any `.lean` file. Every edit in this phase is reverted before the phase
  closes.

**Verification**:
- Four recorded FAIL/restore/PASS cycles, each with both the printed line and the shell exit
  status captured.
- Two of the four additionally record a same-run C16 `PASS`.
- `bash scripts/check-module-invariants.sh` exits 0 on the restored tree.
- `git status --short` shows no residue from any seed.

---

### Phase 6: Documentation and final gate [NOT STARTED]

**Goal**: Record the four routes and the gate that closes each, in the two documents this task
owns, and close on a green full gate.

**Tasks**:
- [ ] **Append** to `docs/development/NAMING_CONVENTION_DEVIATION.md` a new section naming the
      four evasion routes and the gate that now closes each, plus the residual each gate does not
      cover. Append only — do **not** restate or re-edit the burndown table, the "closed at 0"
      claim, or the existing four-blind-spots list, all of which are the sibling task's output and
      are already correct.
- [ ] Add C26 to `docs/development/MODULE_INVARIANTS.md`'s check table (one row, in the
      established "what it checks / why it exists" voice, with the measured evidence that
      motivated it), and add `scripts/nolint-attribute-allowlist.txt` to the "Companion Files"
      section with its admission bar.
- [ ] Add C26 to the "Adding a Check" section's record of checks accepted only after a deliberate
      negative test, naming all four routes tested and the both-line-and-exit-status observation.
- [ ] If Phase 4 shipped a widening or a new `ENFORCE_` flag, document it in the same pass.
- [ ] Obey that page's own warnings, which it records were learned the hard way on itself:
      describe violation *shapes*, never write a literal unresolvable anchor, never phrase a
      historical count so it reads as a current claim, and cite only paths that resolve.
- [ ] No task-number citations anywhere in either document — refer to the sibling work by what it
      did, not by number.
- [ ] Run `bash scripts/check-module-invariants.sh --no-build` after **each** doc edit, not once
      at the end, so a tripwire hit is attributable to the paragraph that caused it.
- [ ] Final gate: `lake build` green, and
      `bash scripts/check-module-invariants.sh` printing `ALL CHECKS PASSED` with exit 0 on the
      clean tree.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- `docs/development/NAMING_CONVENTION_DEVIATION.md` — one appended section.
- `docs/development/MODULE_INVARIANTS.md` — C26 table row, companion-file entry, negative-test
  record.

**Verification**:
- `lake build` exits 0.
- `bash scripts/check-module-invariants.sh` prints `ALL CHECKS PASSED` and exits 0.
- C12, C13, C14 and C15 all pass on the edited docs.
- C9D's docs task-reference count is not increased by this task's prose.
- `NAMING_CONVENTION_DEVIATION.md`'s pre-existing sections are byte-identical to their
  pre-task state apart from the appended section — verifiable with `git diff`.

---

## Lean Challenge Statements

```lean
-- Intentionally empty.
```

This plan's `task_type` is `lean4`, so this section is present as the format requires, but the
plan commits to **no** Lean declarations: its deliverable is a shell/Python invariant in
`scripts/check-module-invariants.sh`, one companion allow-list file, and two documentation
edits. The `- **Goals**:` bullets above accordingly name no Lean identifiers, so the identifier
sets on both sides agree — both empty. The only `.lean` edits this plan makes are the temporary
negative-test seeds in Phase 5, every one of which is reverted before that phase closes.

## Testing & Validation

- [ ] `bash scripts/check-module-invariants.sh --no-build` exits 0 with `PASS C26`.
- [ ] `bash scripts/check-module-invariants.sh` prints `ALL CHECKS PASSED` and exits 0.
- [ ] `lake build` exits 0.
- [ ] `lake exe runLinter FormalSystem` exits 0 (unchanged from baseline).
- [ ] Route (1) negative test: FAIL line + non-zero exit observed, restore, PASS + exit 0.
- [ ] Route (2) negative test: FAIL line + non-zero exit observed, restore, PASS + exit 0.
- [ ] Route (3) negative test: FAIL line + non-zero exit observed **with C16 PASSing in the same
      run**, restore, PASS + exit 0.
- [ ] Route (4) negative test: FAIL line + non-zero exit observed **with C16 PASSing in the same
      run**, restore, PASS + exit 0.
- [ ] `scripts/nolint-attribute-allowlist.txt` reports zero stale entries.
- [ ] `git status --short` clean of negative-test residue.
- [ ] `git diff` on `NAMING_CONVENTION_DEVIATION.md` shows an append only.

## Artifacts & Outputs

- `scripts/check-module-invariants.sh` — C26 (two halves), `ENFORCE_C26`, and the recorded
  `runLinter`-target decision in C16's header.
- `scripts/nolint-attribute-allowlist.txt` — new companion file.
- `docs/development/NAMING_CONVENTION_DEVIATION.md` — one appended section on the four routes and
  their gates.
- `docs/development/MODULE_INVARIANTS.md` — C26 check-table row, companion-file entry,
  negative-test record.
- `specs/558_close_defswithunderscore_gate_evasion_routes/summaries/01_*-summary.md` — execution
  summary, including the four recorded negative-test transcripts.

## Rollback/Contingency

Every change is additive and confined to three files plus one new file. Rollback is
`git revert` of this task's commits; nothing in `FormalSystem/` changes permanently, so no proof
or build artifact depends on this work.

If C26 cannot be made green on the clean tree within its phase — most plausibly because the
`instance` exemption question resolves differently than Phase 1 expects — the contingency is to
ship C26 behind `ENFORCE_C26=0`, reporting its count at every gate on the `ENFORCE_C9_DOCS`
model, and record the residual debt. That is a *documented soft period*, not a pass: the check
still runs and still prints. What is never admissible is deleting the check, narrowing its scope
to make a count reach zero, or flipping any existing `ENFORCE_` flag to 0 — the last of which
`MODULE_INVARIANTS.md` prohibits by name.

If a negative test cannot be made to fail, the check is wrong and the phase does not close. A
check that passes on a deliberately seeded violation is the exact failure mode this task exists
to prevent, and shipping one would reproduce the defect at one remove.
