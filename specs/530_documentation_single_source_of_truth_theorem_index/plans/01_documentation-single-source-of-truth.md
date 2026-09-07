# Implementation Plan: Documentation Single Source of Truth and Theorem Index

- **Task**: 530 - Documentation single source of truth, theorem index, publication packaging
- **Status**: [IMPLEMENTING]
- **Effort**: 33 hours
- **Dependencies**: None (this task is itself a dependency of task 177)
- **Research Inputs**: specs/530_documentation_single_source_of_truth_theorem_index/reports/01_documentation-single-source-of-truth.md
- **Artifacts**: plans/01_documentation-single-source-of-truth.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Make documentation status and counts machine-owned rather than hand-typed, publish the
per-theorem ledger a paper reader needs (`docs/theorem-index.md`), and purge history and process
prose from publication-facing docstrings. Three new owners replace six drifting hand-maintained
authorities: C2/C14 own axiom sets, a new `check-module-invariants.sh --emit-inventory` owns
counts, and `docs/theorem-index.md` owns per-theorem status; every other surface carries a
pointer and at most a five-row highlights table. Done when zero hand-typed file/line counts
remain on the four status surfaces, every SORRY-FREE claim in `Metalogic.lean` is machine-pinned,
`docs/theorem-index.md` exists and resolves, `readme-lint.sh` exits 0, and the archaeology-phrase
grep returns zero hits on live surfaces.

### Research Integration

The research report re-derived every measured-state claim in the task description at HEAD
`f6ce84139` and found nine of sixteen stale, always in the direction of undercounting. This plan
is built on the corrected numbers, not the description's:

- **C14 already pins 54 declarations** (task 529 landed this), not 8. The remaining unpinned
  SORRY-FREE set is the **35** declarations enumerated in report §4.1(a) — item (1)'s
  "extend from 8" is already 80% done.
- **The `file.lean:NNN` citation item is 85x the description's estimate**: 1,354 live citations,
  110 provably wrong. Report §4.4's two-tier scoping rule (enforce in the 184-citation
  publication-facing scope, report-only in `WeakCanonical/**`, fix all 110 wrong sites
  everywhere) is adopted verbatim as the scope of Phases 8-10.
- **Five items are already fixed and are excluded**: E-01, E-02, E-07, E-18, B-17
  (report §2.1).
- **`Conservativity.lean` is dropped from the halve-the-prose list** (report §4.3): its 95.9%
  comment share is by design and its archaeology is already cleared. It is targeted for
  duplication removal only.
- **The E-docs §5.2 seed table cannot be transcribed** — four of sixteen rows name declarations
  that no longer exist and two have the wrong file. Phase 5 uses report §4.2's verified
  corrections.
- **Eight of the twelve flagship results have no paper anchor to add** (compactness,
  non-compactness, consequence-completeness are the formalization's own results). `Paper: —`
  plus a one-clause reason is the deliverable there, and the C15 extension must accept `—`.
- **Design A is adopted** for the inventory generator (extend `check-module-invariants.sh`,
  reuse C7's Boneyard-excluding walk) over promoting `readme-inventory.sh`.
- **`docs/architecture/ADR-NNN` is adopted** over the description's `docs/decisions/*.md`, per
  report §4.3's flag: the repo already carries ADR-001..ADR-004 there, and a task whose purpose
  is removing duplicate authorities must not create a second ADR convention.

### Prior Plan Reference

No prior plan. This is round 1 for task 530.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only (no `roadmap_flag` on this dispatch, so no
roadmap-review/roadmap-update phases are included and ROADMAP.md is not modified). This task
advances **Phase 5: Publication and Documentation**, specifically the un-gated metalogic half of
**Task 177** ("README/docs/module-docstring final polish"), whose remaining scope is gated on the
decidability chain. Phase 5's stated check grounding (C5 module-shaped path resolution in
markdown/docs; C9 zero task-number citations under `FormalSystem/`) is directly extended by
Phases 8-10 here.

## Goals & Non-Goals

**Goals**:
- Counts on all nine registered inventory surfaces are generated, never hand-typed, with
  hand-written Description columns preserved across regeneration.
- Every SORRY-FREE claim in `Metalogic.lean` is machine-pinned by C2 or C14 (the 35 remaining
  declarations added to `C14_BASELINE`).
- `docs/theorem-index.md` exists as the sole per-theorem status ledger, with fully-qualified Lean
  names, a generated Axioms column, and a Notation-and-naming table.
- Each of the 20 flagship declarations carries a one-line `Paper:` anchor (or `Paper: —` with a
  reason), asserted by a new second assertion inside C15.
- A two-tier C20 citation check exists; all 110 provably-wrong `file.lean:NNN` citations are
  fixed repo-wide and the 184 publication-scope citations are converted to declaration names.
- `Validity.lean`, `FrameClassValidity.lean`, `StrongCompleteness.lean` and `SetConsequence.lean`
  carry roughly half their current prose, with layering rationale relocated to ADRs and
  archaeology deleted.
- `CITATION.cff`, `docs/ARCHITECTURE.md`, `references.bib`, README's
  `## Verifying the main theorems`, and `## Tags` lines exist.
- The typst per-declaration axiom table is generated, not hand-written, with one provenance stamp.
- `readme-lint.sh` exits 0.

**Non-Goals**:
- **Classifying the three unresolved paper anchors** `app:drift`, `cor:no-characterization`,
  `lem:deterministic-singleton` (report §7). C15's pre-existing red state is carried unchanged
  and separately tracked; only C15's *new* assertion is required to pass. See the user-decision
  note in Risks.
- Enforcing the citation convention inside `FormalSystem/Metalogic/WeakCanonical/**` (1,083
  citations). Those are reported, never gated.
- Migrating the four existing `docs/architecture/ADR-00N` files to a new location.
- Any change to Lean proof content, theorem statements, or the build graph beyond adding the
  single missing `DiscreteOrder.lean` import to `SoundnessLemmas.lean`.
- Task 177's decidability-gated documentation half.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| R1: Item (4) taken at the description's literal "fix the 16" would fix 16 of 110 known-wrong citations | H | M | Phases 8-10 implement report §4.4's two-tier rule explicitly; Phase 9's acceptance is "all 110, repo-wide", independent of the publication-scope conversion |
| R2: C15 is already red; Phase 7 extends it | H | H | Phase 7's acceptance is "C15's new assertion passes; the pre-existing three-anchor failure is unchanged", never "C15 passes" |
| R3: Regenerating inventories over hand-written descriptions destroys `Semantics/README.md`'s descriptions | H | M | Phase 1's generator regenerates File and Lines only, keying on filename to carry Description across; a missing description gets `<!-- TODO -->`, a vanished file's row is dropped. Verified by diffing `Semantics/README.md`'s Description column before and after |
| R4: `docs/decisions/` vs `docs/architecture/ADR-NNN` fork creates a second competing convention | M | M | Decided in this plan: `docs/architecture/ADR-005..008`. Recorded in Phase 13 |
| R5: Every grep-derived count re-derived by research came out higher, never lower | H | H | Every phase asserting a count carries a **Scope Hypothesis** line; each is re-derived at phase start and treated as a lower bound, never a fact |
| R6: Phases 3, 12 and 14 all edit `Metalogic.lean` / `StrongCompleteness.lean` | M | H | Serialized by the dependency chain below; no two phases in the same wave share a file |
| R7: Build-cost — Phases 4, 11, 12, 16, 17 need a real `lake build` (2,591 jobs) | M | H | Route those through the detached, guarded pattern in `.claude/context/project/lean4/operations/long-builds.md`; all other phases verify under `--no-build` |
| R8: Phases 1, 4, 7, 8, 14 all edit `scripts/check-module-invariants.sh` | M | H | The five script phases are fully serialized (1 -> 4 -> 7 -> 8 -> 14); never scheduled in the same wave |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 4 | 1 |
| 3 | 3, 5, 17 | 2, 4 |
| 4 | 6, 18 | 5, 17 |
| 5 | 7 | 4, 6 |
| 6 | 8 | 7 |
| 7 | 9 | 8 |
| 8 | 10 | 3, 6, 9 |
| 9 | 11, 12, 15 | 3, 10 |
| 10 | 13 | 11, 12 |
| 11 | 14 | 3, 8, 12, 13 |
| 12 | 16 | 2, 3, 13, 14, 15 |
| 13 | 19 | 5, 13, 14, 16 |

Phases within the same wave can execute in parallel. Territory is disjoint within every wave by
construction: no two same-wave phases name the same file under **Files to modify**.

---

### Phase 1: Inventory generator mechanism [COMPLETED]

**Goal**: `scripts/check-module-invariants.sh` gains `--emit-inventory` (writes in place) and
`--emit-inventory --check` (exits non-zero if a rewrite would change a byte), reusing C7's
Boneyard-excluding walk, with one pilot target converted.

**Tasks**:
- [x] Add `--emit-inventory` mode reusing C7's existing traversal; do not duplicate the walk. *(deviation: altered — the walk was extracted to `scripts/lib/live_walk.py` and imported by both C4-C11 and the new mode, rather than the new mode calling into C7's heredoc)*
- [x] Emit `<!-- BEGIN GENERATED: inventory -->` / `<!-- END GENERATED -->` blocks containing
      File and Lines columns only. *(deviation: altered — the marker also accepts `rows=`, `filter=`, `cols=`, `desc=`, `link=` and `sort=` options, because the pilot target's five count tables have four distinct shapes, not one)*
- [x] Implement description carry-across: key on file name, preserve the existing Description
      cell verbatim, emit `<!-- TODO: add description -->` for a new file, drop a row whose file
      no longer exists.
- [x] Add `--check` sub-mode; wire only `--check` into the CI path, never the writer.
- [x] Convert one pilot target (`FormalSystem/Metalogic/README.md`) and confirm its Description
      column is byte-identical before and after.
- [x] Reduce `scripts/readme-inventory.sh` to a thin `exec` shim or delete it, updating any
      caller. *(deviation: altered — the shim reports the replacement and exits 2 rather than `exec`-ing, since the replacement takes a README not a directory)*

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: 9 registered targets exist (report §4.1(b) list); this phase converts 1.
Confirm the remaining 8 still carry hand-maintained count tables by grepping for the table header
shape before Phase 2 starts.

**Files to modify**:
- `scripts/check-module-invariants.sh` - new `--emit-inventory[ --check]` mode
- `scripts/readme-inventory.sh` - reduced to shim or deleted
- `FormalSystem/Metalogic/README.md` - pilot conversion

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` exits 0 immediately after a
  write.
- `bash scripts/check-module-invariants.sh --no-build` is no worse than its pre-phase state
  (C15's three-anchor failure is the only expected non-zero exit).
- `git diff` on the pilot README shows no Description-column change.

---

### Phase 2: Convert and regenerate all inventory targets [COMPLETED]

**Goal**: The remaining eight registered targets carry generated blocks, and every stale per-file
line count and aggregate rollup is corrected by generation rather than by hand.

**Tasks**:
- [x] Convert `README.md`, `FormalSystem/README.md`, `FormalSystem/Automation/README.md`,
      `FormalSystem/Syntax/README.md`, `FormalSystem/Theorems/README.md`,
      `FormalSystem/Metalogic/SoundnessLemmas/README.md`,
      `FormalSystem/Metalogic/Independence/README.md`,
      `FormalSystem/Automation/Tactics/README.md`. *(deviation: altered — `README.md` has no
      per-file table, so a new `rows=totals` marker mode was added and its `Metric | Count`
      rollup converted instead)*
- [x] Regenerate; confirm the corrected ground truth lands (`FormalSystem/` 459 files /
      281,222 lines; `Metalogic/` 330 / 227,266; `Decidability` 62; `WeakCanonical` 179).
      *(deviation: altered — file counts match; line counts are higher than the plan's figures
      and moved during the phase, because a concurrent session is editing
      `BXCanonical/Chronicle/ChronicleTypes.lean`. The generator's output is authoritative, which
      is the point of the phase)*
- [x] Fix the aggregate rollup prose that sits outside the generated blocks
      (`Metalogic/README.md:6-7`, `:213`; `README.md:107`) to read from, or point at, the
      generated block instead of restating a number.
- [x] Confirm `Semantics/README.md`'s Contents table (the best in the tree) is either converted
      losslessly or explicitly registered as already-correct and left alone. *(deviation:
      altered — registered via a new `<!-- INVENTORY: hand-maintained (dir=…) -->` marker, and
      the `INV` check was extended to assert such a table is exhaustive, so registration is an
      exemption from generation but not from checking)*

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: prose

**Scope Hypothesis**: 40 of 72 per-file line-count claims across 7 READMEs are wrong (report §2
row 4). Re-derive with the generator's `--check` diff at phase start; expect the count to be a
lower bound.

**Files to modify**:
- The eight registered READMEs listed above

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` exits 0.
- `grep -rn` for a hand-typed file-count digit on the four status surfaces returns only
  generated-block content.

---

### Phase 3: Delete the Metalogic census block [COMPLETED]

**Goal**: `FormalSystem/Metalogic.lean`'s Module Structure census is deleted and replaced with
three sentences plus pointers; `Metalogic/README.md`'s loose-file section is repaired.

**Tasks**:
- [x] Delete `Metalogic.lean`'s Module Structure block (at `:253-286` as of research
      measurement; locate by content, not line number) and replace it with a short narrative
      pointing at `FormalSystem/Metalogic/README.md` and
      `scripts/check-module-invariants.sh`.
- [x] Confirm the deletion removes the "exclude BOTH Boneyards (there are two)" claim and the
      Kamp-has-its-own-Boneyard claim in the same edit; B0 asserts exactly one.
- [x] Repair `Metalogic/README.md`'s "**Ten** loose files" section: the correct count is 6, and
      five of the eleven table rows are phantoms (`BaseLanguageSoundness.lean`,
      `TMCompletenessReduction.lean`, `SpWitness.lean`, `Z1Countermodel.lean` moved into
      `Metalogic/Conservativity/`; `Conservativity.lean` is now that directory's aggregator).
- [x] Fix the dangling edit fragment in `Metalogic.lean` (at `:131-132` as of measurement:
      "obtained by instantiating the reductions / the single `FrameClass`-generic reduction").
- [x] Reconcile the four-row status ledger copy in `Metalogic.lean` (at `:46`: "the two
      countermodels remain outstanding") against `Conservativity.lean`'s "refuted with both
      halves machine-checked"; the ledger's owner is `docs/theorem-index.md` (Phase 5), so leave
      a pointer here, not a fifth copy.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: the census block is 34 lines and the loose-file table has 11 rows of which
5 are phantom. Re-locate both by content at phase start; line numbers have already moved once
since the review.

**Files to modify**:
- `FormalSystem/Metalogic.lean` - census deletion, fragment fix, ledger pointer
- `FormalSystem/Metalogic/README.md` - loose-file section repair

**Verification**:
- Diff read-through confirms every changed hunk lies inside a `/-!` or `/--` comment region.
- `grep -n 'there are two' FormalSystem/Metalogic.lean` returns nothing.
- B0 and C7 still pass under `--no-build`.

---

### Phase 4: Extend the C14 axiom baseline [COMPLETED]

**Goal**: Every SORRY-FREE claim in `Metalogic.lean` is machine-pinned. The 35 unpinned
declarations from report §4.1(a) are added to `C14_BASELINE` with matching `#print axioms` lines.

**Tasks**:
- [x] Add the 35 declarations to the `C14_BASELINE` heredoc and the corresponding
      `#print axioms` directives, following the existing row shape exactly. *(deviation:
      altered — the re-derived unpinned set is **47**, not 35: the tree uses `ztime`/`rtime`
      naming and carries declarations the report's list predates. C14 now pins 99 and C2 four,
      103 in total)*
- [x] Expand `tmFrag_complete_*` into its four member declarations by name; it is a family, not
      a declaration.
- [x] Decide and record whether `decide` (a `def`, not a theorem) belongs in the flagship pinned
      set; if excluded, remove its SORRY-FREE claim from `Metalogic.lean` rather than leaving it
      prose-only. *(decided: included. `Metalogic.lean` makes a SORRY-FREE claim about it, and
      pinning is what makes that claim machine-checked; `#print axioms` is well-defined on a
      `def`. `Conservativity.TMFrag`, also a `def`, is pinned for the same reason)*
- [x] Record the axiom value for each new row (`pcq` for
      `[propext, Classical.choice, Quot.sound]`, the literal list otherwise) so Phase 5 can
      populate the index's Axioms column without a second build. *(seven declarations carry the
      strict subset `[propext]` or `[propext, Quot.sound]`, recorded literally)*
- [x] Batch all additions into one build cycle.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 35 unpinned declarations, 54 already pinned. Re-derive the unpinned set at
phase start by extracting SORRY-FREE names from `Metalogic.lean` and differencing against the
C2+C14 pinned set; expect the count to have moved.

**Files to modify**:
- `scripts/check-module-invariants.sh` - `C14_BASELINE` rows and `#print axioms` directives

**Verification**:
- A full `bash scripts/check-module-invariants.sh` run (with build, via the guarded long-build
  pattern) reports C14 pass with all 89 pinned declarations.
- The SORRY-FREE-name minus pinned-set difference is empty.

---

### Phase 5: Seed docs/theorem-index.md [COMPLETED]

**Goal**: `docs/theorem-index.md` exists as the sole per-theorem ledger, with fully-qualified
names, a generated Axioms column, and a Notation-and-naming table.

**Tasks**:
- [x] Create `docs/theorem-index.md` with schema
      `| Paper label | Statement (one line) | Lean name | File | Frame class | Axioms |`.
      File column carries no line numbers.
- [x] Transcribe the corrected seed rows, applying report §4.2's seven verified name/file
      corrections (`notCompactDiscrete`, `notStrongCompletenessDiscrete`, `notCompactDedekind`,
      `notStrongCompletenessDedekind`, the two `completeness_dense`/`completeness_discrete`
      splits, and `FormalSystem.ProofSystem.Derivable.deduction`).
- [x] Use fully-qualified Lean names in every row, unconditionally — `completeness_dense` and
      `completeness_discrete` each name two distinct live theorems.
- [x] Populate the Axioms column from Phase 4's recorded values: `pcq` / literal list, plus
      `pinned:C2` or `pinned:C14`; `claimed` only where genuinely prose-only. *(deviation:
      altered — seeding surfaced two unpinned flagship declarations,
      `BXCanonical.completeness_rtime_engine` and `BXCanonical.countermodel_dedekind_dense`.
      They were pinned rather than recorded as `claimed`, so no row reads `claimed`)*
- [x] Add the Notation-and-naming table (E-20) mapping paper term to Lean identifier.
- [x] Replace the ledger copies on the other surfaces with a pointer plus a highlights table of
      at most five rows.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: prose

**Scope Hypothesis**: 16 seed rows plus a continuation list, of which 7 rows need correction.
Re-verify every name resolves and every file path exists before writing the row.

**Files to modify**:
- `docs/theorem-index.md` - new
- `README.md`, `FormalSystem/Metalogic/README.md`, `FormalSystem/Metalogic/Conservativity.lean` -
  ledger copies reduced to pointer plus highlights

**Verification**:
- Every Lean name in the index resolves (grep each fully-qualified name against live scope).
- Every File cell names an existing path and contains no `:NNN`.
- No surface outside the index carries a status table longer than five rows.

---

### Phase 6: Paper anchors at the flagship declarations [COMPLETED]

**Goal**: Each of the 20 flagship declarations carries a one-line `Paper:` anchor in its own
`/--` block, or `Paper: —` with a one-clause reason.

**Tasks**:
- [x] Add a `/--` doc comment to `FormalSystem.Metalogic.BXCanonical.completeness`, which
      currently has none. *(deviation: skipped — the finding is stale. It has a 20-line `/--`
      block at `Completeness.lean`; the research measurement found the *quoted copy* of the
      theorem inside the module `/-!` docstring's ```lean fence, not the declaration. The
      inserter was made comment-aware so a fenced quotation is never mistaken for a declaration)*
- [x] Add `Paper: thm:TM-soundness` to the four soundness rows and `Paper: cor:tm-completeness`
      to the four weak-completeness rows, using anchors pinned in
      `specs/paper-definitions-of-record.md`. *(deviation: altered — eight weak-completeness
      rows carry `cor:tm-completeness`, not four: the four `BXCanonical` engines and the four
      `WeakCompleteness` termini are distinct declarations)*
- [x] Add `Paper: —` plus a one-clause reason ("formalization-native result; no paper anchor") to
      the compactness, non-compactness and consequence-completeness rows — eight of the twelve
      have no anchor to add and this is the correct deliverable, not a gap.
- [x] Copy the placement model from `Semantics/TaskFrame.lean` (`def:frame#Spherical`) and
      `Semantics/Correspondence/DurationFrames.lean` verbatim.
- [x] Cross-check each site against its `docs/theorem-index.md` row.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: local

**Scope Hypothesis**: 20 flagship declaration sites, 0 of which currently carry an anchor in
their own `/--` block. Re-derive the site list from `docs/theorem-index.md`'s rows at phase
start rather than from this plan. **Re-derived: 52 sites across 22 files**, 0 carrying an
anchor. 16 carry a real anchor, 36 carry `Paper: —` with a one-clause reason.

**Files to modify**:
- `FormalSystem/Metalogic/StrongCompleteness.lean`
- `FormalSystem/Metalogic/Compactness.lean`
- `FormalSystem/Metalogic/DiscreteNonCompactness.lean`
- `FormalSystem/Metalogic/DedekindNonCompactness.lean`
- `FormalSystem/Metalogic/BXCanonical/Completeness.lean`
- `FormalSystem/Metalogic/Soundness.lean`

**Verification**:
- `lake build` of each touched module succeeds (a new `/--` block must attach to the intended
  declaration).
- Every `docs/theorem-index.md` row's declaration has either its anchor or `Paper: —` in its own
  doc comment.

---

### Phase 7: Extend C15 with the index assertion [COMPLETED]

**Goal**: C15 gains a second, independent assertion: every `docs/theorem-index.md` row's named
declaration carries either the row's anchor or the literal `Paper: —` in its doc comment.

**Tasks**:
- [x] Parse `docs/theorem-index.md` rows inside C15 and assert the anchor-or-dash condition per
      row.
- [x] Keep the new assertion structurally independent of C15's existing resolution loop; do not
      entangle them, because that loop is currently red.
- [x] Accept `—` as a satisfied cell.
- [x] Report the two halves separately so the pre-existing three-anchor failure remains
      distinguishable from a new-assertion failure.

**Timing**: 1.5 hours

**Depends on**: 4, 6

**Verification Tier**: local

**Files to modify**:
- `scripts/check-module-invariants.sh` - C15 second assertion

**Verification**:
- C15's new assertion passes on the current index.
- C15's pre-existing failure is unchanged and still names exactly `app:drift`,
  `cor:no-characterization`, `lem:deterministic-singleton` — not "C15 passes".
  *(deviation: the premise is stale. Those three anchors now carry `LIVE-UNPINNED` rows in
  `specs/paper-definitions-of-record.md`'s KNOWN-ANCHORS block, so C15's resolution half is
  green and resolves 53 citations. Both halves pass. The plan's R2 risk and the corresponding
  non-goal are moot; no user decision is needed.)*
- Deliberately corrupting one index row's anchor makes the new assertion fail loudly and name
  that row.

---

### Phase 8: C20 citation check and C9 widening [COMPLETED]

**Goal**: A two-tier C20 exists (FAIL on out-of-range or blank-line citations repo-wide;
report-only on any `file.lean:NNN` citation in publication-facing scope, gated by
`ENFORCE_C20=1`), and C9's regex is widened to see `specs/NNN_` paths.

**Tasks**:
- [x] Implement C20 tier 1: resolve every `file.lean:NNN` citation in live scope; FAIL on
      out-of-range or blank-line targets.
- [x] Implement C20 tier 2: report (do not gate) any citation in the publication-facing scope —
      `README.md`, `docs/**`, `typst/**`, every `README.md` under `FormalSystem/**`, and
      `FormalSystem/*.lean` + `FormalSystem/Metalogic/*.lean` + `FormalSystem/Semantics/*.lean`.
- [x] Follow the existing `ENFORCE_C8`/`C9`/`C10` flag pattern for the tier-2 gate.
- [x] Explicitly exclude `FormalSystem/Metalogic/WeakCanonical/**` from tier 2.
- [x] Widen C9's regex with `specs/[0-9]{3}_` so ephemeral report-path citations are visible.
- [x] Record the convention (cite declaration names, never `file:line`) in the standing
      conventions section of `FormalSystem/README.md`.

**Timing**: 2 hours

**Depends on**: 7

**Verification Tier**: local

**Scope Hypothesis**: 1,354 live citations, 29 out of range, 81 on blank lines, 184 in
publication scope across 32 files, 1,083 in `WeakCanonical/**`. Re-derive all five numbers with
the new checker at phase start; the checker's own output supersedes every number in this plan.
**Re-derived by C20 itself**: 1,354 citations; **29** out of range and **89** on blank lines
(118 gated, not 110); **180** in publication scope across **29** files; 64 name a filename that
is ambiguous or archived and are reported unverifiable rather than failed. The widened C9
reports **14** ephemeral `specs/` path citations, one of which
(`scripts/check-evidence-probes.sh`) is a functional path a script reads, not a citation.

**Files to modify**:
- `scripts/check-module-invariants.sh` - C20, C9 regex
- `FormalSystem/README.md` - convention statement

**Verification**:
- C20 tier 1 reports a non-empty list matching the independently-derived wrong-citation set.
- `ENFORCE_C20=1` changes the exit code and the plain run does not.
- C9 with the widened regex reports the `specs/NNN_` sites.

---

### Phase 9: Fix every provably-wrong citation [COMPLETED]

**Goal**: C20 tier 1 is clean repo-wide, and every ephemeral `specs/NNN_slug/` path citation is
removed from live source.

**Tasks**:
- [x] Fix all out-of-range citations, concentrated in `Kamp/NfMultiAnchorBridge/` where fifteen
      sites cite an 87-line `SharedWitness.lean` at `:806`, `:9262`, `:12529`, `:12710`.
- [x] Fix all blank-line-target citations.
- [x] Fix `docs/development/PHASED_IMPLEMENTATION.md`'s citation of `Perpetuity.lean:139` (96
      lines).
- [x] Replace every `specs/NNN_slug/` path citation in live `.lean` files and live markdown with
      a durable anchor (declaration name or section heading), per
      `.claude/rules/no-task-references-in-deliverables.md`.

**Timing**: 2 hours

**Depends on**: 8

**Verification Tier**: prose

**Scope Hypothesis**: 110 provably-wrong sites (29 out-of-range + 81 blank-line) and 23
`specs/NNN_` citations (17 in `.lean`, 6 in markdown). The authoritative counts are C20's and
widened-C9's own output at phase start, not these. **Re-derived: 116 wrong sites across 58
files** (29 out-of-range + 87 blank-line) and **17** ephemeral `specs/` citations across 12
files, plus one functional path in `scripts/check-evidence-probes.sh` that is excluded rather
than rewritten.

**Fix applied**: the line number is *stripped*, leaving the filename — `Foo.lean:806` becomes
`Foo.lean`. The intended line is unrecoverable for an out-of-range citation and unknowable for a
blank-line one, so inventing a declaration name would be a guess; a bare filename is durable and
is what the convention asks for. Stripping a range's start (`Foo.lean:49-54`) left 24
`Foo.lean-54` artifacts, repaired in the same pass.

**Files to modify**:
- Files named by C20 tier 1 output (concentrated in
  `FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/`)
- `docs/development/PHASED_IMPLEMENTATION.md`
- The 13 live `.lean` files named by widened C9

**Verification**:
- C20 tier 1 exits clean.
- Widened C9 exits clean.
- Diff read-through confirms every hunk lies inside a comment region.

---

### Phase 10: Convert publication-scope citations [NOT STARTED]

**Goal**: The 184 publication-scope `file.lean:NNN` citations are replaced by declaration names,
and `docs/reference/API_REFERENCE.md` is brought current.

**Tasks**:
- [ ] Convert every citation in the publication-facing scope to a declaration name, resolving the
      name at the cited line before replacing.
- [ ] Fix `docs/reference/API_REFERENCE.md`'s six citations and its
      `**Last Updated**: 2026-01-11` header.
- [ ] Turn on `ENFORCE_C20=1` in the CI path once the scope is clean.

**Timing**: 2 hours

**Depends on**: 3, 6, 9

**Verification Tier**: prose

**Scope Hypothesis**: 184 citations across 32 files. Re-derive from C20 tier 2's output at phase
start; do not work from this number.

**Files to modify**:
- The 32 files named by C20 tier 2 output
- `docs/reference/API_REFERENCE.md`

**Verification**:
- `ENFORCE_C20=1 bash scripts/check-module-invariants.sh --no-build` exits 0 on the tier-2 gate.
- Diff read-through confirms comment-region containment.

---

### Phase 11: Docstring three-register pass A [NOT STARTED]

**Goal**: `Semantics/Validity.lean` and `Semantics/FrameClassValidity.lean` carry roughly half
their current prose, with no mathematical claim lost.

**Tasks**:
- [ ] Delete archaeology from `Validity.lean` (19 hits: "formerly a sorry", "before this delta",
      "earlier revisions of this docstring", "used to live").
- [ ] Rewrite remaining doc comments in the present tense stating what IS, with a paper anchor
      and caller traps where applicable.
- [ ] Fix `Validity.lean`'s claim that `SemanticConsequence` has a binder list (it is an
      abbreviation with none).
- [ ] Extract `FrameClassValidity.lean`'s rejected-refactoring passage (the `FrameClass`
      relocation rationale) for relocation to an ADR in Phase 13; leave a one-line pointer.
- [ ] Verify no mathematical claim was dropped by diffing the claim set before and after.

**Timing**: 2 hours

**Depends on**: 10

**Verification Tier**: local

**Scope Hypothesis**: `Validity.lean` is 1,001 lines at 71.3% comment share with 19 archaeology
hits; `FrameClassValidity.lean` is 202 lines at 83.2% with 0. Re-measure both at phase start.

**Files to modify**:
- `FormalSystem/Semantics/Validity.lean`
- `FormalSystem/Semantics/FrameClassValidity.lean`

**Verification**:
- `lake build` of both modules succeeds.
- Comment share drops toward 50% on `Validity.lean`.
- The archaeology-phrase grep returns zero hits in both files.
- C19 docstring coverage does not regress below 90%.

---

### Phase 12: Docstring three-register pass B [NOT STARTED]

**Goal**: `StrongCompleteness.lean` and `SetConsequence.lean` carry roughly half their current
prose; `Conservativity.lean`'s duplicated ledger rows are removed.

**Tasks**:
- [ ] Delete the 15 archaeology hits in `StrongCompleteness.lean` and the 12 in
      `SetConsequence.lean`, including "before this collapse there were four byte-identical
      definitions" and "pre-collapse binder shape".
- [ ] Rewrite remaining doc comments in the what-IS register.
- [ ] Remove `Conservativity.lean`'s ledger rows that duplicate `Metalogic.lean`, replacing them
      with a pointer to `docs/theorem-index.md`. Do **not** halve this file: its 95.9% comment
      share is by design and its content is the CEB/CEF/CED/CEC record.
- [ ] Extract layering-rationale passages for Phase 13's ADRs; leave one-line pointers.

**Timing**: 2 hours

**Depends on**: 3, 10

**Verification Tier**: local

**Scope Hypothesis**: `StrongCompleteness.lean` 1,125 lines / 75.8% / 15 hits;
`SetConsequence.lean` 626 / 72.7% / 12; `Conservativity.lean` 295 / 95.9% / 1. Re-measure at
phase start.

**Files to modify**:
- `FormalSystem/Metalogic/StrongCompleteness.lean`
- `FormalSystem/Metalogic/SetConsequence.lean`
- `FormalSystem/Metalogic/Conservativity.lean`

**Verification**:
- `lake build` of all three modules succeeds.
- Archaeology grep returns zero hits across the three files.
- C19 coverage does not regress below 90%.

---

### Phase 13: Architecture decision records [NOT STARTED]

**Goal**: Four ADRs exist under `docs/architecture/` (ADR-005 onward, matching the existing
convention), and their source sites carry pointers instead of duplicated rationale.

**Tasks**:
- [ ] Record the convention decision explicitly in the first new ADR: `docs/architecture/ADR-NNN`
      is used, not a new `docs/decisions/` directory, because the repo already carries
      ADR-001..ADR-004 there.
- [ ] `ADR-005-single-boneyard.md` — archive consolidation, replacing the narrative at
      `FormalSystem/README.md:11-33` and `Metalogic/README.md:10-22`.
- [ ] `ADR-006-metalogic-no-physical-regroup.md` — "Why There Is No Physical Regroup" and "The
      declined regroup" from `Metalogic/README.md`.
- [ ] `ADR-007-decidability-one-directional.md` — the `validity_decidable` retirement, currently
      told in four places (`README.md`, `FormalSystem/README.md`, `Decidability/README.md`,
      `Decidability/Verified/README.md`).
- [ ] `ADR-008-frameclass-validity-seam.md` — the rejected `FrameClass` relocation from
      `FrameClassValidity.lean`.
- [ ] Replace each source site with a one-line pointer to its ADR.

**Timing**: 2 hours

**Depends on**: 11, 12

**Verification Tier**: prose

**Scope Hypothesis**: four rationale narratives across seven source sites, one of which
(`validity_decidable`) has four copies. Re-derive the copy set by grepping for the
`validity_decidable` retirement phrasing at phase start.

**Files to modify**:
- `docs/architecture/ADR-005-single-boneyard.md` (new)
- `docs/architecture/ADR-006-metalogic-no-physical-regroup.md` (new)
- `docs/architecture/ADR-007-decidability-one-directional.md` (new)
- `docs/architecture/ADR-008-frameclass-validity-seam.md` (new)
- `FormalSystem/README.md`, `FormalSystem/Metalogic/README.md`,
  `FormalSystem/Metalogic/Decidability/README.md`,
  `FormalSystem/Metalogic/Decidability/Verified/README.md`, `README.md`,
  `FormalSystem/Semantics/FrameClassValidity.lean` - pointers replace rationale

**Verification**:
- Each rationale appears exactly once in the tree (grep for a distinctive phrase from each).
- `docs/architecture/README.md` lists the four new ADRs.

---

### Phase 14: Sentence-level duplication detection [NOT STARTED]

**Goal**: C18 gains a sentence-level shingle pass, and the two surviving cross-file duplicates
are removed.

**Tasks**:
- [ ] Add a sentence-boundary shingle pass (minimum 15 words) to C18 over `README.md`,
      `FormalSystem/Metalogic.lean`, and the other status surfaces; widen C18, do not add a C21.
- [ ] Remove the duplicate at `README.md:270` / `Metalogic.lean:153` ("single mechanism by which
      closure is shown").
- [ ] Remove the duplicate at `README.md:283` / `Metalogic.lean:164` ("`Mod (AxiomSet .Discrete)`
      and `Mod (AxiomSet .Dedekind)` remain open").
- [ ] Confirm the paragraph-level pass is retained unchanged; it is still the right detector for
      wholesale copy-paste.

**Timing**: 1.5 hours

**Depends on**: 3, 8, 12, 13

**Verification Tier**: local

**Scope Hypothesis**: exactly two sentence-level duplicates survive (research §3.1 found two of
the description's four). The widened C18's own output at phase start is authoritative.

**Files to modify**:
- `scripts/check-module-invariants.sh` - C18 sentence pass
- `README.md`
- `FormalSystem/Metalogic.lean`

**Verification**:
- C18 reports zero at both paragraph and sentence granularity.
- Re-introducing one removed sentence makes the new pass fail loudly and name both sites.

---

### Phase 15: Verifiable-mismatch sweep [NOT STARTED]

**Goal**: Every remaining verified factual mismatch outside the inventory and citation systems is
fixed.

**Tasks**:
- [ ] `Semantics.lean` truth-clause block: correct the three-tuple frame to the four-axiom
      `(W, D, R)` form, remove Nullity from the frame-axiom list (README calls it derived),
      correct the five-argument `TruthAt` to four, correct the `□` clause from `σ.domain t` to
      `σ.IsTotal`, delete the non-existent `H`/`G` clauses, and fix or delete the ` ```lean `
      `#check` example that would not compile.
- [ ] `Soundness.lean`: delete the claim that `TruthAt`'s remaining set argument is supplied as
      `Set.univ` (`TruthAt` takes four arguments).
- [ ] `Semantics/Truth.lean`: delete the pointer to a module-hierarchy-restructuring detail that
      `SoundnessLemmas.lean` does not carry.
- [ ] `SoundnessLemmas/FrameClassVariants.lean`: delete the "resolves the 3 `temporal_duality`
      sorries" claim with its three wrong line numbers (zero sorries exist; C3 asserts it).
- [ ] `Automation/AesopRules.lean`: delete the "excluded pending soundness proofs: TL, MF"
      claim; both are proved.
- [ ] `README.md`: fix `cd ProofChecker` after cloning `BimodalLogic`; reconcile the BibTeX
      `year = {2025}` against `year = {2026}`.
- [ ] Replace the 26 `Bimodal.*` references across 14 READMEs (the namespace does not exist).
- [ ] `docs/README.md`: fix or remove the `lake build :docs` recipe — `doc-gen4` is in neither
      `lakefile.lean` nor `lake-manifest.json`.

**Timing**: 2 hours

**Depends on**: 10

**Verification Tier**: local

**Scope Hypothesis**: 26 `Bimodal.*` references across 14 READMEs; five A-10 stale claims of
which one site (`SoundnessLemmas/Core.lean`) no longer exists and one (`Validity.lean:918`) is
Phase 11's territory. Re-derive both greps at phase start.

**Files to modify**:
- `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/Truth.lean`,
  `FormalSystem/Metalogic/Soundness.lean`,
  `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`,
  `FormalSystem/Automation/AesopRules.lean`
- `README.md`, `docs/README.md`, and the 14 READMEs carrying `Bimodal.*`

**Verification**:
- `grep -rn '\bBimodal\.[A-Z]' --include=*.md` returns zero.
- `lake build` of each touched Lean module succeeds.
- Each corrected claim is checked against the live declaration it describes.

---

### Phase 16: README completeness and stamps [NOT STARTED]

**Goal**: `bash scripts/readme-lint.sh` exits 0.

**Tasks**:
- [ ] Create the five missing READMEs: `ForMathlib/Order/`,
      `FormalSystem/Metalogic/Conservativity/` (12 files, 2,508 lines),
      `FormalSystem/Metalogic/Conservativity/Star/`, `FormalSystem/Semantics/Frames/`,
      `FormalSystem/Semantics/Ultraproduct/`, using `Semantics/README.md` as the quality model
      and the Phase 1 generator for their count tables.
- [ ] Refresh the 9 stale and add the 7 missing `Last verified` stamps across the 47 READMEs.
- [ ] Regenerate `Automation/README.md`'s module list: 15 wrong line counts, 16 missing loose
      modules, and 2 phantom entries (`Automation.lean`, `EFGameTactics.lean`).
- [ ] Add `DiscreteOrder.lean` to `SoundnessLemmas.lean`'s Contents **and** its imports — the
      identical defect A-10 recorded for `Separability.lean`.

**Timing**: 2 hours

**Depends on**: 2, 3, 13, 14, 15

**Verification Tier**: full

**Scope Hypothesis**: 5 missing READMEs, 9 stale + 7 missing stamps across 47 READMEs, 15 wrong
Automation counts. `readme-lint.sh`'s own output at phase start is authoritative.

**Files to modify**:
- Five new `README.md` files
- `FormalSystem/Automation/README.md`
- `FormalSystem/Metalogic/SoundnessLemmas.lean` - Contents and import
- The READMEs carrying stale or missing stamps

**Verification**:
- `bash scripts/readme-lint.sh` exits 0.
- `lake build` succeeds after the `SoundnessLemmas.lean` import addition.
- `check-metalogic-cycles.sh` still passes.

---

### Phase 17: Generate the typst axiom table [NOT STARTED]

**Goal**: `typst/generated/status.typ` carries a generated per-declaration axiom table,
`FormalFoundations.typ`'s hand table is replaced by a `#for` over it, and the three-way
provenance stamp is unified.

**Tasks**:
- [ ] Extend `scripts/typst-status-counts.sh` following the
      `scripts/typst-machine-appendix.sh` pattern: compile a scratch file of `#print axioms`
      directives for the pinned set, parse the output, emit `#let axiom-report-table = (…)`.
- [ ] Use fully-qualified names in every generated row, or the table repeats the
      `completeness_dense` ambiguity it currently has.
- [ ] Replace the hand-written 5-row table in `typst/FormalFoundations.typ` with a `#for` over
      the generated value.
- [ ] Unify provenance: `FormalFoundations.typ`'s "taken at commit `7aae4e51c`" reads from
      `status.typ`'s `stamp-commit`.
- [ ] Fix E-10: split the sorry table into two rows so
      `sorry-total-excl-boneyard = 0` no longer prints beside `("WeakCanonical/", 4)`; the
      generator already computes `SORRY_WEAKCANONICAL_LIVE` and `SORRY_KAMP_BONEYARD`
      separately.
- [ ] Keep the generator a separate script invocation; it needs a built library and cannot run
      under `--no-build`.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Files to modify**:
- `scripts/typst-status-counts.sh`
- `typst/generated/status.typ` (generated)
- `typst/FormalFoundations.typ`

**Verification**:
- `bash scripts/typst-sync-check.sh` passes.
- The typst document compiles.
- Exactly one provenance commit stamp appears across `status.typ` and `FormalFoundations.typ`.

---

### Phase 18: Publication packaging [NOT STARTED]

**Goal**: `CITATION.cff`, `docs/ARCHITECTURE.md`, `references.bib` and README's
`## Verifying the main theorems` section exist.

**Tasks**:
- [ ] Create `CITATION.cff` with `year: 2026`, reconciling the BibTeX discrepancy, and state the
      ProofChecker/BimodalLogic name relationship exactly once.
- [ ] Create `docs/ARCHITECTURE.md` with one layer diagram naming **both** upward edges:
      `Semantics -> ProofSystem` via `Semantics/FrameClassValidity.lean`, and
      `Decidability -> Automation`. Source the layers from `FormalSystem/README.md`'s six
      one-row layer tables and `Metalogic/README.md`; include Layer 0's `ForMathlib` and
      `StarLanguage`, which no existing diagram shows.
- [ ] Create `references.bib` with Reynolds, Blackburn-de Rijke-Venema, Kamp and Prior, already
      cited in prose in `ProofSystem/Axioms.lean`'s `sep` docstring.
- [ ] Add `## Verifying the main theorems` to `README.md`: a `#print axioms` snippet over a
      representative slice of the pinned declarations (not all of them) plus the one-line
      `bash scripts/check-module-invariants.sh`.

**Timing**: 2 hours

**Depends on**: 5, 17

**Verification Tier**: prose

**Files to modify**:
- `CITATION.cff` (new)
- `docs/ARCHITECTURE.md` (new)
- `references.bib` (new)
- `README.md` - new `## Verifying the main theorems` section

**Verification**:
- The `#print axioms` snippet in the README runs verbatim and produces the documented output.
- Both upward edges appear in the `docs/ARCHITECTURE.md` diagram body, not only in prose.
- C12/C13 pass; markdown link checks pass on the new files.

---

### Phase 19: Tags lines [NOT STARTED]

**Goal**: The files a reader would search carry a `## Tags` line.

**Tasks**:
- [ ] Derive the target set from `docs/theorem-index.md`'s File column plus the `Semantics/` and
      `Correspondence/` layer files; record the derived list in the phase's commit message.
- [ ] Add a `## Tags` line to each, using a consistent vocabulary drawn from the index's
      Notation-and-naming table.
- [ ] Add `## Tags` to `docs/theorem-index.md`, `docs/ARCHITECTURE.md` and `README.md`.

**Timing**: 1.5 hours

**Depends on**: 5, 13, 14, 16

**Verification Tier**: prose

**Scope Hypothesis**: the description estimates ~30 files and the tree currently has zero
`## Tags` lines. The target set is derived, not assumed — confirm the derived count before
editing and record it.

**Files to modify**:
- The derived target set (files named by `docs/theorem-index.md` plus the `Semantics/` and
  `Correspondence/` layers)

**Verification**:
- Every file in the derived set carries exactly one `## Tags` line.
- Diff read-through confirms comment/prose-region containment in the `.lean` targets.

## Lean Challenge Statements

This is a documentation and tooling task: the `- **Goals**:` bullets above name **zero new Lean
declarations**, so the identifier set pinned by this section is empty and no ```lean fenced block
is present. The only Lean-file edits in this plan are doc comments, module docstrings, one added
`/--` block on the existing `FormalSystem.Metalogic.BXCanonical.completeness`, and one added
import in `SoundnessLemmas.lean`. No theorem statement, proof term, or definition is introduced,
renamed, or changed.

## Testing & Validation

- [ ] `bash scripts/check-module-invariants.sh --no-build` — C7, C9, C14 (structural half), C18,
      C20 tier 1 all pass; C15's new assertion passes; C15's pre-existing three-anchor failure is
      the only remaining non-zero cause.
- [ ] `bash scripts/check-module-invariants.sh` (full, with build, via the guarded long-build
      pattern) — C14 passes with the extended baseline.
- [ ] `bash scripts/check-module-invariants.sh --emit-inventory --check` exits 0.
- [ ] `ENFORCE_C20=1 bash scripts/check-module-invariants.sh --no-build` exits 0.
- [ ] `bash scripts/readme-lint.sh` exits 0.
- [ ] `bash scripts/typst-sync-check.sh` passes and the typst document compiles.
- [ ] `lake build` green.
- [ ] `grep -rEn 'before the collapse|formerly a strategic sorry|earlier revisions of this docstring|used to live'`
      returns zero hits on live surfaces.
- [ ] `grep -rn '\bBimodal\.[A-Z]' --include=*.md` returns zero.
- [ ] Every `docs/theorem-index.md` Lean name resolves and every File cell names an existing path
      with no `:NNN`.
- [ ] C19 docstring coverage has not regressed below 90%.

## Artifacts & Outputs

- `docs/theorem-index.md` (new) — the sole per-theorem status ledger
- `docs/ARCHITECTURE.md` (new) — layer diagram with both upward edges
- `CITATION.cff` (new), `references.bib` (new)
- `docs/architecture/ADR-005-single-boneyard.md`,
  `ADR-006-metalogic-no-physical-regroup.md`,
  `ADR-007-decidability-one-directional.md`,
  `ADR-008-frameclass-validity-seam.md` (new)
- Five new directory READMEs (`ForMathlib/Order/`, `Metalogic/Conservativity/`,
  `Metalogic/Conservativity/Star/`, `Semantics/Frames/`, `Semantics/Ultraproduct/`)
- `scripts/check-module-invariants.sh` — `--emit-inventory[ --check]`, extended `C14_BASELINE`,
  C15 second assertion, C18 sentence pass, new C20, widened C9
- `scripts/typst-status-counts.sh` — generated per-declaration axiom table
- Nine registered READMEs converted to generated inventory blocks
- `specs/530_documentation_single_source_of_truth_theorem_index/summaries/01_*-summary.md`

## Rollback/Contingency

Every phase is a self-contained commit on a task branch and reverts independently. The two
highest-risk reversions:

- **Phases 1-2 (generated inventory blocks)**: if description carry-across proves lossy, revert
  the two commits and the hand-written tables return intact; the generator's `--check` mode is
  the pre-commit detector, so this should surface before the commit lands.
- **Phase 4 (C14 baseline)**: if the extended baseline turns out to pin a declaration whose axiom
  set is genuinely not `pcq`, remove that row rather than reverting the phase — the recorded
  literal-list values in `docs/theorem-index.md` are the fallback record.

If the task must be abandoned mid-flight, the ordering guarantees a coherent stopping point after
any wave: the generator (waves 1-2), the index (waves 3-4), the checks (waves 5-7), the text
cleanups (waves 8-10) and the packaging (waves 11-12) are each independently valuable and leave
no half-owned surface.
