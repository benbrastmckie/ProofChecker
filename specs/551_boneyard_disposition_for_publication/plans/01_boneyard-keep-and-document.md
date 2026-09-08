# Implementation Plan: Boneyard Disposition for Publication

- **Task**: 551 - Boneyard disposition for publication
- **Status**: [COMPLETED]
- **Effort**: 11 hours
- **Dependencies**: None
- **Research Inputs**: specs/551_boneyard_disposition_for_publication/reports/01_boneyard-disposition-recommendation.md
- **Artifacts**: plans/01_boneyard-keep-and-document.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Research returned a decided verdict: **KEEP the archive, and repair the documentation that
describes it.** CUT ENTIRELY is unavailable (96 files outside the archive cite it, including the
published LaTeX at `latex/subfiles/04-Metalogic.tex:389` and 46 live `.lean` docstrings), SPLIT
buys ~2% of the archive's lines at the cost of ADR-005's single-archive invariant, and the user's
own stated focus is to keep the Boneyard while cleaning it up and improving its documentation.
The archive itself is sound — zero `.olean` files under any `Boneyard` path out of 546 built,
zero structural `sorry` in the live tree, C11 resolving all 536 archived import lines. What
ships badly is its description: four defects (D1-D4 below) that a reviewer would find
immediately. This plan executes the KEEP decision, records it as an ADR so the tree is no longer
shipped undecided, and converts the archive's hand-typed counts into gate-generated ones so the
drift that produced D1/D2 cannot recur.

### Research Integration

Findings carried directly into phases:

- **D1 — three disagreeing archive counts.** `Boneyard/README.md` §One Archive says 163 files /
  90,797 lines / 37 subdirs; `FormalSystem/README.md:312` independently says 156; the §Directory
  Inventory total row says 93 files / 58,738 lines. Measured truth: 168 files / 91,539 lines.
  Phases 4, 5, 9.
- **D2 — the §Directory Inventory describes a tree that no longer exists.** Four rows name
  top-level entries ADR-005 moved under `Kamp/`; five existing subtrees are absent, including
  `Kamp/` itself (47.6% of the archive). Phase 5.
- **D3 — `FormalSystem/FormalSystem.lean` contradicts ADR-005**, still describing "both Boneyard
  trees" and "either tree" in the library's top-level aggregator docstring. Phase 9. Independently
  confirmed during planning: the same docstring's "(210 live files)" for `Metalogic` is also
  stale — the measured live count is 348.
- **D4 — provenance keyed to internal task numbers.** A 19-row §Task Cross-References table and a
  `Task` column keyed on integers that resolve only against `specs/`. Phase 6.
- **Root cause.** `scripts/check-module-invariants.sh`'s `markdown_targets()` prunes `Boneyard`
  from the inventory generator's markdown walk, so the archive README is the one README in the
  tree whose counts are hand-typed and ungated. Phase 2.

Two research statements were checked during planning and are carried as hypotheses rather than
facts, because they drive design decisions in Phase 2:

- Research states a Boneyard-aware variant of `live_subdirs`/`live_files` is required. Reading
  `scripts/lib/live_walk.py`, the exclusion is by the literal directory *name* `Boneyard`, and no
  subdirectory of the archive carries that name (B0 asserts exactly one such directory exists),
  so `live_subdirs("FormalSystem/Boneyard")` and `live_files(sub, ".lean")` appear to work
  unmodified when the archive is itself the scan base. What does need work is narrower and is
  stated in Phase 2's Scope Hypothesis.
- Research states 12 archived files "lack the `#exit` guard that §Build Policy mandates".
  §Expected File Structure actually reads "may use `#exit` for non-compiling reference code" —
  permissive, not mandatory. Phase 3 therefore resolves the policy explicitly before applying it.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only (no `roadmap_flag` was set; no roadmap phases are
added and ROADMAP.md is not modified by this plan). This work sits in:

- **Phase 5: Publication and Documentation** — the front's check grounding is named as "C5
  (module-shaped path resolution in markdown/docs), C9 (zero task-number citations under
  `FormalSystem/`)", which is precisely D4's and Phase 9's territory.
- **Phase 7: Repository Hygiene and Programme Metadata** — the archive's governance and counts.

## Goals & Non-Goals

**Goals**:
- Record the KEEP disposition as a durable, publication-facing decision record, so the archive is
  no longer shipped undecided or unexplained.
- Make the archive's counts machine-generated and gate-enforced, closing D1/D2 at the mechanism
  rather than the symptom.
- Repair D1-D4 so no published file states a wrong or internally-keyed fact about the archive.
- Improve the archive's documentation and comments: a publication-facing framing paragraph, the
  six missing subtree READMEs, and complete taxonomy/detail coverage of all subtrees.
- Preserve, and re-verify by census, the two properties that neutralize the archive's size for a
  reviewer: zero `.olean` under any `Boneyard` path, and zero structural `sorry` in the live tree.

**Non-Goals**:
- Deleting, cutting, or splitting any part of `FormalSystem/Boneyard/`. Task step 4 (execute the
  cut) is not triggered: the recommendation is KEEP and the user's stated focus is to keep it.
- Deleting any archived `.lean` file, including the tombstone-eligible ones. No doc-only
  consolidation pass is in scope.
- Migrating archived identifiers to Mathlib naming, or applying the `untl`/`snce` argument swap.
  Both are deliberately-not-done per the archive's own CONVENTION WARNING.
- Changing any live proof, definition, or tactic. This plan proves no new Lean theorems.
- Modifying `specs/ROADMAP.md`.
- Rewriting `.claude/**` — that tree is a disposable deploy artifact (see
  `.claude/rules/source-store-deploy-boundary.md`); nothing in this plan targets it.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Editing `check-module-invariants.sh` turns INV, B0 or C7 red | H | M | Phase 2 changes the generator with **no** markers yet registered, so `--emit-inventory --check` must remain byte-for-byte green; B0 independently asserts the exclusion filter still removes a non-zero count, so an accidental un-exclusion fails loudly. Full run before and after. |
| Un-pruning `Boneyard` from `markdown_targets()` silently activates checks over 49 archive `.md` files | M | L | Verified during planning: zero `BEGIN GENERATED` and zero `INVENTORY: hand-maintained` markers exist anywhere under `FormalSystem/Boneyard/`, so the walk gains files but no work. Phase 2 re-confirms this before the edit. |
| A generated inventory drops the 9 tombstone subtrees (`scan()` skips subdirs with no `.lean` members) | M | H | Phase 2 explicitly adds representation for README-only subtrees, or Phase 5 registers the table as hand-maintained instead; the choice is made in Phase 2 against the observed generator behavior, not assumed here. |
| Registering the §Directory Inventory as hand-maintained flags tombstone rows as phantoms | M | M | `audit_hand_maintained` computes `want` from subdirs that have `.lean` members, and flags `have - want` entries ending in `/`. Phase 5 confirms the row-key shape against the real checker output before committing the table. |
| Moving the loose `VacuousKEquiv.lean` breaks a live citation | M | M | Exactly one live citation exists (`FormalSystem/Metalogic/WeakCanonical/OrderedSum.lean:54`) plus the inventory row. Phase 3 either updates both atomically or takes the lower-risk option of amending §Expected File Structure to admit a documented root-level file. |
| Re-keying provenance to commit SHAs loses the link if history is rewritten | L | L | Pair every SHA with its date; the existing `When` column already supplies dates, so the pair is redundant enough to survive a rewrite. |
| Correcting counts is a one-shot fix that drifts again | H | H | This is why Phase 2 (generator registration) precedes every count repair: Phases 4-5 are only durable once the numbers are generated rather than typed. |
| Tightening C9 to stop excluding `/Boneyard/` cascades into 168 archived `.lean` files | M | M | Phase 6 measures first (90 C9-shaped occurrences across 34 files under the archive; only 2 in the top-level README) and scopes the tightening to what is actually cleared, or defers it with a recorded reason. |
| A reviewer still reads 91,539 archived lines as a red flag | M | M | Phase 7's framing paragraph leads with the two machine-checked facts that neutralize it (C1: zero `.olean` under any archive path out of 546; C3: zero structural `sorry` live). |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 2, 3 |
| 4 | 5, 9 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 10 | 8, 9 |

Phases within the same wave can execute in parallel. Waves 2 and 4 contain the only genuine
parallelism: Phase 2 owns `scripts/`, Phase 3 owns the archive's subtree directories, and Phase 9
owns the two live-tree files — no two phases in a wave write the same file. Phases 5, 6, 7 and 8
all write `FormalSystem/Boneyard/README.md` and are therefore serialized against each other by
construction, not by data dependency alone.

### Phase 1: Record the KEEP Decision and Capture the Verified Baseline [COMPLETED]

**Goal**: Convert the research recommendation into a durable decision record, and freeze the
before-state that Phase 10 will re-verify against.

**Tasks**:
- [x] Capture the baseline: run `bash scripts/check-module-invariants.sh` (with build) and record
      the full output; record `find .lake/build -name '*.olean' | wc -l`,
      `find .lake -path '*Boneyard*' -name '*.olean' | wc -l`, the C3 live-sorry count, and the
      archive census (`.lean` file count, line count, top-level entry count).
- [x] Write `docs/architecture/ADR-009-Boneyard-Retention.md` (next free number; ADR-001, 004,
      005, 006, 007, 008 exist). Status: Accepted. Content: the KEEP verdict; why CUT ENTIRELY is
      unavailable (the `04-Metalogic.tex:389` citation, 46 live `.lean` docstrings, ADR-005's
      B0/C11 gates, `scripts/boneyard-import-waivers.txt`); why SPLIT is not worth its cost
      (~2% of archive lines removable, and its largest member records a *refuted* route — the
      category with the most scholarly value); what KEEP obliges (counts generated not typed,
      provenance keyed to durable anchors, a publication-facing framing).
- [x] Cross-link the new ADR from `docs/architecture/README.md` in whatever form that file already
      uses for ADR-005 through ADR-008.
- [x] Confirm the ADR contains no task-number citations (`.claude/rules/no-task-references-in-deliverables.md`;
      `docs/` is covered by C9D, computed and reported though not yet enforced).

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: ADR-009 is asserted to be the next free ADR number and
`docs/architecture/README.md` is asserted to be the index that needs the cross-link. Confirm with
`ls docs/architecture/` and by reading that README before writing, rather than trusting this line.

**Files to modify**:
- `docs/architecture/ADR-009-Boneyard-Retention.md` - new; the KEEP decision record
- `docs/architecture/README.md` - add the ADR to the index

**Verification**:
- The baseline output is recorded verbatim in the phase's commit message or a scratch note that
  Phase 10 can compare against.
- `bash scripts/check-module-invariants.sh --no-build` still reports ALL CHECKS PASSED (a new
  `docs/` markdown file must not perturb C5's module-shaped path resolution).
- Every hunk of this phase's diff lies in a new or existing markdown file; no `.lean` or `.sh`
  file is touched.

---

### Phase 2: Make the Inventory Generator Archive-Aware [COMPLETED]

**Goal**: Remove the mechanical cause of D1/D2 — the archive is the one tree whose counts the
generator cannot see — without changing a single byte of current output.

**Tasks**:
- [x] Re-confirm zero `BEGIN GENERATED` and zero `INVENTORY: hand-maintained` markers exist under
      `FormalSystem/Boneyard/`, so un-pruning cannot activate latent work.
- [x] Drop `"Boneyard"` from the directory filter in `markdown_targets()`
      (`scripts/check-module-invariants.sh`), leaving `.git`, `specs`, `.claude`, `.lake` and
      `node_modules` pruned. Note in a comment why the archive is now walked (its README owns the
      archive's counts and must be gated like every other README).
- [x] Teach `scan()`'s `rows=totals` branch to label correctly when the scan base is itself the
      archive. Today it computes `live = live_files(directory, ".lean")` and separately collects
      files whose path contains `/Boneyard/`; with `dir=FormalSystem/Boneyard` both sets are the
      same 168 files, so the block would emit a "Live `.lean` files" row for archived code.
      Emit archive-shaped rows instead (archived file count, archived line count, top-level
      subdirectory count, archive-directory count).
- [x] Give the `rows=subdirs` branch a way to represent a README-only subtree. `scan()` currently
      does `if not members: continue`, which would silently drop all 9 tombstones from a generated
      archive inventory — a regression against today's hand-typed table, which lists them.
- [x] Document any new marker option in the `--emit-inventory` header comment block, which is the
      generator's documented option surface.
- [x] Run `bash scripts/check-module-invariants.sh --emit-inventory --check`: it must pass with no
      file reported changed, because no marker has been registered yet. *(deviation: altered — it
      passed byte-for-byte at the moment of the edit; a later re-run reported one changed file,
      `README.md`'s `Live lines` rollup moving 282,014 -> 282,051, which is the concurrent
      live-tree `WorldHistory` -> `ConvexHistory` work and not this phase. Diff inspected
      line-by-line to confirm; the file was restored untouched.)

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that `live_subdirs`/`live_files` in
`scripts/lib/live_walk.py` need **no** modification (their exclusion is by the literal directory
name `Boneyard`, which no subdirectory of the archive carries), contradicting the research
report's expectation of a Boneyard-aware variant. Confirm at implementation time by calling
`live_subdirs("FormalSystem/Boneyard")` and checking it returns the 39 subtree directories; if it
does not, add the variant the research anticipated and record the correction.

**Files to modify**:
- `scripts/check-module-invariants.sh` - `markdown_targets()` filter; `scan()` totals labelling
  and empty-subdir representation; `--emit-inventory` option documentation
- `scripts/lib/live_walk.py` - only if the Scope Hypothesis above is refuted *(not modified:
  the Scope Hypothesis was CONFIRMED — `live_subdirs("FormalSystem/Boneyard")` returns the 39
  subtree directories and `live_files` returns all 168 archived files, so no Boneyard-aware
  variant was needed. The research report's expectation is corrected here.)*

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` passes and reports **zero**
  changed files (this is the no-op guarantee: capability added, output unchanged).
- `bash scripts/check-module-invariants.sh` (full, with build) reports ALL CHECKS PASSED, with B0
  still asserting exactly 1 archive directory and a non-zero exclusion count, and C7's live
  inventory numerically identical to the Phase 1 baseline.
- `git diff` confirms no `.md` file changed in this phase.

---

### Phase 3: Close the Archive's Structural Gaps [COMPLETED]

**Goal**: Settle the archive's file-level shape before any count is generated over it, so the
inventory is built once against a stable tree.

**Tasks**:
- [x] Write the six missing subtree READMEs, each following the shape §Expected File Structure
      requires (purpose, file inventory, why archived, relationship to active code):
      `BXCanonicalQuasimodel/`, `DeadConvergenceProof/`, `FMPVariants/`, `RestrictedMCSDeferral/`,
      `SoundnessVariants/`, `StaviDiscretePath/`. Source the "why archived" text from the existing
      §Directory Inventory row and §Subdirectory Details entry for each, not from fresh invention.
- [x] Resolve the `#exit` policy explicitly. *(chose option (a): mandatory.)* §Build Policy establishes liveness-equals-
      reachability (no lakefile target covers the archive); §Expected File Structure says archived
      `.lean` files *may* use `#exit`. Either (a) amend §Expected File Structure to state that
      `#exit` is mandatory and add it to the 12 files that lack it, or (b) state plainly that
      `#exit` is a belt-and-braces convenience and not required, and leave the 12 alone. Record
      the choice and its reason in the README; do not leave the two sections in tension.
- [x] Option (a) taken: `#exit` added to the 12 files, preserving each file's existing
      `ARCHIVED (Boneyard)` header placement. Note that 11 of the 12 sit in `BundleDeadHalf/`,
      `RetiredTactics/`, `LimitMCSCoherenceDeadCases/` and `SupersededCompleteness/` — the four
      subtrees archived after the last README refresh, which is the same story as their absence
      from the inventory table.
- [x] Decide the loose `FormalSystem/Boneyard/VacuousKEquiv.lean`. *(chose the amend-the-policy option: the file stays at the archive root, admitted explicitly by §Expected File Structure and given a generated inventory row; zero live-tree diff.)* Exactly two references exist:
      `FormalSystem/Metalogic/WeakCanonical/OrderedSum.lean:54` (a live docstring, path-shaped) and
      the §Directory Inventory row. Either `git mv` it into a `VacuousKEquiv/` subtree with a
      README and update both references atomically, or amend §Expected File Structure to admit a
      documented root-level file. Prefer whichever leaves C5 green with the smaller live-tree diff.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Six subtrees are asserted to lack a README and twelve archived `.lean` files
to lack `#exit`. Confirm at implementation time with
`for d in FormalSystem/Boneyard/*/; do [ -f "$d/README.md" ] || echo "$d"; done` and
`for f in $(find FormalSystem/Boneyard -name '*.lean'); do grep -q '^#exit' "$f" || echo "$f"; done`,
and reconcile any difference before acting on the list.

**Files to modify**:
- `FormalSystem/Boneyard/{BXCanonicalQuasimodel,DeadConvergenceProof,FMPVariants,RestrictedMCSDeferral,SoundnessVariants,StaviDiscretePath}/README.md` - new
- `FormalSystem/Boneyard/README.md` - §Expected File Structure / §Build Policy `#exit` policy statement
- Up to 12 archived `.lean` files - `#exit` guards, only under option (a)
- `FormalSystem/Metalogic/WeakCanonical/OrderedSum.lean` - only if `VacuousKEquiv.lean` moves

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED — in particular
  C5 (module-shaped path resolution in markdown/docs) after any new README's internal links, and
  C11 (all archived import lines resolve) after any file move.
- `lake build` stays green if any live-tree file was touched; archived `.lean` edits cannot affect
  it, since no `.olean` is produced under any `Boneyard` path.
- `bash scripts/readme-lint.sh` still passes (it skips `Boneyard` at every stage, so new subtree
  READMEs are expected to be invisible to it — confirm rather than assume).

---

### Phase 4: Generate the Archive's Counts at Their Single Source [COMPLETED]

**Goal**: Replace the hand-typed counts table in §One Archive with a generated block, so D1's
primary instance becomes a gate-enforced invariant.

**Tasks**:
- [x] Wrap the §One Archive counts table in
      `<!-- BEGIN GENERATED: inventory dir=FormalSystem/Boneyard rows=totals ... -->` /
      `<!-- END GENERATED -->`, using the archive-shaped rows Phase 2 added.
- [x] Run `bash scripts/check-module-invariants.sh --emit-inventory` and inspect the rewritten
      block. Independently re-derive each emitted number
      (`find FormalSystem/Boneyard -name '*.lean' | wc -l`,
      `find FormalSystem/Boneyard -name '*.lean' -exec cat {} + | wc -l`) and confirm agreement.
- [x] Keep the surrounding prose that makes this section the single source, and keep the
      `Archive directories in the repository | 1` claim tied to B0 rather than to a typed figure.
- [x] Preserve the existing narrative about the consolidated second archive and the `find` filter
      guidance — the generated block replaces the *table*, not the section.

**Timing**: 1 hour

**Depends on**: 2, 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The archive is asserted to hold 168 `.lean` files and 91,539 lines against
documented figures of 163 / 90,797. These are post-Phase-3 quantities and may have shifted if
Phase 3 moved a file. Confirm from the generator's own output, and treat any disagreement between
the generator and a hand `find` as a Phase 2 defect rather than as a number to type in.

**Files to modify**:
- `FormalSystem/Boneyard/README.md` - §One Archive counts table becomes a generated block

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` passes: the committed block is
  byte-identical to what the generator produces.
- Every emitted number matches an independent `find`/`wc` re-derivation.
- Deliberately perturbing one digit in the committed block makes INV fail, and reverting restores
  it — the one-shot proof that the count is now gated rather than merely correct.

---

### Phase 5: Rebuild and Register the Directory Inventory [COMPLETED]

**Goal**: Fix D2 — a table naming four entries that no longer exist and omitting five that do,
including the largest subtree in the archive — and register it so it cannot silently drift again.

**Tasks**:
- [x] Enumerate the archive's real top-level shape and reconcile it against the table: remove or
      re-home the four rows ADR-005 moved under `Kamp/` (`KampBypassArchive`,
      `KampNegationClosure`, `RabinovichPath`, `VecEADecomposition`), and add the five missing
      subtrees (`Kamp/`, `BundleDeadHalf/`, `RetiredTactics/`, `SupersededCompleteness/`,
      `LimitMCSCoherenceDeadCases/`).
- [x] Choose the durable mechanism *(chose GENERATION: `rows=both cols=files-lines link=yes empty=include sort=lines-desc`, 40 rows, one hand-written trailing column)*, against the generator behavior Phase 2 established:
      **either** a `<!-- BEGIN GENERATED: inventory dir=FormalSystem/Boneyard rows=subdirs
      cols=files-lines link=yes -->` block (which requires collapsing the current six columns to
      one hand-written trailing column, since the generator preserves exactly one) **or** an
      `<!-- INVENTORY: hand-maintained (dir=FormalSystem/Boneyard) -->` registration, which keeps
      the richer column set and buys exhaustiveness checking without generated counts.
- [x] Hand-maintained registration NOT chosen, so `audit_hand_maintained`'s key shape does not apply, match `audit_hand_maintained`'s key shape: `want`
      is built from `basename(subdir) + "/"` for subdirs that contain `.lean` files, and phantom
      detection only flags keys ending in `.lean` or `/`. Confirm the tombstone rows land on the
      intended side of that boundary by running the checker, not by reasoning about it.
- [x] Fix the total row *(removed it: the totals are generated once, in §One Archive)* (currently 93 files / 58,738 lines) so it agrees with §One Archive, or
      remove it in favor of the generated counts block from Phase 4 — one number, one owner.
- [x] Add a per-subtree inventory to `FormalSystem/Boneyard/Kamp/README.md` so the archive's
      largest component (47.6% of its lines) is not a single opaque row, using the same mechanism
      chosen above.

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The archive is asserted to have 39 top-level subdirectories plus one loose
`.lean` file; the research report says 38 directories plus one loose file, and `ls
FormalSystem/Boneyard` returns 41 entries (directories, plus `README.md`, plus
`VacuousKEquiv.lean`). Resolve this discrepancy by direct enumeration before writing any row, and
re-check after Phase 3's possible move of the loose file. *(RESOLVED by direct enumeration: 39
subdirectories + `VacuousKEquiv.lean` + `README.md` = 41 `ls` entries, so the plan's figure is
right and the research report's 38 is wrong. Phase 3 did not move the loose file. The generated
table carries 40 rows, verified row-by-row against `os.listdir` for both directions.)* Also asserted: 24 of 39 subtrees have a
§Subdirectory Details entry and 16 of 39 are classified by the taxonomy — confirm both counts in
Phase 8 rather than carrying them forward untested. *(CONFIRMED mechanically in Phase 7: 24/39
had a detail entry, 16/39 were classified. Both are now 39/39, plus the root-level file in the
taxonomy, verified by name-by-name grep in both directions.)*

**Files to modify**:
- `FormalSystem/Boneyard/README.md` - §Directory Inventory rebuilt and registered
- `FormalSystem/Boneyard/Kamp/README.md` - per-subtree inventory for the largest subtree

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` passes; the INV line reports
  both "every generated inventory block is current" and "every hand-maintained one is exhaustive".
- Every top-level entry returned by `ls FormalSystem/Boneyard` has exactly one row, and every row
  names something that exists.
- The inventory's file/line totals agree with §One Archive's generated counts.

---

### Phase 6: Re-Key Provenance to Durable Anchors [COMPLETED]

**Goal**: Fix D4 — replace provenance keyed to repository-internal task numbers with anchors an
external reader of a published formalization can actually follow.

**Tasks**:
- [x] Recover a commit SHA for each archival event, following renames
      (`git log --follow --diff-filter=A -- <path>`, `git log --diff-filter=R`), and pair each SHA
      with the date already present in the §Task Cross-References `When` column.
- [x] Rewrite §Task Cross-References as a provenance table *(retitled "Provenance: When Each Subtree Was Archived"; grew from 19 rows to 37, one per archival event, covering all 40 top-level entries)* keyed on date + short SHA, with the
      "What It Archived" text preserved verbatim. Retitle the section accordingly — "Task
      Cross-References" is itself the internal framing being retired.
- [x] Drop the `Task` column in §Directory Inventory *(dropped in Phase 5: generation preserves exactly one hand-written trailing column)* (Phase 5's structure decides which);
      if the mechanism chosen there is generation, this column must be folded into the single
      hand-written trailing column or dropped.
- [x] Sweep the top-level README for the remaining C9-shaped citations and clear them.
- [x] Measure whether C9's `/Boneyard/` exclusion can now be narrowed *(measured: 88 occurrences across 33 files remain after clearing this README's two. Recorded the exclusion and its reason in the README rather than tightening C9 into a red gate; `scripts/check-module-invariants.sh` NOT modified in this phase.)* (for example, to `.md` files
      only, or dropped entirely). Then either tighten `scripts/check-module-invariants.sh`'s C9
      filter so this repair is gate-enforced, or record in the README why it stays excluded. Do not
      tighten C9 into a red gate.

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: §Task Cross-References is asserted to hold 19 rows, and the archive as a
whole to carry 90 C9-shaped task-number occurrences across 34 files, of which only 2 are in the
top-level README (which is why C9 passes today despite the `Task` column: bare integers in a table
cell do not match its `tasks?\s+#?[0-9]+` shape). Re-measure all three with the exact C9 regex
before deciding the scope of any C9 tightening — a naive tightening would pull in every archived
`.lean` docstring.

**Files to modify**:
- `FormalSystem/Boneyard/README.md` - §Task Cross-References re-keyed; `Task` column resolved
- `scripts/check-module-invariants.sh` - C9 filter *(NOT modified: the measurement did not support narrowing it)*

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED, with C9 green
  under whatever filter is in force at the end of the phase.
- Every SHA in the new table resolves: `git cat-file -e <sha>^{commit}` for each.
- The top-level README contains zero C9-regex matches.

---

### Phase 7: Complete the Taxonomy and Subdirectory Coverage [COMPLETED]

**Goal**: Make the archive's own narrative sections describe all of it, not a little over half —
this is the "cleaning up and improving documentation/comments" the user asked for.

**Tasks**:
- [x] Classify every top-level subtree *(a fifth category was genuinely needed and added: **Orphaned, Not Refuted** — correct code, often still compiling, retired only because nothing imported it. 11 of the 40 entries fall there and fit none of the original four.)* under §Archival Reason Taxonomy's four categories (Unsound
      Axioms / Semantics, Superseded Approaches, Structural Dead Ends, Architectural
      Incompatibility), adding a category only if a subtree genuinely fits none.
- [x] Add a §Subdirectory Details entry *(15 added; the section was rebuilt in alphabetical order so coverage is checkable by heading diff)* for each subtree that lacks one, drawing on that subtree's
      own README where it has one (including the six written in Phase 3).
- [x] Distinguish, for each subtree, which of the three research categories *(a second, independent `Provenance class` column — Superseded / Refuted / Orphaned-Unfinished — on the exhaustive 40-row classification table, kept deliberately orthogonal to the archival reason)* it belongs to —
      genuinely superseded, a refuted approach still cited elsewhere, or merely unfinished. This is
      the characterization task step 1 asked for, and it belongs in the archive's own README rather
      than only in a task report.
- [x] Cross-check the two named guard-first exceptions *(both intact and still linked from the CONVENTION WARNING; the guard-first fact is now also carried on their inventory rows and detail entries, and `LimitMCSCoherenceDeadCases/` is recorded as a third guard-first subtree)* (`BundleDeadHalf/`, `RetiredTactics/`)
      survive intact and are still reachable from the CONVENTION WARNING.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: 15 subtrees are asserted to lack a §Subdirectory Details entry and 23 to be
unclassified by the taxonomy. Derive both lists mechanically at implementation time by diffing the
`### ` headings under §Subdirectory Details, and the names appearing under §Archival Reason
Taxonomy, against the enumerated top-level directory list from Phase 5.

**Files to modify**:
- `FormalSystem/Boneyard/README.md` - §Archival Reason Taxonomy, §Subdirectory Details

**Verification**:
- Every top-level subtree name appears at least once under §Archival Reason Taxonomy and once
  under §Subdirectory Details; verified by a name-by-name grep, not by eye.
- `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED (C5 covers the new
  intra-document anchors and relative links).
- Every changed hunk is prose or a markdown table; no code or count is edited by hand in this
  phase.

---

### Phase 8: Publication-Facing Framing [COMPLETED]

**Goal**: Give a reader who has never seen this repository the two paragraphs that turn 91,539
archived lines from a red flag into evidence of a governed quarantine.

**Tasks**:
- [x] Add an opening framing section at the top of `FormalSystem/Boneyard/README.md`, before the
      CONVENTION WARNING, stating: what the archive is; that it is not built and no `.olean` is
      produced under any `Boneyard` path; that it carries every `sorry` in the tree **by design**
      while the live tree's structural sorry count is zero; that both facts are machine-checked
      (C1, C3, B0, C11) rather than asserted; and why it ships — retired-attempt provenance is
      evidence of what was tried and why it failed.
- [x] Promote and rewrite §When to Consult the Boneyard *(retitled "When to Consult the Archive"; now points at the classification table's Refuted class and at the paper's own citation)* for an external reader, since it is already
      close to the needed framing.
- [x] Link the framing to ADR-009 (the disposition decision) and ADR-005 (the single-archive
      invariant), so the "why does this ship" question has a documented answer one click away.
- [x] Give `FormalSystem/README.md`'s Boneyard row *(the row was rewritten in Phase 9, which landed first as the plan directed; Phase 8 left it alone and edited the top-level `README.md` tree comment instead)* and the top-level `README.md`, if it mentions
      the archive, a one-line framing consistent with the above — pointing at the archive README
      rather than restating any number.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: prose

**Commit Mode**: per-substep

**Files to modify**:
- `FormalSystem/Boneyard/README.md` - new framing section; §When to Consult the Boneyard rewritten
- `FormalSystem/README.md` - Boneyard row framing (coordinate with Phase 9, which owns the count
  in that same row; if both phases would touch line 312, Phase 9 lands first and Phase 8 edits
  only the prose it leaves behind)

**Verification**:
- The framing paragraph states no number that is not either generated (Phase 4) or a named check
  ID; a reader can verify every claim in it by running one named command.
- `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED.
- Diff read-through confirms every hunk is prose; no table row, count, or code line is altered.

---

### Phase 9: Retire the Duplicate Counts and the Stale Two-Archive Docstring [COMPLETED]

**Goal**: Fix D1's second instance and D3 — the two live-tree files that state wrong facts about
the archive, one of which is the first file a reviewer opens.

**Tasks**:
- [x] Replace `FormalSystem/README.md:312`'s "ARCHIVE — 156 archived `.lean` files, excluded from
      the live build" with a description carrying **no number**, pointing to
      `Boneyard/README.md` as the single source. This restores ADR-005 decision 4, which the
      duplicate figure already violates.
- [x] Correct `FormalSystem/FormalSystem.lean`'s module docstring (the `FormalSystem.Metalogic`
      bullet and the two sentences following it): drop "the two-Boneyard counting caveat", "Both
      Boneyard trees", and "either tree"; restate in the single-archive present tense and cite
      ADR-005. Keep the substantive claim that archived identifiers predate the Mathlib naming
      migration and were deliberately left untouched.
- [x] Correct the same docstring's stale "(210 live files)" *(took the remove-the-parenthetical option: it points at `Metalogic/README.md` instead, since no gate owns that number)* for `FormalSystem.Metalogic` — the
      measured live count is 348 — or remove the parenthetical entirely and point at
      `Metalogic/README.md`, which is the better fix since no gate owns this number.
- [x] Sweep for any other hand-typed archive count outside `Boneyard/README.md` and retire it the
      same way.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: Exactly two hand-typed archive counts are asserted to exist outside the
archive README (`FormalSystem/README.md:312` and `FormalSystem.lean`'s "210 live files"), and the
live `Metalogic` file count is asserted to be 348 against a documented 210. Confirm the sweep with
a repo-wide grep for archive-count-shaped strings (excluding `.git`, `.lake`, `specs`, `.claude`)
and re-derive 348 with `find FormalSystem/Metalogic -name '*.lean' -not -path '*/Boneyard/*' | wc -l`
before editing.

**Files to modify**:
- `FormalSystem/README.md` - line ~312, the Boneyard row's hand-typed count
- `FormalSystem/FormalSystem.lean` - module docstring: two-archive language and stale live count

**Verification**:
- `lake build` is green — `FormalSystem.lean` is the library's top-level aggregator, so a malformed
  docstring is a build-visible defect, and this is why the tier is `local` rather than `prose`.
- `bash scripts/check-module-invariants.sh --no-build` reports ALL CHECKS PASSED, with C5 green
  over the docstring's module-shaped path references.
- A repo-wide grep for the retired figures (156, 163, 90,797, 210) returns no hit outside `specs/`
  and the git history.

---

### Phase 10: Final Gate, Census Re-Verification, and Task Summary [COMPLETED]

**Goal**: Prove the headline properties survived intact, and close the task with the evidence a
reviewer would ask for.

**Tasks**:
- [x] Run the full gate: `lake build` (green, default target) and
      `bash scripts/check-module-invariants.sh` (ALL CHECKS PASSED, including B0, C1, C3, C5, C7,
      C9, C11, C20 and INV).
- [x] Re-run the live sorry census with the exact C3 regex over `Metalogic`, `Syntax`, `Semantics`,
      `ProofSystem`, `Theorems` and `Automation`, excluding `Boneyard`: it must still be **0**.
- [x] Re-run the `.olean` census *(Boneyard 0 as at baseline; total 547 vs baseline 546 — the +1 is a live module from concurrent work, not this task, which added no live module)*: `find .lake -path '*Boneyard*' -name '*.olean' | wc -l` is 0, and
      the total `.olean` count is unchanged from the Phase 1 baseline.
- [x] Run the adjacent lints *(`readme-lint.sh`, `typst-status-counts.sh`, `check-copyright-headers.sh` pass; `typst-sync-check.sh` fails on 4 PRE-EXISTING violations left by the `RetiredTactics/` archival in `1ff119610`, a different task — same citations present before this task's first commit, and this task never touched `typst/`. `typst/generated/status.typ` was regenerated during the check and restored to HEAD, since its diff carried another task's declaration renames.)* the archive participates in: `bash scripts/readme-lint.sh`,
      `bash scripts/typst-sync-check.sh`, `bash scripts/typst-status-counts.sh`, and
      `bash scripts/check-copyright-headers.sh`; confirm the generated `typst/generated/status.typ`
      archive row is unchanged or regenerated consistently.
- [x] Confirm the archive is intact as a body of work: `git diff --stat` shows no
      archived `.lean` file deleted, and the file/line census matches Phase 1's baseline modulo
      any Phase 3 `#exit` additions and the loose-file move.
- [x] Write the execution summary at
      `specs/551_boneyard_disposition_for_publication/summaries/01_boneyard-keep-and-document-summary.md`,
      recording the disposition (KEEP), the four defects closed, the generator change that
      prevents recurrence, and the before/after census.

**Timing**: 1 hour

**Depends on**: 8, 9

**Verification Tier**: full

**Commit Mode**: per-substep

**Files to modify**:
- `specs/551_boneyard_disposition_for_publication/summaries/01_boneyard-keep-and-document-summary.md` - new

**Verification**:
- `lake build` green and `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED.
- Live structural sorry census: 0. Boneyard `.olean` count: 0. Both re-derived, not quoted.
- Zero archived `.lean` files deleted across the whole task's diff.

## Lean Challenge Statements

This plan commits to **no** new Lean declarations: it changes documentation, module docstrings,
and one gate script, and proves nothing. The identifier set declared by this section is therefore
empty, which matches the empty set of identifier-shaped bullets under `- **Goals**:` above — the
equality this section's contract requires. No ```lean fenced block is emitted, because emitting an
empty or placeholder declaration would assert a commitment the plan does not make. The section is
present because `plan-format.md` gates it on `task_type: lean4`, which this task carries.

## Testing & Validation

- [x] `lake build` green on the default target, before and after.
- [x] `bash scripts/check-module-invariants.sh` reports ALL CHECKS PASSED (full run, with build).
- [x] `bash scripts/check-module-invariants.sh --emit-inventory --check` passes — every generated
      block current, every hand-maintained one exhaustive.
- [x] B0 still asserts exactly 1 archive directory and a non-zero exclusion count.
- [x] C3 live structural sorry census: 0, re-derived with the exact regex.
- [x] C11 still resolves every archived import line (536 at baseline, 7 waived).
- [x] `find .lake -path '*Boneyard*' -name '*.olean' | wc -l` returns 0.
- [x] C5 green over every new or changed markdown link and module-shaped path.
- [x] C9 green under whatever filter Phase 6 leaves in force.
- [x] `bash scripts/readme-lint.sh`, `typst-status-counts.sh` and `check-copyright-headers.sh`
      all pass. `typst-sync-check.sh` does NOT pass — 4 violations in
      `typst/chapters/p4-proof-automation.typ` (`AesopRules.lean`,
      `Automation/Tactics/Helpers.lean`, `Tactics/Helpers.lean`, `tm_auto 5`), all PRE-EXISTING:
      they were left by the `RetiredTactics/` archival in commit `1ff119610`, a different task,
      were present before this task's first commit, and this task never touched `typst/`.
      Recorded as a follow-up rather than repaired here.
- [x] No archived `.lean` file deleted: `git diff --stat` over the whole task shows zero deletions
      under `FormalSystem/Boneyard/`.
- [x] Every count published about the archive is either generated by the gate or is a named check
      ID; no hand-typed archive figure survives outside `specs/`.

## Artifacts & Outputs

- `docs/architecture/ADR-009-Boneyard-Retention.md` - the KEEP disposition decision record
- `docs/architecture/README.md` - ADR index entry
- `FormalSystem/Boneyard/README.md` - generated counts block, rebuilt and registered Directory
  Inventory, re-keyed provenance, completed taxonomy and subdirectory details, publication-facing
  framing, resolved `#exit` and file-structure policy
- `FormalSystem/Boneyard/Kamp/README.md` - per-subtree inventory for the archive's largest component
- Six new subtree READMEs under `FormalSystem/Boneyard/`
- `FormalSystem/README.md` - hand-typed archive count retired
- `FormalSystem/FormalSystem.lean` - single-archive docstring, stale live count corrected
- `scripts/check-module-invariants.sh` - archive-aware inventory generator
- Up to 12 archived `.lean` files - `#exit` guards, only if Phase 3 chooses the mandatory policy
- `specs/551_boneyard_disposition_for_publication/summaries/01_boneyard-keep-and-document-summary.md`

## Rollback/Contingency

Every phase is a commit, so rollback is `git revert` of the offending phase commit; nothing in
this plan deletes content, so no rollback needs to restore a file from history.

- **If Phase 2 cannot be made a no-op** (the generator change moves a byte of existing output),
  stop and revert that phase rather than accepting the diff: the whole value of the change is that
  it adds capability without touching current counts. Fall back to registering the §Directory
  Inventory as hand-maintained (which needs no generator change) and repairing §One Archive's
  counts by hand with a `<!-- verified: {date} -->` note, accepting that D1 is then fixed but not
  gated, and record that concession in ADR-009.
- **If tightening C9 in Phase 6 turns the gate red**, leave the `/Boneyard/` exclusion in place and
  record the measured occurrence count and the reason in the README. A red gate is a worse
  publication state than a documented exclusion.
- **If the loose-file move in Phase 3 breaks C5 or C11**, revert to amending §Expected File
  Structure instead; the file's location is cosmetic and the gates are not.
- **If the task must be abandoned mid-flight**, the ADR from Phase 1 is the one artifact that must
  land regardless: it is what converts "shipped undecided" into "shipped decided", which is the
  failure mode the task exists to prevent.
