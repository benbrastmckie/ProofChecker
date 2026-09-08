# Research Report: Boneyard Disposition for Publication

**Task**: 551 - Boneyard disposition for publication
**Started**: 2026-09-07T00:00:00Z
**Completed**: 2026-09-07T00:00:00Z
**Effort**: Medium
**Dependencies**: None
**Sources/Inputs**: - Codebase measurement (`find`/`grep`/`git`), `scripts/check-module-invariants.sh --no-build` (full green run), `FormalSystem/Boneyard/README.md`, `FormalSystem/README.md`, `FormalSystem/FormalSystem.lean`, `docs/architecture/ADR-005-Single-Boneyard.md`, `typst/SYNC-MAP.md`, `latex/subfiles/04-Metalogic.tex`, `.claude/scripts/audit-deletion-references.sh`
**Artifacts**: - specs/551_boneyard_disposition_for_publication/reports/01_boneyard-disposition-recommendation.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Recommendation: KEEP, with a documentation-integrity repair.** Not "keep as-is" — the tree
  itself is sound and well-governed, but the documentation that *describes* it has drifted badly
  and is the actual publication liability.
- **CUT ENTIRELY is not available.** 96 files outside the archive cite it, including 46 live
  `.lean` files, the LaTeX paper (`latex/subfiles/04-Metalogic.tex:389` explicitly tells the
  reader the approach "is archived in `Boneyard/` for historical reference"), the Typst
  build, a test file, and 8 scripts. Cutting would break a published cross-reference and
  invalidate an accepted ADR.
- **SPLIT buys almost nothing.** Only 8 of 39 subtrees have zero path-shaped external citation,
  and together they are ~1,900 lines — 2% of the archive. The size argument is carried almost
  entirely by `Kamp/` (43,551 lines, 47.6%), which is the single most heavily cited subtree
  (22 external citing files).
- **The quarantine demonstrably works.** Live structural `sorry` count is **0**; a full build
  produces **546** `.olean` files and **zero** under any `Boneyard` path; check `C11` verifies
  all 536 archived import lines resolve; `B0` asserts exactly one archive directory.
- **Four concrete documentation defects** (detailed below) ship today and would embarrass a
  reviewer: stale counts in three disagreeing places, a directory inventory naming four
  subtrees that no longer exist and omitting five that do, a contradiction between
  `FormalSystem.lean` and the ADR accepted the same day, and provenance keyed to internal task
  numbers meaningless to any external reader.
- **Root cause is mechanical and fixable:** `scripts/check-module-invariants.sh:173` prunes
  `Boneyard` from the inventory generator's markdown walk, so the archive README is the one
  README in the tree whose counts are hand-typed and ungated.

## Context & Scope

The task asks for a reasoned disposition of `FormalSystem/Boneyard/` ahead of publication, with
steps 1-3 strictly read-only. Nothing was deleted, moved, or edited. All figures below were
re-measured against the working tree rather than copied from documentation, precisely because
the documentation turns out to be the unreliable part.

Two premises carried in the task description were checked and found **stale**, and this matters
because they were offered as the starting point:

1. *"The two Boneyard trees are already distinguished ... (there is a documented two-Boneyard
   counting caveat)"*. There is now exactly **one** archive.
   `docs/architecture/ADR-005-Single-Boneyard.md` (Status: **Accepted**, 2026-09-07) consolidated
   the second archive from `FormalSystem/Metalogic/WeakCanonical/Kamp/Boneyard/` into
   `FormalSystem/Boneyard/Kamp/KampWeakCanonical/`. Check `B0` now asserts the count is exactly 1
   and passes. The two-Boneyard caveat still surviving in `FormalSystem/FormalSystem.lean` is a
   defect, not a starting point (see Findings).
2. *"`scripts/audit-deletion-references.sh` exists for this"*. It does **not** exist at that
   path. It exists at `.claude/scripts/audit-deletion-references.sh`, and its own header scopes
   it to agent-system artifacts under `agent-system/extensions` — it is not the right instrument
   for a Lean subtree. Its *method* (literal grep, wildcard grep, reachability) was applied
   manually instead; the repo's own `check-module-invariants.sh` (C11/C12/C13/C20) is the
   correct native instrument and already covers the archive.

## Findings

### Measured Facts (re-derived, not quoted)

| Quantity | Measured | Documented as | Where documented |
|---|---:|---:|---|
| Archived `.lean` files | **168** | 163 / 156 | `Boneyard/README.md` §Counts / `FormalSystem/README.md:312` |
| Archived lines | **91,539** | 90,797 | `Boneyard/README.md` §Counts |
| Top-level archive subdirectories | **39** (38 dirs + 1 loose `.lean`) | 37 | `Boneyard/README.md` §Counts |
| Directory-inventory table total | — | 93 files / 58,738 lines | `Boneyard/README.md` §Directory Inventory |
| Live `.lean` files (Boneyard excluded) | **478** | — | — |
| Live lines | **282,014** | — | — |
| Archive share of `FormalSystem/` lines | **24.5%** | "doubles the apparent size" | task description |
| Live structural `sorry` (C3 regex) | **0** | 0 | C3, passing |
| Archived structural `sorry` | **108 occurrences in 41 files** | 39 files | task description |
| `.olean` files built | 546, of which **0** under `Boneyard` | inert | `Boneyard/README.md` |
| Archived files carrying `#exit` | **156 of 168** | "never compiled" policy | §Build Policy |
| Archived import lines resolving | **536 (7 waived)** | — | C11, passing |

The "doubles the apparent size" framing overstates the cost by a factor of two: the archive is a
quarter of `FormalSystem/`, not half of it.

### Composition and Concentration

| Subtree | lines | files | note |
|---|---:|---:|---|
| `Kamp/` | 43,551 | 85 | 47.6% of the archive; holds the consolidated former nested archive (`KampWeakCanonical/`) plus `KampBypassArchive/`, `KampNegationClosure/`, `RabinovichPath/`, `VecEADecomposition/` |
| `StrictSemanticsLegacy/` | 14,392 | 9 | architectural incompatibility (open-guard migration) |
| `StaviDiscretePath/` | 4,981 | 4 | EF-game pipeline, no live consumers |
| `ChainCompleteness/` | 4,265 | 12 | superseded by SuccChain |
| `SorriedDeclExcisions/` | 3,351 | 6 | verified-dead sorry closures |
| next 25 subtrees | ~18,900 | 52 | — |
| 9 tombstones (README only) | 0 | 0 | `BundleTemporalCoherence`, `BX1DependentCode`, `ClosedGuardLegacy`, `NonBurgessSeed`, `OpenGuardInvalid`, `StageInductionGapAnalysis`, `TAxiomDependentCode`, `UltrafilterDeadCode`, `XuLemma321Legacy` |

Two subtrees (`Kamp/` + `StrictSemanticsLegacy/`) are 63% of the archive. Any size-driven
argument is really an argument about those two, and both are among the most heavily cited.

### Live-Reference Audit (the gate on any removal)

Path-shaped citations of the form `Boneyard/<subtree>`, counted outside the archive and outside
`specs/`:

- **96 files** in the repository cite `Boneyard` at all.
- **46 live `.lean` files** cite it in docstrings — including `Metalogic.lean`,
  `Metalogic/WeakCanonical.lean`, `Metalogic/Bundle.lean`, `ProofSystem/Axioms.lean`,
  `Theorems/TemporalDerived.lean`, `Automation/Normalization.lean`, and
  `Tests/BimodalTest/Automation/TacticsTest.lean`.
- **The publication surface cites it.** `latex/subfiles/04-Metalogic.tex:389`: *"archived in
  `Boneyard/` for historical reference; it is not one of the three current developments above,
  and its archival is a matter of historical record rather than a claim that the live routes
  supersede it in spirit."* `typst/generated/status.typ:29` carries a generated row
  `("WeakCanonical/ (archived, Boneyard/Kamp/)", 4)`.
- **8 scripts** depend on it structurally: `check-module-invariants.sh`, `lib/live_walk.py`,
  `boneyard-import-waivers.txt`, `check-metalogic-cycles.sh`, `readme-lint.sh`,
  `typst-sync-check.sh`, `typst-status-counts.sh`, `check-copyright-headers.sh`.

Subtrees with **zero** path-shaped external citation (the only removal candidates):
`UltrafilterDeadCode` (0 lines, tombstone), `RestrictedMCSDeferral` (772),
`NonBurgessSeed` (0, tombstone), `MergedBracketQuarantine` (1,036), `DiscreteXY` (0, tombstone),
`DeadCanonicalModel` (0 by path, but 3 by name), `BXCanonicalQuasimodel` (166),
`BX1DependentCode` (0, tombstone). Excluding tombstones (which are pure README and cost nothing),
this is **~1,974 lines, 2.2% of the archive**. `MergedBracketQuarantine`'s own README records a
*refuted* route (violates the no-nesting audit and Rabinovich Lemma 5.1) — exactly the negative
knowledge with standalone scholarly value, so cutting it is the worst trade in the set.

### Documentation Defects Shipping Today

**D1 — Three disagreeing archive counts, in violation of the tree's own ADR.**
ADR-005 decision 4 states the archive's counts are stated "in exactly one place",
`FormalSystem/Boneyard/README.md`. In fact: `Boneyard/README.md` says 163 files / 90,797 lines /
37 subdirs; `FormalSystem/README.md:312` independently says "156 archived `.lean` files"; the
`Boneyard/README.md` §Directory Inventory total row says 93 files / 58,738 lines. The measured
truth is 168 / 91,539 / 39. All three published figures are wrong, and the ADR's
single-source rule is already broken by the second one.

**D2 — The Directory Inventory table describes a tree that no longer exists.**
It lists four top-level entries that ADR-005 moved under `Kamp/`: `KampBypassArchive`,
`KampNegationClosure`, `RabinovichPath`, `VecEADecomposition`. It omits five subtrees that do
exist: `Kamp/` (the largest, 47.6% of the archive), `BundleDeadHalf/`, `RetiredTactics/`,
`SupersededCompleteness/`, `LimitMCSCoherenceDeadCases/`. §Subdirectory Details covers 24 of 39
entries; the §Archival Reason Taxonomy classifies only 16 of 39.

**D3 — `FormalSystem/FormalSystem.lean` contradicts the ADR accepted the same day.**
Lines 45-49 still read "the two-Boneyard counting caveat. **Both Boneyard trees** are excluded
..." and "See `Boneyard/README.md` before grepping **either tree**". ADR-005 makes this false.
This is a module docstring in the library's top-level aggregator — the first file a reviewer
opens. (`typst/SYNC-MAP.md:22-24` describes the same two-archive history but correctly frames it
as past tense with the consolidation noted, so it is accurate.)

**D4 — Provenance is keyed to internal task numbers.**
`Boneyard/README.md` §Task Cross-References is a 19-row table whose primary key is a task number
(80, 83, 85, 93, ...), and the §Directory Inventory carries a `Task` column of the same. These
resolve only against `specs/`, which is repository-internal task-management state. To an external
reader of a published formalization they are opaque tokens. This also sits against the repo's own
`no-task-references-in-deliverables` rule; check `C9` passes only because its pattern matches
`task N`-shaped prose, not bare integers in a table cell. The durable anchors — dates and commit
SHAs — are already partly present (the `When` column) and `git log` supplies the rest.

**Secondary gaps** (lower severity): 6 subtrees lack the `README.md` that
§Expected File Structure requires — `BXCanonicalQuasimodel`, `DeadConvergenceProof`,
`FMPVariants`, `RestrictedMCSDeferral`, `SoundnessVariants`, `StaviDiscretePath`. 12 of 168
archived files lack the `#exit` guard that §Build Policy mandates, and they cluster in exactly
the four subtrees missing from the inventory table (`BundleDeadHalf` 6, `RetiredTactics` 4,
`LimitMCSCoherenceDeadCases` 1, `SupersededCompleteness` 1) — one consistent story: subtrees
archived after the last README refresh were never registered anywhere.
`VacuousKEquiv.lean` sits loose at the archive root, also contrary to §Expected File Structure.

### Root Cause of the Drift

Every live README's inventory is generated and gated: `INV` checks that each
`<!-- BEGIN GENERATED: inventory -->` block is current, and 14 READMEs carry one. The archive
README carries none, and cannot — `scripts/check-module-invariants.sh:173` prunes `Boneyard`
from `markdown_targets()`:

```python
dirs[:] = [d for d in dirs
           if d not in (".git", "specs", ".claude", ".lake", "node_modules", "Boneyard")]
```

so a block placed in `Boneyard/README.md` would be invisible to both the generator and the check.
This is why the one README in the tree describing 24.5% of it is also the only one whose numbers
are hand-typed. The generator already knows how to emit archive rows — `scan()` under
`rows=totals` emits `Archived `.lean` files` and `Archived lines` (lines ~221-228) — so the
capability exists; only the walk excludes the directory.

### External Resources

No Mathlib or `lean-lsp` search was required: this is a repository-organization and
documentation-integrity question, not a lemma-discovery one. The `lean-lsp` search tools
(`leansearch`, `loogle`, `leanfinder`, `state_search`, `hammer_premise`) were deliberately not
invoked — there is no proof goal in scope, and calling them would have produced noise rather
than evidence. Verification was done with the repository's own gate,
`scripts/check-module-invariants.sh --no-build`, which ran to **ALL CHECKS PASSED**.

### Recommendations

**Recommend KEEP, paired with a documentation-integrity repair.** The three options as framed
map onto the evidence as follows:

- **CUT ENTIRELY — rejected.** It would break a citation in the published LaTeX
  (`04-Metalogic.tex:389`), orphan 46 live `.lean` docstrings, invalidate ADR-005 and its B0/C11
  gates, and delete the `boneyard-import-waivers.txt` record of what was deleted and why. The
  archive is fully git-tracked (217 files) and receives commits regularly — the eight most recent
  touching it span the last several implementation cycles — so it is a maintained artifact, not
  abandoned detritus. "History is preserved in git" understates the loss: what would be lost is
  the *curated* index over that history, which is the part with scholarly value.
- **SPLIT — rejected as not worth its cost.** The removable set is ~2% of the archive by lines,
  and its most substantial member (`MergedBracketQuarantine`) records a refuted route, which is
  the category the task itself identifies as most valuable to a subsequent researcher. Splitting
  also forfeits ADR-005's single-archive invariant that B0 currently enforces for free.
- **KEEP — recommended**, but explicitly *not* "as-is". The tree is sound; its description is
  not. Shipping D1-D4 unrepaired is the failure mode the task warns against ("what is not
  defensible is shipping it undecided and unexplained") — the archive is currently explained
  *incorrectly*, which is worse than unexplained.

Proposed repair, ordered by value-per-effort:

1. **Un-prune `Boneyard` from the inventory walk** (`check-module-invariants.sh:173`) and give
   `Boneyard/README.md` a generated counts block plus a generated per-subtree inventory. This
   converts D1 and D2 from recurring manual defects into gate-enforced invariants and prevents
   recurrence. Requires a Boneyard-aware variant of `live_subdirs`/`live_files`, since
   `lib/live_walk.py` excludes the archive by name glob by design.
2. **Delete the hand-typed count at `FormalSystem/README.md:312`**, replacing it with a link to
   the archive README, restoring ADR-005 decision 4.
3. **Correct `FormalSystem/FormalSystem.lean` lines 45-49** to the single-archive present tense,
   citing ADR-005.
4. **Re-key provenance to durable anchors.** Replace the `Task` column and §Task Cross-References
   table with date + commit SHA. This is the change that most directly serves an external
   reader.
5. **Add a publication-facing framing paragraph** at the top of `Boneyard/README.md` stating, for
   a reader who has never seen this repository: what the archive is, that it is not built, that
   it carries every `sorry` in the tree by design, that the live tree is sorry-free, and why it
   ships. §When to Consult the Boneyard is already close to this and can be promoted.
6. **Close the secondary gaps**: 6 missing subtree READMEs, 12 missing `#exit` guards, the loose
   `VacuousKEquiv.lean`, taxonomy coverage for the 23 unclassified subtrees, and §Subdirectory
   Details for the 15 missing entries.

Steps 1-4 are the publication-blocking set. Steps 5-6 are quality.

## Decisions

- **Do not delete anything.** Steps 1-3 of the task are read-only and were honored; nothing was
  moved, edited, or removed during this research.
- **Recommend against invoking task step 4** (execute the cut). The recommendation is KEEP, so
  the gated cut-execution step does not trigger.
- **Treat the task description's two premises as stale** and re-derive from the tree, rather than
  starting from them as instructed. Documented above with the contradicting evidence, because
  silently substituting different premises would have been worse than flagging them.
- **Do not use `.claude/scripts/audit-deletion-references.sh`** as the reference audit
  instrument; it is scoped to agent-system artifacts. Its three-pass method was applied manually
  and `check-module-invariants.sh` used as the native gate.
- **Classify by external citation rather than by the README's taxonomy**, because the taxonomy
  covers only 16 of 39 subtrees and is itself one of the defects found.

## Risks & Mitigations

- **Risk**: Repair step 1 changes a passing gate script; a mistake could turn `INV` or `B0` red.
  **Mitigation**: `B0` already asserts the archive-exclusion filter removes a non-zero count, so
  an accidental un-exclusion fails loudly rather than silently. Run the full
  `check-module-invariants.sh` (with build) before and after.
- **Risk**: Re-keying provenance to commit SHAs (step 4) loses the association if history is ever
  rewritten. **Mitigation**: pair each SHA with its date, which the existing `When` column already
  supplies; the pair is redundant enough to survive a rewrite.
- **Risk**: Correcting the counts is a one-shot fix that drifts again.
  **Mitigation**: this is exactly why step 1 (generator registration) is ordered first — steps 2
  and 4 are only durable once the numbers are generated.
- **Risk**: A reviewer still reads 91,539 archived lines as a red flag regardless of framing.
  **Mitigation**: the framing paragraph (step 5) should lead with the two verifiable facts that
  neutralize it — zero `.olean` files under any archive path out of 546 built, and zero
  structural `sorry` in the live tree, both machine-checked by `C1`/`C3`.
- **Risk**: `Kamp/` at 47.6% dominates the archive and its internal structure is undocumented at
  the top level. **Mitigation**: it has its own `README.md`; step 1's generated per-subtree
  inventory would surface its four sub-subtrees without hand-maintenance.

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task has no proof goal: it is a
  repository-organization and documentation-integrity decision. `lean_multi_attempt`,
  `lean_hammer_premise`, and the goal-directed search tools have no target here, and the
  APOLLO-style decomposition pattern does not apply.

## Context Extension Recommendations

- **Topic**: Archive/quarantine subtree governance in a Lean formalization intended for
  publication.
  **Gap**: Existing Lean context covers build repair, MCP tooling, and hard-mode contracts, but
  nothing covers how an archived-code tree should be documented, counted, and gate-enforced so
  that its description cannot drift from its contents.
  **Recommendation**: a short context file capturing the pattern this task surfaced — archive
  counts must be generated by the same instrument that generates live counts, or they will
  silently diverge; the inventory generator's directory-pruning list is the place that decision
  is made.
- **Topic**: Verifying task-description premises before building on them.
  **Gap**: The dispatch supplied two factual premises (two Boneyard trees; a script at a given
  path) that were both stale, and the instruction was to "start from those rather than
  re-deriving".
  **Recommendation**: strengthen the research-agent contract to require cheap verification of any
  factual premise a dispatch instructs the agent not to re-derive, and to report the
  contradiction explicitly rather than silently substituting.

## Appendix

### Commands used

```bash
find FormalSystem/Boneyard -name '*.lean' | wc -l                       # 168
find FormalSystem/Boneyard -name '*.lean' -exec cat {} + | wc -l        # 91,539
find FormalSystem -name '*.lean' -not -path '*/Boneyard/*' | wc -l      # 478
grep -rEn '(^[[:space:]]*sorry[[:space:]]*$)|(:=[[:space:]]*sorry[[:space:]]*$)|(\bexact sorry\b)|(<;> sorry)' \
     --include='*.lean' FormalSystem --exclude-dir=Boneyard | wc -l     # 0  (C3 regex)
find .lake -path '*Boneyard*' -name '*.olean' | wc -l                   # 0
find .lake/build -name '*.olean' | wc -l                                # 546
bash scripts/check-module-invariants.sh --no-build                      # ALL CHECKS PASSED
git ls-files FormalSystem/Boneyard | wc -l                              # 217
```

Per-subtree external-citation counts were produced by looping the 38 subtree basenames through
`grep -rl "Boneyard/$b" . --exclude-dir={.git,.lake,Boneyard,specs}`.

### References consulted

- `docs/architecture/ADR-005-Single-Boneyard.md` — the single-archive decision and its rationale
- `docs/architecture/ADR-006-Metalogic-No-Physical-Regroup.md` — cites the archive
- `FormalSystem/Boneyard/README.md` — 548 lines; the archive's own governance document
- `FormalSystem/README.md` §"Counting Live Files: Exclude the Archive"
- `FormalSystem/Metalogic/README.md` — the two-Boneyard counting caveat, now consolidated
- `scripts/check-module-invariants.sh` — B0, C3, C7, C9, C11, C12, C13, C20, INV
- `scripts/boneyard-import-waivers.txt` — the permanent record of unrepairable archived imports
- `typst/SYNC-MAP.md`, `typst/generated/status.typ`, `latex/subfiles/04-Metalogic.tex`
- `.claude/scripts/audit-deletion-references.sh` — method reference; scope checked and rejected
