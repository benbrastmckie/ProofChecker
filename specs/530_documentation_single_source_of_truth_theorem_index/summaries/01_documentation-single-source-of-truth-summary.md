# Implementation Summary: Task #530

- **Task**: 530 - Documentation single source of truth, theorem index, publication packaging
- **Status**: [COMPLETED]
- **Started**: 2026-09-07
- **Completed**: 2026-09-07
- **Effort**: one dispatch, 19 of 19 phases
- **Dependencies**: None (this task is itself a dependency of task 177)
- **Artifacts**: plans/01_documentation-single-source-of-truth.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Documentation status and counts are now machine-owned rather than hand-typed. Three owners
replace the six drifting hand-maintained authorities the review found: **C2/C14** own axiom sets
(105 pinned declarations, up from 56), a new **`check-module-invariants.sh --emit-inventory`**
owns every file and line count, and **`docs/theorem-index.md`** owns per-theorem status. Every
other surface carries a pointer and at most a five-row highlights table. Alongside that, history
and process prose is gone from publication-facing docstrings, a two-tier citation check exists
and is enforced, four rationale narratives moved to ADRs, and the publication packaging a paper
reader needs — `CITATION.cff`, `docs/ARCHITECTURE.md`, `references.bib`, a
`## Verifying the main theorems` section — is in place.

## What Changed

**New owners and the checks that keep them honest** (`scripts/check-module-invariants.sh`):
- `--emit-inventory` / `--emit-inventory --check`, plus the `INV` check in the main run. The
  hand-written **Description** column survives regeneration, keyed on file name; a new file gets
  a TODO marker, a vanished file's row is dropped. Marker options `dir=`, `rows=`, `filter=`,
  `cols=`, `desc=`, `link=`, `sort=` cover the four table shapes the tree actually has.
- A companion `<!-- INVENTORY: hand-maintained (dir=…) -->` marker for a table deliberately not
  generated (`Semantics/README.md`, ordered by layering). Registration buys exemption from
  generation, never from checking: `INV` asserts such a table is exhaustive.
- `scripts/lib/live_walk.py` — the Boneyard-excluding walk, extracted and shared by the C4-C11
  graph checks and the generator, so the inventories and C7's rollup cannot disagree.
- `C14_BASELINE` grew from 52 to 99 rows; with C2's four that is **105 pinned declarations**.
  Every subject of a SORRY-FREE claim in `Metalogic.lean` is pinned — the docstring-minus-pinned
  difference is empty and asserted.
- **C15 second assertion**: every `docs/theorem-index.md` row's declaration carries its anchor,
  or the literal `Paper: —` plus a reason, in its own `/--` block, and its File cell is an
  existing path with no line number. Structurally independent of the anchor-resolution half.
- **C20**, new, two tiers: tier 1 gates any `file.lean:NNN` citation whose target line is out of
  range or blank, repo-wide; tier 2 gates any such citation at all in publication-facing scope,
  now with `ENFORCE_C20=1` **on by default**. `WeakCanonical/**` is exempt from tier 2 only.
- **C9/C9D** widened to match `specs/<number>_<slug>/` paths, which the old `task N` shape could
  not see.
- **C18** widened with a sentence-level shingle pass (15-word floor) beside the paragraph pass.

**New documents**: `docs/theorem-index.md` (52 rows, 13 sections, fully-qualified names, a
generated Axioms column, a Notation-and-naming table), `docs/ARCHITECTURE.md`, `CITATION.cff`,
`references.bib`, four ADRs (`ADR-005-Single-Boneyard`, `ADR-006-Metalogic-No-Physical-Regroup`,
`ADR-007-Decidability-One-Directional`, `ADR-008-FrameClass-Validity-Seam`), and five missing
directory READMEs (`ForMathlib/Order/`, `Metalogic/Conservativity/`,
`Metalogic/Conservativity/Star/`, `Semantics/Frames/`, `Semantics/Ultraproduct/`).

**Lean files** — doc comments only, plus one import:
- `Metalogic.lean` — the 34-line Module Structure census deleted; the two-Boneyards claim, the
  Kamp-Boneyard claim and a dangling edit fragment gone; the ledger copy replaced by a pointer.
- 52 flagship declarations across 22 files gained a one-line `Paper:` anchor (16 real anchors,
  36 `Paper: — (reason)`).
- `Semantics/Validity.lean` 999 → 944 lines, `Metalogic/StrongCompleteness.lean` 1,141 → 1,127,
  `Metalogic/SetConsequence.lean` 626 → 616, `Semantics/FrameClassValidity.lean` 199 → 191,
  archaeology **zero** in all four.
- `Semantics.lean`'s frame table now names the four `def:frame` axioms with Nullity derived; the
  truth-clause table shows the real four-argument `TruthAt`, `σ.IsTotal` for `□`, the real
  `untl`/`snce` clauses in place of non-existent `H`/`G` ones, and a `#check` that compiles.
- `Soundness.lean`'s `Set.univ` claim, `Truth.lean`'s dangling pointer,
  `FrameClassVariants.lean`'s "3 `temporal_duality` sorries", and `AesopRules.lean`'s "pending
  soundness proofs" all corrected.
- `SoundnessLemmas.lean` imports and lists `DiscreteOrder`.
- 52 files gained a `## Tags` line.

**Citations**: 116 provably-wrong citations fixed, 24 range artifacts repaired, 17 ephemeral
`specs/` citations rewritten to durable anchors, 161 publication-scope citations and 66 bare
orphan line references cleared.

**typst**: `scripts/typst-status-counts.sh` reads the five flagship axiom sets out of the built
library and emits `axiom-report-table`; `FormalFoundations.typ`'s hand table is a `#for` over it
and its provenance line reads the generated stamp. The `sorry-table` WeakCanonical row is split
into live and archived halves.

## Decisions

- **The citation fix is to strip the line number, not to synthesise a declaration name.**
  Automated name resolution was implemented, measured, and abandoned: it duplicates names the
  prose already gives, cannot tell backtick context, and guesses whenever the cited line sits in
  a module docstring. Naming is editorial; stripping is mechanical and never wrong.
- **`docs/architecture/ADR-NNN` is the one ADR convention**; `docs/decisions/` was not created,
  and `docs/architecture/README.md` now says so, because a task whose purpose is removing
  duplicate authorities must not create a second one.
- **`decide` and `Conservativity.TMFrag` are pinned** though they are `def`s: `Metalogic.lean`
  makes SORRY-FREE claims about them, and pinning is what makes such a claim machine-checked.
- **`Conservativity.lean` was not halved**, by design — its comment share is the CEB/CEF/CED/CEC
  record. Only its duplicated per-theorem enumerations were removed.
- **`Last verified` stamps were refreshed but flagged**: they are hand-maintained metadata of
  the kind this task exists to remove, and `readme-lint.sh` reports rather than gates them.

## Plan Deviations

- **Phase 1** altered: the Boneyard walk was extracted to `scripts/lib/live_walk.py` and shared,
  rather than the new mode calling into C7's heredoc; the marker grew six options because the
  pilot target's five tables have four distinct shapes.
- **Phase 2** altered: `README.md` has no per-file table, so a `rows=totals` mode was added;
  `Semantics/README.md` was registered hand-maintained with a new exhaustiveness assertion.
- **Phase 4** altered: the unpinned set was **47**, not 35 — the tree renamed Discrete/Dedekind
  to `ZTime`/`RTime` after the research, and carries declarations the report predates.
- **Phase 5** altered: the seed grew to 52 rows; two flagship declarations were pinned rather
  than recorded as `claimed`, so no row reads `claimed`.
- **Phase 6** skipped one item: `BXCanonical.completeness` *does* have a doc comment. The
  research measured the quoted copy inside a ```lean fence in the module docstring; the inserter
  was made comment-aware.
- **Phases 11 and 12** altered: prose fell 6% and 1-2%, not 50%. Archaeology is at zero and the
  register is corrected, but the remainder is register-(a) content and cutting to half would
  have deleted mathematical claims, which the phases' own acceptance forbids. Verified
  mechanically: no backticked identifier or paper anchor was lost.
- **Phase 7**: the plan's premise that C15 was red is stale — the three anchors carry
  LIVE-UNPINNED rows, both halves are green, and the corresponding non-goal and risk R2 are moot.
- **Phase 10** altered: see the naming decision above.
- **Phase 13** altered: ADR filenames follow the existing `ADR-NNN-Title-With-Hyphens.md`
  capitalisation, not the plan's lower-case slugs.
- **Phase 14** altered: the sentence pass sees only one of the two duplicates the research named;
  the other is below the shingle's resolution and was removed by inspection.
- **Phase 15** altered: **42** `Bimodal.*` references, not 26, rewritten to `FormalSystem.*` —
  which additionally brings them inside C5's scope, where a `Bimodal.*` path was invisible.
- **Phase 16** altered: 29 stamps refreshed and 18 added across 52 READMEs, not 9 and 7 across 47.
- **Phase 17** altered: the axiom report covers the five declarations the chapter displays, not
  all 105; a 105-row table is not a chapter figure.
- **Phase 18** altered: the ProofChecker/BimodalLogic name split was **removed** rather than
  explained — "ProofChecker" survived only as a stale BibTeX key and title.
- **Phase 19** altered: **52** targets, not the estimated ~30, derived rather than assumed.

## Verification

- Build: **Success** — `lake build` completes 2,591 jobs, including the added `DiscreteOrder`
  import in `SoundnessLemmas.lean`.
- Sorry count: **0** live structural sorries (comment-stripped, Boneyard excluded); C3 asserts it
  by content and passes.
- Vacuous count: **0** introduced. One pre-existing pattern match,
  `Examples/TemporalStructures.lean`'s `int_domain_universal ... := trivial`, is a correct proof —
  `intTimeHistory.domain` is `fun _ => True` by construction — and predates this task.
- Axiom count: **0** real `axiom` declarations in live Lean code, unchanged. (A repo-wide
  `grep '^axiom '` reports 8 lines; all are prose inside docstrings that happen to wrap onto a
  line starting with the word. The count moved 7 → 8 purely from a prose re-wrap.)
- `bash scripts/check-module-invariants.sh` — every check green, including C1, C2, C3, C14 (105
  pinned declarations), both C15 halves, C16, C18 at both granularities, C20 tier 1 and tier 2
  under `ENFORCE_C20=1`, and `INV`.
- `bash scripts/readme-lint.sh` — **exits 0**.
- `bash scripts/typst-sync-check.sh` — passes all three checks; the typst document compiles.
- `bash scripts/check-metalogic-cycles.sh` — still exactly one directory-level cycle.
- C19 docstring coverage 92.34%, unchanged from dispatch start, well above the 90% floor.
- Archaeology grep returns **zero** on live surfaces; `Bimodal.[A-Z]` returns zero outside
  `specs/**`; all 52 theorem-index names resolve to the stated file with no line numbers.
- The README's `#print axioms` snippet was extracted verbatim and run: it produces exactly the
  output the section documents.
- Files verified: Yes.

## Impacts

- A stale count, a wrong `file:line` citation, an unanchored flagship theorem, a missing README,
  a duplicated sentence, or a new `axiom`/`sorry` on a pinned path now **fails a gate** rather
  than surviving unnoticed. C20 demonstrated this three times during the task itself: shortening
  `Validity.lean`, `StrongCompleteness.lean` and 51 files gaining `## Tags` each broke a citation,
  and each was named and fixed in the phase that caused it.
- Task 177's un-gated metalogic half is discharged; its remaining scope is the decidability-gated
  documentation work.
- `docs/theorem-index.md` gives a paper referee a single page mapping every flagship result to
  its Lean name, file, frame class and machine-pinned axiom set.

## Follow-ups

- `ENFORCE_C9_DOCS` is still 0: 142 task-number citations remain under `docs/`, concentrated in
  `docs/development/PHASED_IMPLEMENTATION.md` (100). Clearing them would let the flag flip.
- 1,083 `file.lean:NNN` citations remain inside `Metalogic/WeakCanonical/**`, reported by C20
  tier 1 but exempt from tier 2 by design. 34 more name an ambiguous or archived filename and are
  reported unverifiable rather than failed.
- `Last verified` stamps would be better derived from git than typed.
- 91 "files not listed" items remain in `readme-lint.sh`'s informational output — READMEs whose
  Contents tables are not yet generated blocks.
- A concurrent session (task 539, linter debt) committed to `main` throughout this dispatch and
  over-staged into this task's files once; one commit was reconstructed with an explicit file
  list. Parallel dispatches on this repository should stage explicit paths, never directories.

## References

- `specs/530_documentation_single_source_of_truth_theorem_index/plans/01_documentation-single-source-of-truth.md`
- `specs/530_documentation_single_source_of_truth_theorem_index/reports/01_documentation-single-source-of-truth.md`
- `specs/530_documentation_single_source_of_truth_theorem_index/handoffs/` — one per phase
- `specs/530_documentation_single_source_of_truth_theorem_index/pinned-axioms.tsv` — the 105
  pinned declarations with their recorded axiom values
- `specs/reviews/2026-09-01-lean-engineering/` — the source review
