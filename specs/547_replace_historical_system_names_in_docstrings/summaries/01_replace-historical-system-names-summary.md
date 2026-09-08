# Implementation Summary: Task #547

- **Task**: 547 - Replace historical system names in docstrings
- **Status**: [COMPLETED]
- **Started**: 2026-09-07
- **Completed**: 2026-09-07
- **Effort**: ~4 hours
- **Dependencies**: 546 (completed). Blocks the anchor re-pinning follow-up.
- **Artifacts**: plans/01_replace-historical-system-names.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Retired the historical extension names `TM⁺_f`, `TM⁺_c`, `TM⁺_dc`, `TM_f`, `TM_c`, `TM_dc`, `BX_f`
and `BX_c` from every live comment, docstring, README, doc page and sync map, replacing them with
the paper's current `z`/`d`/`r` subscripts, and recorded in one canonical place how this
repository's two families of system name map onto the paper's. Twelve passages asserted things
about the paper that its `z`/`d`/`r` revision has retracted or resolved — verbatim quotations of a
deleted sentence, a "real gap" argument the paper has closed, an "open question" it has answered,
and a `TM⁺_c`-vs-`TM⁺_dc` contrast that collapses to one name — and those were rewritten by hand
rather than token-swapped. No Lean identifier, no anchor label and no row of
`specs/paper-definitions-of-record.md` was touched.

## What Changed

Every hunk in all 20 source files lies inside a `/-! -/` or `/-- -/` docstring, a `--` comment, or
markdown prose. No declaration, term, tactic, axiom or `sorry` was added or changed.

- `FormalSystem/Metalogic/Conservativity.lean` — gained the canonical **System names, and how
  they map onto the paper** section in its module docstring; the "Two live-paper facts" block
  de-quoted and restated from the live `def:TMplus-f` closing sentence; remaining names renamed.
- `docs/README.md` — gained a prose-adapted **System Names and the Paper's Mapping** section with
  a five-row correspondence table.
- `FormalSystem/ProofSystem/Axioms.lean` — the CO-basis note now records that the paper derives CO
  from `BX_d + PU + SEP`, matching this tree; the fix.md C4 amendment note discharged, with the
  paper's own commented ℚ-flow conjecture identified as the route `Independence.CoNotPriorU`
  refutes; the "`TM⁺_c` gap" passage replaced by a statement that `ValidComplete` is
  repository-only.
- `FormalSystem/Semantics/Validity.lean` — `ValidComplete` is "the class of no paper system".
- `FormalSystem/Semantics/FrameProperty.lean` — two de-quotation sites (module header and the
  `TaskFrame.IsZTime` docstring); `cor:tm-completeness` references retargeted to `TM⁺_r`.
- `FormalSystem/Semantics/FrameClassValidity.lean` — per-constructor anchors rewritten in the new
  vocabulary; the ℤ-time quotation de-quoted.
- `FormalSystem/BaseLanguage/Axioms.lean` — the system table's CO row is `TM_r`, the `TM_c`/`TM_dc`
  caveat deleted, and the one-time "these four names are Lean-only and have no paper counterpart"
  sentence added at the table, pointing at `Conservativity.lean` for the full mapping.
- `FormalSystem/BaseLanguage/AxiomDischarge.lean` — the `TM_dc`-not-`TM_c` contrast collapsed to `TM_r`.
- `FormalSystem/Metalogic/Conservativity/Backward.lean` — the CEC "fidelity caveat" retired; the
  row reads `TM_r ⟶ TM⁺_r`, and `TM⁺_r` *is* the paper's `TM_r`.
- `FormalSystem/Metalogic/Conservativity/Fragment.lean` — `TMFrag`'s docstring now describes the
  H/G-fragment of `TM⁺` as the set of Past/Future theorems of the paper's `TM`.
- `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean` — mechanical rename, plus the stale
  "By Hölder (paper `def:TMplus-f`, line 4613)" citation de-staled.
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean`,
  `FormalSystem/BaseLanguage/Derivation.lean`, `docs/theorem-index.md` — mechanical rename.
- `FormalSystem/Theorems/DedekindDerived.lean` — CO is derived in `BX_r`, not an extra axiom.
- `FormalSystem/Theorems/DiscreteUnfolding.lean` — `DF` distinguishes *this tree's* `TM_z` from `TM`.
- `README.md`, `FormalSystem/README.md` — the "there is no gap" and "one question does remain open"
  paragraphs rewritten as resolved; three co-located task-546 `FrameClass.Dedekind` residue lines
  fixed inside the rewritten text.
- `docs/user-guide/architecture.md`, `typst/SYNC-MAP.md` — renamed.
- Four generated inventory blocks regenerated (`README.md`, `FormalSystem/Metalogic/README.md`,
  `FormalSystem/Metalogic/Conservativity/README.md`, `FormalSystem/Theorems/README.md`), whose
  line counts this task's edits invalidated.

## Decisions

- **New prose cites the record's anchor labels, not the paper's live ones.** The paper has
  relabelled `def:TMplus-f`/`-d`/`-c` to `def:BX-z`/`-d`/`-r`, but C15 resolves citations against
  `specs/paper-definitions-of-record.md`, whose re-pin is separate work. Citing `def:BX-z` here
  would turn C15 red. The mapping paragraph says so inline.
- **The BaseLanguage systems are described as having no paper name**, with one sentence noting the
  commented-out Past/Future footnote — the option the plan's `user_decision` recommended.
- **Line-number citations into `possible_worlds.tex` were dropped, not updated.** They drift; both
  the sweep touched were already stale.
- **`typst/FormalFoundations.typ` was left alone.** It transcribes the paper environment the record
  pins, and renaming it independently would desynchronize it from the record.

## Plan Deviations

- **Phase 1** altered: the `check-module-invariants.sh` baseline exits 1 on a pre-existing C9
  task-number citation in `MintBound.lean`, unrelated to this file set. C14 and C15 both PASS.
- **Phase 1** altered: census confirmed at 74 lines / 19 files, but `FormalSystem/README.md`'s six
  lines sit at 194/195/197/199/201/361, not where the plan guessed.
- **Phase 2** altered: cited `def:TMplus-f`/`-d`/`-c` rather than the paper's live `def:BX-*`
  labels (see Decisions); dropped the `possible_worlds.tex:4274` line number rather than updating
  it — that line is a different comment.
- **Phase 3** altered: also de-staled the adjacent "By Hölder … line 4613" sentence in
  `Z1Countermodel.lean`, which cites a moved line and a superseded argument.
- **Phase 4** altered: a fourth de-quotation site, the `TaskFrame.IsZTime` docstring in
  `FrameProperty.lean`, was found and fixed; the census grep missed it because its markdown
  emphasis splits the token as ``**BX**`_f```.
- **Phase 4** altered: the anchor-count check is recorded as *non-decreasing* rather than exact
  (`def:TMplus-f` 18 → 19, `def:TMplus-c` 10 → 11, `cor:tm-completeness` 40 → 46). The rewrites
  cite the pinned anchors in more places than the retired quotations did; no label was renamed or
  removed, which is the property C15 actually gates on.
- **Phase 6** altered: the recorded task-546 residue list is seven sites, not five —
  `FormalSystem/README.md:174` and `:182` also carry it and sit outside the rewritten paragraphs.
- **Phase 7** altered: the plan's `lake build FormalSystem` is **not sufficient** for the
  invariants gate. `FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound` lies
  outside that target's closure, so the scoped build reported success while `MintBound.olean` was
  absent, and C1, C2, C14 and C16 all failed on the missing object file. A full `lake build` is
  required before `check-module-invariants.sh` can evaluate those checks at all.
- **Phase 7** altered: an initial invariants run showed four extra failures plus two stale
  aggregate inventory blocks, all traced to a concurrent session editing and rebuilding
  `MintBound.lean` — its `.olean` was repeatedly deleted mid-rebuild, and its line count feeds the
  `Decidability/` aggregate in two READMEs. After that session settled, a clean re-run left only
  the pre-existing C9.
- **Phase 7** added: regenerating four stale generated inventory blocks, which the plan did not
  anticipate.

## Verification

- Build: `lake build FormalSystem` green (exit 0); full `lake build` green (exit 0, 2592 jobs).
  Both detached through `lake-build-guard.sh`.
- Sorry count: 0 (no `sorry` added; no Lean term changed).
- Vacuous count: 0.
- Axiom count: unchanged — C2 and C14's axiom baselines both match.
- Tests: `lake build BimodalTest` exits 0 (C1).
- Files verified: Yes.
- Scoped completeness grep
  (`grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)' --include='*.lean' --include='*.md' --include='*.typ' --include='*.sh' --exclude-dir=Boneyard FormalSystem Tests typst docs scripts README.md`)
  returns no output.
- `scripts/readme-lint.sh` PASS.
- `scripts/check-module-invariants.sh` no worse than the Phase 1 baseline: both runs end with
  exactly one substantive failure, **C9**, on the same pre-existing task-number citation in
  `MintBound.lean`, a file this task never touches. **C15 PASS** (53 anchor citations resolve, 52
  theorem-index rows); **C14 PASS** (both rows); C1, C2, C16 and INV all PASS.
- `specs/paper-definitions-of-record.md` and `FormalSystem/Metalogic/Conservativity/Star/`
  unmodified across every commit (`git diff --stat` empty for both).
- Diff read-through: every hunk lies inside a comment, docstring, or markdown/typst prose.
- No "X, not X" sentence and no quotation of the deleted "successor-Archimedean discrete class"
  sentence survives in live scope.

## Impacts

- A reader of `Conservativity/` can tell the two `TM` families apart from one canonical passage
  instead of reconstructing the distinction from scattered caveats.
- Four passages that told a future dispatch the paper had an unresolved gap or open question no
  longer do, so that dispatch will not spend effort re-opening settled ground.
- The anchor re-pinning follow-up inherits a clean split: every anchor label and every record row
  is untouched.

## Follow-ups

- Re-pin `specs/paper-definitions-of-record.md` to the paper's `def:BX-z`/`-d`/`-r` labels, then
  retarget the label citations this sweep left pointing at the old spellings, and rename the
  historical names in `typst/FormalFoundations.typ` alongside that re-pin.
- Seven `FrameClass.Dedekind` / `FrameClass.Discrete` residue sites remain outside the paragraphs
  this sweep rewrote; enumerated in `handoffs/547-548-boundary.md`.
- The task description's premise that the paper carries a live Past/Future footnote is false —
  `possible_worlds.tex:1331-1341` is commented out in full. If the author un-comments it, the
  mapping paragraph's second bullet should be revised to cite it.
- Run a full `lake build`, not `lake build FormalSystem`, before `check-module-invariants.sh`;
  `MintBound` is outside the scoped target's closure.

## References

- `specs/547_replace_historical_system_names_in_docstrings/plans/01_replace-historical-system-names.md`
- `specs/547_replace_historical_system_names_in_docstrings/reports/01_historical-system-name-sweep.md`
- `specs/547_replace_historical_system_names_in_docstrings/baseline/phase1-baseline.md`
- `specs/547_replace_historical_system_names_in_docstrings/handoffs/547-548-boundary.md`
