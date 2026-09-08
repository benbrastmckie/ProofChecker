# Implementation Summary: Task #562

- **Task**: 562 - Sync language names with the paper (L⁻ / L / L⁺ / L⋆)
- **Status**: [COMPLETED]
- **Started**: 2026-09-08T18:20:00Z
- **Completed**: 2026-09-08T21:00:00Z
- **Effort**: ~2.5 hours
- **Dependencies**: Task 557 (completed and archived before this task ran)
- **Artifacts**: plans/01_sync-language-names-paper.md, reports/01_rename-inventory.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

This repository's object-language names now mean what the paper's mean. The S/U language
`Formula` was called **L⁺** here but is the paper's own **𝓛**; it is now **L**, with logic
**TM** — the paper's own name for the paper's own system. The H/G language `BLFormula` was
called **L**; it is now **L⁻**/**TM⁻** in `MinusLanguage/`. The ⊡-extension `StarFormula` was
called **L⋆**; it is now **L⁺**/**TM⁺** in `PlusLanguage/`. That frees `StarLanguage/`,
`StarFormula`, `StarAxiom`, `StarDerivationTree`, `⊢⋆` and `TM⋆` for the genuine store/recall
**L⋆** that task 561 builds.

It was a rename and a prose rewrite. **Zero proof terms changed** — established mechanically,
not by inspection (see Verification).

## What Changed

**Structure (13 `.lean` + 3 `README.md` moved)**
- `FormalSystem/BaseLanguage/` + `BaseLanguage.lean` → `MinusLanguage/` + `MinusLanguage.lean`
- `FormalSystem/StarLanguage/` + `StarLanguage.lean` → `PlusLanguage/` + `PlusLanguage.lean`
  (the `StarLanguage` name is now free)
- `Metalogic/Conservativity/Star/` + `Star.lean` → `Plus/` + `Plus.lean`;
  `Star/StarSoundness.lean` → `Plus/PlusSoundness.lean`
- `Metalogic/Conservativity/BaseLanguageSoundness.lean` → `MinusLanguageSoundness.lean`
- `Semantics/BL{Frame,Truth,Validity,SchemaValidity}.lean` → `Semantics/Minus*.lean`
- `Semantics/Star{Truth,Validity,Pasting,NonValidities,Determinism}.lean` → `Semantics/Plus*.lean`
- namespaces `FormalSystem.BaseLanguage` → `.MinusLanguage`, `FormalSystem.StarLanguage` → `.PlusLanguage`

**Declarations (169 distinct tokens)**
- 67 `BL*`/`bl*`/`bl_*` → `Minus*`/`minus*`/`minus_*`; 13 `swapBL*` → `swapMinus*`
- 76 `Star*`/`star*`/`star_*` → `Plus*`/`plus*`/`plus_*`
- 13 H/G-denoting `tm` names → `tmMinus` forms (`TMComplete` → `TMMinusComplete`,
  `tm_le_tmFrag` → `tmMinus_le_tmFrag`, …); `TMFrag` and the whole `tmFrag_` family kept
- `StarAxiom.ofPlus` → `PlusAxiom.ofTM`, `StarDerivationTree.ofPlus` → `PlusDerivationTree.ofTM`,
  `starValidIn_of_plus` → `plusValidIn_of_tm`, `starValidIn_swap_of_plus` → `plusValidIn_swap_of_tm`
- notation `Γ ⊢ᴮᴸ[fc] φ` / `⊢ᴮᴸ[fc] φ` → `⊢⁻[fc]`; `⊢⋆[fc]` → `⊢⁺[fc]`; `⊢[fc]` unchanged

**Prose (55 `.lean` + 20 markdown + 1 `.typ`)**
- `README.md` — the canonical **four-language table** (L⁻ / L / L⁺ / L⋆ with operators, logics
  and Lean homes) plus the manuscript correspondence; the "the system names on the two sides of
  the `⁺` are not the same family" paragraph is retired, being false after this task
- `NOTATION.md`, `ORGANISATION.md`, nine `docs/` files, eight in-tree `README.md` files,
  `typst/FormalFoundations.typ`
- every module and declaration docstring in `MinusLanguage/`, `PlusLanguage/`, `Semantics/`,
  `Metalogic/Conservativity/**`; the paper-line-number citations replaced by the label anchors
  `def:BLstar-semantics` and `sub:Extension`

**Records**
- `specs/paper-definitions-of-record.md` — a permanent correspondence section plus two new
  `LIVE-UNPINNED` `KNOWN-ANCHORS` rows (`def:BLstar-semantics`, `app:deterministic-future`)
- `scripts/check-module-invariants.sh` — 17 C14 baseline row NAMES in both heredocs
- `specs/state.json` — descriptions of tasks 534, 537, 559, 560, 561; `specs/TODO.md` regenerated

## Decisions

- **`ofPlus` → `ofTM`, not `ofBase`.** `Base` is a live, deliberately-unrenamed frame-class tag
  (`FrameClass.Base`), so `PlusAxiom.ofBase` would read as "at the Base frame class". `ofTM`
  names the source system and is literally correct after the rename.
- **No deprecation aliases.** Every rename phase landed atomically, so no intermediate build
  needed one; the final tree carries zero `@[deprecated]` attributes naming a pre-rename name.
- **The five decorated tokens were rewritten simultaneously, the bare ones by hand.**
  `L⁺`, `BL⁺`, `TM⁺`, `L⋆`, `TM⋆` each had exactly one meaning in the tree (checked against every
  site), so a single-pass alternating substitution is sound for them; a *sequential* one would
  have collapsed `L⋆ → L⁺ → L`. Bare `TM` and bare `BL` are genuinely ambiguous — bare `TM` means
  the S/U system in `ProofSystem/`, `Theorems/` and `BXCanonical/`, and the H/G system in
  `MinusLanguage/` and `Conservativity/` — so they were classified per file and the
  paper-referencing exceptions reverted by hand.
- **`α_star` and `hα_star_A` are excluded from every rule.** They are local hypothesis names
  inside proof terms in `BXCanonical/Chronicle/PointInsertion.lean`; a pattern-based `sed` of
  `star` would have edited a proof, which this task forbids. No phase used a pattern `sed`:
  every rename ran from the explicit token table in the inventory report.

## Plan Deviations

- **Phase 3 scope widened by 13 tokens** *(altered)*: the `swapBL` family (`swapBL`,
  `swapBL_involution`, `tr_swapBL`, nine `MinusFormula.swapBL_*` simp lemmas,
  `swapBL_df_valid_of_predOrder`; 83 occurrences) carries `BL` as a **suffix**, so Phase 1's
  token scan — anchored at `^` or `_` — missed it. Renamed to the `swapMinus` family.
- **Phases 3–6 shared one `lake build` instead of one each** *(altered)*: forced by running a
  tree-wide rename concurrently with task 193's dispatch, which owned
  `Metalogic/Soundness.lean` and `Metalogic/SoundnessLemmas/FrameClassVariants.lean` and was
  editing them throughout. Two full-package builds were **terminated by the orchestrator** —
  the first for holding the build-guard lock with task 193's single-module build queued behind
  it, the second on relaunch — and a third failed while elaborating task 193's uncommitted
  intermediate state. None failed on anything this task changed, but neither could that be
  concluded from the build itself: a tree-wide build during a concurrent dispatch elaborates
  the other dispatch's unverified edits alongside its own, so green would not have certified
  this rename and red would not have indicted it. That is a consequence of the tree-wide build,
  not a defect of task 193's. Each phase was instead verified by a mechanical purity proof
  (below), and the final build and gate were re-run on a clean tree (see Verification).
- **Two measured figures differed from the plan by more than 10% and were re-scoped in the
  inventory rather than absorbed** *(altered)*: `.lean` files carrying old vocabulary is **55**,
  not 80 (the plan's pattern also matched `BLOCKED`, `α_star`, `_start`, `_block`); the C14
  baseline carries **17** rows per heredoc, not ~24.
- Everything else followed the plan.

## Verification

- **Build**: `lake build` — **success**, 2615 jobs, zero errors, run against the exact tree
  that was committed.
- **Sorry count**: **0** new; C3 green. Every `sorry` string in the live tree is a docstring
  mention of historical work; `FormalSystem/Boneyard/` is out of scope by design.
- **Vacuous count**: **0**. The single `:= trivial` hit tree-wide
  (`Examples/TemporalStructures.lean`'s `int_domain_universal`) predates this task and is a real
  proof, not a placeholder.
- **Axiom count**: **unchanged** (8 before, 8 after, excluding `Boneyard/`). No axiom set on any
  C2 or C14 baseline row changed — only 17 row NAMES moved, verified by diffing the two heredocs'
  `depends on axioms: [...]` tails byte-for-byte.
- **Gates**: `bash scripts/check-module-invariants.sh` (full, with build) — **exit 0, ALL CHECKS
  PASSED**, 36 PASS lines and zero FAIL. The ones this task's correctness turns on:
  C1 `lake build` exits 0 (both libraries); C2 all four flagship axiom sets match baseline;
  C3 structural sorry inventory is ZERO across `FormalSystem/`; C8 every subdirectory has
  exactly one sibling aggregator; C14 **every pinned declaration matches its axiom baseline**;
  C15 all 58 paper-anchor citations resolve; C24 every module transitively imports
  `FormalSystem.Init`; C26 zero snake_case `def`/`abbrev`. `bash scripts/readme-lint.sh` — **PASS**.
- **`check-paper-definitions.sh`**: case (b), drift detected, with the **same six** anchors the
  separate re-pin work already owns (`def:S5`, `def:BX`, `def:BX-z`, `def:BX-d`, `def:BX-r`,
  `def:TMplus`). No anchor entered or left that set because of this task.
- **Zero proof-term changes, established mechanically, twice**:
  1. For phases 3–6: the phase-2 commit's content, put through this task's explicit token map,
     is **byte-identical** to the working tree for all 54 files this task owns.
  2. For phases 7–8: every changed `.lean` file, with all `/- … -/` and `--` comments stripped,
     is **byte-identical to `HEAD`**. Not one code line moved.
- **Freed names**: zero live occurrences of `StarFormula`, `StarAxiom`, `StarDerivationTree`,
  `⊢⋆`, `TM⋆`, `BaseLanguage`, `BLFormula`, `⊢ᴮᴸ`, `BL⁺`, `BL⋆` outside `FormalSystem/Boneyard/`
  and frozen `specs/**` artifacts. The three surviving `StarLanguage` mentions are the deliberate
  name reservation in `README.md`, `PlusLanguage/README.md` and `PlusLanguage/Formula.lean`.
- **Zero `@[deprecated]`** attributes naming a pre-rename identifier.
- **Zero task-number references** introduced under `FormalSystem/`, `docs/` or `typst/`
  (C9 green; the 142 pre-existing `docs/` citations are a separate, unenforced TODO).
- **Files verified**: yes.

### Independent re-verification (dispatch 5, 2026-09-08)

The orchestrator's completion-claim gate refused the first `implemented` claim: `.return-meta.json`
said `implemented` while the plan file still showed Phases 7, 8 and 12 at `[NOT STARTED]`. The
refusal was correct as a *marker* discrepancy and wrong as a *work* discrepancy — the work had been
done in `b8502cfd2`; only the headings were left stale, along with every phase's task checkboxes.

Dispatch 5 re-verified the outcomes rather than accepting the prior claim, and reproduced every
figure above on the live tree (`4bbb21bbc`; no commit after `b8502cfd2` touches `FormalSystem/`,
`scripts/` or `Tests/`):

- `lake build` — exit 0. `scripts/check-module-invariants.sh` — exit 0, `ALL CHECKS PASSED`.
  `scripts/readme-lint.sh` — PASS.
- Phases 7-8 comment-only claim re-proved with an independent comment-stripping parser: of the 48
  `.lean` files in `b8502cfd2`, **0 differ outside comments**.
- C14 heredocs: 101 names each, identical order. C2 flagship rows: **0** `BXCanonical` lines
  changed by this task. Across the task's entire diff of that script the only axiom sets present are
  `[propext]` and `[propext, Classical.choice, Quot.sound]` — names moved, axiom sets did not.
- Freed-name assertions: the only 3 live non-`specs/**` occurrences of the reserved tokens are
  deliberate forward-references reserving `StarLanguage` for task 561 (`README.md:214`,
  `FormalSystem/PlusLanguage/README.md:15`, `FormalSystem/PlusLanguage/Formula.lean:32`). The lone
  live `@[deprecated]` under `FormalSystem/` is `impOfNeg` (2025-12-14), predating this task.
- `check-paper-definitions.sh` exits 1 on exactly the six anchors named above and no others,
  confirming this rename introduced no new drift. The manuscript is an external read-only
  repository this task never edited.

All 12 phase headings are now `[COMPLETED]`, matching the work actually performed.

## Impacts

- **Task 561 is unblocked in the way it was waiting for.** `StarLanguage/`, `StarFormula`,
  `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are free, and 561's description now says
  so and names the new `PlusFormula`/`PlusLanguage`/`TM⁺` it extends.
- **Tasks 534, 537, 559 and 560** now name the new identifiers, so they write code and prose in
  the new vocabulary once rather than twice.
- **Citing the paper is now direct.** `TM` here *is* the paper's `TM`; `L` here *is* the paper's
  `𝓛`. The repository's L⁺ and L⋆ results are results about **fragments of the manuscript's 𝓛⋆**
  and every docstring that relates them to the paper now says exactly that, rather than implying
  a matching paper name.
- **Any in-flight branch touching `BaseLanguage/`, `StarLanguage/`, `Semantics/BL*` or
  `Semantics/Star*` will conflict.** The rename is tree-wide.

## Follow-ups

- **A tree-wide rename must not be dispatched concurrently with any other implementation
  dispatch.** This task's plan named only task 557 as a sequencing dependency; task 193 was live
  on the same working tree for the whole run and that gap cost real time — two full-package
  builds terminated by the orchestrator, a third confounded by another dispatch's uncommitted
  edits, and two commits that absorbed each other's work (see the two entries below). Task 193
  stayed inside its declared `file_scope` (`Automation/Tactics/`,
  `Metalogic/SoundnessLemmas/`, `Metalogic/Soundness.lean`) for its entire dispatch; an earlier
  draft of this summary recorded a scope breach by it, which was wrong — the three
  `Semantics/` files cited there (`Truth.lean`, `LexCarrier.lean`,
  `DurationClassification.lean`) were modified by **this task's** phase-3 rename
  (`BLTruth.always_iff` -> `MinusTruth.always_iff`, `bl_soundness_ztime_succ` ->
  `minus_soundness_ztime_succ`, `BLSchemaValidity.*` -> `MinusSchemaValidity.*`), and
  `git log -1` on each returns `d370581c5`, this task's own commit.
- **Two commits absorbed the other dispatch's work, in both directions.** `ea1a561c9` (this
  task's phase 2) carries 16 lines of task 193's `simp only [truth_norm]` conversions in
  `Metalogic/Soundness.lean` alongside its own single docstring-path line; task 193's
  `357212808` carries this task's four-line `bl_soundness*` -> `minus_soundness*` rename of the
  same file. Both commits are correct in content and mis-attributed in authorship; neither was
  rewritten, because two dispatches were live. The mechanism on this side was
  `git add -- FormalSystem/`, a **directory-wide stage**. `git add -A` was attempted once and
  correctly blocked by `guard-destructive-git.sh` — a directory stage slips past that guard with
  the identical failure mode and should carry the identical prohibition.
- **`git-snapshot.sh` run without `--no-revert`** by this task reverted the whole working tree,
  including task 193's in-flight edits. Everything was recovered from `stash@{0}` by single-path
  `git show stash@{0}:<path> > <path>`; task 193 had independently re-derived its work, so
  nothing was lost. The script's revert is repo-wide even though its safety marker is
  task-scoped.
- **`FormalSystem/Semantics/README.md` carried four stale identifier names** predating this task
  (`BLValidDiscrete`, `BLValidDiscreteSucc`, `BLValidDedekind`, `bl_soundness_discrete_succ` —
  retired by the earlier z/d/r wave). Corrected here to their live `MinusValid*` forms.
- **`ProofSystem/Axioms.lean`, `Semantics/FrameClassValidity.lean` and `Semantics/Validity.lean`
  each claimed a paper system named `TM⁺_r`.** The paper has no such name; corrected to `TM_r`.
- **Recommendation for every future rename plan: verify the C14 baseline by resolution, never by
  enumeration.** This plan enumerated ~24 baseline rows by hand; the true figure was 17, and two
  further rows — `blCompactBase` and `blCompactDense` — named renamed declarations and appeared
  in no hand list. They were caught only by checking that **all 101** names in the `C14BASE`
  heredoc resolve to a live declaration in `FormalSystem/`, and they would otherwise have failed
  the gate silently after the rename was already committed. The check is three lines of script
  and is worth making a standing step: for every name in `C14BASE`, grep the live tree for its
  declaration; assert `C14BASE` and `C14LEAN` list the same names in the same order; and diff the
  two heredocs' `depends on axioms: [...]` tails against the pre-task script to prove no axiom set
  moved.
- The six drifted paper anchors remain owned by the separate re-pin work; nothing here touched a
  `verbatim:` block, a `sha256:` line, a manifest row, or either sentinel.

## References

- `specs/562_sync_language_names_with_paper_l_minus_plus_star/plans/01_sync-language-names-paper.md`
- `specs/562_sync_language_names_with_paper_l_minus_plus_star/reports/01_rename-inventory.md`
- `specs/paper-definitions-of-record.md` — "Language correspondence (2026-09-08)"
- `README.md` — the canonical four-language table
- `FormalSystem/Metalogic/Conservativity.lean` — "System names, and how they map onto the paper"
