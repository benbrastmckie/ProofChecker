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
- **Phases 3–6 shared one `lake build` instead of one each** *(altered)*: forced by a
  concurrency collision with task 193, which was editing
  `Metalogic/SoundnessLemmas/FrameClassVariants.lean` and `Metalogic/Soundness.lean` throughout.
  Two full builds were killed mid-run and a third failed on task 193's own in-progress broken
  proof term — none on anything this task changed. Each phase was instead verified by a
  mechanical purity proof (below), and the shared build then came back green over all 2615 jobs.
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

- **Concurrency, worth recording**: task 193 was implementing on the same tree throughout, and
  outside its declared `file_scope` (it also modified `Semantics/Truth.lean`,
  `Semantics/LexCarrier.lean` and `Semantics/DurationClassification.lean`). Two of this task's
  builds were killed and one failed on 193's broken intermediate state. Sequencing a tree-wide
  rename against a concurrent per-file sweep costs real time; the plan named only task 557.
- **`FormalSystem/Semantics/README.md` carried four stale identifier names** predating this task
  (`BLValidDiscrete`, `BLValidDiscreteSucc`, `BLValidDedekind`, `bl_soundness_discrete_succ` —
  retired by the earlier z/d/r wave). Corrected here to their live `MinusValid*` forms.
- **`ProofSystem/Axioms.lean`, `Semantics/FrameClassValidity.lean` and `Semantics/Validity.lean`
  each claimed a paper system named `TM⁺_r`.** The paper has no such name; corrected to `TM_r`.
- The six drifted paper anchors remain owned by the separate re-pin work; nothing here touched a
  `verbatim:` block, a `sha256:` line, a manifest row, or either sentinel.

## References

- `specs/562_sync_language_names_with_paper_l_minus_plus_star/plans/01_sync-language-names-paper.md`
- `specs/562_sync_language_names_with_paper_l_minus_plus_star/reports/01_rename-inventory.md`
- `specs/paper-definitions-of-record.md` — "Language correspondence (2026-09-08)"
- `README.md` — the canonical four-language table
- `FormalSystem/Metalogic/Conservativity.lean` — "System names, and how they map onto the paper"
