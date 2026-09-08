# Implementation Plan: Task #562

- **Task**: 562 - Sync language names with the paper (L⁻ / L / L⁺ / L⋆)
- **Status**: [IMPLEMENTING]
- **Effort**: 18 hours
- **Dependencies**: Task 557 (in progress) — its `file_scope` includes `Syntax/Formula.lean`,
  `Metalogic/Conservativity/TMCompletenessReduction.lean` and
  `Metalogic/Conservativity/DenseObstructionTransfer.lean`; a global rename dispatched
  concurrently would collide. Phase 2 opens with an explicit clean-tree / 557-status check.
- **Research Inputs**: None (no research report; the task description is a full specification
  carrying the mapping, the identifier scheme and measured surface counts — see
  "No research phase" under Overview)
- **Artifacts**: plans/01_sync-language-names-paper.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false (name-and-prose sweep; zero proof-term changes, zero new declarations)

## Overview

This repository's object-language names currently mean something different from the paper's. The
S/U language `Formula` is called **L⁺** here but is the paper's own **𝓛**; the H/G language
`BLFormula` is called **L** here but has no paper counterpart at all; the ⊡-extension
`StarFormula` is called **L⋆** here but is only the ⊡-fragment of the paper's **𝓛⋆**. This task
performs the three-way rename that makes the repository's names mean what the paper's mean —
`Formula`/TM become **L**/TM, `BaseLanguage`/TM become **L⁻**/TM⁻, `StarLanguage`/TM⋆ become
**L⁺**/TM⁺ — thereby freeing `StarLanguage/`, `StarFormula`, `⊢⋆` and TM⋆ for the genuine
store/recall **L⋆** that task 561 builds.

It is a rename and a prose rewrite. No proof term changes. A rename that forces a proof edit is a
defect to report, not to absorb.

### No research phase

No `research_path` was supplied and none was requested. The task description is a specification,
not a research question: it fixes the target convention, the (a)–(e) mapping, the recommended
identifier scheme, the six deliverables and the hard constraints, and it carries measured surface
counts. Everything the plan needed beyond that was resolved by direct `grep`/`Read` within this
dispatch (results in "Measured surface" below).

### Measured surface (re-derived in this dispatch)

Every figure below is a **hypothesis to be re-confirmed at implementation time**, not a fact; each
phase that asserts one carries a `Scope Hypothesis` line.

| Surface | Measure | Command |
|---|---|---|
| BL-family declarations | 63 | declaration scan over `FormalSystem/**/*.lean`, filtered `(^\|\.)(BL[A-Za-z0-9]\|bl_\|bl[A-Z])` |
| Star-family declarations | 66 | same scan, filtered `(^\|\.)(Star[A-Za-z]\|star[A-Z_])` |
| tm-family declarations | 23 | same scan, filtered `(^\|\.)(tm[A-Z_]\|TM)` |
| BL-family occurrences | 1287 | `grep -rhoE '\b(BL[A-Za-z0-9]\|bl_\|bl[A-Z])[A-Za-z0-9_]*' --include='*.lean' FormalSystem/` |
| Star-family occurrences | 1457 | same shape, Star pattern |
| tm-family occurrences | 196 | same shape, `TMComplete\|TMFrag\|tmComplete\|tmFrag\|tm_le_tmFrag\|tm_lt_tmFrag` |
| `FormalSystem.BaseLanguage.` qualified uses | 126 | `grep -rn 'BaseLanguage\.' --include='*.lean' FormalSystem/` |
| `FormalSystem.StarLanguage.` qualified uses | 16 | `grep -rn 'StarLanguage\.' --include='*.lean' FormalSystem/` |
| `.lean` files carrying old vocabulary (identifiers or tokens) | 80 | union grep over `FormalSystem/` + `Tests/` |
| Markdown files carrying old vocabulary | 20 | 18 under `FormalSystem/` + `docs/` + `README.md`, plus `NOTATION.md` and `ORGANISATION.md` |
| `typst/FormalFoundations.typ` occurrences | 15 | `grep -noE` over the old-name token set |
| Open task descriptions to re-word | 5 (534, 537, 559, 560, 561) | 69 vocabulary hits total in `specs/state.json` descriptions |
| `check-module-invariants.sh` C14 baseline rows naming renamed declarations | ~24 | `bl_soundness*`, `bl_not_derivable_nil_bot*`, `tmComplete*`, `star_soundness_validIn`, `starDerivable_ofFormula_iff`, `starValidIn_ofFormula_iff`, `deterministic_not_starDefinable` |

Two findings the task description did not name, both load-bearing:

1. **`NOTATION.md` and `ORGANISATION.md` at the repository root** carry the old vocabulary
   (`### BL⁺, the base language`, `### TM⋆, the stability language`, the `StarLanguage/` layer-0
   row). They are in scope and are added to deliverable (3).
2. **`scripts/check-module-invariants.sh`'s C14 baseline is a pair of heredocs (`C14BASE` and
   `C14LEAN`) compared by exact string equality and required to list the same declarations in the
   same order.** ~24 of its rows name declarations this task renames. Both heredocs must be edited
   together, in place, order preserved. This is a NAME-only edit; no axiom set on any row changes.
   C2's own four flagship rows are all `BXCanonical` declarations and are untouched by this task.

### Research Integration

No research report exists for this task. See "No research phase" above.

### Prior Plan Reference

No prior plan. The task description cites archived tasks 546, 548 and 552 (the history-vocabulary
and z/d/r renames) as the manner to follow; their artifacts are archived and were not loaded. The
manner is reproduced structurally here: mechanical layer first, declarations second, prose last,
gates at the end, and a `specs/paper-definitions-of-record.md` prose-only correspondence entry
following the precedent of that file's own "Vocabulary alignment (2026-09-07): prose only, no
re-pin" section.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch and no roadmap phases are added. `specs/ROADMAP.md`
was not consulted or modified.

## Goals & Non-Goals

**Goals**:

- Rename the H/G language and its logic: `BaseLanguage/` → `MinusLanguage/`, `BLFormula` →
  `MinusFormula`, `⊢ᴮᴸ[fc]` → `⊢⁻[fc]`, `bl_*`/`BL*`/`blValid*` → `minus_*`/`Minus*`/`minusValid*`,
  and every `tm`-prefixed name that denotes the H/G system → its `tmMinus` form. Result: **L⁻**
  with logic **TM⁻**.
- Rename the ⊡-extension and its logic: `StarLanguage/` → `PlusLanguage/`, `StarFormula` →
  `PlusFormula`, `StarAxiom`/`StarDerivationTree`/`StarDerivable` →
  `PlusAxiom`/`PlusDerivationTree`/`PlusDerivable`, `⊢⋆[fc]` → `⊢⁺[fc]`, `star_*`/`Star*` →
  `plus_*`/`Plus*`. Result: **L⁺** with logic **TM⁺**.
- Leave `Formula`, `ProofSystem.DerivationTree`, `⊢[fc]` and every `tm` name denoting the S/U
  system unrenamed; they now read as **L** and **TM**, matching the paper's 𝓛 and TM.
- Leave `TMFrag` and `FrameClass.Base` unrenamed (per (e) of the task description).
- Free the names `StarLanguage/`, `StarFormula`, `⊢⋆` and TM⋆ entirely — zero live occurrences
  outside `Boneyard/` at the end of the task — so task 561 can claim them.
- Rewrite `README.md`, the six in-tree `README.md` files, `NOTATION.md`, `ORGANISATION.md`, the
  nine `docs/` files and `typst/FormalFoundations.typ` to the new vocabulary, with one table
  stating the four languages, their operators, their logics and their Lean homes.
- Re-pin `specs/paper-definitions-of-record.md` so C15 resolves, recording as a **permanent**
  correspondence (not a pending one) that the manuscript has exactly two languages, 𝓛 and 𝓛⋆.
- Re-word the open descriptions of tasks 534, 537, 559, 560 and 561 to the new identifiers.
- `lake build FormalSystem` green at the end of every phase; `scripts/check-module-invariants.sh`
  fully green at the end.

**Non-Goals**:

- No proof-term changes. A rename that forces a proof edit is reported as a defect and the phase
  stops; it is not absorbed.
- No `sorry`, structural or strategic.
- No change to the manuscript, and no proposal of manuscript changes. `possible_worlds.tex` is
  read-only input; the author's decision is that the paper keeps only 𝓛 and 𝓛⋆.
- No implementation of the genuine L⋆ (store/recall). This task only frees the names; task 561
  builds it.
- No change to any axiom SET in the C2 or C14 baselines — only baseline row NAMES move.
- No renaming of `TMFrag`, `FrameClass.Base`, `Formula`, or any S/U-denoting `tm` name.
- No edits under `FormalSystem/Boneyard/` (archived; excluded from C3, C14 and C15 scope).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A blanket `sed` of `Star` → `Plus` collides with pre-existing `Plus`/`plus` tokens (`StarAxiom.ofPlus`, `starValidIn_of_plus`, `StarDerivationTree.ofPlus`), silently producing `PlusAxiom.ofPlus`-style nonsense or double-renames | H | H | Never blanket-sed. Every phase renames from the explicit name-by-name mapping table produced in Phase 1, longest-name-first, with a post-rename `grep` asserting zero occurrences of each old name and zero occurrences of the forbidden collision shapes (`ofPlus`, `plus_of_plus`, `PlusPlus`) |
| A rename forces a proof edit (name appears in a `simp` set, `rename_i`, structure projection, or a `Name`-literal in `Automation/`) | H | M | HARD CONSTRAINT: stop, record the site in the phase's notes and in the summary as a defect, do not edit the proof term. Escalate to the user rather than absorbing |
| A docstring `L⁺` means the S/U language in one file and the ⊡-extension in another; search-replace produces false statements | H | H | Every `L⁺`/`L⋆`/`TM`/`TM⁺`/`TM⋆` docstring site is classified BY HAND in Phase 1's inventory and re-read individually in Phases 7–9. No token-level replacement is permitted in the prose phases |
| C14's `C14BASE`/`C14LEAN` heredocs drift apart (they are compared by exact string equality, same declarations in the same order) | H | M | Phase 12 edits both heredocs in one pass, preserving row order, and diffs them against each other before running the gate |
| The aggregator convention (`X/` has exactly one sibling `X.lean`) or C24 (root closure ⊇ every module, each importing `FormalSystem.Init`) breaks mid-rename | M | M | Directory renames and aggregator renames land in the same atomic-batch phase (2 and 5), with `lake build FormalSystem` plus `scripts/check-module-invariants.sh --no-build` run at phase close |
| Concurrent edits from task 557 collide on `Syntax/Formula.lean`, `Conservativity/TMCompletenessReduction.lean`, `Conservativity/DenseObstructionTransfer.lean` | H | M | Phase 2 opens with a clean-tree check and a 557-status check; if 557 is not out of those files, the phase stops and reports rather than proceeding |
| A new `def:`-prefixed paper anchor cited by the rewritten prose (e.g. `def:BLstar-semantics`) has no MANIFEST or KNOWN-ANCHORS row, turning C15 red | M | M | Phase 10 adds a `LIVE-UNPINNED` KNOWN-ANCHORS row for any newly cited `def:`/`thm:`/`lem:`/`cor:`/`app:`/`rmk:` anchor before Phase 12's gate. Note `sub:Extension` is NOT matched by C15's pattern and needs no row |
| Deprecation aliases kept for a green intermediate build survive into the final tree | M | L | No phase in this plan requires an alias (every rename phase is `atomic-batch`). If one is nonetheless introduced, Phase 12 asserts zero `@[deprecated]` attributes naming any pre-rename identifier |
| C26 (no underscore inside a live `def`/`abbrev` name component) is violated by a new name | L | L | The scheme keeps every renamed `def`/`abbrev` in camelCase (`minusTruthAt`, `MinusValidIn`, `PlusTruthAt`); underscores appear only on `theorem` names, where C26 does not apply. Phase 12 runs C26 |

## Identifier Scheme (confirmed)

Lean identifiers cannot carry `⁺`/`⁻`/`⋆`; notation can. The scheme below is the task
description's recommendation, confirmed, with two decisions resolved.

| Old | New | Note |
|---|---|---|
| `FormalSystem/BaseLanguage/` + `BaseLanguage.lean` | `FormalSystem/MinusLanguage/` + `MinusLanguage.lean` | directory + sibling aggregator move together |
| `FormalSystem/StarLanguage/` + `StarLanguage.lean` | `FormalSystem/PlusLanguage/` + `PlusLanguage.lean` | `StarLanguage/` is thereby FREED for task 561 |
| namespace `FormalSystem.BaseLanguage` | namespace `FormalSystem.MinusLanguage` | 126 qualified uses + `open` sites |
| namespace `FormalSystem.StarLanguage` | namespace `FormalSystem.PlusLanguage` | 16 qualified uses + `open` sites |
| `Metalogic/Conservativity/Star/` + `Star.lean` | `Metalogic/Conservativity/Plus/` + `Plus.lean` | |
| `Metalogic/Conservativity/BaseLanguageSoundness.lean` | `Metalogic/Conservativity/MinusLanguageSoundness.lean` | |
| `Semantics/BL{Frame,Truth,Validity,SchemaValidity}.lean` | `Semantics/Minus{Frame,Truth,Validity,SchemaValidity}.lean` | |
| `Semantics/Star{Truth,Validity,Pasting,NonValidities,Determinism}.lean` | `Semantics/Plus{Truth,Validity,Pasting,NonValidities,Determinism}.lean` | |
| `BLFormula` | `MinusFormula` | |
| `StarFormula` | `PlusFormula` | |
| `StarAxiom`, `StarDerivationTree`, `StarDerivable`, `StarContext` | `PlusAxiom`, `PlusDerivationTree`, `PlusDerivable`, `PlusContext` | |
| notation `⊢ᴮᴸ[fc]` | `⊢⁻[fc]` | both the `Γ ⊢ᴮᴸ[fc] φ` and the nil-context form |
| notation `⊢⋆[fc]` | `⊢⁺[fc]` | both forms |
| notation `⊢[fc]`, `⊢ φ` | unchanged | now reads as TM, which is what it always meant to the paper |
| `BL*` / `bl_*` / `blValid*` | `Minus*` / `minus_*` / `minusValid*` | 63 declarations |
| `Star*` / `star_*` | `Plus*` / `plus_*` | 66 declarations |
| `TaskFrame.BLValidOn`, `TaskFrame.StarValidOn` | `TaskFrame.MinusValidOn`, `TaskFrame.PlusValidOn` | |
| `TMComplete*`, `tmComplete*`, `tm_le_tmFrag`, `tm_lt_tmFrag_ztime` | `TMMinusComplete*`, `tmMinusComplete*`, `tmMinus_le_tmFrag`, `tmMinus_lt_tmFrag_ztime` | these denote the H/G system |
| `TMFrag`, `tmFrag_*` | unchanged | `TMFrag fc φ := TM ⊢[fc] tr φ` — after the rename that sentence is literally true |
| `tmFrag_iff_blValidIn`, `tmFrag_iff_star` | `tmFrag_iff_minusValidIn`, `tmFrag_iff_plus` | the `tmFrag_` prefix stays; the suffix moves |
| `star_of_tm{,_base,_dense,_rtime,_ztime}` | `plus_of_tmMinus{,_base,_dense,_rtime,_ztime}` | |
| `FrameClass.Base` | unchanged | a frame-class tag, not a language |

**Decision 1 — `StarAxiom.ofPlus` / `StarDerivationTree.ofPlus` become `PlusAxiom.ofTM` /
`PlusDerivationTree.ofTM`**, not `ofBase`. Both candidates were offered by the task description.
`ofBase` is rejected because `Base` is a live, deliberately-unrenamed frame-class tag
(`FrameClass.Base`), and `PlusAxiom.ofBase` would read as "at the Base frame class" rather than
"embedding of the S/U schemata". `ofTM` names the source system unambiguously and is literally
correct after the rename. `starValidIn_of_plus` / `starValidIn_swap_of_plus` follow the same rule:
`plusValidIn_of_tm` / `plusValidIn_swap_of_tm`.

**Decision 2 — no deprecation aliases.** The task description permits pre-rename names to survive
as deprecation aliases only if a phase needs them for a green intermediate build. Every rename
phase here is `atomic-batch`, so the whole rename lands in one commit per phase and no alias is
needed. Phase 12 asserts none exists.

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
| 7 | 7, 8 | 6 |
| 8 | 9 | 7, 8 |
| 9 | 10, 11 | 9 |
| 10 | 12 | 10, 11 |

Phases within the same wave can execute in parallel. Waves 2–6 are strictly sequential because
every rename layer touches an overlapping file set (e.g.
`Metalogic/Conservativity/Star/Forward.lean` opens both `FormalSystem.BaseLanguage` and
`FormalSystem.StarLanguage`), so the Minus and Plus chains cannot be parallelised without a
territory conflict. Phases 7 and 8 partition the prose surface by disjoint directory; Phases 10
and 11 touch disjoint files (`specs/paper-definitions-of-record.md` vs `specs/state.json`).

---

### Phase 1: Rename inventory and hand-classified docstring map [COMPLETED]

**Goal**: Produce deliverable (1) — the inventory mapping every affected directory, file,
declaration, notation and docstring phrase to its new name, with every ambiguous `L⁺`/`TM`/`TM⁺`
docstring site classified by hand. This is the mapping table every later phase renames from.

**Tasks**:
- [ ] Re-derive each row of the "Measured surface" table above with the stated command; record any
      figure that differs and note the difference in the report.
- [ ] Enumerate all 63 BL-family, 66 Star-family and 23 tm-family declarations with fully
      qualified names, their defining file, and their new name per the Identifier Scheme table.
- [ ] Enumerate the file and directory moves (11 `.lean` renames, 2 directory renames, 1
      subdirectory rename, 3 aggregator renames, 3 README moves).
- [ ] Enumerate the 4 notation declaration sites (`BaseLanguage/Derivation.lean:162,165`,
      `StarLanguage/Derivation.lean:165,168`) and their new tokens.
- [ ] Grep every occurrence of `L⁺`, `L⋆`, `L⁻`, `TM⁺`, `TM⋆`, `BL⁺`, `BL⋆` and bare `TM`/`L` in
      `FormalSystem/**/*.lean` docstrings, `FormalSystem/**/*.md`, `docs/**`, `README.md`,
      `NOTATION.md`, `ORGANISATION.md`, `typst/FormalFoundations.typ`; classify EACH site by hand
      as (S/U → L), (H/G → L⁻), (⊡ → L⁺), (store/recall → L⋆, task 561's), or
      (paper's 𝓛 / 𝓛⋆ — leave as a paper reference), and record the classification per site.
- [ ] Flag every site whose sentence STRUCTURE must change (files discussing two or all three
      languages, where a token swap alone would produce a false sentence).
- [ ] Record the ~24 `check-module-invariants.sh` C14 baseline rows that name renamed declarations,
      in the order they appear, for Phase 12.
- [ ] Record every `docs/theorem-index.md` row whose Lean name is renamed (the `pcq pinned:C14`
      rows).
- [ ] Write the inventory to `specs/562_sync_language_names_with_paper_l_minus_plus_star/reports/01_rename-inventory.md`.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The counts in the "Measured surface" table (63 / 66 / 23 declarations, 80
`.lean` files, 20 markdown files, 15 typst occurrences, ~24 C14 rows) are hypotheses. Confirm each
by re-running the stated command at implementation time and recording the actual figure in the
inventory report; if any figure differs by more than 10%, note it explicitly and re-scope the
affected later phase rather than silently absorbing the difference.

**Files to modify**:
- `specs/562_sync_language_names_with_paper_l_minus_plus_star/reports/01_rename-inventory.md` — new

**Verification**:
- The inventory names a new identifier for every declaration in the three families, with no
  `TBD` rows.
- Every ambiguous docstring site carries an explicit hand classification, not a rule.
- `git status` shows no change under `FormalSystem/`, `docs/` or the repository root.

---

### Phase 2: L⁻ structural layer — directories, aggregators, modules, namespaces [COMPLETED]

**Goal**: Move the H/G language's files and namespace to the `Minus` names, leaving every
declaration name untouched. `lake build FormalSystem` green at phase close.

**Tasks**:
- [ ] Confirm the working tree is clean and task 557 is not currently holding
      `Syntax/Formula.lean`, `Conservativity/TMCompletenessReduction.lean` or
      `Conservativity/DenseObstructionTransfer.lean`. If it is, STOP and report.
- [ ] `git mv FormalSystem/BaseLanguage FormalSystem/MinusLanguage` and
      `git mv FormalSystem/BaseLanguage.lean FormalSystem/MinusLanguage.lean`.
- [ ] `git mv` the four `Semantics/BL*.lean` files to `Semantics/Minus*.lean`.
- [ ] `git mv FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` to
      `MinusLanguageSoundness.lean`.
- [ ] Update every `import FormalSystem.BaseLanguage*` and `import FormalSystem.Semantics.BL*`
      line, including in `FormalSystem/FormalSystem.lean`, `Semantics.lean`,
      `Metalogic/Conservativity.lean`.
- [ ] Rename `namespace FormalSystem.BaseLanguage` / `end FormalSystem.BaseLanguage` to
      `FormalSystem.MinusLanguage` at all 5 sites, and update all 126 `BaseLanguage.`-qualified
      uses and every `open FormalSystem.BaseLanguage`.
- [ ] `git mv FormalSystem/MinusLanguage/README.md` content unchanged for now (prose lands in
      Phase 7).

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 126 `BaseLanguage.`-qualified uses across the tree and 5 namespace-declaration
sites. Confirm with `grep -rn 'BaseLanguage' --include='*.lean' FormalSystem/ Tests/` immediately
before and after; the after-count outside `Boneyard/` must be 0.

**Files to modify**:
- `FormalSystem/BaseLanguage/` → `FormalSystem/MinusLanguage/` (5 `.lean` + `README.md`)
- `FormalSystem/BaseLanguage.lean` → `FormalSystem/MinusLanguage.lean`
- `FormalSystem/Semantics/BL{Frame,Truth,Validity,SchemaValidity}.lean` → `Minus*.lean`
- `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` → `MinusLanguageSoundness.lean`
- `FormalSystem/FormalSystem.lean`, `FormalSystem/Semantics.lean`,
  `FormalSystem/Metalogic/Conservativity.lean` — import lines
- the ~10 modules carrying `open FormalSystem.BaseLanguage` or `BaseLanguage.`-qualified uses

**Verification**:
- `lake build FormalSystem` green.
- `grep -rn 'BaseLanguage' --include='*.lean' FormalSystem/ Tests/ | grep -v Boneyard` returns
  nothing.
- `bash scripts/check-module-invariants.sh --no-build` green on C23, C24 and the aggregator
  convention (every `X/` has exactly one sibling `X.lean`).
- `git diff --stat` shows renames only; no hunk touches a proof term.

---

### Phase 3: L⁻ declarations and notation [COMPLETED]

**Goal**: Rename all 63 BL-family declarations to their `Minus`/`minus` forms and the `⊢ᴮᴸ`
notation to `⊢⁻`.

**Tasks**:
- [ ] Rename `BLFormula` → `MinusFormula`, including its `namespace BLFormula` block.
- [x] Rename the semantics family: `BLTruthAt`, `BLFrame`, `BLFrameTruth`, `BLFrameValid`,
      `BLValid*`, `BLValidIn*`, `BLValidOnFrames*`, `BLValidZTime*`, `BLValidDense`,
      `BLValidRTime`, `BLSemanticConsequence`, `BLSetConsequenceOnFrames`,
      `BLSetSemanticConsequenceOn`, `TaskFrame.BLValidOn` → `Minus*` forms.
- [ ] Rename the lowercase family: `blValid*`, `blFrameValid_*`, `blTruthAt_timeShift`,
      `blCompact*`, `blSetConsequence*`, `bl_soundness*`, `bl_not_derivable_nil_bot*`,
      `bl_box_universal`, `bl_derivable_valid_and_swap_valid_zTimeSucc`, `BLCompact` →
      `minus*`/`minus_*`/`MinusCompact` forms.
- [ ] Change notation `⊢ᴮᴸ[` → `⊢⁻[` at both sites in `MinusLanguage/Derivation.lean` and every
      use site.
- [ ] Assert `grep -rn '⊢ᴮᴸ' FormalSystem/ Tests/ | grep -v Boneyard` returns nothing.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 63 declarations and 1287 occurrences. Confirm with the two commands in the
Measured surface table before and after; the after-count of the BL pattern outside `Boneyard/`
must be 0. Rename longest-name-first to avoid prefix-shadowing (`BLValidIn` before `BLValid`).

**Files to modify**:
- `FormalSystem/MinusLanguage/*.lean`, `FormalSystem/Semantics/Minus*.lean`,
  `FormalSystem/Metalogic/Conservativity/{MinusLanguageSoundness,Fragment,FragmentCompactness,Backward,SpWitness,SpCountermodel,Z1Countermodel,TMCompletenessReduction}.lean`
  and the remaining modules the Phase 1 inventory names

**Verification**:
- `lake build FormalSystem` green.
- Zero live occurrences of any of the 63 old names (`grep` per name, from the inventory).
- `git diff` contains no hunk that changes a tactic, term, or proof structure — only identifiers.
- If any rename forced a proof edit, the phase STOPS and the site is reported as a defect.

---

### Phase 4: tm-family split (TM⁻ vs TM) [COMPLETED]

**Goal**: Move every `tm`-prefixed name that denotes the H/G system onto its `tmMinus` form,
leaving `TMFrag`, `tmFrag_*` and every S/U-denoting `tm` name alone.

**Tasks**:
- [ ] Rename `TMComplete`, `TMCompleteBase`, `TMCompleteZTime`, `tmComplete_iff_forward`,
      `tmComplete_iff_tmFrag_le_tm`, `tmCompleteBase_iff_forwardBase`, `tmCompleteBase_refuted`,
      `tmCompleteDense_iff_forwardDense`, `tmCompleteRTime_iff_forwardRTime`,
      `tmCompleteZTime_iff_forwardZTime`, `tmCompleteZTime_refuted` → `TMMinusComplete*` /
      `tmMinusComplete*` forms.
- [ ] Rename `tm_le_tmFrag` → `tmMinus_le_tmFrag`, `tm_lt_tmFrag_ztime` →
      `tmMinus_lt_tmFrag_ztime`.
- [ ] Rename `tmFrag_iff_blValidIn` → `tmFrag_iff_minusValidIn` (suffix only; the `tmFrag_` prefix
      stays).
- [ ] Leave `TMFrag`, `tmFrag_sound`, `tmFrag_complete*`, `tmFrag_z1_ztime`, `tmFrag_iff_star`
      (renamed in Phase 6) as they are.
- [ ] Confirm no `tm` name that denotes the S/U system was renamed, by reading each renamed
      declaration's statement.

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 23 tm-family declarations, of which ~14 are renamed and ~9 (the `tmFrag_`
family plus `TMFrag`) are deliberately kept. Confirm the keep/rename split by reading each
declaration's statement — the test is whether the statement quantifies over `MinusFormula`
(rename) or `Formula` (keep) — and record the split in the phase notes.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/{Fragment,TMCompletenessReduction,SpWitness,SpCountermodel}.lean`
  and the further modules the Phase 1 inventory names

**Verification**:
- `lake build FormalSystem` green.
- Zero live occurrences of the old `tmComplete*` / `tm_le_tmFrag` / `tm_lt_tmFrag_ztime` names.
- `TMFrag` and `tmFrag_sound` still exist unrenamed.

---

### Phase 5: L⁺ structural layer — directories, aggregators, modules, namespaces [COMPLETED]

**Goal**: Move the ⊡-extension's files and namespace onto the `Plus` names, freeing
`StarLanguage/` entirely. Declaration names untouched in this phase.

**Tasks**:
- [ ] `git mv FormalSystem/StarLanguage FormalSystem/PlusLanguage` and
      `git mv FormalSystem/StarLanguage.lean FormalSystem/PlusLanguage.lean`.
- [ ] `git mv FormalSystem/Metalogic/Conservativity/Star FormalSystem/Metalogic/Conservativity/Plus`
      and `Conservativity/Star.lean` → `Conservativity/Plus.lean`; rename
      `Conservativity/Plus/StarSoundness.lean` → `PlusSoundness.lean`.
- [ ] `git mv` the five `Semantics/Star*.lean` files to `Semantics/Plus*.lean`.
- [ ] Update every `import FormalSystem.StarLanguage*`, `import ...Conservativity.Star*` and
      `import FormalSystem.Semantics.Star*` line, including `FormalSystem/FormalSystem.lean`,
      `Semantics.lean`, `Metalogic/Conservativity.lean`.
- [ ] Rename `namespace FormalSystem.StarLanguage` / `end` at all 3 sites and update all 16
      `StarLanguage.`-qualified uses and every `open FormalSystem.StarLanguage`.

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 16 `StarLanguage.`-qualified uses, 3 namespace-declaration sites, 5 Semantics
file moves, 4 `Conservativity/Star/` file moves. Confirm with
`grep -rn 'StarLanguage\|Conservativity.Star' --include='*.lean' FormalSystem/ Tests/` before and
after; the after-count outside `Boneyard/` must be 0.

**Files to modify**:
- `FormalSystem/StarLanguage/` → `FormalSystem/PlusLanguage/` (3 `.lean` + `README.md`)
- `FormalSystem/StarLanguage.lean` → `FormalSystem/PlusLanguage.lean`
- `FormalSystem/Metalogic/Conservativity/Star/` → `Plus/` (4 `.lean` + `README.md`),
  `Conservativity/Star.lean` → `Plus.lean`
- `FormalSystem/Semantics/Star{Truth,Validity,Pasting,NonValidities,Determinism}.lean` → `Plus*.lean`
- `FormalSystem/FormalSystem.lean`, `FormalSystem/Semantics.lean`,
  `FormalSystem/Metalogic/Conservativity.lean` — import lines
- `Metalogic/Independence/{StateSetTruth,DeterminismUndefinable,RealTranslationFrame}.lean` — `open` lines

**Verification**:
- `lake build FormalSystem` green.
- `grep -rn 'StarLanguage' --include='*.lean' FormalSystem/ Tests/ | grep -v Boneyard` returns
  nothing — the directory name is FREED for task 561.
- `bash scripts/check-module-invariants.sh --no-build` green on C23, C24 and the aggregator
  convention.

---

### Phase 6: L⁺ declarations and notation [COMPLETED]

**Goal**: Rename all 66 Star-family declarations to their `Plus`/`plus` forms, the `⊢⋆` notation
to `⊢⁺`, and resolve `ofPlus` per Decision 1.

**Tasks**:
- [ ] Rename `StarFormula` → `PlusFormula` (including its `namespace StarFormula` block),
      `StarAxiom` → `PlusAxiom`, `StarDerivationTree` → `PlusDerivationTree` (and its namespace),
      `StarDerivable` → `PlusDerivable`, `StarContext` → `PlusContext`.
- [ ] Rename `StarAxiom.ofPlus` → `PlusAxiom.ofTM`, `StarAxiom.minFrameClass_ofPlus` →
      `PlusAxiom.minFrameClass_ofTM`, `StarDerivationTree.ofPlus` → `PlusDerivationTree.ofTM`,
      `starValidIn_of_plus` → `plusValidIn_of_tm`, `starValidIn_swap_of_plus` →
      `plusValidIn_swap_of_tm` (Decision 1).
- [ ] Rename the semantics family: `StarTruthAt`, `starTruthAt_*`, `StarValid*`, `StarValidIn*`,
      `StarValidOnFrames*`, `StarValidDense`, `StarValidRTime`, `StarValidZTime`,
      `TaskFrame.StarValidOn`, `starValid*`, `starValidIn_*`, `starValidOn*` → `Plus*`/`plus*`.
- [ ] Rename the proof-theory family: `star_soundness*`, `star_backward_*`, `star_of_tm*` →
      `plus_of_tmMinus*`, `starDerivable_*`, `star_derivable_valid_and_swap_validIn`,
      `star_not_derivable_nil_bot`, `starAxiom_*`, `forward_star*` → `forward_plus*`.
- [ ] Rename the residual sites: `tmFrag_iff_star` → `tmFrag_iff_plus`,
      `deterministic_not_starDefinable` → `deterministic_not_plusDefinable`,
      `paste_starValid`/`snce_paste_starValid`/`untl_paste_starValid`/`stab_allFuture_starValid`/
      `future_dstab_starValid`/`fzero_starValidOn_iff_f1`/
      `stab_biconditional_starValidOn_of_deterministic` → their `plusValid` forms.
- [ ] Change notation `⊢⋆[` → `⊢⁺[` at both sites in `PlusLanguage/Derivation.lean` and every use
      site.
- [ ] Assert `grep -rn '⊢⋆\|TM⋆' FormalSystem/ Tests/ | grep -v Boneyard` returns nothing — both
      tokens FREED for task 561.
- [ ] Assert no `ofPlus`, `PlusPlus`, or `plus_of_plus` shape was produced.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: 66 declarations and 1457 occurrences. Confirm with the two commands in the
Measured surface table before and after; the after-count of the Star pattern outside `Boneyard/`
must be 0. Rename longest-name-first (`StarValidOnFrames` before `StarValid`).

**Files to modify**:
- `FormalSystem/PlusLanguage/*.lean`, `FormalSystem/Semantics/Plus*.lean`,
  `FormalSystem/Metalogic/Conservativity/Plus/*.lean`,
  `FormalSystem/Metalogic/Independence/{StateSetTruth,DeterminismUndefinable,RealTranslationFrame}.lean`,
  `FormalSystem/Metalogic/Conservativity/Fragment.lean`, and the remaining modules the Phase 1
  inventory names

**Verification**:
- `lake build FormalSystem` green.
- Zero live occurrences of any of the 66 old names, and zero of `StarFormula`, `StarAxiom`,
  `⊢⋆`, `TM⋆`.
- `git diff` contains no proof-term hunk. Any rename that forced one STOPS the phase and is
  reported as a defect.

---

### Phase 7: Docstrings in the renamed homes [NOT STARTED]

**Goal**: Rewrite the module and declaration docstrings in the L⁻ and L⁺ homes plus the semantics
and conservativity modules onto the new vocabulary, using Phase 1's per-site hand classification.

**Tasks**:
- [ ] Rewrite `FormalSystem/MinusLanguage.lean`'s module docstring: it currently says "the
      tense-primitive base language BL and its logic TM" and cites the bridge as
      `TM ⊢ φ ⟹ TM⁺ ⊢ tr φ`; the new statement is L⁻ / TM⁻ and `TM⁻ ⊢ φ ⟹ TM ⊢ tr φ`. Its
      "Module Invariant" paragraph names `BaseLanguage/` and `BLTruthAt` throughout.
- [ ] Rewrite `FormalSystem/PlusLanguage.lean`'s module docstring: "the language L⋆ and its logic
      TM⋆" becomes L⁺ / TM⁺; "L⁺ (`FormalSystem.Syntax.Formula`)" becomes "L
      (`FormalSystem.Syntax.Formula`)"; "the 45 TM⁺ schemata re-declared over `StarFormula`"
      becomes "the 45 TM schemata re-declared over `PlusFormula`".
- [ ] Rewrite the docstrings in `MinusLanguage/*.lean`, `PlusLanguage/*.lean`,
      `Semantics/Minus*.lean`, `Semantics/Plus*.lean`,
      `Metalogic/Conservativity/**.lean` — every site per its Phase 1 classification, re-read
      individually, never token-swapped.
- [ ] Rewrite `FormalSystem/MinusLanguage/README.md`, `FormalSystem/PlusLanguage/README.md`,
      `FormalSystem/Metalogic/Conservativity/README.md`,
      `FormalSystem/Metalogic/Conservativity/Plus/README.md`.
- [ ] Where a docstring relates a repo language to the paper, use the correspondence wording fixed
      in deliverable (4): the manuscript has exactly two languages, 𝓛 and 𝓛⋆; L⁻ has no manuscript
      counterpart; L⁺ is the ⊡-only fragment of 𝓛⋆; L⋆ is the time-register fragment of 𝓛⋆. Never
      imply a matching paper name.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: the docstring sites in these directories are a subset of the 80 `.lean`
files carrying old vocabulary; Phase 1's inventory names the exact set. Confirm the phase's file
list against that inventory before starting and record any file the inventory missed.

**Files to modify**:
- `FormalSystem/{MinusLanguage,PlusLanguage}.lean` and their directories' `.lean` + `README.md`
- `FormalSystem/Semantics/{Minus,Plus}*.lean`, `FormalSystem/Semantics/README.md`
- `FormalSystem/Metalogic/Conservativity/**` (`.lean` + both `README.md`)

**Verification**:
- Every changed hunk lies inside a `/-! -/`, `/-- -/` or `--` region, or inside a `.md` file — read
  the diff to confirm; no hunk crosses out of a comment boundary.
- `lake build FormalSystem` green (doc comments are load-bearing in Lean: a malformed `/--` breaks
  elaboration).
- No occurrence of `L⋆`/`TM⋆` in these files now denotes the ⊡-extension.

---

### Phase 8: Docstrings in the rest of the tree [NOT STARTED]

**Goal**: Rewrite the remaining `FormalSystem/` docstrings and in-tree READMEs onto the new
vocabulary.

**Tasks**:
- [ ] Rewrite the old-vocabulary docstring sites in `FormalSystem/{Syntax,ProofSystem,Theorems,Automation,Examples,ForMathlib}/**.lean`
      and `FormalSystem/{Metalogic,MainResults,FormalSystem,Init}.lean` and
      `FormalSystem/Metalogic/{Algebraic,Bundle,BXCanonical,Core,Decidability,Independence,SoundnessLemmas,WeakCanonical}/**`.
- [ ] Update `FormalSystem/Metalogic.lean`'s module docstring SORRY-FREE claim list, whose bullets
      name `bl_soundness*`, `star_soundness_validIn`, `starDerivable_ofFormula_iff` and the
      `tmComplete*` family — the names must match the C14 baseline Phase 12 edits.
- [ ] Rewrite `FormalSystem/README.md`, `FormalSystem/Metalogic/README.md`,
      `FormalSystem/Metalogic/Independence/README.md`.
- [ ] Leave `FormalSystem/Boneyard/` untouched.

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: this phase's file set is the complement of Phase 7's within the 80
old-vocabulary `.lean` files, plus 3 in-tree READMEs. Confirm the partition covers the inventory
exactly — no file in both phases, none in neither.

**Files to modify**:
- the complement set named above, per the Phase 1 inventory
- `FormalSystem/README.md`, `FormalSystem/Metalogic/README.md`,
  `FormalSystem/Metalogic/Independence/README.md`

**Verification**:
- Every changed hunk lies inside a comment or a `.md` file.
- `lake build FormalSystem` green.
- `grep -rn 'L⁺\|L⋆\|TM⁺\|TM⋆\|BL⁺\|BL⋆' --include='*.lean' FormalSystem/ | grep -v Boneyard`
  returns only sites whose new meaning is correct (each one checked against the inventory).

---

### Phase 9: Root and docs/ prose, and the four-language table [COMPLETED]

**Goal**: Deliverable (3) — rewrite the repository's user-facing documentation to the new
vocabulary, including one table stating the four languages, their operators, their logics and
their Lean homes.

**Tasks**:
- [ ] `README.md`: rewrite `### The base language L and the stability extension L⋆` (line ~204) and
      its five-row highlights table onto L / L⁻ / L⁺ / L⋆; RETIRE the divergence paragraph at line
      ~202 ("The system names on the two sides of the `⁺` are not the same family...") — after this
      task it is false; update the directory tree at lines ~110–111.
- [ ] Add the **four-language table** to `README.md` (the canonical statement; the other documents
      point at it rather than restating it):

      | Language | Operators | Logic | Lean home |
      |---|---|---|---|
      | L⁻ | ⊥, →, □, H, G | TM⁻ | `FormalSystem/MinusLanguage/`, `MinusFormula`, `⊢⁻[fc]` |
      | L | ⊥, →, □, S, U | TM (TM_z, TM_d, TM_r) | `FormalSystem/Syntax/`, `Formula`, `⊢[fc]` |
      | L⁺ | L plus ⊡ | TM⁺ | `FormalSystem/PlusLanguage/`, `PlusFormula`, `⊢⁺[fc]` |
      | L⋆ | L⁺ plus ↑ⁱ/↓ⁱ | (task 561) | `FormalSystem/StarLanguage/` — name reserved, not yet built |

- [ ] `NOTATION.md`: rewrite `### BL⁺, the base language` and `### TM⋆, the stability language`
      onto the new names and the new notation tokens `⊢⁻[fc]` / `⊢⁺[fc]`.
- [ ] `ORGANISATION.md`: update the layer-0 row (`Syntax/`, `ProofSystem/`, `StarLanguage/`,
      `ForMathlib/`).
- [ ] `docs/theorem-index.md`: rewrite the two language rows (lines ~43–44), including the "Name
      collision" note — after this task the collision is gone and the note is retired; update the
      five `bl_soundness*` / `bl_not_derivable_nil_bot` Lean-name rows and every other renamed Lean
      name.
- [ ] `docs/ARCHITECTURE.md`: the layer diagram (line ~46), the "Layer 0 is four modules" note
      (~77) and the `StarLanguage/` row (~84).
- [ ] `docs/user-guide/architecture.md`: the directory tree (~1082, ~1110).
- [ ] `docs/development/MODULE_ORGANIZATION.md`: the tree (~15–25), the layer list (~152–168) and
      the "Where `BaseLanguage` sits" paragraph.
- [ ] `docs/README.md`: the `TM` row of its vocabulary table (~38).
- [ ] `docs/development/NAMING_CONVENTION_DEVIATION.md`: the `BaseLanguage.Derivable` note (~104)
      and the `FormalSystem.BaseLanguage` note (~291).
- [ ] `docs/reference/API_REFERENCE.md`, `docs/project-info/implementation-status.md`,
      `docs/project-info/known-limitations.md`.
- [ ] `typst/FormalFoundations.typ`: the 15 old-name occurrences (~133, ~136, ~1186–1199 `TM⁺`;
      ~1275–1278 `BaseLanguage`). Do not regenerate `typst/generated/` by hand.
- [ ] Assert no task numbers were introduced under `FormalSystem/` or `docs/`.

**Timing**: 2 hours

**Depends on**: 7, 8

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: 4 root files (`README.md`, `NOTATION.md`, `ORGANISATION.md`, plus the
`CLAUDE.md` check), 9 `docs/` files and 1 `.typ` file. Confirm by re-running
`grep -rlE 'L⁺|L⋆|TM⁺|TM⋆|BL⁺|BL⋆|BaseLanguage|StarLanguage' --include='*.md' --include='*.typ' docs/ typst/ *.md`
before and after; the after-set must contain only files whose remaining occurrences are correct
under the new convention.

**Files to modify**:
- `README.md`, `NOTATION.md`, `ORGANISATION.md`
- `docs/README.md`, `docs/ARCHITECTURE.md`, `docs/theorem-index.md`,
  `docs/reference/API_REFERENCE.md`, `docs/user-guide/architecture.md`,
  `docs/development/{MODULE_ORGANIZATION,NAMING_CONVENTION_DEVIATION}.md`,
  `docs/project-info/{implementation-status,known-limitations}.md`
- `typst/FormalFoundations.typ`

**Verification**:
- `bash scripts/readme-lint.sh` green.
- The four-language table exists exactly once, in `README.md`; every other document points at it.
- `bash scripts/check-task-references.sh` (or the equivalent lint) reports no task number under
  `FormalSystem/` or `docs/`.

---

### Phase 10: Re-pin specs/paper-definitions-of-record.md [COMPLETED]

**Goal**: Deliverable (4) — record the repo↔manuscript correspondence as PERMANENT, and keep C15
resolving.

**Tasks**:
- [ ] Add a new dated section following the file's own "Vocabulary alignment (2026-09-07): prose
      only, no re-pin" precedent, stating: the manuscript has exactly **two** languages, 𝓛 and 𝓛⋆,
      where 𝓛⋆ bundles ⊡ with both the time-store/recall and world-store/recall families
      (line-independent anchor: the sentence defining `\BL^\star` in `\S sub:Extension`).
- [ ] State that `def:BLplus-language` and `def:TMplus` keep their anchor labels and now correspond
      to this repository's **L** and **TM** — exactly as the paper's own content already says.
- [ ] State, as a PERMANENT correspondence and not a pending one: this repository's **L⁻** has no
      manuscript counterpart (the H/G fragment was withdrawn from the paper — task 548's record);
      its **L⁺** is the ⊡-only fragment of the manuscript's 𝓛⋆; its **L⋆** is the time-register
      fragment of the manuscript's 𝓛⋆.
- [ ] Determine whether the prose written in Phases 7–9 cites any `def:`/`thm:`/`lem:`/`cor:`/
      `app:`/`rmk:` anchor that has no MANIFEST or KNOWN-ANCHORS row (e.g. `def:BLstar-semantics`).
      Add a `LIVE-UNPINNED` KNOWN-ANCHORS row for each, with a reason. Note `sub:Extension` uses the
      `sub:` prefix, which C15's pattern does not match — it needs no row.
- [ ] Follow the file's own "How to extend this record" rule: this is a prose-and-classification
      change, so **no `verbatim:` block, no `sha256:` line, no manifest row, and neither the
      `PINNED_COMMIT` nor the `FILE_CHECKSUM` sentinel is touched** unless a drift correction is
      actually being absorbed.
- [ ] Re-run `bash scripts/check-paper-definitions.sh` and record its case (a)/(b) verdict and its
      drifted-anchor set in the new section, as every prior section does.

**Timing**: 1 hour

**Depends on**: 9

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: zero new MANIFEST rows and at most a handful of new KNOWN-ANCHORS rows.
Confirm by diffing the C15 cited-anchor set (the script's own `C15_CITED` computation) before and
after Phases 7–9; every anchor newly appearing must have a row.

**Files to modify**:
- `specs/paper-definitions-of-record.md`

**Verification**:
- `bash scripts/check-module-invariants.sh --no-build` reports C15 green.
- `bash scripts/check-paper-definitions.sh` verdict recorded verbatim in the new section.
- No sentinel line (`PINNED_COMMIT`, `FILE_CHECKSUM`, `LINE_COUNT`) changed, unless a genuine drift
  correction was absorbed and is documented as such.

---

### Phase 11: Re-word the dependent open task descriptions [COMPLETED]

**Goal**: Deliverable (5) — tasks 534, 537, 559, 560 and 561 name the new identifiers, so they are
written once rather than twice.

**Tasks**:
- [ ] For each of `project_number` 534, 537, 559, 560, 561 in `specs/state.json`, rewrite the
      `description` field's old-vocabulary occurrences to the new names, re-reading each sentence
      rather than token-swapping (the same L⁺-ambiguity applies here).
- [ ] Update task 561's description to state that `StarLanguage/`, `StarFormula`, `StarAxiom`,
      `StarDerivationTree`, `⊢⋆[fc]` and TM⋆ are now FREE and are the names it should claim.
- [ ] Do not edit `specs/TODO.md` directly; run `bash .claude/scripts/generate-todo.sh` to
      regenerate it from `specs/state.json`.
- [ ] Do not change any task's `status`, `dependencies`, or `artifacts`.

**Timing**: 45 minutes

**Depends on**: 9

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: 69 old-vocabulary occurrences across the five descriptions (537: 26, 559: 14,
534: 10, 560: 10, 561: 9). Confirm with the `jq … [scan(…)] | length` measurement in the Measured
surface table before and after; the after-count must be 0 except where a description deliberately
records the rename itself.

**Files to modify**:
- `specs/state.json` (five `description` fields only)
- `specs/TODO.md` (regenerated, not hand-edited)

**Verification**:
- `jq empty specs/state.json` parses.
- The five descriptions carry no pre-rename identifier except where recording the rename.
- No other field of any task changed (`git diff specs/state.json` reviewed hunk by hunk).
- `specs/TODO.md` regenerated and consistent with `specs/state.json`.

---

### Phase 12: Full gate run and C14 baseline name update [NOT STARTED]

**Goal**: Deliverable (6) — `scripts/check-module-invariants.sh` fully green, with the C14 baseline
row NAMES updated and every axiom set unchanged.

**Tasks**:
- [ ] Update the ~24 rows in `scripts/check-module-invariants.sh`'s `C14_BASELINE` (`C14BASE`
      heredoc) that name renamed declarations: `bl_soundness{,_dense,_ztime,_rtime}`,
      `bl_not_derivable_nil_bot{,_ztime}`, `tmComplete_iff_forward`,
      `tmComplete{Base,ZTime,Dense,RTime}_iff_forward*`, `star_soundness_validIn`,
      `starDerivable_ofFormula_iff`, `Semantics.starValidIn_ofFormula_iff`,
      `deterministic_not_starDefinable`, plus any further row the Phase 1 inventory recorded.
- [ ] Apply the SAME edits, in the SAME order, to the `C14LEAN` heredoc — the two are compared by
      exact string equality. Diff the two declaration lists against each other before running.
- [ ] Change NAMES only. No axiom set on any row changes. If one does, that is a regression and a
      HARD STOP, not a new baseline.
- [ ] Confirm C2's four flagship rows (all `Metalogic.BXCanonical.*`) are untouched.
- [ ] Run `lake build` (full, not just `FormalSystem`) and `bash scripts/check-module-invariants.sh`
      with no flags.
- [ ] Confirm C2, C3, C14, C15, C23, C24, C26 and the aggregator convention are green; record the
      full output in the summary.
- [ ] Assert zero live occurrences of `StarLanguage`, `StarFormula`, `StarAxiom`,
      `StarDerivationTree`, `⊢⋆`, `TM⋆`, `BaseLanguage`, `BLFormula`, `⊢ᴮᴸ`, `BL⁺`, `BL⋆` outside
      `FormalSystem/Boneyard/` and outside `specs/**` (where historical artifacts are frozen).
- [ ] Assert zero `@[deprecated]` attributes naming any pre-rename identifier (Decision 2).
- [ ] Assert zero `sorry` (C3 covers this; re-state the result explicitly).

**Timing**: 1 hour

**Depends on**: 10, 11

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: ~24 C14 baseline rows require a name change. Confirm by grepping the
`C14BASE` and `C14LEAN` heredocs for each old name from the Phase 1 inventory and counting the
hits in each; the two counts must be equal.

**Files to modify**:
- `scripts/check-module-invariants.sh` (both C14 heredocs)

**Verification**:
- `lake build` green, zero warnings introduced.
- `bash scripts/check-module-invariants.sh` exits 0 with C2, C3, C14, C15, C23, C24 and C26 all
  reported PASS.
- The freed-name assertions above all return zero hits.

---

**Deviations recorded during execution**:
- Phase 3 gained an item the inventory did not anticipate: the `swapBL` family (13 tokens,
  83 occurrences — `swapBL`, `swapBL_involution`, `tr_swapBL`, the nine `MinusFormula.swapBL_*`
  simp lemmas, and `swapBL_df_valid_of_predOrder`) carries `BL` as a *suffix*, so the Phase 1
  token scan (anchored at `^` or `_`) missed it. Renamed to the `swapMinus` family in the same
  phase. *(deviation: altered — scope widened by 13 tokens)*
- Phases 3–6 share ONE `lake build FormalSystem` at the close of Phase 6 rather than one build
  each. *(deviation: altered — build cadence)* Forced by a concurrency collision with task 193,
  which was editing `Metalogic/SoundnessLemmas/FrameClassVariants.lean` and
  `Metalogic/Soundness.lean` throughout: two full builds were killed mid-run and a third failed
  on 193's own in-progress broken proof term, none of them on anything this task changed. Each
  phase's rename is instead verified by a **mechanical purity proof** — the phase-2 commit's
  content, put through this task's explicit token map, is byte-identical to the working tree for
  all 54 files this task owns. The two files where it is not identical
  (`Metalogic/Soundness.lean`, `SoundnessLemmas/FrameClassVariants.lean`) differ only by task
  193's `truth_norm` tactic edits, which this task did not make and does not commit.

## Lean Challenge Statements

This plan's Challenge-statement declaration set is **empty**, and so is the identifier set named
under `- **Goals**:` above — the two sets are therefore equal, as this document's format requires.

The emptiness is structural, not an omission: this task proves no theorem and declares nothing new.
It is a rename-and-prose sweep whose HARD CONSTRAINT is that no proof term changes, so there is no
statement for a Challenge module to pin. Every `- **Goals**:` bullet above names a rename or a
document rewrite; none names a theorem identifier to be proved. A snapshot tool run against this
plan should produce an empty module and report no mismatch.

## Testing & Validation

- [ ] `lake build FormalSystem` green at the close of every one of Phases 2–12.
- [ ] `lake build` (full, including `Tests/`) green at Phase 12.
- [ ] `bash scripts/check-module-invariants.sh` exits 0 with C2, C3, C14, C15, C23, C24, C26 and
      the aggregator convention all PASS.
- [ ] `bash scripts/check-paper-definitions.sh` run and its verdict recorded in
      `specs/paper-definitions-of-record.md`.
- [ ] `bash scripts/readme-lint.sh` green.
- [ ] Zero live occurrences of `StarLanguage`, `StarFormula`, `StarAxiom`, `StarDerivationTree`,
      `⊢⋆`, `TM⋆`, `BaseLanguage`, `BLFormula`, `⊢ᴮᴸ`, `BL⁺`, `BL⋆` outside `FormalSystem/Boneyard/`
      and `specs/**`.
- [ ] Zero `sorry` (C3).
- [ ] Zero proof-term changes: the cumulative `git diff` across Phases 2–6 contains no hunk that
      alters a tactic, a term, or a proof structure. Any that does is a reported defect.
- [ ] Zero task-number references introduced under `FormalSystem/` or `docs/`.
- [ ] `jq empty specs/state.json` parses and `specs/TODO.md` is regenerated, not hand-edited.

## Artifacts & Outputs

- `specs/562_sync_language_names_with_paper_l_minus_plus_star/plans/01_sync-language-names-paper.md`
  (this file)
- `specs/562_sync_language_names_with_paper_l_minus_plus_star/reports/01_rename-inventory.md`
  (deliverable 1, written in Phase 1)
- `specs/562_sync_language_names_with_paper_l_minus_plus_star/summaries/01_sync-language-names-paper-summary.md`
- The renamed tree: `FormalSystem/MinusLanguage/`, `FormalSystem/PlusLanguage/`,
  `FormalSystem/Metalogic/Conservativity/Plus/`, `FormalSystem/Semantics/{Minus,Plus}*.lean`
- Rewritten documentation: `README.md` (with the four-language table), `NOTATION.md`,
  `ORGANISATION.md`, six in-tree `README.md` files, nine `docs/` files,
  `typst/FormalFoundations.typ`
- `specs/paper-definitions-of-record.md` (deliverable 4)
- `specs/state.json` + regenerated `specs/TODO.md` (deliverable 5)
- `scripts/check-module-invariants.sh` (C14 baseline row names only)

## Rollback/Contingency

- Every phase is one commit (`atomic-batch` phases are exactly one; `per-substep` phases are a
  short run of green sub-step commits). Reverting a phase is `git revert` of its commit range —
  the tree is green before and after every phase boundary, so a revert lands on a green tree.
- Before Phase 2, take `bash .claude/scripts/git-snapshot.sh 562` so any destructive recovery is
  permitted by the guard hook.
- If a rename forces a proof edit (the HARD CONSTRAINT tripwire): stop the phase, revert only the
  offending identifier's rename, keep the rest of the phase, and report the site as a defect with
  the failing goal state. Do not edit the proof term.
- If task 557 lands concurrently on `Syntax/Formula.lean`,
  `Conservativity/TMCompletenessReduction.lean` or `Conservativity/DenseObstructionTransfer.lean`
  mid-task: stop at the current phase boundary (green), let 557 finish, rebase, and re-run the
  affected phase's assertion greps before continuing.
- If C14's two heredocs are found to have drifted apart after editing: restore both from `git
  show HEAD:scripts/check-module-invariants.sh` and redo the edit in a single pass over both
  blocks.
