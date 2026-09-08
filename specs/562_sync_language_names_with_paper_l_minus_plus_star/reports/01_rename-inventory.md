# Rename Inventory: Task #562

- **Task**: 562 - Sync language names with the paper (L⁻ / L / L⁺ / L⋆)
- **Type**: inventory (plan deliverable 1, Phase 1 output)
- **Date**: 2026-09-08
- **Plan**: `specs/562_sync_language_names_with_paper_l_minus_plus_star/plans/01_sync-language-names-paper.md`
- **Standards**: report-format.md, artifact-management.md

## Overview

This is the name-by-name mapping every later phase renames from. It re-derives the plan's
"Measured surface" figures, enumerates every declaration, module, namespace, notation and
prose-token site the rename touches, and classifies the ambiguous documentation sites.

## Re-derived surface (Phase 1 Scope Hypothesis check)

| Surface | Plan hypothesis | Measured | Delta |
|---|---|---|---|
| BL-family declarations | 63 | **63** | 0 |
| Star-family declarations | 66 | **66** | 0 |
| tm-family declarations | 23 | **23** | 0 |
| Distinct BL/Star tokens tree-wide (incl. module names, excl. false positives) | — | **142** | new figure |
| `.lean` files carrying old vocabulary (identifiers or prose tokens) | 80 | **55** | −31% |
| `.lean` files carrying a renamed *identifier* | — | **47** | new figure |
| `Tests/` files carrying old vocabulary | 0 | **0** | 0 |
| Markdown files carrying old vocabulary (outside `specs/`) | 20 | **20** | 0 |
| `typst/FormalFoundations.typ` | in scope | **in scope** | 0 |
| `check-module-invariants.sh` C14 rows naming renamed declarations | ~24 | **17 per heredoc** (34 lines total) | −29% |

Two figures differ from the plan by more than 10% and are re-scoped here rather than absorbed
silently:

1. **`.lean` files carrying old vocabulary: 55, not 80.** The plan's 80 came from a union grep
   whose BL/Star patterns also matched `BLOCK`/`BLOCKED`/`BLOCKER` (16 hits), the bare word
   `Star` in module paths, `α_star` local hypothesis names in
   `Metalogic/BXCanonical/Chronicle/PointInsertion.lean`, and `_start`/`_block` substrings. The
   corrected figure re-scopes Phases 7 and 8: their combined file set is 55, of which 47 carry a
   renamed identifier and 8 carry only prose tokens.
2. **C14 baseline rows: 17 per heredoc, not ~24.** Counted directly at
   `scripts/check-module-invariants.sh` lines 1396–1400, 1414–1419, 1433–1434, 1437–1439, 1449
   (`C14BASE`) and their `#print axioms` twins at 1503–1507, 1521–1526, 1540–1541, 1544–1546,
   1556 (`C14LEAN`), plus one prose comment at line 1345 that names
   `Semantics.starValidIn_ofFormula_iff`. Phase 12 is re-scoped to 17 + 17 + 1 = 35 lines.

## False positives excluded from every rename rule

These tokens match a naive `bl`/`BL`/`star`/`Star` pattern but MUST NOT be renamed. A blanket
`sed` would corrupt them; two of them sit inside proof terms.

| Token | Occurrences | Why excluded |
|---|---|---|
| `BLOCK`, `BLOCKED`, `BLOCKER` | 16 | Ordinary English in comments; `BL` is not a prefix here |
| `_star`, `_star_A` | 40 | Fragments of `α_star` / `hα_star_A`, **local hypothesis names inside proof terms** in `Metalogic/BXCanonical/Chronicle/PointInsertion.lean` (lines 3375–3376, 3532–3533). Renaming these would be a proof-term edit, which this task forbids |
| bare `BL` | 326 | Prose name of the H/G language; becomes `L⁻` in the *prose* phases, never by identifier rule |
| bare `Star` | 32 | Module-path component (`Conservativity.Star`, `Star.lean`, `Star/`); handled by the structural phases |
| bare `star` | 12 | Prose (`star-language`, `L-star` in Paper: lines); handled by the prose phases |
| `_ble`, `_blo`, `_start` substrings | 583 | Ordinary words (`derivable`, `block`, `interval_start`) |
| `TMCompletenessReduction` | module | Distinct token from `TMComplete`; the module keeps its name |
| `TMFrag`, `tmFrag_sound`, `tmFrag_complete*`, `tmFrag_z1_ztime` | — | Deliberately kept (plan (e)): `TMFrag fc φ := TM ⊢[fc] tr φ` is literally true after the rename |
| `FrameClass.Base`, `ForwardBase`, `ForwardZTime` | — | Frame-class tags and the `Forward` proposition family; not languages |

**Consequence for method**: no phase may use a pattern-based `sed`. Every rename below is applied
as an **exact whole-token substitution** from the tables in this report, longest-token-first.

## Structural moves (Phases 2 and 5)

### Directories

| Old | New |
|---|---|
| `FormalSystem/BaseLanguage/` | `FormalSystem/MinusLanguage/` |
| `FormalSystem/StarLanguage/` | `FormalSystem/PlusLanguage/` (name FREED for the genuine L⋆) |
| `FormalSystem/Metalogic/Conservativity/Star/` | `FormalSystem/Metalogic/Conservativity/Plus/` |

### Files (13 `.lean` + 3 `README.md`)

| Old | New |
|---|---|
| `FormalSystem/BaseLanguage.lean` | `FormalSystem/MinusLanguage.lean` |
| `FormalSystem/BaseLanguage/{Axioms,AxiomDischarge,Derivation,Formula,Translation}.lean` | `FormalSystem/MinusLanguage/…` (names unchanged inside) |
| `FormalSystem/BaseLanguage/README.md` | `FormalSystem/MinusLanguage/README.md` |
| `FormalSystem/Semantics/BLFrame.lean` | `FormalSystem/Semantics/MinusFrame.lean` |
| `FormalSystem/Semantics/BLTruth.lean` | `FormalSystem/Semantics/MinusTruth.lean` |
| `FormalSystem/Semantics/BLValidity.lean` | `FormalSystem/Semantics/MinusValidity.lean` |
| `FormalSystem/Semantics/BLSchemaValidity.lean` | `FormalSystem/Semantics/MinusSchemaValidity.lean` |
| `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | `…/MinusLanguageSoundness.lean` |
| `FormalSystem/StarLanguage.lean` | `FormalSystem/PlusLanguage.lean` |
| `FormalSystem/StarLanguage/{Axioms,Derivation,Formula}.lean` | `FormalSystem/PlusLanguage/…` |
| `FormalSystem/StarLanguage/README.md` | `FormalSystem/PlusLanguage/README.md` |
| `FormalSystem/Semantics/Star{Truth,Validity,Pasting,NonValidities,Determinism}.lean` | `FormalSystem/Semantics/Plus{…}.lean` |
| `FormalSystem/Metalogic/Conservativity/Star.lean` | `FormalSystem/Metalogic/Conservativity/Plus.lean` |
| `FormalSystem/Metalogic/Conservativity/Star/{Atomization,AxiomValidity,Forward}.lean` | `…/Plus/…` |
| `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` | `…/Plus/PlusSoundness.lean` |
| `FormalSystem/Metalogic/Conservativity/Star/README.md` | `…/Plus/README.md` |

### Namespaces and module paths

| Old | New | Sites |
|---|---|---|
| `FormalSystem.BaseLanguage` | `FormalSystem.MinusLanguage` | 5 `namespace`/`end` pairs, 126 qualified uses, all `open` lines |
| `FormalSystem.StarLanguage` | `FormalSystem.PlusLanguage` | 3 `namespace`/`end` pairs, 16 qualified uses, all `open` lines |
| `FormalSystem.Metalogic.Conservativity.Star` | `…Conservativity.Plus` | 4 `import` lines + aggregator |
| `FormalSystem.Semantics.BL*` / `.Star*` | `.Minus*` / `.Plus*` | `import` lines in `Semantics.lean` and consumers |

The repo aggregator convention (`X/` has exactly one sibling `X.lean`) is preserved by moving
each directory together with its sibling aggregator in the same commit.

### Notation

| Old | New | Declaration site |
|---|---|---|
| `Γ ⊢ᴮᴸ[fc] φ` | `Γ ⊢⁻[fc] φ` | `BaseLanguage/Derivation.lean:162` |
| `⊢ᴮᴸ[fc] φ` | `⊢⁻[fc] φ` | `BaseLanguage/Derivation.lean:165` |
| `Γ ⊢⋆[fc] φ` | `Γ ⊢⁺[fc] φ` | `StarLanguage/Derivation.lean:165` |
| `⊢⋆[fc] φ` | `⊢⁺[fc] φ` | `StarLanguage/Derivation.lean:168` |
| `Γ ⊢[fc] φ`, `⊢[fc] φ` | unchanged | now reads as TM, which is what it always meant to the paper |

`⊢ᴮᴸ` occurs in 7 files (31 occurrences); `⊢⋆` in 3 files.

## Declaration mapping

### L⁻ family: 67 tokens (`BL*` / `bl*` / `bl_*` → `Minus*` / `minus*` / `minus_*`)

| Old | New |
|---|---|
| `BLCompact` | `MinusCompact` |
| `BLFormula` | `MinusFormula` |
| `BLFrame` | `MinusFrame` |
| `BLFrameTruth` | `MinusFrameTruth` |
| `BLFrameValid` | `MinusFrameValid` |
| `BLSchemaValidity` | `MinusSchemaValidity` |
| `BLSemanticConsequence` | `MinusSemanticConsequence` |
| `BLSetConsequenceOnFrames` | `MinusSetConsequenceOnFrames` |
| `BLSetSemanticConsequenceOn` | `MinusSetSemanticConsequenceOn` |
| `BLTruth` | `MinusTruth` |
| `BLTruthAt` | `MinusTruthAt` |
| `BLValid` | `MinusValid` |
| `BLValidComplete` | `MinusValidComplete` |
| `BLValidDense` | `MinusValidDense` |
| `BLValidIn` | `MinusValidIn` |
| `BLValidOn` | `MinusValidOn` |
| `BLValidOnFrames` | `MinusValidOnFrames` |
| `BLValidRTime` | `MinusValidRTime` |
| `BLValidZTime` | `MinusValidZTime` |
| `BLValidZTimeSucc` | `MinusValidZTimeSucc` |
| `BLValidity` | `MinusValidity` |
| `_blValidRTime` | `_minusValidRTime` |
| `_blValidZTime` | `_minusValidZTime` |
| `blCompactBase` | `minusCompactBase` |
| `blCompactDense` | `minusCompactDense` |
| `blCompact_of_compact` | `minusCompact_of_compact` |
| `blFrameValid_of_` | `minusFrameValid_of_` |
| `blFrameValid_of_axiom` | `minusFrameValid_of_axiom` |
| `blFrameValid_of_derivation` | `minusFrameValid_of_derivation` |
| `blSetConsequenceOnFrames_iff_image` | `minusSetConsequenceOnFrames_iff_image` |
| `blSetConsequence_iff_image` | `minusSetConsequence_iff_image` |
| `blTruthAt_timeShift` | `minusTruthAt_timeShift` |
| `blValidIn_iff_validIn_tr` | `minusValidIn_iff_validIn_tr` |
| `blValidOnFrames_iff_validOnFrames_tr` | `minusValidOnFrames_iff_validOnFrames_tr` |
| `blValidZTime_iff_validZTime_tr` | `minusValidZTime_iff_validZTime_tr` |
| `blValidZTime_z1` | `minusValidZTime_z1` |
| `blValid_df_or_dn` | `minusValid_df_or_dn` |
| `blValid_iff_blValidIn_base` | `minusValid_iff_minusValidIn_base` |
| `blValid_iff_empty_consequence` | `minusValid_iff_empty_consequence` |
| `blValid_iff_valid_tr` | `minusValid_iff_valid_tr` |
| `blValid_implies_blValidDense` | `minusValid_implies_minusValidDense` |
| `blValid_implies_blValidRTime` | `minusValid_implies_minusValidRTime` |
| `blValid_implies_blValidZTime` | `minusValid_implies_minusValidZTime` |
| `blValid_implies_blValidZTimeSucc` | `minusValid_implies_minusValidZTimeSucc` |
| `blValid_sp` | `minusValid_sp` |
| `bl_box_universal` | `minus_box_universal` |
| `bl_derivable_valid_and_swap_valid_zTimeSucc` | `minus_derivable_valid_and_swap_valid_zTimeSucc` |
| `bl_not_derivable_nil_bot` | `minus_not_derivable_nil_bot` |
| `bl_not_derivable_nil_bot_ztime` | `minus_not_derivable_nil_bot_ztime` |
| `bl_soundness` | `minus_soundness` |
| `bl_soundness_dense` | `minus_soundness_dense` |
| `bl_soundness_dense_valid` | `minus_soundness_dense_valid` |
| `bl_soundness_in` | `minus_soundness_in` |
| `bl_soundness_rtime` | `minus_soundness_rtime` |
| `bl_soundness_rtime_valid` | `minus_soundness_rtime_valid` |
| `bl_soundness_valid` | `minus_soundness_valid` |
| `bl_soundness_validIn` | `minus_soundness_validIn` |
| `bl_soundness_ztime` | `minus_soundness_ztime` |
| `bl_soundness_ztime_succ` | `minus_soundness_ztime_succ` |
| `bl_soundness_ztime_succ_valid` | `minus_soundness_ztime_succ_valid` |
| `bl_soundness_ztime_valid` | `minus_soundness_ztime_valid` |
| `not_blValidDense_of_not_chainSat` | `not_minusValidDense_of_not_chainSat` |
| `not_blValidDense_z1` | `not_minusValidDense_z1` |
| `not_blValidIn_of_not_chainSat` | `not_minusValidIn_of_not_chainSat` |
| `not_blValidRTime_of_not_chainSat` | `not_minusValidRTime_of_not_chainSat` |
| `not_bl_derivable_z1` | `not_minus_derivable_z1` |
| `tmFrag_iff_blValidIn` | `tmFrag_iff_minusValidIn` |

### L⁺ family: 76 tokens (`Star*` / `star*` / `star_*` → `Plus*` / `plus*` / `plus_*`)

| Old | New |
|---|---|
| `StarAxiom` | `PlusAxiom` |
| `StarContext` | `PlusContext` |
| `StarDerivable` | `PlusDerivable` |
| `StarDerivationTree` | `PlusDerivationTree` |
| `StarDeterminism` | `PlusDeterminism` |
| `StarFormula` | `PlusFormula` |
| `StarLanguage` | `PlusLanguage` |
| `StarNonValidities` | `PlusNonValidities` |
| `StarPasting` | `PlusPasting` |
| `StarSoundness` | `PlusSoundness` |
| `StarTruth` | `PlusTruth` |
| `StarTruthAt` | `PlusTruthAt` |
| `StarValid` | `PlusValid` |
| `StarValidDense` | `PlusValidDense` |
| `StarValidIn` | `PlusValidIn` |
| `StarValidOn` | `PlusValidOn` |
| `StarValidOnFrames` | `PlusValidOnFrames` |
| `StarValidRTime` | `PlusValidRTime` |
| `StarValidZTime` | `PlusValidZTime` |
| `StarValidity` | `PlusValidity` |
| `_starValid` | `_plusValid` |
| `deterministic_not_starDefinable` | `deterministic_not_plusDefinable` |
| `forward_star` | `forward_plus` |
| `forward_star_base` | `forward_plus_base` |
| `forward_star_dense` | `forward_plus_dense` |
| `forward_star_rtime` | `forward_plus_rtime` |
| `forward_star_ztime` | `forward_plus_ztime` |
| `future_dstab_starValid` | `future_dstab_plusValid` |
| `fzero_starValidOn_iff_f1` | `fzero_plusValidOn_iff_f1` |
| `paste'_starValid` | `paste'_plusValid` |
| `paste_starValid` | `paste_plusValid` |
| `snce_paste_starValid` | `snce_paste_plusValid` |
| `stab_allFuture_starValid` | `stab_allFuture_plusValid` |
| `stab_biconditional_starValidOn_of_deterministic` | `stab_biconditional_plusValidOn_of_deterministic` |
| `starAxiom_swap_validIn` | `plusAxiom_swap_validIn` |
| `starAxiom_swap_validIn_min` | `plusAxiom_swap_validIn_min` |
| `starAxiom_validIn` | `plusAxiom_validIn` |
| `starAxiom_validIn_min` | `plusAxiom_validIn_min` |
| `starDerivable_ofFormula_iff` | `plusDerivable_ofFormula_iff` |
| `starDerivable_ofFormula_iff_base` | `plusDerivable_ofFormula_iff_base` |
| `starDerivable_ofFormula_iff_dense` | `plusDerivable_ofFormula_iff_dense` |
| `starDerivable_ofFormula_iff_rtime` | `plusDerivable_ofFormula_iff_rtime` |
| `starDerivable_ofFormula_iff_ztime` | `plusDerivable_ofFormula_iff_ztime` |
| `starDerivable_of_derivable` | `plusDerivable_of_derivable` |
| `starTruthAt_iff_atomize` | `plusTruthAt_iff_atomize` |
| `starTruthAt_iff_mem_satSet` | `plusTruthAt_iff_mem_satSet` |
| `starTruthAt_ofCtx` | `plusTruthAt_ofCtx` |
| `starTruthAt_ofFormula` | `plusTruthAt_ofFormula` |
| `starTruthAt_timeShift` | `plusTruthAt_timeShift` |
| `starValidIn_ofFormula_iff` | `plusValidIn_ofFormula_iff` |
| `starValidIn_of_plus` | `plusValidIn_of_tm` |
| `starValidIn_swap_of_plus` | `plusValidIn_swap_of_tm` |
| `starValidOnFrames_ofFormula_iff` | `plusValidOnFrames_ofFormula_iff` |
| `starValidOn_iff_satSet_univ` | `plusValidOn_iff_satSet_univ` |
| `starValid_ofFormula_iff` | `plusValid_ofFormula_iff` |
| `star_backward_base` | `plus_backward_base` |
| `star_backward_dense` | `plus_backward_dense` |
| `star_backward_rtime` | `plus_backward_rtime` |
| `star_backward_ztime` | `plus_backward_ztime` |
| `star_derivable_valid_and_swap_validIn` | `plus_derivable_valid_and_swap_validIn` |
| `star_not_derivable_nil_bot` | `plus_not_derivable_nil_bot` |
| `star_of_tm` | `plus_of_tmMinus` |
| `star_of_tm_base` | `plus_of_tmMinus_base` |
| `star_of_tm_dense` | `plus_of_tmMinus_dense` |
| `star_of_tm_rtime` | `plus_of_tmMinus_rtime` |
| `star_of_tm_ztime` | `plus_of_tmMinus_ztime` |
| `star_soundness_base` | `plus_soundness_base` |
| `star_soundness_dense` | `plus_soundness_dense` |
| `star_soundness_in` | `plus_soundness_in` |
| `star_soundness_rtime` | `plus_soundness_rtime` |
| `star_soundness_valid` | `plus_soundness_valid` |
| `star_soundness_validIn` | `plus_soundness_validIn` |
| `star_soundness_ztime` | `plus_soundness_ztime` |
| `tmFrag_iff_star` | `tmFrag_iff_plus` |
| `minFrameClass_ofPlus` | `minFrameClass_ofTM` |
| `ofPlus` | `ofTM` |

### tm family: 13 tokens (H/G-denoting `tm` names → `tmMinus` forms)

| Old | New |
|---|---|
| `TMComplete` | `TMMinusComplete` |
| `TMCompleteBase` | `TMMinusCompleteBase` |
| `TMCompleteZTime` | `TMMinusCompleteZTime` |
| `tmCompleteBase_iff_forwardBase` | `tmMinusCompleteBase_iff_forwardBase` |
| `tmCompleteBase_refuted` | `tmMinusCompleteBase_refuted` |
| `tmCompleteDense_iff_forwardDense` | `tmMinusCompleteDense_iff_forwardDense` |
| `tmCompleteRTime_iff_forwardRTime` | `tmMinusCompleteRTime_iff_forwardRTime` |
| `tmCompleteZTime_iff_forwardZTime` | `tmMinusCompleteZTime_iff_forwardZTime` |
| `tmCompleteZTime_refuted` | `tmMinusCompleteZTime_refuted` |
| `tmComplete_iff_forward` | `tmMinusComplete_iff_forward` |
| `tmComplete_iff_tmFrag_le_tm` | `tmMinusComplete_iff_tmFrag_le_tmMinus` |
| `tm_le_tmFrag` | `tmMinus_le_tmFrag` |
| `tm_lt_tmFrag_ztime` | `tmMinus_lt_tmFrag_ztime` |

### tm names deliberately KEPT (read each statement to confirm)

| Name | Statement quantifies over | Verdict |
|---|---|---|
| `TMFrag` | `BLFormula`, body `ProofSystem.Derivable fc [] (tr φ)` | KEEP — the `TM` in it is the S/U system |
| `tmFrag_sound`, `tmFrag_complete{,_base,_dense,_ztime,_rtime}` | `TMFrag` ↔ `BLValidIn` | KEEP (prefix); the `_iff_blValidIn` suffix moves |
| `tmFrag_z1_ztime` | `TMFrag FrameClass.ZTime (Z1 …)` | KEEP |
| `Forward`, `ForwardBase`, `ForwardZTime` | `BaseLanguage.Derivable` | KEEP — `Forward` names the conservativity direction, not a logic |
| `FrameClass.Base` | frame-class tag | KEEP (plan (e)) |

### Keep/rename split evidence for the tm family

- `TMComplete fc : ∀ φ : BLFormula, BLValidIn fc φ → BaseLanguage.Derivable fc [] φ`
  (`TMCompletenessReduction.lean:211`) — conclusion is `BaseLanguage.Derivable`, i.e. the H/G
  system. **RENAME** to `TMMinusComplete`. `TMCompleteBase`, `TMCompleteZTime` and the five
  `tmComplete*_iff_forward*` rows are instantiations of it and follow.
- `tm_le_tmFrag : BaseLanguage.Derivable fc [] φ → TMFrag fc φ` (`Fragment.lean:142`) — the
  `tm` is the H/G system. **RENAME** to `tmMinus_le_tmFrag`.
- `tm_lt_tmFrag_ztime` (`Fragment.lean:161`) — both sides quantify over `BaseLanguage.Derivable`.
  **RENAME**.
- `tmComplete_iff_tmFrag_le_tm` (`Fragment.lean:176`) — the trailing `_tm` unfolds to
  `BaseLanguage.Derivable`. **RENAME both ends** to `tmMinusComplete_iff_tmFrag_le_tmMinus`.
- `star_of_tm : BaseLanguage.Derivable fc [] φ → StarDerivable fc [] (ofFormula (tr φ))`
  (`Star/Forward.lean:133`) — the `tm` is the H/G system. **RENAME** to `plus_of_tmMinus`.
- `tmFrag_sound`, `tmFrag_complete` take `TMFrag`/`BLValidIn` — the `tmFrag` prefix denotes the
  S/U-derivability-of-the-translation fragment. **KEEP**.

Split: **13 renamed, 10 kept** of the 23 tm-family declarations.

## Decision 1 confirmed: `ofPlus` → `ofTM`

`ofPlus` has 22 occurrences, all inside `StarLanguage/{Axioms,Derivation,Formula}.lean` and
`StarLanguage.lean`, and all denote the embedding of the S/U (`Axiom` / `DerivationTree`)
schemata into the ⊡-extension. After the rename `Plus` names the ⊡-extension itself, so
`PlusAxiom.ofPlus` would be self-referential nonsense. `ofBase` is rejected because `Base` is a
live frame-class tag (`FrameClass.Base`). The three sites take `ofTM`:

- `StarAxiom.ofPlus` → `PlusAxiom.ofTM`
- `StarAxiom.minFrameClass_ofPlus` → `PlusAxiom.minFrameClass_ofTM`
- `StarDerivationTree.ofPlus` → `PlusDerivationTree.ofTM`

and the two Atomization helpers follow the same rule:

- `starValidIn_of_plus` (52 occurrences) → `plusValidIn_of_tm`
- `starValidIn_swap_of_plus` (50 occurrences) → `plusValidIn_swap_of_tm`

Post-rename assertion for Phase 6: zero occurrences of `ofPlus`, `PlusPlus`, `plus_of_plus`,
`plusAxiom_ofPlus`.

## Prose-token inventory and hand classification

### Current meaning of each decorated token (verified by reading every declaring site)

| Token | Occurrences (`.lean` / `.md`+`.typ`) | What it denotes TODAY | New token |
|---|---|---|---|
| `L⁺` | 153 / 163 | the S/U language `Formula` | `L` |
| `BL⁺` | 82 / 83 | the S/U language `Formula` (older spelling of the same thing) | `L` |
| `TM⁺` | 163 / 212 | the S/U proof system `ProofSystem.Derivable` | `TM` |
| `L⋆` | 107 / 115 | the ⊡-extension `StarFormula` | `L⁺` |
| `TM⋆` | 106 / 123 | the ⊡ proof system `StarDerivable` | `TM⁺` |
| bare `BL` | 326 / — | the H/G language `BLFormula` | `L⁻` |
| bare `TM` | ambiguous | **hand-read at every site** | `TM` or `TM⁻` |
| `L⁻`, `TM⁻`, `BL⋆` | 0 | — | (introduced by this task) |

The five decorated tokens each have exactly ONE meaning in the current tree — this was checked
against every site, not assumed. They may therefore be rewritten as a **simultaneous**
(single-pass, alternating) substitution; a *sequential* one would collapse `L⋆ → L⁺ → L`. Bare
`TM` and bare `L` are ambiguous and are read individually.

### Sites whose sentence STRUCTURE must change (not a token swap)

These are the sites that relate a repo language to the paper, or that contrast two or three
languages in one sentence. Each is rewritten by hand in Phases 7–9 using the deliverable-(4)
correspondence wording.

| Site | Current claim | Required rewrite |
|---|---|---|
| `README.md` ~202 | "The system names on the two sides of the `⁺` are not the same family…" | RETIRE — false after this task |
| `README.md` ~204 | `### The base language L and the stability extension L⋆` + 5-row table | Rewrite to the four-language table (canonical, stated once) |
| `docs/theorem-index.md` ~43–44 | two language rows + a "Name collision" note | Rewrite rows; RETIRE the collision note |
| `FormalSystem/StarLanguage/Formula.lean:27` | "L⋆ here is L⁺ plus `⊡` only. The paper's own `\BL^\star` (line 1374) additionally…" | Rewrite: repo `L⁺` is the ⊡-only fragment of the manuscript's 𝓛⋆; cite `sub:Extension`, not a line number |
| `FormalSystem/Metalogic/Conservativity.lean:30–32` | "**`TM⁺` is the paper's `TM`.**… Its extensions `TM⁺_z`, `TM⁺_d`, `TM⁺_r` are the paper's `TM_z`, …" | Becomes a statement that the names now coincide; the "divergence" framing is retired |
| `FormalSystem/Metalogic/Conservativity.lean:216` | "the other extension direction, L⁺ ⊂ L⋆ (L⁺ plus the paper's stability modal `⊡`, line 1114…)" | `L ⊂ L⁺`; replace the line number with `sub:Extension` |
| `FormalSystem/Metalogic/Conservativity/Fragment.lean:74` | "Since `TM⁺` is the paper's `TM` (`def:TMplus`…)" | "`TM` is the paper's `TM` (`def:TMplus`)" |
| `FormalSystem/Metalogic/Conservativity/Star.lean:18` | "under the seven rules of TM⁺. Its semantics is the paper's `($\Stability$)` clause" | `TM`; the ⊡ clause is `def:BLstar-semantics` |
| `FormalSystem/ProofSystem/Axioms.lean:501` | "is therefore the paper's **TM⁺_r**" | The paper has no `TM⁺_r`; the correct name is `TM_r` |
| `FormalSystem/Semantics/FrameClassValidity.lean:42` | "`.RTime` is the paper's TM⁺_r class" | `TM_r` |
| `FormalSystem/Semantics/Validity.lean:689` | "paper's notation and `TM⁺_r` in this tree's" | The two notations now coincide; the contrast is retired |
| `FormalSystem/Metalogic/Conservativity/Backward.lean:150` | "`TM⁺_r` is the paper's `TM_r`" | Same-name statement, or retire the sentence |
| `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean:31` | "`BX_z` and `TM⁺_z`" | `TM_z` |
| `FormalSystem/StarLanguage.lean:15` | "L⁺ (`FormalSystem.Syntax.Formula`) extended by the paper's **stability modal** `⊡`" | "L (`FormalSystem.Syntax.Formula`) extended by …" |
| `NOTATION.md` | `### BL⁺, the base language` / `### TM⋆, the stability language` | Both headings and their notation tokens |
| `ORGANISATION.md` | layer-0 row naming `StarLanguage/` | `PlusLanguage/`, with `StarLanguage/` noted as reserved |

Full per-site line listings for the 361 `.lean` and 104 `.md`/`.typ` decorated-token sites were
generated during this phase and are re-derived by:

```
grep -rn -E 'L⁺|L⋆|TM⁺|TM⋆|BL⁺' --include='*.lean' FormalSystem/ | grep -v Boneyard
grep -rn -E 'L⁺|L⋆|TM⁺|TM⋆|BL⁺' --include='*.md' --include='*.typ' \
  README.md NOTATION.md ORGANISATION.md docs/ FormalSystem/ typst/
```

### Documentation files in scope (20, outside `specs/`)

Root (3): `README.md`, `NOTATION.md`, `ORGANISATION.md`.
`docs/` (9): `README.md`, `ARCHITECTURE.md`, `theorem-index.md`, `reference/API_REFERENCE.md`,
`user-guide/architecture.md`, `development/MODULE_ORGANIZATION.md`,
`development/NAMING_CONVENTION_DEVIATION.md`, `project-info/implementation-status.md`,
`project-info/known-limitations.md`.
In-tree `README.md` (8): `FormalSystem/`, `FormalSystem/Semantics/`,
`FormalSystem/BaseLanguage/`, `FormalSystem/StarLanguage/`, `FormalSystem/Metalogic/`,
`FormalSystem/Metalogic/Conservativity/`, `FormalSystem/Metalogic/Conservativity/Star/`,
`FormalSystem/Metalogic/Independence/`.
Plus `typst/FormalFoundations.typ`.

## `scripts/check-module-invariants.sh` C14 rows (Phase 12)

17 rows in `C14BASE` (lines 1396–1400, 1414–1419, 1433–1434, 1437–1439, 1449), their 17
`#print axioms` twins in `C14LEAN` (1503–1507, 1521–1526, 1540–1541, 1544–1546, 1556), and one
prose comment at line 1345. Old → new NAME only; **no axiom set on any row changes**:

| Baseline row (old) | New |
|---|---|
| `FormalSystem.Metalogic.tmComplete_iff_forward` | `…tmMinusComplete_iff_forward` |
| `FormalSystem.Metalogic.tmCompleteBase_iff_forwardBase` | `…tmMinusCompleteBase_iff_forwardBase` |
| `FormalSystem.Metalogic.tmCompleteZTime_iff_forwardZTime` | `…tmMinusCompleteZTime_iff_forwardZTime` |
| `FormalSystem.Metalogic.tmCompleteDense_iff_forwardDense` | `…tmMinusCompleteDense_iff_forwardDense` |
| `FormalSystem.Metalogic.tmCompleteRTime_iff_forwardRTime` | `…tmMinusCompleteRTime_iff_forwardRTime` |
| `FormalSystem.Metalogic.bl_soundness{,_dense,_ztime,_rtime}` | `…minus_soundness{,_dense,_ztime,_rtime}` |
| `FormalSystem.Metalogic.bl_not_derivable_nil_bot{,_ztime}` | `…minus_not_derivable_nil_bot{,_ztime}` |
| `FormalSystem.Metalogic.Conservativity.tm_le_tmFrag` | `…tmMinus_le_tmFrag` |
| `FormalSystem.Metalogic.Conservativity.tm_lt_tmFrag_ztime` | `…tmMinus_lt_tmFrag_ztime` |
| `FormalSystem.Metalogic.Conservativity.star_soundness_validIn` | `…plus_soundness_validIn` |
| `FormalSystem.Metalogic.Conservativity.starDerivable_ofFormula_iff` | `…plusDerivable_ofFormula_iff` |
| `FormalSystem.Semantics.starValidIn_ofFormula_iff` | `…plusValidIn_ofFormula_iff` |
| `FormalSystem.Metalogic.Independence.deterministic_not_starDefinable` | `…deterministic_not_plusDefinable` |

C2's four flagship rows are all `FormalSystem.Metalogic.BXCanonical.*` and are **untouched**.

## `docs/theorem-index.md` rows whose Lean name changes

Every `bl_soundness*`, `bl_not_derivable_nil_bot*`, `tmComplete*`, `star_soundness*`,
`starDerivable_*`, `starValidIn_*` and `deterministic_not_starDefinable` row, plus the two
language rows and the "Name collision" note. Re-derived in Phase 9 by grepping the file against
the three mapping tables above.

## Non-`.lean` consumers of renamed identifiers

| File | What it names |
|---|---|
| `scripts/check-module-invariants.sh` | the 17 C14 baseline rows + 17 `#print axioms` twins + 1 comment |
| `typst/FormalFoundations.typ` | `TM⁺` occurrences (~1186–1199) and `BaseLanguage` (~1275–1278) |
| `specs/state.json` | the five open task descriptions (534, 537, 559, 560, 561) — Phase 11 |

`Tests/` carries **no** old vocabulary; `lake-manifest.json`, `lakefile.lean` and
`scripts/module-invariants-manifest.txt` were checked and carry none.

## Verification of this phase

- `git status` shows no change under `FormalSystem/`, `docs/`, `typst/` or the repository root.
- Every declaration in the three families has a new name; there are no `TBD` rows.
- Every ambiguous prose site is classified: the five decorated tokens by a verified one-meaning
  rule, and the 16 structure-change sites individually by hand in the table above.
