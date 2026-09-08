# Rename Worklist (frozen scope for Phases 2-9)

- **Task**: 557 - burn_down_invisible_snake_case_public_defs
- **Produced by**: Phase 1 (Baseline measurement and frozen worklist)
- **Status**: frozen — later phases consume this list; they do not re-derive scope

## Scan commands (authoritative)

```
# public
grep -rnE "^\s*(noncomputable )?(protected )?(def|abbrev) [A-Za-z][A-Za-z0-9']*_" FormalSystem/ --include=*.lean | grep -v /Boneyard/
# private
grep -rnE "^\s*private (noncomputable )?def [A-Za-z][A-Za-z0-9']*_" FormalSystem/ --include=*.lean | grep -v /Boneyard/
```

## Measured scope vs. the plan's and the description's hypotheses

| Population | Description | Plan (Phase 1 Scope Hypothesis) | **Measured now** |
|---|---|---|---|
| Public snake_case `def`/`abbrev` outside `Boneyard/` | 71 | 71 | **75** |
| Private snake_case `def` outside `Boneyard/` | 47 (13 files) | 103 (20 files) | **103** (20 files) |
| Total | 118 | 174 | **178** |

The public count is **75, not 71**. The four extra matches are all in the `## Usage` fenced `lean` code block of the `FormalSystem/Syntax.lean` module docstring (`necessity_p`, `future_q`,
`possibly_p`, `always_p` at lines 61-66) — documentation examples, not elaborated declarations,
exactly as Phase 1's last task anticipated. They are carried in this worklist as
documentation-consistency renames so the Phase 10 acceptance scan comes back empty; the count of
real, elaborated public declarations is 71, matching both the description and the plan.

The private count is **103 across 20 files**, confirming the plan's re-measurement and refuting
the description's 47 across 13 files. The seven files the description omits entirely:

- `FormalSystem/Metalogic/WeakCanonical/IntegerModel/ShiftAndGlue.lean` (4)
- `FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/SubBracket2.lean` (2)
- `FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/CarrierKv.lean` (1)
- `FormalSystem/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean` (2)
- `FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleMonadicBridge.lean` (2)
- `FormalSystem/Metalogic/Bundle/WitnessSeed.lean` (2)
- `FormalSystem/Theorems/GeneralizedNecessitation.lean` (1)

Per-file private counts the description also understates: `PointInsertion.lean` 20 (not 2),
`StaviCompleteness.lean` 11 (not 7), `GoodStructuresModelSurgery.lean` 9 (not 1),
`TemporalDerived.lean` 10 (not 1), `FlowFrame.lean` 3 (not 1), `DeductionTheorem.lean` 3 (not 2),
`CustomGame.lean` 3 (matches). `Saturation.lean` 17, `Formula.lean` 5, `DatasetGenerator.lean` 4,
`Normalization.lean` 2 and `Perpetuity/Principles.lean` 1 match the description.

## Naming rule applied

Mechanical, per `docs/development/NAMING_CONVENTION_DEVIATION.md` ("The naming rule now in force"):
split on `_`; lowercase the first character of the first segment; upper-case the first character of
every later alphabetic segment; keep digit segments adjacent. Examples the plan pins:
`box_4_ctx` -> `box4Ctx`, `mp_chain_2` -> `mpChain2`, `until_F_ctx` -> `untilFCtx`,
`perpetuity_1` -> `perpetuity1`, `is_Z_type` -> `isZType`, `F_top_and_absorb` -> `fTopAndAbsorb`.

One documented deviation from the purely mechanical output, taken from the plan itself:
`sp_derivable_rtime` -> `spDerivableRTime` (not `spDerivableRtime`), following the `ZTime`/`RTime`
scheme's lowerCamel row.

## Collision probe

Probe run for every distinct target name: `grep -rlwF "<newName>" --include=*.lean FormalSystem/ Tests/`.
Eight target names produced hits; seven are **not** genuine collisions, and the evidence for each
is recorded below. One is genuine and is resolved with a longer descriptive name.

| Target | Hits | Verdict | Evidence |
|---|---|---|---|
| `spDerivableDense` | `DenseObstructionTransfer.lean:167` | not a collision | the sole hit is the file's own `### Naming exemption` prose, which *proposes* this very name; no declaration |
| `spDerivableRTime` | `DenseObstructionTransfer.lean:167` | not a collision | same line, same reason |
| `listConj` | `NormalForm.lean` (`MonadicFormula.listConj`) | not a collision | different namespace (`...WeakCanonical.MonadicFormula` vs `...BXCanonical.Chronicle`), and `PointInsertion` does **not** import `NormalForm` (transitive import closure computed; result False) |
| `sfDisj` | `CharacteristicFormula.lean:53` | not a collision | `StaviCompleteness` does **not** import `CharacteristicFormula` (transitive closure computed; result False), so the two short names never coexist in one environment |
| `sfDisjList` | `CharacteristicFormula.lean:58` | not a collision | same evidence |
| `sfConjList` | `CharacteristicFormula.lean:65` | not a collision | same evidence |
| `doubleNegation` | `Propositional/Core.lean:135` and 27 further files | not a collision | `Principles.lean` imports `Propositional.Core` transitively but its only `open`s are `FormalSystem.Syntax`, `FormalSystem.ProofSystem`, `FormalSystem.Theorems.Combinators` (lines 43-45) — `FormalSystem.Theorems.Propositional` is **not** opened, and both in-file uses of the private helper are unqualified while both references to the public one are written `Propositional.doubleNegation` |
| `ctxMp` | `Combinators.lean:678` | **GENUINE COLLISION** | `Combinators.ctxMp` is a public `def` with a byte-identical signature and body, `TemporalDerived.lean` imports `Theorems.Combinators` (line 9) **and** opens it (line 94), so an unqualified `ctxMp` inside `TemporalDerived` would have two live interpretations. **Resolved**: `ctx_mp` -> `ctxMpLocal` (recorded here, never left snake_case). Its sibling `ctx_thm` -> `ctxThm` is unaffected — the corresponding combinator is named `thmIn`, not `ctxThm` |

No within-file duplicate target was produced (checked: zero duplicates on the `file|target` key).
Two old names recur across files (`neg_imp_antecedent`, `neg_imp_neg_consequent`, each in both
`ChronicleMonadicBridge.lean` and `FlowFrame.lean`); both instances are `private` and live in
different namespaces, so both take the same mechanical target independently.

## Baselines (Phase 1, verbatim results)

| Gate | Command | Baseline |
|---|---|---|
| Full build | `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 --` | exit 0 (green) |
| Linter | `lake exe runLinter FormalSystem` | exit 0, `-- Linting passed for FormalSystem.` — **0 findings**, the measurement this task proves wrong by scan |
| Invariants | `bash scripts/check-module-invariants.sh` | exit 0, `ALL CHECKS PASSED` |
| Sorry census | `bash .claude/scripts/lean-sorry-census.sh FormalSystem/` | 162 census lines; **2** outside `Boneyard/` |
| Axioms | `grep -rn "^axiom " FormalSystem/ --include=*.lean \| wc -l` | **11** |
| Vacuous | single-line vacuous-definition grep over `FormalSystem/` | **1** |
| Dataset export | `lake exe proof_extractor` | `Registry size: 487 theorems`; `Theorems processed: 487/487`; `Total proof steps: 12077` |
| In-source nolint | `grep -rn "nolint defsWithUnderscore" FormalSystem/` | 2 sites: `DenseObstructionTransfer.lean:179` (to be deleted) and `UserTactics.lean:270` (the three documented tactic-token exemptions, out of scope) |
| `scripts/nolints.json` | `grep defsWithUnderscore` | no entries |

The linter reporting **0** while the scan reports **178** is the defect this task closes.

## The worklist

Format: `file | line | old name | new name`. Lines are as measured at freeze time; later phases
locate declarations by name, not by line.

### Public declarations (75)

```
FormalSystem/Syntax.lean                                                     61  necessity_p                  -> necessityP
FormalSystem/Syntax.lean                                                     62  future_q                     -> futureQ
FormalSystem/Syntax.lean                                                     65  possibly_p                   -> possiblyP
FormalSystem/Syntax.lean                                                     66  always_p                     -> alwaysP
FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean         122  sp_derivable_dense           -> spDerivableDense
FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean         146  sp_derivable_rtime           -> spDerivableRTime
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1359  nf_order_0_1                 -> nfOrder01
FormalSystem/Theorems/ContextualProofs.lean                                  73  identity_in_ctx              -> identityInCtx
FormalSystem/Theorems/ContextualProofs.lean                                  77  mp_in_context                -> mpInContext
FormalSystem/Theorems/ContextualProofs.lean                                  83  mp_chain_2                   -> mpChain2
FormalSystem/Theorems/ContextualProofs.lean                                  92  mp_chain_3                   -> mpChain3
FormalSystem/Theorems/ContextualProofs.lean                                 103  conj_proj_left               -> conjProjLeft
FormalSystem/Theorems/ContextualProofs.lean                                 107  conj_proj_right              -> conjProjRight
FormalSystem/Theorems/ContextualProofs.lean                                 111  apply_in_ctx                 -> applyInCtx
FormalSystem/Theorems/ContextualProofs.lean                                 120  weakened_axiom               -> weakenedAxiom
FormalSystem/Theorems/ContextualProofs.lean                                 124  ecq_computable               -> ecqComputable
FormalSystem/Theorems/ContextualProofs.lean                                 136  ldi_computable               -> ldiComputable
FormalSystem/Theorems/ContextualProofs.lean                                 151  rdi_computable               -> rdiComputable
FormalSystem/Theorems/ContextualProofs.lean                                 158  conj_intro_ctx               -> conjIntroCtx
FormalSystem/Theorems/ContextualProofs.lean                                 171  box_elim_ctx                 -> boxElimCtx
FormalSystem/Theorems/ContextualProofs.lean                                 177  box_4_ctx                    -> box4Ctx
FormalSystem/Theorems/ContextualProofs.lean                                 183  box_b_ctx                    -> boxBCtx
FormalSystem/Theorems/ContextualProofs.lean                                 190  box_to_diamond_ctx           -> boxToDiamondCtx
FormalSystem/Theorems/ContextualProofs.lean                                 202  k_dist_ctx                   -> kDistCtx
FormalSystem/Theorems/ContextualProofs.lean                                 213  box_pair_ctx                 -> boxPairCtx
FormalSystem/Theorems/ContextualProofs.lean                                 226  diamond_5_ctx                -> diamond5Ctx
FormalSystem/Theorems/ContextualProofs.lean                                 232  box_to_future_ctx            -> boxToFutureCtx
FormalSystem/Theorems/ContextualProofs.lean                                 245  temp_k_ctx                   -> tempKCtx
FormalSystem/Theorems/ContextualProofs.lean                                 253  connect_future_ctx           -> connectFutureCtx
FormalSystem/Theorems/ContextualProofs.lean                                 259  connect_past_ctx             -> connectPastCtx
FormalSystem/Theorems/ContextualProofs.lean                                 265  box_future_ctx               -> boxFutureCtx
FormalSystem/Theorems/ContextualProofs.lean                                 271  box_past_ctx                 -> boxPastCtx
FormalSystem/Theorems/ContextualProofs.lean                                 281  until_F_ctx                  -> untilFCtx
FormalSystem/Theorems/ContextualProofs.lean                                 288  since_P_ctx                  -> sincePCtx
FormalSystem/Theorems/ContextualProofs.lean                                 294  serial_future_ctx            -> serialFutureCtx
FormalSystem/Theorems/ContextualProofs.lean                                 309  mp_in_context_weak           -> mpInContextWeak
FormalSystem/Theorems/ContextualProofs.lean                                 313  mp_chain_2_weak              -> mpChain2Weak
FormalSystem/Theorems/ContextualProofs.lean                                 317  ecq_computable_weak          -> ecqComputableWeak
FormalSystem/Theorems/ContextualProofs.lean                                 321  box_elim_ctx_weak            -> boxElimCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 325  k_dist_ctx_weak              -> kDistCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 329  box_4_ctx_weak               -> box4CtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 333  box_b_ctx_weak               -> boxBCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 337  connect_future_ctx_weak      -> connectFutureCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 341  connect_past_ctx_weak        -> connectPastCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 345  until_F_ctx_weak             -> untilFCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 349  since_P_ctx_weak             -> sincePCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 353  identity_in_ctx_weak         -> identityInCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 357  apply_in_ctx_weak            -> applyInCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 361  conj_intro_ctx_weak          -> conjIntroCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 365  box_pair_ctx_weak            -> boxPairCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 370  box_future_ctx_weak          -> boxFutureCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 374  box_past_ctx_weak            -> boxPastCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 378  serial_future_ctx_weak       -> serialFutureCtxWeak
FormalSystem/Theorems/ContextualProofs.lean                                 389  identity_weakened            -> identityWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 393  b_combinator_weakened        -> bCombinatorWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 398  dni_weakened                 -> dniWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 402  connect_future_weakened      -> connectFutureWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 406  connect_past_weakened        -> connectPastWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 410  temp_future_weakened         -> tempFutureWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 415  pairing_weakened             -> pairingWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 419  modal_t_weakened             -> modalTWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 423  modal_4_weakened             -> modal4Weakened
FormalSystem/Theorems/ContextualProofs.lean                                 428  modal_b_weakened             -> modalBWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 432  modal_k_dist_weakened        -> modalKDistWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 437  ex_falso_weakened            -> exFalsoWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 441  prop_k_weakened              -> propKWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 446  prop_s_weakened              -> propSWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 450  until_F_weakened             -> untilFWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 454  since_P_weakened             -> sincePWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 458  serial_future_weakened       -> serialFutureWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 462  serial_past_weakened         -> serialPastWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 466  theorem_flip_weakened        -> theoremFlipWeakened
FormalSystem/Theorems/ContextualProofs.lean                                 471  theorem_app1_weakened        -> theoremApp1Weakened
FormalSystem/Theorems/Perpetuity/Principles.lean                             77  perpetuity_1                 -> perpetuity1
FormalSystem/Theorems/Perpetuity/Principles.lean                            308  perpetuity_2                 -> perpetuity2
```

### Private declarations (103)

```
FormalSystem/Metalogic/Core/DeductionTheorem.lean                            63  weaken_under_imp             -> weakenUnderImp
FormalSystem/Metalogic/Core/DeductionTheorem.lean                            71  weaken_under_imp_ctx         -> weakenUnderImpCtx
FormalSystem/Metalogic/Core/DeductionTheorem.lean                           221  deduction_with_mem           -> deductionWithMem
FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleMonadicBridge.lean    354  neg_imp_antecedent           -> negImpAntecedent
FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleMonadicBridge.lean    384  neg_imp_neg_consequent       -> negImpNegConsequent
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean            832  ex_falso_from_assumption     -> exFalsoFromAssumption
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean            980  conj_intro_curried           -> conjIntroCurried
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1195  and_left_impl                -> andLeftImpl
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1200  and_right_impl               -> andRightImpl
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1209  derivation_from_implied      -> derivationFromImplied
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1245  list_conj                    -> listConj
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1251  list_conj_implies_elem       -> listConjImpliesElem
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1320  untl_left_mono_deriv         -> untlLeftMonoDeriv
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1329  snce_left_mono_deriv         -> snceLeftMonoDeriv
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1338  untl_right_mono_deriv        -> untlRightMonoDeriv
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1347  snce_right_mono_deriv        -> snceRightMonoDeriv
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1427  iterated_enrichment          -> iteratedEnrichment
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1468  iterated_enrichment_since    -> iteratedEnrichmentSince
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1882  lemma_2_7_seed               -> lemma27Seed
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1891  l27_guard                    -> l27Guard
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1905  l27_collect_guards           -> l27CollectGuards
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           1923  l27_a_event_list             -> l27AEventList
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           2657  lemma_2_7_since_seed         -> lemma27SinceSeed
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           2661  l27s_c5_event_list           -> l27sC5EventList
FormalSystem/Metalogic/BXCanonical/Chronicle/PointInsertion.lean           2681  l27s_b5_guard_list           -> l27sB5GuardList
FormalSystem/Metalogic/WeakCanonical/NormalForm.lean                        178  normalForm_fintype_and_decEq -> normalFormFintypeAndDecEq
FormalSystem/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean    781  c5_forward_walk              -> c5ForwardWalk
FormalSystem/Metalogic/BXCanonical/Chronicle/CounterexampleElimination.lean   1498  c5_backward_walk             -> c5BackwardWalk
FormalSystem/Metalogic/Algebraic/FlowFrame.lean                             548  neg_imp_antecedent           -> negImpAntecedent
FormalSystem/Metalogic/Algebraic/FlowFrame.lean                             578  neg_imp_neg_consequent       -> negImpNegConsequent
FormalSystem/Metalogic/Algebraic/FlowFrame.lean                             604  past_tf_deriv                -> pastTfDeriv
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean         127  stavi_untl_fo                -> staviUntlFo
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean         181  stavi_snce_fo                -> staviSnceFo
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1306  sf_disj                      -> sfDisj
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1309  sf_disjList                  -> sfDisjList
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1317  sf_top                       -> sfTop
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1319  sf_conjList                  -> sfConjList
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1328  sf_atom_literal              -> sfAtomLiteral
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1384  nf_x_preds_sf                -> nfXPredsSf
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1397  nf_exist_sf_depth0           -> nfExistSfDepth0
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1467  nf_exist_sf                  -> nfExistSf
FormalSystem/Metalogic/WeakCanonical/EFGames/StaviCompleteness.lean        1517  nf_succ_sf                   -> nfSuccSf
FormalSystem/Metalogic/WeakCanonical/EFGames/CustomGame.lean                371  round_mono_emb               -> roundMonoEmb
FormalSystem/Metalogic/WeakCanonical/EFGames/CustomGame.lean               1178  restrict_emb_left            -> restrictEmbLeft
FormalSystem/Metalogic/WeakCanonical/EFGames/CustomGame.lean               1408  restrict_emb_right           -> restrictEmbRight
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    609  right_gap_class_prop         -> rightGapClassProp
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    691  is_Z_type                    -> isZType
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    700  good_sentence                -> goodSentence
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    768  good_formula_relativized     -> goodFormulaRelativized
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    785  good_rel_lifted              -> goodRelLifted
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    803  right_gap_class_formula      -> rightGapClassFormula
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean    959  gap_formula_R                -> gapFormulaR
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean   1042  contemp_eq_body              -> contempEqBody
FormalSystem/Metalogic/WeakCanonical/IntegerModel/GoodStructuresModelSurgery.lean   1186  spread_formula               -> spreadFormula
FormalSystem/Metalogic/WeakCanonical/IntegerModel/ShiftAndGlue.lean          28  choose_good_witness          -> chooseGoodWitness
FormalSystem/Metalogic/WeakCanonical/IntegerModel/ShiftAndGlue.lean          41  cofinal_pos_seq              -> cofinalPosSeq
FormalSystem/Metalogic/WeakCanonical/IntegerModel/ShiftAndGlue.lean          46  cofinal_neg_seq              -> cofinalNegSeq
FormalSystem/Metalogic/WeakCanonical/IntegerModel/ShiftAndGlue.lean          52  mk_cofinal_seq               -> mkCofinalSeq
FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/SubBracket2.lean    154  kvE_sub2_leftSlots           -> kvESub2LeftSlots
FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/SubBracket2.lean    162  kvE_sub2_rightSlots          -> kvESub2RightSlots
FormalSystem/Metalogic/WeakCanonical/Kamp/NfMultiAnchorBridge/CarrierKv.lean    161  kv_body                      -> kvBody
FormalSystem/Metalogic/Decidability/Saturation.lean                        1247  probe_p                      -> probeP
FormalSystem/Metalogic/Decidability/Saturation.lean                        1248  probe_q                      -> probeQ
FormalSystem/Metalogic/Decidability/Saturation.lean                        1251  probe_FGp                    -> probeFGp
FormalSystem/Metalogic/Decidability/Saturation.lean                        1253  probe_nGFp                   -> probeNGFp
FormalSystem/Metalogic/Decidability/Saturation.lean                        1255  probe_Upq                    -> probeUpq
FormalSystem/Metalogic/Decidability/Saturation.lean                        1257  probe_seed                   -> probeSeed
FormalSystem/Metalogic/Decidability/Saturation.lean                        1495  mt_p                         -> mtP
FormalSystem/Metalogic/Decidability/Saturation.lean                        1573  et_p                         -> etP
FormalSystem/Metalogic/Decidability/Saturation.lean                        1574  et_q                         -> etQ
FormalSystem/Metalogic/Decidability/Saturation.lean                        1575  et_r                         -> etR
FormalSystem/Metalogic/Decidability/Saturation.lean                        2355  fc_p                         -> fcP
FormalSystem/Metalogic/Decidability/Saturation.lean                        2457  pl_p                         -> plP
FormalSystem/Metalogic/Decidability/Saturation.lean                        2458  pl_r                         -> plR
FormalSystem/Metalogic/Decidability/Saturation.lean                        2524  an_p                         -> anP
FormalSystem/Metalogic/Decidability/Saturation.lean                        2525  an_q                         -> anQ
FormalSystem/Metalogic/Decidability/Saturation.lean                        2642  fa_p                         -> faP
FormalSystem/Metalogic/Decidability/Saturation.lean                        2644  fa_q                         -> faQ
FormalSystem/Metalogic/Bundle/WitnessSeed.lean                              151  allFuture_bot_imp_neg_deriv  -> allFutureBotImpNegDeriv
FormalSystem/Metalogic/Bundle/WitnessSeed.lean                              170  allPast_bot_imp_neg_deriv    -> allPastBotImpNegDeriv
FormalSystem/Theorems/GeneralizedNecessitation.lean                          55  temp_k_dist_local            -> tempKDistLocal
FormalSystem/Theorems/TemporalDerived.lean                                  135  neg_contrapositive_imp_neg   -> negContrapositiveImpNeg
FormalSystem/Theorems/TemporalDerived.lean                                  141  top_and_intro                -> topAndIntro
FormalSystem/Theorems/TemporalDerived.lean                                  156  F_neg_contra_imp_F_neg       -> fNegContraImpFNeg
FormalSystem/Theorems/TemporalDerived.lean                                  167  G_imp_to_G_contra            -> gImpToGContra
FormalSystem/Theorems/TemporalDerived.lean                                  175  G_contra_to_GK               -> gContraToGK
FormalSystem/Theorems/TemporalDerived.lean                                  205  dne_lift_F                   -> dneLiftF
FormalSystem/Theorems/TemporalDerived.lean                                  217  FF_to_F_top_and              -> fFToFTopAnd
FormalSystem/Theorems/TemporalDerived.lean                                  230  F_top_and_absorb             -> fTopAndAbsorb
FormalSystem/Theorems/TemporalDerived.lean                                  371  ctx_mp                       -> ctxMpLocal
FormalSystem/Theorems/TemporalDerived.lean                                  375  ctx_thm                      -> ctxThm
FormalSystem/Theorems/Perpetuity/Principles.lean                             54  double_negation              -> doubleNegation
FormalSystem/Automation/Normalization.lean                                  558  p_atom                       -> pAtom
FormalSystem/Automation/Normalization.lean                                  559  q_atom                       -> qAtom
FormalSystem/Automation/DatasetGenerator.lean                               970  p_test                       -> pTest
FormalSystem/Automation/DatasetGenerator.lean                               971  q_test                       -> qTest
FormalSystem/Automation/DatasetGenerator.lean                              1066  r_test                       -> rTest
FormalSystem/Automation/DatasetGenerator.lean                              1067  s_test                       -> sTest
FormalSystem/Syntax/Formula.lean                                            285  p_cmplx                      -> pCmplx
FormalSystem/Syntax/Formula.lean                                            286  q_cmplx                      -> qCmplx
FormalSystem/Syntax/Formula.lean                                            586  p_cmplx2                     -> pCmplx2
FormalSystem/Syntax/Formula.lean                                            587  q_cmplx2                     -> qCmplx2
FormalSystem/Syntax/Formula.lean                                            639  p_cmplx3                     -> pCmplx3
```
