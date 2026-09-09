# Phases 11-12 handoff — task 537 — DELIVERABLE (3) LANDED

- **Phase 11a** (`Metalogic/Independence/NaiveSystem.lean`): `PlusAxiom.IsNaive`,
  `PlusDerivationTree.NaiveOnly`, `NaiveDerivable`, `naiveDerivable_imp_plusDerivable`,
  `NaiveDerivable.mono`, and the derived rules. No second axiom inductive: the naive system is a
  predicate on the existing trees, so `PlusAxiom` is untouched.
- **Phase 11b** (`Metalogic/Independence/CoarsenedModels.lean`): `CoarseModel`, `SameUnder`,
  `CTruthAt` and its clause lemmas; the three structural ports `c_truth_congr_ext`,
  `cTruthAt_timeShift`, `c_stab_state_only`; the atomization transfer `cTruthAt_iff_atomize` with
  `cValid_of_tm`/`cValid_swap_of_tm`; the six naive `⊡` validities; the two 53-arm dispatches
  `naiveAxiom_cValid`/`naiveAxiom_cValid_swap`; and naive soundness `naive_cValid` with its
  contrapositive `not_naiveDerivable_of_cRefuted`.
- **Phase 12** (`Metalogic/Independence/PastingIndependence.lean`): the model `pModel` (the
  deterministic clock over ℤ at family index `Unit`, coarsened by `|·|`), the truth calculus along
  a flow line, `pTotal_toHist`, and the two headline theorems `pasteNotNaiveDerivable`,
  `untlPasteNotNaiveDerivable`, plus `plusAxiomSetNonRedundant`.
- **Gate outcome**: Phase 11's explicit go/no-go gate PASSED — the atomization step closes,
  because the coarsened `⊡` is still a state formula.
- **Friction note**: `omega` does not see order hypotheses elaborated at `↑(TemporalOrder.of ℤ)`
  rather than at `ℤ`; the fix is to put the genuinely `ℤ`-typed operand first (`t > s`, not
  `s < t`) or to discharge closed numeric side conditions with `decide`.
- **Next action**: Phase 14 (documentation and invariants), then the summary.
