# Phases 3-5 handoff — task 537

- **Phase 3** (`Metalogic/Deterministic/Engines.lean`): `derivable_of_validDetBase`,
  `derivable_of_validDetDense`, `derivable_of_validDetZTime`, `derivable_of_validDetRTime`, each
  the parent engine's script with the countermodel's determinism component fed to the narrowed
  hypothesis. The `.ZTime` dense branch was factored out of `derivable_of_validZTime` as
  `BXCanonical.ztimeNextTop` (noncomputable — it routes through `deductionTheorem`).
- **Phase 4** (`Metalogic/Deterministic/Erasure.lean`): `erasePlus`, `erasePlus_ofFormula`,
  `erasePlus_swapTemporal`, `plusTruthAt_erasePlus_of_deterministic`, and the equivalidity
  corollary `plusValidDetIn_iff_validDetIn_erasePlus`.
- **Phase 5** (`PlusLanguage/Substitution.lean`): `substPlus`, `substCtxPlus`, `substPlus_atom`,
  `substPlus_swapTemporal`, `PlusAxiom.ofTMSubst` (45 arms), `PlusDerivationTree.ofTMSubst`,
  `plusDerivable_substPlus`. Scope hypothesis confirmed: exactly the 45 `Axiom` constructors
  `PlusAxiom.ofTM` covers.
- **Next action**: Phase 6 — the extended system `DetAxiom` / `DetDerivationTree` /
  `DetDerivable` in `Metalogic/Deterministic/System.lean`.
- **Deferred**: Phase 5's congruence audit is deferred into Phase 8 (annotated inline).
