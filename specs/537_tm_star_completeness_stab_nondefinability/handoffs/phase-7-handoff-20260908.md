# Phases 6-7 handoff — task 537

- **Phase 6** (`Metalogic/Deterministic/System.lean`): `DetAxiom` (two arms: `ofPlus`,
  `determined`), `DetAxiom.minFrameClass`, `DetDerivationTree` (the same seven rules),
  `height`/`lift`/`ofWeakeningNil` and the two mp-height lemmas, `DetDerivable`,
  `DetDerivationTree.ofPlus` / `.determinedAxiom` / `.stabNecessitation` / `.ofTM` / `.ofTMSubst`,
  and the Prop-level `detDerivable_of_plusDerivable`, `detDerivable_of_derivable`,
  `detDerivable_substPlus`, `detDerivable_determined`. The live `PlusAxiom` is untouched.
- **Phase 7** (`Metalogic/Deterministic/Soundness.lean`): `detAxiom_validDeterminedIn`,
  `detAxiom_swap_validDeterminedIn`, the companion recursion
  `det_derivable_valid_and_swap_validDeterminedIn`, `detSoundness` (over the *Determined*-valid
  frames), `detSoundnessDet`, `detSoundnessIn`, and consistency `det_not_derivable_nil_bot`
  (witness `F¹`).
- **Next action**: Phase 8 — the syntactic collapse `detDerivable_iff_erasePlus`. The propositional
  glue will be imported from `Theorems/` via `detDerivable_substPlus` at reserved atoms; the
  modal and temporal congruences need no substitution, since `PlusAxiom.modal_k_dist`,
  `.left_mono_until_G`, `.right_mono_until`, `.left_mono_since_H`, `.right_mono_since` are already
  stated at arbitrary `PlusFormula` arguments.
