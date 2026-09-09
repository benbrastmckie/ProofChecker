# Phases 8-9 handoff — task 537 — DELIVERABLE (1) LANDED

- **Phase 8** (`Metalogic/Deterministic/Collapse.lean`): the Prop-level rule layer (`detMp`,
  `detPlusAxiom`, `detNec`, `detTNec`, `detHNec`), six propositional theorems imported from
  `Theorems/` by `detDerivable_substPlus` at reserved atoms, the derived
  `detImpTrans`/`detIffIntro`/`detIffMp`/`detIffMpr`/`detIffRefl`/`detIffSymm`/`detIffTrans`, the
  four congruence rules, `detStabIff`, and the collapse `detDerivable_iff_erasePlus` plus the
  transport `detDerivable_of_derivable_erasePlus`.
- **Phase 9** (`Metalogic/Deterministic/Completeness.lean`): `detCompletenessBase/Dense/ZTime/RTime`,
  the uniform `detCompleteness`, the coincidence corollary
  `logicDeterministicEqDeterminedValid`, the intermediate-class transfers
  `detCompletenessBetween` / `logicBetweenEqDeterministic`, and the `⊡ = identity` row
  `detDerivable_iff_derivable_erasePlus`. `derivable_of_validDet` was added to `Engines.lean` as
  the uniform-in-`fc` form.
- **Verification**: scoped build clean; `#print axioms` for the four completeness rows and the
  coincidence corollary reports exactly `[propext, Classical.choice, Quot.sound]`.
- **Next action**: Phase 10 — `stabNotDefinable`, via `Semantics/Truth.lean`'s `TruthCorr` and
  `truthAt_of_truthCorr`.
