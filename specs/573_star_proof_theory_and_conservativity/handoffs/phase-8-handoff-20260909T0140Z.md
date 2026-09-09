# Phase 5-8 handoff — task 573

- **Next action**: Phase 9 (documentation, metatheory rows, the completeness OPEN record).
- **State**: `StarLanguage/Embedding.lean` (`ofPlusTree`, `starDerivable_of_plusDerivable`,
  `starDerivable_of_derivable`); `Conservativity/Star/StarAxiomValidity.lean` (16 named
  `starValid_*` register lemmas + both dispatch lemmas, 17 arms each, no wildcard);
  `Conservativity/Star/StarSoundness.lean` (companion recursion, four rows, consistency);
  `Conservativity/Star/Forward.lean` (unconditional TM row + conditional TM⁺ pair);
  `Conservativity/Star.lean` aggregator wired into `Conservativity.lean`. All four compiled
  first-try; `lake build FormalSystem.Metalogic.Conservativity` green (2392 jobs).
- **Decisions**: `StarValidIn`'s binder-shape adapters were missing from
  `Semantics/StarValidity.lean` (its docstring claims them); rather than edit that shared file
  while task 572 is in flight, `starValidIn_of_forall_total` / `starValidIn_apply_total` are
  declared locally in `StarSoundness.lean`.
- **Remaining**: Phase 9 docs + `--emit-inventory` for the new Star/README.md block, then the
  full verification suite.
