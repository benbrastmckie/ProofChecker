# Phase 1 handoff — task 573

- **Next action**: Phase 2 (`FormalSystem/Semantics/StarNonValidities.lean`, the three refutations).
- **State**: `StarFormula.swapTemporal`, `swap_temporal_involution`, the `swap_temporal_*`
  push-through family (`top`, `neg`, `diamond`, `some_future`, `some_past`, `all_future`,
  `all_past`, `and`, `or`, `iff`, `dstab`, `timeStore`, `timeRecall`) and the pin
  `ofPlus_swapTemporal` are landed in `FormalSystem/StarLanguage/Formula.lean`; full `lake build`
  green.
- **Decisions**: `ofPlus_swapTemporal` is proved by structural induction, not `rfl` — the same
  shape `ofFormula_swapTemporal` uses. `swap_temporal_iff` was added beyond the plan's named list
  because every `.iff`-shaped register axiom's swap arm routes through it.
- **Deviations**: none.
