# Phase 3 handoff

- **Next action**: Phase 4 — add `not_blValidIn_of_not_chainSat` plus the ℚ and ℝ
  instantiations to `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean`.
  All three are already elaborated green via `lean_run_code`; the ℝ half needs
  `import Mathlib.Algebra.Order.Archimedean.Real.Basic` and the `FrameClass.Sat .RTime`
  witness `⟨inferInstance, fun _ hne hbdd => Real.exists_isLUB hne hbdd⟩`, the same term
  `Metalogic/DedekindNonCompactness.lean` already uses. Both instantiations need an explicit
  `(fc := …)` — the `BLValidDense`/`BLValidRTime` `def`s do not unfold soon enough to
  determine the metavariable.
- **State**: Phases 1–3 [COMPLETED] and committed. `lake build FormalSystem.Metalogic.Conservativity`
  green; `check-module-invariants.sh` ALL CHECKS PASSED; zero `sorry` added.
- **Key decisions**: `chainSat`'s `box` clause takes no time argument (universal over both
  coordinates), per `bl_box_universal`. Phase 2's `sp_derivable_*` keep the plan's exact
  `DerivationTree`-valued signatures, with a documented `nolint defsWithUnderscore` exemption
  rather than a `Prop`-valued restatement.
- **Deviations so far**: annotated inline on the plan's Phase 1 and Phase 2 checklists.
