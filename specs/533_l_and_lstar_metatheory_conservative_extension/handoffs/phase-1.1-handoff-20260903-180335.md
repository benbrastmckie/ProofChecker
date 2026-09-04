# Phase 1.1 handoff — TMFrag landed

- **Next action**: Phase 1.2 (`Conservativity/FragmentCompactness.lean` + `Conservativity.lean` wiring).
- **State**: `FormalSystem/Metalogic/Conservativity/Fragment.lean` builds sorry-free (scoped guarded build green);
  `#print axioms tmFrag_iff_blValidIn` / `tm_lt_tmFrag_discrete` = propext, Classical.choice, Quot.sound.
- **Key decisions**: file imports `Conservativity.Z1Countermodel` (end of the child chain), namespace
  `FormalSystem.Metalogic.Conservativity`; `tm_lt_tmFrag_discrete` witnesses with `Z1 (.atom (Atom.mkBase "p"))`.
- **Build-guard note**: the guarded invocation is `lake-build-guard.sh build --timeout 1800 -- build <Module>`
  (the lake subcommand must follow `--`).
- **Deviations**: none.
