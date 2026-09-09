# Phase 2 handoff — task 573

- **Next action**: Phase 3 (`FormalSystem/StarLanguage/Axioms.lean`, `StarAxiom` +
  `StarAxiom.minFrameClass`).
- **State**: `mfWitness`, `refute_modal_future`, `storeG_recall_valid`, `refute_erasure` landed in
  `FormalSystem/Semantics/StarNonValidities.lean`; scoped build green (993 jobs).
- **Decisions**: the Scope Hypothesis (three refutations + one witness = four declarations) held
  exactly; no fourth REJECT-table refutation was added, since none was needed by a later phase.
  `storeG_recall_valid` closes via `Function.update_self` plus `StarTruth.atom_iff` on both
  sides rather than `simpa`, because the atom clause's vector-independence is a definitional
  unfold that `simpa` will not perform.
- **Deviations**: none.
- **Build-invocation note**: the guard requires the lake subcommand after `--`
  (`lake-build-guard.sh build --timeout 1800 -- build [Module]`); the bare `-- ` form exits 77
  without building.
