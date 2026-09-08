# Phase 1 Handoff (task 547)

- **Next action**: Phase 2 — write the canonical mapping paragraph into
  `FormalSystem/Metalogic/Conservativity.lean`'s module docstring and `docs/README.md`.
- **State**: baseline captured under `specs/547_.../baseline/`; build green; C14/C15 PASS;
  C9 pre-existing FAIL (unrelated file).
- **Key decision**: the paper's Past/Future footnote is commented out (`possible_worlds.tex:1331-1341`),
  so the mapping prose says the repository's `TM` side has no paper counterpart rather than
  identifying it with a footnote that is not live. Surfaced as a non-blocking `user_decision`.
- **Deviations**: `FormalSystem/README.md` line numbers differ from the plan's guess (same file,
  same count); baseline invariants exit 1 on pre-existing C9.
