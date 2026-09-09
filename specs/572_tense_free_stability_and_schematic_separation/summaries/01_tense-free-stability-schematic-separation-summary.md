# Implementation Summary: Task #572

- **Task**: 572 - Tense-free stability and schematic separation
- **Status**: [COMPLETED]
- **Started**: 2026-09-09T00:06:55Z
- **Completed**: 2026-09-09T00:00:00Z
- **Effort**: ~4 hours
- **Dependencies**: Task 571 (schematic `Det-pm`) — `[COMPLETED]`
- **Artifacts**: plans/01_tense-free-stability-schematic-separation.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The strong structural result the task gated everything on **holds**, and holds more strongly than
the description anticipated. `FormalSystem/Semantics/StarStateLocal.lean` defines the
**state-locality** fragment of L⋆ by structural recursion, proves it sound against the semantic
property, exhibits a countermodel for each excluded constructor, and lands the headline
`φ ↔ ⊡φ`. With that in hand the atom restriction on the forward-determinism separation is
retired: `fn_sentDet_atom` is deleted and replaced by `fn_sentDet_stateLocal`, `fn_separates` is
strengthened in place, and `fn_sentDet_bounds` records the two-sided bound as one machine-checked
object. The refutations `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` are byte-for-byte
unchanged.

## What Changed

- `FormalSystem/Semantics/StarStateLocal.lean` — **new**. `StarFormula.StateLocal` (syntactic,
  nine clauses); `IsStateLocal` (semantic); `isStateLocal_box` and `isStateLocal_stab` (both for
  an **arbitrary** argument); `isStateLocal_of_stateLocal` (the soundness induction);
  `not_isStateLocal_someFuture` / `not_isStateLocal_somePast` / `not_isStateLocal_timeRecall` (the
  three exclusion witnesses, all on `NF`/`natModel`); `stateLocal_stab_iff` and
  `stateLocal_starValid_iff_stab` (the headline, pointwise and as a validity). Plus the `@[simp]`
  clause lemmas and the `StateLocal.neg` / `.and` / `.or` closure lemmas.
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` — `fn_sentDet_atom`
  **deleted**; `fn_sentDet_stateLocal (φ) (hφ : φ.StateLocal)` proved in its place; `fn_separates`
  strengthened to quantify over the fragment; `fn_sentDet_bounds` added; import and docstring
  updated.
- `FormalSystem/Semantics/StarTruth.lean` — design note **(b)** refined: it now separates *what
  fails* (the different-times transfer, which still must not be sought, and the standing
  prohibition on extending the atomization route to `StarFormula`) from *what holds* (the
  same-time congruence on the `StateLocal` fragment), with a pointer to the new module.
- `FormalSystem/Semantics.lean` — import plus a module-index bullet.
- `FormalSystem/Semantics/README.md`, `FormalSystem/StarLanguage/README.md`,
  `FormalSystem/Metalogic/Independence/README.md`, `docs/theorem-index.md` — inventory rows,
  correspondence-table rows, and the rewritten "One recorded divergence" paragraph.

### The structural question, settled

`box` was the task's open question. It is **in** the fragment, and for an arbitrary argument:
`StarTruthAt M τ t v (.box φ)` is `∀ σ, σ.IsTotal → StarTruthAt M σ t v φ`, which does not mention
`τ` at all, so `isStateLocal_box` is `Iff.rfl`. `stab` is likewise unconditional, via
`sameStateAt_congr_left`. Neither needed the recursive fallback the plan held in reserve, so the
fragment is strictly larger than a naive "every subformula is state-local" reading. The final
table:

| Constructor | In the fragment | Route |
|---|---|---|
| `atom`, `bot` | yes | the clause reads the state at `t` only / constant |
| `imp φ ψ` | yes if both are | pointwise |
| `box φ` | yes, arbitrary `φ` | `Iff.rfl` — the clause discards `τ` |
| `stab φ` | yes, arbitrary `φ` | `sameStateAt_congr_left` |
| `timeStore i φ` | yes if `φ` is | evaluation stays at `t`; IH at `Function.update v i t` |
| `untl`, `snce`, `timeRecall` | **no** | `not_isStateLocal_someFuture` / `_somePast` / `_timeRecall` |

## Decisions

- **`StarFormula.StateLocal` lives in `namespace FormalSystem.StarLanguage`**, not
  `FormalSystem.Semantics` as the plan's Challenge block showed. Lean 4 generalized field notation
  resolves `φ.StateLocal` only against the namespace of `φ`'s type, and every other signature in
  the plan — `fn_sentDet_stateLocal (hφ : φ.StateLocal)` included — depends on that notation. The
  statement is otherwise byte-for-byte the Challenge's. It is also the right home on the merits:
  the predicate is purely syntactic.
- **The fragment is sound, not complete**, and the module docstring says so with a witness:
  `↑ⁱ↓ⁱφ` is semantically state-local whenever `φ` is, but is syntactically rejected. Recorded so
  the gap reads as a design choice rather than an oversight.
- **Same-time, not different-times.** `stab_state_only`'s shape (`τ(t) = σ(s)`, two times) does
  not generalize to this fragment and was not attempted; the same-time shape is what the consumer
  (`settledDisj_iff`, which evaluates `φ` at the single time held in register `2`) actually needs.
- **All three exclusion witnesses live on one frame** (`NF` with `natModel`), reusing the tree's
  existing countermodel rather than building a second two-state frame.
- **No `[COMPLETED WITH EXCLUSIONS]` on the task**: Phase 1's gate passed outright, so the
  contingency branch (record the failure, leave `fn_sentDet_atom` standing) never engaged.

## Plan Deviations

- **Phase 1** altered: `StarFormula.StateLocal` declared in `FormalSystem.StarLanguage` rather
  than `FormalSystem.Semantics` — see Decisions above for why the plan's own signatures require it.
- **Phase 3** altered: `stateLocal_starValid_iff_stab` uses `StarValid.of_forall_total`, not the
  plan's `TaskFrame.StarValidOn.of_forall_total`, whose conclusion is `F.StarValidOn` rather than
  the `StarValid` this theorem states.
- **Phase 5** last task skipped: "apply the widenings the survey identifies, one commit per
  widened statement" — the survey identified **zero** widenings outside Phase 4, so there was no
  commit to make. The phase is `[COMPLETED WITH EXCLUSIONS]` with a full
  `#### Reasoned Exclusions` table in the plan.
- **Commit granularity**: phases 1-3 landed in one commit and phases 4-5 in another, rather than
  one per phase. Phases 1-3 all edit the single new file and were verified by one type-check;
  Phase 5 produced no code change of its own.
- **Phase 6** altered: `scripts/readme-inventory.sh`, which the plan names, is deprecated and
  prints a pointer rather than regenerating. The live command is
  `bash scripts/check-module-invariants.sh --emit-inventory`, which was used; the hand-written
  summary text in the `ForwardDeterministicFrame.lean` inventory row still named
  `fn_sentDet_atom` and was edited by hand, only the line count being generated.
- **Phase 6** altered: `FormalSystem/StarLanguage/README.md` was edited as planned, but the
  collision the plan's Risks table anticipated materialised — the concurrent task in that
  neighbourhood committed the file, carrying these edits in under its own commit message. The
  content is in `HEAD` and was verified there (`fn_sentDet_atom`: 0 hits; state-locality rows:
  present); only the attribution differs.

## Verification

- Build: **Success** — full `lake build` exits 0
- Sorry count: **0** in every file touched (`FormalSystem/Semantics/StarStateLocal.lean`,
  `ForwardDeterministicFrame.lean`, `StarTruth.lean`); the live-tree census is empty
- Vacuous count: **0**
- Axiom count: **unchanged** — no new `axiom` declaration
- `bash scripts/check-module-invariants.sh`: exits **0**
- `grep -rn 'fn_sentDet_atom' FormalSystem/ Tests/ docs/ README.md`: **no hits**
- `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet`: unchanged in `git diff`
- Files verified: Yes

### Measured axiom sets (`#print axioms`)

| Declaration | Axioms |
|---|---|
| `StarFormula.StateLocal` | (none) |
| `isStateLocal_box`, `isStateLocal_stab`, `isStateLocal_of_stateLocal`, `stateLocal_stab_iff` | `[propext]` |
| `not_isStateLocal_someFuture`, `not_isStateLocal_somePast`, `not_isStateLocal_timeRecall`, `stateLocal_starValid_iff_stab` | `[propext, Classical.choice, Quot.sound]` |
| `fn_sentDet_stateLocal`, `fn_separates`, `fn_sentDet_bounds` | `[propext, Classical.choice, Quot.sound]` |

The last row matches the retired `fn_sentDet_atom` exactly, so the separation's axiom cost is
unchanged by the widening. Every docstring axiom claim was written from these measured values.

### Incident, recorded

While probing git state mid-Phase-6 I ran a bare `git stash`, which briefly reverted the working
tree — my own uncommitted work and a concurrent task's alike. It was popped immediately and every
file verified restored (content checks on `Semantics.lean`, `ForwardDeterministicFrame.lean`,
`docs/theorem-index.md`, `StarStateLocal.lean` all pass). A full `lake build` was in flight across
that window, so its green result was discarded rather than trusted; the build and the invariants
gate reported above are from runs entirely after the restore. No work was lost.

One unrelated transient also occurred: an invariants run failed C1 on
`FormalSystem.Metalogic.BXCanonical.Chronicle.PointInsertion` while two builds contended. Rebuilt
in isolation, it is green, and the final gate run passes C1.

## Impacts

- Any later result needing "this formula's truth is fixed by the present world state" can now cite
  `isStateLocal_of_stateLocal` instead of re-running the argument at atoms. The pattern recurs
  wherever `⟨τ⟩ₓ` is quantified over.
- The forward-determinism separation is now bounded from both sides by a single object
  (`fn_sentDet_bounds`), which is the publishable shape the task asked for: the validity is
  exactly the state-local fragment on the positive side and demonstrably not everything on the
  negative side.
- `StarTruth.lean`'s design note (b) no longer reads as forbidding this line of work, while its
  actual prohibition (no atomization route for `StarFormula`) is preserved verbatim in force.

## Follow-ups

- `stab_atom_of_atom` (`Semantics/PlusTruth.lean`) is the L⁺ shadow of this task's headline and is
  still atom-restricted. Widening it needs a `PlusFormula`-level fragment, which this task's
  Non-Goals and territory both excluded. The cheap route for a future task: define it as
  `(ofPlus φ).StateLocal` and transfer along `starTruthAt_ofPlus`. Its two consumers
  (`Metalogic/Conservativity/Plus/AxiomValidity.lean`) need the atom instance regardless, since
  the AS axiom is atom-restricted in the proof system itself.
- `StarFormula.StateLocal` is sound but not complete. A complete characterization would have to
  admit `↑ⁱ↓ⁱφ` and its relatives, i.e. track which registers are provably equal to the evaluation
  time — a register-analysis pass, not a structural recursion. Not attempted, and not needed by
  any consumer in the tree.

## References

- `specs/572_tense_free_stability_and_schematic_separation/plans/01_tense-free-stability-schematic-separation.md`
- `specs/572_tense_free_stability_and_schematic_separation/handoffs/phase-3-handoff-20260909.md`
- `specs/572_tense_free_stability_and_schematic_separation/handoffs/phase-5-handoff-20260909.md`
- `FormalSystem/Semantics/StarStateLocal.lean`
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`
