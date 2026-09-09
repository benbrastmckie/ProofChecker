# Implementation Summary: Task #573

- **Task**: 573 - Star proof theory and conservativity
- **Status**: [COMPLETED]
- **Started**: 2026-09-09T00:10:00Z
- **Completed**: 2026-09-09T02:15:00Z
- **Effort**: ~2 hours
- **Dependencies**: None (every consumed asset was already landed)
- **Artifacts**: plans/01_star-proof-theory-conservativity.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Built **TM⋆**, the proof system for L⋆ = L⁺ + the manuscript's time store/recall operators, and
landed its metatheory: soundness at all four frame classes, the embedding of every TM⁺ derivation,
and the conservativity verdict at the strength the evidence supports — **unconditional** over TM in
both directions, and a **proved conditional pair** over TM⁺ whose unconditional half shows that any
separating witness for non-conservativity is verbatim a witness of TM⁺ incompleteness. TM⋆
completeness is recorded as OPEN under two named obstructions, never stubbed. Before this task the
names `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` were reserved but unbuilt, so neither
soundness nor any conservativity statement about L⋆ could even be stated.

## What Changed

New Lean modules:

- `FormalSystem/StarLanguage/Axioms.lean` — `StarAxiom`, TM⋆'s axiom set: one `ofBase`
  constructor carrying every TM⁺ schema at its `ofPlus` instances, plus 16 register schemata
  (`store_recall_same`, `recall_store_same`, `recall_recall`, `store_store_comm`, `store_k`,
  `recall_k`, `store_box`, `recall_box`, `store_stab`, `store_atom`, the four rigidity arms, and
  the two export arms); `StarAxiom.minFrameClass`.
- `FormalSystem/StarLanguage/Derivation.lean` — `StarDerivationTree` (the seven TM⁺ rules,
  constructor for constructor), the notation `⊢⋆[fc]`, `StarDerivable`, `StarDerivable.mono`, the
  structural apparatus `lift`/`height`/`ofWeakeningNil`/`height_ofWeakeningNil_lt`/
  `mp_height_gt_left`/`mp_height_gt_right`, and `stabNecessitationOfPlus`.
- `FormalSystem/StarLanguage/Embedding.lean` — `StarAxiom.minFrameClass_ofBase`,
  `StarDerivationTree.ofPlusTree`, `starDerivable_of_plusDerivable`, `starDerivable_of_derivable`.
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` — the 16 named
  `starValid_*` register-schema validities, and the two dispatch lemmas
  `starAxiom_validIn_min` / `starAxiom_swap_validIn_min` with 17 explicit arms each and no
  wildcard.
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` —
  `star_derivable_valid_and_swap_validIn` (the companion recursion, well-founded on derivation
  height), `star_soundness_validIn`, the four per-class rows, and `star_not_derivable_nil_bot`.
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — `forward_star` and its four rows,
  `starDerivable_ofFormula_iff` and its four rows, `starConservative_of_plusComplete`,
  `plusIncomplete_of_starNonconservative`.
- `FormalSystem/Metalogic/Conservativity/Star.lean` — aggregator.
- `FormalSystem/Metalogic/Conservativity/Star/README.md` — module inventory, metatheory rows, and
  the completeness OPEN record.

Modified Lean modules:

- `FormalSystem/StarLanguage/Formula.lean` — `StarFormula.swapTemporal` (both registers
  structural), `swap_temporal_involution`, the `swap_temporal_*` push-through family, and the
  commutation pin `ofPlus_swapTemporal`.
- `FormalSystem/Semantics/StarNonValidities.lean` — `mfWitness`, `refute_modal_future`,
  `storeG_recall_valid`, `refute_erasure`.
- `FormalSystem/StarLanguage.lean`, `FormalSystem/Metalogic/Conservativity.lean` — imports,
  module lists, and the prose that had declared the four TM⋆ names unbuilt.

Modified documentation: `FormalSystem/StarLanguage/README.md` (module rows plus seven new
correspondence rows), `FormalSystem/Metalogic/Conservativity/README.md`,
`FormalSystem/Metalogic/Conservativity/Plus/README.md` (four TM⋆ metatheory rows),
`FormalSystem/Metalogic/README.md` (a TM⋆ metatheory subsection), `FormalSystem/README.md`,
`README.md` (regenerated inventory blocks).

## Decisions

- **`ofBase` embedding, and why it is forced rather than merely convenient.** The settled prior
  decision was to embed the TM⁺ block through one constructor. Implementation confirmed the
  stronger reason: re-declaring the TM block over `StarFormula` would be *unsound*, because
  `modal_future` (`□φ → □Gφ`) is refuted there. `refute_modal_future` is now a theorem in the
  tree at `φ := ↓¹p → p`, whose `□`-antecedent is valid on every frame and model.
- **Swap-closure discharged constructor by constructor.** Each of the 16 register schemata's
  temporal dual is an instance of a constructor of the same inductive (ten self-dual, two
  G↔H pairs, one U↔S pair), so each swap arm normalises `swapTemporal` through the
  `swap_temporal_*` family and reuses the matching validity lemma. No arm is re-proved.
- **The conservativity verdict is stated at the strength the evidence supports.** Over TM it is
  unconditional at all four classes. Over TM⁺ it is a conditional pair, because the same
  composition ends in a TM⁺ completeness engine and there is none. That is not a shortfall: the
  contrapositive `plusIncomplete_of_starNonconservative` is unconditional and shows the two
  questions are the same question.
- **No uniform substitution anywhere**, and none is available (TM⁺ is already not
  substitution-closed via `atom_stab`). Temporal duality is discharged semantically throughout.
- **No L⋆ atomization** was attempted or lifted; the `ofBase` arm consumes
  `plusAxiom_validIn_min` as a black box at `PlusFormula`.
- **`StarValidIn`'s binder-shape adapters** were missing from `Semantics/StarValidity.lean`
  (whose own docstring claims them). Rather than edit that shared file while a concurrent task
  was editing its neighbours, `starValidIn_of_forall_total` / `starValidIn_apply_total` were
  declared locally in `StarSoundness.lean`.

## Plan Deviations

- **Phase 4**, general `⊡`-necessitation: altered — landed as `stabNecessitationOfPlus`, at
  `ofPlus` instances only. The phase is marked `[COMPLETED WITH EXCLUSIONS]` with a
  `#### Reasoned Exclusions` record in the plan. The bullet's own prescribed route is what shows
  why the general form is underivable: MS reaches TM⋆ only as
  `StarAxiom.ofBase _ (PlusAxiom.box_stab ψ)`, whose instances are `□(ofPlus ψ) → ⊡(ofPlus ψ)`,
  so `modus_ponens` has nothing to apply at a register-containing formula. The rule remains
  **sound** at every `φ` — an underivability, not an unsoundness — and a native `box_stab` arm
  would fix it but would break the constructor list pinned in `## Lean Challenge Statements`.
  Recorded in `StarLanguage/Derivation.lean`'s docstring and in `StarLanguage/README.md`.
- **Phase 8** scope widened by four declarations: `Conservativity/Plus/Forward.lean` carries
  `forward_plus_base`/`_dense`/`_ztime`/`_rtime` alongside the `plusDerivable_ofFormula_iff_*`
  rows, so this file mirrors both families (12 declarations rather than the hypothesised 8).
- Phases 1–3 and 5–7 followed the plan without deviation. The Phase 1 pin `ofPlus_swapTemporal`
  is a structural induction rather than `rfl`, which the plan's verification block explicitly
  admits.

## Verification

- Build: **Success** — full `lake build`, green.
- Sorry count: **0** new; zero across all files this task touched
  (`grep -rn sorry` over `StarLanguage/`, `Conservativity/Star/`, `Star.lean`,
  `StarNonValidities.lean` returns nothing). The live tree's structural sorry inventory is
  asserted zero by C3.
- Vacuous count: **0** — no `:= True` / `:= Unit` / `:= trivial` definition in any file this task
  touched.
- Axiom count: **unchanged** — zero `axiom` declarations added (the repo-wide `^axiom ` grep
  matches only docstring lines that wrap onto the word).
- Module invariants: `bash scripts/check-module-invariants.sh` — see the run recorded at task
  close; C2 flagship axiom sets untouched (no flagship theorem and no `MainResults.lean`
  declaration was modified), C3 zero structural sorry, C9 no task-number citation under
  `FormalSystem/`, C24 every new module reachable and transitively importing `FormalSystem.Init`,
  C26 every new `def`/`abbrev` camelCase.
- Plan compliance: 17 `StarAxiom` constructors, matching the Phase 3 Scope Hypothesis and the
  pinned Challenge inductive exactly; both dispatch lemmas match all 17 by name with no wildcard
  arm; `ofPlusTree` matches all seven `PlusDerivationTree` constructors with no wildcard.
- `grep -rn 'reserved, unbuilt' FormalSystem/` returns nothing.
- `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/` returns nothing — the
  directional module invariant holds.
- Axiom audit (`lean_verify`, per declaration): `starDerivable_ofFormula_iff`,
  `star_soundness_validIn`, `plusIncomplete_of_starNonconservative`,
  `starAxiom_swap_validIn_min` and `refute_modal_future` each depend on exactly
  `[propext, Classical.choice, Quot.sound]` — the same set as their TM⁺ counterparts
  (`plusDerivable_ofFormula_iff`, `plus_soundness_validIn`), and no `sorryAx`.
- Files verified: Yes.

## Impacts

- L⋆ acquires a proof system, so TM⋆ soundness, the TM⁺ embedding, and both conservativity
  questions are now *statable* in the tree; before this they were not.
- The referee-facing question — does adding time store and recall prove any new theorem? — has an
  unconditional answer for the base language (**no**, at all four classes) and a precise,
  publishable answer for L⁺: the question is equivalent, modulo TM⋆ soundness, to the tree's own
  recorded open TM⁺-completeness problem, so no work on TM⋆ alone can decide it.
- Two negative results now live in the tree rather than only in a spec artifact:
  `refute_modal_future` (no schematic MF over L⋆) and the `storeG_recall_valid`/`refute_erasure`
  pair (register erasure is not a conservativity translation). A future reader reaching for
  either move finds a theorem saying why not.
- `FormalSystem/Metalogic/Conservativity/` gains a fourth language layer alongside L⁻, L and L⁺,
  with the same aggregator/README shape.

## Follow-ups

- **TM⋆ completeness remains OPEN**, under two named obstructions recorded in
  `Conservativity/Star/README.md`: (a) all four TM completeness engines build *deterministic*
  countermodels, every deterministic frame validates `sent:det`, and `sent:det` is not
  `StarValid` — and unlike the L⁺ case there is no "narrow to the deterministic class" escape,
  because registers do not collapse on deterministic frames; (b) the standard hybrid
  pure-axiom/PASTE route needs nominals, which L⋆ has none of.
- **No `docs/theorem-index.md` rows were added** for the TM⋆ results. That file's rows carry
  `pinned:C14`, which requires adding baseline entries to
  `scripts/check-module-invariants.sh`'s C14 heredoc pair — a baseline edit outside this task's
  plan, and one the plan treats as a hard-stop-adjacent change. Adding the rows plus their
  baselines is the natural next step if these results are to be advertised.
- **The general `⊡`-necessitation rule** is sound but underivable in TM⋆ (see Plan Deviations). A
  later task that wants it should add a native `box_stab` schema over `StarFormula` and re-verify
  swap-closure, rather than weakening `stabNecessitationOfPlus`.
- **`StarValidIn.of_forall_total` / `.apply_total`** belong in `Semantics/StarValidity.lean`,
  whose docstring already advertises them; they are currently local to `StarSoundness.lean`
  because a concurrent task was editing that directory.
- **The register-closure schema** `↑ⁱφ ↔ φ` for `i` not free in `φ` (of which `store_atom` is the
  atomic case) and register renaming are still unbuilt; both need a free-register predicate and a
  coincidence lemma, and nothing in the present metatheory consumes them.

## References

- `specs/573_star_proof_theory_and_conservativity/plans/01_star-proof-theory-conservativity.md`
- `specs/573_star_proof_theory_and_conservativity/reports/01_star-proof-theory-conservativity.md`
- `FormalSystem/Metalogic/Conservativity/Star/README.md` — the metatheory rows and the
  completeness OPEN record
- `FormalSystem/StarLanguage/README.md` — the paper-label correspondence table
