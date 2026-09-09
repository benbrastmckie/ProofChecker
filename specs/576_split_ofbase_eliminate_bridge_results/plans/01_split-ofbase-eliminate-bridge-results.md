# Implementation Plan: Split the ofBase monolith and eliminate the ofPlus-restricted bridge results

- **Task**: 576 - Split the ofBase monolith and eliminate the ofPlus-restricted bridge results from TM-star
- **Status**: [IMPLEMENTING]
- **Effort**: 23 hours
- **Dependencies**: Task 574 (landed), Task 575 (landed)
- **Research Inputs**: `specs/576_split_ofbase_eliminate_bridge_results/reports/01_ofbase-split-schema-measurement.md`
- **Artifacts**: plans/01_split-ofbase-eliminate-bridge-results.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

`StarAxiom.ofBase (φ : PlusFormula) (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)`
(`FormalSystem/StarLanguage/Axioms.lean:136`) packages the entire TM⁺ schema block into TM⋆ at
`ofPlus` instances only, because one schema — `modal_future` — is refuted over `StarFormula`.
This plan replaces that monolith with per-schema constructors stated directly over `StarFormula`,
carries `modal_future` alone under an explicit `RecallFree` (`↓ⁱ`-free) side condition, re-proves
validity and swap-validity for every new arm, retires `ofBase` outright, and replaces the
`ofPlus`-restricted `stabNecessitationOfPlus` with an unrestricted `stabNecessitation`. Done
means: `ofBase` and `stabNecessitationOfPlus` are both gone, every widening deliverable 7 covers
has landed, the three conservativity results are re-verified against the new axiom set,
`lake build` and `lake build BimodalTest` are green, `bash scripts/check-module-invariants.sh`
exits 0 with C2/C3/C9/C14/C15/C24/C26 green, and there is no new `sorry`.

### Research Integration

The research report re-established the gating measurement **by machine-checked proof** and
corrected it in two directions. This plan is built on its findings; the load-bearing ones:

- **The count is 53, not 45.** `ofBase` quantifies over `PlusAxiom`, which has 53 constructors
  (45 TM + 8 stability-modal). Re-confirmed independently during this planning dispatch:
  `grep -cE '^\s*\| [a-zA-Z_0-9]+ *[({:]'` over the `inductive PlusAxiom` block of
  `FormalSystem/PlusLanguage/Axioms.lean` returns **53**. The task description's "45 / 44 of 45"
  undercounts by the eight `⊡` schemata — and `box_stab`, the schema the headline bridge result
  hangs on, is one of them.
- **52 of 53 are schematic without any side condition; the 53rd is schematic under
  `RecallFree`.** 36 were proved individually at arbitrary `StarFormula` metavariables in
  `specs/576_split_ofbase_eliminate_bridge_results/.probes/*.lean` (seven files, all green). The
  remaining 17 were argued by mirror/transport, not proved — **Phase 1 of this plan closes that
  gap by proof before anything else runs**, which is what deliverable 1 demands.
- **No residual embedding arm is required.** Deliverable 4's conditional ("if a residual
  embedding arm is still required") does not fire; the docstring list of schemata that cannot be
  stated schematically is empty.
- **The side condition is `RecallFree`, not `RegFree`** (report D-2). `□↑¹p → □G↑¹p` is sound and
  is *not* an `ofPlus` instance, so `RegFree` would discard a proved widening. `↑¹p` is
  `RecallFree` and `ofPlus_ne_timeStore` shows it is not an embedded formula: the widening is
  proper, not cosmetic. This is a deliberate, measured deviation from deliverable 3's literal
  wording, authorized by deliverable 1's "proceed with whatever the true measurement supports".
- **`paste`/`untl_paste` need L⋆ purity predicates that are themselves strictly wider than
  `ofBase` supplies**, because `StarIsPureFuture.box`/`.stab` admit arbitrary bodies, so `□↓¹p`
  is pure-future. A second proper widening, independent of MF's.
- **No conservativity direction breaks.** All three results are proved semantically and never
  pattern-match `StarAxiom`; widening a *sound* axiom set cannot disturb them. The real
  obligation is on the backward half: `ofPlusTree`'s one-line `axiom` case becomes a 53-arm
  dispatch (Phase 11).
- **cslib precedent read (user directive, report F8).** The `SchemaUnion`/`ModalSchemaTag`
  representation is rejected here for four independent reasons — no subsumption lattice to
  compute, `StarAxiom` must stay `Type`-valued for the soundness recursion, side conditions break
  `.Holds` decidability, and the wildcard-free dispatch is a deliberate build gate a `fin_cases`
  over a tag set does not reproduce. Deliverable 2's "each with its own constructor mirroring
  `PlusAxiom`'s corresponding arm" is therefore **confirmed** by the reference read, not merely
  inherited from the task description. The predicate-level `SoundnessLemmas/` convention
  (cslib's `FrameCorrespondence`/`unionSound` analogue) transfers as a principle and is already
  practised here — it is measurably why `sep`, `z1` and `prior_UZ` transcribe in one-line
  bodies — but building the library is deferred (report D1), out of territory.

### Prior Plan Reference

No prior plan exists for this task. `specs/575_plus_state_locality_fragment/plans/01_*.md` was
consulted for artifact shape and for the "retire, never keep both" discipline its Phase 5
executed; it is a different task's artifact, not a template.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and `roadmap_flag` is not set, so no ROADMAP.md
phases are added. `specs/ROADMAP.md` exists but does not enumerate this task among its named
fronts (the single `576` hit at line 725 is a line-count column of an unrelated table row).

### Sequencing discipline inherited from the dispatch

The `.decisions.json` answer of cycle 4 is binding on what follows this task: **576 implements
and completes first; only then does 577 receive its forced research round.** The dependency edge
577 → 576 is substantive ordering and must not be weakened. Nothing in this plan may be deferred
into 577.

## Goals & Non-Goals

**Goals** — the declarations to land:

- `RecallFree`
- `RecallFree.swapTemporal`
- `StarIsPureFuture`
- `StarIsPurePast`
- `StarIsPureFuture.swapTemporal`
- `StarIsPurePast.swapTemporal`
- `recallFree_ofPlus`
- `starIsPureFuture_ofPlus`
- `starIsPurePast_ofPlus`
- `StarFormula.swap_temporal_kPlus`
- `StarFormula.swap_temporal_kMinus`
- `star_truth_congr_agreeFrom`
- `star_truth_congr_agreeUpTo`
- `star_paste_valid`
- `star_untl_paste_valid`
- `starKPlus_iff`
- `starKMinus_iff`
- `recallFree_vector_irrelevant`
- `StarAxiom.ofPlusAxiom`
- `StarAxiom.minFrameClass_ofPlusAxiom`
- `stabNecessitation`

**Goals** — the non-declaration outcomes:

- 53 new `StarAxiom` constructors mirroring `PlusAxiom`'s arms one-for-one, stated directly over
  `StarFormula`, with `modal_future` alone carrying a `RecallFree` side condition and
  `paste`/`untl_paste` carrying the L⋆ purity side conditions.
- 53 named `starValid_{constructor}` validity lemmas and 53 arms in each of
  `starAxiom_validIn_min` and `starAxiom_swap_validIn_min`, both dispatch lemmas remaining
  **wildcard-free**. These 53 + 53 are not pinned individually in `## Lean Challenge Statements`
  below: each one's statement is fixed mechanically by its mirror constructor's shape, and the
  constructor shapes are fixed by `PlusAxiom`'s corresponding arms.
- `StarAxiom.ofBase` **deleted** — constructor, `minFrameClass` arm, both dispatch arms, and
  `StarAxiom.minFrameClass_ofBase`.
- `stabNecessitationOfPlus` **deleted**, replaced by the unrestricted `stabNecessitation`. Never
  both.
- Deliverable 7's survey landed as a table with a per-result verdict, and every result the split
  actually covers widened — not only the headline.
- Deliverable 8's re-verification: `starDerivable_ofFormula_iff`,
  `starConservative_of_plusComplete`, `plusIncomplete_of_starNonconservative` re-checked against
  the new axiom set, with the backward half's frame-class agreement proved as a named lemma
  rather than 53 inline `rfl`s.
- `lake build` green, `lake build BimodalTest` green,
  `bash scripts/check-module-invariants.sh` exit 0 with C2/C3/C9/C14/C15/C24/C26 green, zero new
  `sorry`, zero task-number citations under `FormalSystem/`.

**Non-Goals**:

- **Any L⋆ atomization.** It does not exist and cannot: the TM⁺ arms of `plusAxiom_validIn_min`
  go through `Conservativity/Plus/Atomization.lean`, which rests on `stab_state_only`'s
  different-times transfer — precisely the invariant `StarFormula` is built to break
  (`Semantics/StarTruth.lean` design note (b)). Every schematic arm at L⋆ is a fresh direct proof
  against `StarTruthAt`. This prohibition is repeated in the docstrings and must be repeated in
  the summary.
- **Any argument by uniform substitution.** Forbidden by the task and unsound here:
  `PlusAxiom.atom_stab` already makes TM⁺ non-substitution-closed. The predicate-level route is
  the sound alternative and is not substitution in disguise — it quantifies over arbitrary
  predicates from the start.
- Building the predicate-level schema-soundness library (report D1), the order-dual swap-arm
  refactor (D2), the `star_truth_norm` simp attribute and relocation of the K± clause lemmas to
  `Semantics/StarTruth.lean` (D3), or a `RegFree` predicate with no consumer (D4). All four are
  out of territory; D3's workaround (declaring the K± lemmas in
  `Conservativity/Star/StarAxiomValidity.lean`) is adopted instead.
- Any change to `PlusAxiom`, to `Metalogic/Soundness.lean`'s L-level proofs, to
  `Metalogic/SoundnessLemmas/**`, or to `Semantics/PlusPasting.lean` (imported and reused
  **read-only**).
- Weakening `refute_modal_future`. It is confirmed, unchanged, and its witness (`↓¹p → p`) is
  exactly the boundary of the `RecallFree` fragment — it becomes the properness witness for the
  side condition, not a casualty of it.
- Removing the `ofPlus` restriction from results whose restriction *is* their content
  (`ofPlusTree`, `starDerivable_of_plusDerivable`, `starDerivable_of_derivable`,
  `starTruthAt_ofPlus`, `starValidOn_ofPlus`, `starValidOnFrames_ofPlus`, the conservativity
  statements, `refute_sentDet`). Phase 12 records each with its specific reason.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The build cannot be green between "add 53 constructors" and "supply 53×3 arms", because `minFrameClass` and both dispatch lemmas are wildcard-free by design | H | H | **Structural decision (see "Sequencing decision" below): `ofBase` is retained as a temporary scaffold through Phases 4-10 and deleted in Phase 11.** Each group phase adds its constructors together with their `minFrameClass` arms and both dispatch arms, so every phase ends green. The task cannot complete with both present; Phase 11 is mandatory, not optional |
| A group phase splits a temporal dual pair, so its swap arms need a validity lemma from a later phase | H | M | Every group below is **swap-closed by construction**: each member's temporal dual is a member of the same group. Each group phase carries a Scope Hypothesis line requiring this to be re-confirmed against the constructor list before the arms are written |
| One of the 17 not-individually-verified schemata turns out **not** to be sound at arbitrary `StarFormula` | H | L | This is a successful gate, not a failure (deliverable 1). Phase 1 measures before any `FormalSystem/` edit; a failing schema is carried under a stated side condition or left on `ofPlusAxiom`'s derived route with its obstruction named, the 53-row table records the true verdict, and every downstream group phase adjusts. Nothing is stubbed with `sorry` |
| Name collision: `StarIsPureFuture` vs `FormalSystem.PlusLanguage.IsPureFuture` in modules that `open` both namespaces (every file under `Conservativity/Star/` does) | M | H | The `Star`-prefixed names are chosen for exactly this reason and are fixed in the Goals list. `RecallFree` has no Plus-side twin. Confirm with `grep -rn "IsPureFuture\|RecallFree" FormalSystem/` before Phase 2 lands |
| 53 new `starValid_*` lemma names collide with existing declarations in `FormalSystem.Metalogic.Conservativity` (e.g. `untl_paste_starValid` already exists at Plus level) | M | M | Phase 4 opens with a collision scan over the 53 target names; any collision resolves by a `starValid_`-prefixed name matching the constructor, never by shadowing |
| `StarAxiom.minFrameClass` disagrees with `PlusAxiom.minFrameClass` on some arm, silently breaking backward conservativity | H | M | Proved as one named lemma `StarAxiom.minFrameClass_ofPlusAxiom` rather than 53 inline `rfl`s, so a mismatch is a named failure at a single site (report's mitigation, adopted) |
| C14's four pinned TM⋆ axiom-set rows drift | M | L | The new predicates are plain inductives contributing no axioms, so `[propext]` and `[propext, Classical.choice, Quot.sound]` should be preserved — **re-run `bash scripts/check-module-invariants.sh` at every phase boundary rather than only at the end**. If a set does change, update the baseline NAME only, never its axiom set (hard constraint) |
| An implementer reaches for L⋆ atomization or uniform substitution to shortcut 53 arms | H | M | Both are Non-Goals above with their obstructions named; the prohibition is already recorded in `StarAxiomValidity.lean` and `StarTruth.lean` docstrings and is restated in every group phase's task list |
| Territory gap G1 (`StarLanguage/Embedding.lean`) is not granted, leaving `ofBase` unretirable | H | L | Phases 1-10 are independent of G1 and land first. The assumption is stated explicitly below; deliverable 4 ("RETIRE the monolithic `ofBase`") cannot be met without it, so the plan proceeds under it rather than blocking |
| The 53-arm `ofPlusTree` dispatch or the deletion of `ofBase` lands half-applied, leaving the tree with a broken embedding | H | M | Phase 11 is `atomic-batch` and is preceded by `bash .claude/scripts/git-snapshot.sh 576`. Intermediate per-file states are expected red and must not be committed |
| Adding a file (`StarPasting.lean`) perturbs generated inventories (README totals, C5 module paths, C15 anchors, C24 `Init` reachability, C19 docstring coverage) | M | M | Phase 13 is a dedicated documentation-and-gate phase; every new declaration carries a docstring and a `Paper:` anchor from the moment it is written |

### Sequencing decision: `ofBase` is a scaffold through Phases 4-10

The dispatch's deliverable 4 requires retiring `ofBase`, and the git-workflow mandate requires
every phase to end green and be committed. Those two cannot both hold if the constructors and
the deletion land together, because `StarAxiom.minFrameClass`, `starAxiom_validIn_min`,
`starAxiom_swap_validIn_min`, `StarAxiom.minFrameClass_ofBase` and
`StarDerivationTree.ofPlusTree` all break the moment the inductive changes shape.

The resolution: **add first, delete last.** Phases 4-10 add the 53 mirror constructors in
swap-closed groups, each group landing its constructors, its `minFrameClass` arms and both
dispatch arms in the same green commit, while `ofBase` remains untouched. Phase 11 then deletes
`ofBase` in one atomic batch together with the `ofPlusAxiom` rewrite of `ofPlusTree` and the
`stabNecessitation` replacement.

This is a temporary, in-task scaffold, not a "keep both" outcome: `ofBase` and the mirror
constructors coexist only between Phase 4 and Phase 11, and **the task cannot reach `completed`
with `ofBase` still present.** The distinct rule in `.claude/rules/plan-compliance.md` — never
restate a theorem under its own name in weakened form — is not engaged by this: nothing is
restated or weakened, and `stabNecessitationOfPlus` (which *is* covered by that rule) is deleted
in the same atomic batch that introduces its replacement, never coexisting with it.

### Territory note (stated assumptions, not silent widenings)

The dispatch names the territory as `StarLanguage/Axioms.lean`, `StarLanguage/Derivation.lean`,
`StarLanguage/Formula.lean`, `Semantics/StarNonValidities.lean`,
`Metalogic/Conservativity/Star/**` and `StarLanguage/README.md`. Two deliverables cannot be met
inside that literal boundary, so this plan proceeds under two explicit assumptions:

1. **`FormalSystem/StarLanguage/Embedding.lean` is added to the territory (report G1, blocking).**
   It holds `StarAxiom.minFrameClass_ofBase` and `StarDerivationTree.ofPlusTree`, both hard
   consumers of `ofBase`. Deliverable 4 is impossible without editing it. Edits there are
   confined to replacing the two `ofBase` consumers and retargeting one `example`.
2. **Six out-of-territory files carrying `ofBase` prose that becomes false are added as a
   documentation sweep (report G2, non-blocking but C14/C15-risky).**
   `FormalSystem/StarLanguage.lean` (l.25), `FormalSystem/Metalogic/README.md` (l.291),
   `FormalSystem/Metalogic/Soundness.lean` (l.126),
   `FormalSystem/Metalogic/Conservativity.lean` (l.369),
   `FormalSystem/Metalogic/Conservativity/Star.lean` (l.15), `docs/theorem-index.md` (l.184).
   All doc-only. Leaving them stale contradicts the tree's own "no prose-only claims" discipline.

`FormalSystem/Semantics/PlusPasting.lean` is **imported and reused read-only** (report G4) — not
an edit. `FormalSystem/Semantics/StarTruth.lean` is deliberately **not** touched (report G3): the
K± clause lemmas are declared in `Conservativity/Star/StarAxiomValidity.lean` instead, following
the precedent `starTruth_iff_iff` already sets there; relocation is deferred as D3.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |
| 9 | 10 | 3, 9 |
| 10 | 11 | 10 |
| 11 | 12 | 11 |
| 12 | 13 | 12 |

Phases within the same wave can execute in parallel. Phases 4-10 are strictly sequential because
they all edit `StarLanguage/Axioms.lean` and `Conservativity/Star/StarAxiomValidity.lean`; Phase
3 writes a new file and is independent of the group chain until Phase 10 consumes it.

---

### Phase 1: Measurement closure gate — the 53-row verdict, by proof [COMPLETED]

**Goal**: Close deliverable 1 before any `FormalSystem/` edit. 36 of 53 schemata were proved at
arbitrary `StarFormula` metavariables in the research probes; this phase proves the remaining 17
and records a complete 53-row verdict table. **This phase gates everything after it.**

**Tasks**:
- [x] Re-confirm the constructor count mechanically: the `inductive PlusAxiom` block of
      `FormalSystem/PlusLanguage/Axioms.lean` has 53 constructors. Record the command and its
      output in the phase notes
- [x] Re-run all seven existing probes (`lake env lean specs/576_split_ofbase_eliminate_bridge_results/.probes/0N_*.lean`)
      and confirm each is still green against the current tree
- [x] Write `specs/576_split_ofbase_eliminate_bridge_results/.probes/08_measurement-closure.lean`
      proving, at **arbitrary** `StarFormula` metavariables (never at `ofPlus` instances):
      the 11 BX past mirrors `right_mono_until`, `right_mono_since`, `connect_past`,
      `enrichment_since`, `self_accum_since`, `absorb_since`, `linear_since`, `since_P`,
      `temp_linearity_past`, `P_since_equiv`, `serial_past`
- [x] In the same file, prove the 4 closed uniformity schemata `discrete_symm_bwd`,
      `discrete_propagate_fwd`, `discrete_propagate_bwd`, `discrete_box_necessity` by
      `starValidOnFrames_ofPlus` transport (each is a parameterless formula, hence literally an
      `ofPlus` image — pin the `rfl` as `.probes/03` does)
- [x] In the same file, prove `prior_SZ` (`.ZTime`) and `prior_S_gap` (`.RTime`), the order duals
      of `prior_UZ` and `prior_U_gap`, through `DiscreteOrder.exists_nearest_lt` and
      `Separability.exists_isGLB_of_lub` at `P := fun x => StarTruthAt M τ x v φ`
- [x] Record the complete **53-row verdict table** in this plan file as a `#### Measurement`
      subsection under this phase: constructor, verdict (schematic / conditional / failing),
      side condition if any, and the probe file + theorem name that establishes it
- [ ] If any schema fails at arbitrary `φ`, report the corrected measurement honestly in the
      table and in the phase notes, adjust the affected group phase's constructor list, and state
      whether the failing schema is carried under a side condition or excluded with its
      obstruction named. **A corrected count is a successful gate, never a reason to stub**
- [ ] `lake env lean` green on all eight probe files; no `sorry` anywhere in them


#### Measurement

Mechanical constructor count, re-run at implementation time:

```
$ grep -cE '^\s*\| [a-zA-Z_0-9]+ *[({:]' <(sed -n '/^inductive PlusAxiom/,/^\/--$/p' \
    FormalSystem/PlusLanguage/Axioms.lean)
53
```

All eight probe files are green under `lake env lean` (re-run 2026-09-09); no `sorry` in any of
them. The verdict below is by machine-checked proof at **arbitrary** `StarFormula` metavariables
except where the Evidence column says `closed`, in which case the schema is a parameterless
formula that is literally an `ofPlus` image and the transport `rfl` is pinned in the probe.

| # | Constructor | Verdict | Side condition | Evidence |
|---|---|---|---|---|
| 1 | `prop_k` | schematic | — | .probes/01 `prop_k` |
| 2 | `prop_s` | schematic | — | .probes/01 `prop_s` |
| 3 | `ex_falso` | schematic | — | .probes/01 `ex_falso` |
| 4 | `peirce` | schematic | — | .probes/01 `peirce` |
| 5 | `modal_t` | schematic | — | .probes/01 `modal_t` |
| 6 | `modal_4` | schematic | — | .probes/01 `modal_4` |
| 7 | `modal_b` | schematic | — | .probes/01 `modal_b` |
| 8 | `modal_5_collapse` | schematic | — | .probes/01 `modal_5_collapse` |
| 9 | `modal_k_dist` | schematic | — | .probes/01 `modal_k_dist` |
| 10 | `serial_future` | schematic | — | .probes/03 `serial_future` (closed; `ofPlus` transport) |
| 11 | `serial_past` | schematic | — | .probes/08 `serial_past` (closed; `ofPlus` transport) |
| 12 | `left_mono_until_G` | schematic | — | .probes/02 `left_mono_until_G` |
| 13 | `left_mono_since_H` | schematic | — | .probes/06 `left_mono_since_H` |
| 14 | `right_mono_until` | schematic | — | .probes/08 `right_mono_until` |
| 15 | `right_mono_since` | schematic | — | .probes/08 `right_mono_since` |
| 16 | `connect_future` | schematic | — | .probes/02 `connect_future` |
| 17 | `connect_past` | schematic | — | .probes/08 `connect_past` |
| 18 | `enrichment_until` | schematic | — | .probes/02 `enrichment_until` |
| 19 | `enrichment_since` | schematic | — | .probes/08 `enrichment_since` |
| 20 | `self_accum_until` | schematic | — | .probes/02 `self_accum_until` |
| 21 | `self_accum_since` | schematic | — | .probes/08 `self_accum_since` |
| 22 | `absorb_until` | schematic | — | .probes/02 `absorb_until` |
| 23 | `absorb_since` | schematic | — | .probes/08 `absorb_since` |
| 24 | `linear_until` | schematic | — | .probes/02 `linear_until` |
| 25 | `linear_since` | schematic | — | .probes/08 `linear_since` |
| 26 | `until_F` | schematic | — | .probes/02 `until_F` |
| 27 | `since_P` | schematic | — | .probes/08 `since_P` |
| 28 | `temp_linearity` | schematic | — | .probes/02 `temp_linearity` |
| 29 | `temp_linearity_past` | schematic | — | .probes/08 `temp_linearity_past` |
| 30 | `F_until_equiv` | schematic | — | .probes/02 `F_until_equiv` |
| 31 | `P_since_equiv` | schematic | — | .probes/08 `P_since_equiv` |
| 32 | `modal_future` | **conditional** | `RecallFree φ` | .probes/07 `modal_future_recallFree`; refuted at arbitrary `φ` by `refute_modal_future` (`↓¹p → p`) |
| 33 | `discrete_symm_fwd` | schematic | — | .probes/03 `discrete_symm_fwd` (closed; `ofPlus` transport) |
| 34 | `discrete_symm_bwd` | schematic | — | .probes/08 `discrete_symm_bwd` (closed; `ofPlus` transport) |
| 35 | `discrete_propagate_fwd` | schematic | — | .probes/08 `discrete_propagate_fwd` (closed) |
| 36 | `discrete_propagate_bwd` | schematic | — | .probes/08 `discrete_propagate_bwd` (closed) |
| 37 | `discrete_box_necessity` | schematic | — | .probes/08 `discrete_box_necessity` (closed) |
| 38 | `prior_UZ` | schematic | — | .probes/02 `prior_UZ` (`.ZTime`) |
| 39 | `prior_SZ` | schematic | — | .probes/08 `prior_SZ` (`.ZTime`) |
| 40 | `z1` | schematic | — | .probes/02 `z1` (`.ZTime`) |
| 41 | `density` | schematic | — | .probes/02 `density` (`.Dense`) |
| 42 | `dense_indicator` | schematic | — | .probes/03 `dense_indicator` (`.Dense`, closed) |
| 43 | `prior_U_gap` | schematic | — | .probes/03 `prior_U_gap` (`.RTime`) |
| 44 | `prior_S_gap` | schematic | — | .probes/08 `prior_S_gap` (`.RTime`) |
| 45 | `sep` | schematic | — | .probes/04 `sep` (`.RTime`) |
| 46 | `stab_k` | schematic | — | .probes/01 `stab_k` |
| 47 | `stab_t` | schematic | — | .probes/01 `stab_t` |
| 48 | `stab_4` | schematic | — | .probes/01 `stab_4` |
| 49 | `stab_5` | schematic | — | .probes/01 `stab_5` |
| 50 | `box_stab` | schematic | — | .probes/01 `box_stab` |
| 51 | `atom_stab` | schematic | — | .probes/01 `atom_stab` |
| 52 | `paste` | schematic (mirrored side condition) | `StarIsPureFuture φ`, `StarIsPurePast ψ` — the L⋆ mirrors of `PlusAxiom.paste`'s own | .probes/05 `star_paste_valid` |
| 53 | `untl_paste` | schematic (mirrored side condition) | `StarIsPurePast α`, `StarIsPureFuture φ` — likewise | .probes/05 `star_untl_paste_valid` |

**Verdict: 52 of 53 are schematic over `StarFormula` with no side condition beyond the one their
`PlusAxiom` mirror already carries; `modal_future` alone needs a new one (`RecallFree`).** The
prior count is confirmed, not corrected: no additional schema failed. `paste` and `untl_paste`
are listed as *mirrored* side conditions because `PlusAxiom.paste`/`untl_paste` already carry
purity hypotheses — their L⋆ counterparts mirror those arm for arm and add nothing new, so they
are not exceptions to the 52.

The gate therefore passes with the shape the plan predicted, and no group phase's constructor
list changes.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts (a) `PlusAxiom` has exactly 53 constructors, (b) exactly
17 of them are not yet individually proved at arbitrary `StarFormula`, and (c) all 17 will
succeed. Confirm (a) by the grep above, (b) by cross-checking the probe inventory against the
53-name list, and (c) by proof — a failure of (c) is the gate firing, and the verdict table
records the true measurement.

---

### Phase 2: The syntactic layer — `RecallFree`, the two L⋆ purity predicates, transfers [COMPLETED]

**Goal**: Add to `FormalSystem/StarLanguage/Formula.lean` every purely syntactic ingredient the
new constructors' side conditions need, plus the two missing `swapTemporal` clause lemmas.

**Tasks**:
- [x] Scan for name collisions first: `grep -rn "RecallFree\|StarIsPureFuture\|StarIsPurePast\|swap_temporal_kPlus\|swap_temporal_kMinus" FormalSystem/`
- [x] Declare `RecallFree : StarFormula → Prop` as an inductive with eight arms — every
      `StarFormula` constructor except `timeRecall` (`atom`, `bot`, `imp`, `box`, `untl`, `snce`,
      `stab`, `timeStore`), lifting `.probes/07` verbatim
- [x] Declare `StarIsPureFuture` and `StarIsPurePast`, mirroring `PlusFormula.IsPureFuture` /
      `IsPurePast` (`PlusLanguage/Formula.lean:299,308`) arm for arm and adding a `timeStore`
      arm; `timeRecall` is deliberately absent. Document in each docstring *why* `timeRecall` is
      excluded (`↓ⁱφ` reads at a time the register names, which may lie on the far side of the
      pasting point) and that `box`/`stab` admit **arbitrary** bodies, so `□↓¹p` is pure-future
- [x] Add `RecallFree.swapTemporal`, `StarIsPureFuture.swapTemporal`,
      `StarIsPurePast.swapTemporal` (lifted from `.probes/07` and `.probes/05`)
- [x] Add the three `ofPlus` transfer lemmas by induction on `PlusFormula`: `recallFree_ofPlus`
      (`RecallFree (ofPlus ψ)` for every `ψ`), `starIsPureFuture_ofPlus`
      (`IsPureFuture ψ → StarIsPureFuture (ofPlus ψ)`), `starIsPurePast_ofPlus`
- [x] Add `StarFormula.swap_temporal_kPlus` and `StarFormula.swap_temporal_kMinus`, mirroring
      `PlusFormula`'s (`PlusLanguage/Formula.lean:277,281`)
- [x] Pin the properness of the `RecallFree` widening as `example`s: `↑¹p` is `RecallFree`, and
      is not an `ofPlus` image (`ofPlus_ne_timeStore`); `↓¹p → p` is **not** `RecallFree`, which
      is exactly `refute_modal_future`'s witness
- [x] Every declaration carries a docstring (C19) and a `Paper:` anchor where one applies (C15);
      no task-number citations (C9)
- [x] Confirm the module invariant holds: nothing under `FormalSystem/StarLanguage/` imports
      anything from `FormalSystem/Semantics/`. `recallFree_vector_irrelevant` is semantic and
      therefore does **not** go here — it lands in Phase 9
- [x] `lake build FormalSystem.StarLanguage.Formula` green, then `lake build` green

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/StarLanguage/Formula.lean` — three new inductives, five new theorems, three
  transfer lemmas, two swap clause lemmas, properness pins, module docstring additions

---

### Phase 3: L⋆ pasting — the two purity congruences, PS and US [COMPLETED]

**Goal**: Create `FormalSystem/Metalogic/Conservativity/Star/StarPasting.lean` holding the
semantic content the `paste` and `untl_paste` arms consume, reusing
`Semantics/PlusPasting.lean`'s formula-independent construction read-only.

**Tasks**:
- [x] Create the file with the standard copyright header (`bash scripts/check-copyright-headers.sh`
      must accept it) and a module docstring stating why it lives here rather than in
      `Semantics/StarPasting.lean` (report D-4: territory, and the precedent `StarAxiomValidity.lean`
      already sets for `starTruth_iff_iff`)
- [x] Import `FormalSystem.Semantics.PlusPasting` and `FormalSystem.Semantics.StarValidity`;
      reuse `paste`, `paste_isTotal`, `paste_agreeFrom`, `paste_agreeUpTo`, `AgreeFrom`,
      `AgreeUpTo`, `agreeFrom_mono`, `agreeUpTo_mono` **read-only** — no edit to `PlusPasting.lean`
- [x] Prove `star_truth_congr_agreeFrom` by induction on `StarIsPureFuture`, with the register
      vector **universally quantified in the motive** so the `timeStore` case recurses at
      `Function.update v i t` (lifted from `.probes/05`)
- [x] Prove `star_truth_congr_agreeUpTo`, its `StarIsPurePast` twin
- [x] Prove `star_paste_valid` (PS over `StarFormula`) and `star_untl_paste_valid` (US), both
      lifted from `.probes/05`
- [x] Register the module in `FormalSystem/Metalogic/Conservativity/Star.lean` and in
      `FormalSystem/Metalogic/Conservativity/Star/README.md`'s module index
- [x] Every declaration carries a docstring and, where one applies, a `Paper:` anchor
- [x] `lake build FormalSystem.Metalogic.Conservativity.Star.StarPasting` green, then
      `lake build` green

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Star/StarPasting.lean` (new)
- `FormalSystem/Metalogic/Conservativity/Star.lean`,
  `FormalSystem/Metalogic/Conservativity/Star/README.md` (registration)

---

### Phase 4: Group A — propositional, S5 modal, and the six non-pasting `⊡` schemata [COMPLETED]

**Goal**: Add the first 15 mirror constructors with their `minFrameClass` arms, their named
validity lemmas, and their arms in both dispatch lemmas — the build green at the end. `ofBase`
is untouched.

**Constructors (15)**: `prop_k`, `prop_s`, `ex_falso`, `peirce`, `modal_t`, `modal_4`, `modal_b`,
`modal_5_collapse`, `modal_k_dist`, `stab_k`, `stab_t`, `stab_4`, `stab_5`, `box_stab`,
`atom_stab`. All 15 were proved at arbitrary `φ` in `.probes/01`. All route to `.Base`.

**Tasks**:
- [x] Scan for collisions on the 53 target `starValid_*` names before writing any of them:
      `grep -rn "starValid_" FormalSystem/` and check against the constructor list
- [x] Add the 15 constructors to `inductive StarAxiom`, each with a docstring stating the schema
      and mirroring `PlusAxiom`'s corresponding arm's shape and argument order exactly
- [x] `StarAxiom.minFrameClass`: all 15 fall to the existing `_ => .Base` wildcard; add a pin
      `example` for one of them confirming this rather than assuming it
- [x] Add the 15 `starValid_*` lemmas to `Conservativity/Star/StarAxiomValidity.lean`, lifted
      from `.probes/01`. No atomization, no uniform substitution — direct proofs against
      `StarTruthAt`
- [x] Add the 15 arms to `starAxiom_validIn_min` and 15 to `starAxiom_swap_validIn_min`; every
      member of this group is self-dual, so each swap arm normalises `swapTemporal` through the
      `StarFormula.swap_temporal_*` family and lands on the matching validity lemma at swapped
      arguments
- [x] Extend `Axioms.lean`'s swap-closure list with a row per new constructor
- [x] `lake build` green; `bash scripts/check-module-invariants.sh` exit 0; no new `sorry`
- [x] Commit

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Scope Hypothesis**: asserts 15 constructors in this group, all `.Base`, all self-dual under
`swapTemporal`. Confirm by reading `PlusAxiom`'s corresponding arms and
`PlusAxiom.minFrameClass`'s routing before writing the arms; a member whose dual is not in this
group must move to the phase holding its dual, and the wave table updated.

---

### Phase 5: Group B — seriality, monotonicity, connection [COMPLETED]

**Goal**: The next 8 mirror constructors, arms and swap arms; build green.

**Constructors (8)**: `serial_future`, `serial_past`, `left_mono_until_G`, `left_mono_since_H`,
`right_mono_until`, `right_mono_since`, `connect_future`, `connect_past`. All route to `.Base`.
Swap-closed: the four G/H and U/S pairs are both present.

**Tasks**:
- [x] Add the 8 constructors with docstrings mirroring `PlusAxiom`'s arms
- [x] Add the 8 `starValid_*` lemmas — transcriptions of the corresponding L-level proofs in
      `Metalogic/Soundness.lean` under the substitution `TruthAt M τ t ↦ StarTruthAt M τ t v`,
      `Truth.*_iff ↦ StarTruth.*_iff`. `serial_future`, `left_mono_until_G` and `connect_future`
      are already in `.probes/02`/`.probes/03`; `left_mono_since_H` is in `.probes/06`
- [x] Add the 8 arms to each dispatch lemma; each swap arm lands on its dual member's validity
      lemma at swapped arguments
- [x] Extend the swap-closure list; `lake build` green; invariants exit 0; commit

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: full

**Scope Hypothesis**: asserts 8 constructors, all `.Base`, forming four dual pairs entirely
inside this group. Confirm against the constructor list before writing the swap arms.

---

### Phase 6: Group C — enrichment, self-accumulation, absorption, linearity [COMPLETED]

**Goal**: The next 8 mirror constructors, arms and swap arms; build green.

**Constructors (8)**: `enrichment_until`, `enrichment_since`, `self_accum_until`,
`self_accum_since`, `absorb_until`, `absorb_since`, `linear_until`, `linear_since`. All `.Base`,
four U/S dual pairs, all inside the group.

**Tasks**:
- [x] Add the 8 constructors with docstrings mirroring `PlusAxiom`'s arms
- [x] Add the 8 `starValid_*` lemmas by transcription; the `until` half of each pair is already
      in `.probes/02`. These are the heaviest of the BX block — expect `simp only` over the
      `StarTruth.*_iff` clause family, then `rintro`/`rcases lt_trichotomy`, mirroring the L
      proofs' `simp only [truth_norm]` shape. There is no `truth_norm` simp set on the L⋆ side
      (report D3, deferred): spell the clause lemmas out
- [x] Add the 8 arms to each dispatch lemma; extend the swap-closure list
- [x] `lake build` green; invariants exit 0; commit

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: asserts 8 constructors, all `.Base`, four dual pairs inside the group.
Confirm before writing the swap arms.

---

### Phase 7: Group D — `until_F`/`since_P`, temporal linearity, the two equivalences [COMPLETED]

**Goal**: The next 6 mirror constructors, arms and swap arms; build green.

**Constructors (6)**: `until_F`, `since_P`, `temp_linearity`, `temp_linearity_past`,
`F_until_equiv`, `P_since_equiv`. All `.Base`, three dual pairs inside the group.

**Tasks**:
- [x] Add the 6 constructors with docstrings mirroring `PlusAxiom`'s arms
- [x] Add the 6 `starValid_*` lemmas by transcription (`until_F`, `temp_linearity` and
      `F_until_equiv` are in `.probes/02`)
- [x] Add the 6 arms to each dispatch lemma; extend the swap-closure list
- [x] `lake build` green; invariants exit 0; commit

**Timing**: 1.5 hours

**Depends on**: 6

**Verification Tier**: full

**Scope Hypothesis**: asserts 6 constructors, all `.Base`, three dual pairs inside the group.
Confirm before writing the swap arms.

---

### Phase 8: Group E — discrete uniformity, density, Prior, Z1 [COMPLETED]

**Goal**: The next 10 mirror constructors — the first with non-`.Base` frame classes — their
`minFrameClass` arms, validity and swap arms; build green.

**Constructors (10)**: `discrete_symm_fwd`, `discrete_symm_bwd`, `discrete_propagate_fwd`,
`discrete_propagate_bwd`, `discrete_box_necessity` (all `.Base`), `density` and `dense_indicator`
(`.Dense`), `prior_UZ` and `prior_SZ` (`.ZTime`), `z1` (`.ZTime`).

**Tasks**:
- [x] Add the 10 constructors with docstrings mirroring `PlusAxiom`'s arms
- [x] Add **5 explicit `minFrameClass` arms** — `density`, `dense_indicator`, `prior_UZ`,
      `prior_SZ`, `z1` — placed before the `_ => .Base` wildcard, matching
      `PlusAxiom.minFrameClass`'s routing exactly. Add a pin `example` per non-`.Base` arm
- [x] Add the 10 `starValid_*` lemmas: the five closed uniformity formulas are three-line
      `starValidOnFrames_ofPlus` transports (they are parameterless, hence literally `ofPlus`
      images — pin the `rfl`); `density`, `dense_indicator`, `prior_UZ`, `z1` are in
      `.probes/02`/`.probes/03`; `prior_SZ` comes from Phase 1's `.probes/08`. `prior_UZ`,
      `prior_SZ` and `z1` reuse `SoundnessLemmas/DiscreteOrder.lean`'s `exists_nearest_gt` /
      `exists_nearest_lt` / `forall_gt_of_succ_step` at `P := fun x => StarTruthAt M τ x v φ` —
      one-line bodies. Do **not** inline the order-theoretic content
- [x] Add the 10 arms to each dispatch lemma; extend the swap-closure list
- [x] `lake build` green; **re-run `bash scripts/check-module-invariants.sh` with attention to
      C2/C14** — this is the first phase introducing non-`.Base` routing; commit

**Scope Hypothesis outcome (measured, not predicted)**: the constructor and frame-class halves
hold exactly — 10 constructors, 5 non-`.Base` (2 `.Dense`, 3 `.ZTime`), routing identical to
`PlusAxiom.minFrameClass`. The **duality half is corrected**: only `discrete_symm_fwd` ↔
`discrete_symm_bwd` and `prior_UZ` ↔ `prior_SZ` are dual pairs inside the group. The duals of
`discrete_propagate_fwd`, `discrete_propagate_bwd`, `discrete_box_necessity`, `dense_indicator`,
`density` and `z1` are not instances of *any* constructor of `StarAxiom` — `swapTemporal`
exchanges `untl`/`snce` and there is no past twin of density or Z1 among the schemata. This is
not a defect in the grouping: the L level has exactly the same shape, carrying a dedicated
`*_swap_valid` lemma per such schema in `SoundnessLemmas/FrameClassVariants.lean`. Six named
`starValid_*_swap` lemmas were added in this phase to supply them — the four closed ones by
`ofPlus` transport from `plusAxiom_swap_validIn_min`, `density` and `z1` directly. No later
phase's work was consumed and no statement was weakened.

**Timing**: 2 hours

**Depends on**: 7

**Verification Tier**: full

**Scope Hypothesis**: asserts 10 constructors, of which exactly 5 are non-`.Base` (2 `.Dense`,
3 `.ZTime`), and that each member's dual is in this group. Confirm against
`PlusAxiom.minFrameClass` (`PlusLanguage/Axioms.lean:310`) arm by arm before writing the
`minFrameClass` arms.

---

### Phase 9: Group F — Reynolds Dedekind, and `modal_future` under `RecallFree` [COMPLETED]

**Goal**: The 4 remaining non-pasting constructors, including the single conditional arm; build
green. This is the phase that discharges deliverable 3.

**Constructors (4)**: `prior_U_gap` and `prior_S_gap` (`.RTime`), `sep` (`.RTime`),
`modal_future` (`.Base`, carrying `(hφ : RecallFree φ)`).

**Tasks**:
- [x] Add the two semantic helper lemmas to `Conservativity/Star/StarAxiomValidity.lean`:
      `starKPlus_iff` and `starKMinus_iff` (from `.probes/03`/`.probes/04`), declared here rather
      than in `Semantics/StarTruth.lean` per report D-5, with a docstring naming the precedent
      (`starTruth_iff_iff`) and recording the relocation as deferred
- [x] Add `recallFree_vector_irrelevant` (from `.probes/07`) — the register vector is inert on
      `↓ⁱ`-free formulas; the `timeStore` case recurses at `Function.update v i t`. This is one
      of the two genuinely novel proofs of the round, not a transcription
- [x] Add the 4 constructors. `modal_future` takes `(φ : StarFormula) (hφ : RecallFree φ)` — the
      **only** constructor in the whole inductive carrying a side condition that `PlusAxiom`'s
      corresponding arm does not. Its docstring must state: the schema, that MF is refuted at
      `↓¹p → p` (`refute_modal_future`), that `RecallFree` is strictly wider than the `ofPlus`
      image with `□↑¹p → □G↑¹p` as the witness, and why `RegFree` was rejected
- [x] Add 3 explicit `minFrameClass` arms routing `prior_U_gap`, `prior_S_gap`, `sep` to `.RTime`,
      with pin `example`s; `modal_future` falls to the `.Base` wildcard — pin that too
- [x] Add the 4 `starValid_*` lemmas: `sep` reuses `SoundnessLemmas/Separability.lean`'s
      `sep_order` unchanged at `P := {u | StarTruthAt M τ u v φ}` (`.probes/04`); `prior_U_gap`
      from `.probes/03`, `prior_S_gap` from `.probes/08`; `modal_future` from `.probes/07`
      (`starTruthAt_timeShift` + `add_sub_cancel` + `recallFree_vector_irrelevant`)
- [x] Add the 4 arms to each dispatch lemma. `modal_future`'s swap arm uses
      `RecallFree.swapTemporal` and the `modal_future_recallFree_swap` proof from `.probes/07`
- [x] Extend the swap-closure list, including the new side-condition row
- [x] `lake build` green; invariants exit 0; commit

**Scope Hypothesis outcome (measured)**: 4 constructors, 3 of them `.RTime`, confirmed;
`modal_future` is confirmed as the sole constructor in the whole inductive carrying a side
condition its `PlusAxiom` mirror lacks (`grep -c "RecallFree" FormalSystem/StarLanguage/Axioms.lean`
finds it on one constructor only). The **duality half is corrected** the same way Phase 8's was:
`prior_U_gap` ↔ `prior_S_gap` is a dual pair, but `sep` and `modal_future` have no dual
constructor. `starValid_sep_swap` (through `SoundnessLemmas.sep_order_mirror`, so the
nested-interval argument is written once, not mirrored by hand) and `starValid_modal_future_swap`
(through `RecallFree.swapTemporal`) supply those two duals. The L level has the identical shape
(`Metalogic/Soundness.lean`'s `sep_swap_valid`, `SoundnessLemmas`' `mf_swap_valid`).

**Timing**: 2 hours

**Depends on**: 8

**Verification Tier**: full

**Scope Hypothesis**: asserts 4 constructors, 3 of them `.RTime`, and that `modal_future` is the
sole constructor in the entire inductive carrying a side condition absent from its `PlusAxiom`
mirror. Confirm the second half by re-reading the constructor list after this phase: exactly one
`RecallFree` hypothesis should appear, plus the two purity hypotheses Phase 10 adds.

---

### Phase 10: Group G — `paste` and `untl_paste` at the L⋆ purity predicates [NOT STARTED]

**Goal**: The last 2 mirror constructors, completing the 53. Build green; `ofBase` now has no
schema it alone supplies.

**Constructors (2)**: `paste (φ ψ) (hφ : StarIsPureFuture φ) (hψ : StarIsPurePast ψ)`,
`untl_paste (α φ) (hα : StarIsPurePast α) (hφ : StarIsPureFuture φ)`. Both `.Base`.

**Tasks**:
- [ ] Add the 2 constructors, mirroring `PlusAxiom.paste`/`untl_paste`
      (`PlusLanguage/Axioms.lean:298,302`) argument for argument, with `IsPureFuture`/`IsPurePast`
      replaced by their `Star`-prefixed L⋆ counterparts
- [ ] Docstring each with the **second proper widening**: because `StarIsPureFuture.box` and
      `.stab` admit arbitrary bodies, the L⋆ pure fragment contains register-carrying formulas
      such as `□↓¹p`, so these two schemata reach strictly further than `ofBase` supplied. Pin
      that as an `example`
- [ ] `minFrameClass`: both fall to the `.Base` wildcard; add a pin `example`
- [ ] Add `starValid_paste` and `starValid_untl_paste` from Phase 3's `star_paste_valid` /
      `star_untl_paste_valid`
- [ ] Add both arms to each dispatch lemma; the swap arms pair PS↔US through
      `StarIsPureFuture.swapTemporal` / `StarIsPurePast.swapTemporal`
- [ ] Extend the swap-closure list; record in `Axioms.lean`'s docstring that all 53 mirror
      constructors are now present
- [ ] Confirm mechanically that the constructor count of `StarAxiom` is now 53 + 16 + `ofBase`
      = 70, and that both dispatch lemmas are still wildcard-free
- [ ] `lake build` green; invariants exit 0; commit

**Timing**: 1.5 hours

**Depends on**: 3, 9

**Verification Tier**: full

**Scope Hypothesis**: asserts 2 constructors here and 53 mirror constructors in total across
Phases 4-10 (15+8+8+6+10+4+2). Confirm by counting the constructor lines of `inductive StarAxiom`
and subtracting the 16 register arms and `ofBase`.

---

### Phase 11: Retire `ofBase`; retire `stabNecessitationOfPlus` [NOT STARTED]

**Goal**: Delete the monolith and the restricted bridge result, replacing the embedding route
with a **derived** function over the schematic constructors. This is the phase that discharges
deliverables 4 and 6.

**Tasks**:
- [ ] `bash .claude/scripts/git-snapshot.sh 576` before the first deletion
- [ ] In `StarLanguage/Embedding.lean`, define
      `StarAxiom.ofPlusAxiom {φ : PlusFormula} (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)` — a
      53-arm dispatch sending each `PlusAxiom` constructor to its `StarAxiom` mirror at
      `ofPlus`-instantiated arguments. `ofPlus` commutes with the formula constructors
      definitionally, so each arm should be a direct constructor application; `modal_future`
      supplies `recallFree_ofPlus`, and `paste`/`untl_paste` supply `starIsPureFuture_ofPlus` /
      `starIsPurePast_ofPlus`
- [ ] **This is the structural difference that makes the retirement real**: `ofBase` was a
      *constructor* (a primitive axiom arm); `ofPlusAxiom` is a *derived* function, provable
      from the schematic constructors and adding nothing to TM⋆. Record that in its docstring
- [ ] Prove `StarAxiom.minFrameClass_ofPlusAxiom : (StarAxiom.ofPlusAxiom ax).minFrameClass = ax.minFrameClass`
      as one named `cases` lemma over `PlusAxiom` — **not** 53 inline `rfl`s — so a routing
      mismatch is a named failure at a single site
- [ ] Rewrite `StarDerivationTree.ofPlusTree`'s `axiom` case to use `ofPlusAxiom` and
      `minFrameClass_ofPlusAxiom`; the other six cases are unchanged
- [ ] Delete `StarAxiom.minFrameClass_ofBase`
- [ ] Delete the `ofBase` constructor from `inductive StarAxiom`, its `minFrameClass` arm, and
      its arm in each of `starAxiom_validIn_min` and `starAxiom_swap_validIn_min`
- [ ] In `StarLanguage/Derivation.lean`, add
      `stabNecessitation {fc} {ψ : StarFormula} (d : ⊢⋆[fc] ψ) : ⊢⋆[fc] StarFormula.stab ψ`,
      built from `necessitation` and the schematic `StarAxiom.box_stab`, and **delete**
      `stabNecessitationOfPlus`. Never keep both; never restate the old name in weakened form
- [ ] Retarget the two `example`s that assert the restriction: in `Derivation.lean`, "MF reaches
      TM⋆ through `ofBase` … and only there" becomes a `RecallFree` non-embedded witness
      (`□↑¹p → □G↑¹p`); in `Embedding.lean`, the MF-at-`⊡` acceptance check retargets to the new
      constructor via `ofPlusAxiom`
- [ ] `grep -rn "ofBase\|stabNecessitationOfPlus" FormalSystem/ docs/` returns **no** live hits
- [ ] `lake build` green, `lake build BimodalTest` green, invariants exit 0, no new `sorry`

**Timing**: 2 hours

**Depends on**: 10

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: asserts exactly five code consumers of `ofBase` (`StarAxiom.minFrameClass`,
`starAxiom_validIn_min`, `starAxiom_swap_validIn_min`, `StarAxiom.minFrameClass_ofBase`,
`StarDerivationTree.ofPlusTree`) plus `stabNecessitationOfPlus`. Confirm with
`grep -rn "ofBase" FormalSystem/` before deleting; any consumer not on that list is a plan
deviation and must be reported, not silently absorbed.

**Files to modify**:
- `FormalSystem/StarLanguage/Axioms.lean` — `ofBase` deleted, `minFrameClass` arm deleted,
  docstring rewritten
- `FormalSystem/StarLanguage/Embedding.lean` — `ofPlusAxiom`, `minFrameClass_ofPlusAxiom`,
  `ofPlusTree` rewritten, `minFrameClass_ofBase` deleted, `example` retargeted
- `FormalSystem/StarLanguage/Derivation.lean` — `stabNecessitation` added,
  `stabNecessitationOfPlus` deleted, `example` retargeted, `⊡`-necessitation docstring rewritten
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` — two `ofBase` arms deleted

---

### Phase 12: Deliverable 7 survey and deliverable 8 conservativity re-verification [NOT STARTED]

**Goal**: Widen every other `ofPlus`-restricted result the split covers — not only the headline —
and re-verify the three conservativity results against the new axiom set, reporting any breakage
as a theorem rather than working around it.

**Tasks**:
- [ ] Enumerate mechanically, not from the report: every declaration reachable from
      `FormalSystem/StarLanguage/` and `FormalSystem/Metalogic/Conservativity/Star/` whose
      statement mentions `ofPlus`, `ofStarCtx` or `PlusFormula`
      (`grep -rn "ofPlus\|ofStarCtx" FormalSystem/StarLanguage/ FormalSystem/Metalogic/Conservativity/Star/`)
- [ ] Record the survey in this plan file as a `#### Restriction survey` subsection under this
      phase: one row per result, with verdict **WIDENED** / **DIED WITH `ofBase`** /
      **STAYS RESTRICTED** and, for the last, the *specific* reason the restriction is the
      result's content rather than a limitation on it
- [ ] Widen every result the split actually covers. The expected set from research is
      `stabNecessitationOfPlus` (done in Phase 11), `minFrameClass_ofBase` (died in Phase 11),
      and the two MF `example`s (retargeted in Phase 11) — **but the enumeration above is
      authoritative over that expectation**, and any additional widenable result found must be
      widened here, not deferred
- [ ] Re-verify `starDerivable_ofFormula_iff`, `starConservative_of_plusComplete` and
      `plusIncomplete_of_starNonconservative` (`Conservativity/Star/Forward.lean`) build
      unchanged against the new axiom set. Forward halves depend on TM⋆ soundness only, which is
      preserved because every new arm is proved sound; the backward halves depend on `ofPlusTree`,
      now guarded by `minFrameClass_ofPlusAxiom`
- [ ] **If a conservativity direction does break, that is a real finding about the language.**
      State it as a theorem with its witness and report it in the summary. Never silently weaken
      a statement or work around it
- [ ] Record the new positive fact as pinned `example`s: TM⋆ is now strictly stronger at
      register-carrying formulas (`⊢⋆ □↑¹p → □G↑¹p`, and `⊢⋆ ⊡φ` from `⊢⋆ φ` at arbitrary `φ`)
      while proving no new L⁺ theorem — conservativity is a statement about embedded formulas and
      is proved through the semantics
- [ ] `lake build` green; `lake build BimodalTest` green; invariants exit 0

**Timing**: 1.5 hours

**Depends on**: 11

**Verification Tier**: full

**Scope Hypothesis**: asserts the survey's expected outcome (3 widened/died, 8 families staying
restricted by nature). The `grep` enumeration is the confirmation; a result found outside the
expected set changes the survey table, and the table records what was measured, not what was
predicted.

---

### Phase 13: Documentation sweep and full gate [NOT STARTED]

**Goal**: Bring every docstring, README and index into agreement with the new axiom set, and run
the complete gate.

**Tasks**:
- [ ] Rewrite `StarLanguage/Axioms.lean`'s module docstring: the "Why the TM⁺ schemata are
      embedded rather than re-declared" section is now false and is replaced by the split's
      rationale — 52 schematic, `modal_future` alone at `RecallFree`, `paste`/`untl_paste` at the
      L⋆ purity predicates, no residual embedding arm. Update the "Extension recipe" and the
      "Frame classes" sections to the new arm counts
- [ ] Correct the `ofBase` prose in `StarLanguage/README.md` (l.36, 38, 49, 57, 65-68, 115),
      `StarLanguage/Derivation.lean` (the `⊡`-necessitation section),
      `StarLanguage/Formula.lean` (l.76, 362), `Semantics/StarNonValidities.lean` (l.54, 128 —
      MF now reaches every `↓ⁱ`-free formula, not only `ofPlus` instances),
      `Metalogic/Conservativity/Star/README.md` (l.12, 34) and
      `Star/StarAxiomValidity.lean` (l.29-33 — the "return on the `ofBase` design" paragraph is
      now the cost this task paid)
- [ ] Mirror the **"no L⋆ atomization, ever"** prohibition into `StarLanguage/README.md`'s
      invariant list (research Context Extension recommendation); it is the single most likely
      shortcut a future agent reaches for when facing 53 arms
- [ ] Sweep the six out-of-territory prose consumers (Territory note assumption 2):
      `FormalSystem/StarLanguage.lean` (l.25), `FormalSystem/Metalogic/README.md` (l.291),
      `FormalSystem/Metalogic/Soundness.lean` (l.126),
      `FormalSystem/Metalogic/Conservativity.lean` (l.369),
      `FormalSystem/Metalogic/Conservativity/Star.lean` (l.15), `docs/theorem-index.md` (l.184)
- [ ] Add `docs/theorem-index.md` rows for the new headline declarations and re-anchor any row
      naming a deleted one
- [ ] Regenerate inventories where the gate requires it (`--emit-inventory`) after adding
      `StarPasting.lean`
- [ ] Run the full gate: `lake build`, `lake build BimodalTest`,
      `bash scripts/check-module-invariants.sh` exit 0 with **C2, C3, C9, C14, C15, C24, C26 all
      green**. If a C2/C14 pinned name changed because a declaration was renamed, update the
      baseline **NAME only, never its axiom set**
- [ ] `grep -rn "ofBase\|stabNecessitationOfPlus" . --include=*.lean --include=*.md` returns hits
      only under `specs/`
- [ ] Zero task-number citations under `FormalSystem/` (C9)

**Timing**: 1.5 hours

**Depends on**: 12

**Verification Tier**: full

**Scope Hypothesis**: asserts 7 in-territory prose consumers and 6 out-of-territory ones at the
line numbers above. Line numbers drift as earlier phases edit these files — confirm by
`grep -rn "ofBase"` rather than by line number, and treat the counts as the hypothesis they are.

## Lean Challenge Statements

```lean
import FormalSystem.StarLanguage.Embedding
import FormalSystem.Metalogic.Conservativity.Star.StarAxiomValidity
import FormalSystem.Semantics.PlusPasting

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.PlusLanguage
open FormalSystem.ProofSystem (FrameClass)

def RecallFree : StarFormula → Prop := sorry

theorem RecallFree.swapTemporal {φ : StarFormula} (h : RecallFree φ) :
    RecallFree φ.swapTemporal := sorry

def StarIsPureFuture : StarFormula → Prop := sorry

def StarIsPurePast : StarFormula → Prop := sorry

theorem StarIsPureFuture.swapTemporal {φ : StarFormula} (h : StarIsPureFuture φ) :
    StarIsPurePast φ.swapTemporal := sorry

theorem StarIsPurePast.swapTemporal {φ : StarFormula} (h : StarIsPurePast φ) :
    StarIsPureFuture φ.swapTemporal := sorry

theorem recallFree_ofPlus (ψ : PlusFormula) : RecallFree (ofPlus ψ) := sorry

theorem starIsPureFuture_ofPlus {ψ : PlusFormula} (h : IsPureFuture ψ) :
    StarIsPureFuture (ofPlus ψ) := sorry

theorem starIsPurePast_ofPlus {ψ : PlusFormula} (h : IsPurePast ψ) :
    StarIsPurePast (ofPlus ψ) := sorry

theorem StarFormula.swap_temporal_kPlus (φ : StarFormula) :
    (StarFormula.kPlus φ).swapTemporal = StarFormula.kMinus φ.swapTemporal := sorry

theorem StarFormula.swap_temporal_kMinus (φ : StarFormula) :
    (StarFormula.kMinus φ).swapTemporal = StarFormula.kPlus φ.swapTemporal := sorry

def StarAxiom.ofPlusAxiom {φ : PlusFormula} (ax : PlusAxiom φ) : StarAxiom (ofPlus φ) := sorry

theorem StarAxiom.minFrameClass_ofPlusAxiom {φ : PlusFormula} (ax : PlusAxiom φ) :
    (StarAxiom.ofPlusAxiom ax).minFrameClass = ax.minFrameClass := sorry

def stabNecessitation {fc : FrameClass} {ψ : StarFormula}
    (d : StarDerivationTree fc [] ψ) : StarDerivationTree fc [] (StarFormula.stab ψ) := sorry

end FormalSystem.StarLanguage

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.StarLanguage
open FormalSystem.Semantics

theorem starKPlus_iff {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (v : ℕ → F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t v (StarFormula.kPlus φ) ↔
      ∀ s, t < s → τ.dom s → StarTruthAt M τ s v φ := sorry

theorem starKMinus_iff {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (v : ℕ → F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t v (StarFormula.kMinus φ) ↔
      ∀ s, s < t → τ.dom s → StarTruthAt M τ s v φ := sorry

theorem recallFree_vector_irrelevant {F : TaskFrame} (M : TaskModel F) {φ : StarFormula}
    (hφ : RecallFree φ) :
    ∀ (τ : ConvexHistory F) (t : F.Duration) (v w : ℕ → F.Duration),
      StarTruthAt M τ t v φ ↔ StarTruthAt M τ t w φ := sorry

theorem star_truth_congr_agreeFrom {F : TaskFrame} (M : TaskModel F) {φ : StarFormula}
    (hφ : StarIsPureFuture φ) :
    ∀ (τ σ : ConvexHistory F), τ.IsTotal → σ.IsTotal → ∀ t, AgreeFrom τ σ t →
      ∀ v : ℕ → F.Duration, (StarTruthAt M τ t v φ ↔ StarTruthAt M σ t v φ) := sorry

theorem star_truth_congr_agreeUpTo {F : TaskFrame} (M : TaskModel F) {φ : StarFormula}
    (hφ : StarIsPurePast φ) :
    ∀ (τ σ : ConvexHistory F), τ.IsTotal → σ.IsTotal → ∀ t, AgreeUpTo τ σ t →
      ∀ v : ℕ → F.Duration, (StarTruthAt M τ t v φ ↔ StarTruthAt M σ t v φ) := sorry

theorem star_paste_valid {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (hτ : τ.IsTotal) (t : F.Duration) (v : ℕ → F.Duration) {φ ψ : StarFormula}
    (hφ : StarIsPureFuture φ) (hψ : StarIsPurePast ψ) :
    StarTruthAt M τ t v
      (.imp (StarFormula.dstab φ)
        (.imp (StarFormula.dstab ψ) (StarFormula.dstab (φ.and ψ)))) := sorry

theorem star_untl_paste_valid {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (hτ : τ.IsTotal) (t : F.Duration) (v : ℕ → F.Duration) {α φ : StarFormula}
    (hα : StarIsPurePast α) (hφ : StarIsPureFuture φ) :
    StarTruthAt M τ t v
      (.imp (.untl α (StarFormula.dstab φ)) (StarFormula.dstab (.untl α φ))) := sorry

end FormalSystem.Metalogic.Conservativity
```

These pin the *statements*, not their homes or their implementation shapes.
`RecallFree`, `StarIsPureFuture` and `StarIsPurePast` are written above as `def … : … → Prop`
because a Challenge module forces `sorry` bodies; they land as **inductives** with the arms fixed
in Phase 2 (every `StarFormula` constructor but `timeRecall` for `RecallFree`; `PlusFormula`'s six
purity arms plus a `timeStore` arm for the two purity predicates). `starKPlus_iff` and
`starKMinus_iff` are stated here in the shape `.probes/03`/`.probes/04` verified; their exact
guard/domain phrasing may be adjusted to match the existing `StarTruth.*_iff` family. Binder order
and implicit/explicit choices may be adjusted at implementation time to match the mirrored Plus-
side declarations arm for arm; the propositional content may not.

The 53 mirror constructors, the 53 `starValid_*` lemmas and the 106 dispatch arms are
deliberately **not** pinned here: each is fixed mechanically by its `PlusAxiom` mirror's shape,
and pinning 53 restatements of `PlusAxiom` would duplicate the very inductive this task keeps
structurally comparable.

## Testing & Validation

- [ ] `lake build` exits 0
- [ ] `lake build BimodalTest` exits 0
- [ ] `bash scripts/check-module-invariants.sh` exits 0, with C2, C3, C9, C14, C15, C24 and C26
      all green
- [ ] Zero new `sorry` anywhere (C3); every unreachable result recorded as a reasoned exclusion
      with its obstruction named, never stubbed
- [ ] `grep -rn "ofBase" . --include=*.lean --include=*.md` returns hits only under `specs/`
- [ ] `grep -rn "stabNecessitationOfPlus" . --include=*.lean --include=*.md` returns hits only
      under `specs/`
- [ ] `inductive StarAxiom` has exactly 53 mirror constructors + 16 register constructors and no
      `ofBase`
- [ ] `starAxiom_validIn_min` and `starAxiom_swap_validIn_min` are both wildcard-free and have
      one arm per constructor
- [ ] `StarAxiom.minFrameClass` routes each mirror constructor to the same `FrameClass` as
      `PlusAxiom.minFrameClass` routes its mirror — proved by `minFrameClass_ofPlusAxiom`, not
      asserted
- [ ] `modal_future` is the sole constructor carrying a `RecallFree` hypothesis; `paste` and
      `untl_paste` are the sole constructors carrying purity hypotheses
- [ ] `refute_modal_future` is unchanged and still refutes MF at `↓¹p → p`
- [ ] The three conservativity results build unchanged; any direction that breaks is stated as a
      theorem, never silently weakened
- [ ] Zero task-number citations under `FormalSystem/` (C9)
- [ ] `git diff --stat` shows no change to `FormalSystem/PlusLanguage/Axioms.lean`,
      `FormalSystem/Metalogic/Soundness.lean`'s proofs, `FormalSystem/Metalogic/SoundnessLemmas/**`
      or `FormalSystem/Semantics/PlusPasting.lean`

## Artifacts & Outputs

- `FormalSystem/StarLanguage/Formula.lean` (modified: `RecallFree`, the two purity predicates,
  their swap lemmas, three `ofPlus` transfer lemmas, two swap clause lemmas)
- `FormalSystem/StarLanguage/Axioms.lean` (modified: 53 mirror constructors, 8 non-`.Base`
  `minFrameClass` arms, pins, `ofBase` deleted, module docstring rewritten)
- `FormalSystem/StarLanguage/Derivation.lean` (modified: `stabNecessitation` added,
  `stabNecessitationOfPlus` deleted, `example` retargeted, docstring section rewritten)
- `FormalSystem/StarLanguage/Embedding.lean` (modified: `ofPlusAxiom`,
  `minFrameClass_ofPlusAxiom`, `ofPlusTree` rewritten, `minFrameClass_ofBase` deleted)
- `FormalSystem/Metalogic/Conservativity/Star/StarPasting.lean` (new)
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` (modified: K± clause
  lemmas, `recallFree_vector_irrelevant`, 53 `starValid_*` lemmas, 106 dispatch arms, two
  `ofBase` arms deleted)
- `FormalSystem/Semantics/StarNonValidities.lean`,
  `FormalSystem/Metalogic/Conservativity/Star/README.md`,
  `FormalSystem/Metalogic/Conservativity/Star.lean`, `FormalSystem/StarLanguage/README.md`
  (modified: prose)
- `FormalSystem/StarLanguage.lean`, `FormalSystem/Metalogic/README.md`,
  `FormalSystem/Metalogic/Soundness.lean`, `FormalSystem/Metalogic/Conservativity.lean`,
  `docs/theorem-index.md`, `README.md` (modified: out-of-territory prose and indices)
- `specs/576_split_ofbase_eliminate_bridge_results/.probes/08_measurement-closure.lean` (new)
- `specs/576_split_ofbase_eliminate_bridge_results/plans/01_split-ofbase-eliminate-bridge-results.md`
  (this file, gaining Phase 1's `#### Measurement` table and Phase 12's `#### Restriction survey`)
- `specs/576_split_ofbase_eliminate_bridge_results/summaries/01_split-ofbase-eliminate-bridge-results-summary.md`

## Rollback/Contingency

Phases 1-3 are additive (one probe file, one new module, additive declarations in
`Formula.lean`); reverting them leaves the tree functionally unchanged. Phases 4-10 are additive
to `StarAxiom` and each ends green and committed, so any one of them reverts independently by its
own commit — the tree at that point still has `ofBase` and still builds, merely with fewer mirror
constructors than intended.

Phase 11 is the only destructive step. It is `atomic-batch` precisely because the `ofBase`
deletion, the `ofPlusAxiom` rewrite of `ofPlusTree` and the `stabNecessitation` replacement must
land together; it is guarded by `bash .claude/scripts/git-snapshot.sh 576`. If the 53-arm
dispatch cannot be completed, revert Phase 11's commit: Phases 1-10 stand on their own, the
widenings they carry are real, and the retirement is recorded as blocked rather than
half-applied. **Never leave a committed tree in which `ofBase` and its mirror constructors both
carry the same schemata beyond this task, and never leave one in which
`stabNecessitationOfPlus` and `stabNecessitation` coexist.**
