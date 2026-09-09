# Implementation Plan: Lift the state-locality fragment to L⁺

- **Task**: 575 - Lift the state-locality fragment to L-plus and retire the atom-restricted stability lemma
- **Status**: [NOT STARTED]
- **Effort**: 10 hours
- **Dependencies**: None
- **Research Inputs**: None (Stage 1.5 assessment: the task description is a specification, not a research question — see "Research Integration" below)
- **Artifacts**: plans/01_plus-state-locality-fragment.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

`FormalSystem/Semantics/StarStateLocal.lean` gives L⋆ a fully systematic treatment of
state-locality; L⁺ has only the different-times `stab_state_only` and the ad hoc atom-level
consequence `stab_atom_of_atom` (`Semantics/PlusTruth.lean:232`). This plan builds the L⁺
fragment natively — `PlusFormula.StateLocal` by structural recursion over all seven constructors,
the semantic property, its soundness induction, the two countermodel exclusions, and the headline
`φ ↔ ⊡φ` — mirroring `StarStateLocal.lean` arm for arm; then retires `stab_atom_of_atom` by
generalizing it in place and deleting the atom-restricted statement; then makes the three
existing shapes of the concept (`stab_state_only`, `c_stab_state_only`, the L⋆ fragment) relate
explicitly to the new one, including a proved transfer along `ofPlus`. Done means: every
deliverable landed, `lake build` green, `bash scripts/check-module-invariants.sh` exit 0, and no
new `sorry`.

### Research Integration

No research report exists and none was requested. Stage 1.5's assessment: the task description
carries the defect, the ground-truth reference module, the deliverable list, the hard constraints
and the acceptance bar; every remaining unknown was resolved by targeted reads inside this
planning dispatch (the seven `PlusTruthAt` clauses, `SameStateAt`/`sameStateAt_congr_left`/
`stab_congr_sameState`, `PlusValid.of_forall_total`, the `NF`/`natHist`/`natModel` countermodel
kit, `ofPlus`'s seven arms, and the two `stab_atom_of_atom` consumers). That is planning, not
research.

Facts established during planning that the phases below rest on:

- **`box` is state-local for L⁺, unconditionally.** `PlusTruthAt M τ t (.box φ)` is
  `∀ σ, σ.IsTotal → PlusTruthAt M σ t φ` (`Semantics/PlusTruth.lean:121`) — it does not mention
  `τ`, so the two sides are literally the same proposition. Expected `Iff.rfl`, exactly as
  `isStateLocal_box`. It is still settled **by proof** in Phase 2; this is the hypothesis, not
  the result.
- **`stab` is state-local for L⁺, unconditionally, and it is already proved.**
  `stab_congr_sameState` (`Semantics/PlusTruth.lean`) is precisely the same-time statement,
  stated at domain hypotheses rather than totality. Phase 2 should discharge
  `isPlusStateLocal_stab` from it rather than re-proving it — this is the first of the three
  relations deliverable 6 asks for, landed as a proof dependency rather than as prose.
- **The `ofPlus` transfer is a clean biconditional, not merely preservation.** `ofPlus`
  (`StarLanguage/Formula.lean:319`) maps the seven L⁺ constructors onto the seven matching L⋆
  ones, and the two `StateLocal` recursions agree arm for arm on all seven
  (`True/True`, `True/True`, `∧/∧`, `True/True`, `False/False`, `False/False`, `True/True`), so
  `(ofPlus φ).StateLocal ↔ φ.StateLocal` should fall to a seven-case induction.
- **`stab_atom_of_atom` has exactly two proof consumers**, both in
  `Metalogic/Conservativity/Plus/AxiomValidity.lean` (lines 147 and 263), both discharging the
  `PlusAxiom.atom_stab p` arm, and both already sitting inside `PlusValidIn.of_forall_total`,
  which supplies the `τ.IsTotal` the generalized lemma needs (they currently discard it as `_`).
  It has five further prose-only references (`PlusTruth.lean:35`, `PlusNonValidities.lean:156`,
  `StabUndefinable.lean:48`, `StarNonValidities.lean:87`, `PlusLanguage/Axioms.lean:37,291`).
- **The prior round already surveyed the L⋆ side of deliverable 5's second half.**
  `specs/572_tense_free_stability_and_schematic_separation/plans/01_tense-free-stability-schematic-separation.md`
  Phase 5 carries a classified table of every atom-restricted statement it found, and names
  `stab_atom_of_atom` as "the one genuine near-miss", excluded on territory grounds. Phase 6 of
  this plan reuses that table's classification vocabulary and extends the scan to the L⁺ side.

### Prior Plan Reference

No prior plan exists for this task. The task-572 plan cited above is a **different task's**
artifact, consulted as evidence (see the last bullet), not as a template.

### Roadmap Alignment

No `roadmap_path` was provided in this dispatch and `roadmap_flag` is not set; no ROADMAP.md
phases are added.

## Goals & Non-Goals

**Goals** — the declarations to land:

- `PlusFormula.StateLocal`
- `IsPlusStateLocal`
- `isPlusStateLocal_box`
- `isPlusStateLocal_stab`
- `isPlusStateLocal_of_stateLocal`
- `not_isPlusStateLocal_someFuture`
- `not_isPlusStateLocal_somePast`
- `plusStateLocal_stab_iff`
- `plusStateLocal_plusValid_iff_stab`
- `stab_of_stateLocal`
- `stateLocal_ofPlus_iff`

**Goals** — the non-declaration outcomes:

- Retire the atom-restricted stability lemma at `FormalSystem/Semantics/PlusTruth.lean:232`:
  generalize in place, delete the restricted statement, update both proof consumers and all five
  prose references. Never keep both, never restate it under its old name in weakened form.
- Survey every other atom-restricted statement reachable from `Semantics/PlusTruth.lean` and
  widen each one the new result actually covers, with a per-candidate verdict and evidence.
- State, in the new module's docstring, how the L⁺ fragment relates to the L⋆ fragment along
  `ofPlus` and how both relate to the coarsened port at
  `Metalogic/Independence/CoarsenedModels.lean:325`.
- Verify explicitly — not by assumption — that the atomization route
  (`Metalogic/Conservativity/Plus/Atomization.lean`) still builds and still gets everything it
  needs from `stab_state_only`.
- `lake build` green, `bash scripts/check-module-invariants.sh` exit 0, zero new `sorry`, zero
  task-number citations under `FormalSystem/`.

**Non-Goals**:

- Changing the statement of `stab_state_only`. It is not atom-restricted, so it is not a
  widening candidate; it is a hard-constraint consumer to be protected, not edited.
- Widening the `PlusAxiom.atom_stab` **axiom constructor** (`PlusLanguage/Axioms.lean:291`).
  That would change the deductive system TM⁺ and every soundness/completeness proof over it.
  Only its semantic witness is generalized. Phase 6 records this as an evidenced exclusion.
- Any edit to `FormalSystem/StarLanguage/**` or to `Semantics/StarStateLocal.lean`.
- Weakening the hypotheses of `IsPlusStateLocal` below `StarStateLocal.lean`'s shape. Deliverable
  2 demands arm-for-arm structural comparability; a possible strengthening (domain-at-`t` in
  place of `IsTotal`) is recorded in the docstring as a deliberate deferral, not taken.
- Completeness of the syntactic fragment. Like its L⋆ twin it is sufficient, not necessary.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Name collision in `FormalSystem.Semantics`: `IsStateLocal`, `isStateLocal_box`, `isStateLocal_stab`, `isStateLocal_of_stateLocal`, `stateLocal_stab_iff` are all already taken by `StarStateLocal.lean` in that same namespace, and `FormalSystem/Semantics.lean` imports both | H | H | The `IsPlusStateLocal`/`isPlusStateLocal_*`/`plusStateLocal_*` prefixes fixed in the Goals list above are chosen for exactly this reason. Confirm with `grep -rn "theorem isPlusStateLocal\|def IsPlusStateLocal"` before and `lake build` after |
| Ambiguity between `FormalSystem.PlusLanguage.stateLocal_atom` and `FormalSystem.StarLanguage.stateLocal_atom` in any module that opens both namespaces | M | M | Only the Phase 7 transfer module sees both. It must qualify rather than `open` both; this is a stated Phase 7 task |
| Placing the `ofPlus` transfer in the new fragment module would force `Metalogic/Conservativity/Plus/AxiomValidity.lean` (which must import the fragment module after Phase 5) to depend on the entire L⋆ tower, inverting the L → L⁺ → L⋆ layering | H | H | Split: the fragment lives in `Semantics/PlusStateLocal.lean` (L⋆-free); the transfer lives in a second small module `Semantics/StateLocalTransfer.lean` sitting above both. See "Territory note" below |
| Deleting `stab_atom_of_atom` breaks `AxiomValidity.lean`, and through it the atomization route | H | M | Phase 5 is a single `full`-tier phase covering deletion, both call-site substitutions and the whole-tree build; the `Atomization.lean` verification is an explicit task, not an assumption |
| The generalized `stab_of_stateLocal` requires `τ.IsTotal` where `stab_atom_of_atom` required none — a hypothesis the consumers must be able to supply | M | L | Established during planning: both call sites are already inside `PlusValidIn.of_forall_total`, which binds `τ.IsTotal` (currently discarded as `_`). Phase 5 re-verifies at the call site rather than trusting this note |
| `box` turns out **not** to be state-local for L⁺ despite holding for L⋆ | H | L | This is a named significant finding, not a failure: Phase 2 then excludes `box` from the recursion, records the countermodel alongside Phase 3's, and every downstream phase's `box` arm follows the exclusion. Phase 2 carries a Scope Hypothesis line for this |
| Adding two files perturbs `check-module-invariants.sh` (generated inventory totals in `README.md`, C5 markdown module paths, C15 theorem-index anchoring, C24 `Init` reachability, C19 docstring coverage) | M | M | Phase 8 is a dedicated documentation-and-gate phase running `--emit-inventory` and the full gate; every new declaration carries a docstring and a `Paper:` anchor from the moment it is written |
| Countermodel arithmetic on `NF`/`natModel` differs from the L⋆ proofs because L⁺ has no register vector | L | M | The `PlusNonValidities.lean` refutations are the closer model to copy from than the `StarStateLocal.lean` ones; both are available |

**Territory note (stated assumption, not a silent widening).** The dispatch names the territory
as `Semantics/PlusTruth.lean`, a new state-locality module under `Semantics/`, and
`Semantics/README.md`, and forbids touching `StarLanguage/` or `StarStateLocal.lean`. Two
deliverables cannot be met inside that literal boundary, so this plan proceeds under explicit
assumptions and touches neither forbidden path:

1. **Deliverable 5 requires editing consumers.** "Delete the atom-restricted statement" plus
   "`lake build` green" forces the two `AxiomValidity.lean` call sites and the five prose
   references. Edits there are restricted to mechanical call-site substitution and reference
   renaming — no restatement, no weakening.
2. **Deliverable 6 requires a second new module.** The transfer lemma is provable (see Research
   Integration), so "if a transfer lemma along `ofPlus` is provable, prove it" applies; but
   proving it inside the fragment module drags L⋆ into L⁺ conservativity. A second small module
   above both towers is the only placement that both proves the lemma and preserves the layering.
   The obstruction that forces the split is recorded in both modules' docstrings.
3. **Registration files follow mechanically**: `FormalSystem/Semantics.lean` (aggregator import
   plus module-index bullet) and `docs/theorem-index.md` (rows mirroring the L⋆ twin's rows 154
   and 155), both required for the gate.

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4, 7 | 2 |
| 4 | 5 | 4 |
| 5 | 6 | 5 |
| 6 | 8 | 3, 6, 7 |

Phases within the same wave can execute in parallel. Phase 7 depends on 2 only for the module
docstring's relation prose; its lemma depends on Phase 1 alone.

---

### Phase 1: The syntactic fragment `PlusFormula.StateLocal` [NOT STARTED]

**Goal**: Create `FormalSystem/Semantics/PlusStateLocal.lean` with the syntactic predicate by
structural recursion over all seven `PlusFormula` constructors, its `@[simp]` clause lemmas, and
the derived-operator closure lemmas — mirroring `StarStateLocal.lean`'s first namespace block arm
for arm.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/PlusStateLocal.lean` with the standard copyright header
      (copy the shape from `StarStateLocal.lean`; `bash scripts/check-copyright-headers.sh`
      must accept it) and `import FormalSystem.Semantics.PlusNonValidities`
- [ ] Write a placeholder module docstring with `# Main Definitions` / `# Main Results` /
      `## Tags` sections; the full relation prose lands in Phase 8
- [ ] In `namespace FormalSystem.PlusLanguage`, define `PlusFormula.StateLocal : PlusFormula →
      Prop` by structural recursion, one arm per constructor: `atom`/`bot` `True`, `imp`
      conjunctive, `box` `True`, `untl`/`snce` `False`, `stab` `True`
- [ ] Add the `@[simp]` clause lemmas mirroring `StarStateLocal.lean`'s: `stateLocal_atom`,
      `stateLocal_bot`, `stateLocal_imp_iff`, `stateLocal_box`, `not_stateLocal_untl`,
      `not_stateLocal_snce`, `stateLocal_stab`
- [ ] Add `not_stateLocal_someFuture` and `not_stateLocal_somePast` (`someFuture` is `untl top`,
      `somePast` is `snce top` — `Semantics/PlusTruth.lean` clause lemmas confirm the unfoldings)
- [ ] Add the derived-operator closure lemmas `StateLocal.neg`, `StateLocal.and`, `StateLocal.or`
- [ ] Give every declaration a docstring (C19 floor) and no task-number citation (C9)
- [ ] `lake build FormalSystem.Semantics.PlusStateLocal` green

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: seven constructors, and the seven clause lemmas plus two derived-operator
exclusions plus three closure lemmas listed above. Confirm the constructor count against
`FormalSystem/PlusLanguage/Formula.lean:90-106` at implementation time; if a constructor has been
added or removed since this plan was written, the recursion must cover the actual set and the
count here is superseded.

**Files to modify**:
- `FormalSystem/Semantics/PlusStateLocal.lean` — new file

**Verification**:
- `lake build FormalSystem.Semantics.PlusStateLocal` exits 0, zero `sorry`
- `grep -c "^| \." ` over the recursion confirms one arm per constructor
- `bash scripts/check-copyright-headers.sh` accepts the new file

---

### Phase 2: The semantic property and the soundness induction [NOT STARTED]

**Goal**: Define `IsPlusStateLocal`, settle `box` and `stab` **by proof** for arbitrary
arguments, and prove the seven-case soundness induction `isPlusStateLocal_of_stateLocal`.

**Tasks**:
- [ ] Define `IsPlusStateLocal (φ : PlusFormula) : Prop` in `namespace FormalSystem.Semantics`,
      mirroring `IsStateLocal`'s shape minus the register vector (L⁺ has no registers): quantify
      `F`, `M`, `τ`, `σ`, `τ.IsTotal`, `σ.IsTotal`, `t`, `SameStateAt τ σ t`, conclude the
      `PlusTruthAt` biconditional
- [ ] Docstring the deliberate non-weakening: the hypotheses could be `τ.domain t`/`σ.domain t`
      rather than totality; totality is kept for arm-for-arm comparability with `IsStateLocal`
- [ ] Prove `isPlusStateLocal_box` for an arbitrary `φ`. Expected `Iff.rfl` — the `box` clause
      never mentions `τ`. **If it does not go through**, stop, produce a countermodel, exclude
      `box` from Phase 1's recursion, and record the finding prominently (see Scope Hypothesis)
- [ ] Prove `isPlusStateLocal_stab` for an arbitrary `φ` **from `stab_congr_sameState`**
      (`Semantics/PlusTruth.lean`) rather than re-deriving it from `sameStateAt_congr_left`; this
      proof dependency is itself one of deliverable 6's three relations
- [ ] Prove `isPlusStateLocal_of_stateLocal : ∀ {φ}, φ.StateLocal → IsPlusStateLocal φ` by
      induction, seven cases: `atom` by the valuation transfer, `bot` `Iff.rfl`, `imp` by
      `imp_congr` on the two IHs, `box`/`stab` by the two lemmas above with no IH, `untl`/`snce`
      vacuous via `not_stateLocal_untl`/`not_stateLocal_snce`
- [ ] Give each declaration a `Paper:` anchor line or the literal `Paper: —` plus a reason,
      mirroring `isStateLocal_of_stateLocal`'s
- [ ] `lake build FormalSystem.Semantics.PlusStateLocal` green

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: seven induction cases, and `box`/`stab` hold unconditionally. Confirm by
proof, not by analogy with L⋆. If `box` fails, the phase closes as
`[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record naming the countermodel,
Phase 1's recursion is amended, and Phase 3 gains a third exclusion.

**Files to modify**:
- `FormalSystem/Semantics/PlusStateLocal.lean` — add the semantics namespace block

**Verification**:
- `lake build FormalSystem.Semantics.PlusStateLocal` exits 0, zero `sorry`
- `grep -n "| atom\|| bot\|| imp\|| box\|| untl\|| snce\|| stab" ` over the induction shows all
  seven arms present
- `isPlusStateLocal_stab`'s proof term mentions `stab_congr_sameState`

---

### Phase 3: The countermodel exclusions [NOT STARTED]

**Goal**: Exclude the failing constructors by **theorem**, not by stipulation:
`not_isPlusStateLocal_someFuture` and `not_isPlusStateLocal_somePast` on `NF` with `natModel`.

**Tasks**:
- [ ] Add the three private witness histories on `NF` mirroring `StarStateLocal.lean`'s
      (`zeroHist`, `lateHist`, `earlyHist`) and their `SameStateAt`-at-`0` lemmas, adapted to
      `PlusTruthAt`. Prefer `PlusNonValidities.lean`'s proof idiom over `StarStateLocal.lean`'s
      where they differ — the former is already register-free
- [ ] Prove `not_isPlusStateLocal_someFuture (p : Atom)` using `PlusTruth.someFuture_iff`:
      `F p` holds at `(zeroHist, 0)` and fails at `(lateHist, 0)`
- [ ] Prove `not_isPlusStateLocal_somePast (p : Atom)` using `PlusTruth.somePast_iff`
      symmetrically with `earlyHist`
- [ ] If Phase 2 excluded `box`, add its countermodel here too
- [ ] Docstring each as the `untl` / `snce` exclusion respectively, and state (as
      `StarStateLocal.lean` does) that both live on one frame — no second countermodel frame is
      built
- [ ] `lake build FormalSystem.Semantics.PlusStateLocal` green

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: exactly two exclusions are needed (`untl`, `snce`) — the L⁺ case is
strictly easier than L⋆'s because there are no registers and `timeRecall` does not arise. Confirm
by checking that every constructor whose `StateLocal` arm is `False` after Phase 2 has a
corresponding `not_isPlusStateLocal_*` theorem; a mismatch means the hypothesis was wrong and the
missing exclusion must be added.

**Files to modify**:
- `FormalSystem/Semantics/PlusStateLocal.lean` — add the exclusions section

**Verification**:
- `lake build FormalSystem.Semantics.PlusStateLocal` exits 0, zero `sorry`
- Every `False` arm of `PlusFormula.StateLocal` has a matching `not_isPlusStateLocal_*` theorem

---

### Phase 4: The headline biconditional and the generalized stability lemma [NOT STARTED]

**Goal**: `φ ↔ ⊡φ` on the fragment, pointwise and as a validity, plus the one-directional
`stab_of_stateLocal` that Phase 5 substitutes for the retired atom-restricted lemma.

**Tasks**:
- [ ] Prove `plusStateLocal_stab_iff`: pointwise `PlusTruthAt M τ t φ ↔ PlusTruthAt M τ t
      (.stab φ)` for `φ.StateLocal` at a total `τ`. `→` from `isPlusStateLocal_of_stateLocal`;
      `←` by instantiating the `stab` clause at `τ` itself via `SameStateAt.refl` — the only
      place `τ.IsTotal` is used
- [ ] Prove `plusStateLocal_plusValid_iff_stab : PlusValid (PlusFormula.iff φ (.stab φ))` from it,
      via `PlusValid.of_forall_total` and the `PlusTruth.and_iff`/`imp_iff` clause lemmas,
      mirroring `stateLocal_starValid_iff_stab`
- [ ] Prove `stab_of_stateLocal` — the `→` half in the argument shape the retired lemma had
      (`M`, `τ`, `hτ`, `t`, hypothesis `PlusTruthAt M τ t φ`, conclusion `PlusTruthAt M τ t
      (.stab φ)`) — so Phase 5's call sites are a one-line substitution
- [ ] Docstring `stab_of_stateLocal` as the strict generalization of the retired atom-restricted
      lemma, naming what it strictly extends
- [ ] `Paper: —` anchors with reasons on the two headline results, mirroring the L⋆ twins
- [ ] `lake build FormalSystem.Semantics.PlusStateLocal` green

**Timing**: 1 hour

**Depends on**: 2

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Semantics/PlusStateLocal.lean` — add the headline section

**Verification**:
- `lake build FormalSystem.Semantics.PlusStateLocal` exits 0, zero `sorry`
- `stab_of_stateLocal` typechecks when applied at `stateLocal_atom p` — confirm with a scratch
  `example` (removed before commit) or `lean_multi_attempt`

---

### Phase 5: Retire `stab_atom_of_atom` [NOT STARTED]

**Goal**: Delete the atom-restricted statement, redirect both proof consumers to
`stab_of_stateLocal`, update every prose reference, and verify explicitly that the atomization
route is intact.

**Tasks**:
- [ ] Add `import FormalSystem.Semantics.PlusStateLocal` to
      `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean` and confirm no import cycle
      (`bash scripts/check-metalogic-cycles.sh` if applicable; otherwise the build settles it)
- [ ] Replace both `atom_stab p` arms (`AxiomValidity.lean:147` and `:263`) with
      `stab_of_stateLocal (stateLocal_atom p) …`, binding the `τ.IsTotal` currently discarded as
      `_` in the `PlusValidIn.of_forall_total` lambda
- [ ] Delete `theorem stab_atom_of_atom` from `FormalSystem/Semantics/PlusTruth.lean` (currently
      at `:232`). Do not rename it, do not leave a specialization behind, do not restate it in
      weakened form
- [ ] Update the `Main Results` bullet at `PlusTruth.lean:35` to name the new lemma and its module
- [ ] Update the four remaining prose references: `PlusNonValidities.lean:156`,
      `Metalogic/Independence/StabUndefinable.lean:48`,
      `Semantics/StarNonValidities.lean:87`, `PlusLanguage/Axioms.lean:37` and `:291`
- [ ] Confirm zero residue: `grep -rn "stab_atom_of_atom" --include=*.lean --include=*.md .`
      returns hits only under `specs/`
- [ ] **Verify the atomization route explicitly**: `lake build
      FormalSystem.Metalogic.Conservativity.Plus.Atomization` and
      `…Plus.AxiomValidity` both green; confirm `Atomization.lean` still consumes
      `stab_state_only` unchanged (`grep -n "stab_state_only" Atomization.lean` shows the same
      call at `:198` against an unmodified statement)
- [ ] Full `lake build` green

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: two proof consumers and five prose references, enumerated in Research
Integration above. Re-run the residue `grep` at implementation time before deleting; if the hit
set differs from this list, the actual set governs and this count is superseded.

**Files to modify**:
- `FormalSystem/Semantics/PlusTruth.lean` — delete the theorem, update the Main Results bullet
- `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean` — import plus two call sites
- `FormalSystem/Semantics/PlusNonValidities.lean` — prose reference
- `FormalSystem/Metalogic/Independence/StabUndefinable.lean` — prose reference
- `FormalSystem/Semantics/StarNonValidities.lean` — prose reference
- `FormalSystem/PlusLanguage/Axioms.lean` — two prose references

**Verification**:
- `lake build` exits 0 with zero `sorry`
- `grep -rn "stab_atom_of_atom" --include=*.lean --include=*.md .` returns nothing outside
  `specs/`
- `stab_state_only`'s statement is byte-identical to its pre-phase form (`git diff` on
  `PlusTruth.lean` shows only the deletion and the docstring bullet)

---

### Phase 6: The atom-restricted survey on the L⁺ side [NOT STARTED]

**Goal**: Enumerate every other atom-restricted statement reachable from `Semantics/PlusTruth.lean`,
give each a widen-or-exclude verdict with evidence, and apply every widening the new result
actually covers.

**Tasks**:
- [ ] Scan the reachable L⁺ scope: `grep -rn "(p : Atom)\|(p q : Atom)\|(a : Atom)"` over
      `FormalSystem/Semantics/Plus*.lean`, `FormalSystem/PlusLanguage/`,
      `FormalSystem/Metalogic/Conservativity/Plus/`, and
      `FormalSystem/Metalogic/Independence/CoarsenedModels.lean`
- [ ] Classify each hit using the vocabulary the prior round established
      (`specs/572_.../plans/01_….md` Phase 5 table): refutation-shaped (widening weakens —
      exclude), hypothesis-position atom (widening weakens — exclude), clause lemma or structure
      field (not an atom-restricted statement — exclude), conclusion-position atom covered by the
      new result (**widen**)
- [ ] Decide each conclusion-position candidate **by attempting the widening**, not by
      inspection. Known candidates to reach a verdict on, each with evidence:
      `PlusNonValidities.lean`'s five refutations (`refute_stab_box`, `refute_allFuture_stab`,
      `refute_stab_allFuture_past`, `refute_determined`, `refute_somePast_stab`);
      `PlusTruth.atom_iff`; `CoarsenedModels.lean`'s `cValid_atom_stab`; and the
      `PlusAxiom.atom_stab` constructor
- [ ] Apply every widening the verdict supports, preserving each consumer's needs (check consumers
      before editing; a widening that forces a consumer to reconstruct the old instance is not a
      widening)
- [ ] Record the full table as a `#### Reasoned Exclusions` subsection under this phase in this
      plan file, with `Item` / `Reason` / `Evidence` columns, covering every excluded candidate
- [ ] Full `lake build` green

**Timing**: 1.5 hours

**Depends on**: 5

**Verification Tier**: full

**Scope Hypothesis**: the eight named candidates above are the complete reachable set, and the
expected verdict is zero further widenings (the five refutations are refutation-shaped,
`atom_iff` is a clause lemma, `cValid_atom_stab` turns on `K.atom_inv` rather than state-locality
and lives in the coarsened truth relation the new result does not cover, and widening the axiom
constructor is a Non-Goal). Confirm by running the scan; a candidate outside this list governs
over the list.

**Files to modify**:
- Whatever the verdicts require; `specs/575_plus_state_locality_fragment/plans/01_plus-state-locality-fragment.md`
  gains the `#### Reasoned Exclusions` record either way

**Verification**:
- The scan command and its raw hit count are recorded in the Evidence column
- Every hit appears in the table with a verdict; no hit is silently dropped
- `lake build` exits 0

---

### Phase 7: The `ofPlus` transfer and the three-notion relation [NOT STARTED]

**Goal**: Prove `stateLocal_ofPlus_iff` in a module sitting above both towers, and pin the
relations the docstrings will state.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/StateLocalTransfer.lean` with the standard copyright header,
      importing `FormalSystem.Semantics.PlusStateLocal` and
      `FormalSystem.Semantics.StarStateLocal`
- [ ] Docstring the module's reason for existing: the transfer cannot live in
      `PlusStateLocal.lean` without inverting the L → L⁺ → L⋆ layering
      (`Conservativity/Plus/AxiomValidity.lean` imports the fragment module after Phase 5 and must
      not acquire an L⋆ dependency), and it cannot live in `StarStateLocal.lean`, which is outside
      this task's territory
- [ ] Do **not** `open` both `FormalSystem.PlusLanguage` and `FormalSystem.StarLanguage`:
      `stateLocal_atom`, `stateLocal_box`, `stateLocal_stab`, `stateLocal_imp_iff`,
      `not_stateLocal_untl`, `not_stateLocal_snce` exist in both. Qualify instead
- [ ] Prove `stateLocal_ofPlus_iff (φ : PlusFormula) : (StarLanguage.ofPlus φ).StateLocal ↔
      φ.StateLocal` by induction on `φ`, seven cases, unfolding `ofPlus` and both recursions
- [ ] If the induction does not close, record the specific obstruction — the exact case, the two
      arms that fail to agree, and why — in the docstring, and downgrade the statement to whatever
      direction is provable rather than leaving it unstated
- [ ] Draft the three-notion relation prose for Phase 8's docstring pass: (a) the new fragment vs.
      the L⋆ fragment along `ofPlus` — this lemma; (b) the new `isPlusStateLocal_stab` vs.
      `stab_state_only` — the same-time shadow of a different-times statement, related by
      `plusTruthAt_timeShift`, with `stab_congr_sameState` the shared core; (c) both vs.
      `c_stab_state_only` (`Metalogic/Independence/CoarsenedModels.lean:325`) — the coarsened port
      of (b), stated at `SameUnder K` (π-agreement) rather than state equality, and therefore not
      covered by the new result
- [ ] `lake build FormalSystem.Semantics.StateLocalTransfer` green

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: `ofPlus`'s seven arms and both `StateLocal` recursions agree arm for arm,
so the transfer is a biconditional. Confirm by proof; if only one direction closes, state that
direction and record the obstruction rather than asserting the biconditional.

**Files to modify**:
- `FormalSystem/Semantics/StateLocalTransfer.lean` — new file

**Verification**:
- `lake build FormalSystem.Semantics.StateLocalTransfer` exits 0, zero `sorry`
- `FormalSystem/Semantics/PlusStateLocal.lean` has no `StarLanguage` import (grep confirms the
  layering held)

---

### Phase 8: Documentation, indices, and the full gate [NOT STARTED]

**Goal**: Bring every docstring, README and index into agreement with the tree, and pass the
repository gate.

**Tasks**:
- [ ] Complete `PlusStateLocal.lean`'s module docstring: `Main Definitions`, `Main Results`, the
      seven-row constructor table (`Constructor | State-local? | Why`) mirroring
      `StarStateLocal.lean`'s nine-row one, a "Sound, not complete" note, a note that both
      exclusions live on one frame, the **three-notion relation** from Phase 7's draft, References
      and Tags
- [ ] Complete `StateLocalTransfer.lean`'s docstring symmetrically
- [ ] `FormalSystem/Semantics.lean`: add both imports and both module-index bullets, mirroring the
      `StarStateLocal` bullet at `:153-160`
- [ ] `FormalSystem/Semantics/README.md`: add a row for each new module to the module table,
      mirroring the `StarStateLocal.lean` row at `:41`
- [ ] `docs/theorem-index.md`: add rows for `isPlusStateLocal_of_stateLocal`,
      `plusStateLocal_plusValid_iff_stab` and `stateLocal_ofPlus_iff`, mirroring rows `:154-155`;
      each row's declaration must carry its anchor at the declaration itself (C15's second
      assertion) — `Paper: —` plus a reason is the correct anchor here
- [ ] `bash scripts/check-module-invariants.sh --emit-inventory` to refresh generated inventory
      blocks (`README.md`'s totals row moves when files are added), then re-run with `--check`
- [ ] Confirm zero task-number citations under `FormalSystem/` (C9) — this plan's phases are the
      only place task numbers may appear
- [ ] `lake build` green with zero `sorry`
- [ ] `bash scripts/check-module-invariants.sh` exits 0
- [ ] Write the execution summary to
      `specs/575_plus_state_locality_fragment/summaries/01_plus-state-locality-fragment-summary.md`

**Timing**: 1.5 hours

**Depends on**: 3, 6, 7

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/PlusStateLocal.lean`, `FormalSystem/Semantics/StateLocalTransfer.lean` —
  docstrings
- `FormalSystem/Semantics.lean` — imports and module index
- `FormalSystem/Semantics/README.md` — module table rows
- `docs/theorem-index.md` — three rows
- `README.md` — regenerated inventory block

**Verification**:
- `lake build` exits 0
- `bash scripts/check-module-invariants.sh` exits 0 (all of C1, C4, C5, C9, C14, C15, C19, C24,
  INV)
- `bash .claude/scripts/lean-sorry-census.sh` (or the gate's C3) reports no new `sorry`

---

## Lean Challenge Statements

```lean
import FormalSystem.Semantics.PlusNonValidities
import FormalSystem.Semantics.StarStateLocal

namespace FormalSystem.PlusLanguage

def PlusFormula.StateLocal : PlusFormula → Prop := sorry

end FormalSystem.PlusLanguage

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage

def IsPlusStateLocal (φ : PlusFormula) : Prop := sorry

theorem isPlusStateLocal_box (φ : PlusFormula) : IsPlusStateLocal (.box φ) := sorry

theorem isPlusStateLocal_stab (φ : PlusFormula) : IsPlusStateLocal (.stab φ) := sorry

theorem isPlusStateLocal_of_stateLocal {φ : PlusFormula} (hφ : φ.StateLocal) :
    IsPlusStateLocal φ := sorry

theorem not_isPlusStateLocal_someFuture (p : Atom) :
    ¬ IsPlusStateLocal (PlusFormula.someFuture (.atom p)) := sorry

theorem not_isPlusStateLocal_somePast (p : Atom) :
    ¬ IsPlusStateLocal (PlusFormula.somePast (.atom p)) := sorry

theorem plusStateLocal_stab_iff {F : TaskFrame} {φ : PlusFormula} (hφ : φ.StateLocal)
    (M : TaskModel F) (τ : ConvexHistory F) (hτ : τ.IsTotal) (t : F.Duration) :
    PlusTruthAt M τ t φ ↔ PlusTruthAt M τ t (.stab φ) := sorry

theorem plusStateLocal_plusValid_iff_stab {φ : PlusFormula} (hφ : φ.StateLocal) :
    PlusValid (PlusFormula.iff φ (.stab φ)) := sorry

theorem stab_of_stateLocal {F : TaskFrame} {φ : PlusFormula} (hφ : φ.StateLocal)
    (M : TaskModel F) (τ : ConvexHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (h : PlusTruthAt M τ t φ) : PlusTruthAt M τ t (.stab φ) := sorry

theorem stateLocal_ofPlus_iff (φ : PlusFormula) :
    (StarLanguage.ofPlus φ).StateLocal ↔ φ.StateLocal := sorry

end FormalSystem.Semantics
```

These pin the *statements*, not their homes: `PlusFormula.StateLocal` through
`stab_of_stateLocal` land in `FormalSystem/Semantics/PlusStateLocal.lean`, and
`stateLocal_ofPlus_iff` in `FormalSystem/Semantics/StateLocalTransfer.lean` (see the Territory
note). Binder order and implicit/explicit choices may be adjusted at implementation time to match
the `StarStateLocal.lean` twin arm for arm; the propositional content may not.

## Testing & Validation

- [ ] `lake build` exits 0
- [ ] Zero new `sorry` anywhere (`scripts/check-module-invariants.sh` C3)
- [ ] `bash scripts/check-module-invariants.sh` exits 0
- [ ] `grep -rn "stab_atom_of_atom" --include=*.lean --include=*.md .` returns hits only under
      `specs/`
- [ ] `stab_state_only`'s statement is unchanged; `Metalogic/Conservativity/Plus/Atomization.lean`
      builds and still cites it
- [ ] `FormalSystem/Semantics/PlusStateLocal.lean` contains no `StarLanguage` import
- [ ] `git diff --stat` shows no change under `FormalSystem/StarLanguage/` and none to
      `FormalSystem/Semantics/StarStateLocal.lean`
- [ ] Zero task-number citations under `FormalSystem/`
- [ ] Every `False` arm of `PlusFormula.StateLocal` has a matching `not_isPlusStateLocal_*`
      theorem

## Artifacts & Outputs

- `FormalSystem/Semantics/PlusStateLocal.lean` (new)
- `FormalSystem/Semantics/StateLocalTransfer.lean` (new)
- `FormalSystem/Semantics/PlusTruth.lean` (modified: theorem deleted, docstring updated)
- `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean` (modified: import, two call sites)
- `FormalSystem/Semantics/PlusNonValidities.lean`, `FormalSystem/Semantics/StarNonValidities.lean`,
  `FormalSystem/Metalogic/Independence/StabUndefinable.lean`,
  `FormalSystem/PlusLanguage/Axioms.lean` (modified: prose references)
- `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`, `docs/theorem-index.md`,
  `README.md` (modified: registration and indices)
- `specs/575_plus_state_locality_fragment/plans/01_plus-state-locality-fragment.md` (this file,
  gaining Phase 6's `#### Reasoned Exclusions` record)
- `specs/575_plus_state_locality_fragment/summaries/01_plus-state-locality-fragment-summary.md`

## Rollback/Contingency

Phases 1-4 and 7 are purely additive (two new files); reverting them removes the files and leaves
the tree byte-identical. Phase 5 is the only destructive step: it is `atomic-batch` precisely
because the deletion and the two call-site substitutions must land together, and it is guarded by
`bash .claude/scripts/git-snapshot.sh 575` before the deletion. If the atomization route breaks,
revert Phase 5's commit — the fragment modules stand on their own and Phases 6 and 8 can proceed
against a tree that still carries the atom-restricted lemma, with the retirement recorded as
blocked rather than half-applied. Never leave `stab_atom_of_atom` and `stab_of_stateLocal`
coexisting in a committed tree.
