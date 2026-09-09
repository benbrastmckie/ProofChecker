# Implementation Plan: Tense-Free Stability and the Schematic Separation

- **Task**: 572 - Tense-free stability and schematic separation
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: Task 571 (schematic `Det-pm`) — `[COMPLETED]`, so `Semantics/StarDeterminism.lean` and `StarLanguage/README.md` are released territory
- **Research Inputs**: None (no research artifact for this round; the description is a specification and every structural question it raises was settled by direct reads of the tree — see Overview)
- **Artifacts**: plans/01_tense-free-stability-schematic-separation.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, .claude/rules/plan-compliance.md, .claude/rules/lean4.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

`fn_sentDet_atom` (`FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`) restricts
the forward-determinism separation to sentence letters, and its own docstring names the real
reason: "an atom's truth depends on nothing but the state at the time of evaluation". This plan
first establishes the structural result that closes that reason — a syntactic **state-locality**
fragment of `StarFormula`, proved sound against the semantic property — and only then, gated on
that result, uses it to retire the atom restriction. The refutations
`fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` are untouched: together with the new
theorem they bound the truth from both sides, and Phase 4 records that two-sided bound as a
single theorem.

### The structural question, settled by reading the truth recursion

`StarTruthAt` (`FormalSystem/Semantics/StarTruth.lean:96-108`) fixes the answer for each
constructor, at the **same evaluation time and the same register vector** — which is the
formulation the consumer actually needs (see "Why same-time, not different-times" below):

| Constructor | State-local? | Why (from the clause itself) |
|---|---|---|
| `atom p` | yes | `M.valuation (τ.states t ht) p` reads the state at `t` and nothing else |
| `bot` | yes | constant |
| `imp φ ψ` | yes if both are | pointwise |
| `box φ` | **yes, unconditionally** | `∀ σ, σ.IsTotal → StarTruthAt M σ t v φ` does not mention `τ` at all |
| `stab φ` | **yes, unconditionally** | `∀ σ, σ.IsTotal → SameStateAt τ σ t → …`, and `sameStateAt_congr_left` (`Semantics/PlusTruth.lean:99`) says the class `⟨τ⟩ₜ` is unchanged by replacing `τ` with any history agreeing at `t` |
| `untl ψ φ` | no | quantifies over `s > t`, where the histories may diverge |
| `snce ψ φ` | no | quantifies over `s < t`, likewise |
| `timeStore i φ` | yes if `φ` is | evaluation stays at `t`; both sides update the register to the same `t` |
| `timeRecall i φ` | no | moves evaluation to `v i`, which the hypothesis at `t` does not constrain |

The task lists `box` as an OPEN QUESTION to be settled rather than assumed. The reading above
settles it **positively and more strongly than the description anticipated**: `box φ` and `stab φ`
are state-local for an *arbitrary* argument, because neither clause reads `τ` in a way the
same-state hypothesis fails to control. Phase 1 must confirm this by proof; if either
unconditional form resists, the fallback is the weaker recursive clause
(`.box φ => StateLocal φ`), and only if *that* also fails is the constructor excluded with a
recorded countermodel.

### Why same-time, not different-times

`stab_state_only` (`Semantics/PlusTruth.lean:385`) is a **different-times** statement:
`τ.states t = σ.states s` transfers `⊡φ` from `(τ,t)` to `(σ,s)`. That shape does not generalize
to this fragment — `box φ` at `t` and at `s` can differ, and `timeStore i` writes a different time
into the register on each side. The same-time shape (`SameStateAt τ σ t`, one `t`, one `v`) is
both provable for the fragment and exactly what the consumer needs: `settledDisj_iff`
(`Semantics/StarValidity.lean:222`) evaluates `φ` at the *single* time `v 2 = y` across all
`σ ∈ ⟨τ⟩ₓ`, and `states_eq_of_forwardDeterministic` supplies `SameStateAt σ σ' y` for every such
pair when `y ≥ x`. The two lemmas compose with nothing left over.

### Research Integration

No research artifact for this round. The plan was written directly against the tree: the
constructor table above is read off `StarTruthAt`; the `SameStateAt` API
(`refl`/`symm`/`trans`/`sameStateAt_congr_left`/`sameStateAt_iff_of_total`) is
`Semantics/PlusTruth.lean:75-105`; the consumer shape is `sentDet_unfold` / `settledDisj_iff`
(`Semantics/StarValidity.lean:210-230`); and every countermodel Phase 2 needs is already
constructible from `NF`, `natHist`, `natModel` (`Semantics/PlusNonValidities.lean:65-80`), whose
`natHist` accepts an arbitrary `f : ℤ → ℕ`.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` supplied for this dispatch; `ROADMAP.md` was not consulted.

## Goals & Non-Goals

- **Goals**: `StarFormula.StateLocal`, `IsStateLocal`, `isStateLocal_of_stateLocal`,
  `isStateLocal_box`, `isStateLocal_stab`, `not_isStateLocal_someFuture`,
  `not_isStateLocal_somePast`, `not_isStateLocal_timeRecall`, `stateLocal_stab_iff`,
  `stateLocal_starValid_iff_stab`, `fn_sentDet_stateLocal`, `fn_separates`, `fn_sentDet_bounds`
- **Non-Goals**:
  - Any past-free, recall-free, or otherwise ad hoc fragment. If Phase 1's structural result
    fails, the task closes with the failure recorded; no weaker fragment is substituted.
  - A *complete* (necessary-and-sufficient) syntactic characterization of semantic state-locality.
    `StateLocal` is sound, not complete — e.g. `↑ⁱ↓ⁱφ` is semantically state-local whenever `φ` is
    but is syntactically rejected. Phase 1 records this explicitly in the module docstring so the
    gap reads as a design choice rather than an oversight.
  - Touching `fn_refutes_sentDet_somePast` or `not_forall_fn_sentDet`. Both stay exactly as they
    stand.
  - Any change to `Semantics/StarDeterminism.lean`'s `detPM` chain. `deterministic_of_detPM`
    carries its atom restriction in a **hypothesis** position, where widening weakens the theorem;
    Phase 5 records that as a reasoned exclusion rather than "widening the headline only".
  - Any uniform-substitution argument (unsound here — `Semantics/StarNonValidities.lean:60-66`
    records why).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The unconditional `box`/`stab` clauses do not go through in Lean (e.g. a domain-proof obligation in `sameStateAt_congr_left` is harder than it reads) | M | L | Phase 1 fallback ladder: unconditional → recursive (`StateLocal φ`) → excluded with countermodel. Each rung is a smaller theorem, none is a different fragment |
| The whole structural result fails | H | VL | Phase 1 is an explicit gate. On failure: record the countermodel, leave `fn_sentDet_atom` untouched, close `[COMPLETED WITH EXCLUSIONS]`, do not proceed to Phases 3-5 |
| Retiring `fn_sentDet_atom` breaks a consumer not found by the Phase 4 survey | M | L | Phase 4's Scope Hypothesis: the dependent set is exactly `ForwardDeterministicFrame.lean` (self), `StarLanguage/README.md` (3 rows), `Metalogic/Independence/README.md` (1 generated row). Confirm by `grep -rn` over `FormalSystem/ Tests/ docs/ README.md` before deleting |
| `check-module-invariants.sh` C14 (documented axiom/sorry counts) fails because new declarations pull in `Classical.choice` where a docstring claims choice-freedom | M | M | Phase 6 runs `#print axioms` on every new declaration before writing any docstring axiom claim; prefer `by_cases` on a decidable proposition or `Classical.em` explicitly, and state the actual axiom set rather than an aspirational one |
| Task 573 (`[PLANNING]`, same `StarLanguage/` neighbourhood) collides on `StarLanguage/README.md` | M | M | 572 touches only the three `fn_sentDet_atom` rows in that file, in Phase 6, as the last edit; re-read the file immediately before editing and stop if the rows have moved |
| A new module under `Semantics/` is unreachable from the build graph, tripping C6 | L | L | Phase 1 adds the `import` to `FormalSystem/Semantics.lean` in the same sub-step that creates the file |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5 | 4 |
| 5 | 6 | 2, 5 |

Phases within the same wave can execute in parallel.

### Phase 1: The state-locality fragment and its soundness theorem [COMPLETED]

**Goal**: Create `FormalSystem/Semantics/StarStateLocal.lean` carrying the syntactic predicate,
the semantic property, and the induction connecting them. **This phase is the gate for the whole
task.**

**Tasks**:
- [x] Create `FormalSystem/Semantics/StarStateLocal.lean` with the standard copyright header,
      importing `FormalSystem.Semantics.StarTruth` and `FormalSystem.Semantics.StarValidity`
- [x] Add `import FormalSystem.Semantics.StarStateLocal` to `FormalSystem/Semantics.lean` in the
      same sub-step (keeps the module in the build graph; C6 otherwise demands a manifest entry)
- [x] Define `StarFormula.StateLocal : StarFormula → Prop` by structural recursion, exactly the
      nine clauses of the Overview table *(deviation: altered — declared in `namespace FormalSystem.StarLanguage`, not `FormalSystem.Semantics` as the Challenge block shows. Lean 4 generalized field notation resolves `φ.StateLocal` only against the namespace of `φ`'s type, so every other signature in this plan — `fn_sentDet_stateLocal (hφ : φ.StateLocal)` included — requires the declaration to live there. The statement itself is byte-for-byte the Challenge's.)*
- [x] Define `IsStateLocal (φ : StarFormula) : Prop` — the semantic property, quantifying over
      every frame, model, pair of total histories, time and register vector
- [x] Prove `isStateLocal_box (φ) : IsStateLocal (.box φ)` — **this settles the task's open
      question**; the clause discards `τ`
- [x] Prove `isStateLocal_stab (φ) : IsStateLocal (.stab φ)` via `sameStateAt_congr_left`
- [x] Prove `isStateLocal_of_stateLocal : φ.StateLocal → IsStateLocal φ` by induction on `φ`,
      with the motive quantified over `v` (the `timeStore` case instantiates it at
      `Function.update v i t`)
- [x] Write the module docstring: the constructor table with the reason for each verdict; the
      same-time-vs-different-times contrast with `stab_state_only`; the explicit
      soundness-not-completeness note (`↑ⁱ↓ⁱφ`)
- [x] **GATE** (passed — the induction closed for all nine constructors with the fragment exactly as the Overview table gives it; `box` and `stab` went through in their *unconditional* form, so no rung of the fallback ladder was used): if the induction cannot be closed for the fragment as defined, walk the fallback
      ladder for the offending constructor (unconditional → recursive → excluded + countermodel).
      If no non-degenerate fragment survives, STOP: record the failure and the countermodel in
      this module, mark this phase `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions`
      table, leave `fn_sentDet_atom` untouched, and skip Phases 3-6 except the docs sub-step

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: the fragment is asserted to comprise exactly the six admitting constructors
of the Overview table (`atom`, `bot`, `imp`, `box`, `stab`, `timeStore`). Confirm at
implementation time by closing the induction with no additional hypothesis; any constructor whose
case cannot be closed moves to Phase 2's exclusion list and the table is corrected in both this
plan's summary and the module docstring.

**Files to modify**:
- `FormalSystem/Semantics/StarStateLocal.lean` - new: predicate, semantic property, soundness
- `FormalSystem/Semantics.lean` - one `import` line, placed after `StarNonValidities`

**Verification**:
- `lake env lean FormalSystem/Semantics/StarStateLocal.lean` exits 0 with no `sorry` and no error
- `grep -c "sorry" FormalSystem/Semantics/StarStateLocal.lean` is 0
- `isStateLocal_of_stateLocal` type-checks with `StateLocal` unfolded to the six admitting
  constructors

---

### Phase 2: Non-preservation witnesses for the excluded constructors [COMPLETED]

**Goal**: Prove that `untl`, `snce` and `timeRecall` are genuinely excluded — the fragment's
boundary is a theorem, not a stipulation.

**Tasks**:
- [x] Prove `not_isStateLocal_someFuture (p : Atom) : ¬ IsStateLocal (someFuture (.atom p))` over
      `NF`: `τ = natHist (fun _ => 0)`, `σ = natHist (fun s => if s ≤ 0 then 0 else 1)`, agreeing
      at `0` and disagreeing about `F p` there (`|p| = {0}` under `natModel`)
- [x] Prove `not_isStateLocal_somePast (p : Atom) : ¬ IsStateLocal (somePast (.atom p))` over `NF`
      with `σ = natHist (fun s => if s < 0 then 1 else 0)` — the same history
      `PlusNonValidities.lean` already uses for `P⊡p → ⊡Pp`
- [x] Prove `not_isStateLocal_timeRecall (p : Atom) : ¬ IsStateLocal (.timeRecall 0 (.atom p))`
      with the Phase-2 `untl` history pair and a register vector holding `1`
- [x] Record in the module docstring that all three witnesses live on one frame (`NF`), reusing
      the tree's existing countermodel rather than building a second two-state frame

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: exactly three excluded constructors, hence exactly three witness theorems,
all constructible on `NF`. Confirm at implementation time: if Phase 1's gate demoted `box` or
`stab`, add the corresponding witness here and say so in the summary; if a witness cannot be built
on `NF`, name the frame actually used.

**Files to modify**:
- `FormalSystem/Semantics/StarStateLocal.lean` - the three witness theorems and their docstrings

**Verification**:
- `lake env lean FormalSystem/Semantics/StarStateLocal.lean` exits 0
- each witness is stated as a negation of `IsStateLocal`, not of `StateLocal` (the syntactic
  predicate is `False` on these constructors by definition and would be a vacuous claim)

---

### Phase 3: The headline biconditional `φ ↔ ⊡φ` [COMPLETED]

**Goal**: The strong result the task names, in both a pointwise and a validity form.

**Tasks**:
- [x] Prove `stateLocal_stab_iff (hφ : φ.StateLocal) (M τ) (hτ : τ.IsTotal) (t v) :
      StarTruthAt M τ t v φ ↔ StarTruthAt M τ t v (.stab φ)` — `→` from
      `isStateLocal_of_stateLocal`, `←` by instantiating the `⊡` clause at `τ` itself via
      `SameStateAt.refl`
- [x] Prove `stateLocal_starValid_iff_stab (hφ : φ.StateLocal) :
      StarValid (StarFormula.iff φ (.stab φ))` via `StarValid.of_forall_total` *(deviation: altered — the plan named `TaskFrame.StarValidOn.of_forall_total`, whose conclusion is `F.StarValidOn`, not the `StarValid` this theorem states; `StarValid.of_forall_total` is the adapter with the right conclusion)*
- [x] Record in the docstring that the `←` direction is where totality is used, and that this is
      the companion facing the other way to `stab_state_only`: `stab_state_only` says `⊡φ` is
      state-local, this says a state-local `φ` is already `⊡`-stable

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Semantics/StarStateLocal.lean` - the two headline theorems

**Verification**:
- `lake env lean FormalSystem/Semantics/StarStateLocal.lean` exits 0
- `stateLocal_starValid_iff_stab` instantiates at `.atom p` to a closed term (sanity check that
  the fragment is inhabited by the atoms the old theorem covered)

---

### Phase 4: Retire the atom restriction on the separation [COMPLETED]

**Goal**: Replace `fn_sentDet_atom` with the state-local statement, strengthen `fn_separates`,
and record the two-sided bound.

**Tasks**:
- [x] Confirm the dependent set of `fn_sentDet_atom` by `grep -rn 'fn_sentDet_atom'` over
      `FormalSystem/ Tests/ docs/ README.md specs/` before any deletion
- [x] Add `import FormalSystem.Semantics.StarStateLocal` to
      `Metalogic/Independence/ForwardDeterministicFrame.lean`
- [x] Prove `fn_sentDet_stateLocal (φ : StarFormula) (hφ : φ.StateLocal) :
      FN.StarValidOn (sentDet φ)`, following `fn_sentDet_atom`'s existing proof shape:
      `sentDet_unfold`, `settledDisj_iff`, `update_two_apply_two`, then `by_cases` on
      `StarTruthAt M τ y v φ` with `states_eq_of_forwardDeterministic` supplying
      `SameStateAt τ σ y` for `y ≥ x` and `isStateLocal_of_stateLocal` transporting truth
- [x] **Delete** `fn_sentDet_atom` — do not keep both, and do not restate it as a corollary
- [x] Strengthen `fn_separates` in place to
      `(∀ φ : StarFormula, φ.StateLocal → FN.StarValidOn (sentDet φ)) ∧ ¬ FN.Deterministic`
- [x] Add `fn_sentDet_bounds`: one conjunction pairing the new validity with
      `¬ StarFormula.StateLocal (somePast (.atom p))` and `fn_refutes_sentDet_somePast p`, so the
      two-sided bound is a single machine-checked object
- [x] Update the module docstring's Main Results list and the two prose paragraphs that explain
      the sentence-letter restriction, replacing "an atom's truth depends on nothing but the state
      at the time of evaluation" with the fragment-level reason and a pointer to the new module
- [x] Leave `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` byte-for-byte unchanged

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: interface

**Scope Hypothesis**: `fn_sentDet_atom`'s dependents are exactly three sites —
`ForwardDeterministicFrame.lean` itself, `StarLanguage/README.md` (3 rows), and
`Metalogic/Independence/README.md` (1 generated inventory row). Confirm by the `grep -rn` in the
first task above; any additional site is added to Phase 6's doc list and reported in the summary.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` - import, new theorem,
  deletion of `fn_sentDet_atom`, strengthened `fn_separates`, new `fn_sentDet_bounds`, docstring

**Verification**:
- `lake env lean FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` exits 0
- `grep -rn 'fn_sentDet_atom' FormalSystem/ Tests/` returns nothing
- `grep -n 'fn_refutes_sentDet_somePast\|not_forall_fn_sentDet'` shows both still present, and
  `git diff` shows no hunk inside either declaration

---

### Phase 5: Survey and widen every other reachable atom-restricted statement [COMPLETED WITH EXCLUSIONS]

**Goal**: Discharge the description's clause (b) — widen every atom-restricted statement the new
result actually covers, and record a reason for each one it does not.

**Tasks**:
- [x] Enumerate candidates: `grep -rn '(p : Atom)' FormalSystem/Semantics/Star*.lean
      FormalSystem/Metalogic/Independence/*.lean`, keeping only statements whose atom restriction
      sits in a **conclusion** and whose proof turns on state-locality
- [x] For each candidate, decide and act:
      - covered by the fragment and in conclusion position -> widen to `φ.StateLocal`, retiring
        the atom form
      - atom restriction in a **hypothesis** position (e.g. `deterministic_of_detPM`) -> do NOT
        widen; widening weakens the theorem. Record as a reasoned exclusion
      - refutation-shaped (`refute_sentDet`, `fzero_refutes_sentDet`,
        `fn_refutes_sentDet_somePast`) -> do NOT touch; an atom-level refutation is already the
        strongest form
- [x] Write the resulting decision table into a `#### Reasoned Exclusions` subsection of this
      phase in the plan, with the `grep` output as Evidence
- [x] Apply the widenings the survey identifies, one commit per widened statement *(deviation: skipped — the survey identified zero widenings outside Phase 4, so there was no commit to make; the Scope Hypothesis anticipated exactly this)*

**Timing**: 1.5 hours

**Depends on**: 4

**Verification Tier**: interface

**Scope Hypothesis**: the candidate set is asserted to be small — the pre-scan found atom-shaped
statements at `Semantics/StarNonValidities.lean:67,82`,
`Metalogic/Independence/StarDiscrimination.lean:122,168`,
`Semantics/StarDeterminism.lean:271,313`, and the `ForwardDeterministicFrame.lean` sites Phase 4
already handled, of which the pre-scan expects **zero** further widenings (all are refutations or
hypothesis-position restrictions). Confirm by running the `grep` and classifying every hit; a
non-zero widening count is a correction to this hypothesis and must be stated in the summary.

**Files to modify**:
- whichever candidate files the survey identifies (expected: none beyond Phase 4's)
- `specs/572_tense_free_stability_and_schematic_separation/plans/01_tense-free-stability-schematic-separation.md` -
  the `#### Reasoned Exclusions` table for this phase

**Verification**:
- every candidate from the `grep` appears exactly once in the decision table, either widened or
  excluded with a reason and evidence
- `lake build` green after any widening

#### Reasoned Exclusions

The survey ran the plan's `grep -rn '(p : Atom)' FormalSystem/Semantics/Star*.lean
FormalSystem/Metalogic/Independence/*.lean` over the tree as it stands after Phase 4. Every hit
is classified below. **Widenings applied outside Phase 4: zero** — confirming this phase's Scope
Hypothesis. Two corrections to the pre-scan's line numbers are recorded in the Evidence column:
`StarNonValidities.lean`'s sites moved to `92,107` (and three new sites `129,160,180` landed
there from the concurrent `StarFormula.swapTemporal` work), and the pre-scan missed
`CoarsenedModels.lean` and the L⁺ site `PlusTruth.lean:232` entirely.

| Item | Reason | Evidence |
|---|---|---|
| `refute_sentDet` | Refutation-shaped. An atom-level refutation is the **strongest** form: it says the schema fails already at the simplest instance. Widening would weaken it. | `Semantics/StarNonValidities.lean:92` |
| `not_starValid_sentDet` | Refutation-shaped; it is `refute_sentDet` relayed to unrestricted validity. | `Semantics/StarNonValidities.lean:107` |
| `refute_modal_future` | Refutation-shaped. Also outside this task's territory (concurrent MF/erasure work owns that file). | `Semantics/StarNonValidities.lean:129` |
| `storeG_recall_valid` | Conclusion-position atom, but **not covered by the fragment**: the formula is `↑¹G↓¹p → p`, whose proof turns on the atom clause not reading the *register vector*, not on state-locality. Its `↓¹` subformula puts it outside `StateLocal` outright, and `G` puts it outside too. Also outside territory. | `Semantics/StarNonValidities.lean:160` |
| `refute_erasure` | Refutation-shaped; also outside territory. | `Semantics/StarNonValidities.lean:180` |
| `fzero_refutes_sentDet` | Refutation-shaped. | `Metalogic/Independence/StarDiscrimination.lean:122` |
| `sentDet_discriminates` | A **contrast at one formula**: valid over `F¹`, refuted over `F°`, at the same `φ`. Both halves are already at their strongest — the positive half is the instance of the fully schematic `f1_sentDet (φ : StarFormula)`, and the negative half is an atom-level refutation. Widening the shared `φ` to `φ.StateLocal` would make the negative half a weaker claim while adding nothing to the positive one. | `Metalogic/Independence/StarDiscrimination.lean:168`; `f1_sentDet` at `:154` is already schematic |
| `deterministic_of_detPM` | Atom restriction sits in a **hypothesis**. Widening it weakens the theorem — the whole point of the converse is that the atomic fragment already *forces* determinism. | `Semantics/StarDeterminism.lean:271` |
| Theorem C's left conjunct | Same hypothesis-position reason; it is `deterministic_of_detPM`'s statement inside the three-way equivalence. | `Semantics/StarDeterminism.lean:314` |
| `cValid_atom_stab` | Conclusion-position atom, and its proof *does* turn on a locality property — but the wrong one: `K.atom_inv`, a field of the coarsening structure, not state-locality of a fragment. It is also an L⁺ (`PlusFormula`) statement, and it exists to discharge exactly one arm of `naiveAxiom_cValid`'s `PlusAxiom` dispatch, where the AS axiom is itself atom-restricted. | `Metalogic/Independence/CoarsenedModels.lean:454`; consumer arm in `naiveAxiom_cValid` |
| `CoarsenedModels.lean:113`, `:158`; `StateSetTruth.lean:93`; `PastingIndependence.lean:174-277`; `StabUndefinable.lean:168-235`; `StarTruth.lean:115` | Not atom-*restricted statements* at all: clause lemmas (`atom_iff`, `mem_satSet_atom`), coarsening-structure fields, and refutation witnesses whose `p` names a particular separator. None has an atom restriction that state-locality could lift. | the `grep` output |
| `stab_atom_of_atom` (L⁺) | **The one genuine near-miss, recorded rather than silently skipped.** It is the L⁺ shadow of this task's headline: `p → ⊡p` for atoms, proved from exactly the state-locality reason. The result *does* cover it — but in L⋆, where the widening already landed as `stateLocal_stab_iff`. Widening the L⁺ statement itself would require a second fragment defined by recursion on `PlusFormula`, which the plan's Non-Goals and the task's declared territory both exclude; and its two consumers (`Metalogic/Conservativity/Plus/AxiomValidity.lean:147,263`) need precisely the atom instance, the AS axiom being atom-restricted in the proof system. A future task could define the L⁺ fragment as `(ofPlus φ).StateLocal` and transfer along `starTruthAt_ofPlus` at no proof cost. | `Semantics/PlusTruth.lean:232`; consumers at `Metalogic/Conservativity/Plus/AxiomValidity.lean:147,263`; missed by the plan's pre-scan, whose `grep` scope was `Semantics/Star*.lean` plus `Metalogic/Independence/` |

---

### Phase 6: Documentation, indices, and the full gate [NOT STARTED]

**Goal**: Bring every index, README and docstring into agreement with the tree, and pass the
repository gate.

**Tasks**:
- [ ] `FormalSystem/Semantics.lean`: add the `StarStateLocal` bullet to the module index docstring
      (matching the `PlusTruth`/`StarTruth` bullet style)
- [ ] `FormalSystem/Semantics/README.md`: add the `StarStateLocal.lean` table row
- [ ] `FormalSystem/Semantics/StarTruth.lean`: refine design note **(b)**. It currently says the
      `stab_state_only` analogue "must not be sought", which a reader would take as forbidding
      this work. State precisely what fails (the **different-times** transfer, inside a recall
      scope) and what now holds (same-time state-locality for the `StateLocal` fragment), with a
      pointer to the new module. Do not weaken the existing warning about extending the
      atomization route to `StarFormula`
- [ ] `FormalSystem/StarLanguage/README.md`: update the three `fn_sentDet_atom` rows (module
      inventory, correspondence table, and the "One recorded divergence" paragraph). Re-read the
      file immediately before editing — task 573 is active in this neighbourhood
- [ ] `FormalSystem/Metalogic/Independence/README.md`: regenerate the inventory block
      (`bash scripts/readme-inventory.sh`) so the `ForwardDeterministicFrame.lean` line count and
      summary are current
- [ ] `docs/theorem-index.md`: add rows for the new public declarations, each carrying its paper
      anchor or the literal `Paper: —` plus a reason (this result is not a manuscript theorem;
      it is the structural closure of `fn_sentDet_atom`'s docstring reason)
- [ ] Run `#print axioms` on every new declaration and write the **actual** axiom set into any
      docstring that makes an axiom claim — never an aspirational one (C14)
- [ ] Run the full gate

**Timing**: 1.5 hours

**Depends on**: 2, 5

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`,
  `FormalSystem/Semantics/StarTruth.lean`, `FormalSystem/StarLanguage/README.md`,
  `FormalSystem/Metalogic/Independence/README.md`, `docs/theorem-index.md`

**Verification**:
- `lake build` exits 0
- `bash scripts/check-module-invariants.sh` exits 0
- `grep -rn 'sorry' FormalSystem/Semantics/StarStateLocal.lean` returns nothing
- no task-number citation under `FormalSystem/` (C9)

## Lean Challenge Statements

```lean
import FormalSystem.Semantics.StarTruth
import FormalSystem.Semantics.StarValidity
import FormalSystem.Semantics.StarDeterminism
import FormalSystem.Metalogic.Independence.ForwardDeterministicFrame

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.StarLanguage
open FormalSystem.StarLanguage.StarFormula

/-- The syntactic state-locality fragment of L⋆. -/
def StarFormula.StateLocal : StarFormula → Prop
  | .atom _ => True
  | .bot => True
  | .imp φ ψ => StarFormula.StateLocal φ ∧ StarFormula.StateLocal ψ
  | .box _ => True
  | .untl _ _ => False
  | .snce _ _ => False
  | .stab _ => True
  | .timeStore _ φ => StarFormula.StateLocal φ
  | .timeRecall _ _ => False

/-- The semantic property the syntactic fragment approximates. -/
def IsStateLocal (φ : StarFormula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ σ : ConvexHistory F), τ.IsTotal → σ.IsTotal →
    ∀ (t : F.Duration) (v : ℕ → F.Duration), SameStateAt τ σ t →
      (StarTruthAt M τ t v φ ↔ StarTruthAt M σ t v φ)

theorem isStateLocal_box (φ : StarFormula) : IsStateLocal (.box φ) := sorry

theorem isStateLocal_stab (φ : StarFormula) : IsStateLocal (.stab φ) := sorry

theorem isStateLocal_of_stateLocal {φ : StarFormula} (hφ : φ.StateLocal) :
    IsStateLocal φ := sorry

theorem not_isStateLocal_someFuture (p : Atom) :
    ¬ IsStateLocal (StarFormula.someFuture (.atom p)) := sorry

theorem not_isStateLocal_somePast (p : Atom) :
    ¬ IsStateLocal (StarFormula.somePast (.atom p)) := sorry

theorem not_isStateLocal_timeRecall (p : Atom) :
    ¬ IsStateLocal (.timeRecall 0 (.atom p)) := sorry

theorem stateLocal_stab_iff {F : TaskFrame} {φ : StarFormula} (hφ : φ.StateLocal)
    (M : TaskModel F) (τ : ConvexHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (v : ℕ → F.Duration) :
    StarTruthAt M τ t v φ ↔ StarTruthAt M τ t v (.stab φ) := sorry

theorem stateLocal_starValid_iff_stab {φ : StarFormula} (hφ : φ.StateLocal) :
    StarValid (StarFormula.iff φ (.stab φ)) := sorry

end FormalSystem.Semantics

namespace FormalSystem.Metalogic.Independence

open FormalSystem.Syntax
open FormalSystem.Semantics
open FormalSystem.StarLanguage

theorem fn_sentDet_stateLocal (φ : StarFormula) (hφ : φ.StateLocal) :
    FN.StarValidOn (sentDet φ) := sorry

theorem fn_separates :
    (∀ φ : StarFormula, φ.StateLocal → FN.StarValidOn (sentDet φ)) ∧
      ¬ FN.Deterministic := sorry

theorem fn_sentDet_bounds (p : Atom) :
    (∀ φ : StarFormula, φ.StateLocal → FN.StarValidOn (sentDet φ)) ∧
      ¬ StarFormula.StateLocal (StarFormula.somePast (.atom p)) ∧
      ¬ FN.StarValidOn (sentDet (StarFormula.somePast (.atom p))) := sorry

end FormalSystem.Metalogic.Independence
```

## Testing & Validation

- [ ] `lake build` exits 0
- [ ] `bash scripts/check-module-invariants.sh` exits 0
- [ ] Zero `sorry` in every file touched
- [ ] `grep -rn 'fn_sentDet_atom' FormalSystem/ Tests/` returns nothing (the old statement is
      retired, not duplicated)
- [ ] `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` are unchanged in `git diff`
- [ ] Every excluded constructor has a non-preservation witness theorem, or a recorded reason
- [ ] No task-number citation under `FormalSystem/`

## Artifacts & Outputs

- `FormalSystem/Semantics/StarStateLocal.lean` (new)
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` (modified)
- `FormalSystem/Semantics/StarTruth.lean` (docstring note (b) refined)
- `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`,
  `FormalSystem/StarLanguage/README.md`, `FormalSystem/Metalogic/Independence/README.md`,
  `docs/theorem-index.md` (indices and prose)
- `specs/572_tense_free_stability_and_schematic_separation/summaries/01_tense-free-stability-schematic-separation-summary.md`

## Rollback/Contingency

Every phase commits separately, so any phase can be reverted with `git revert` on its own commit.
The one irreversible-looking step is Phase 4's deletion of `fn_sentDet_atom`; it is confined to a
single commit whose revert restores the theorem verbatim. If Phase 1's gate fails, nothing after
it runs: `fn_sentDet_atom` is never touched, the failure and its countermodel are recorded in
`StarStateLocal.lean`, and the task closes `[COMPLETED WITH EXCLUSIONS]`.
