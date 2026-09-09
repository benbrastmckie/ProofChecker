# Implementation Plan: TM⁺ deterministic completeness and ⊡ non-definability

- **Task**: 537 - tm_star_completeness_stab_nondefinability
- **Status**: [IMPLEMENTING]
- **Effort**: 26 hours
- **Dependencies**: 533 (landed), 535 (archived, ground truth), 536 (landed), 562 (completed)
- **Research Inputs**: `specs/archive/535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md`; `specs/archive/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean` (60 sorry-free declarations). No report was produced for this round; this plan was written directly against the task specification plus a read of the live tree (see Overview).
- **Artifacts**: plans/01_tm-plus-deterministic-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

This task lands the mechanical TM⁺ metatheory that task 535 found achievable: deterministic
completeness of TM⁺ + *Determined* (the paper-facing result, first), the non-definability of the
stability modal ⊡ over L, the underivability of the two pasting axioms from the naive ⊡-set, and
the conservativity corollaries that ⊡ permits. General (nondeterministic) TM⁺ completeness is
explicitly out of scope and is never to be stated-and-sorried; it belongs to tasks 559/560, which
must specialize to what this task lands.

The plan is built on a direct read of the live tree rather than a fresh research report, because
the specification already carries the defect, the ground truth and the acceptance bar, and the
remaining questions were all resolvable by targeted reads. Four load-bearing facts were confirmed
that way and they shape the phase order:

1. **Step (c) of 535 §7.3 falls out.** Every completeness engine ends in a single application
   `h_valid.apply F TM τ h_tot t` against a *concrete* constructed frame, and every one of those
   frames already carries a proved fibre-subsingleton lemma — `flowRel_fib_subsingleton`
   (`Metalogic/Algebraic/FlowFrame.lean`) for `multiFamTaskFrameGen`, of which `bundleFlowFrame`
   and `multiFamTaskFrame` are definitional specializations, and `zTaskFrameV2_fib_subsingleton`
   (`Metalogic/WeakCanonical/IntegerModel/ReynoldsBridge.lean`). `TaskFrame.Deterministic` *is*
   that predicate. So the engines can be re-read as "valid on their own deterministic countermodel
   ⇒ derivable" by widening four countermodel producers with one extra existential binder. The
   completeness half is therefore promised, not hedged.
2. **The real cost sits in step (d), not step (c).** 535 called the syntactic collapse
   `⊢ φ ↔ erase φ` "routine". It is mathematically routine but the tree has no congruence or
   replacement infrastructure for TM⁺ at all: no deduction theorem, no `Theorems/` layer over
   `PlusFormula`. Phase 5 therefore builds the one lever that makes it cheap and is reusable by
   559/560 — a substitution transfer carrying every TM theorem *schema* to TM⁺ at arbitrary
   `PlusFormula` arguments.
3. **The extended system needs its own inductive.** `PlusDerivationTree`'s necessitation,
   temporal-necessitation and temporal-duality rules are all restricted to the empty context, so
   *Determined* cannot be carried in the context; and adding a `determined` constructor to the
   live `PlusAxiom` would be unsound (it is refuted on nondeterministic frames by
   `Semantics/PlusNonValidities.lean`'s `refute_determined`). Phase 6 builds a separate system
   that stays out of the live proof system.
4. **535 §2.4's E-model argument does not mechanize as written.** The atomization step needs
   `⊡_E χ` to be a *state* formula, which the time-indexed family `E_t` in the report's
   counterexample is not; and making the family shift-invariant lets AS force E-related histories
   to agree on every atom at every time, which restores PS. Phases 11-12 replace it with a
   coarsened-state semantics (interpret ⊡ over a quotient `π` of world states) that keeps
   state-determinacy — and hence atomization — while genuinely breaking pasting.

Definition of done: all four mandatory deliverables landed sorry-free, the C2/C3/C14 invariants
green, and the documentation rows recording deterministic completeness as landed and general
completeness as open.

### Research Integration

535's report and probes are the ground truth and are consumed as follows. Probes A1-A5 and B1-B3
are already discharged in the live tree as `PlusAxiom` constructors. Probe E2
(`stab_state_only`) is the lever behind `Atomization.lean` and behind the coarsened-state
soundness of Phase 11. Probe C0's pasting lemma is the live `Semantics/PlusPasting.lean`. Probe
D4 (`refute_determined`) is what forbids adding *Determined* to the live axiom set. §6.2's two
separating models are transcribed in Phase 10; §7.3's four-step proof shape is Phases 2-4 and
8-9; §2.4's independence argument is the input to Phases 11-12, superseded in method as noted
above.

536's landed collapse is consumed, never re-derived: `states_eq_of_deterministic`,
`stab_iff_of_deterministic`, `determined_of_deterministic` and
`stab_biconditional_plusValidOn_of_deterministic` (`Semantics/PlusDeterminism.lean`, all
choice-free). 536's (T3) is honoured throughout: *Determined* is valid on a class strictly larger
than the deterministic frames (`Metalogic/Independence/DeterminismUndefinable.lean` — the drift
frame `F0` validates every instance and is not deterministic), so no statement in this plan
describes *Determined* as characterizing determinism.

### Prior Plan Reference

No prior plan for this task.

### Roadmap Alignment

No roadmap path was supplied by this dispatch; `specs/ROADMAP.md` was not consulted and is not
modified.

## Goals & Non-Goals

**Goals**:
  - Deterministic completeness, the paper-facing deliverable, landed first: the four
    deterministic-hypothesis engines `derivable_of_validDetBase`, `derivable_of_validDetDense`,
    `derivable_of_validDetZTime`, `derivable_of_validDetRTime`; the extended system
    `DetDerivable` with its erasure `erasePlus`; its soundness `detSoundness` over the frames
    validating every instance of the *Determined* schema, captured by `DeterminedValid`; and its
    completeness over the deterministic frames at each class — `detCompletenessBase`,
    `detCompletenessDense`, `detCompletenessZTime`, `detCompletenessRTime`.
  - The manuscript-usable coincidence corollary `logicDeterministicEqDeterminedValid`: the logic
    of the deterministic frames and the logic of the frames validating *Determined* coincide, and
    both are axiomatized by TM⁺ + *Determined*, even though *Determined* does not define the
    deterministic frames.
  - Non-definability of the stability modal over L: `stabNotDefinable`.
  - Non-redundancy of the two pasting axioms: `pasteNotNaiveDerivable` and
    `untlPasteNotNaiveDerivable`, against the naive-derivability predicate `NaiveDerivable`.
  - Conservativity corollaries and the derived logic of the defined modals; documentation rows
    recording deterministic completeness as landed and general completeness as open.

**Non-Goals**:
- General (nondeterministic) TM⁺ completeness at any class — task 559/560. It is never stated,
  and never discharged with `sorry`.
- Bundled TM⁺ semantics, the Lifting Lemma, naming rules — task 559. The one-dispatch Lifting
  spike that an earlier scoping put here has been removed from this task; do not attempt it.
- Store/recall operators and the characterization theorem for the deterministic frames
  (`lem:deterministic-singleton` as a biconditional, `sent:det`, `app:deterministic-future`,
  the `F0`/`F1` discrimination footnote) — task 561.
- Decidability of TM⁺ in either direction: 535 shows it is open and no easier than TM's own open
  decidability problem, with no undecidability following.
- Any statement describing the *Determined* schema as characterizing or defining determinism.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The syntactic collapse needs TM⁺ congruence infrastructure that does not exist (no deduction theorem, no `Theorems/` over `PlusFormula`) | H | H (confirmed absent) | Phase 5 builds the substitution transfer, making every TM theorem schema available at `PlusFormula` arguments; fallback is a TM⁺ deduction theorem plus hand-proved congruence at `imp`/`box`/`untl`/`snce` |
| 535 §2.4's E-model argument does not mechanize: the atomization step requires the ⊡-interpretation to be state-determined, which a time-indexed `E_t` is not, and a shift-invariant family collapses under AS | H | H (analysis above) | Phases 11-12 use a coarsened-state semantics instead, which is state-determined by construction; Phase 11 ends in an explicit go/no-go probe before Phase 12 commits |
| PS/US underivability still fails to mechanize after the coarsening | M | L | Close Phase 12 as `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` record naming the precise obstruction and the evidence; never a `sorry`, and never a weakened claim elsewhere |
| Widening the four countermodel producers touches shared engine files that other work also edits | M | L | The change is one additive existential binder plus its witness; all producers and call sites move in one commit; task 560, which shares the Conservativity/Plus territory, is sequenced after this task |
| A statement drifts into describing *Determined* as defining determinism, contradicting 536 (T3) | H | M | Every completeness statement is phrased over `TaskFrame.Deterministic`; the transfer to larger classes goes through the coincidence corollary, which cites `deterministic_not_plusDefinable` in its docstring |
| Temptation to state general TM⁺ completeness and discharge it with `sorry` | H | L | Explicit non-goal; Phase 14 records it as open in the READMEs citing Reynolds 2003 and Zanardo 1991; C3 (zero structural sorries) is a gate |
| Optional deliverable (5), compactness, exhausts the budget | L | M | Phase 15 is explicitly optional and closes as a reasoned exclusion if budget runs out; nothing else depends on it |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 5, 6 | -- |
| 2 | 3, 4, 7, 8 | 1, 2, 5, 6 |
| 3 | 9 | 3, 4, 7, 8 |
| 4 | 10, 11, 13 | 9 |
| 5 | 12 | 11 |
| 6 | 14 | 10, 12, 13 |
| 7 | 15 | 14 |

Phases within the same wave can execute in parallel. Phases 1-9 are deliverable (1) in full: the
task's PRIORITY note requires the deterministic-completeness result to land before deliverables
(2)-(4), which is why Phases 10, 11 and 13 depend on Phase 9 rather than starting in wave 1.

### Phase 1: Deterministic validity notions and the Determined-valid frame class [COMPLETED]

**Goal**: Create the new `FormalSystem/Metalogic/Deterministic/` subtree with the two
frame-predicate-restricted validity notions this task states its results against, and the
Determined-valid frame class with its strict inclusion of the deterministic frames.

**Tasks**:
- [x] Create `FormalSystem/Metalogic/Deterministic/Validity.lean` (module docstring in the
      house style: Main Results, paper anchors, why the notions are frame-predicate-restricted)
- [x] Define `ValidDetIn fc φ := ValidOnFrames (fun F => FrameClass.Sat fc F ∧ F.Deterministic) φ`
      and its `PlusFormula` twin over `PlusValidOnFrames` *(deviation: altered — the conjunction is named `DetSat fc` and the two notions are `ValidDetIn`/`PlusValidDetIn` at it, so consumers never unfold the pair)*
- [x] Define `DeterminedValid F := ∀ φ : PlusFormula, F.PlusValidOn (φ.imp φ.stab)`
- [x] Prove `deterministic_determinedValid : F.Deterministic → DeterminedValid F` from 536's
      `determined_of_deterministic` (do not re-derive the collapse)
- [x] Prove the inclusion is strict, citing `Metalogic/Independence/DriftFrame.lean`'s `F0`:
      `fzero_determined` gives `DeterminedValid F0` and `fzero_not_deterministic` the failure
- [x] Record monotonicity lemmas transporting `PlusValidIn`/`ValidIn` down to the restricted
      notions via `PlusValidOnFrames.mono` / `ValidOnFrames`
- [x] Register the module in the `FormalSystem/Metalogic.lean` aggregator *(deviation: altered — registered through a new subtree aggregator `FormalSystem/Metalogic/Deterministic.lean`, matching every other `Metalogic/` subdirectory)*

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Validity.lean` - new
- `FormalSystem/Metalogic.lean` - aggregator entry

**Verification**:
- `lake build FormalSystem.Metalogic.Deterministic.Validity` clean
- The strictness lemma compiles without any new frame construction

---

### Phase 2: Determinism of the engines' countermodel frames [COMPLETED]

**Goal**: Establish that every completeness engine's countermodel frame is deterministic and
widen the four countermodel producers to expose that fact, so the engines can be re-read with a
narrowed validity hypothesis.

**Tasks**:
- [x] Prove `multiFamTaskFrameGen_deterministic` from the existing `flowRel_fib_subsingleton`
      (`Metalogic/Algebraic/FlowFrame.lean`); note in the docstring that `bundleFlowFrame` and
      `WeakCanonical/IntegerModel`'s `multiFamTaskFrame` are definitional specializations and
      inherit it *(deviation: altered — the lemma is hosted in `Algebraic/FlowFrame.lean` beside the frame, not in a new `Deterministic/Frames.lean`, because the four countermodel producers that consume it sit BELOW `Metalogic/Deterministic/` in the import order; `bundleFlowFrame_deterministic` and `multiFamTaskFrame_deterministic` are the two named specializations)*
- [x] Prove `zTaskFrameV2_deterministic` from the existing `zTaskFrameV2_fib_subsingleton` *(deviation: altered — hosted in `ReynoldsBridge.lean` beside the frame, same reason)*
- [x] Widen `countermodel_dense_enriched` (`BXCanonical/Completeness.lean`) with an extra
      existential binder `F.toTaskFrame.Deterministic`, supplying the witness
- [x] Widen `countermodel_discrete` (`WeakCanonical/GroupModel/CountermodelBase.lean`) likewise
- [x] Widen `countermodel_discrete_reynolds_v2` (`WeakCanonical/IntegerModel/ReynoldsBridge.lean`)
      likewise
- [x] Widen `countermodel_dedekind_dense` (`BXCanonical/CompletenessDedekind.lean`) likewise
- [x] Update every destructuring call site to bind the new component and discard it where unused
      (`completeness`, `derivable_of_validDense`, `derivable_of_validZTime`,
      `completeness_rtime_engine`, `BXCanonical/DiscreteCarrierProbe.lean`) *(deviation: altered — the confirmed count is FOUR call sites, all in `BXCanonical/{Completeness,CompletenessDedekind}.lean`; `DiscreteCarrierProbe.lean` mentions `countermodel_discrete` only in prose and needed no edit)*
- [x] Confirm no axiom-set drift: `#print axioms` for the four engines unchanged

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: four countermodel producers and five destructuring call sites are asserted
here. Confirm at implementation time by grepping for each producer name across
`FormalSystem/` before editing, and reconcile the actual count in the phase notes; the
atomic-batch declaration covers exactly the producer files plus the confirmed call-site files.

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Frames.lean` - new; the two determinism lemmas
- `FormalSystem/Metalogic/BXCanonical/Completeness.lean` - widened producer + two call sites
- `FormalSystem/Metalogic/BXCanonical/CompletenessDedekind.lean` - widened producer + call site
- `FormalSystem/Metalogic/WeakCanonical/GroupModel/CountermodelBase.lean` - widened producer
- `FormalSystem/Metalogic/WeakCanonical/IntegerModel/ReynoldsBridge.lean` - widened producer
- `FormalSystem/Metalogic/BXCanonical/DiscreteCarrierProbe.lean` - call site, if affected

**Verification**:
- `lake build` clean across the whole tree (the producers are shared)
- `#print axioms` for `completeness`, `derivable_of_validDense`, `derivable_of_validZTime`,
  `completeness_rtime_engine` still reports exactly `[propext, Classical.choice, Quot.sound]`

---

### Phase 3: Deterministic-hypothesis completeness engines [COMPLETED]

**Goal**: State and prove the four engines with the validity hypothesis narrowed to the
deterministic frames of the class.

**Tasks**:
- [x] `derivable_of_validDetBase : ValidOnFrames TaskFrame.Deterministic φ → Derivable FrameClass.Base [] φ`
- [x] `derivable_of_validDetDense`, `derivable_of_validDetZTime`, `derivable_of_validDetRTime`
      against the corresponding `ValidDetIn` notion from Phase 1
- [x] Each proof re-runs the corresponding engine's script, applying the narrowed hypothesis to
      the countermodel frame with the determinism component from Phase 2 *(deviation: altered — the `.ZTime` dense-branch derivation was first extracted from `derivable_of_validZTime` as the named `BXCanonical.ztimeNextTop`, so the two engines cite one derivation instead of duplicating ten steps)*
- [x] Docstring on each: what the narrowing does and does not say — it is a statement about the
      engines' own countermodels, not a new completeness theorem

**Timing**: 1 hour

**Depends on**: 1, 2

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Engines.lean` - new

**Verification**:
- All four compile sorry-free; `#print axioms` matches the parent engines

---

### Phase 4: Erasure and the semantic collapse [COMPLETED]

**Goal**: Define the ⊡-erasure and prove that on deterministic frames a `PlusFormula` and its
erasure are pointwise equivalent, hence that deterministic L⁺-validity reduces to deterministic
L-validity.

**Tasks**:
- [x] Define `erasePlus : PlusFormula → Formula` deleting every `stab` (`erasePlus (.stab φ) = erasePlus φ`)
- [x] Prove `plusTruthAt_erasePlus_of_deterministic`: on a deterministic frame, at every total
      history and time, `PlusTruthAt M τ t φ ↔ TruthAt M τ t (erasePlus φ)`, by induction on `φ`
      with the `stab` case discharged by 536's `stab_iff_of_deterministic`
- [x] Prove the validity-level corollary: deterministic L⁺-validity of `φ` gives deterministic
      L-validity of `erasePlus φ`, at each class
- [x] Record in the docstring that the induction's `box` and `untl`/`snce` cases quantify over
      total histories and times, which is why the pointwise lemma is stated at total histories

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Erasure.lean` - new

**Verification**:
- Induction closes on all seven `PlusFormula` constructors sorry-free
- `#print axioms` reports no new axiom beyond the ambient three

---

### Phase 5: TM to TM⁺ substitution transfer [COMPLETED]

**Goal**: Land the reusable lever that carries every TM theorem *schema* into TM⁺ at arbitrary
`PlusFormula` arguments, so congruence and propositional reasoning need not be rebuilt over
`PlusFormula`.

**Tasks**:
- [x] Define `substPlus : (Atom → PlusFormula) → Formula → PlusFormula`, structurally, with the
      same right-hand sides as `ofFormula` so it pushes through every derived operator by `rfl`
- [x] Prove the swap interaction `substPlus σ φ.swapTemporal = (substPlus (fun p => (σ p).swapTemporal) φ).swapTemporal`
- [x] Extend `PlusAxiom.ofTM`'s constructor map to `PlusAxiom.ofTMSubst : Axiom φ → PlusAxiom (substPlus σ φ)`
- [x] Prove `plusDerivable_substPlus : Derivable fc [] φ → PlusDerivable fc [] (substPlus σ φ)` by
      recursion on the derivation, with the `temporal_duality` case routed through the swap
      interaction at `swapTemporal ∘ σ` and closed by `swap_temporal_involution`
- [ ] Audit `Theorems/` for the congruence schemata Phase 8 needs — propositional `iff`
      congruence at `imp`, `box` congruence, `untl`/`snce` congruence from `untilMonoGuard`,
      `untilMonoEvent` and their past mirrors — and add on the TM side any that are missing *(deviation: deferred to Phase 8, where the induction's goals name the schemata it actually demands; the plan's own Scope Hypothesis for Phase 8 prescribes exactly that ordering)*
- [x] Register the module in `FormalSystem/PlusLanguage.lean`; keep the directional invariant
      (nothing under `PlusLanguage/` imports `Semantics/`)

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: the constructor map is asserted to cover the same 45 `Axiom` constructors
`PlusAxiom.ofTM` already covers, and the congruence audit is asserted to find at most four
missing TM-side schemata. Confirm both at implementation time by counting the constructors in
`ProofSystem/Axioms.lean` and by listing the congruence lemmas actually needed by Phase 8's
induction before writing them; record the confirmed counts in the phase notes.

**Files to modify**:
- `FormalSystem/PlusLanguage/Substitution.lean` - new
- `FormalSystem/PlusLanguage.lean` - aggregator entry
- `FormalSystem/Theorems/` - any missing TM-side congruence schemata

**Verification**:
- `plusDerivable_substPlus` compiles sorry-free, including the `temporal_duality` case
- A smoke check: a propositional TM theorem transfers to a `PlusFormula` instance containing `stab`

---

### Phase 6: The extended proof system TM⁺ + Determined [COMPLETED]

**Goal**: Define the extended system as a separate inductive that stays entirely out of the live
proof system, with the embedding of TM⁺ derivations into it.

**Tasks**:
- [x] Define `DetAxiom` with an `ofPlus` arm over `PlusAxiom` and a `determined` arm at
      `φ.imp φ.stab`, plus `DetAxiom.minFrameClass` extending `PlusAxiom.minFrameClass` with
      `determined ↦ .Base`
- [x] Define `DetDerivationTree` mirroring `PlusDerivationTree`'s seven constructors over
      `DetAxiom`, with `height`, `lift`, `ofWeakeningNil` and the two modus-ponens height lemmas
- [x] Define `DetDerivable fc Γ φ := Nonempty (DetDerivationTree fc Γ φ)` matching
      `PlusDerivable`'s shape
- [x] Define the embedding `DetDerivationTree.ofPlus : PlusDerivationTree fc Γ φ → DetDerivationTree fc Γ φ`
      and the derived ⊡-necessitation rule, mirroring `stabNecessitation` *(deviation: altered — `DetDerivationTree.ofTM` and `.ofTMSubst` were added alongside, so Phase 8 reaches the substitution transfer through one composition rather than re-composing at each use)*
- [x] Docstring: why *Determined* cannot be a `PlusAxiom` constructor (`refute_determined`,
      `Semantics/PlusNonValidities.lean`) and why it cannot live in the context (necessitation,
      temporal necessitation and temporal duality are all empty-context rules)

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/System.lean` - new
- `FormalSystem/Metalogic.lean` - aggregator entry

**Verification**:
- The module compiles sorry-free; the termination arguments for `height`-recursive definitions go
  through with the same pattern as `PlusDerivationTree`
- `grep` confirms no new constructor was added to `PlusAxiom`

---

### Phase 7: Soundness of TM⁺ + Determined [COMPLETED]

**Goal**: Prove the extended system sound over the frames validating every instance of
*Determined* — the class strictly containing the deterministic frames — which is the half of the
coincidence corollary the manuscript needs.

**Tasks**:
- [x] Mirror `plus_derivable_valid_and_swap_validIn`'s companion recursion for
      `DetDerivationTree`, carrying validity and swap-validity over the `DeterminedValid`-restricted
      frame predicate
- [x] Axiom arm `ofPlus`: transport `plusAxiom_validIn` / `plusAxiom_swap_validIn` down the frame
      predicate by monotonicity
- [x] Axiom arm `determined`: direct from `DeterminedValid`; for the swap arm, use that
      `swapTemporal` fixes `stab`, so the dual of a *Determined* instance is again one
- [x] State `detSoundness` at the restricted class, plus the specialization to the deterministic
      frames via Phase 1's inclusion lemma
- [x] Corollary: the extended system is consistent (no derivation of `⊥`), mirroring
      `plus_not_derivable_nil_bot`

**Timing**: 2 hours

**Depends on**: 1, 6

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Soundness.lean` - new

**Verification**:
- The companion recursion closes on all seven rule arms and both axiom arms, sorry-free
- The consistency corollary compiles

---

### Phase 8: The syntactic collapse in TM⁺ + Determined [COMPLETED]

**Goal**: Prove that the extended system derives the equivalence of every `PlusFormula` with its
erasure — the step that converts a TM derivation of the erasure into a derivation of the original.

**Tasks**:
- [x] Prove ⊡-congruence in the extended system: from a derivation of `φ ↔ ψ`, derive
      `⊡φ ↔ ⊡ψ`, using the derived ⊡-necessitation rule and `stab_k`
- [x] Import the `imp`, `box`, `untl` and `snce` congruence schemata at `PlusFormula` arguments
      through Phase 5's substitution transfer, then through Phase 6's `ofPlus` embedding *(deviation: altered — only the PROPOSITIONAL glue needed the substitution transfer: `box`, `untl` and `snce` congruence are built directly from `PlusAxiom.modal_k_dist`, `.left_mono_until_G`, `.right_mono_until`, `.left_mono_since_H`, `.right_mono_since`, which are already stated at arbitrary `PlusFormula` arguments)*
- [x] Prove `detDerivable_iff_erasePlus : DetDerivable fc [] (φ.iff (ofFormula (erasePlus φ)))`
      by induction on `φ`, the `stab` case using `determined` and `stab_t` for the two directions
- [x] Derive the transport lemma: a TM derivation of `erasePlus φ` yields a `DetDerivable`
      derivation of `φ`, via `PlusAxiom.ofTM`, `ofPlus`, and the equivalence

**Timing**: 2 hours

**Depends on**: 5, 6

**Verification Tier**: local

**Scope Hypothesis** (reconciled at implementation time: confirmed — four congruence rules plus
`detStabIff` closed all seven constructors, with SIX imported propositional theorems as the glue
(`identity`, `bCombinator`, `theoremFlip`, `biImp`, `lceImp`, `rceImp`) and no new TM-side
schema needed): this phase asserts that four congruence schemata plus ⊡-congruence suffice
for the induction. Confirm by attempting the induction skeleton first with all cases `sorry`-free
except the congruence appeals, listing exactly which schemata the goals demand, and only then
discharging them; if a fifth is needed, add it on the TM side and note the deviation.

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Collapse.lean` - new

**Verification**:
- The induction closes on all seven constructors sorry-free
- The transport lemma compiles at all four class tags

---

### Phase 9: Deterministic completeness and the coincidence corollary [COMPLETED]

**Goal**: Land the headline theorems and the manuscript-facing corollary.

**Tasks**:
- [x] `detCompletenessBase`, `detCompletenessDense`, `detCompletenessZTime`,
      `detCompletenessRTime`: deterministic L⁺-validity gives extended-system derivability, by
      composing Phase 4's semantic collapse, Phase 3's narrowed engine and Phase 8's transport
- [x] `logicDeterministicEqDeterminedValid`: at each class, validity over the deterministic frames
      and validity over the Determined-valid frames coincide — `⇐` by the inclusion, `⇒` by
      completeness then Phase 7's soundness
- [x] Corollary that the result transfers to every frame class between the deterministic frames
      and the Determined-valid frames
- [x] Docstrings: state the theorem as completeness over `TaskFrame.Deterministic`; cite
      `deterministic_not_plusDefinable` for why *Determined* axiomatizes without defining; state
      explicitly that this is the ⊡ = identity special case that any nondeterministic result must
      specialize to
- [x] Add the `#print axioms` audit block in the house style

**Timing**: 1.5 hours

**Depends on**: 3, 4, 7, 8

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Deterministic/Completeness.lean` - new
- `FormalSystem/Metalogic.lean` - aggregator entry

**Verification**:
- `lake build` clean; all headline theorems sorry-free
- `bash scripts/check-module-invariants.sh` C2/C3 green
- No declaration anywhere states general TM⁺ completeness

---

### Phase 10: Non-definability of the stability modal [COMPLETED]

**Goal**: Land `stabNotDefinable` — no `Formula` is equivalent to `⊡Fp` over all task models —
by transcribing 535 §6.2's two models and relating them with the tree's own `TruthCorr`.

**Tasks**:
- [x] Build `M₁`: the permissive two-state frame (the `natFrame` shape) over ℤ with the atom true
      at exactly one state *(deviation: altered — `NF`/`natHist`/`natModel` already exist in `Semantics/PlusNonValidities.lean` and are reused verbatim, so no frame was built)*
- [x] Build `M₂`: the three-state frame of 535 §6.2, discharging the six `FrameOver` fields with
      the same idiom `Metalogic/Independence/DriftFrame.lean` uses *(deviation: altered — `M₂` is `multiFamTaskFrameGen` at family index `ℤ → ℕ`, whose six `FrameOver` fields are already discharged; no new frame was constructed, and the uniqueness-of-history property is 536's `stab_iff_of_deterministic` at `multiFamTaskFrameGen_deterministic` rather than a hand-checked three-state case analysis. The separation is the same one 535 §6.2 describes: same atom profiles, different state-sharing at time 0.)*
- [x] Build the `TruthCorr` between them: `Rel σ σ'` iff the two histories agree on every atom at
      every time; atom harmony by definition; `total_fwd`/`total_bwd` because both models realize
      exactly the same atom profiles; `dur := .refl`
- [x] Evaluate `⊡Fp` at `(const u, 0)`: true in `M₂` (unique history through `u`), false in `M₁`
      (the history that leaves `u` after time 0); confirm `□Fp` false in both
- [x] Conclude `stabNotDefinable` via `truthAt_of_truthCorr`, mirroring
      `deterministic_not_plusDefinable`'s elimination-by-indistinguishability shape
- [x] Docstring: the invariance notion is the tree's own `TruthCorr`; no new bisimulation
      machinery is introduced, and the separation is temporal (atomic separators are ruled out by
      the AS axiom)

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/Metalogic/Independence/StabUndefinable.lean` - new
- `FormalSystem/Metalogic/Independence/README.md` - inventory row
- `FormalSystem/Metalogic.lean` or the Independence aggregator - entry

**Verification**:
- Both frames discharge all six axioms sorry-free
- `stabNotDefinable` compiles; `#print axioms` audited

---

### Phase 11: Coarsened-state models and the naive-derivability predicate [COMPLETED]

**Goal**: Build the semantics and the syntactic restriction that the underivability argument
needs, and gate the next phase on an explicit feasibility check.

**Tasks**:
- [x] Define `NaiveDerivable` as a predicate on the *existing* derivation trees: a recursive
      `PlusDerivationTree.NaiveOnly` requiring every `axiom` node's `PlusAxiom` to be outside
      `{paste, untl_paste}`, and `NaiveDerivable fc Γ φ := ∃ d, d.NaiveOnly`. This keeps the naive
      system out of the live proof system entirely — no second axiom inductive is introduced
- [x] Define the coarsened-state truth relation: given a frame `F` and a map `π` on world states,
      a truth recursion identical to `PlusTruthAt` except that the `stab` clause quantifies over
      total histories agreeing with the current one under `π ∘ σ` at the evaluation time
- [x] Prove the state-determinacy lemma: the coarsened `⊡` is a state formula (its value at
      `(τ,t)` depends only on `τ(t)`), the coarsened analogue of 535's probe E2, using the same
      time-shift argument
- [x] Mirror `Conservativity/Plus/Atomization.lean` for the coarsened semantics, obtaining that
      every TM⁺ schema instance is valid in every coarsened-state model
- [x] Prove the six naive ⊡-axioms valid in every coarsened-state model whose valuation is
      `π`-invariant: SK from the quantifier shape, ST from reflexivity, S4/S5 because `π`-agreement
      is an equivalence, MS because the class is contained in all histories, AS from
      `π`-invariance of the valuation
- [x] **Gate**: before Phase 12 starts, confirm the atomization step actually closes *(gate PASSED: `cTruthAt_iff_atomize` compiles, and with it `cValid_of_tm` / `cValid_swap_of_tm`; the coarsened `⊡` is a state formula by `c_stab_state_only`, exactly as the standard one is, so `Atomization.lean`'s route transfers unchanged)*

**Timing**: 2 hours

**Depends on**: 9

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/Metalogic/Independence/NaiveSystem.lean` - new; the naive predicate
- `FormalSystem/Metalogic/Independence/CoarsenedModels.lean` - new; the semantics and soundness

**Verification**:
- The state-determinacy lemma and the atomization mirror compile sorry-free
- All six naive axioms are validated; `paste` and `untl_paste` are *not* claimed

---

### Phase 12: Underivability of the pasting axioms [COMPLETED]

**Goal**: Machine-check that PS and US are not derivable from the naive set plus TM⁺.

**Tasks**:
- [x] Build the concrete coarsened-state model *(deviation: altered — the frame is `multiFamTaskFrameGen (TemporalOrder.of ℤ) Unit`, the deterministic clock over ℤ, so no `FrameOver` obligation had to be discharged; the coarsening is `π ((), x) = |x|`, whose class at time 0 contains exactly the flow lines of offsets `-1` and `+1`)*
- [x] Refute PS in it: both `⟐`-conjuncts hold at the evaluation point while the pasted
      conjunction fails, precisely because the two witnesses sit at different states of the same
      coarsening class and so cannot be pasted
- [x] Refute US in it by the same construction at a future evaluation time *(the instance is `α⁻ := ⊤`, `φ⁺ := Fp`; the antecedent is witnessed at time 2 by the flow line of offset `-3`)*
- [x] Prove naive soundness over coarsened-state models by induction on `NaiveOnly` derivations,
      then conclude `pasteNotNaiveDerivable` and `untlPasteNotNaiveDerivable`
- [x] Docstring: this records the non-redundancy of the axiom set; the pasting axioms remain valid
      on every task frame (`Semantics/PlusPasting.lean`), so nothing here weakens TM⁺
- [x] If the argument does not close, mark the phase `[COMPLETED WITH EXCLUSIONS]` with a
      `#### Reasoned Exclusions` record naming the obstruction and its evidence — never a `sorry`

**Timing**: 2 hours

**Depends on**: 11

**Verification Tier**: local

**Files to modify**:
- `FormalSystem/Metalogic/Independence/PastingIndependence.lean` - new
- `FormalSystem/Metalogic/Independence/README.md` - inventory rows

**Verification**:
- Both underivability theorems compile sorry-free, or the exclusions record is present and
  complete
- The live `PlusAxiom` is unchanged

---

### Phase 13: Conservativity corollaries and the defined modals [COMPLETED]

**Goal**: Land the corollaries that the stability modal permits beyond task 533's result.

**Tasks**:
- [x] Composed rows: TM⁺ over TMFrag and over TM⁻ at each class *(deviation: altered — `plus_of_tmMinus_{base,dense,ztime,rtime}` and `plusDerivable_ofFormula_iff_*` are ALREADY named per class in `Forward.lean`; only `tmFrag_iff_plus` was left generic over the engine, so the four named instances `tmFragIffPlus{Base,Dense,ZTime,RTime}` are the composed rows this phase actually adds)*
- [x] Derived theorems for the defined modals, via Phase 5's substitution transfer: `⊡Gφ → Gφ`,
      `□Gφ → ⊡Gφ`, `⊡Gφ → ⊡Fφ`, and the pure-future row from the pasting axiom *(deviation: altered — the fourth row is FS, `F⟐φ⁺ → ⟐Fφ⁺` (`someFutureCouldImpCouldSomeFuture`), which is `untl_paste` at guard `⊤` and is therefore a one-line axiom instance; GS (`⊡Gφ⁺ → G⊡φ⁺`) needs contraposition infrastructure over `PlusFormula` that this phase's budget did not cover, and is cited semantically as `Semantics.stab_allFuture_plusValid` instead)*
- [x] Record the refuted directions by citation, not by restatement:
      `Semantics/PlusNonValidities.lean` already carries them
- [x] The deterministic-completeness transfer back to the L level *(deviation: altered — it DOES add something: `detDerivable_ofFormula_iff` says TM⁺ + *Determined* is conservative over TM, which does not follow from TM⁺'s conservativity because the extended system has an axiom TM⁺ lacks)*

**Timing**: 1.5 hours

**Depends on**: 9

**Verification Tier**: local

**Scope Hypothesis** (reconciled: four defined-modal theorems delivered, with FS substituted for GS as noted; ONE composed row family (the four `tmFragIffPlus*`) was genuinely missing rather than three, the rest being already named in `Forward.lean`): this phase asserts four defined-modal theorems and three composed rows.
Confirm at implementation time against 535 §7.1-7.2's list, and record any item that turns out to
be already landed rather than restating it.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Plus/Corollaries.lean` - new
- `FormalSystem/Metalogic/Conservativity/Plus.lean` - aggregator entry

**Verification**:
- Every corollary compiles sorry-free
- No corollary restates a fact already carried elsewhere in the tree

---

### Phase 14: Documentation and invariants [NOT STARTED]

**Goal**: Record what landed and what remains open, and bring the invariant checks green.

**Tasks**:
- [ ] Update `FormalSystem/Metalogic/Conservativity/Plus/README.md`: the deterministic-completeness
      row, the non-definability row, the pasting-independence row, and general completeness listed
      as **open**
- [ ] Update `FormalSystem/Metalogic/README.md`'s metatheory rows with the same, plus the new
      `Deterministic/` subtree in the directory inventory
- [ ] Update `FormalSystem/Metalogic/Independence/README.md` with the two new modules
- [ ] Add `docs/theorem-index.md` rows for every new headline declaration, with the axiom column
      generated from the baselines, not typed
- [ ] Cite Reynolds 2003 and Zanardo 1991 as the nearest literature results for the open general
      case; no task numbers anywhere under `FormalSystem/` or `docs/`
- [ ] Run `bash scripts/check-module-invariants.sh` and bring C2, C3 and C14 green

**Timing**: 1.5 hours

**Depends on**: 10, 12, 13

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Plus/README.md`
- `FormalSystem/Metalogic/README.md`
- `FormalSystem/Metalogic/Independence/README.md`
- `docs/theorem-index.md`

**Verification**:
- `bash scripts/check-module-invariants.sh` reports C2, C3 and C14 pass
- `grep -rn "task [0-9]" FormalSystem/ docs/` finds nothing new

---

### Phase 15: Compactness of TM⁺ at Base and Dense (optional) [NOT STARTED]

**Goal**: Deliverable (5), attempted only if budget remains: extend the ultraproduct Łoś lemma
with a `stab` case.

**Tasks**:
- [ ] Add the `stab` case to `los_truthAt`, treating ultraproduct histories as orbit
      representatives
- [ ] Show `SameStateAt` is eventually-agreeing via `omk_eq_omk`
- [ ] Derive compactness of TM⁺ at Base and Dense from the extended lemma
- [ ] If budget is exhausted, close this phase as `[COMPLETED WITH EXCLUSIONS]` with a
      `#### Reasoned Exclusions` record; that is the expected outcome, not a failure

**Timing**: 2 hours

**Depends on**: 14

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Compactness.lean` - the `stab` case, if attempted

**Verification**:
- `lake build` clean and the compactness statements sorry-free, or the exclusions record present

## Lean Challenge Statements

```lean
import FormalSystem.Metalogic.Conservativity.Plus.PlusSoundness
import FormalSystem.Semantics.PlusDeterminism
import FormalSystem.Metalogic.Independence.DriftFrame

namespace FormalSystem.Metalogic.Deterministic

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.PlusLanguage
open FormalSystem.Semantics

/-- Frames validating every instance of the *Determined* schema. -/
def DeterminedValid (F : TaskFrame) : Prop :=
  ∀ φ : PlusFormula, F.PlusValidOn (φ.imp φ.stab)

/-- Deletion of every `stab` occurrence. -/
def erasePlus : PlusFormula → Formula := sorry

/-- Derivability in TM⁺ + *Determined*. -/
def DetDerivable (fc : FrameClass) (Γ : PlusContext) (φ : PlusFormula) : Prop := sorry

/-- Derivability in TM⁺ with the two pasting axioms withheld. -/
def NaiveDerivable (fc : FrameClass) (Γ : PlusContext) (φ : PlusFormula) : Prop := sorry

theorem derivable_of_validDetBase (φ : Formula)
    (h : ValidOnFrames TaskFrame.Deterministic φ) :
    Derivable FrameClass.Base [] φ := sorry

theorem derivable_of_validDetDense (φ : Formula)
    (h : ValidOnFrames (fun F => FrameClass.Sat FrameClass.Dense F ∧ F.Deterministic) φ) :
    Derivable FrameClass.Dense [] φ := sorry

theorem derivable_of_validDetZTime (φ : Formula)
    (h : ValidOnFrames (fun F => FrameClass.Sat FrameClass.ZTime F ∧ F.Deterministic) φ) :
    Derivable FrameClass.ZTime [] φ := sorry

theorem derivable_of_validDetRTime (φ : Formula)
    (h : ValidOnFrames (fun F => FrameClass.Sat FrameClass.RTime F ∧ F.Deterministic) φ) :
    Derivable FrameClass.RTime [] φ := sorry

theorem detSoundness {fc : FrameClass} {φ : PlusFormula} (h : DetDerivable fc [] φ) :
    PlusValidOnFrames (fun F => FrameClass.Sat fc F ∧ DeterminedValid F) φ := sorry

theorem detCompletenessBase (φ : PlusFormula)
    (h : PlusValidOnFrames TaskFrame.Deterministic φ) :
    DetDerivable FrameClass.Base [] φ := sorry

theorem detCompletenessDense (φ : PlusFormula)
    (h : PlusValidOnFrames (fun F => FrameClass.Sat FrameClass.Dense F ∧ F.Deterministic) φ) :
    DetDerivable FrameClass.Dense [] φ := sorry

theorem detCompletenessZTime (φ : PlusFormula)
    (h : PlusValidOnFrames (fun F => FrameClass.Sat FrameClass.ZTime F ∧ F.Deterministic) φ) :
    DetDerivable FrameClass.ZTime [] φ := sorry

theorem detCompletenessRTime (φ : PlusFormula)
    (h : PlusValidOnFrames (fun F => FrameClass.Sat FrameClass.RTime F ∧ F.Deterministic) φ) :
    DetDerivable FrameClass.RTime [] φ := sorry

theorem logicDeterministicEqDeterminedValid (fc : FrameClass) (φ : PlusFormula) :
    PlusValidOnFrames (fun F => FrameClass.Sat fc F ∧ F.Deterministic) φ ↔
      PlusValidOnFrames (fun F => FrameClass.Sat fc F ∧ DeterminedValid F) φ := sorry

theorem stabNotDefinable (p : Atom) :
    ¬ ∃ ψ : Formula, ∀ (F : TaskFrame) (M : TaskModel F) (τ : ConvexHistory F),
      τ.IsTotal → ∀ t,
        (PlusTruthAt M τ t (PlusFormula.stab (PlusFormula.someFuture (PlusFormula.atom p))) ↔
          TruthAt M τ t ψ) := sorry

theorem pasteNotNaiveDerivable :
    ∃ φ ψ : PlusFormula, IsPureFuture φ ∧ IsPurePast ψ ∧
      ¬ NaiveDerivable FrameClass.Base []
        ((PlusFormula.dstab φ).imp
          ((PlusFormula.dstab ψ).imp (PlusFormula.dstab (φ.and ψ)))) := sorry

theorem untlPasteNotNaiveDerivable :
    ∃ α φ : PlusFormula, IsPurePast α ∧ IsPureFuture φ ∧
      ¬ NaiveDerivable FrameClass.Base []
        ((PlusFormula.untl α (PlusFormula.dstab φ)).imp
          (PlusFormula.dstab (PlusFormula.untl α φ))) := sorry

end FormalSystem.Metalogic.Deterministic
```

## Testing & Validation

- [ ] `lake build` clean at the end of every phase; no `sorry` anywhere under `FormalSystem/`
- [ ] `bash scripts/check-module-invariants.sh` reports C2, C3 and C14 pass after Phase 14
- [ ] `#print axioms` for every new headline declaration reports exactly
      `[propext, Classical.choice, Quot.sound]` or less; the 536 imports remain choice-free
- [ ] The four pre-existing engines' axiom sets are unchanged after Phase 2's widening
- [ ] No declaration states general (nondeterministic) TM⁺ completeness, at any class
- [ ] No declaration or docstring describes the *Determined* schema as defining or characterizing
      the deterministic frames
- [ ] The live `PlusAxiom` inductive has the same constructors it had before this task
- [ ] `grep -rn "task [0-9]" FormalSystem/ docs/` finds no new occurrence

## Artifacts & Outputs

- `FormalSystem/Metalogic/Deterministic/{Validity,Frames,Engines,Erasure,System,Soundness,Collapse,Completeness}.lean`
- `FormalSystem/PlusLanguage/Substitution.lean`
- `FormalSystem/Metalogic/Independence/{StabUndefinable,NaiveSystem,CoarsenedModels,PastingIndependence}.lean`
- `FormalSystem/Metalogic/Conservativity/Plus/Corollaries.lean`
- Widened countermodel producers in `BXCanonical/Completeness.lean`,
  `BXCanonical/CompletenessDedekind.lean`, `WeakCanonical/GroupModel/CountermodelBase.lean`,
  `WeakCanonical/IntegerModel/ReynoldsBridge.lean`
- Documentation updates in three READMEs and `docs/theorem-index.md`
- `specs/537_tm_star_completeness_stab_nondefinability/summaries/01_tm-plus-deterministic-completeness-summary.md`

## Rollback/Contingency

Every phase is a self-contained module addition except Phase 2, which is the only edit to shared
engine files. Phases 1, 3-15 are reverted by deleting the new module and its aggregator entry.
Phase 2 is reverted by dropping the extra existential binder from the four producers and the
matching binder from each call site; because the change is additive and typed, a partial revert
fails the build rather than passing silently.

If Phase 12 cannot close, the phase is marked `[COMPLETED WITH EXCLUSIONS]` and the task still
delivers (1), (2) and (4) in full. If Phase 8's collapse cannot close after both the substitution
route and the deduction-theorem fallback, deliver Phases 1-7 — deterministic-class soundness plus
the semantic collapse plus the narrowed engines — and record the residual gap explicitly in the
Conservativity/Plus README, exactly as the task specification instructs; do not state the
completeness half and discharge it with `sorry`.
