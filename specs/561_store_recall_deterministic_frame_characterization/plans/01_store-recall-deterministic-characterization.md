# Implementation Plan: Task #561 — the characterization theorem for the deterministic task frames

- **Task**: 561 - Store/recall and the characterization theorem for the deterministic task frames
- **Status**: [COMPLETED]
- **Effort**: 21 hours (core, Phases 1-14) plus 2 hours optional (Phase 15)
- **Dependencies**: None. Independent of 537 (deterministic completeness) and of 559/560
  (nondeterministic completeness); must not wait on them.
- **Research Inputs**: None for this round. Ground truth read directly at plan time:
  `specs/archive/536_stability_deterministic_collapse_store_recall/reports/02_correspondence-record-and-store-recall-recommendation.md`
  (Parts I and II, incl. the transport-layer breakage table II.3 and the choice asymmetry II.4);
  `/home/benjamin/Philosophy/Papers/PossibleWorlds/specs/105_characterize_deterministic_task_frames/reports/02_determinism-axiom-correspondence.md`
  (§2 bridge lemma, §3.3 `F^N`, §4 Theorem C); manuscript labels `def:BLstar-semantics`,
  `lem:deterministic-singleton`, `app:deterministic`, `app:drift`, `cor:no-characterization`,
  `sent:det`, `app:deterministic-future` (read-only, by `\label` never by line number).
- **Artifacts**: plans/01_store-recall-deterministic-characterization.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Build `StarLanguage/` — the repository's genuine **L⋆ = L⁺ + time store/recall** — and use it to
land the manuscript's characterization theorem for the deterministic task frames: the part of the
deterministic-frame appendix that task 536 could not reach because it needs operators
`PlusFormula` does not have. The plan opens the ZFC half of `lem:deterministic-singleton`
(deliverable 1), then builds the new formula type and its semantics over points `(τ, x, v⃗)`
(deliverables 2), then lands `app:deterministic-future` in both halves (3), the live-text
discrimination footnote (4), Theorem C's `Det-pm` half (5), and the forward-determinism separation
via `F^N` (6). Deliverable (7), a world-register `Det-m`, is optional and last.

Definition of done: Phases 1-14 landed with `lake build` green, no new `sorry`, every headline
declaration listed under **Goals** present with the statement pinned in `## Lean Challenge
Statements`, and `bash scripts/check-module-invariants.sh` reporting C2/C3/C14 pass (with C15,
C24 and C26 also green, since the plan adds new modules, new anchors and new `def` names).

### Research Integration

No research report was produced for this round, and none was needed: the dispatch description is
a specification (the defect, the deliverable order, the ground truth, and the acceptance bar are
all named), and every remaining question was resolved by targeted reads of the tree at plan time.
Those reads changed the plan in five places, each recorded here so the implementer does not
re-derive them:

1. **`⇒_0` is the identity for free.** `FrameOver.nullity_identity` is a *structure field*
   (`∀ w u, TaskRel w 0 u ↔ w = u`, `Semantics/TaskFrame.lean`), strictly stronger than the
   paper's derived `lem:nullity`. The paper's Step 1 for the (⇐) bridge — deriving injectivity at
   `0` from *Limit* plus `lem:nullity` — is therefore **not needed** in Lean. Record the deviation
   at the site; do not transcribe the paper's Step 1.
2. **The bridge is stated pointwise on states, not as history equality.** `states_eq_of_deterministic`
   (`Semantics/PlusDeterminism.lean`) already concludes pointwise state agreement, and the (⇐)
   direction only needs pointwise agreement as its *hypothesis*. Taking the pointwise form on both
   sides gives a strictly stronger biconditional than the history-equality form and avoids needing
   history extensionality at a general frame.
3. **The refuting frame for `app:deterministic-future`'s negative half is the tree's existing
   `NF`.** The paper says the negative half reuses "the same non-deterministic task frame `F'` and
   countermodel presented in `app:deterministic`"; in this tree that countermodel is
   `NF = FrameOver.natFrame (D := ℤ)` with `natHist`, `natModel` and the pair
   `τ = const 0` / `σ = fun s => if s ≤ 0 then 0 else 1` used by `refute_determined`
   (`Semantics/PlusNonValidities.lean`). `natModel`'s valuation is `n = 0`, so `|p| = {0}` and
   `τ(1) = 0 ∈ |p|`, `σ(1) = 1 ∉ |p|`, `τ(0) = σ(0) = 0` — the paper's `w₀`/`w₁` shape exactly.
   Reusing it is the fidelity-preserving choice, not a shortcut; building a second two-state
   frame `F'` from scratch would duplicate it.
4. **The finite-fibres *Saturation* helper that 536 flagged as possibly nonexistent is
   constructible.** `TaskFrame.sInter_nonempty_of_directed_of_minimal` (`Semantics/TaskFrame.lean`)
   is exactly the constructive core: a directed family with a `⊆`-minimal member has nonempty
   intersection. Finite fibres give finite members (segments are `Fib ∩ Fib`, hence finite by
   `Set.Finite.subset`), and a member of least `ncard` is minimal. So Phase 11 writes
   `TaskFrame.saturation_of_fib_finite` beside `saturation_of_fib_subsingleton` rather than
   recording an obstruction. The `[COMPLETED WITH EXCLUSIONS]` escape the dispatch authorizes is
   retained as Phase 12/13's contingency only.
5. **`StarLanguage/` is genuinely free.** `ls FormalSystem/StarLanguage` is empty and no
   `Star*.lean` file exists anywhere in the tree; `PlusLanguage/README.md` already reserves the
   name in prose ("Their time-register half is what this tree reserves the name L⋆
   (`FormalSystem/StarLanguage/`) for"). Task 562's rename has landed. Note that 536's report
   cites the pre-rename paths `StarTruth.lean` / `StarDeterminism.lean` / `Conservativity/Star/`
   for what are now `PlusTruth.lean` / `PlusDeterminism.lean` / `Conservativity/Plus/`; translate
   every such path when reading it.

### Prior Plan Reference

No prior plan for task 561. The archived task 536 plan
(`specs/archive/536_stability_deterministic_collapse_store_recall/plans/01_determinism-collapse-and-non-definability.md`)
is the effort calibration: it landed the `⊡`-only half of this appendix at comparable module
sizes (`DriftFrame.lean` 254 lines, `DriftHistories.lean` 178, `StateSetTruth.lean` 240), which is
the per-phase size this plan targets. 536's own non-goals (II.5 of its report 02) are inherited
verbatim as this plan's Non-Goals.

### Roadmap Alignment

`specs/ROADMAP.md` was not supplied in the dispatch context and is not consulted by this plan.
No roadmap phases are added (the dispatch carries no `roadmap_flag`).

## Goals & Non-Goals

**Goals**:
- The bridge lemma as a biconditional: `TaskFrame.SingletonClasses`,
  `deterministic_of_singletonClasses` (the ZFC half, via `thm:extension`), and
  `deterministic_iff_singletonClasses`.
- The store/recall language and its semantics: `StarFormula`, the embedding `ofPlus`,
  `StarTruthAt` over points `(τ, x, v⃗)`, the truth-transfer `starTruthAt_ofPlus`, and the two
  transport lemmas `star_truth_congr_ext` and `starTruthAt_timeShift` (the latter with the
  stored-time vector **shifted**, not dropped).
- Validity for L⋆ and `app:deterministic-future`: `TaskFrame.StarValidOn`, `sentDet`, the paper's
  `(∗)` unfolding chain `sentDet_unfold`, the positive half `sentDet_of_deterministic`, and the
  negative half `refute_sentDet`.
- The live-text discrimination footnote: `fzero_refutes_sentDet` and `f1_sentDet`.
- Theorem C's `Det-pm` half: `detPM`, `detPM_of_deterministic`, `deterministic_of_detPM`, and the
  definability statement `deterministic_starDefinable`.
- The forward-determinism separation: `TaskFrame.saturation_of_fib_finite`,
  `TaskFrame.ForwardDeterministic`, the frame `FN`, `fn_forwardDeterministic`,
  `fn_not_deterministic`, and `fn_sentDet_atom` (the sentence-letter form; the schematic
  `fn_sentDet` is false — see the dated note in `## Lean Challenge Statements`).

**Non-Goals**:
- **No proof system for L⋆.** The names `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are
  claimed by this task's directory but are **not built here** — the deliverables are semantic
  throughout. Reserve them in `StarLanguage/README.md`; declare none of them.
- No constructors added to `PlusFormula`. Task 533's atomization/conservativity route rests on
  `stab_state_only`, which is false inside a recall scope; adding store/recall to `PlusFormula`
  would invalidate it. `StarFormula` is a separate inductive with an embedding, following the
  landed `MinusFormula`/`PlusFormula` pattern.
- No world registers on the main path. The evaluation point is `(τ, x, v⃗)` with `v⃗` a vector of
  stored **times** only, per `def:BLstar-semantics`'s own suppression of `μ⃗` in the appendix.
  A single-world-register `Det-m` is Phase 15, optional and last, and is deliberately excluded
  from the Goals and Challenge identifier sets above.
- No manuscript writes. Do not edit `possible_worlds.tex` and do not draft `Det-pm`/`Det-m`
  manuscript prose: PossibleWorlds task 105 owns that text and the file has a concurrent human
  editor. Reading by `\label` is permitted; citing by line number is not.
- No argument by uniform substitution anywhere. It is unsound here: `p → ⊡p` is frame-valid over
  `F°` while `Fp → ⊡Fp` is refutable.
- No restatement of `determined_of_deterministic` as a biconditional. Its converse is *proved
  false* (`determined_valid_on_non_deterministic`), not merely unproved.
- No choice-free pin promised for any "validity ⟹ frame condition" direction. Those manufacture
  separating worlds through `thm:extension` and are ZFC by construction (536 report 02 §II.4).
- No task numbers under `FormalSystem/`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `starTruthAt_timeShift`'s `box`/`stab` cases need an inverse shift plus congruence, as `plusTruthAt_timeShift` does — with a vector now in play the inverse-shift bookkeeping doubles | M | H | Phase 4 is scoped to the transport layer alone and follows `PlusTruth.lean`'s existing proof shape verbatim, substituting `(fun i => v i + Δ)` for the dropped vector. The identity `Function.update v i t ∘ (· + Δ) = Function.update (v · + Δ) i (t + Δ)` is the one new rewrite; prove it as a named helper first |
| `F^N`'s six `FrameOver` obligations are a full frame construction (the `DriftFrame.lean` shape, ~250 lines) and could overrun one agent run | M | M | Phase 12 builds the frame only; Phase 13 carries the results over it. If `saturation` resists, close Phase 12 `[COMPLETED WITH EXCLUSIONS]` with the obstruction evidenced, per the dispatch's explicit authorization — never with `sorry` |
| `TaskFrame.lean` is 105 KB; adding `saturation_of_fib_finite` there risks a slow edit/rebuild cycle | L | M | Phase 11 is a single insertion beside `saturation_of_fib_subsingleton` plus one line in the module docstring's Main Definitions list. Verification is `lake build FormalSystem.Semantics.TaskFrame` first, full build second |
| C15 rejects new docstrings citing `sent:det`, which has no row in `specs/paper-definitions-of-record.md` | M | H | Phase 14 adds the `sent:det` KNOWN-ANCHORS row and **updates two now-stale rows**: `app:deterministic-future` ("the Lean formalization of it is future work") and `def:BLstar-semantics` ("the store/recall clauses, which no module here implements"). Both become false the moment Phase 6 lands |
| C26 rejects a new `def`/`abbrev` whose name contains an underscore | L | M | Every new `def`/`abbrev` in this plan is camelCase (`StarFormula`, `StarTruthAt`, `ofPlus`, `sentDet`, `detPM`, `FN`, `ForwardDeterministic`, `SingletonClasses`); only `theorem` names are snake_case |
| C24 rejects a new module with no path to `FormalSystem.Init` | L | M | Every new module is imported from its component aggregator (`FormalSystem/StarLanguage.lean`, `FormalSystem/Semantics.lean`, `FormalSystem/Metalogic.lean`), and `FormalSystem/FormalSystem.lean` gains `import FormalSystem.StarLanguage`. Phase 2 lands the aggregator wiring with the first new module |
| Adding an `Extension.lean` import to `PlusDeterminism.lean` would drag Zorn into the module carrying the choice-free pin | M | M | Phase 1 writes a **new** module `Semantics/DeterministicBridge.lean`; `PlusDeterminism.lean` is not edited at all, so its four-declaration `[propext]` pin is visibly untouched |
| The `Det-pm` (⇒) direction is silently assumed choice-free by analogy with the collapse | H | L | It is ZFC: it concludes a frame condition and routes through Phase 1's Zorn half. Phase 10's docstring must say so, and must not carry a `Classical.choice`-free claim |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 11 | -- |
| 2 | 3, 12 | 2 (for 3), 11 (for 12) |
| 3 | 4, 5 | 3 |
| 4 | 6, 7 | 4, 5 |
| 5 | 8, 9, 13 | 6, 7 (for 8); 5, 6 (for 9); 6, 12 (for 13) |
| 6 | 10 | 1, 9 |
| 7 | 14 | 1-13 |
| 8 | 15 | 14 |

Phases within the same wave can execute in parallel.

---

### Phase 1: `lem:deterministic-singleton` as a biconditional [COMPLETED]

**Goal**: Land the (⇐) half — `⟨τ⟩_x = {τ}` for every `τ, x` implies `Deterministic` — via
`thm:extension`, and package it with the existing (⇒) half as one biconditional, without touching
`PlusDeterminism.lean`.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/DeterministicBridge.lean` importing
      `FormalSystem.Semantics.Extension.Extension` and `FormalSystem.Semantics.PlusDeterminism`.
- [ ] Define `TaskFrame.SingletonClasses F : Prop` as the pointwise-on-states form: for all total
      `τ σ` and all `x`, `SameStateAt τ σ x → ∀ y, τ.states y _ = σ.states y _`. Record in the
      docstring why the pointwise form is used on both sides (Overview note 2) and that it is
      strictly stronger as a hypothesis than the history-equality form.
- [ ] Prove `singletonClasses_of_deterministic : F.Deterministic → F.SingletonClasses` by direct
      application of `states_eq_of_deterministic`. Choice-free.
- [ ] Prove `deterministic_of_singletonClasses`. Route: `deterministic_iff`; given `w ⇒_x u` and
      `w ⇒_x v`, split on `x = 0` (`F.nullity_identity` closes it outright — the paper's
      *Limit* + `lem:nullity` Step 1 is unnecessary here, record the deviation) and `x ≠ 0`
      *(deviation: altered — the paper's Step 1, deriving `⇒_0 = id` from *Limit* plus
      `lem:nullity`, is **not transcribed**: `FrameOver.nullity_identity` is a structure field,
      so the `x = 0` branch closes on it outright. Recorded in the module docstring, as the plan
      directed.)*
      (build the two-point `PartialHistory` on the non-convex domain `fun t => t = 0 ∨ t = x`
      with `states t _ := if t = x then u else w`, discharging `respects_task` in four cases —
      `nullity_identity` twice, the hypothesis once, and `F.converse` once; extend both by
      `PartialHistory.extension`; read off `states 0 = w` and `states x = u` / `= v` from
      `Extends.agree`; apply `SingletonClasses` at time `0` and instant `x`).
- [ ] Prove `deterministic_iff_singletonClasses` as the `⟨_, _⟩` of the two halves.
- [ ] Record the choice dependence honestly in the module docstring, mirroring `thm:extension`'s
      own footnote: the (⇐) half is a theorem of ZFC via Zorn; the (⇒) half is choice-free and its
      pin in `PlusDeterminism.lean` is untouched by this module's existence.
- [ ] Add `import FormalSystem.Semantics.DeterministicBridge` to `FormalSystem/Semantics.lean`.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/DeterministicBridge.lean` - new module (all four declarations)
- `FormalSystem/Semantics.lean` - one aggregator import line

**Verification**:
- `lake build` green, no `sorry`
- `#print axioms FormalSystem.Semantics.deterministic_of_singletonClasses` reports
  `Classical.choice` (expected, recorded); `#print axioms
  FormalSystem.Semantics.states_eq_of_deterministic` still reports `[propext]` only
- `git diff --stat FormalSystem/Semantics/PlusDeterminism.lean` is empty

---

### Phase 2: `StarFormula` and the `StarLanguage/` component [COMPLETED]

**Goal**: Land the L⋆ formula type — L⁺ plus `timeStore i` and `timeRecall i` for `i : ℕ` — as a
separate inductive with a constructor-to-constructor embedding from `PlusFormula`, following the
landed `MinusLanguage`/`PlusLanguage` pattern.

**Tasks**:
- [ ] Create `FormalSystem/StarLanguage/Formula.lean` with `inductive StarFormula` carrying
      `atom`, `bot`, `imp`, `box`, `untl`, `snce`, `stab`, `timeStore (i : ℕ)`,
      `timeRecall (i : ℕ)`.
- [ ] Mirror `PlusFormula`'s derived operators verbatim — `top`, `neg`, `someFuture`, `somePast`,
      `allFuture`, `allPast`, `and`, `or`, `iff`, `diamond`, `always`, `sometimes` — using
      `PlusFormula`'s right-hand sides unchanged, so the embedding commutes with each by `rfl`.
      `always` is required by Phase 9 and must be present.
- [ ] Define `ofPlus : PlusFormula → StarFormula`, constructor for constructor, with
      `ofPlus_injective` and the `rfl`-shaped commutation lemmas for the derived operators the
      later phases consume (`ofPlus_neg`, `ofPlus_allFuture`, `ofPlus_always` at minimum).
- [ ] Create `FormalSystem/StarLanguage.lean` (component aggregator, `PlusLanguage.lean`'s shape)
      and `FormalSystem/StarLanguage/README.md` (`PlusLanguage/README.md`'s shape), including the
      **module invariant** section: nothing under `FormalSystem/StarLanguage/` imports anything
      from `FormalSystem/Semantics/`, checkable by
      `grep -rn 'FormalSystem.Semantics' FormalSystem/StarLanguage/`.
- [ ] Record in the README that `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are
      **reserved and unbuilt** — this component is semantic-only.
- [ ] Add `import FormalSystem.StarLanguage` to `FormalSystem/FormalSystem.lean`, placed after
      `FormalSystem.PlusLanguage`.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: this phase asserts a **nine-constructor** inductive and an enumerated
derived-operator list drawn from `PlusLanguage/Formula.lean`. Confirm at implementation time by
`grep -c '^  | ' FormalSystem/PlusLanguage/Formula.lean` against the mirrored set and by
`grep -n '^def ' FormalSystem/PlusLanguage/Formula.lean`; mirror exactly what is there, and record
any operator deliberately not mirrored.

**Files to modify**:
- `FormalSystem/StarLanguage/Formula.lean` - new
- `FormalSystem/StarLanguage/README.md` - new
- `FormalSystem/StarLanguage.lean` - new aggregator
- `FormalSystem/FormalSystem.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/` returns nothing
- `lake exe checkInitImports` (C24) passes for the new modules

---

### Phase 3: `StarTruthAt` over points `(τ, x, v⃗)` [COMPLETED]

**Goal**: Land the truth recursion for L⋆ over the manuscript's `def:BLstar-semantics` point with
world registers suppressed, plus the clause lemmas and the embedding's truth transfer.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/StarTruth.lean`. Define
      `StarTruthAt (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (v : ℕ → F.Duration) :
      StarFormula → Prop`, with the seven L⁺ clauses carried over from `PlusTruthAt` verbatim
      (`v` threaded untouched, including through `box` and `stab`) and the two new clauses:
      `timeStore i φ` at `(τ, x, v)` iff `φ` at `(τ, x, Function.update v i x)`;
      `timeRecall i φ` at `(τ, x, v)` iff `φ` at `(τ, v i, v)`.
- [ ] Add the clause lemmas mirroring `PlusTruth.*` (`atom_iff`, `stab_iff`, `untl_iff`, …, plus
      `timeStore_iff` and `timeRecall_iff`).
- [ ] Prove `starTruthAt_ofPlus : StarTruthAt M τ x v (ofPlus φ) ↔ PlusTruthAt M τ x φ` by
      induction on `φ`; `v` is inert on the image of `ofPlus`.
- [ ] Module docstring must record, as design decisions rather than defects: (a)
      `plusTruthAt_timeShift`'s L⋆ restatement carries the vector **shifted** (`v⃗ + c`), not
      dropped — the statement lands in Phase 4; (b) `stab_state_only` **fails inside a recall
      scope, by design** — it is the invariant this language is built to break, and it is why
      task 533's atomization route must not be extended to `StarFormula`.
- [ ] Add `import FormalSystem.Semantics.StarTruth` to `FormalSystem/Semantics.lean`.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarTruth.lean` - new
- `FormalSystem/Semantics.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `starTruthAt_ofPlus` elaborates with `v` universally quantified and unused in the conclusion

---

### Phase 4: the transport layer — congruence and vector-shifted time shift [COMPLETED]

**Goal**: Restate the two transport lemmas 536's report 02 §II.3 flagged as breaking, in the forms
that survive time registers.

**Tasks**:
- [ ] Prove the update/shift commutation helper first, as a named lemma:
      `Function.update v i t` shifted pointwise by `Δ` equals `Function.update (fun j => v j + Δ) i (t + Δ)`.
- [ ] Prove `star_truth_congr_ext`: the L⋆ analogue of `truth_congr_ext`, transporting truth
      between two total histories agreeing pointwise on states, at a fixed `v`.
- [x] Prove `starTruthAt_timeShift`: *(deviation: altered — the pinned Challenge statement's
      totality hypothesis `hσ : σ.IsTotal` is **dropped**, which strengthens the lemma. It is
      unused: the `box` and `stab` cases apply totality to the quantified history `ρ`, never to
      `σ`, exactly as `plusTruthAt_timeShift` — which likewise takes no totality hypothesis —
      does. Recorded in the lemma's own docstring.)*
      `StarTruthAt M (σ.timeShift Δ) t v φ ↔ StarTruthAt M σ (t + Δ) (fun i => v i + Δ) φ`,
      following `plusTruthAt_timeShift`'s proof shape (the `box` and `stab` cases need the inverse
      shift plus `star_truth_congr_ext`); the `timeStore` case consumes the helper above, the
      `timeRecall` case is the vector lookup commuting with the shift.
- [ ] Record in the docstring that this is the restatement the dispatch requires — the vector is
      shifted, never dropped — and cross-reference 536 report 02 §II.3's entry for
      `starTruthAt_timeShift` (which is stated there against the pre-rename file name).

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarTruth.lean` - the transport section appended

**Verification**:
- `lake build` green, no `sorry`
- Both lemmas stated with `v` explicit; no lemma in the file asserts a state-only dependence for
  `stab` at a `StarFormula` argument

---

### Phase 5: L⋆ validity, `sent:det`, and the `(∗)` unfolding chain [COMPLETED]

**Goal**: Land validity for L⋆ (quantifying over stored-time vectors, as `def:frame-validity`
requires once `v⃗` is a parameter of the point), the sentence `sent:det`, and the paper's `(∗)`
biconditional chain as a reusable lemma.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/StarValidity.lean` mirroring `PlusValidity.lean`:
      `TaskFrame.StarValidOn F φ := ∀ M (τ : TaskFrame.HF F) x v, StarTruthAt M τ.val x v φ`,
      then `StarValidOnFrames` (the primitive, indexed by a bare frame predicate),
      `StarValidIn`, `StarValid`, and the `mono` lemmas.
- [ ] Prove `starValidOn_ofPlus`-shaped transfer: `F.StarValidOn (ofPlus φ) ↔ F.PlusValidOn φ`,
      from `starTruthAt_ofPlus`.
- [x] Define `sentDet (φ : StarFormula) : StarFormula` as
      `timeStore 1 (someFuture (timeStore 2 (timeRecall 1 (or (stab (timeRecall 2 φ.neg)) (stab (timeRecall 2 φ))))))`,
      transcribing `sent:det` exactly. Record the register indices used (`1` and `2`) and that
      `someFuture` is the tree's `F`. *(deviation: altered — `allFuture`, not `someFuture`. The
      manuscript defines `\Future` in its preamble as a **boxed** `F` (universal future), and
      `app:deterministic-future`'s `(∗)` chain reads "for all `y > x`". This phase's own Scope
      Hypothesis provided for exactly this: "if the display differs, the definition follows the
      manuscript and this line is superseded." Recorded in `StarValidity.lean`'s docstring. The
      plan's pinned `sentDet_unfold` Challenge statement — a `∀ y, x < y → …` — already agreed
      with the manuscript, so the Challenge section needed no change.)*
- [ ] Prove `sentDet_unfold`, the paper's `(∗)`: truth of `sentDet φ` at `(τ, x, v)` is equivalent
      to `∀ y > x`, the disjunction `stab (timeRecall 2 φ.neg) ∨ stab (timeRecall 2 φ)` holding at
      `(τ, x, Function.update (Function.update v 1 x) 2 y)`. Four rewrite steps, one per line of
      the paper's chain.
- [ ] Add `import FormalSystem.Semantics.StarValidity` to `FormalSystem/Semantics.lean`.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: this phase asserts that `sent:det` uses exactly **two** registers, indices
`1` and `2`, and the tree's `someFuture` for `\Future`. Confirm at implementation time against the
manuscript's `sent:det` display (by `\label`, never by line number) before fixing the definition;
if the display differs, the definition follows the manuscript and this line is superseded.

**Files to modify**:
- `FormalSystem/Semantics/StarValidity.lean` - new
- `FormalSystem/Semantics.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `sentDet_unfold` is stated as an `Iff` and closes by `Iff.rfl` or a short `simp only` over the
  clause lemmas

---

### Phase 6: `app:deterministic-future`, positive half [COMPLETED]

**Goal**: `sentDet φ` is valid over every `TaskFrame.Deterministic` frame, for every
`StarFormula φ`, consuming `states_eq_of_deterministic` rather than re-deriving the collapse.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/StarDeterminism.lean`.
- [ ] Prove the L⋆ collapse at a point: over a deterministic frame, any total `σ` with
      `SameStateAt τ σ x` agrees with `τ` at every time (`states_eq_of_deterministic`), so
      `star_truth_congr_ext` transports every `StarFormula` from `τ` to `σ` at any `v`. This is
      the L⋆ twin of `stab_iff_of_deterministic` and is the phase's engine.
- [ ] Prove `sentDet_of_deterministic : F.Deterministic → ∀ φ, F.StarValidOn (sentDet φ)`, by
      `sentDet_unfold` plus a case split on whether `φ` holds at `(τ, y, v')`: the first case gives
      the `stab (timeRecall 2 φ)` disjunct, the second the `stab (timeRecall 2 φ.neg)` disjunct —
      the paper's own two-line argument.
- [ ] Docstring: state that this half is the safe direction (frame condition ⟹ validity) and
      records only `[propext]`-class dependence modulo the carrier; pin it with `#print axioms`
      in the docstring following `PlusDeterminism.lean`'s convention.
- [ ] Add `import FormalSystem.Semantics.StarDeterminism` to `FormalSystem/Semantics.lean`.

**Timing**: 1.5 hours

**Depends on**: 4, 5

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` - new
- `FormalSystem/Semantics.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `#print axioms FormalSystem.Semantics.sentDet_of_deterministic` recorded in the docstring and
  matching the actual output

---

### Phase 7: `app:deterministic-future`, negative half [COMPLETED]

**Goal**: Refute `sentDet` over a non-deterministic frame, reusing the tree's existing countermodel
for `app:deterministic` — which is what the paper's own proof does.

**Tasks**:
- [ ] Create `FormalSystem/Semantics/StarNonValidities.lean` importing
      `FormalSystem.Semantics.PlusNonValidities` (for `NF`, `natHist`, `natHist_isTotal`,
      `natModel`) and `FormalSystem.Semantics.StarValidity`.
- [ ] Prove `refute_sentDet (p : Atom) : ¬ StarValid (sentDet (StarFormula.atom p))`, at
      `τ = natHist (fun _ => 0)`, `x = 0`, `y = 1`, with `σ = natHist (fun s => if s ≤ 0 then 0 else 1)`
      as the `⊡`-witness. `natModel`'s valuation `n = 0` gives `|p| = {0}`, so `τ(1) ∈ |p|` and
      `σ(1) ∉ |p|` while `τ(0) = σ(0)`: `σ` refutes the `p` disjunct and `τ` itself refutes the
      `¬p` disjunct, exactly the paper's pair of witnesses.
- [ ] Docstring: record that `NF` is this tree's `F'` — the same non-deterministic frame and
      countermodel `app:deterministic`'s negative half (`refute_determined`) already uses — and
      that this is the paper's own reuse, not a substitution.
- [ ] Add `import FormalSystem.Semantics.StarNonValidities` to `FormalSystem/Semantics.lean`.

**Timing**: 1 hour

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarNonValidities.lean` - new
- `FormalSystem/Semantics.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- The refutation names the same history pair as `refute_determined`; a `grep` of both proofs shows
  the shared `fun s => if s ≤ 0 then 0 else 1` witness

---

### Phase 8: the discrimination footnote — `F°` refutes `sent:det`, `F¹` validates it [COMPLETED]

**Goal**: Land the live-text footnote following `app:deterministic-future`: store/recall
discriminate `F°` from `F¹`, which `cor:no-characterization` shows nothing without them can.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/StarDiscrimination.lean` importing `DriftFrame`,
      `RealTranslationFrame`, and the Phase 6/7 modules.
- [ ] Prove `fzero_refutes_sentDet`: over `F0`, with `|p| = [3/2, ∞)` and the possible worlds
      `τ(t) = t`, `σ(t) = 2t`, both disjuncts of `sentDet` fail at `(σ, 0)` — the paper's own
      witnesses, transcribed. Requires exhibiting `τ` and `σ` as total histories of `F0`; use
      `DriftHistories.lean`'s affine-witness idiom rather than the general `cor:occurrence`.
- [ ] Prove `f1_sentDet : ∀ φ, F1.StarValidOn (sentDet φ)` as `sentDet_of_deterministic` applied
      to `f1_deterministic` — one line; this half is Phase 6's positive result instantiated, and
      the phase must not re-derive it.
- [ ] State the discrimination as a single named result: `sentDet` separates `F0` from `F1` while,
      by `deterministic_not_plusDefinable`, no `PlusFormula` does. Cite
      `cor:no-characterization` and `app:drift` by `\label`, and cite
      `deterministic_not_plusDefinable` (`Independence/DeterminismUndefinable.lean`) by name.
- [ ] Add the module to `FormalSystem/Metalogic.lean` (or the `Independence` aggregator it uses)
      and add a row to `FormalSystem/Metalogic/Independence/README.md`'s Modules table.

**Timing**: 1.5 hours

**Depends on**: 6, 7

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Independence/StarDiscrimination.lean` - new
- `FormalSystem/Metalogic/Independence/README.md` - one Modules row, plus a Key Results entry
- `FormalSystem/Metalogic.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `f1_sentDet`'s proof term references `sentDet_of_deterministic` and `f1_deterministic` and
  nothing else

---

### Phase 9: `Det-pm`, and its validity over the deterministic frames [COMPLETED]

**Goal**: Define `Det-pm` — `sent:det` with `\Future` replaced by `always` — and land the (⇐)
direction of Theorem C from Phase 6's engine.

**Tasks**:
- [ ] In `FormalSystem/Semantics/StarDeterminism.lean`, define
      `detPM (p : Atom) : StarFormula` as `sentDet`'s shape with `someFuture` replaced by
      `always`, transcribing task 105 report 02 §4's display. Use a bare atom `p`, not a schema
      variable — the report's §4.1 note that one sentence letter suffices is what makes the later
      (⇒) direction legitimate, and it is **not** an appeal to uniform substitution.
- [ ] Prove `detPM_unfold`, the `always` analogue of `sentDet_unfold`: truth at `(τ, x, v)` iff
      for **all** `y` (not only `y > x`) the disjunction holds at the twice-updated vector. The
      paper's chain transfers verbatim because temporal operators do not disturb `v⃗`; the one new
      ingredient is `always`'s three-way unfolding into `allPast ∧ · ∧ allFuture`.
- [ ] Prove `detPM_of_deterministic : F.Deterministic → ∀ p, F.StarValidOn (detPM p)`, reusing
      Phase 6's collapse engine unchanged.
- [ ] Docstring: cite **Theorem C as a report-level result pending paper integration** — never as
      manuscript text and never as a conjecture (536 report 02 §I.5) — naming the PossibleWorlds
      task 105 report as its source.

**Timing**: 1.5 hours

**Depends on**: 5, 6

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` - the `Det-pm` section appended

**Verification**:
- `lake build` green, no `sorry`
- The docstring's Theorem C citation names the report path and carries no manuscript `\label`
  claiming `Det-pm` appears in the paper

---

### Phase 10: Theorem C, `Det-pm` half — `Det-pm` defines the deterministic frames [COMPLETED]

**Goal**: The (⇒) direction and the definability biconditional: `F.StarValidOn (detPM p)` iff
`F.Deterministic`.

**Tasks**:
- [ ] Prove `deterministic_of_detPM`: assume `F.StarValidOn (detPM p)`. Fix total `τ`, `σ` with
      `SameStateAt τ σ x`, and `y`. Take the model over `F` with `M.valuation w _ := w = τ.states y _`
      (the report's singleton valuation `|p| = {τ(y)}`). The `¬p` disjunct fails, witnessed by `τ`
      itself; so the `p` disjunct holds and `σ.states y _ = τ.states y _`. As `y` was arbitrary
      this is `F.SingletonClasses`, and Phase 1's `deterministic_of_singletonClasses` closes.
- [ ] Prove `deterministic_starDefinable : (∀ p, F.StarValidOn (detPM p)) ↔ F.Deterministic`
      (or the single-`p` form if the singleton valuation makes one letter sufficient — decide at
      implementation time and record which was taken).
- [ ] Docstring: state plainly that this direction is **ZFC**, because it concludes a frame
      condition and routes through `thm:extension` (536 report 02 §II.4's choice-asymmetry table).
      Do **not** promise or attempt a choice-free pin. Do record the actual `#print axioms` output.
- [ ] Docstring: record that the single-sentence-letter statement is legitimate by task 105 report
      02 §4.1 (forward direction proved for arbitrary `φ`, converse by one valuation), and is
      **not** an appeal to uniform substitution, which is unsound here.

**Timing**: 1.5 hours

**Depends on**: 1, 9

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` - the definability section appended

**Verification**:
- `lake build` green, no `sorry`
- `#print axioms FormalSystem.Semantics.deterministic_of_detPM` reports `Classical.choice`, and
  the docstring says so rather than claiming otherwise

---

### Phase 11: the finite-fibres *Saturation* helper [COMPLETED]

**Goal**: Land `TaskFrame.saturation_of_fib_finite` — the helper 536 flagged as possibly
nonexistent — beside its subsingleton sibling, unblocking `F^N`.

**Tasks**:
- [ ] In `FormalSystem/Semantics/TaskFrame.lean`, beside `saturation_of_fib_subsingleton`, prove
      `saturation_of_fib_finite {W : Type} {R : W → D → W → Prop} (h : ∀ w x, (Fib R w x).Finite) :
      Saturation R`.
- [ ] Route: every member of a fibre/segment family is finite (a segment is `Fib ∩ Fib`, so
      `Set.Finite.subset` with `Set.inter_subset_left`); a nonempty finite family-member set has a
      member of least `ncard`; least cardinality plus finiteness upgrades to `⊆`-minimality; then
      `sInter_nonempty_of_directed_of_minimal` closes.
- [ ] Docstring: record that this is the finite-**fibres** variant of `cor:saturation-finite`
      (which is the finite-**carrier** result and does not apply when `W` is infinite), that the
      constructive core is `sInter_nonempty_of_directed_of_minimal`, and the honest axiom
      dependence of producing the minimal member.
- [ ] Add the new name to `TaskFrame.lean`'s module-docstring Main Definitions list, beside the
      existing `saturation_of_fib_subsingleton` entry.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Semantics/TaskFrame.lean` - one theorem plus one docstring list line

**Verification**:
- `lake build FormalSystem.Semantics.TaskFrame` green first, then full `lake build` green
- No `sorry`; `saturation_of_fib_subsingleton`'s statement and proof are byte-identical to before
  (`git diff` shows only additions)

---

### Phase 12: `ForwardDeterministic` and the separating frame `F^N` [COMPLETED]

**Goal**: State the forward-deterministic predicate and build the frame `F^N` — `W = ℕ`, `D = ℤ`,
`f(0) = 0`, `f(n) = n - 1`, `w ⇒_n u` iff `u = f^n(w)` for `n ≥ 0`, extended by the converse
convention — discharging all six `FrameOver` obligations.

**Tasks**:
- [ ] In `FormalSystem/Semantics/FrameProperty.lean`, define
      `TaskFrame.ForwardDeterministic F : Prop` as the fibre-subsingleton condition restricted to
      `0 ≤ d`. Docstring must point at `Deterministic`'s own docstring, which already explains why
      the **unrestricted** binder is the real notion, and must state that `ForwardDeterministic` is
      strictly weaker and is introduced only to name what `sent:det` defines.
- [ ] Create `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`. Define the
      relation two-sidedly and prove the six obligations: `nullity_identity` (`f^0 = id`),
      `converse` (by definition), `comp` in both directions (`u := f^x w` interpolates, since
      `f^y ∘ f^x = f^(x+y)`), `serial` (`f^x w` forward, `w + x` backward), `limit` via
      `TaskFrame.limit_of_succOrder` (ℤ is a `SuccOrder` with `NoMaxOrder`), and `saturation` via
      Phase 11's `saturation_of_fib_finite` — fibres at `d ≥ 0` are singletons and at `d < 0` are
      contained in `Set.Iic (w + (-d))`, hence finite.
- [ ] Prove `fn_forwardDeterministic : FN.ForwardDeterministic` and
      `fn_not_deterministic : ¬ FN.Deterministic` (the witness is `fib 0 (-1) = {0, 1}`, i.e.
      `0 ⇒_{-1} 0` and `0 ⇒_{-1} 1`).
- [ ] Docstring: record task 105 report 02 §3.3's observation that the separating frame **must be
      infinite** — on a finite `W`, *Seriality* makes each `⇒_x` (`x ≥ 0`) surjective and hence
      injective, so forward determinism already entails backward determinism. `W = ℕ` is not
      incidental.

**Timing**: 2 hours

**Depends on**: 11

**Verification Tier**: full

**Scope Hypothesis**: this phase asserts **six** `FrameOver` obligations and a single new module of
roughly `DriftFrame.lean`'s size. Confirm the obligation count at implementation time by reading
`structure FrameOver`'s field list in `Semantics/TaskFrame.lean`; if `saturation` genuinely resists
after Phase 11's helper is in hand, close this phase `[COMPLETED WITH EXCLUSIONS]` with a
`#### Reasoned Exclusions` table naming the obstruction and its evidence — never with `sorry`.

**Files to modify**:
- `FormalSystem/Semantics/FrameProperty.lean` - `ForwardDeterministic` plus a docstring pointer
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` - new
- `FormalSystem/Metalogic/Independence/README.md` - one Modules row
- `FormalSystem/Metalogic.lean` - one import line

**Verification**:
- `lake build` green, no `sorry`
- `fn_not_deterministic` and `fn_forwardDeterministic` both elaborate against the frame as built

---

### Phase 13: `sent:det` defines only forward determinism [COMPLETED WITH EXCLUSIONS]

**Goal**: Close deliverable (6): `sent:det` is valid over `F^N`, which is not `Deterministic` —
so `sent:det` does not characterize the deterministic frames, only the forward-deterministic ones.

**Tasks**:
- [ ] Prove the forward analogue of Phase 6's engine: on a `ForwardDeterministic` frame, two total
      histories agreeing at `x` agree at every `y ≥ x`. This is `states_eq_of_deterministic`'s
      proof with the duration `y - x` now nonnegative, which is exactly the instance the guarded
      binder supports.
- [x] Prove `fn_sentDet : ∀ φ, FN.StarValidOn (sentDet φ)` from that engine plus `sentDet_unfold`
      (whose `∀ y > x` restriction is what makes the forward engine sufficient).
      *(deviation: altered — landed as `fn_sentDet_atom (p : Atom)`, at a **sentence letter**.
      The recorded schematic statement is **false**, and `fn_refutes_sentDet_somePast` is the
      machine-checked refutation. See the Reasoned Exclusions table below.)*
- [ ] State the separation as a named result: `sentDet` is valid over `FN` while
      `¬ FN.Deterministic`, so no reading of `app:deterministic-future` may be strengthened to a
      characterization. Contrast it explicitly with Phase 10's `deterministic_starDefinable`,
      where `always` closes the gap.
- [ ] Docstring: record that `lem:deterministic-singleton` genuinely requires the bidirectional
      reading of `def:deterministic` — weakening the definition to `0 ≤ d` would make `F^N`
      deterministic and the singleton lemma false (task 105 report 02 §3.3, consequence 2).

**Timing**: 1.5 hours

**Depends on**: 6, 12

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` - the results section appended

**Verification**:
- `lake build` green, no `sorry`
- The separation result names both `fn_sentDet_atom` and `fn_not_deterministic` in one statement
  (`fn_separates`), so a reader cannot take either half alone for a characterization

#### Reasoned Exclusions

| Excluded item | Reason | Evidence |
|---|---|---|
| `fn_sentDet (φ : StarFormula) : FN.StarValidOn (sentDet φ)` — the schematic form formerly pinned in `## Lean Challenge Statements`, corrected there in place on 2026-09-08 | **The recorded statement is false.** Forward determinism settles the future and says nothing about the past, so a past-looking instance distinguishes two possible worlds of the same stability class at a *future* time. `F^N`'s own witnesses `fnZeroHist ≡ 0` and `fnRampHist n = max(0, −n)` agree at `0` and differ at every negative time; with `\|p\| = {3}`, `P p` holds for the ramp world at time `1` and fails for the constant world, so both disjuncts of `settledDisj` fail at `(τ, 0, ·)` with register `2` holding `1`. | `fn_refutes_sentDet_somePast` and `not_forall_fn_sentDet` (`Metalogic/Independence/ForwardDeterministicFrame.lean`) — Lean-checked refutations of the recorded statement, `lake build` green |
| — replaced by | `fn_sentDet_atom (p : Atom) : FN.StarValidOn (sentDet (StarFormula.atom p))`, the sentence-letter form. This is what the ground-truth source actually claims: PossibleWorlds task 105 report 02 §3.2's Theorem A runs the singleton valuation `\|p\| = {τ(y)}`, so its statement is at the sentence-letter level throughout. Nothing in the source is contradicted; the plan generalised it one step too far. | `fn_sentDet_atom`, `fn_separates`, `fn_forwardDeterministic_not_singletonClasses` |

**Raised for the user, not laundered.** Per `.claude/rules/plan-compliance.md`, a same-named
weaker restatement is the defect this section exists to catch. The recorded statement is not
weakened here — it is *disproved*, and the disproof is in the tree. Deliverable (6) of the
dispatch ("`sent:det` defines only FORWARD determinism (separating frame `F^N`)") is delivered in
full; only the plan's over-general Challenge line is excluded, with the refutation as evidence.

---

### Phase 14: documentation, correspondence table, and the invariant gates [COMPLETED]

**Goal**: Every manuscript `\label` this task touches maps to a Lean name or an explicit
exclusion, every new anchor is recorded, and the module-invariant script is green.

**Tasks**:
- [ ] Extend the paper-label correspondence table so each of `lem:deterministic-singleton` (now
      **both** halves), `app:deterministic-future` (both halves), `sent:det`, the discrimination
      footnote, `def:BLstar-semantics`'s store/recall clauses, and Theorem C's `Det-pm` half maps
      to a Lean declaration or a stated exclusion. Place it in `FormalSystem/StarLanguage/README.md`
      (the new component's own table) and cross-link it from
      `FormalSystem/Metalogic/Independence/README.md` and `FormalSystem/PlusLanguage/README.md`.
      Record `Det-m` and `TM⋆` as explicit exclusions with reasons.
- [ ] Add the `sent:det` row to `specs/paper-definitions-of-record.md`'s KNOWN-ANCHORS block
      (`LIVE-UNPINNED`, cited by name only).
- [ ] **Update two now-stale KNOWN-ANCHORS rows**: `app:deterministic-future`'s note says "the
      Lean formalization of it is future work", and `def:BLstar-semantics`'s says "the store/recall
      clauses, which no module here implements". Both are false once Phases 3 and 6 land.
- [ ] Update `FormalSystem/PlusLanguage/README.md`'s reservation sentence to point at the built
      `StarLanguage/` rather than a reserved name, and `FormalSystem/Semantics/README.md`'s module
      table with the four new `Star*.lean` modules plus `DeterministicBridge.lean`.
- [ ] Run `bash scripts/check-module-invariants.sh` and bring C2, C3, C14, C15, C24 and C26 green.
      C14 in particular needs the new declarations' documented axiom counts to match the tree —
      update every `#print axioms` figure asserted in a docstring to the value actually reported.
- [ ] Run `bash scripts/check-task-references.sh` to confirm no task number leaked into
      `FormalSystem/**` or any deliverable outside `specs/**`.

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13

**Verification Tier**: full

**Scope Hypothesis**: this phase asserts **one new** and **two updated** KNOWN-ANCHORS rows, and
five new modules to list in `Semantics/README.md`. Confirm both counts at implementation time by
`grep -n 'sent:det\|app:deterministic-future\|def:BLstar-semantics' specs/paper-definitions-of-record.md`
and by `git status --short FormalSystem/` against the modules actually landed; if a phase closed
`[COMPLETED WITH EXCLUSIONS]`, the counts shrink accordingly and the exclusion is recorded in the
correspondence table rather than silently dropped.

**Files to modify**:
- `FormalSystem/StarLanguage/README.md` - the correspondence table
- `FormalSystem/PlusLanguage/README.md` - reservation sentence updated to a pointer
- `FormalSystem/Metalogic/Independence/README.md` - cross-link plus Key Results
- `FormalSystem/Semantics/README.md` - module table rows
- `specs/paper-definitions-of-record.md` - one new row, two updated rows

**Verification**:
- `bash scripts/check-module-invariants.sh` reports C2, C3, C14, C15, C24, C26 pass
- `bash scripts/check-task-references.sh` clean
- `lake build` green, no `sorry` anywhere in the new modules

---

### Phase 15: OPTIONAL — `Det-m` with a single world register [COMPLETED WITH EXCLUSIONS]

**Goal**: Optional and last. Add a single world register `μ` to the evaluation point and land
Theorem C's `Det-m` half, per 536 report 02 §II.1.

**Tasks**:
- [ ] Extend the point to `(τ, x, v⃗, μ)` with `μ : F.HF`, adding `worldStore` and `worldRecall`
      constructors, per `def:BLstar-semantics`'s `(↑_M)`/`(↓_M)` clauses.
- [ ] Define `detM` as `⇃w¹ ⊡ always (p ↔ ↾w¹ p)` and prove it defines the deterministic frames,
      reusing Phase 1 for the (⇒) direction and Phase 6's engine for (⇐).
- [ ] Restate `star_truth_congr_ext` for the two-component point (536 report 02 §II.3: pointwise
      state agreement no longer suffices, since the register can point at a third history).

**Timing**: 2 hours

**Depends on**: 14

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/StarLanguage/Formula.lean` - two constructors
- `FormalSystem/Semantics/StarTruth.lean` - the register component and the restated congruence
- `FormalSystem/Semantics/StarDeterminism.lean` - `detM` and its definability theorem

**Verification**:
- `lake build` green, no `sorry`
- If not attempted, close as `[COMPLETED WITH EXCLUSIONS]` with a one-row
  `#### Reasoned Exclusions` table recording that the phase was declared optional at plan time and
  that every committed deliverable landed without it

#### Reasoned Exclusions

| Excluded item | Reason | Evidence |
|---|---|---|
| World registers `↑_M`/`↓_M`, `detM`, and the two-component-point restatement of `star_truth_congr_ext` | Declared **optional and last** at plan time (dispatch deliverable 7, "OPTIONAL: Det-m with a single world register"), and deliberately excluded from the plan's Goals and Challenge identifier sets. Every committed deliverable (1)-(6) landed without it. | Goals section of this plan lists no `Det-m` identifier; `FormalSystem/StarLanguage/README.md`'s correspondence table records `Det-m` and the world-register clauses of `def:BLstar-semantics` as explicit exclusions with reasons |

---

## Lean Challenge Statements

```lean
import FormalSystem.Semantics.PlusDeterminism
import FormalSystem.Semantics.PlusNonValidities
import FormalSystem.Semantics.Extension.Extension
import FormalSystem.Metalogic.Independence.DriftFrame
import FormalSystem.Metalogic.Independence.RealTranslationFrame

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage

/-! Phase 1 -/

/-- `⟨τ⟩_x = {τ}` for every possible world and time, in the tree's pointwise-on-states form. -/
def TaskFrame.SingletonClasses (F : TaskFrame) : Prop := sorry

theorem deterministic_of_singletonClasses {F : TaskFrame} (h : F.SingletonClasses) :
    F.Deterministic := sorry

theorem deterministic_iff_singletonClasses (F : TaskFrame) :
    F.Deterministic ↔ F.SingletonClasses := sorry

/-! Phase 2 — the carriers, pinned as opaque `def`s because the real declarations are an
`inductive` and its recursor-shaped embedding. -/

/-- The language L⋆ = L⁺ + time store/recall. -/
def StarFormula : Type := sorry

/-- The constructor-to-constructor embedding of L⁺ into L⋆. -/
def ofPlus : PlusFormula → StarFormula := sorry

/-! Phases 3-4 -/

/-- Truth of an L⋆ formula at a model, history, time, and stored-time vector. -/
def StarTruthAt {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (v : ℕ → F.Duration) : StarFormula → Prop := sorry

theorem starTruthAt_ofPlus {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (x : F.Duration) (v : ℕ → F.Duration) (φ : PlusFormula) :
    StarTruthAt M τ x v (ofPlus φ) ↔ PlusTruthAt M τ x φ := sorry

theorem star_truth_congr_ext {F : TaskFrame} (M : TaskModel F) (φ : StarFormula)
    (τ σ : ConvexHistory F) (x : F.Duration) (v : ℕ → F.Duration)
    (hdom : ∀ s, τ.domain s ↔ σ.domain s)
    (hst : ∀ (s : F.Duration) (hτ : τ.domain s) (hσ : σ.domain s),
      τ.states s hτ = σ.states s hσ) :
    StarTruthAt M τ x v φ ↔ StarTruthAt M σ x v φ := sorry

theorem starTruthAt_timeShift {F : TaskFrame} (M : TaskModel F) (φ : StarFormula)
    (σ : ConvexHistory F) (hσ : σ.IsTotal) (t Δ : F.Duration) (v : ℕ → F.Duration) :
    StarTruthAt M (σ.timeShift Δ) t v φ ↔ StarTruthAt M σ (t + Δ) (fun i => v i + Δ) φ := sorry

/-! Phase 5 -/

/-- `def:frame-validity` for L⋆: true at every model, possible world, time, and stored-time
vector. -/
def TaskFrame.StarValidOn (F : TaskFrame) (φ : StarFormula) : Prop := sorry

/-- `sent:det`, transcribed. -/
def sentDet (φ : StarFormula) : StarFormula := sorry

/-- The paper's `(∗)` chain for `sent:det`. -/
theorem sentDet_unfold {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (v : ℕ → F.Duration) (φ : StarFormula) :
    StarTruthAt M τ x v (sentDet φ) ↔
      ∀ y : F.Duration, x < y →
        StarTruthAt M τ x (Function.update (Function.update v 1 x) 2 y)
          (sorry : StarFormula) := sorry

/-! Phase 6 -/

theorem sentDet_of_deterministic {F : TaskFrame} (hD : F.Deterministic) (φ : StarFormula) :
    F.StarValidOn (sentDet φ) := sorry

/-! Phase 7 -/

theorem refute_sentDet (p : Atom) :
    ¬ NF.StarValidOn (sentDet (ofPlus (PlusFormula.atom p))) := sorry

/-! Phases 9-10 -/

/-- `Det-pm`: `sent:det` with `\Future` replaced by `always`. -/
def detPM (p : Atom) : StarFormula := sorry

theorem detPM_of_deterministic {F : TaskFrame} (hD : F.Deterministic) (p : Atom) :
    F.StarValidOn (detPM p) := sorry

theorem deterministic_of_detPM {F : TaskFrame} (h : ∀ p : Atom, F.StarValidOn (detPM p)) :
    F.Deterministic := sorry

/-- **Theorem C, `Det-pm` half**: `Det-pm` defines the deterministic frames. -/
theorem deterministic_starDefinable (F : TaskFrame) :
    (∀ p : Atom, F.StarValidOn (detPM p)) ↔ F.Deterministic := sorry

/-! Phase 11 -/

theorem TaskFrame.saturation_of_fib_finite {D : Type} [AddCommGroup D] [LinearOrder D]
    [IsOrderedAddMonoid D] [Nontrivial D] {W : Type} {R : W → D → W → Prop}
    (h : ∀ w x, (TaskFrame.Fib R w x).Finite) : TaskFrame.Saturation R := sorry

/-! Phase 12 -/

/-- Forward determinism: fibres are subsingletons at nonnegative durations only. Strictly weaker
than `TaskFrame.Deterministic`, and introduced only to name what `sent:det` defines. -/
def TaskFrame.ForwardDeterministic (F : TaskFrame) : Prop := sorry

/-- `F^N`: `W = ℕ`, `D = ℤ`, the absorbing predecessor map. -/
def FN : TaskFrame := sorry

theorem fn_forwardDeterministic : FN.ForwardDeterministic := sorry

theorem fn_not_deterministic : ¬ FN.Deterministic := sorry

/-! Phase 13 -/

/-- **Corrected 2026-09-08.** This line originally pinned the *schematic* statement
`fn_sentDet (φ : StarFormula) : FN.StarValidOn (sentDet φ)`. That statement is **false**, and its
refutation is now in the tree: `fn_refutes_sentDet_somePast` exhibits a `StarFormula` instance
(`P p`) of `sent:det` that fails over `F^N`, and `not_forall_fn_sentDet` reads that off as the
negation of the schematic form (both in
`FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`). The reason: forward
determinism constrains the future and says nothing about the past, so a past-looking instance
distinguishes two possible worlds of the same stability class at a *future* time. The
sentence-letter form pinned below is what the ground-truth source actually claims — PossibleWorlds
task 105 report 02 §3.2's Theorem A runs the singleton valuation `|p| = {τ(y)}`, so its statement
is at the sentence-letter level throughout. The plan generalised it one step too far; nothing in
the source is contradicted. See Phase 13's `#### Reasoned Exclusions` table. -/
theorem fn_sentDet_atom (p : Atom) : FN.StarValidOn (sentDet (StarFormula.atom p)) := sorry

end FormalSystem.Semantics
```

```lean
import FormalSystem.Metalogic.Independence.DriftFrame
import FormalSystem.Metalogic.Independence.RealTranslationFrame

namespace FormalSystem.Metalogic.Independence

open FormalSystem.Semantics

/-! Phase 8 — the discrimination footnote. Stated against the Phase 5 carriers, which the
snapshot module above declares. -/

theorem fzero_refutes_sentDet (p : Atom) : ¬ F0.StarValidOn (sentDet (sorry : StarFormula)) :=
  sorry

theorem f1_sentDet (φ : StarFormula) : F1.StarValidOn (sentDet φ) := sorry

end FormalSystem.Metalogic.Independence
```

**Note on this section's fidelity.** Two declarations above carry a `sorry` in *statement*
position rather than only in body position: `sentDet_unfold`'s disjunction argument and
`fzero_refutes_sentDet`'s atom, both of which mention `StarFormula` constructors that do not exist
until Phase 2 lands. They are pinned here at the granularity the section supports; the
implementer fixes the real statements in Phases 5 and 8 and must record any divergence from the
shapes above in the phase's own docstring.

## Testing & Validation

- [ ] `lake build` green after every phase, with no new `sorry` anywhere under `FormalSystem/`
- [ ] `bash scripts/check-module-invariants.sh` reports C2, C3 and C14 pass after Phase 14
- [ ] C15, C24 and C26 also pass — the plan adds new paper anchors, new modules and new `def`
      names, so all three are in scope even though the dispatch names only C2/C3/C14
- [ ] `bash scripts/check-task-references.sh` clean (no task numbers under `FormalSystem/`)
- [ ] `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/` returns nothing (the
      component's module invariant)
- [ ] `git diff FormalSystem/Semantics/PlusDeterminism.lean` is empty across the whole task —
      the (⇒) half's choice-free pin is untouched
- [ ] No declaration anywhere states `determined_of_deterministic` or any of its relatives as a
      biconditional
- [ ] Every `#print axioms` figure asserted in a new docstring matches the value actually reported

## Artifacts & Outputs

New Lean modules:
- `FormalSystem/Semantics/DeterministicBridge.lean`
- `FormalSystem/StarLanguage/Formula.lean`, `FormalSystem/StarLanguage.lean`
- `FormalSystem/Semantics/StarTruth.lean`
- `FormalSystem/Semantics/StarValidity.lean`
- `FormalSystem/Semantics/StarDeterminism.lean`
- `FormalSystem/Semantics/StarNonValidities.lean`
- `FormalSystem/Metalogic/Independence/StarDiscrimination.lean`
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`

Modified Lean modules:
- `FormalSystem/Semantics/TaskFrame.lean` (`saturation_of_fib_finite`)
- `FormalSystem/Semantics/FrameProperty.lean` (`ForwardDeterministic`)
- `FormalSystem/Semantics.lean`, `FormalSystem/Metalogic.lean`, `FormalSystem/FormalSystem.lean`
  (aggregator imports)

Documentation:
- `FormalSystem/StarLanguage/README.md` (new, carrying the paper-label correspondence table)
- `FormalSystem/PlusLanguage/README.md`, `FormalSystem/Semantics/README.md`,
  `FormalSystem/Metalogic/Independence/README.md` (updated)
- `specs/paper-definitions-of-record.md` (one new KNOWN-ANCHORS row, two updated rows)

Task artifacts:
- `specs/561_store_recall_deterministic_frame_characterization/summaries/01_*-summary.md`

## Rollback/Contingency

Every phase is a separate module or a localized append, and every phase commits on green, so
rollback is per-phase `git revert` of that phase's commit. The two edits to pre-existing large
modules (`TaskFrame.lean` in Phase 11, `FrameProperty.lean` in Phase 12) are pure additions plus
one docstring list line each, so reverting them cannot disturb any existing declaration.

If Phase 12's `saturation` obligation resists after Phase 11's helper is in hand, close Phases 12
and 13 `[COMPLETED WITH EXCLUSIONS]` with a `#### Reasoned Exclusions` table naming the
obstruction and its evidence, and record the exclusion in Phase 14's correspondence table — never
discharge it with `sorry`. The same applies to Phase 15, which is optional by construction.

If the whole task must be abandoned mid-flight, the `StarLanguage/` component is removable in one
step: delete the directory, delete the `Star*.lean` modules under `Semantics/` and
`Metalogic/Independence/`, and revert the three aggregator import lines. Phases 1 and 11 are
independently valuable and should be kept even then — the bridge biconditional and the
finite-fibres *Saturation* helper have consumers beyond this task.
