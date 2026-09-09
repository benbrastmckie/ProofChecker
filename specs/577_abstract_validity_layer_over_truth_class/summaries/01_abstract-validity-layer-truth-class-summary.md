# Implementation Summary: Task #577

- **Task**: 577 - Abstract the per-language validity layer over a truth-relation class
- **Status**: [COMPLETED]
- **Started**: 2026-09-09
- **Completed**: 2026-09-09
- **Effort**: ~4 hours
- **Dependencies**: 576 (completed; the enumeration was taken against the post-576 tree at `f5f1c9345`)
- **Artifacts**: plans/01_abstract-validity-layer-truth-class.md, probes/04_scope-enumeration.txt, probes/axiom-parity.lean, probes/04_axiom-baseline.txt, probes/04_axiom-parity-result.txt
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

Two new leaf modules now carry, written once, the layers that four object languages each paid for
separately: `Semantics/ValidityLayer.lean` (the class `PointTruth`, abstracting truth at a point
`(M, τ, x)`, with `def:frame-validity` and its whole adapter family stated against it) and
`Semantics/TruthClauses.lean` (one class per primitive operator over an environment-carrying
truth relation, with the derived operators and their characterization lemmas proved once, tiered
by which primitives a language has). All four languages instantiate both; **77 per-language proof
bodies became one-line delegations**, and not one declaration was renamed, restated or removed.

The task's hard gating question — whether one abstraction covers both point shapes, `(τ, x)` for
L/L⁻/L⁺ and `(τ, x, v⃗)` for L⋆ — is settled **affirmatively, by `rfl` against the unmodified L⋆
definitions**, not by argument. The honest boundary is a single criterion, and it is stated in
both modules' extension contracts.

## What Changed

### New modules

- `FormalSystem/Semantics/ValidityLayer.lean` (315 lines) — `class PointTruth` (one field, `sat`);
  4 generic `def`s (`TaskFrame.GenericValidOn`, `GenericValidOnFrames`, `GenericValidIn`,
  `GenericValid`); 14 generic theorems (`genericValidOn_iff_total`, two `mono`, the eight
  binder-shape adapters, the three `of_not` contrapositives). Carries the validity-layer
  extension contract.
- `FormalSystem/Semantics/TruthClauses.lean` (590 lines) — `class TruthEnv` (the pointed relation
  with an inert `Env` parameter); 8 operator classes (`BotClause`, `ImpClause`, `BoxClause`,
  `UntlClause`, `SnceClause`, `StabClause`, `AllFutureClause`, `AllPastClause`) and 4 capability
  bundles (`BoolClauses`, `UntlClauses`, `TenseClauses`, `StabClauses`); 14 derived-operator
  `abbrev`s; 14 generic clause lemmas. Carries the clause-layer extension contract.
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` (319 lines) — 56 `:= rfl` coincidences
  (16 validity, 40 derived-operator) plus a toy fifth language with 15 inherited-name examples.

### Instantiated, statements untouched

| File | Instances added | Proof bodies delegated |
|------|-----------------|------------------------|
| `Semantics/Validity.lean` | `PointTruth Formula` | 12 |
| `Semantics/MinusValidity.lean` | `PointTruth MinusFormula` | 8 |
| `Semantics/PlusValidity.lean` | `PointTruth PlusFormula` | 8 |
| `Semantics/StarValidity.lean` | `PointTruth StarFormula` (the `∀ v` fold) | 10 |
| `Semantics/Truth.lean` | `TruthEnv Formula`, `UntlClauses Formula` | 10 |
| `Semantics/MinusTruth.lean` | `TruthEnv MinusFormula`, `TenseClauses MinusFormula` | 8 |
| `Semantics/PlusTruth.lean` | `TruthEnv PlusFormula`, `StabClauses PlusFormula` | 10 |
| `Semantics/StarTruth.lean` | `TruthEnv StarFormula`, `StabClauses StarFormula` | 11 |
| | **12 instances** | **77 bodies** |

Also: `FormalSystem/Semantics.lean` (2 imports + 2 docstring entries),
`FormalSystem/Semantics/README.md` and `Tests/BimodalTest/Semantics/README.md` (one row each),
`Tests/BimodalTest.lean` (1 import), and the generated inventory blocks in `README.md` /
`FormalSystem/README.md`.

### Deliverable 1 — the measured scope

Measured by a comment-aware declaration walker over the eight truth/validity modules, not
surveyed. Full listing with `file:line` anchors and attributes in `probes/04_scope-enumeration.txt`.

| Category | Measured | Report's survey | What it is |
|----------|----------|-----------------|------------|
| A — validity layer | **65** | 64 | 16 `def`s + 11 frame-class tag `def`s + **38 theorems** (the delegated ones) |
| B — derived-clause layer | **39** | 37 | the language-agnostic clause lemmas (**39 delegated**) |
| C — primitive clause lemmas | **22** | 28 | the shared-operator clause restatements; these become instance payload |
| D — genuinely language-specific | **116** | 113 | everything else |
| **Total** | **242** | 242 | |

Three corrections to the research survey, each recorded in the enumeration file's header:
`MinusValidZTimeSucc` was missing from the tag-`def` count (A: 64→65); L⁻'s two conditional
existential-tense lemmas are in scope and did in fact delegate (B: 37→39); and six clause lemmas
for **non-shared** constructors (`Truth.atom_iff_of_domain`, `Truth.atom_false_of_not_domain`,
`PlusTruth.atom_iff`, `StarTruth.atom_iff`, `StarTruth.timeStore_iff`, `StarTruth.timeRecall_iff`)
cannot be payload of a shared operator class and are reclassified to D (C: 28→22, D: 113→116).

### Deliverable 2 — one abstraction, both point shapes: settled by proof

The L⋆ instance folds the stored-time vector into the point predicate:

```lean
instance : PointTruth StarFormula where
  sat {F} M τ t φ := ∀ v : ℕ → F.Duration, StarTruthAt M τ t v φ
```

This is statement-preserving because `v` is the **innermost** binder of every L⋆ validity
definition, and a `Pi` telescope `∀ M τ x v, …` is literally `∀ M τ x, (∀ v, …)`. The evidence is
four `rfl`s against the *unmodified* L⋆ definitions, now permanent tests:

```lean
example : TaskFrame.StarValidOn F φ = TaskFrame.GenericValidOn F φ := rfl
example : StarValidOnFrames P φ = GenericValidOnFrames P φ := rfl
example : StarValidIn fc φ = GenericValidIn fc φ := rfl
example : StarValid φ = GenericValid φ := rfl
```

All four close by bare `rfl`, with no `show` and no `change`. On the clause side the same fact
appears as `Env F := ℕ → F.Duration` with all six shared clause fields discharged by `Iff.rfl`.
**The plan's "cannot cover both" branch did not fire.**

### Deliverable 6 — the extension contract

Written into both modules' `## Design Invariants` sections **from the instantiations actually
performed**, each claim citing the instance it is drawn from. In brief, a fifth language supplies:

1. one `PointTruth` instance with one field (`sat`), `∀`-closed over any extra per-point
   parameters — and inherits all 18 validity-layer names;
2. one `TruthEnv` instance (`Env` = the extra-parameter type, or `PUnit`) plus one bundle
   instance whose clause fields are all `Iff.rfl`/`fun h => h` — and inherits the tier its
   primitives earn.

Two obligations bind an extra parameter, both exercised by L⋆ and both stated as obligations
rather than observations: **O1** it must be the innermost binder of the language's own `ValidOn`
and every adapter (this is what makes the fold statement-preserving, and it is what the `rfl`
above checks); **O2** it must thread unchanged through every *shared* operator clause.

## Decisions

- **`def` bodies are never replaced — only `theorem` bodies.** Each language's four validity
  `def`s keep their bodies and their reducibility. `Valid` alone has ~787 occurrences; replacing
  its body or promoting it to `abbrev` would change `unfold`/`simp` behaviour at every one. Confining
  delegation to proof-irrelevant declarations is precisely why no downstream file needed editing.
- **`Generic` prefix, not a nested `PointTruth` namespace.** A bare `Valid`/`ValidIn`/
  `ValidOnFrames` inside a namespace nested under `FormalSystem.Semantics` is a C23 failure
  (outer-shadows-inner bare-declaration pair). The generic notions are top-level with the
  `Generic` prefix, mirroring the tree's own `Minus`/`Plus`/`Star` convention.
- **`StabClause` carries the same-state relation as a field.** `SameStateAt` lives in
  `PlusTruth.lean`, above `TruthClauses.lean` in the import order, so naming it directly would be
  a cycle. Each instance supplies it, so `PlusTruth.dstab_iff` and `StarTruth.dstab_iff` keep
  their statements verbatim. Nothing was relocated.
- **Bundles for instances, fine-grained classes for lemmas.** Each generic lemma names exactly the
  operator classes its proof consumes; the four `extends` bundles exist only so a language
  declares one instance instead of six. Stating a lemma against a bundle would force a fifth
  language to supply operators the lemma does not need.
- **Classical discipline in `neg_iff`/`top_true`.** Both are `[propext]` in all four languages;
  proving them generically by `rw` plus explicit terms, never `by_contra`/`push Not`, is what kept
  every wrapper's axiom set from drifting.

## Plan Deviations

- **Phase 5** altered: the generic lemmas' instance-binder lists were narrowed, by a finer
  `section` split, to exactly the classes each proof consumes — where the plan's
  `## Lean Challenge Statements` block carried wider `variable` lists (e.g. `[BoxClause L]` on
  `neg_iff`). Lean's `unusedSectionVars` linter flags the wider form, and a wider list would force
  a fifth language to supply operators a lemma does not use. Each new generic lemma is thereby
  **strictly stronger**, and no pre-existing declaration is affected. The `extends` bundles the
  plan names were built as specified and are in use.
- **Phase 5** altered: the plan's `always'`/`someFuture'`/`somePast'` tense-primitive operators
  landed under those exact names, but split across three `section`s (`TenseFuture`, `TensePast`,
  `TenseAlways`) for the same binder-narrowing reason.
- **Phase 10** altered: the toy fifth language lives in namespace `FifthLanguage` rather than
  `Toy`, because `namespace Toy` + `inductive Toy` trips the `dupNamespace` linter that C16 gates.
- **One downstream file was edited — comments only.** Adding
  `import FormalSystem.Semantics.TruthClauses` to `Semantics/Truth.lean` shifted its line
  numbering by one, which invalidated two `Semantics/Truth.lean:134-135` line-number citations in
  `Metalogic/Decidability/Tableau.lean` comments (`check-module-invariants.sh` C20 tier 1). They
  were repaired to the durable anchor "`TruthAt`'s `untl` clause in `Semantics/Truth.lean`",
  which is the repair C20 itself prescribes. **No statement, proof, definition or code changed in
  that file.** This is flagged because the task said no downstream consumer may require editing:
  the constraint held for every consumer of a delegated declaration, and this is a line-number
  comment citation that any new module in `Semantics/` would have invalidated identically.

## Verification

- Build: **Success** — full `lake build` green (guarded, detached).
- Tests: **Passed** — `lake build BimodalTest` green, including all 56 `rfl` coincidences and the
  toy fifth-language conformance section.
- Sorry count: **0** in every touched and new module (repo-wide `sorry` occurrences remain
  confined to the pre-existing `FormalSystem/Boneyard/`).
- Vacuous count: **0** — no `:= True`/`Unit`/`trivial` placeholder anywhere.
- Axiom count: **unchanged, 14 → 14** (`grep -c '^axiom ' FormalSystem/`).
- `scripts/check-module-invariants.sh`: **exit 0, ALL CHECKS PASSED**, including C2 (all four
  flagship axiom sets match baseline), C14 (every pinned declaration matches its axiom baseline),
  C16 (simpNF/docBlame/dupNamespace clean), C19 (docstring coverage 92.19%, floor 90%), C23
  (no outer-shadows-inner bare-declaration pair — the `Generic` prefix decision holds), C24, C26.
- **Axiom parity across all 77 delegated names**: *no name gained an axiom.* Four names lost one —
  `PlusTruth`/`StarTruth`'s `someFuture_iff` and `somePast_iff` went `[propext, Quot.sound]` →
  `[propext]`, because the generic proof discharges the `⊤` guard through `top_true` where the
  originals reached for `simp`. L's own `some_future_iff`/`some_past_iff` were already `[propext]`,
  so the generic lemma matches the tighter of the two pre-existing proofs. Fewer axioms is a
  strictly stronger result and no repo baseline moved. Full record in
  `probes/04_axiom-parity-result.txt`; `probes/04_axiom-baseline.txt` is deliberately left as the
  pre-refactor capture.
- **Deliverable 4 verified mechanically**: a declaration-header diff of all eight touched files
  against `f5f1c9345` reports **0 changed and 0 lost signatures**; the only additions are the 12
  new instances. The four truth recursions (`TruthAt`, `MinusTruthAt`, `PlusTruthAt`,
  `StarTruthAt`) are byte-identical. Attribute counts unchanged (L's `@[simp, truth_norm]` still
  10, L⁻'s `@[simp]` still 8).
- **242/242 enumerated declarations still resolve** (`#check @...` over the whole enumeration).
- Files verified: Yes.

## Impacts

- A fifth object language now pays **one `PointTruth` instance and one clause bundle instance**
  for the whole validity layer and the derived-operator clause family, instead of ~19 hand-written
  theorem bodies. That is the deliverable the refactor exists to buy, and the contract stating it
  is written from four real instantiations rather than aspirationally.
- The separation between the four formula inductives is **untouched**: the class abstracts the
  truth *relation*, exposes no recursor, and never relates the types. `StarLanguage/README.md`'s
  reason for separate types is unaffected, and `stab_state_only` and the atomization route it
  guards are not in scope of the abstraction.
- Deferred item **D1** (a predicate-level schema-soundness library) can now be written against one
  truth-relation class instead of four separate validity layers, which was the stated reason for
  sequencing it after this task.
- The 56 `rfl` tests are a standing regression guard: any future edit that makes a per-language
  validity notion or derived operator diverge from the generic one turns the test build red
  instead of silently forking the two layers.

## Follow-ups

- **The consequence layer is out of scope but would instantiate cleanly.**
  `ConsequenceOnFrames`/`SemanticConsequenceIn`/`SemanticConsequence`,
  `MinusSemanticConsequence`, the `SetConsequenceOnFrames` pair, and
  `Metalogic/Deterministic/Validity.lean`'s six adapters all fit `PointTruth` as it stands, but
  live under `Metalogic/**`, outside this task's stated territory. Worth a follow-up task.
- **`Metalogic/Independence/CoarsenedModels.lean`'s `CTruth.*`** is a fifth clause-family
  duplicate; same reason for exclusion, same recommendation.
- **`MinusFrameTruth`** (`Semantics/MinusFrame.lean`) sits outside for a structural reason rather
  than a territorial one: it is not `TaskFrame`-pointed, and this class is. Abstracting over the
  frame notion as well would be a distinct, larger piece of work.
- L's collected `Truth.always_iff` (`∀ s` form) stays L-only by design: collapsing the three
  strict cases needs the frame's trichotomy, which no generic lemma has. Only the tri form is
  generic.

## References

- `specs/577_abstract_validity_layer_over_truth_class/plans/01_abstract-validity-layer-truth-class.md`
- `specs/577_abstract_validity_layer_over_truth_class/reports/01_abstract-validity-layer-truth-class.md`
- `specs/577_abstract_validity_layer_over_truth_class/probes/04_scope-enumeration.txt` — deliverable 1
- `specs/577_abstract_validity_layer_over_truth_class/probes/04_axiom-baseline.txt`,
  `probes/axiom-parity.lean`, `probes/04_axiom-parity-result.txt` — the axiom-parity gate
- `FormalSystem/Semantics/ValidityLayer.lean`, `FormalSystem/Semantics/TruthClauses.lean` —
  the two extension contracts
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` — the `rfl` coincidences and the toy
  fifth-language conformance check
