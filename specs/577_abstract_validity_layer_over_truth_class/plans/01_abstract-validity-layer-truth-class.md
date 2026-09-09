# Implementation Plan: Task #577

- **Task**: 577 - Abstract the per-language validity layer over a truth-relation class
- **Status**: [IMPLEMENTING]
- **Effort**: 16 hours
- **Dependencies**: 576 (completed; the enumeration in the research report was taken against the post-576 tree at HEAD `e3a2c0f1a`)
- **Research Inputs**: specs/577_abstract_validity_layer_over_truth_class/reports/01_abstract-validity-layer-truth-class.md (plus the three compiled probes under `specs/577_abstract_validity_layer_over_truth_class/probes/`)
- **Artifacts**: plans/01_abstract-validity-layer-truth-class.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Land two new leaf modules -- `FormalSystem/Semantics/ValidityLayer.lean` (a class `PointTruth L`
abstracting "truth at a point `(M, τ, t)`", with the validity layer written once against it) and
`FormalSystem/Semantics/TruthClauses.lean` (operator/clause classes with an inert `Env` parameter,
with the derived-operator family and its truth lemmas written once) -- then instantiate each per
language, one language per phase, turning every duplicated per-language proof body into a
one-line delegation while leaving every per-language *name*, *statement*, *attribute set* and
`def` body byte-identical. The design is settled by the research round's three compiled probes:
one abstraction covers both point shapes because L⋆'s stored-time vector `v` is the innermost
binder everywhere, so `∀ v` folds into `sat` without touching any binder telescope. Definition of
done: `lake build` and `lake build BimodalTest` green, zero `sorry`, `scripts/check-module-invariants.sh`
exit 0 with every axiom baseline unchanged, no downstream file edited, and an extension contract
in the new modules' docstrings written from the four instantiations actually performed.

### Research Integration

Integrated from `reports/01_abstract-validity-layer-truth-class.md`:

- **Deliverable 1 (scope) is measured, not surveyed**: the territory holds 1058 declarations (not
  "roughly 658"); the eight truth/validity files hold 242, of which 64 are language-agnostic
  validity-layer declarations, 37 are language-agnostic derived-clause lemmas, 28 are primitive
  clause lemmas that become instance payload, and 113 are genuinely language-specific. Phase 1
  re-derives this list explicitly (Scope Hypothesis) and it becomes the axiom-parity list.
- **Deliverable 2 (both point shapes) is settled affirmatively by `rfl`** against the unmodified
  live definitions (probe 1: `TaskFrame.StarValidOn F φ = <generic> F φ := rfl`). Not re-derived
  here; the plan's Phase 4 reproduces the load-bearing identity as a permanent test.
- **The honest boundary is one criterion**: the class abstracts the truth *relation*, not the
  inductive *type*, so it exposes no recursor; anything proved by `induction φ` stays
  per-language. That covers `timeShift` (3 declarations, 2 statements, 3 proof routes, absent in
  L⁻), `truth_congr_ext`, `stab_state_only`, the `ofPlus`/`ofFormula` bridges, the `StateLocal`
  families, and `SameStateAt`. `MinusFrameTruth` (a non-`TaskFrame` frame notion) and
  `Metalogic/Independence/CoarsenedModels.lean`'s `CTruth.*` family sit outside for a second
  reason: the class is `TaskFrame`-pointed. None of these is a defect.
- **Survey corrections adopted**: `swapTemporal` (syntax `def`), `interpolates` (a frame
  property), and `sometimes` (no truth lemma anywhere) are struck from scope.
- **Axiom parity is a measured hazard**: probe 3 shows all eleven checked pairs identical
  *because* the generic `neg_iff` avoids `by_contra`/`push_neg`; a generic proof that reaches for
  classical tactics where the original did not drifts a baseline. This plan makes a per-name
  `#print axioms` diff a gate of every instantiation phase (Phase 1 captures the baseline).
- **cslib precedent adopted**: one class per operator bundled by `extends` (handles L⁻'s
  `allPast`/`allFuture`-primitive divergence without a second monolithic class); `abbrev` for the
  *new* generic derived operators only; `protected`/`section`-scoped capability groups; a
  `## Design Invariants` docstring section as the home of the extension contract. **Rejected with
  reason**: cslib's Representation A (changes elimination forms downstream -- 577's forbidden
  outcome); `def`→`abbrev` promotion of the four existing per-language validity `def`s (`Valid`
  alone has 787 occurrences; reducibility change would alter `simp`/`unfold` tree-wide); the
  bundled-`Judgement`/`Point` trick (changes `TaskFrame.ValidOn`'s binder shape).

### Planning-time findings not in the report

Two facts surfaced while grounding the plan against the harness, and both change what the
implementer must do relative to the probes:

1. **C23 forbids the probes' generic naming.** `scripts/check-module-invariants.sh` C23 (the
   "outer-shadows-inner bare-declaration pair" assertion) records every *bare* (undotted)
   declaration with its namespace stack and fails when the same bare name appears in a namespace
   nested under another that also declares it. L's `Valid`, `ValidIn` and `ValidOnFrames` are
   bare in `FormalSystem.Semantics` (`Semantics/Validity.lean:359,370,408`), so a generic
   `def ValidIn` inside `namespace PointTruth` (nested under `FormalSystem.Semantics`) is a
   C23 failure. Census of every candidate generic name against the walker: **only these three
   collide**. Every clause-lemma name (`neg_iff`, `and_iff`, ..., `always_iff_tri`) lives in a
   sibling namespace (`Semantics.Truth`, `.MinusTruth`, `.PlusTruth`, `.StarTruth`,
   `.MinusFrameTruth`, `Metalogic.Independence.CTruth`), which C23 does not relate, and every
   derived-operator name (`neg`, `and`, ...) lives under `Syntax.Formula` and the three language
   `Formula` namespaces, also siblings. Wrapper theorems (`ValidIn.mono`) are dot-qualified and
   are never recorded. **Decision**: the generic validity notions are top-level in
   `FormalSystem.Semantics` with a `Generic` prefix, mirroring the tree's own
   `Minus`/`Plus`/`Star` prefix convention one-for-one (`TaskFrame.GenericValidOn`,
   `GenericValidOnFrames`, `GenericValidIn`, `GenericValid`, `GenericValidIn.mono`, ...); the
   class keeps the descriptive name `PointTruth`. The generic clause layer lives in
   `namespace TruthClauses` (a sibling of `Truth`), never bare in `FormalSystem.Semantics`. The
   implementer may pick a different prefix, but MUST NOT place a bare `Valid`/`ValidIn`/
   `ValidOnFrames` in any namespace nested under `FormalSystem.Semantics`, and MUST NOT evade
   the walker by writing dot-qualified `PointTruth.ValidIn` -- that reproduces the genuine
   bare-reference ambiguity C23 exists to prevent.
2. **The challenge-snapshot tool pins only `def`/`theorem`/`instance`.** `class` and `abbrev`
   declarations pass through `lean-challenge-snapshot.sh` unpinned, so the Goals list below
   names the generic `def`s and `theorem`s only; the classes and `abbrev`s are recorded as
   non-declaration outcomes, as the task 576 plan did for constructors.

Also confirmed at planning time: `Semantics/FrameClassValidity.lean` imports only `FrameProperty`
and `ProofSystem.Axioms`, so a leaf `ValidityLayer.lean` importing `TaskModel`, `ConvexHistory`
and `FrameClassValidity` sits below `Validity.lean` with no cycle; `FormalSystem/Semantics.lean`
is the aggregator both new modules must join (C8/C6); `FormalSystem/Semantics/README.md` carries
a per-module table that must gain two rows (C5/C12); `Tests/BimodalTest.lean` is the test root a
new test module registers in (C4); and `lean-lsp` MCP is unavailable (wrapper script missing), so
every phase verifies by compilation through `.claude/scripts/lake-build-guard.sh`, exactly as the
research round did.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as roadmap context for this dispatch and does not
list this task. Its near-term directive (2026-09-08: foundations and small, bounded results only)
is consistent with a statement-preserving refactor. No ROADMAP.md edits are made by this plan.

## Goals & Non-Goals

**Goals**:
- `TaskFrame.GenericValidOn`
- `GenericValidOnFrames`
- `GenericValidIn`
- `GenericValid`
- `genericValidOn_iff_total`
- `GenericValidOnFrames.mono`
- `GenericValidIn.mono`
- `TaskFrame.GenericValidOn.of_forall_total`
- `TaskFrame.GenericValidOn.apply_total`
- `GenericValidOnFrames.of_forall_total`
- `GenericValidOnFrames.apply_total`
- `GenericValidIn.of_forall_total`
- `GenericValidIn.apply_total`
- `GenericValid.of_forall_total`
- `GenericValid.apply`
- `GenericValidOnFrames.of_not`
- `GenericValidIn.of_not`
- `GenericValid.of_not`
- `TruthClauses.neg_iff`
- `TruthClauses.top_true`
- `TruthClauses.and_iff`
- `TruthClauses.or_iff`
- `TruthClauses.diamond_iff`
- `TruthClauses.someFuture_iff`
- `TruthClauses.somePast_iff`
- `TruthClauses.allFuture_iff`
- `TruthClauses.allPast_iff`
- `TruthClauses.always_iff_tri`
- `TruthClauses.dstab_iff`
- `TruthClauses.someFuture_iff_of_allFuture`
- `TruthClauses.somePast_iff_of_allPast`
- `TruthClauses.always_iff_of_tense`

**Goals** -- non-declaration outcomes:
- `class PointTruth (L : Type)` with the single field `sat`, instantiated for `Formula`,
  `MinusFormula`, `PlusFormula` and (with the `∀ v` fold) `StarFormula`.
- The clause classes: a base `TruthEnv L` (fields `Env : TaskFrame → Type` and the pointed truth
  relation `T`), one class per primitive operator bundling the operator with its truth clause
  (`BotClause`, `ImpClause`, `BoxClause`, `UntlClause`, `SnceClause`, `StabClause`,
  `AllFutureClause`, `AllPastClause`), and the bundles by `extends` (`BoolClauses`,
  `UntlClauses`, `TenseClauses`, `StabClauses`); instantiated for all four languages, L⁻ via the
  tense-primitive bundle.
- The generic derived operators as `abbrev`s under `TruthClauses` (`neg`, `top`, `and`, `or`,
  `diamond`, `someFuture`, `somePast`, `allFuture`, `allPast`, `always`, `dstab`, plus the
  tense-primitive `someFuture`/`somePast`), each coinciding with its per-language `def` by `rfl`.
- 38 validity-layer and 37 (+2 conditional) clause-layer per-language theorem bodies replaced by
  one-line delegations, with statements, attributes and names byte-identical.
- An extension contract in both modules' `## Design Invariants` docstring sections, written from
  the instantiations performed.
- A test module `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` pinning every `rfl`
  coincidence and a toy fifth-language conformance check.

**Non-Goals**:
- Merging, unifying or weakening the separation between the four formula inductives
  (`StarLanguage/README.md`, "Why the operators are not added to PlusFormula") -- not touched.
- Changing any theorem statement, renaming any declaration, promoting any existing `def` to
  `abbrev`, or editing any file outside the eight truth/validity modules, the two new modules,
  the aggregator, the README rows and the test tree.
- Abstracting anything proved by induction on a formula type: `timeShift_preserves_truth`,
  `plusTruthAt_timeShift`, `starTruthAt_timeShift`, `truth_congr_ext`/`star_truth_congr_ext`,
  `stab_state_only`, `plusTruthAt_ofFormula`, `starTruthAt_ofPlus`, `starValidOn_ofPlus`,
  `starValidOnFrames_ofPlus`, `PlusStateLocal`/`StarStateLocal`, `SameStateAt`.
- L's collected `Truth.always_iff` (`∀ s` form, `@[simp, truth_norm]`): stays L-only; only the
  tri form is generic.
- The consequence layer (`ConsequenceOnFrames`/`SemanticConsequenceIn`/`SemanticConsequence`,
  `MinusSemanticConsequence`, `SetConsequenceOnFrames`/`MinusSetConsequenceOnFrames`) and
  `Metalogic/Deterministic/Validity.lean`'s six `of_forall_total`/`apply_total` adapters. Both
  would instantiate against `PointTruth`, but `Metalogic/**` is outside this task's stated
  territory. Recommend a follow-up task; likewise for `CTruth.*` in
  `Metalogic/Independence/CoarsenedModels.lean`, a fifth clause-family duplicate.
- Restoring `.claude/scripts/lean-lsp-mcp-wrapper.sh` (report's context recommendation; not a
  blocker -- compile-probe verification is stronger).
- Adding a cslib dependency or copying cslib code.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A generic proof uses `by_contra`/`push_neg`/`simp` where the original used `rw`+terms, drifting a wrapper's axiom set from `[propext]` to `[propext, Classical.choice, Quot.sound]` | H | M | Phase 1 captures `#print axioms` for every wrapper-candidate name into `probes/04_axiom-baseline.txt`; every instantiation phase re-runs the same probe and diffs to zero. Phase 5 additionally checks each generic lemma's own set is a subset of the intersection of its wrappers' baselines. Drift is a defect to fix in the generic proof, never a rebaseline. |
| C23 failure from a bare generic namesake in a nested namespace (see Planning-time findings) | H | H if the probe naming is copied | The `Generic` prefix decision above; `check-module-invariants.sh` runs in Phase 1 before any instance exists, so a naming violation surfaces with zero blast radius. |
| Elaboration-order failures in wrapper bodies (`?inst` metavariable: unifier cannot invert `StarValidOnFrames P φ ≟ GenericValidOnFrames (L := ?) ?φ`) | M | H | Known and solved in probe 1: named arguments `(L := StarFormula) (φ := φ)` in the *proof body*; never touches a statement. |
| `PUnit` or `Env` leaking into a preserved statement | H | L | Wrappers restate the live statement verbatim and discharge `e := PUnit.unit` inside the proof; a diff of every wrapper's signature against `git show HEAD:<file>` is a per-phase task. |
| A derived-operator `rfl` bridge fails because a per-language `def` is not textually the Lukasiewicz/untl encoding the generic `abbrev` uses | M | L | Report verified all four languages' `neg`/`top`/`and`/`or`/`diamond` character-identical and `always` identically associated; `MinusFormula.someFuture := (φ.neg.allFuture).neg` matches the tense-primitive generic. If a bridge still fails for one operator, leave that wrapper's body as it stands and record a Reasoned Exclusion with the failing `rfl` as evidence -- never edit the syntax `def`. |
| Fine-grained operator classes (one per operator, bundled by `extends`) produce instance diamonds or non-`rfl` projections that the probe's coarse `BoolCore`/`UntlCore`/`StabCore` chain did not | M | M | Phase 5 builds the fine grain first; if `rfl` bridges or instance resolution fail after one honest attempt, fall back to the probe's coarse chain (proven green) plus a separate small tense-primitive class for L⁻, and record the fallback in the module docstring. |
| Tagging a generic lemma `@[simp]` changes downstream simp sets; tagging both L `always` forms strands proofs (`Truth.lean` docstring) | H | L | Generic lemmas carry NO attributes; wrappers keep exactly the attributes they have today (`@[simp, truth_norm]` on L, `@[simp]` on L⁻, `@[simp]` on `bot_false` only for L⁺/L⋆). C16 simpNF is a per-phase gate. |
| Adding `[LinearOrder F.Duration]` as a binder for a generic trichotomy proof hits an instance-diamond mismatch against `instDistribLatticeOfLinearOrder` (report, tactic table) | M | L | The collected `always_iff` is L-only and stays out of the generic layer; no generic lemma needs trichotomy. |
| Long builds livelock a foreground call | M | H | Every build goes through `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build <target>` under `Bash(run_in_background: true)` per `context/project/lean4/operations/long-builds.md`. |
| Private helper lemmas orphaned by body replacement trip C17 (reporting-only) or docBlame | L | M | Each instantiation phase removes `private` declarations that its body replacements orphaned (they are not public names); non-private names are never removed. |
| A downstream file turns red after a body replacement | H | L | Impossible in principle for a `theorem` (proof-irrelevant, statement unchanged); would signal a statement moved -- revert the substep, do not edit the consumer. The four per-language validity `def` bodies are never replaced (Decision 2 of the report), so no `unfold`/`simp [Valid]` site can change. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 5 | -- |
| 2 | 2, 3, 4, 6, 7, 8, 9 | 1, 5 |
| 3 | 10 | 2, 3, 4, 6, 7, 8, 9 |

Phases within the same wave can execute in parallel. The wave-2 phases are file-disjoint, but
every phase runs `lake build` on the same package, so in a single worktree they serialize; the
recommended dispatch order is numeric (L first as the template, L⋆ last as the divergent shape).
Phases 6-9 depend on Phase 1 only for the test module it creates.

Every phase closes with the same gate set, restated once here rather than in each phase:
(G1) `lake build` green via the build guard; (G2) `lake build BimodalTest` green; (G3) zero
`sorry` introduced (`grep -rn "sorry" <touched files>` unchanged); (G4) axiom-parity diff empty
for every name on `probes/04_scope-enumeration.txt` (from Phase 2 on); (G5)
`bash scripts/check-module-invariants.sh` exit 0; (G6) no file outside the phase's declared file
list modified (`git status --short`). Each green substep is committed as
`task 577 phase {P}.{O}: ...` per the Commit-Per-Green-Substep mandate.

### Phase 1: `Semantics/ValidityLayer.lean` -- the truth class and the generic validity layer, with the scope enumeration and axiom baseline [COMPLETED]

**Goal**: Land the leaf module holding `PointTruth` and the validity layer written once, with no
instances yet (zero blast radius), and freeze the measurement that gates everything after it: the
explicit list of every declaration the abstraction covers and its current axiom set.

**Tasks**:
- [ ] Enumerate, by reading the eight files (`Semantics/{Truth,MinusTruth,PlusTruth,StarTruth,Validity,MinusValidity,PlusValidity,StarValidity}.lean`), every declaration in the report's categories A (validity layer, 64), B (derived-clause layer, 37), C (instance payload, 28) and D (language-specific, 113); write the list with its category and file:line anchors to `specs/577_abstract_validity_layer_over_truth_class/probes/04_scope-enumeration.txt`. Correct the report where it is wrong and say so in the file header. This is deliverable 1; its count is reported in the summary.
- [ ] Write `specs/577_abstract_validity_layer_over_truth_class/probes/axiom-parity.lean` importing `FormalSystem.Semantics.StarValidity` and `FormalSystem.Semantics.MinusValidity` and issuing `#print axioms` for every category-A and category-B name (the 101 wrapper candidates, plus `MinusTruth.someFuture_iff`/`somePast_iff`); run it with `lake env lean` (or temporarily inside the package as the research round did, deleting afterwards) and save the output as `probes/04_axiom-baseline.txt`. This runs BEFORE any body changes, so it is the pre-refactor truth.
- [ ] Create `FormalSystem/Semantics/ValidityLayer.lean`: copyright header; imports `FormalSystem.Semantics.TaskModel`, `FormalSystem.Semantics.ConvexHistory`, `FormalSystem.Semantics.FrameClassValidity`; module docstring with `# `, `## Main Definitions`, `## Main Results`, `## Design Invariants` (initial extension-contract wording from the report's draft, explicitly marked as to be re-verified in Phase 10), `## References`, `## Tags`, following `Semantics/StarValidity.lean`'s header shape.
- [ ] `class PointTruth (L : Type) where sat : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → L → Prop` with a docstring stating the `∀`-closure convention for languages with extra per-point parameters.
- [ ] Generic definitions as `def` (never `abbrev`), bodies copied binder-for-binder from `Semantics/Validity.lean:274,359,370,408` with `TruthAt` replaced by `PointTruth.sat`: `TaskFrame.GenericValidOn`, `GenericValidOnFrames`, `GenericValidIn`, `GenericValid`.
- [ ] Generic theorems, statements copied from the L (and, for the `GenericValidOn` pair, the L⋆) originals modulo the predicate: `genericValidOn_iff_total`, `GenericValidOnFrames.mono`, `GenericValidIn.mono`, `TaskFrame.GenericValidOn.{of_forall_total,apply_total}`, `GenericValidOnFrames.{of_forall_total,apply_total}`, `GenericValidIn.{of_forall_total,apply_total}`, `GenericValid.{of_forall_total,apply}`, `{GenericValidOnFrames,GenericValidIn,GenericValid}.of_not`. Proofs are the probe-1 terms; no classical tactics anywhere (`of_not` is `fun hc => h (of_forall_total hc)`).
- [ ] Run `#print axioms` on every generic theorem; each must be a subset of the corresponding L baseline entry (expected: `[propext]` at most, most `[]`).
- [ ] Register the module in `FormalSystem/Semantics.lean` (before `FormalSystem.Semantics.Validity`) and add its row to `FormalSystem/Semantics/README.md`'s module table.
- [ ] Create `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` (imports `FormalSystem.Semantics.ValidityLayer`; a `#check`-level smoke example) and register it in `Tests/BimodalTest.lean`; add its row to `Tests/BimodalTest/Semantics/README.md`.
- [ ] Confirm C24 (`lake exe checkInitImports`) and C19 (every new declaration has a docstring) as part of G5.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: 18 generic declarations (4 `def`s + 14 theorems) cover the 64 category-A
names (38 theorem bodies to delegate later; 16 `def`s and 10 frame-class tag `def`s untouched);
101 (+2) names on the axiom-parity list. Confirm by the enumeration file's per-category counts;
if the report's 64/37/28/113 split is wrong, the file says so and the summary reports the
corrected count.

**Files to modify**:
- `FormalSystem/Semantics/ValidityLayer.lean` - new
- `FormalSystem/Semantics.lean` - add import
- `FormalSystem/Semantics/README.md` - add row
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - new
- `Tests/BimodalTest.lean` - add import
- `Tests/BimodalTest/Semantics/README.md` - add row
- `specs/577_abstract_validity_layer_over_truth_class/probes/{04_scope-enumeration.txt,axiom-parity.lean,04_axiom-baseline.txt}` - new

**Verification**:
- G1, G2, G3, G5, G6; `04_axiom-baseline.txt` exists and lists every name on the enumeration's A and B rows; generic-theorem axiom sets are each `⊆ [propext]`; no `instance` declared in this phase.

---

### Phase 2: Instantiate the validity layer for L (`Semantics/Validity.lean`) [COMPLETED]

**Goal**: Make L the template instantiation: one instance, twelve theorem bodies delegated, every
statement byte-identical, the four validity `def`s and four frame-class tag `def`s untouched.

**Tasks**:
- [ ] Add `import FormalSystem.Semantics.ValidityLayer` to `Semantics/Validity.lean`.
- [ ] Add `instance : PointTruth Formula where sat M τ t φ := TruthAt M τ t φ` immediately before `TaskFrame.ValidOn` (`:274`), with a docstring.
- [ ] Replace the proof bodies -- and nothing else -- of: `validOn_iff_total` (`:290`), `ValidOnFrames.mono` (`:484`), `ValidIn.mono` (`:497`), `ValidOnFrames.of_forall_total` (`:527`), `ValidOnFrames.apply_total` (`:534`), `ValidIn.of_forall_total` (`:540`), `ValidIn.apply_total` (`:547`), `Valid.of_forall_total` (`:419`), `Valid.apply` (`:427`), `ValidOnFrames.of_not` (`:560`), `ValidIn.of_not` (`:572`), `Valid.of_not` (`:436`) with one-line delegations to the `Generic*` theorems, using `(L := Formula) (φ := φ)` named arguments where elaboration needs them. Keep every docstring and attribute.
- [ ] Do NOT touch the bodies of `TaskFrame.ValidOn`, `ValidOnFrames`, `ValidIn`, `Valid`, `ValidDense`, `ValidZTime`, `ValidRTime`, `ValidComplete` (report Decision 2 and 7: reducibility and `unfold`/`simp` behaviour at 787 `Valid` sites must not change).
- [ ] Diff every touched signature against `git show HEAD:FormalSystem/Semantics/Validity.lean` -- the signature lines must be identical.
- [ ] Remove any `private` helper orphaned by the replacements (expected: none).
- [ ] Extend `ValidityLayerTest.lean`: `example (F) (φ : Formula) : TaskFrame.ValidOn F φ = TaskFrame.GenericValidOn F φ := rfl` and the three siblings for `ValidOnFrames`/`ValidIn`/`Valid`.
- [ ] Re-run `probes/axiom-parity.lean`, diff against `04_axiom-baseline.txt`: must be empty.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: exactly 12 L theorem bodies change and 0 signatures change. Confirm with
`git diff --stat` (one file plus the test) and a signature diff.

**Files to modify**:
- `FormalSystem/Semantics/Validity.lean` - instance + 12 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - 4 `rfl` coincidences

**Verification**:
- G1-G6; axiom-parity diff empty; signature diff empty; `git diff` shows no consumer file touched.

---

### Phase 3: Instantiate the validity layer for L⁻ and L⁺ (`Semantics/MinusValidity.lean`, `Semantics/PlusValidity.lean`) [COMPLETED]

**Goal**: Repeat the L template for the two `(τ, x)`-pointed languages whose files mirror
`Validity.lean` binder-for-binder.

**Tasks**:
- [ ] `MinusValidity.lean`: `instance : PointTruth MinusFormula where sat M τ t φ := MinusTruthAt M τ t φ`; delegate the 8 category-A theorem bodies (`MinusValidOnFrames.mono`, `MinusValidIn.mono`, the six `of_forall_total`/`apply_total` adapters); leave `TaskFrame.MinusValidOn`, `MinusValidOnFrames`, `MinusValidIn`, `MinusValid`, `MinusValidDense`, `MinusValidZTime`, `MinusValidRTime` bodies untouched.
- [ ] `PlusValidity.lean`: `instance : PointTruth PlusFormula where sat M τ t φ := PlusTruthAt M τ t φ`; delegate the 8 category-A theorem bodies (`PlusValidOnFrames.mono`, `PlusValidIn.mono`, six adapters); leave the four `def`s and three tag `def`s untouched.
- [ ] Note the report's binder-convention finding: these files may declare `M τ t` via `variable` blocks; the wrapper statement is whatever the file has today -- copy nothing from L.
- [ ] Signature diff against `HEAD` for both files; orphaned-`private` sweep.
- [ ] Extend the test module with the 8 `rfl` coincidences (4 per language).
- [ ] Axiom-parity diff empty.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: 8 + 8 theorem bodies, 0 signatures. Confirm as in Phase 2; if a file has
an adapter the enumeration missed, add it to `04_scope-enumeration.txt` and the parity list
rather than skipping it silently.

**Files to modify**:
- `FormalSystem/Semantics/MinusValidity.lean` - instance + 8 proof bodies
- `FormalSystem/Semantics/PlusValidity.lean` - instance + 8 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - 8 `rfl` coincidences

**Verification**:
- G1-G6; axiom-parity diff empty; signature diffs empty.

---

### Phase 4: Instantiate the validity layer for L⋆ with the `∀ v` fold (`Semantics/StarValidity.lean`) [COMPLETED]

**Goal**: The phase that settles deliverable 2 in the landed tree: fold the stored-time vector
into `sat` and show, by `rfl` against the unmodified L⋆ definitions, that the `(τ, x, v)` point
shape is covered by the same abstraction.

**Tasks**:
- [ ] `instance : PointTruth StarFormula where sat {F} M τ t φ := ∀ v : ℕ → F.Duration, StarTruthAt M τ t v φ`, with a docstring recording the innermost-binder argument (`StarValidOn F φ = ∀ M τ x v, …` is, as a Pi telescope, literally `∀ M τ x, (∀ v, …)`).
- [ ] Delegate the 10 category-A bodies: `StarValidOnFrames.mono`, `StarValidIn.mono`, `TaskFrame.StarValidOn.{of_forall_total,apply_total}`, `StarValidOnFrames.{of_forall_total,apply_total}`, `StarValidIn.{of_forall_total,apply_total}`, `StarValid.{of_forall_total,apply}` (`StarValidity.lean:74-160`). Twelve of the eighteen probe-1 delegations needed `(L := StarFormula) (φ := φ)`; expect the same here.
- [ ] Leave `TaskFrame.StarValidOn`, `StarValidOnFrames`, `StarValidIn`, `StarValid`, `starValidOn_ofPlus`, `starValidOnFrames_ofPlus`, `sentDet`, `sentDet_unfold`, `not_starValidOn_sentDet` untouched (the `ofPlus` bridges are proved by induction and sit outside the abstraction by the stated criterion).
- [ ] Extend the test module with the four L⋆ coincidences, the first being the load-bearing `example (F) (φ : StarFormula) : TaskFrame.StarValidOn F φ = TaskFrame.GenericValidOn F φ := rfl`.
- [ ] Signature diff; orphaned-`private` sweep; axiom-parity diff empty (`StarValid.apply` must stay `[propext]`).

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: full

**Scope Hypothesis**: 10 theorem bodies, 0 signatures; all four `rfl` coincidences close
without any `show`/`change`. If any coincidence needs more than `rfl`, the fold is NOT
statement-preserving for that definition -- stop, record the failing goal as a BLOCKING finding
in the summary, and do not adjust the definition.

**Files to modify**:
- `FormalSystem/Semantics/StarValidity.lean` - instance + 10 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - 4 `rfl` coincidences

**Verification**:
- G1-G6; axiom-parity diff empty; the four L⋆ `rfl` examples compile.

---

### Phase 5: `Semantics/TruthClauses.lean` -- operator/clause classes, generic derived operators, generic clause lemmas [COMPLETED]

**Goal**: Land the second leaf module: the `Env`-parameterised pointed-truth base, one class per
primitive operator bundling the operator with its truth clause, bundles by `extends`, the
derived operators as `abbrev`s, and the derived-clause lemmas proved once -- with the
classical-tactic discipline that keeps axiom parity.

**Tasks**:
- [ ] Capture the clause-layer axiom baseline if Phase 1's `04_axiom-baseline.txt` does not already cover every category-B name (it should; verify).
- [ ] Create `FormalSystem/Semantics/TruthClauses.lean`: header; imports `FormalSystem.Semantics.TaskModel`, `FormalSystem.Semantics.ConvexHistory`; module docstring with `## Design Invariants` (initial contract wording, re-verified in Phase 10) and an explicit statement that the generic layer imports nothing language-specific.
- [ ] `class TruthEnv (L : Type) where Env : TaskFrame → Type; T : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → Env F → L → Prop`.
- [ ] Operator classes at cslib's grain, each `[TruthEnv L]`-parameterised and bundling operator + clause: `BotClause` (`bot`, `bot_clause : ¬ T M τ t e bot`), `ImpClause`, `BoxClause` (`∀ σ, σ.IsTotal → T M σ t e φ`), `UntlClause`, `SnceClause`, `StabClause`, `AllFutureClause`, `AllPastClause`. Clause statements are copied from `Semantics/Truth.lean`'s `TruthAt` (`:240-249`) with `e` threaded inert. `StabClause` carries the same-state relation as a `sameState` field (see the note under `## Lean Challenge Statements`): `SameStateAt` lives in `PlusTruth.lean`, above this module in the import order, so the generic module must not name it; L⁺/L⋆ instances supply `SameStateAt` and the live `dstab_iff` statements are untouched.
- [ ] Bundles: `BoolClauses L extends BotClause L, ImpClause L, BoxClause L`; `UntlClauses L extends BoolClauses L, UntlClause L, SnceClause L`; `TenseClauses L extends BoolClauses L, AllFutureClause L, AllPastClause L` (L⁻'s primitive-tense shape); `StabClauses L extends UntlClauses L, StabClause L`. If `extends` diamonds break `rfl` bridges or instance resolution, fall back to the probe-2 coarse chain plus a standalone tense class and record why.
- [ ] Under `namespace TruthClauses`, with `section`-scoped capability groups, the derived operators as `abbrev` with bodies character-identical to `Syntax/Formula.lean:136,139,149,159,169,179,451,456,461,478`: `neg φ := imp φ bot`, `top := imp bot bot`, `and φ ψ := neg (imp φ (neg ψ))`, `or φ ψ := imp (neg φ) ψ`, `diamond φ := neg (box (neg φ))`, `someFuture φ := untl top φ`, `somePast φ := snce top φ`, `allFuture φ := neg (someFuture (neg φ))`, `allPast φ := neg (somePast (neg φ))`, `always φ := and (allPast φ) (and φ (allFuture φ))`, `dstab φ := neg (stab (neg φ))` (confirm against `PlusLanguage/Formula.lean:183`); and the tense-primitive pair `someFuture' φ := neg (allFuture (neg φ))`, `somePast' φ := neg (allPast (neg φ))` (names to be chosen so they do not collide; confirm against `MinusLanguage/Formula.lean:122,126`).
- [ ] Generic lemmas, no attributes: `neg_iff` (by `rw` + explicit terms ONLY -- this is what keeps `Truth.neg_iff` at `[propext]`), `top_true`, `and_iff`, `or_iff`, `diamond_iff`, `someFuture_iff`, `somePast_iff`, `allFuture_iff`, `allPast_iff`, `always_iff_tri`, `dstab_iff`, `someFuture_iff_of_allFuture`, `somePast_iff_of_allPast`, `always_iff_of_tense`. Proof routes per the report's tactic table.
- [ ] `#print axioms` on every generic lemma; assert each is a subset of the INTERSECTION of the baseline sets of the wrappers that will delegate to it (from `04_axiom-baseline.txt`). `neg_iff` and `top_true` must be `⊆ [propext]`.
- [ ] Register in `FormalSystem/Semantics.lean` (before `FormalSystem.Semantics.Truth`) and add the README row; extend the test module's imports.
- [ ] No instances in this phase.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

**Scope Hypothesis**: 1 base class + 8 operator classes + 4 bundles + 13 `abbrev`s + 14 generic
lemmas ≈ 250 lines; every generic lemma's axiom set is within the intersection bound. Confirm by
the `#print axioms` table recorded in the phase's commit message or the summary.

**Files to modify**:
- `FormalSystem/Semantics/TruthClauses.lean` - new
- `FormalSystem/Semantics.lean` - add import
- `FormalSystem/Semantics/README.md` - add row
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - import

**Verification**:
- G1, G2, G3, G5, G6; the axiom-subset assertion holds for every generic lemma; no `@[simp]` on any generic lemma; C23 passes with the new class and namespace names.

---

### Phase 6: Instantiate the clause layer for L (`Semantics/Truth.lean`) [NOT STARTED]

**Goal**: Instantiate `TruthEnv Formula` (`Env _ := PUnit`) and the clause classes, then
delegate the ten L derived-clause lemmas while preserving `@[simp, truth_norm]` on every one that
carries it today and leaving the collected `always_iff` alone.

**Tasks**:
- [ ] Add `import FormalSystem.Semantics.TruthClauses`; after `TruthAt` (`:240`), add the instances `TruthEnv Formula`, `BotClause`, `ImpClause`, `BoxClause`, `UntlClause`, `SnceClause` (hence `UntlClauses Formula`), each clause field `Iff.rfl` or `fun h => h`. The existing primitive clause lemmas (category C) stay as they are.
- [ ] Delegate, keeping attributes and docstrings: `Truth.neg_iff` (`:429`), `top_true` (`:435`), `and_iff` (`:440`), `or_iff` (`:448`), `diamond_iff` (`:457`), `some_future_iff` (`:326`), `some_past_iff` (`:343`), `future_iff` (`:360`), `past_iff` (`:378`), `always_iff_tri` (`:505`). Wrapper bodies pass `PUnit.unit` for `e`; `PUnit` never appears in a signature.
- [ ] Do NOT touch `Truth.always_iff` (`:517`, collected `∀ s` form): it needs the frame's trichotomy and is L-only.
- [ ] Extend the test module: `rfl` bridges `Formula.neg φ = TruthClauses.neg φ` and siblings for `top`, `and`, `or`, `diamond`, `someFuture`, `somePast`, `allFuture`, `allPast`, `always`.
- [ ] Signature diff; orphaned-`private` sweep; axiom-parity diff empty (`Truth.neg_iff` stays `[propext]`).

**Timing**: 1.5 hours

**Depends on**: 1, 5

**Verification Tier**: full

**Scope Hypothesis**: 10 theorem bodies, 0 signatures, 0 attribute changes (verify with
`grep -c "@\[simp, truth_norm\]"` unchanged at 10). Confirm by diff.

**Files to modify**:
- `FormalSystem/Semantics/Truth.lean` - instances + 10 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - 10 `rfl` bridges

**Verification**:
- G1-G6; axiom-parity diff empty; attribute count unchanged; C16 simpNF unchanged.

---

### Phase 7: Instantiate the clause layer for L⁻ via the tense-primitive bundle (`Semantics/MinusTruth.lean`) [NOT STARTED]

**Goal**: Instantiate the first genuine syntax-side divergence: L⁻ has `allPast`/`allFuture` as
primitive constructors, so it instantiates `TenseClauses`, not `UntlClauses`, and its two
existential-tense lemmas are derived in the opposite duality direction.

**Tasks**:
- [ ] Add the import; after `MinusTruthAt` (`:107`), instances `TruthEnv MinusFormula` (`Env _ := PUnit`), `BotClause`, `ImpClause`, `BoxClause`, `AllFutureClause`, `AllPastClause` (hence `TenseClauses MinusFormula`); `past_iff` (`:136`) and `future_iff` (`:140`) remain as the payload names they are today.
- [ ] Delegate, preserving `@[simp]`: `MinusTruth.neg_iff` (`:146`), `top_true` (`:150`), `and_iff` (`:153`), `or_iff` (`:159`), `diamond_iff` (`:172`), `always_iff` (`:200`, tri form, via `always_iff_of_tense`).
- [ ] Attempt `somePast_iff` (`:180`) and `someFuture_iff` (`:188`) via `somePast_iff_of_allPast`/`someFuture_iff_of_allFuture`, contingent on the `rfl` bridges `MinusFormula.someFuture φ = TruthClauses.someFuture' φ` (and past). If a bridge fails, leave both bodies as they stand and record a `#### Reasoned Exclusions` row with the failing `rfl` goal as evidence; close the phase `[COMPLETED WITH EXCLUSIONS]`. Both outcomes are acceptable per the report.
- [ ] Extend the test module with the L⁻ bridges (`neg`, `top`, `and`, `or`, `diamond`, `always`, and the two tense ones if they hold).
- [ ] Signature diff; orphaned-`private` sweep; axiom-parity diff empty.

**Timing**: 1.5 hours

**Depends on**: 1, 5

**Verification Tier**: full

**Scope Hypothesis**: 6 mandatory + 2 conditional theorem bodies, 0 signatures. Confirm by diff;
the conditional pair's outcome is recorded either as two more delegations or as a Reasoned
Exclusions table.

**Files to modify**:
- `FormalSystem/Semantics/MinusTruth.lean` - instances + 6 (+2) proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - L⁻ `rfl` bridges

**Verification**:
- G1-G6; axiom-parity diff empty; `MinusTruth.diamond_iff` stays `[propext, Classical.choice, Quot.sound]`.

---

### Phase 8: Instantiate the clause layer for L⁺ (`Semantics/PlusTruth.lean`) [NOT STARTED]

**Goal**: Instantiate `StabClauses PlusFormula` (`Env _ := PUnit`) and delegate the ten L⁺
derived-clause lemmas, including the first `dstab_iff`.

**Tasks**:
- [ ] Add the import; after `PlusTruthAt` (`:120`), instances `TruthEnv PlusFormula`, the five `UntlClauses` operator classes, and `StabClause` (clause copied from `PlusTruthAt`'s `stab` arm; `stab_state_only` at `:380` is untouched and outside the abstraction).
- [ ] Delegate, preserving the file's attribute set (`@[simp]` on `bot_false` only, none on these): `PlusTruth.top_true` (`:160`), `neg_iff` (`:162`), `and_iff` (`:165`), `or_iff` (`:169`), `dstab_iff` (`:176`), `someFuture_iff` (`:181`), `allFuture_iff` (`:185`), `somePast_iff` (`:189`), `allPast_iff` (`:193`), `diamond_iff` (`:197`). Respect the file's explicit-binder `variable` convention: the statement is what the file has today.
- [ ] L⁺ has no `always` lemma -- add none.
- [ ] Extend the test module with the L⁺ bridges including `PlusFormula.dstab φ = TruthClauses.dstab φ`.
- [ ] Signature diff; orphaned-`private` sweep; axiom-parity diff empty.

**Timing**: 1 hour

**Depends on**: 1, 5

**Verification Tier**: full

**Scope Hypothesis**: 10 theorem bodies, 0 signatures. Confirm by diff.

**Files to modify**:
- `FormalSystem/Semantics/PlusTruth.lean` - instances + 10 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - L⁺ `rfl` bridges

**Verification**:
- G1-G6; axiom-parity diff empty.

---

### Phase 9: Instantiate the clause layer for L⋆ with `Env F := ℕ → F.Duration` (`Semantics/StarTruth.lean`) [NOT STARTED]

**Goal**: The phase that validates the `Env` design: the stored-time vector is the environment,
threaded inert through every shared clause, and the eleven L⋆ derived-clause lemmas delegate with
their trailing `v` binder intact.

**Tasks**:
- [ ] Add the import; after `StarTruthAt` (`:110`), instances `TruthEnv StarFormula` with `Env F := ℕ → F.Duration` and `T M τ t v φ := StarTruthAt M τ t v φ`, the `StabClauses` operator classes; `timeStore`/`timeRecall` are extra constructors the shared core never mentions (contract obligation O2) -- nothing about them is instantiated.
- [ ] Delegate, preserving attributes: `StarTruth.top_true` (`:160`), `neg_iff` (`:162`), `and_iff` (`:165`), `or_iff` (`:169`), `someFuture_iff` (`:175`), `allFuture_iff` (`:179`), `somePast_iff` (`:183`), `allPast_iff` (`:187`), `diamond_iff` (`:191`), `dstab_iff` (`:195`), `always_iff` (`:201`, tri form). The wrapper passes the file's `v` as `e`.
- [ ] Untouched by construction: `starTruthAt_ofPlus`, `star_truth_congr_ext`, `update_shift_comm`, `starTruthAt_timeShift` (`:318`) -- the honest boundary; the module's design note (a) already records why the vector shifts.
- [ ] Extend the test module with the L⋆ bridges (`neg`, `and`, `diamond`, `dstab`, `always`, and the rest).
- [ ] Signature diff; orphaned-`private` sweep; axiom-parity diff empty (`StarTruth.dstab_iff` stays `[propext, Classical.choice, Quot.sound]`).

**Timing**: 1.5 hours

**Depends on**: 1, 5

**Verification Tier**: full

**Scope Hypothesis**: 11 theorem bodies, 0 signatures; no wrapper needs a `v`-specialised generic
lemma. Confirm by diff; if a wrapper cannot delegate because its statement mentions `v` in a
position the generic `e` does not cover, that lemma is language-specific -- record it in
`04_scope-enumeration.txt` as a category correction and a Reasoned Exclusion, do not bend the
class.

**Files to modify**:
- `FormalSystem/Semantics/StarTruth.lean` - instances + 11 proof bodies
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - L⋆ `rfl` bridges

**Verification**:
- G1-G6; axiom-parity diff empty.

---

### Phase 10: Extension contract from the instantiations performed, fifth-language conformance check, and the final sweep [NOT STARTED]

**Goal**: Write deliverable 6 from what Phases 2-4 and 6-9 actually did, prove the contract
sufficient with a toy fifth language in the test tree, confirm nothing superseded remains and
nothing was renamed, and run the full gate set one last time.

**Tasks**:
- [ ] Rewrite `ValidityLayer.lean`'s `## Design Invariants` section as the validity-layer contract: exactly one instance with one field (`sat`, `∀`-closed over any extra per-point parameters); obligations O1 (every extra parameter is the innermost binder of the language's `ValidOn` and every adapter) and O2 (extra parameters are threaded unchanged through `imp`/`box`/`untl`/`snce`/`stab`); the enumerated inherited names (`TaskFrame.GenericValidOn`, `GenericValidOnFrames`, `GenericValidIn`, `GenericValid`, both `mono`, the eight adapters, the three `of_not`, `genericValidOn_iff_total`); the explicit NOT-inherited list (anything proved by induction on the language: time-shift, congruence, state-locality, embedding bridges); and the no-`abbrev`-promotion and no-bare-namesake naming invariants. Every claim must cite the phase-landed instance it is drawn from -- if any obligation was not needed by all four instances, say which.
- [ ] Rewrite `TruthClauses.lean`'s `## Design Invariants` as the clause-layer contract: `TruthEnv` (`Env` = the extra-parameter type or `PUnit`) plus the operator-class instances whose clause fields are `Iff.rfl`/`fun h => h`; the tiered inheritance table (Bool → 5 lemmas; + untl/snce → 5 more; + stab → `dstab_iff`; tense-primitive → the alternative pair + `always`); the requirement that the language's derived operators be the Lukasiewicz/untl encodings character-for-character (that is what makes the `rfl` bridges hold); the "generic lemmas carry no attributes; wrappers carry the language's" rule; and the "if you want a bridge/elimination API, a statement moved -- revert" rule.
- [ ] Toy fifth language in `ValidityLayerTest.lean`: a minimal `inductive Toy` with `bot`/`imp`/`box` (and an atom), a six-line truth recursion, `instance : PointTruth Toy` and the three Bool clause instances; `example`s that `GenericValid`, `GenericValidIn.mono`, `TruthClauses.neg_iff` and `TruthClauses.diamond_iff` elaborate at `Toy`. Budget 30 minutes; if it overruns, drop it and record why in the summary.
- [ ] Sweep: `grep` each of the eight files for any remaining duplicated proof text of a delegated lemma (there should be none); confirm no `private` orphan remains (C17 report shows no new rows); confirm every name on `04_scope-enumeration.txt` still resolves (`#check` list run via `lake env lean`).
- [ ] Docs sync: verify the two `Semantics/README.md` rows and the test README row read correctly after the contract is final; grep `docs/` and `README.md` for any exhaustive `Semantics/` module inventory and add the two modules where one exists (C12/C13 resolve).
- [ ] Final gate set (G1-G6) including the full `check-module-invariants.sh` run; record the measured counts (territory total, per-category split, bodies delegated per language, exclusions) for the summary.

**Timing**: 2 hours

**Depends on**: 2, 3, 4, 6, 7, 8, 9

**Verification Tier**: full

**Scope Hypothesis**: the contract enumerates 18 inherited validity-layer names for one instance
field and 11 (+3 tense-primitive) clause-layer names for six `Iff.rfl` lines; the toy language
instantiates in ≤ 60 lines. Confirm by the test module compiling and the docstring's lists
matching `04_scope-enumeration.txt`'s category-A/B rows one-for-one.

**Files to modify**:
- `FormalSystem/Semantics/ValidityLayer.lean` - docstring contract
- `FormalSystem/Semantics/TruthClauses.lean` - docstring contract
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` - toy language
- `FormalSystem/Semantics/README.md`, `Tests/BimodalTest/Semantics/README.md`, any docs inventory - rows

**Verification**:
- G1-G6; C19 docstring coverage unchanged or higher; C9 zero task-number citations under `FormalSystem/` (the docstrings cite module names and section headings, never this task); the contract's inherited-name lists match the enumeration file.

## Lean Challenge Statements

The classes (`PointTruth`, `TruthEnv`, the operator classes and bundles) and the derived-operator
`abbrev`s are not pinned here because the snapshot tool pins `def`/`theorem`/`instance` only;
they appear in the block as scaffolding so the pinned statements type-check standalone. The exact
class field shapes are fixed by `Semantics/Truth.lean`'s `TruthAt` clauses and the probes.

```lean
import FormalSystem.Semantics.TaskModel
import FormalSystem.Semantics.ConvexHistory
import FormalSystem.Semantics.FrameClassValidity

namespace FormalSystem.Semantics

class PointTruth (L : Type) where
  sat : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → L → Prop

variable {L : Type} [PointTruth L]

def TaskFrame.GenericValidOn (F : TaskFrame) (φ : L) : Prop := sorry

def GenericValidOnFrames (P : TaskFrame → Prop) (φ : L) : Prop := sorry

def GenericValidIn (fc : ProofSystem.FrameClass) (φ : L) : Prop := sorry

def GenericValid (φ : L) : Prop := sorry

theorem genericValidOn_iff_total (F : TaskFrame) (φ : L) :
    F.GenericValidOn φ ↔ ∀ (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal →
      ∀ x : F.Duration, PointTruth.sat M τ x φ := sorry

theorem GenericValidOnFrames.mono {P Q : TaskFrame → Prop} {φ : L} (h : ∀ F, Q F → P F)
    (hP : GenericValidOnFrames P φ) : GenericValidOnFrames Q φ := sorry

theorem GenericValidIn.mono {fc₁ fc₂ : ProofSystem.FrameClass} {φ : L} (h : fc₁ ≤ fc₂)
    (hv : GenericValidIn fc₁ φ) : GenericValidIn fc₂ φ := sorry

theorem TaskFrame.GenericValidOn.of_forall_total {F : TaskFrame} {φ : L}
    (h : ∀ (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal → ∀ x : F.Duration,
           PointTruth.sat M τ x φ) : F.GenericValidOn φ := sorry

theorem TaskFrame.GenericValidOn.apply_total {F : TaskFrame} {φ : L} (h : F.GenericValidOn φ)
    (M : TaskModel F) (τ : ConvexHistory F) (hτ : τ.IsTotal) (x : F.Duration) :
    PointTruth.sat M τ x φ := sorry

theorem GenericValidOnFrames.of_forall_total {P : TaskFrame → Prop} {φ : L}
    (h : ∀ (F : TaskFrame), P F → ∀ (M : TaskModel F) (τ : ConvexHistory F),
           τ.IsTotal → ∀ x : F.Duration, PointTruth.sat M τ x φ) :
    GenericValidOnFrames P φ := sorry

theorem GenericValidOnFrames.apply_total {P : TaskFrame → Prop} {φ : L}
    (h : GenericValidOnFrames P φ) (F : TaskFrame) (hF : P F) (M : TaskModel F)
    (τ : ConvexHistory F) (hτ : τ.IsTotal) (x : F.Duration) : PointTruth.sat M τ x φ := sorry

theorem GenericValidIn.of_forall_total {fc : ProofSystem.FrameClass} {φ : L}
    (h : ∀ (F : TaskFrame), fc.Sat F → ∀ (M : TaskModel F) (τ : ConvexHistory F),
           τ.IsTotal → ∀ x : F.Duration, PointTruth.sat M τ x φ) :
    GenericValidIn fc φ := sorry

theorem GenericValidIn.apply_total {fc : ProofSystem.FrameClass} {φ : L}
    (h : GenericValidIn fc φ) (F : TaskFrame) (hF : fc.Sat F) (M : TaskModel F)
    (τ : ConvexHistory F) (hτ : τ.IsTotal) (x : F.Duration) : PointTruth.sat M τ x φ := sorry

theorem GenericValid.of_forall_total {φ : L}
    (h : ∀ (F : TaskFrame) (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal →
           ∀ x : F.Duration, PointTruth.sat M τ x φ) : GenericValid φ := sorry

theorem GenericValid.apply {φ : L} (h : GenericValid φ) (F : TaskFrame) (M : TaskModel F)
    (τ : ConvexHistory F) (hτ : τ.IsTotal) (x : F.Duration) : PointTruth.sat M τ x φ := sorry

theorem GenericValidOnFrames.of_not {P : TaskFrame → Prop} {φ : L}
    (h : ¬ GenericValidOnFrames P φ) :
    ¬ ∀ (F : TaskFrame), P F → ∀ (M : TaskModel F) (τ : ConvexHistory F),
        τ.IsTotal → ∀ x : F.Duration, PointTruth.sat M τ x φ := sorry

theorem GenericValidIn.of_not {fc : ProofSystem.FrameClass} {φ : L}
    (h : ¬ GenericValidIn fc φ) :
    ¬ ∀ (F : TaskFrame), fc.Sat F → ∀ (M : TaskModel F) (τ : ConvexHistory F),
        τ.IsTotal → ∀ x : F.Duration, PointTruth.sat M τ x φ := sorry

theorem GenericValid.of_not {φ : L} (h : ¬ GenericValid φ) :
    ¬ ∀ (F : TaskFrame) (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal →
        ∀ x : F.Duration, PointTruth.sat M τ x φ := sorry

class TruthEnv (L : Type) where
  Env : TaskFrame → Type
  T : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → Env F → L → Prop

class BotClause (L : Type) [TruthEnv L] where
  bot : L
  bot_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F), ¬ TruthEnv.T M τ t e bot

class ImpClause (L : Type) [TruthEnv L] where
  imp : L → L → L
  imp_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ ψ : L),
    TruthEnv.T M τ t e (imp φ ψ) ↔ (TruthEnv.T M τ t e φ → TruthEnv.T M τ t e ψ)

class BoxClause (L : Type) [TruthEnv L] where
  box : L → L
  box_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L),
    TruthEnv.T M τ t e (box φ) ↔ ∀ σ : ConvexHistory F, σ.IsTotal → TruthEnv.T M σ t e φ

class UntlClause (L : Type) [TruthEnv L] where
  untl : L → L → L
  untl_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ ψ : L),
    TruthEnv.T M τ t e (untl φ ψ) ↔ ∃ s : F.Duration, t < s ∧ TruthEnv.T M τ s e ψ ∧
      ∀ r : F.Duration, t < r → r < s → TruthEnv.T M τ r e φ

class SnceClause (L : Type) [TruthEnv L] where
  snce : L → L → L
  snce_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ ψ : L),
    TruthEnv.T M τ t e (snce φ ψ) ↔ ∃ s : F.Duration, s < t ∧ TruthEnv.T M τ s e ψ ∧
      ∀ r : F.Duration, s < r → r < t → TruthEnv.T M τ r e φ

class StabClause (L : Type) [TruthEnv L] where
  stab : L → L
  sameState : ∀ {F : TaskFrame}, ConvexHistory F → ConvexHistory F → F.Duration → Prop
  stab_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L),
    TruthEnv.T M τ t e (stab φ) ↔ ∀ σ : ConvexHistory F, σ.IsTotal →
      sameState τ σ t → TruthEnv.T M σ t e φ

class AllFutureClause (L : Type) [TruthEnv L] where
  allFuture : L → L
  allFuture_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (t : F.Duration) (e : TruthEnv.Env L F) (φ : L),
    TruthEnv.T M τ t e (allFuture φ) ↔ ∀ s : F.Duration, t < s → TruthEnv.T M τ s e φ

class AllPastClause (L : Type) [TruthEnv L] where
  allPast : L → L
  allPast_clause : ∀ {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (t : F.Duration) (e : TruthEnv.Env L F) (φ : L),
    TruthEnv.T M τ t e (allPast φ) ↔ ∀ s : F.Duration, s < t → TruthEnv.T M τ s e φ

namespace TruthClauses

section Bool
variable {L : Type} [TruthEnv L] [BotClause L] [ImpClause L] [BoxClause L] {F : TaskFrame}

abbrev neg (φ : L) : L := ImpClause.imp φ BotClause.bot
abbrev top : L := ImpClause.imp (BotClause.bot : L) BotClause.bot
abbrev and (φ ψ : L) : L := neg (ImpClause.imp φ (neg ψ))
abbrev or (φ ψ : L) : L := ImpClause.imp (neg φ) ψ
abbrev diamond (φ : L) : L := neg (BoxClause.box (neg φ))

theorem neg_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (neg φ) ↔ ¬ TruthEnv.T M τ t e φ := sorry

theorem top_true (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) : TruthEnv.T M τ t e (top : L) := sorry

theorem and_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ ψ : L) :
    TruthEnv.T M τ t e (and φ ψ) ↔ (TruthEnv.T M τ t e φ ∧ TruthEnv.T M τ t e ψ) := sorry

theorem or_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ ψ : L) :
    TruthEnv.T M τ t e (or φ ψ) ↔ (TruthEnv.T M τ t e φ ∨ TruthEnv.T M τ t e ψ) := sorry

theorem diamond_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (diamond φ) ↔
      ∃ σ : ConvexHistory F, σ.IsTotal ∧ TruthEnv.T M σ t e φ := sorry
end Bool

section Untl
variable {L : Type} [TruthEnv L] [BotClause L] [ImpClause L] [BoxClause L]
  [UntlClause L] [SnceClause L] {F : TaskFrame}

abbrev someFuture (φ : L) : L := UntlClause.untl top φ
abbrev somePast (φ : L) : L := SnceClause.snce top φ
abbrev allFuture (φ : L) : L := neg (someFuture (neg φ))
abbrev allPast (φ : L) : L := neg (somePast (neg φ))
abbrev always (φ : L) : L := and (allPast φ) (and φ (allFuture φ))

theorem someFuture_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (someFuture φ) ↔ ∃ s : F.Duration, t < s ∧ TruthEnv.T M τ s e φ := sorry

theorem somePast_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (somePast φ) ↔ ∃ s : F.Duration, s < t ∧ TruthEnv.T M τ s e φ := sorry

theorem allFuture_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (allFuture φ) ↔ ∀ s : F.Duration, t < s → TruthEnv.T M τ s e φ := sorry

theorem allPast_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (allPast φ) ↔ ∀ s : F.Duration, s < t → TruthEnv.T M τ s e φ := sorry

theorem always_iff_tri (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (always φ) ↔
      (∀ s : F.Duration, s < t → TruthEnv.T M τ s e φ) ∧ TruthEnv.T M τ t e φ ∧
        (∀ s : F.Duration, t < s → TruthEnv.T M τ s e φ) := sorry
end Untl

section Stab
variable {L : Type} [TruthEnv L] [BotClause L] [ImpClause L] [BoxClause L] [StabClause L]
  {F : TaskFrame}

abbrev dstab (φ : L) : L := neg (StabClause.stab (neg φ))

theorem dstab_iff (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (dstab φ) ↔
      ∃ σ : ConvexHistory F, σ.IsTotal ∧ StabClause.sameState (L := L) τ σ t ∧
        TruthEnv.T M σ t e φ := sorry
end Stab

section Tense
variable {L : Type} [TruthEnv L] [BotClause L] [ImpClause L] [BoxClause L]
  [AllFutureClause L] [AllPastClause L] {F : TaskFrame}

abbrev someFuture' (φ : L) : L := neg (AllFutureClause.allFuture (neg φ))
abbrev somePast' (φ : L) : L := neg (AllPastClause.allPast (neg φ))
abbrev always' (φ : L) : L :=
  and (AllPastClause.allPast φ) (and φ (AllFutureClause.allFuture φ))

theorem someFuture_iff_of_allFuture (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (someFuture' φ) ↔ ∃ s : F.Duration, t < s ∧ TruthEnv.T M τ s e φ := sorry

theorem somePast_iff_of_allPast (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (somePast' φ) ↔ ∃ s : F.Duration, s < t ∧ TruthEnv.T M τ s e φ := sorry

theorem always_iff_of_tense (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration)
    (e : TruthEnv.Env L F) (φ : L) :
    TruthEnv.T M τ t e (always' φ) ↔
      (∀ s : F.Duration, s < t → TruthEnv.T M τ s e φ) ∧ TruthEnv.T M τ t e φ ∧
        (∀ s : F.Duration, t < s → TruthEnv.T M τ s e φ) := sorry
end Tense

end TruthClauses

end FormalSystem.Semantics
```

Notes on the block: `SameStateAt` is a `def` on `ConvexHistory F` alone
(`Semantics/PlusTruth.lean:78`), but `PlusTruth.lean` imports `Truth.lean`, which will import
`TruthClauses.lean`, so the generic module cannot name it without an import cycle -- and the
generic layer imports nothing language-specific in any case. `StabClause` therefore carries the
same-state relation as its own `sameState` field; the L⁺ and L⋆ instances supply `SameStateAt`,
so the live `PlusTruth.dstab_iff`/`StarTruth.dstab_iff` statements (which mention `SameStateAt`)
are unchanged and their wrappers delegate by the instance field's defeq. Nothing is relocated.
The `untl`/`snce` clause shapes above match `Semantics/Truth.lean:240-249` (`untl ψ φ`: `φ`
eventual, `ψ` throughout the open interval; `someFuture φ := untl top φ`); Phase 5 copies them
from the source verbatim, which is authoritative over this block.

## Testing & Validation

- [ ] `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build FormalSystem` green after every phase (detached, per `long-builds.md`).
- [ ] `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build BimodalTest` green after every phase; `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` holds every `rfl` coincidence (12 validity, 30+ derived-operator) and the toy fifth language.
- [ ] `probes/axiom-parity.lean` output byte-identical to `probes/04_axiom-baseline.txt` after every instantiation phase (Phases 2-4, 6-9) and at the end.
- [ ] `bash scripts/check-module-invariants.sh` exit 0 after every phase; C2/C14 baselines unchanged; C23 and C26 pass with the new names; C16 simpNF unchanged; C24 covers both new modules; C19 coverage not lowered.
- [ ] Signature diff (`git show HEAD~N:<file>` vs working tree, declaration headers only) empty for all eight touched files.
- [ ] `git diff --stat` across the whole task touches only: the eight truth/validity modules, the two new modules, `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`, the test module, `Tests/BimodalTest.lean`, `Tests/BimodalTest/Semantics/README.md`, `specs/577_*/**`.
- [ ] `grep -rn "sorry" FormalSystem/Semantics/{ValidityLayer,TruthClauses}.lean` empty; C3 structural inventory unchanged.
- [ ] `grep -rn "577" FormalSystem/ Tests/` empty (C9).

## Artifacts & Outputs

- `specs/577_abstract_validity_layer_over_truth_class/plans/01_abstract-validity-layer-truth-class.md` (this file)
- `specs/577_abstract_validity_layer_over_truth_class/summaries/01_abstract-validity-layer-truth-class-summary.md` (written by the implementer; must report the measured counts and the honest-boundary list)
- `specs/577_abstract_validity_layer_over_truth_class/probes/04_scope-enumeration.txt`, `probes/axiom-parity.lean`, `probes/04_axiom-baseline.txt`
- `FormalSystem/Semantics/ValidityLayer.lean` (new; `PointTruth`, `Generic*` validity layer, extension contract)
- `FormalSystem/Semantics/TruthClauses.lean` (new; `TruthEnv`, operator/clause classes, `TruthClauses.*` derived operators and lemmas, extension contract)
- `Tests/BimodalTest/Semantics/ValidityLayerTest.lean` (new)
- Edited: `FormalSystem/Semantics/{Truth,MinusTruth,PlusTruth,StarTruth,Validity,MinusValidity,PlusValidity,StarValidity}.lean` (instances + proof bodies only), `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`, `Tests/BimodalTest.lean`, `Tests/BimodalTest/Semantics/README.md`

## Rollback/Contingency

- Every phase is independently revertable with `git revert` of its phase commits: Phases 1 and 5
  add leaf modules nobody imports until the instantiation phases, so reverting them is a file
  deletion plus two aggregator lines; each instantiation phase changes one file's proof bodies and
  adds one instance block, so reverting it restores the original bodies with zero downstream
  effect (statements never changed).
- If Phase 4's `rfl` coincidences fail, the `∀ v` fold is not statement-preserving: revert Phase 4,
  keep Phases 1-3 (three languages abstracted is a valid partial outcome), report the failing goal
  as the named obstruction, and close with exclusions. Do not adjust any L⋆ definition.
- If Phase 5's fine-grained classes cannot be made to bridge by `rfl`, fall back within the phase
  to the probe-2 coarse chain (proven green); if that also fails for a specific language, that
  language's clause layer stays per-language and the phase for it closes
  `[COMPLETED WITH EXCLUSIONS]` with the failing bridge as evidence.
- If any axiom-parity diff is non-empty, fix the generic proof (remove the classical tactic);
  never rebaseline, never change the wrapper's statement.
- If a name cannot be preserved for any reason, that is a BLOCKING finding: stop the phase, record
  it in the summary, and leave the tree at the last green commit.
