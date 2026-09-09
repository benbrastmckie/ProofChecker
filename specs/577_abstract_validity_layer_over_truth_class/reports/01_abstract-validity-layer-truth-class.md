# Research Report: Task #577

**Task**: 577 - Abstract the per-language validity layer over a truth-relation class
**Started**: 2026-09-09T16:09:00Z
**Completed**: 2026-09-09T16:45:00Z
**Effort**: ~35 min agent time; 3 compiled Lean probes, all green
**Dependencies**: 576 (completed) — enumeration taken against the post-576 tree
**Sources/Inputs**:
- Codebase: `FormalSystem/Semantics/**`, `FormalSystem/{Minus,Plus,Star}Language/**`, `FormalSystem/Syntax/Formula.lean`
- Three compiled research probes under `specs/577_abstract_validity_layer_over_truth_class/probes/`
- Design-precedent read of `/home/benjamin/Projects/cslib` (`Cslib/Foundations/Logic/{Connectives,Axioms}.lean`, `docs/modal-axiom-schema-architecture.md` §3 and §6, `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean`)
- `lean-lsp` MCP was UNAVAILABLE this session (server failed to connect: missing
  `.claude/scripts/lean-lsp-mcp-wrapper.sh`). All verification was done by compiled probe through
  `lake-build-guard.sh` instead, which is strictly stronger evidence than LSP hover.

**Artifacts**:
- `specs/577_abstract_validity_layer_over_truth_class/reports/01_abstract-validity-layer-truth-class.md` (this report)
- `specs/577_abstract_validity_layer_over_truth_class/probes/01_validity-layer.lean.txt` (green)
- `specs/577_abstract_validity_layer_over_truth_class/probes/02_clause-layer.lean.txt` (green)
- `specs/577_abstract_validity_layer_over_truth_class/probes/03_axiom-parity.lean.txt` + `03_axiom-parity-output.txt`

**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The hard design question (deliverable 2) is SETTLED AFFIRMATIVELY, by compilation, not by
  assumption.** One abstraction covers both point shapes. The hinge is that the L⋆ stored-time
  vector `v` is the **innermost binder** of every L⋆ validity definition and of every L⋆ adapter,
  so `∀ v` folds into a per-language "truth at a point" predicate without disturbing any binder
  telescope. Probe 1 proves twelve `rfl` identities — including
  `TaskFrame.StarValidOn F φ = PointTruth.ValidOn F φ` — with the existing definitions
  **untouched**, then re-derives eighteen existing adapter names with statements copied verbatim
  and one-line delegating proofs. It compiles green.
- **The clause / derived-operator layer also abstracts across all four languages**, via a second
  class carrying an `Env : TaskFrame → Type` parameter (`PUnit` for L/L⁻/L⁺, `ℕ → F.Duration` for
  L⋆) that is threaded inert. Probe 2 proves the generic `neg`/`top`/`and`/`or`/`diamond`/
  `someFuture`/`somePast`/`allFuture`/`allPast`/`dstab`/`always` families once and instantiates
  them at 26 existing names, verbatim. Green.
- **Axiom sets are preserved exactly.** Probe 3 ran `#print axioms` on eleven existing
  declarations and their generic-delegating replacements: **every pair is identical**. The
  `scripts/check-module-invariants.sh` baseline constraint is met by measurement, not by hope.
- **Measured scope, correcting the survey.** The territory holds **1058** declarations, not
  "roughly 658". The eight truth/validity files hold **242**. Of those: **64** are
  language-agnostic validity-layer declarations, **37** are language-agnostic derived-clause
  lemmas, **28** are primitive clause lemmas that become the *instance payload* (the price a
  language pays), and **113** are genuinely language-specific.
- **The honest boundary is one criterion, not a list**: *the abstraction covers everything proved
  from the truth relation; it covers nothing proved by induction on the formula type.* A class
  abstracts the truth **relation**, not the inductive **type**, so it exposes no recursor.
  `timeShift`, `truth_congr_ext`, `stab_state_only`, the `ofPlus`/`ofFormula` embedding bridges,
  and the `StateLocal` families all sit outside for that single reason.
- **Three of the survey's named items are wrong** and must not be planned against:
  `swapTemporal` is a *syntax* `def` on four formula types, not a validity-layer item;
  `interpolates` is a *frame* property (`TaskFrame.Interpolates`) with no per-language
  duplication at all; `sometimes` exists only as a syntax `def` with no truth lemma in any
  language. `timeShift` is on the list but is **3** declarations with **two different
  statements**, not 4 parallel ones.
- **Recommendation**: build the abstraction as the probes did — a class hierarchy internally
  DRY, with **every existing name preserved as a thin verbatim-statement wrapper**. This is a
  deliberate departure from cslib's own chosen architecture, for a reason cslib itself records
  (see Findings → External Resources).

## Context & Scope

Researched: which declarations across `Semantics/**`, `PlusLanguage/**`, `StarLanguage/**` and
`MinusLanguage/**` are language-agnostic; whether a single abstraction can cover the `(τ, x)`
point shape of L/L⁻/L⁺ and the `(τ, x, v)` shape of L⋆; and what shape that abstraction should
take in Lean, informed by cslib.

Constraints honoured throughout: the four-separate-inductives decision is **not** revisited; no
theorem statement may change; no downstream consumer may require editing; axiom baselines must
not drift; no task numbers under `FormalSystem/`.

Enumeration was taken against the **post-576 tree** (HEAD `e3a2c0f1a`, task 576 `completed`), as
the prior-decision block required. `StarValidIn.of_forall_total`/`.apply_total` were found in
their post-574 home, `Semantics/StarValidity.lean`, as predicted.

**Probes were compiled inside the package and then deleted from `FormalSystem/`**; their sources
are archived under `specs/.../probes/` as `.lean.txt` so nothing under `FormalSystem/` is left
behind and no aggregator, README or invariant is perturbed.

## Findings

### Codebase Patterns

#### Measured scope (deliverable 1)

| Directory | Declarations |
|---|---|
| `FormalSystem/Semantics/**` | 791 |
| `FormalSystem/PlusLanguage/**` | 92 |
| `FormalSystem/StarLanguage/**` | 89 |
| `FormalSystem/MinusLanguage/**` | 86 |
| **Territory total** | **1058** |

The description's "roughly 658" is an undercount by ~40%. Counting method: declaration keyword at
column 0, attributes stripped, docstring/section-comment bodies excluded (`specs/.../probes/`
holds nothing for this; the counter is a 20-line Python filter, reproducible from the method
description above).

The eight files that actually carry the duplication:

| File | Decls | File | Decls |
|---|---|---|---|
| `Semantics/Truth.lean` | 45 | `Semantics/Validity.lean` | 53 |
| `Semantics/MinusTruth.lean` | 14 | `Semantics/MinusValidity.lean` | 23 |
| `Semantics/PlusTruth.lean` | 39 | `Semantics/PlusValidity.lean` | 20 |
| `Semantics/StarTruth.lean` | 25 | `Semantics/StarValidity.lean` | 23 |
| | | **Total** | **242** |

Classification of those 242:

| Category | Count | Disposition |
|---|---|---|
| A. Language-agnostic — **validity layer** | **64** | written once; 64 verbatim wrappers |
| B. Language-agnostic — **derived-clause layer** | **37** | written once (11 generic lemmas); 37 verbatim wrappers |
| C. **Primitive clause lemmas** (instance payload) | 28 | stay per-language; each is one `Iff.rfl`/`fun h => h` line and *is* the instance field |
| D. **Genuinely language-specific** | 113 | untouched |

Category A, by language (definitions + `mono` + binder-shape adapters + `of_not` + class-tag
instances):

- **L** (20): `TaskFrame.ValidOn`, `validOn_iff_total`, `ValidOnFrames`, `ValidIn`, `Valid`,
  `ValidOnFrames.mono`, `ValidIn.mono`, `ValidOnFrames.{of_forall_total,apply_total,of_not}`,
  `ValidIn.{of_forall_total,apply_total,of_not}`, `Valid.{of_forall_total,apply,of_not}`,
  `ValidDense`, `ValidZTime`, `ValidRTime`, `ValidComplete`
- **L⁻** (15): the same minus the three `of_not` and `validOn_iff_total`, plus `MinusValidDense`,
  `MinusValidZTime`, `MinusValidRTime`
- **L⁺** (15): `TaskFrame.PlusValidOn`, `PlusValidOnFrames`, `PlusValidIn`, `PlusValid`,
  `PlusValid{Dense,ZTime,RTime}`, `PlusValidOnFrames.mono`, `PlusValidIn.mono`, six adapters
- **L⋆** (14): `TaskFrame.StarValidOn`, `StarValidOnFrames`, `StarValidIn`, `StarValid`, two
  `mono`, **eight** adapters (L⋆ uniquely also carries `TaskFrame.StarValidOn.of_forall_total`
  and `.apply_total`)

Category B, by family: Boolean derived (`neg_iff`, `top_true`, `and_iff`, `or_iff`,
`diamond_iff`) × 4 languages = 20; untl-derived temporal (`someFuture`/`somePast`/`allFuture`/
`allPast`, spelled `some_future_iff`/`some_past_iff`/`future_iff`/`past_iff` on the L side) × 3
languages = 12; `dstab_iff` × 2 = 2; `always` tri-form × 3 = 3.

#### Deliverable 2, settled by proof: one abstraction, both point shapes

The design that works, and compiles:

```lean
class PointTruth (L : Type) where
  sat : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → L → Prop
```

with instances

```lean
instance : PointTruth Formula      where sat M τ t φ := TruthAt M τ t φ
instance : PointTruth MinusFormula where sat M τ t φ := MinusTruthAt M τ t φ
instance : PointTruth PlusFormula  where sat M τ t φ := PlusTruthAt M τ t φ
instance : PointTruth StarFormula  where
  sat {F} M τ t φ := ∀ v : ℕ → F.Duration, StarTruthAt M τ t v φ
```

**Why the L⋆ instance is not a contortion.** `v` is the innermost binder everywhere it occurs:
`TaskFrame.StarValidOn F φ = ∀ M τ x v, StarTruthAt M τ.val x v φ` is, as a Pi telescope,
*literally* `∀ M τ x, (∀ v, StarTruthAt M τ.val x v φ)`. Folding `∀ v` into `sat` therefore
changes nothing about the definition's type — and the same holds for every adapter, whose `v` is
a trailing explicit argument.

Probe 1 verifies twelve identities by `rfl` **against the unmodified live definitions**:

```
TaskFrame.ValidOn F φ      = PointTruth.ValidOn F φ        -- rfl
TaskFrame.MinusValidOn F φ = PointTruth.ValidOn F φ        -- rfl
TaskFrame.PlusValidOn F φ  = PointTruth.ValidOn F φ        -- rfl
TaskFrame.StarValidOn F φ  = PointTruth.ValidOn F φ        -- rfl   ← the load-bearing one
ValidOnFrames P φ / StarValidOnFrames P φ  = PointTruth.ValidOnFrames P φ   -- rfl
ValidIn fc φ / StarValidIn fc φ            = PointTruth.ValidIn fc φ        -- rfl
Valid φ / MinusValid φ / PlusValid φ / StarValid φ = PointTruth.Valid φ     -- rfl
```

and then re-derives **eighteen** existing adapter names — six L, ten L⋆, one L⁻, one L⁺ — with
their statements copied character-for-character from the live source and proofs that are single
delegations. Green at `994/994` jobs.

**The one friction, and it is invisible to consumers.** Twelve of the eighteen delegations need
named-argument annotations (`(L := StarFormula) (φ := φ)`) because Lean's unifier cannot invert
`StarValidOnFrames P φ ≟ PointTruth.ValidOnFrames ?L ?φ` with the instance still a metavariable.
This is a *proof-body* detail of the wrapper. It never appears in a statement and never reaches a
downstream call site.

#### The clause layer, also settled by proof

```lean
class BoolCore (L : Type) where
  Env : TaskFrame → Type
  T : ∀ {F : TaskFrame}, TaskModel F → ConvexHistory F → F.Duration → Env F → L → Prop
  bot : L ; imp : L → L → L ; box : L → L
  bot_clause / imp_clause / box_clause : …
class UntlCore (L) extends BoolCore L where untl snce : L → L → L ; untl_clause snce_clause : …
class StabCore (L) extends UntlCore L where stab : L → L ; stab_clause : …
```

`Env` is `fun _ => PUnit` for L, L⁻, L⁺ and `fun F => ℕ → F.Duration` for L⋆; every instance's
three-to-six clause fields are `Iff.rfl` or `fun h => h`. The generic derived operators are
defined once from the class fields and coincide with the per-language ones **definitionally** —
probe 2 checks fourteen such `rfl`s, e.g. `Formula.neg φ = BoolCore.neg φ`,
`StarFormula.dstab φ = StabCore.dstab φ`, `Formula.always φ = UntlCore.always φ`.

Crucially, `PUnit` **never enters a preserved statement**: the generic lemma carries the `e`
binder, and the wrapper discharges it as `PUnit.unit` in its *proof*. The wrapper's statement is
the live one, unchanged.

#### Axiom parity (probe 3) — the `check-module-invariants.sh` constraint, measured

`#print axioms` on eleven existing declarations against their generic-delegating replacements:

| Declaration | Existing | Generic-delegating |
|---|---|---|
| `Truth.neg_iff` | `[propext]` | `[propext]` |
| `Truth.and_iff` / `or_iff` / `diamond_iff` / `future_iff` / `always_iff_tri` | `[propext, Classical.choice, Quot.sound]` | identical |
| `PlusTruth.and_iff` → `PlusTruth.dstab_iff'` | `[propext, Classical.choice, Quot.sound]` | identical |
| `StarTruth.dstab_iff`, `MinusTruth.diamond_iff` | `[propext, Classical.choice, Quot.sound]` | identical |
| `ValidOnFrames.of_forall_total` | `[propext]` | `[propext]` |
| `StarValid.apply` | `[propext]` | `[propext]` |

**Every pair matches.** Note in particular that the generic `neg_iff` was written to avoid
`by_contra`/`push_neg`, which is what keeps it at bare `[propext]` and preserves
`Truth.neg_iff`'s classical-freedom. The implementation must hold that line: a generic proof that
reaches for `by_contra` where the original did not *will* drift a baseline. This is a real,
avoidable hazard and belongs in the plan as a per-lemma check.

#### The honest boundary (deliverable 2's "partial abstraction" clause)

**One criterion covers every excluded declaration**: a class abstracts the truth *relation*, not
the inductive *type*. It provides no recursor, so any lemma proved by `induction φ` is out of
scope — its statement could be abstracted, but its proof could not, and the proof is the entire
cost.

Measured: `induction φ` occurs 5× in `Truth.lean`, 2× in `PlusTruth.lean`, 3× in `StarTruth.lean`,
1× in `PlusValidity.lean`, 0× in the four remaining files.

The prior-decision block flagged `starTruthAt_timeShift` as the expected divergence. **Confirmed,
and it is worse than flagged**: there are only **three** time-shift truth lemmas, not four, and
they carry **two different statements**:

- `Semantics/Truth.lean:804` `timeShift_preserves_truth` —
  `TruthAt M (σ.timeShift (y - x)) x φ ↔ TruthAt M σ y φ`, proved *not* by induction but through
  the `TruthCorr`/`shiftCorr` structure
- `Semantics/PlusTruth.lean:311` `plusTruthAt_timeShift` —
  `PlusTruthAt M (σ.timeShift Δ) t φ ↔ PlusTruthAt M σ (t + Δ) φ`, by induction
- `Semantics/StarTruth.lean:318` `starTruthAt_timeShift` — the same with
  `(fun i => v i + Δ)`, by induction
- **L⁻ has no time-shift truth lemma at all.**

So `timeShift` is not a four-way duplicate that a class could unify; it is a two-shape, three-site
family with three different proof routes. It stays per-language. `StarTruth.lean`'s design note
(a) already records why the vector must shift; nothing here is a defect.

Also outside: `truth_congr_ext` / `star_truth_congr_ext`, `stab_state_only`, `plusTruthAt_ofFormula`,
`starTruthAt_ofPlus`, `starValidOn_ofPlus`, `starValidOnFrames_ofPlus`, the `PlusStateLocal` /
`StarStateLocal` pair (29 and 30 declarations, structurally parallel but each proved by induction
over its own inductive), and the `SameStateAt` family.

#### Divergences the plan must not paper over

1. **L⁻ has `allPast`/`allFuture` as PRIMITIVE constructors**; L/L⁺/L⋆ derive them from
   `untl`/`snce`. So `MinusTruth.past_iff`/`future_iff` are `Iff.rfl` on constructor clauses while
   `Truth.past_iff`/`future_iff` are derived — and `MinusTruth.somePast_iff`/`someFuture_iff` run
   the classical duality in the *opposite* direction from the other three. L⁻ therefore needs its
   own small "allFuture-primitive" class, or its four temporal lemmas stay where they are. **This
   is the first genuine boundary, and it is on the syntax side, not the semantics side.**
2. **Binder conventions differ across the four files.** `MinusTruth.*` and `Truth.*` take
   `{M} {τ} {t}` implicit; `PlusTruth.*` and `StarTruth.*` take them explicit via a `variable`
   block. A single generic lemma cannot emit both shapes — which is a further reason the
   wrapper-per-name design is not merely convenient but *required*.
3. **`always` is not one lemma.** L has *two* (`always_iff` collected `∀ s`, tagged
   `@[simp, truth_norm]`; `always_iff_tri` untagged introduction form); L⁻ and L⋆ have *one* each
   (the tri form, under the name `always_iff`); **L⁺ has none**. `Truth.lean`'s docstring already
   warns that tagging both L forms `@[simp]` strands proofs — a hazard the refactor must not
   re-arm.
4. **Attribute sets differ.** L's clause lemmas carry `@[simp, truth_norm]`; L⁻'s carry `@[simp]`;
   L⁺/L⋆ carry `@[simp]` on `bot_false` only. The wrapper design preserves these for free (the
   wrapper *is* the named declaration); a "redefine the def as the generic one" design would not.

#### Survey corrections (deliverable 1 explicitly invites these)

| Survey item | Reality |
|---|---|
| `swapTemporal` | A **syntax** `def` in `Syntax/Formula.lean:672`, `PlusLanguage/Formula.lean:208`, `StarLanguage/Formula.lean:231` (L⁻ has `swapMinus`). **No validity-layer lemma of this name exists in `Semantics/`.** A formula→formula map is not abstractable by a truth-relation class. Out of scope. |
| `interpolates` | `TaskFrame.Interpolates` — a **frame** property. Zero per-language duplication. Out of scope entirely. |
| `sometimes` | Syntax `def` in three formula files; **no `sometimes_iff` truth lemma in any language**. Nothing to abstract. |
| `timeShift` | 3 declarations, 2 statements, 3 proof routes, L⁻ absent. Not abstractable (see boundary above). |
| "roughly 658 declarations" | Measured **1058** in the stated territory. |
| `dstab` | Correct: syntax `def` ×2 plus `dstab_iff` ×2. Both `dstab_iff` **are** abstractable (probe 2). |

#### Adjacent duplication the survey missed (report, do not necessarily scope in)

A **second** parallel family exists at the *consequence* layer, one level above validity:
`ConsequenceOnFrames` / `SemanticConsequenceIn` / `SemanticConsequence` (`Validity.lean`),
`MinusSemanticConsequence` (`MinusValidity.lean`), and the `Set`-indexed
`SetConsequenceOnFrames` / `SetSemanticConsequenceOn` (`Metalogic/SetConsequence.lean`) versus
`MinusSetConsequenceOnFrames` (`Metalogic/Conservativity/FragmentCompactness.lean`). It is the
same shape with a premise-set parameter added, and it would instantiate against the same
`PointTruth` class. Recommend scoping it as an **optional final phase**, gated on the core
landing green, not as a required deliverable.

Likewise `Metalogic/Deterministic/Validity.lean` carries `ValidDetIn`, `PlusValidDetIn` and
`PlusValidDeterminedIn`, each with its own `of_forall_total`/`apply_total` pair — six further
adapters that are instances of the same generic pair at a different frame predicate. Same
recommendation.

### External Resources

#### cslib design-precedent read — what transfers

**Verified at source**, not taken on report.

**(a) The mechanism cslib actually uses.** `Cslib/Foundations/Logic/Connectives.lean` defines
**one class per operator** — `HasBot`, `HasUntil`, `HasSince`, `HasNext` locally, plus upstream
`HasImp`/`HasAnd`/`HasOr`/`HasBox`/`HasDiamond` — and then **bundles by extension**:

```lean
class PropositionalConnectives (F : Type*) extends HasBot F, HasImp F where
  neg : F → F := fun φ => HasImp.imp φ HasBot.bot     -- defaulted field
  top : F      := HasImp.imp (HasBot.bot : F) HasBot.bot
class ModalConnectives          (F : Type*) extends PropositionalConnectives F, HasBox F
class FutureTemporalConnectives (F : Type*) extends PropositionalConnectives F, HasUntil F
class TemporalConnectives       (F : Type*) extends FutureTemporalConnectives F, HasSince F
class BimodalConnectives        (F : Type*) extends TemporalConnectives F, HasBox F
instance (priority := 100) [BimodalConnectives F] : ModalConnectives F where …
```

Its module docstring states the situation this repo is in, verbatim: *"Each concrete formula type
duplicates its constructors (Lean 4 cannot extend inductives) and registers as an instance of the
appropriate bundled class."* `Cslib/Foundations/Logic/Axioms.lean` then writes each schema once,
polymorphically, as `protected abbrev` under a namespace-level `variable {F : Type*}` with
`section` + `variable [HasBot F] [HasImp F]` **capability groups**; the derived operators
`top'`/`neg'`/`conj'`/`disj'` (`Axioms.lean:41,44,55,64`) are `abbrev` precisely so they stay
transparent by defeq at instantiation sites.

**TRANSFERS, and should be adopted**:

1. **One class per operator + bundling by `extends`, with capability groups.** My probe used a
   coarse three-level chain (`BoolCore` → `UntlCore` → `StabCore`); cslib's finer grain is
   strictly better here because it handles L⁻'s `allPast`/`allFuture`-primitive divergence
   cleanly (L⁻ instantiates `HasAllPast`/`HasAllFuture` instead of `HasUntl`/`HasSnce`) instead of
   forcing a second monolithic class. **Recommend the finer grain.**
2. **`abbrev`, not `def`, for the generic derived operators.** The `rfl` bridges in probe 2 pass
   with `def`, but `abbrev`'s reducibility is what keeps `simp` and unification well-behaved at
   the wrapper sites. Free to adopt.
3. **Defaulted class fields for shared derived connectives.** All four languages' `neg`/`top`/
   `and`/`or`/`diamond` are character-identical Lukasiewicz encodings (verified: `Syntax/Formula.lean:136,139,451,456,461`,
   `PlusLanguage/Formula.lean:132,135,156,159,165`, `StarLanguage/Formula.lean:152,155,176,179,185`,
   `MinusLanguage/Formula.lean:104,107,110,113,119`). cslib's defaulted-field idiom is the exact analogue.
4. **`protected abbrev` under a namespace-level `variable`, with `section`-scoped capability
   groups** — the module-organisation idiom for the new file.

**DOES NOT TRANSFER, with the reason**:

1. **cslib makes `and`/`or` PRIMITIVE (`HasAnd`/`HasOr`), rejecting the Lukasiewicz encodings**,
   because it must support minimal and intuitionistic logics where those encodings fail
   ([Wajsberg1938], [McKinsey1939] per its docstring). This repo's four languages are uniformly
   classical and all four *do* define `and`/`or` by the Lukasiewicz encodings. Adopting cslib's
   stance would require changing the formula types — forbidden outright by 577's hard
   constraints. **Keep Lukasiewicz-derived; abstract them as generic `abbrev`s.**
2. **cslib's `HasNext`-primitive rationale** (`next φ = φ U ⊥` fails in some models) is specific
   to LTL and has no counterpart here.
3. **`structure DerivationSystem (F : Type*) [HasImp F]` with the dictionary passed explicitly**
   (`Metalogic/Consistency.lean:56`) is the right shape where a type may carry *several*
   derivation systems. Here each formula type has exactly **one** truth relation, so instance
   inference (a `class`) is correct and an explicit dictionary would only add noise at every
   wrapper. **Choose the class.** cslib splits on exactly this principle — `class HilbertTree D` /
   `class HasMinimalAxioms Axioms` (`Foundations/Logic/Metalogic/GenericMCS.lean:177,195`) are
   instance-implicit because canonical per type, while `DerivationSystem` is an explicit argument
   because several coexist at `Proposition Atom`.
4. **The tag-alphabet shape itself (`ModalSchemaTag` + `SchemaUnion` + `Finset` + `decide`)**
   does not transfer. It is monomorphic in `Proposition Atom` and its entire payoff depends on a
   finite, `DecidableEq` alphabet with a meaningful `⊆` order. Four object languages are not
   elements of such an alphabet; there is no inclusion lattice to expose and nothing for `decide`
   to discharge.
5. **cslib's `module` / `public import` / `@[expose] public section` file headers** are tied to
   its toolchain and `lake shake --add-public` configuration. This repo is on Lean
   `v4.33.0-rc1` with a different lakefile; do **not** copy header shape verbatim without
   checking. What *does* transfer from `ORGANISATION.md`/`CONTRIBUTING.md` is the module-docstring
   discipline (a `## Design Invariants` section recording the properties the module must keep
   true — the natural home for 577's extension contract), the ~1500-line module ceiling with
   "split along the *dependency* structure, never by line count", and the rule that the generic
   layer imports nothing language-specific.

**(a′) cslib's own semantics layer is a NEGATIVE data point, and that matters.** cslib has three
different semantic point shapes — `Satisfies (m : Model) (w : World)`
(`Logics/Modal/Basic.lean:270`), `Satisfies (M : TemporalModel D Atom) (t : D)`
(`Logics/Temporal/Semantics/Satisfies.lean:66`), and `truthAt M Ω τ t`
(`Logics/Bimodal/Semantics/Truth.lean`) — and **abstracts none of them**. Each carries its own
duplicated `@[simp]` clause family: exactly the duplication 577 exists to remove. The only
semantics-side parametrisation anywhere in cslib is
`Foundations/Logic/LogicalEquivalence.lean:20`, which takes validity as a **bare function
parameter** `(Valid : Judgement → Sort w)`, not a class field.

Read this correctly: it is **not** evidence that the abstraction is impossible. It is evidence
that **no one has shown it done**, so this tree had to settle it on its own merits — which probes
1 and 2 did. It also means 577 lands something cslib's authors, working on the same problem
shape, did not attempt.

One adjacent cslib trick was considered and **rejected with a reason**: `Logics/Modal/Basic.lean:296-315`
bundles the point into `structure Judgement World Atom where mk :: (m) (w) (φ)` and abstracts over
the bundle, making arity differences vanish into the instance. Applied here, that would turn
`TaskFrame.ValidOn F φ = ∀ M (τ : F.HF) (x : F.Duration), …` into `∀ (j : Point F), …` — a
**changed binder shape on a preserved definition**, which constraint (4) forbids and which would
break every downstream `h M τ x` application. The `∀ v`-fold achieves the same arity-erasure
*without* touching any binder telescope, which is why it is the design that compiles.

**(b) Representation A vs. B (`docs/modal-axiom-schema-architecture.md` §6) — the most important
finding of the cslib read, and it is a WARNING, not a template.**

cslib chose **Representation A** (a tag alphabet `ModalSchemaTag` + `.Holds` + a `SchemaUnion`
`Finset` combinator) over **Representation B** (macro-generate the per-system inductives, keeping
every constructor name and elimination form verbatim). Its recorded reasoning, quoted:

> **Representation A costs.** The *elimination form* changes at every downstream destructuring
> site: `cases h_ax with | implyK … | modalK …` becomes `obtain ⟨t, ht, hφ⟩ := h_ax; fin_cases t
> <;> …`.
>
> **Representation B wins on migration safety.** Its near-zero downstream blast radius — every
> existing `cases`/`match` site keeps typechecking unchanged — and it delivers the literal DRY
> goal … without touching call sites at all.

cslib accepted A's downstream blast radius because it wanted the modal cube's lattice structure
to be *machine-checkable* — a goal 577 does not share. **Task 577 forbids exactly the cost cslib
accepted**: "no downstream consumer may require editing", "NO theorem may change its statement".
So 577's constraint profile is Representation **B**'s, not A's.

**The design proved green in probes 1 and 2 is the synthesis, and it is strictly better than
either.** The generic layer is A-shaped *internally* (DRY, one proof per fact); the per-language
names are preserved as thin wrappers with verbatim statements, so the downstream blast radius is
**zero** — B's benefit — without B's macro/elaborator machinery, which §6 also flags as
"metaprogramming maintenance burden … less transparent/auditable to a reviewer than a plain
`def`". This synthesis is available to 577 and was not available to cslib because cslib's
duplication was in *inductive constructors* (which cannot be wrapped) whereas 577's is in
*theorem statements* (which can).

**(b′) cslib's name-preservation idiom: `abbrev` redefinition-in-place — evaluated, and
PARTIALLY adopted.** cslib's dominant technique for keeping a name through a refactor is to
*redefine the name itself* as a one-line `abbrev` over the generic layer, preserving the public
API by defeq — `abbrev TAxiom : Proposition Atom → Prop := SchemaUnion tTags`
(`Instances/T.lean:37`), `abbrev S5Axiom := SchemaUnion s5Tags` (`DerivationTree.lean:69`).
`SchemaUnion.lean:43-46` records this as a *design invariant*: the generic shape is chosen so
that redefinition-in-place works. `@[deprecated] alias` appears exactly **once** in the whole
repo, reserved for genuine renames.

Applied here, this splits cleanly:

- **For the four `def`s per language** (`ValidOn`, `ValidOnFrames`, `ValidIn`, `Valid`),
  redefinition-in-place is available — probe 1 proved all twelve bodies are defeq to the generic
  ones. **But converting them from `def` to `abbrev` changes reducibility globally**, and `Valid`
  alone has 787 occurrences across the tree; `simp`, `unfold`, and instance search would all see
  a different transparency. **Recommendation: keep them `def`, and either leave the bodies as
  they stand (relying on the proven defeq) or replace each body with the generic call — but do
  NOT promote them to `abbrev`.** This is a plan-level decision to confirm empirically in phase 2,
  not to assume.
- **For the ~101 theorems**, redefinition-in-place is not applicable at all: a theorem's "body" is
  its proof, and the statement must be re-stated to be preserved. Wrappers are the only route,
  and they are what probes 1 and 2 verified.
- **For the generic derived operators**, `abbrev` (not `def`) — cslib's stated reason (transparent
  by defeq at instantiation sites) is exactly what makes the fourteen `rfl` bridges in probe 2
  hold, and `abbrev` makes them hold more robustly than the `def` the probe used.

**(b″) The elimination-form risk cslib names does not materialise here — and that is checkable,
not asserted.** cslib paid down Representation A's cost with a named `@[simp]` elimination API
(`SchemaUnion.{empty,insert,union}_iff`, `SchemaUnion.lean:173,182,197`). In this design **no
elimination form changes**, because no statement changes: a downstream `cases`/`rw`/`exact`
against `Truth.and_iff` sees byte-identical syntax before and after. **No bridge API needs to be
budgeted.** If any phase finds itself wanting one, that is the signal that a statement moved and
the phase must be reverted, not that an API is missing.

**(b‴) Notation-collision audit — performed, and it passes.** cslib flags this hazard sharply:
`Logics/Bimodal/Semantics/Validity.lean` uses `ℱ` for frames because `F` is scoped notation for
`Formula.someFuture`, and `NOTATION.md:53-82` prescribes positional `@` application over named
`(S := …)` inside such namespaces. **Checked here**: this repo's only notations in the affected
files are `△` (`Syntax/Formula.lean:628`), `▽` (`:635`), `⊨` (`Validity.lean:122,414`) — no
single-letter scoped notation. `F` is universally the `TaskFrame` section variable, which is why
the probes named the language type `L` and not `F`. **No collision; the design is safe as
written.** The plan should nonetheless keep `L` (not `F`) for the language parameter.

**(b⁗) cslib's "register the instance before the derived-connective abbrevs" ordering constraint
does not bite here**, because this refactor does **not** move `Formula.neg`/`PlusFormula.and`/etc.
into class fields — they stay exactly where they are in the four syntax files, and the generic
`abbrev`s are proved to coincide with them by `rfl`. Likewise cslib's "native constructors beat
encodings" note is moot: all four languages already have native constructors for everything the
validity layer touches, which is the cheap case cslib describes.

**(c) `unionSound` / `FrameCorrespondence` — confirms the deferred item D1's sequencing.**
`Cslib/Logics/Modal/Metalogic/SchemaSoundness.lean`'s `unionSound` + `FrameValidatesTag` collapses
15 per-system soundness proofs into one master lemma over an 18-entry validity table, consuming a
small library of `Satisfies.modal{T,Four,B,D,Five}_axiom` frame-correspondence lemmas. That is
squarely the deferred D1 shape, and it **consumes** a validity layer rather than providing one —
confirming the prior decision that D1 sits *above* 577. Do not pull it forward.

**No code was copied and no cslib dependency is proposed.** This was a design-precedent read.

### Recommendations

**A sorry-free path exists.** Nothing in this design requires a `sorry`, an axiom, or a weakened
statement; all three probes are green with zero errors.

**Recommended phase decomposition** (each phase one agent run, `lake build` + `lake build
BimodalTest` green, `check-module-invariants.sh` exit 0, no new `sorry`):

1. **New module `FormalSystem/Semantics/ValidityLayer.lean`** — the `PointTruth` class, the
   generic `ValidOn`/`ValidOnFrames`/`ValidIn`/`Valid`, both `mono`, the eight adapters, the three
   `of_not`. Imports `Semantics/TaskModel`, `Semantics/ConvexHistory`, `Semantics/FrameClassValidity`
   (for `ProofSystem.FrameClass`); sits **below** `Semantics/Validity.lean` in the import order.
   Must transitively import `FormalSystem.Init` (invariant C24) and follow the aggregator
   convention (C8). No instances yet — module compiles with the class alone.
2. **Instantiate L** in `Semantics/Validity.lean`: add the `PointTruth Formula` instance, replace
   each of the 20 category-A proof bodies with a delegation, leaving every statement byte-identical.
   Then delete nothing yet.
3. **Instantiate L⁻**, **L⁺**, **L⋆** — one phase each, same shape. L⋆ is the phase that carries
   the `∀ v` fold and the eight adapters; it is the one to run with the most care.
4. **New module `FormalSystem/Semantics/TruthClauses.lean`** — the operator classes
   (`HasBot`/`HasImp`/`HasBox`/`HasUntl`/`HasSnce`/`HasStab`/`HasAllPast`/`HasAllFuture` at
   cslib's grain, bundled by `extends`), the generic derived-operator `abbrev`s, and the eleven
   generic lemmas.
5. **Instantiate the clause layer per language** — one phase each; L⁻ instantiates the
   allPast/allFuture-primitive bundle, not the untl bundle.
6. **Sweep phase**: delete superseded duplicate *proof bodies* only (there are no superseded
   *declarations* — every name is preserved), re-run the full invariant harness, and write the
   extension contract into the new modules' docstrings **from the instantiations actually
   performed**.
7. *(Optional, gated on 1–6 green)*: the consequence layer and `Deterministic/Validity.lean`
   adapters (see "Adjacent duplication" above).

**Draft extension contract (deliverable 6), written from what the probes actually instantiated.**
A fifth object language `L₅` inherits the validity layer for free by supplying **one instance
with one field**:

```lean
instance : PointTruth L₅ where
  sat {F} M τ t φ := ∀ (extra binders, if any), L₅TruthAt M τ t (extras) φ
```

subject to two obligations, both of which the four current languages meet:

- **O1 (innermost-binder)**: every per-point parameter beyond `(M, τ, t)` must be the *innermost*
  binder of `TaskFrame.L₅ValidOn` and of every adapter. If it is not, the fold changes a binder
  telescope and the statement-preservation guarantee fails.
- **O2 (inert threading)**: those parameters must be threaded unchanged through the `imp`, `box`,
  `untl`, `snce` and `stab` clauses. (L⋆'s `timeStore`/`timeRecall` *do* touch `v` — which is fine,
  because they are extra constructors the shared core never mentions.)

**Inherited for free**: `ValidOn`, `ValidOnFrames`, `ValidIn`, `Valid`, `ValidOnFrames.mono`,
`ValidIn.mono`, `{ValidOn,ValidOnFrames,ValidIn,Valid}.{of_forall_total,apply_total}`,
`{ValidOnFrames,ValidIn,Valid}.of_not` — **fifteen declarations for one instance field.**

For the clause layer, additionally supply `HasBot`/`HasImp`/`HasBox` with `Env` = the extra-parameter
type and three clause fields (each `Iff.rfl` or `fun h => h`) → inherits `neg_iff`, `top_true`,
`and_iff`, `or_iff`, `diamond_iff`. Add `HasUntl`/`HasSnce` (two more `Iff.rfl`) → inherits
`someFuture_iff`, `somePast_iff`, `allFuture_iff`, `allPast_iff`, `always_iff_tri`. Add `HasStab`
(one more `Iff.rfl`) → inherits `dstab_iff`. **Eleven more declarations for six `Iff.rfl` lines** —
*provided* the language's `neg`/`top`/`and`/`or`/`diamond` are the Lukasiewicz encodings
character-for-character, which is what makes the `rfl` bridges hold.

**Explicitly NOT inherited**: anything proved by induction on `L₅` — time-shift, congruence,
state-locality, and any embedding bridge. Those are the price of a new inductive and the
abstraction does not pretend otherwise.

## Decisions

1. **`class` with instance inference, not `structure` with an explicit dictionary.** Each formula
   type has exactly one truth relation; cslib's explicit-dictionary idiom solves a problem this
   repo does not have.
2. **Wrapper-per-name preservation, not redefinition of the per-language `def`s.** Redefining
   `def StarValidOnFrames := PointTruth.ValidOnFrames` would be *defeq* and would compile, but it
   would change what `unfold`/`simp [StarValidOnFrames]` produces at 30+ downstream sites and would
   not preserve the divergent `@[simp, truth_norm]` attribute sets. Wrappers cost one line each and
   preserve everything.
3. **Adopt cslib's one-class-per-operator grain over the probe's coarse three-level chain**, on
   the strength of L⁻'s allPast/allFuture-primitive divergence.
4. **Do not adopt cslib's Representation A trade.** Its accepted cost is 577's forbidden outcome.
5. **`timeShift` stays per-language.** Recorded as the honest boundary, with the criterion named
   (no recursor from a relation-abstracting class) rather than as an isolated exception.
6. **Do not scope the consequence layer or `Deterministic/Validity.lean` into the core phases.**
   Report them; gate them.
7. **Do not promote `Valid`/`ValidIn`/`ValidOnFrames`/`ValidOn` from `def` to `abbrev`**, despite
   cslib's redefinition-in-place idiom being the natural fit. The reducibility change is global
   (`Valid` alone occurs 787 times) and would alter `simp`, `unfold` and instance-search
   behaviour tree-wide — a statement-preserving refactor must not change how those statements
   *elaborate*. Use `abbrev` only for the **new** generic derived operators, where cslib's
   transparency argument applies and nothing pre-existing is affected.
8. **Reject the bundled-`Judgement`/`Point` design** for erasing the arity difference: it changes
   `TaskFrame.ValidOn`'s binder shape and therefore every downstream application. The `∀ v`-fold
   erases the same difference at zero statement cost.

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| A generic proof reaches for `by_contra`/`push_neg` where the original was `rfl`/`id`, drifting an axiom baseline from `[propext]` to `[propext, Classical.choice, Quot.sound]` | **Measured hazard, not hypothetical.** Probe 3 shows the parity holds *because* the generic `neg_iff` avoids classical tactics. Plan must add a per-lemma `#print axioms` diff as a phase gate, and `check-module-invariants.sh` C2/C14 must be run at every phase, never only at the end. Baseline drift is a defect to investigate, never to rebaseline. |
| Elaboration-order failures in wrapper bodies (`?m` for the instance) | Known and solved: named-argument annotations `(L := X) (φ := φ)`. Probe 1 went from 26 errors to 0 by adding them. Cost is confined to proof bodies. |
| L's `always_iff` (collected) vs `always_iff_tri` — tagging both `@[simp]` strands proofs | `Truth.lean`'s own docstring records the reproduced failure. The generic layer must expose the tri form as the introduction lemma and leave the collected form as an L-only derived result; wrappers carry the existing attributes unchanged. |
| The four files' divergent implicit/explicit binder conventions | Wrapper-per-name design handles this by construction; a "one generic lemma, no wrapper" design cannot. Already the chosen design. |
| Territory is broad (1058 declarations) and 577 is sequenced last precisely because it touches everything | Phase 1 adds a leaf module with no instances — zero blast radius. Phases 2–5 are one language each, each independently green and independently committable. Nothing is deleted before its replacement is green. |
| `lean-lsp` MCP unavailable | Already mitigated: every claim in this report that could have been checked by hover was instead checked by compilation. The wrapper script `.claude/scripts/lean-lsp-mcp-wrapper.sh` is missing and should be restored, but it is not a blocker for this task. |
| Temptation to adopt cslib's `abbrev` redefinition-in-place for the four `def`s, changing reducibility tree-wide | Decision 7 forbids the `def`→`abbrev` promotion and states the measured reason (787 `Valid` occurrences). If a phase wants it, it must first demonstrate on a probe that `simp`/`unfold` behaviour is unchanged at every affected site. |
| Plan reaches for a `@[simp]` "bridge API" of the kind cslib needed to pay down Representation A's elimination-form cost | Wanting one is a **defect signal**, not a gap: in this design no statement changes, so no elimination form changes. Treat the impulse as evidence a statement moved, and revert. |
| New module must satisfy the invariant harness (C8 aggregator convention, C24 `FormalSystem.Init` reachability, C19 docstring coverage, C16 linter baseline) | Named explicitly in phase 1's acceptance criteria rather than discovered at the end. |

## Tactic Survey Results

No tactic-portfolio survey was performed: this task has no open proof goal to close. The
verification work was three compiled probes, whose results are reported above in place of a tactic
table. For completeness, the tactics the generic proofs actually needed:

| Goal family | Tactic | Result | Notes |
|---|---|---|---|
| generic `neg_iff` | `rw` + explicit terms | success | deliberately avoids `by_contra`; this is what preserves `[propext]`-only |
| generic `and_iff`, `or_iff`, `diamond_iff`, `dstab_iff` | `rw` + `by_contra` / `by_cases` / `push_neg` | success | classical; matches the originals' axiom set exactly |
| generic `always_iff_tri` | `rw [always, and_iff, and_iff, allPast_iff, allFuture_iff]` | success | closes by `rw` alone |
| all 12 definitional bridges | `rfl` | success | the load-bearing result of probe 1 |
| all 14 derived-operator bridges | `rfl` | success | probe 2 |
| `always_iff` collected form (`∀ s`) | `lt_trichotomy` | success | needed the frame's own `LinearOrder`; an added `[LinearOrder F.Duration]` binder *fails* with an instance-diamond mismatch against `instDistribLatticeOfLinearOrder` — recorded so the implementation does not re-hit it |

## Context Extension Recommendations

- **Topic**: The `lean-lsp` MCP server wrapper.
  **Gap**: `.claude/scripts/lean-lsp-mcp-wrapper.sh` does not exist, so every lean-lsp tool named
  in the lean extension's agent contracts was unavailable this session (ENOENT at spawn).
  **Recommendation**: restore or regenerate the wrapper from `agent-system/extensions/lean/`;
  until then, the extension's "Allowed Tools" section overstates what an agent can actually reach,
  and its blocked-tool alternatives ("use `lean_goal` instead") are themselves unavailable.

- **Topic**: Statement-preserving refactor idiom for Lean.
  **Gap**: No context file records the "generic core + verbatim-statement wrapper" pattern, its
  elaboration-order caveat (`(L := X)` named arguments), or the `#print axioms` parity check that
  must accompany it. This pattern is reusable well beyond this task.
  **Recommendation**: add `context/project/lean4/patterns/statement-preserving-abstraction.md`.

- **Topic**: cslib as a design-precedent corpus.
  **Gap**: The cslib read produced a durable, transferable verdict (its Representation A/B
  deliberation, its operator-class grain, its Lukasiewicz-vs-primitive divergence) that will be
  re-derived by the next task that looks at cslib.
  **Recommendation**: record the transfer/non-transfer table in
  `context/project/cslib/design-precedents.md`.

## Appendix

### Probes (archived, compiled, then removed from `FormalSystem/`)

| Probe | Question | Result |
|---|---|---|
| `probes/01_validity-layer.lean.txt` | Does one `PointTruth` class cover `(τ,x)` and `(τ,x,v)`? Do the existing defs coincide definitionally? Can all 18 adapters be re-derived verbatim? | **Green**, 994/994 jobs, 0 errors |
| `probes/02_clause-layer.lean.txt` | Does the derived-operator family abstract over an `Env`-parameterised clause class, across all four languages? | **Green**, 0 errors |
| `probes/03_axiom-parity.lean.txt` + `-output.txt` | Do the generic-delegating replacements have the same axiom sets as the originals? | **Identical for all 11 pairs** |

Build invocation used throughout (per `context/project/lean4/operations/long-builds.md`):
`bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build <Module>` under
`Bash(run_in_background: true)`.

### Key source anchors

- `FormalSystem/Semantics/Truth.lean:240` `TruthAt`; `:429,435,440,448,457` the Boolean derived family; `:804` `timeShift_preserves_truth`
- `FormalSystem/Semantics/MinusTruth.lean:107` `MinusTruthAt` (note `allPast`/`allFuture` primitive)
- `FormalSystem/Semantics/PlusTruth.lean:120` `PlusTruthAt`; `:311` `plusTruthAt_timeShift`; `:380` `stab_state_only`
- `FormalSystem/Semantics/StarTruth.lean:110` `StarTruthAt`; `:318` `starTruthAt_timeShift`
- `FormalSystem/Semantics/Validity.lean:274,359,370,408` the four L validity defs; `:484–572` the adapter block and its "Two triples, and no more than two" note
- `FormalSystem/Semantics/StarValidity.lean:74–160` the L⋆ mirror, `v` innermost throughout
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Connectives.lean:135–219` the operator/bundle class hierarchy
- `/home/benjamin/Projects/cslib/Cslib/Foundations/Logic/Axioms.lean:41,44,55,64` the `abbrev` derived operators
- `/home/benjamin/Projects/cslib/docs/modal-axiom-schema-architecture.md:419–466` Representation A vs B

### Searches performed

Codebase only (no external search was warranted; `lean-lsp` was unavailable, see Risks):
declaration enumeration across the four territory directories; `swapTemporal`, `interpolates`,
`sometimes`, `dstab`, `timeShift`, `of_forall_total`/`apply_total` call-site counts;
`induction φ` occurrence counts; `@[simp]`/`@[truth_norm]` attribute inventory; cslib greps for
`ModalSchemaTag`, `SchemaUnion`, `unionSound`, `FrameCorrespondence`, `HasAxiom`.
