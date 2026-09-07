# Naming Convention Deviations

This file records two separate naming questions. The first, `defsWithUnderscore`, is **closed**.
The second, the `ZTime` / `RTime` frame-class tag names, is **in force** and is written up under
[The frame-class tag names](#the-frame-class-tag-names-ztime--rtime) below.

## `defsWithUnderscore` — CLOSED

**Status: closed.** The deviation this section recorded no longer exists. The migration it named
as its successor has landed: every affected declaration was renamed to Mathlib conventions,
every `defsWithUnderscore` entry was dropped from `scripts/nolints.json`, and
`lake exe batteries/runLinter FormalSystem` reports `defsWithUnderscore = 0` by genuine
conformance.

This file is retained rather than deleted because two things in it survive the migration: the
architectural root cause, which is still true and still shapes the `Theorems/` layer, and the
operational warning about what does and does not count as evidence for this linter.

## Outcome

| Measure | Before | After |
|---|---|---|
| `defsWithUnderscore`, unmasked | **861** | **0** |
| `scripts/nolints.json` `defsWithUnderscore` entries | 860 | **0** (the file survives, carrying only the grandfathered `docBlame` rows) |
| Inline `@[nolint defsWithUnderscore]` attributes | 0 | **7**, all on auto-generated `tactic*` names |
| `unusedArguments` | 124 | 124 |
| `LINTER FAILED` | 115 | 115 |
| `docBlame` | 39 | 39 |
| `tacticDocs` | 4 | 4 |
| `structureInType` | 1 | 1 |

Every sibling category is unchanged to the unit, which is the evidence that the count fell by
conformance rather than by silencing something.

Alongside the renames, the library root moved from `Theories/Bimodal/` to `FormalSystem/` and the
root namespace `Bimodal` became `FormalSystem`.

## The naming rule now in force

Keyed on what a declaration *produces*, not on which command declares it:

| Declaration produces | Convention | Example |
|---|---|---|
| data (including all `DerivationTree`-valued results) | lowerCamelCase | `allFuture`, `swapTemporal` |
| a `Prop` — i.e. it *defines a predicate* | UpperCamelCase | `TruthAt`, `TemporalTruth`, `IsRDefinableGap` |
| a `Sort`/`Type` | UpperCamelCase | `TaskFrame` |
| a proof (`theorem`/`lemma`) | snake_case | `soundness`, `truth_lemma` |

The `Prop`-valued row is the one that surprises. `α → Prop` has type `Type`, not `Prop`, so a
predicate definition **cannot** be restated as a `theorem` — the conversion is a type error, not
a judgement call. 121 declarations fell in this category, `Semantics.TruthAt` (515 resolved
usages) among them.

## The architectural root cause — still true

`DerivationTree`, defined in
[`FormalSystem/ProofSystem/Derivation.lean`](../../FormalSystem/ProofSystem/Derivation.lean), is
`Type`-valued rather than `Prop`-valued. Every derived result built from it therefore *must* be a
`def` rather than a `theorem` — and `def` is precisely what this linter inspects. A result that is
mathematically a theorem is forced by the encoding into the syntactic category the linter treats
as data.

The `Type`-valued encoding is load-bearing, not incidental:

- `DerivationTree.height` is a computable `Nat`-valued recursor over the tree, with dozens of
  references. It cannot be recovered from a `Nonempty` witness.
- The `Automation/` proof-search layer consumes actual derivation trees — it inspects and
  transforms proof structure, so `Nonempty (DerivationTree …)` would not serve.

**What the migration changed about this argument**: nothing structural. The `Theorems/` layer is
still 135-of-135 `DerivationTree`-valued and still declared with `def`. What changed is the
conclusion drawn from it. The old reading was that a mathematically-theorem-shaped result
deserves a theorem's `snake_case` name and the linter should be suppressed. The rule that
actually applies keys on the syntactic category, so those declarations now take lowerCamelCase
(`impTrans`, `perpetuity3`, `boxMono`) and the linter is satisfied without any exemption.

**Scope of the explanation, unchanged.** It was always precise for `Theorems/` and never extended
to the ordinary data definitions elsewhere in the library, whose names were a plain stylistic
choice. The migration confirmed the proportion: the churn was dominated by data names, not by the
mathematical layer.

## How to re-audit: a green build still proves nothing here

This remains the single most important operational fact in this document, and deleting
`nolints.json` did not change it.

`defsWithUnderscore` is an *environment* linter. It emits **nothing** during `lake build`, and CI
runs `lean-action` with `lint: false`. A green build therefore carries **no information** about
this category. The only gate that observes it is an explicit:

```
lake exe batteries/runLinter FormalSystem
```

Plain `lake exe runLinter` fails — the package declares no `lintDriver`. Expect
`defsWithUnderscore` to be absent from the output, and the sibling categories to remain live and
unchanged at the counts tabulated above.

> **Trap when parsing the output.** batteries pretty-prints `@Name` for declarations with
> implicit arguments. A parser that does not strip the leading `@` silently loses **425 of 861**
> names — measured, not estimated.

## The surviving exemptions, and why they are not a new suppression file

Seven in-source attributes in
[`FormalSystem/Automation/Tactics/Helpers.lean`](../../FormalSystem/Automation/Tactics/Helpers.lean):

```lean
attribute [nolint defsWithUnderscore]
  tacticApply_axiom          -- from the `apply_axiom` tactic token
  tacticModal_t              -- from the `modal_t` tactic token
  tacticAssumption_search    -- from the `assumption_search` tactic token
  tacticModal_k_tactic       -- from the `modal_k_tactic` tactic token
  tacticTemporal_k_tactic    -- from the `temporal_k_tactic` tactic token
  tacticModal_4_tactic       -- from the `modal_4_tactic` tactic token
  tacticModal_b_tactic       -- from the `modal_b_tactic` tactic token
```

Each of these names is **auto-generated by Lean** from a tactic token: `macro "modal_t" : tactic`
produces a declaration called `tacticModal_t`. The underscore is inherited from the token, and
every Lean tactic token is snake_case (`simp_all`, `norm_num`, `push_neg`, `field_simp`).

Mathlib has exactly the same declarations and escapes the linter not by camelCasing them but
because `isBadNameWithUnderscore` (`Mathlib/Tactic/Linter/Style.lean`) whitelists the
`Mathlib.Tactic` namespace prefix outright. This repository's tactics live under
`FormalSystem.Automation`, so they are not covered by that whitelist.

The seven exempted tokens are the ones referenced from `docs/`, where renaming would be a
user-facing API break. Internal-only tokens were renamed instead rather than exempted:
`modal_norm`, `prop_norm`, `modal_op_norm`, `temporal_norm`, `modal_norm_all`, `modal_norm_at`,
`modal_fold`, `prop_decide`, `order_refl`, `order_rev`, `same_order_type_grid`,
`same_order_type_grid_uh`, and the `tm_lemma` label attribute.

**Why this is categorically different from the deleted entries.** A per-declaration in-source
attribute is reviewable in the diff that introduces it, states its reason at the site, and
travels with the declaration. A central JSON list accumulates entries nobody re-justifies — and
it fails silently: during this migration, renaming the root namespace made all 860
fully-qualified entries stop matching at once, and the masked count jumped from 284 to 1144
without a single line of the file changing. That failure mode is a property of the mechanism,
not an accident.

## What would reopen this

Nothing about the naming rule itself; full Mathlib conformance is now the settled convention and
is recorded in [`LEAN_STYLE_GUIDE.md`](LEAN_STYLE_GUIDE.md). The remaining live question is
narrower: if Mathlib's linter ever stops whitelisting the `Mathlib.Tactic` prefix and starts
requiring camelCase tactic tokens, the seven exemptions above become renames.

## The frame-class tag names: `ZTime` / `RTime`

A second, unrelated naming question was settled separately, and this is its record.

### The two senses that had to be told apart

The words *Discrete* and *Dedekind* were doing two different jobs in this tree at once:

1. Naming a **`FrameClass` tag** — `FrameClass.Discrete`, `FrameClass.Dedekind`, and everything
   derived from them (`TaskFrame.IsSuccArchDiscrete`, `ValidDedekind`, `soundness_discrete`,
   `completeness_dedekind`, the tableau rule sets, the CLI string literals).
2. Naming the paper's **bare order conditions** and the order-theoretic property — `IsDiscrete`
   and `IsComplete` from `def:frame-properties`, "Dedekind-complete", "Dedekind cut", and the
   ~560-occurrence Dedekind-INF/SUP API under `Metalogic/WeakCanonical/Kamp/`.

Sense 1 was renamed; sense 2 was not.

### The scheme now in force

One scheme, three casings, applied by grammatical position:

| Position | Old | New | Example |
|---|---|---|---|
| PascalCase (types, constructors, `Prop`-valued defs) | `Discrete` / `Dedekind` | `ZTime` / `RTime` | `ValidDedekind` -> `ValidRTime` |
| lowerCamel (segment naming a PascalCase def) | `discrete` / `dedekind` | `zTime` / `rTime` | `discreteRules` -> `zTimeRules` |
| snake_case (lemma-name segment) | `discrete` / `dedekind` | `ztime` / `rtime` | `soundness_dedekind` -> `soundness_rtime` |
| String literal emitted for a class | `"Discrete"` / `"Dedekind"` | `"ZTime"` / `"RTime"` | `Automation/MachineAppendixExport.lean` |
| String literal parsed as CLI input | `"discrete"` / `"dedekind"` | `"ztime"` / `"rtime"`, legacy spellings still accepted | `Automation/DatasetExport.lean` |

`ZTime` and `RTime` name what the classes *are* — ℤ-time and R-time, which by
`Semantics.complete_duration_discrete_or_dense` and Hölder are, up to order-and-group
isomorphism, exactly `ℤ` and `ℝ`.

### Why the tags were renamed at all

`def:frame-properties` calls the dense-and-complete class **Complete**, and "complete" is already
load-bearing in this tree for *proof-theoretic* completeness (`completeness`, `completeness_dense`,
`completeness_ztime`, `completeness_rtime`, `Metalogic/StrongCompleteness.lean`). A
`TaskFrame.IsComplete`-versus-`FrameClass.Complete` pair would collide with the tree's most-cited
word at exactly the point where the two senses meet. `Dedekind` avoided the collision but
introduced a second one, against the Dedekind-INF/SUP API. Naming the classes for their carriers
resolves both at once, and it lets the bare conditions keep the paper's own names.

### The deviation that survives, stated plainly

**The frame *classes* take z/r names; the frame *conditions* keep the paper's names.** So
`FrameClass.ZTime` is interpreted by `TaskFrame.IsZTime`, which is strictly stronger than the
paper's bare `TaskFrame.IsDiscrete`; and `FrameClass.RTime` is interpreted by
`TaskFrame.IsRTime`, which is `IsDense ∧ IsComplete` — strictly stronger than the paper's bare
Complete clause. `Semantics/FrameProperty.lean` and `Semantics/FrameClassValidity.lean` argue
both narrowings at their definition sites. Prose that names an order *property* therefore still
reads "Discrete", "Dense", "Complete", "Dedekind-complete"; prose that names a *tag* reads
`Base`, `Dense`, `ZTime`, `RTime`. `typst/FormalFoundations.typ` is written in the paper's
vocabulary throughout and keeps the property names except where it explicitly names a frame class
or cites a Lean identifier.

### Deferred: module and file names

Module and file names were deliberately **not** renamed:
`Metalogic/DedekindNonCompactness.lean`, `Metalogic/DiscreteNonCompactness.lean`,
`Metalogic/BXCanonical/CompletenessDedekind.lean`, `Theorems/DedekindDerived.lean`,
`Theorems/DiscreteUnfolding.lean`, `Metalogic/BXCanonical/DiscreteCarrierProbe.lean`.
Renaming them churns import lines tree-wide and invalidates the
`#leansrc("Metalogic.BXCanonical.CompletenessDedekind", ...)` citations in
`typst/FormalFoundations.typ` plus the module path in `scripts/check-module-invariants.sh`, for
no semantic gain. The residual inconsistency is real and is recorded here rather than left
implicit: **a file named for the old tag can declare identifiers named for the new one** — for
instance `Metalogic/DedekindNonCompactness.lean` declares `notCompactRTime`. `Kamp/DedekindINF.lean`
and `Kamp/DedekindINFDense.lean` are *correctly* named for the INF/SUP sense and are never in
scope for a rename.

### Also kept

`layerReynoldsDedekind` (`Automation/MachineAppendixExport.lean`) labels the Reynolds axiom
family, which genuinely encodes definable Dedekind completeness rather than the frame class. The
five `Axiom.discrete_*` constructors (`discrete_symm_fwd`, `discrete_symm_bwd`,
`discrete_propagate_fwd`, `discrete_propagate_bwd`, `discrete_box_necessity`) are Base-valid
uniformity axioms about discreteness, not class-specific axioms, and keep their names.

## Related

- [`LEAN_STYLE_GUIDE.md`](LEAN_STYLE_GUIDE.md) — the naming conventions, now describing the
  settled state rather than a deviation from it
- [`FormalSystem/ProofSystem/Derivation.lean`](../../FormalSystem/ProofSystem/Derivation.lean)
  — the `Type`-valued `DerivationTree` that forces `def` over `theorem`
- [`FormalSystem/Boneyard/README.md`](../../FormalSystem/Boneyard/README.md) — the one tree
  deliberately left un-migrated
