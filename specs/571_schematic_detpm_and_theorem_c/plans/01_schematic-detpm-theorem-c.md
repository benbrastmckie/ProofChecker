# Implementation Plan: Schematic `Det-pm` and Theorem C in its strongest form

- **Task**: 571 - Remove the atom restriction from Det-pm and state Theorem C in its strongest form
- **Status**: [IMPLEMENTING]
- **Effort**: 4 hours
- **Dependencies**: None
- **Research Inputs**: None (no `research_path` supplied; the task description carries the ground
  truth and the codebase reads below confirm it — see "Opening assessment" in the Overview)
- **Artifacts**: plans/01_schematic-detpm-theorem-c.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md,
  .claude/rules/plan-compliance.md, .claude/rules/lean4.md,
  .claude/rules/no-task-references-in-deliverables.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

`FormalSystem/Semantics/StarDeterminism.lean` defines `detPM (p : Atom) : StarFormula`, so the
atom restriction sits in the **definition**, not merely in a theorem. Its sibling `sentDet` is
already schematic and both run on the same schematic engine `settledDisj_of_deterministic`, so
the restriction is an artifact of matching the converse's hypothesis and not a mathematical
limit. This plan widens the definition to a `StarFormula` argument, restates the (⇐) direction
schematically, holds the (⇒) direction's hypothesis at atoms (where it is at its strongest), and
replaces the two-way `deterministic_starDefinable` with a three-way equivalence hinged on
`F.Deterministic`. Definition of done: `lake build` and `lake build BimodalTest` green,
`bash scripts/check-module-invariants.sh` exit 0, zero new `sorry`, and every `#print axioms`
figure asserted in a docstring equal to the measured value.

### Opening assessment (why no research phase)

The description is a specification, not a research question: it names the defect, the file, the
exact target signatures, and the acceptance bar. Targeted reads confirmed every load-bearing
fact within this dispatch's own budget, so a research round would add nothing:

- `FormalSystem/Semantics/StarDeterminism.lean:173` — `def detPM (p : Atom) : StarFormula`,
  confirmed; `detPM_unfold` (`:184`), `detPM_of_deterministic` (`:212`),
  `deterministic_of_detPM` (`:235`), `deterministic_starDefinable` (`:266`).
- `FormalSystem/Semantics/StarValidity.lean:176,187` — `settledDisj φ` and
  `sentDet φ` are already schematic; `sentDet` is literally `detPM`'s shape with `allFuture` in
  place of `always`.
- **No Lean consumer of `detPM` exists outside `StarDeterminism.lean`.** A repo-wide grep for
  `detPM` and `deterministic_starDefinable` across `*.lean` returns only that module plus
  prose mentions in `FormalSystem/Semantics/README.md:39`,
  `FormalSystem/StarLanguage/README.md:56,81`, `FormalSystem/StarLanguage.lean:29`,
  `FormalSystem/Metalogic/Independence/README.md:29`, and
  `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean:304`. The blast radius of
  the widening is therefore one Lean file plus four prose sites.

### Measured axiom baseline (recorded now, so no docstring invents a false claim)

Measured this dispatch against the built library (`lake env lean` on a scratch
`import FormalSystem` file):

| Declaration | `#print axioms` (measured, pre-change) |
|---|---|
| `FormalSystem.Semantics.settledDisj_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
| `FormalSystem.Semantics.sentDet_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
| `FormalSystem.Semantics.detPM_of_deterministic` | `[propext, Classical.choice, Quot.sound]` |
| `FormalSystem.Semantics.deterministic_of_detPM` | `[propext, Classical.choice, Quot.sound]` |
| `FormalSystem.Semantics.deterministic_starDefinable` | `[propext, Classical.choice, Quot.sound]` |

**All five are identical.** This is the single most important fact for the choice-bookkeeping
deliverable: the choice asymmetry is **not** visible in `#print axioms` and must never be written
as though it were. The (⇐) direction's `Classical.choice` is ambient in the L⋆ apparatus
(`StarTruth`'s classical `or_iff`), exactly as `sentDet_of_deterministic`'s existing docstring
already says at `:146-149`. The asymmetry is **structural** and must be stated structurally: the
(⇐) direction routes through `states_eq_of_deterministic` via `star_truth_congr_ext` and adds no
extension-theorem step; the (⇒) direction routes through `deterministic_of_singletonClasses`
(`Semantics/DeterministicBridge.lean`) and hence through `thm:extension` and Zorn's lemma.

### C2 / C14 axiom baselines: no edit expected

`scripts/check-module-invariants.sh`'s C2 baseline pins four `Metalogic.BXCanonical.*` theorems
and C14's baseline pins the consequence/compactness/strong-completeness stack. Neither list
contains any `detPM`, `starDefinable`, `sentDet`, or `settledDisj` name — verified by grep of the
script. **No baseline edit is anticipated.** If a run nonetheless reports C2/C14 divergence, the
sanctioned response is to update the pinned **name** only and never its axiom set; a changed
axiom set is a hard stop, not a new baseline.

### Research Integration

No research report exists for this task. The description supplied the ground truth and the
targeted codebase reads above confirmed it.

### Prior Plan Reference

No prior plan for this task. The originating work is
`specs/561_store_recall_deterministic_frame_characterization/plans/01_store-recall-deterministic-characterization.md`
(phases 9-10), which built `detPM` at an atom in the first place, and whose summary records the
open item this task closes: "the single-`p` strengthening of `deterministic_starDefinable`".
That prior plan is **reference context only**; none of its phases are reused here.

### Roadmap Alignment

No `roadmap_path` was supplied in the dispatch context, so `specs/ROADMAP.md` was not consulted
as a plan input and no roadmap phases are added.

## Goals & Non-Goals

**Goals**:
- Widen the definition so `detPM` takes a `StarFormula`, with `detPM (StarFormula.atom p)`
  literally the former atom instance.
- Deliver the five declarations `detPM`, `detPM_unfold`, `detPM_of_deterministic`,
  `deterministic_of_detPM`, `deterministic_starDefinable` at the signatures pinned in
  `## Lean Challenge Statements` below.
- State Theorem C as a three-way equivalence under the single name `deterministic_starDefinable`,
  whose docstring says plainly that the **atomic fragment already forces** determinism while
  determinism **delivers the full schema**.
- Rewrite the module docstring's choice-asymmetry and single-sentence-letter sections to match
  the new statement, with every asserted `#print axioms` figure equal to the measured value.
- Update `FormalSystem/StarLanguage/README.md`'s paper-label correspondence row for Theorem C so
  it names the three-way statement, plus the three other prose sites that inventory these names.

**Non-Goals**:
- Widening `deterministic_of_detPM`'s hypothesis. It stays `∀ p : Atom, …` — that is the weakest
  hypothesis and precisely the strength of the converse. A widened definition must not tempt a
  widened hypothesis.
- Any appeal to uniform substitution. It is unsound here and the module docstring already records
  why (`p → ⊡p` is frame-valid over the drift frame `F°` while `Fp → ⊡Fp` is refutable over it).
- A choice-free (`Classical.choice`-free) pin for either direction. None exists today, none is
  claimed, and the measured baseline above shows all five declarations already carry
  `Classical.choice` from the ambient L⋆ apparatus.
- Any change to `sentDet`, `settledDisj`, `sentDet_of_deterministic`, or
  `settledDisj_of_deterministic`. The engine is already schematic and is consumed, not touched.
- A `Det-m` (world-register) half, a single-fixed-letter strengthening, or any new frame-class
  result.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The widening is read as license to widen `deterministic_of_detPM`'s hypothesis to `∀ φ` | H | M | Explicit Non-Goal above; the hypothesis is pinned verbatim in `## Lean Challenge Statements`; Phase 2's verification re-reads the signature |
| The type-forced rewrite `detPM p` → `detPM (StarFormula.atom p)` is mistaken for a weakened restatement under the same name (plan-compliance.md, Statement Fidelity) | M | M | It is the **same proposition** after the definition widens, not a weakening. Phase 1 records this in the commit message and the phase notes; the Challenge signatures are the contract |
| A docstring asserts a choice-free pin or an axiom-set difference that `#print axioms` does not show | H | M | The measured baseline is recorded above; Phase 3 re-measures after the change and gates every asserted figure on the measured value; the asymmetry is written structurally, never as an axiom-set difference |
| `#print axioms` figures go stale relative to C14's markdown+`.lean` staleness scan | M | L | Phase 5 runs `scripts/check-module-invariants.sh` in full; C14(i) scans `FormalSystem/*.lean` docstrings |
| A prose site still inventories the old two-way statement after the change | M | M | Phase 4 owns all four prose sites, enumerated by name; Phase 5 re-greps for `starDefinable` repo-wide |
| C17's dead-declaration census flags a newly introduced name | L | L | The name `deterministic_starDefinable` is retained rather than replaced, so its four existing prose references keep it live; C17 is reporting-only and never gates |
| A task number leaks into `FormalSystem/**` prose | M | L | C9 gates it at exit 0; the write-time hook `validate-no-task-references.sh` blocks it earlier |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3, 4 | 2 |
| 4 | 5 | 3, 4 |

Phases within the same wave can execute in parallel. **Territory contract for wave 3**: Phase 3
owns `FormalSystem/Semantics/StarDeterminism.lean` exclusively; Phase 4 owns
`FormalSystem/StarLanguage/README.md`, `FormalSystem/Semantics/README.md`,
`FormalSystem/StarLanguage.lean`, and `FormalSystem/Metalogic/Independence/README.md`
exclusively. Neither may edit the other's files.

---

### Phase 1: Widen `detPM` and `detPM_unfold` to a `StarFormula` argument [COMPLETED]

**Goal**: Deliverable (1). `detPM` takes a `StarFormula`; every mention in the module retypes in
the same edit so the build is green at the phase boundary.

**Tasks**:
- [x] Change `def detPM (p : Atom) : StarFormula` to
      `def detPM (φ : StarFormula) : StarFormula := .timeStore 1 (StarFormula.always (.timeStore 2 (.timeRecall 1 (settledDisj φ))))`
      — the body is unchanged apart from `StarFormula.atom p` becoming `φ`, so
      `detPM (StarFormula.atom p)` is definitionally the former atom instance.
- [x] Widen `detPM_unfold` to `(φ : StarFormula)`, replacing both occurrences of
      `settledDisj (StarFormula.atom p)` in its statement and its `hQ` have-block by
      `settledDisj φ`. The proof body (the `hQ` block, `unfold detPM`, the trichotomy split) is
      unchanged.
- [x] Retype `detPM_of_deterministic`'s conclusion to `F.StarValidOn (detPM (StarFormula.atom p))`
      so the file compiles. **This is a holding edit only** — Phase 2 widens it to `φ`; do not
      change its proof body here.
- [x] Retype `deterministic_of_detPM`'s hypothesis to
      `(h : ∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p)))`. This is **the same
      proposition** as before the widening, not a weakened restatement: `detPM (StarFormula.atom p)`
      unfolds to exactly the old `detPM p`. The proof body is unchanged (`(h p)` still applies).
- [x] Retype `deterministic_starDefinable`'s statement to
      `(∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p))) ↔ F.Deterministic`, proof body
      adjusted only as the elaborator requires. **Holding edit only** — Phase 2 replaces the
      statement.
- [x] Run `lake build` and `lake build BimodalTest`; both must be green with zero new `sorry`.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Commit Mode**: atomic-batch

**Scope Hypothesis**: The plan asserts that the widening's Lean call sites are confined to
`FormalSystem/Semantics/StarDeterminism.lean` (five declarations: `detPM`, `detPM_unfold`,
`detPM_of_deterministic`, `deterministic_of_detPM`, `deterministic_starDefinable`) and that no
other `.lean` file mentions `detPM`. Confirm at implementation time with
`grep -rn "detPM" --include='*.lean' FormalSystem/ Tests/` before editing and with a green
`lake build` after. If any other Lean file appears, stop and widen this phase's declared batch
explicitly rather than editing outside it.

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` — the definition, the unfold lemma, and the three
  type-forced retypes.

**Verification**:
- `grep -n "def detPM" FormalSystem/Semantics/StarDeterminism.lean` shows `(φ : StarFormula)`.
- `lake build` and `lake build BimodalTest` exit 0.
- `grep -rn "sorry" FormalSystem/Semantics/StarDeterminism.lean` returns nothing.
- `deterministic_of_detPM`'s hypothesis still binds `p : Atom` — confirmed by reading the
  signature, not by a name-existence check.

---

### Phase 2: Schematic `detPM_of_deterministic` and the three-way Theorem C [NOT STARTED]

**Goal**: Deliverables (2), (3), and (4). The (⇐) direction becomes schematic in `φ`; the (⇒)
direction's hypothesis stays at atoms; `deterministic_starDefinable` becomes the three-way
equivalence.

**Tasks**:
- [ ] Restate `detPM_of_deterministic (hD : F.Deterministic) (φ : StarFormula) :
      F.StarValidOn (detPM φ)`. Its proof consumes `settledDisj_of_deterministic` **exactly as
      `sentDet_of_deterministic` does** — `refine TaskFrame.StarValidOn.of_forall_total ?_`,
      `intro M τ hτ x v`, `rw [detPM_unfold]`, `intro y`,
      `exact settledDisj_of_deterministic hD M hτ x _ φ`. Do not route it through any other
      lemma, and add no extension-theorem step: it must reach `states_eq_of_deterministic`
      through `star_truth_congr_ext` (via `star_congr_of_deterministic`) and nothing else.
- [ ] Leave `deterministic_of_detPM` exactly as Phase 1 left it. Its hypothesis stays
      `∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p))`. Do not widen it, do not restate
      it, do not add a `∀ φ` variant under its name.
- [ ] Replace `deterministic_starDefinable`'s statement with the three-way equivalence hinged on
      `F.Deterministic`, at the signature pinned in `## Lean Challenge Statements` below. Prove
      it from `deterministic_of_detPM` and `detPM_of_deterministic`; the third leg (full schema ⟹
      atomic fragment) is instantiation at `StarFormula.atom p`.
- [ ] Write the new `deterministic_starDefinable` docstring so it states plainly, in these terms:
      the **atomic fragment already forces** determinism, and determinism **delivers the full
      schema** at every `StarFormula`. Say explicitly that no instance of the schema is inferred
      from another and that this is therefore not an appeal to uniform substitution. Delete the
      superseded "The single-`p` form is not available in the (⇐) direction's shape" paragraph,
      which the new statement makes stale. Do not assert any axiom figure in this phase —
      Phase 3 owns axiom prose.
- [ ] Run `lake build` and `lake build BimodalTest`; both green, zero new `sorry`.

**Timing**: 1 hour

**Depends on**: 1

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` — `detPM_of_deterministic` statement and
  docstring, `deterministic_starDefinable` statement, proof and docstring.

**Verification**:
- The three declarations' signatures match `## Lean Challenge Statements` verbatim, read
  side-by-side rather than checked by name existence (plan-compliance.md, Statement Fidelity).
- `lake build` and `lake build BimodalTest` exit 0.
- `deterministic_of_detPM` is byte-identical to its Phase 1 state — confirm with
  `git diff` scoped to that declaration.
- `#print axioms FormalSystem.Semantics.detPM_of_deterministic` is measured (not asserted in
  prose yet) and handed to Phase 3.

---

### Phase 3: Choice bookkeeping and the module docstring [NOT STARTED]

**Goal**: The module docstring — its result list, its single-sentence-letter section, and its
choice-dependence section — matches the new statement, with every `#print axioms` figure equal to
a value measured after the change.

**Tasks**:
- [ ] Re-measure the axiom sets after Phases 1-2 with a scratch file
      (`import FormalSystem` plus `#print axioms` for `settledDisj_of_deterministic`,
      `sentDet_of_deterministic`, `detPM_of_deterministic`, `deterministic_of_detPM`,
      `deterministic_starDefinable`), run under `lake env lean`. Record the measured values.
- [ ] Rewrite the `## Choice dependence` section (currently lines ~61-70) against the new
      statement. It must say: the (⇐) direction (`detPM_of_deterministic`, schematic in `φ`)
      consumes `states_eq_of_deterministic` through `star_truth_congr_ext` and adds no
      extension-theorem step; the (⇒) direction (`deterministic_of_detPM`, hypothesis at atoms)
      and hence `deterministic_starDefinable` route through `deterministic_of_singletonClasses`
      (`Semantics/DeterministicBridge.lean`) and are **theorems of ZFC** via `thm:extension` and
      Zorn's lemma. State the asymmetry **structurally**, by which lemma each direction routes
      through — never as a difference in `#print axioms`, which does not exist (all measured sets
      are equal). If the section asserts a figure, it must be the measured one verbatim.
- [ ] Rewrite the `## The single sentence letter is not uniform substitution` section: the
      forward direction is now proved for an arbitrary `StarFormula` on **both** the `sentDet` and
      the `Det-pm` side, while the converse still needs only the singleton valuation at one
      letter. Keep the existing reason the appeal is not uniform substitution, and keep the
      `p → ⊡p` / `Fp → ⊡Fp` drift-frame counterexample sentence intact.
- [ ] Update the module docstring's numbered opener (results 1-3) and `## Main Results` /
      `## Main Definitions` lists so `detPM` is described as schematic and result 3 is the
      three-way equivalence rather than a biconditional.
- [ ] Update `detPM`'s own docstring: it is `sent:det`'s shape with `always` in place of
      `\Future`, at an arbitrary `StarFormula`; note that `detPM (StarFormula.atom p)` is the
      atomic instance the converse consumes. Remove the "A bare atom `p` is used rather than a
      schema variable" justification, which the widening makes false.
- [ ] Confirm no task number appears anywhere in the edited prose.
- [ ] Run `lake build` (docstrings elaborate) and confirm green.

**Timing**: 45 minutes

**Depends on**: 2

**Verification Tier**: prose

**Files to modify**:
- `FormalSystem/Semantics/StarDeterminism.lean` — module docstring and the per-declaration
  docstrings for `detPM`, `detPM_of_deterministic`, `deterministic_of_detPM`.

**Verification**:
- Every `[propext, …]` string in the file equals a value measured in this phase — checked one by
  one against the recorded measurement, not from memory.
- No sentence claims a choice-free or `Classical.choice`-free pin for any declaration.
- No sentence argues by uniform substitution; the drift-frame counterexample sentence survives.
- `lake build` exits 0.
- `grep -nE "task [0-9]" FormalSystem/Semantics/StarDeterminism.lean` returns nothing.

---

### Phase 4: Prose inventories and the paper-label correspondence row [NOT STARTED]

**Goal**: The four prose sites that inventory these declarations name the three-way statement.

**Tasks**:
- [ ] `FormalSystem/StarLanguage/README.md` — the paper-label correspondence row
      `| Theorem C, `Det-pm` half (report-level) | … |` must name the **three-way** statement:
      the atomic fragment forces determinism and determinism delivers the full schema, cited to
      `detPM` and `deterministic_starDefinable` (`Semantics/StarDeterminism.lean`). Keep it marked
      report-level and pending paper integration; do not promote it to manuscript text.
- [ ] `FormalSystem/StarLanguage/README.md` — the "Where the L⋆ semantics lives" row for
      `Semantics/StarDeterminism.lean` still lists the same five declaration names; confirm it
      needs no change, or adjust if a name moved.
- [ ] `FormalSystem/Semantics/README.md` — the `StarDeterminism.lean` row's trailing gloss
      ("the last two theorems of ZFC") stays accurate for `deterministic_of_detPM` and
      `deterministic_starDefinable`; extend the row to say `detPM` is schematic.
- [ ] `FormalSystem/StarLanguage.lean` — the module-docstring bullet for
      `Semantics/StarDeterminism.lean` mentions `detPM` and "Theorem C's `Det-pm` half"; leave the
      name list intact and confirm nothing there asserts an atom restriction.
- [ ] `FormalSystem/Metalogic/Independence/README.md` — result 7's closing sentence cites
      `deterministic_starDefinable` for "Det-pm does define the deterministic frames". Confirm it
      still reads correctly against the three-way form; adjust only if it asserts the two-way
      shape.
- [ ] `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean:~304` — the
      `fn_separates` docstring's "Contrast `deterministic_starDefinable`" sentence. Confirm it
      reads correctly against the new statement; this is a docstring in another module's
      territory, so touch it only if it is actually stale.
- [ ] Confirm no task number appears in any edited file.

**Timing**: 30 minutes

**Depends on**: 2

**Verification Tier**: prose

**Scope Hypothesis**: The plan asserts exactly six prose sites (four README/aggregator files plus
two in-`.lean` docstring mentions outside `StarDeterminism.lean`). Confirm at implementation time
with `grep -rn "detPM\|starDefinable" --include='*.md' --include='*.lean' FormalSystem/` and
extend the phase's file list if the grep finds more.

**Files to modify**:
- `FormalSystem/StarLanguage/README.md`
- `FormalSystem/Semantics/README.md`
- `FormalSystem/StarLanguage.lean` (docstring only, if stale)
- `FormalSystem/Metalogic/Independence/README.md` (if stale)
- `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` (docstring only, if stale)

**Verification**:
- The Theorem C row in `FormalSystem/StarLanguage/README.md` names the three-way statement.
- `bash scripts/readme-lint.sh` (if it accepts these paths) reports no new finding.
- `lake build` exits 0 (the two `.lean` docstring edits elaborate).
- `grep -rnE "task [0-9]" FormalSystem/StarLanguage/README.md FormalSystem/Semantics/README.md`
  returns nothing.

---

### Phase 5: Full gate [NOT STARTED]

**Goal**: The repository's complete gate set is green and every acceptance criterion in the task
description is checked off against measured output.

**Tasks**:
- [ ] `lake build` — exit 0.
- [ ] `lake build BimodalTest` — exit 0.
- [ ] `bash scripts/check-module-invariants.sh` — exit 0. Read the C2 and C14 lines specifically:
      both are expected to PASS untouched. If either reports divergence, update the pinned
      **name** only and never its axiom set; a changed axiom set is a hard stop that must be
      escalated, not rebaselined.
- [ ] Confirm C3 (zero structural `sorry`) and C9 (zero task-number citations under
      `FormalSystem/`) both PASS.
- [ ] Re-run the `#print axioms` scratch measurement one final time and diff it against every
      figure asserted in `FormalSystem/Semantics/StarDeterminism.lean`'s docstrings. Any mismatch
      is a defect to fix in this phase, not to record.
- [ ] `grep -rn "detPM" --include='*.lean' FormalSystem/ Tests/` — confirm the only Lean site is
      `StarDeterminism.lean`, closing Phase 1's scope hypothesis.
- [ ] Re-read `deterministic_of_detPM`'s signature one last time and confirm its hypothesis is
      still `∀ p : Atom, …`.

**Timing**: 45 minutes

**Depends on**: 3, 4

**Verification Tier**: full

**Files to modify**: none expected; defect fixes land in whichever file the gate names.

**Verification**:
- All three commands above exit 0 and their output is quoted in the implementation summary.
- The measured axiom table is quoted in the summary alongside the docstring figures it matches.

---

## Lean Challenge Statements

```lean
import FormalSystem.Semantics.StarValidity
import FormalSystem.Semantics.DeterministicBridge

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage
open FormalSystem.StarLanguage

variable {F : TaskFrame}

def detPM (φ : StarFormula) : StarFormula :=
  .timeStore 1 (StarFormula.always (.timeStore 2 (.timeRecall 1 (settledDisj φ))))

theorem detPM_unfold (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (v : ℕ → F.Duration) (φ : StarFormula) :
    StarTruthAt M τ x v (detPM φ) ↔
      ∀ y : F.Duration, StarTruthAt M τ x (Function.update (Function.update v 1 x) 2 y)
        (settledDisj φ) := sorry

theorem detPM_of_deterministic (hD : F.Deterministic) (φ : StarFormula) :
    F.StarValidOn (detPM φ) := sorry

theorem deterministic_of_detPM
    (h : ∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p))) : F.Deterministic := sorry

theorem deterministic_starDefinable (F : TaskFrame) :
    ((∀ p : Atom, F.StarValidOn (detPM (StarFormula.atom p))) ↔ F.Deterministic) ∧
      (F.Deterministic ↔ ∀ φ : StarFormula, F.StarValidOn (detPM φ)) := sorry

end FormalSystem.Semantics
```

**Why this shape for the three-way equivalence.** Two conjoined biconditionals hinged on
`F.Deterministic` is the chosen form. It reads as the paper's sentence (atomic fragment ⟺
determinism ⟺ full schema), its first conjunct is *literally* the old
`deterministic_starDefinable` after the type-forced retype — so the name is **extended, never
weakened** — and `.1` / `.2` give downstream callers the two halves directly.
`List.TFAE` was considered and rejected: it is idiomatic Mathlib but has **zero precedent in this
repository** (a repo-wide grep for `TFAE` under `FormalSystem/` returns nothing), and it would
force every downstream use through `TFAE.out` index arithmetic for no gain at three items. Do not
substitute TFAE at implementation time; if the conjunction shape genuinely cannot be proved as
written, mark the phase `[BLOCKED]` and escalate rather than restating it.

## Testing & Validation

- [ ] `lake build` exits 0.
- [ ] `lake build BimodalTest` exits 0.
- [ ] `bash scripts/check-module-invariants.sh` exits 0, with C1, C2, C3, C9, C14 all PASS.
- [ ] Zero new `sorry` anywhere under `FormalSystem/` (C3 asserts the inventory is zero).
- [ ] `detPM (StarFormula.atom p)` is definitionally the pre-change `detPM p` — confirmed by the
      unchanged body of `deterministic_of_detPM`, which still compiles against the atomic
      hypothesis without a bridging lemma.
- [ ] `deterministic_of_detPM`'s hypothesis binds `p : Atom`, not `φ : StarFormula`.
- [ ] Every `#print axioms` figure asserted in a docstring equals the post-change measured value.
- [ ] No task-number citation under `FormalSystem/`.

## Artifacts & Outputs

- `FormalSystem/Semantics/StarDeterminism.lean` — schematic `detPM`, `detPM_unfold`,
  `detPM_of_deterministic`; `deterministic_of_detPM` held at atoms; three-way
  `deterministic_starDefinable`; rewritten module docstring.
- `FormalSystem/StarLanguage/README.md` — Theorem C paper-label correspondence row naming the
  three-way statement.
- `FormalSystem/Semantics/README.md` — updated `StarDeterminism.lean` inventory row.
- `FormalSystem/StarLanguage.lean`, `FormalSystem/Metalogic/Independence/README.md`,
  `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` — prose touch-ups if stale.
- `specs/571_schematic_detpm_and_theorem_c/summaries/01_schematic-detpm-theorem-c-summary.md` —
  execution summary, carrying the measured axiom table and the quoted gate output.

## Rollback/Contingency

Every change is confined to `FormalSystem/` and every phase ends at a green `lake build`, so a
per-phase `git revert` of the phase's commit restores the previous green state. Phase 1 is an
`atomic-batch` commit precisely so that the widening can be reverted as one unit. If Phase 2's
three-way statement cannot be proved as written, the phase is marked `[BLOCKED]` and escalated —
the fallback is **not** to substitute a weaker or differently-shaped statement, and **not** to
widen `deterministic_of_detPM`'s hypothesis to make the proof easier. If the C2 or C14 axiom
baselines diverge with a changed axiom **set** (as opposed to a changed pinned name), stop: that
is a hard stop under `scripts/check-module-invariants.sh`'s own contract and is escalated rather
than rebaselined.
