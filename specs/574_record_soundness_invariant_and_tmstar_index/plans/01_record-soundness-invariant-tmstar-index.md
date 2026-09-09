# Implementation Plan: Record the Soundness Invariant and the TM⋆ Index Rows

- **Task**: 574 - Record the load-bearing soundness invariant and close the TM-star documentation gaps
- **Status**: [NOT STARTED]
- **Effort**: 5 hours
- **Dependencies**: None
- **Research Inputs**: None (no research phase dispatched; the task description carries the
  defect, the evidence, the work list and the acceptance bar, and every remaining unknown was
  resolved by direct `grep`/`Read` inspection during planning — see Preliminary Findings)
- **Artifacts**: plans/01_record-soundness-invariant-tmstar-index.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Four gaps, all documentation-and-scaffolding rather than mathematics. (1) The fact that time-shift
homogeneity is consumed by a *very small*, enumerable set of soundness proofs — and that this is
why `StarAxiom` embeds the TM⁺ schema block through a single `ofBase` arm rather than
re-declaring the TM schemata — is recorded nowhere. (2) The `StarValidIn` binder-shape adapters
live in `Conservativity/Star/StarSoundness.lean` while `Semantics/StarValidity.lean`'s own
docstring advertises them. (3) `docs/theorem-index.md` has no TM⋆ rows. (4) Index rows require
`pinned:C14` baseline entries in `scripts/check-module-invariants.sh`, and C15's second assertion
additionally requires a `Paper:` line in each named declaration's own doc comment.

Definition of done: `lake build` green, no new `sorry`, `bash scripts/check-module-invariants.sh`
exits 0, the invariant is stated at the point a language-extension author reads first, and every
new index row is machine-pinned rather than prose-only.

### Research Integration

No research report exists for this round. The description was a specification, not a research
question; the codebase reads below were done at plan time, within the planning dispatch's own
tool budget.

### Preliminary Findings (plan-time, to be confirmed at implementation time)

These are plan-time reads, not verified conclusions. Phase 1 owns the confirmation.

- **The "sole consumer" claim is very likely an undercount.** Grepping
  `TimeShift.timeShift_preserves_truth` shows a second soundness-side consumer that Soundness.lean
  itself already imports: `mf_swap_valid` in
  `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`, the swapped-MF lemma that
  carries TF's validity. Soundness.lean's own existing docstring already says "Time-shift
  invariance (MF, TF)" — two axioms, not one. A third, in a different object language, is
  `minusTruthAt_timeShift` in `FormalSystem/Metalogic/Conservativity/MinusLanguageSoundness.lean`,
  which is L⁻'s mirror of the same fact. A corrected count is the expected outcome of Phase 1,
  not a failure of it.
- **Phase 3's relocation looks unobstructed.** The adapters' real names are
  `starValidIn_of_forall_total` / `starValidIn_apply_total` (snake_case free functions in
  `FormalSystem.Metalogic.Conservativity`), not the dotted `StarValidIn.of_forall_total` /
  `.apply_total` the description names. `StarValidIn` is *defined* in
  `Semantics/StarValidity.lean`, which already has `ProofSystem.FrameClass` in scope through
  `Semantics/PlusValidity.lean`, and the exact L⁺ counterparts (`PlusValidIn.of_forall_total` /
  `.apply_total`) already sit in `Semantics/PlusValidity.lean`. No import cycle is expected; the
  docstring-correction fallback is retained but should not be needed.
- **Phase 5 must touch files outside the declared TERRITORY.** C15's second assertion requires
  every `docs/theorem-index.md` row's named declaration to carry a `Paper: <anchor>` or
  `Paper: — (reason)` line in its own `/--` block. Two of the six named results already do
  (`star_soundness_validIn`, `starDerivable_ofFormula_iff`); four do not — `StarAxiom`
  (`FormalSystem/StarLanguage/Axioms.lean`), `StarDerivationTree`
  (`FormalSystem/StarLanguage/Derivation.lean`), `starConservative_of_plusComplete` and
  `plusIncomplete_of_starNonconservative` (both `FormalSystem/Metalogic/Conservativity/Star/Forward.lean`).
  See Risks below for the assumption under which this proceeds.
- **The "completeness OPEN row" cannot be a table row.** C15's `ROW` regex requires a backticked,
  fully-qualified `FormalSystem.…` Lean name in the third cell; an open problem has no
  declaration. `docs/theorem-index.md` currently contains no `OPEN` row and no OPEN convention —
  its established idiom for a non-theorem status is the prose section
  `## Statuses that are refutations, not gaps`. Phase 5 therefore records TM⋆ completeness as a
  prose bullet in that section, not as a row.
- **C14's `grep 'depends on axioms'` filter drops axiom-free declarations.** The `C14_BASELINE`
  and `C14LEAN` heredocs are compared by exact string equality after filtering `lake env lean`
  output through `grep 'depends on axioms'`. A declaration whose `#print axioms` prints
  `does not depend on any axioms` contributes a line to neither side. Adding such a declaration to
  the `C14LEAN` heredoc is harmless; adding a fabricated line for it to `C14_BASELINE` is a hard
  C14 failure. `StarAxiom` and `StarDerivationTree` are `inductive`s and are the candidates most
  likely to hit this. Phase 4 therefore measures first and derives the row set from the
  measurement.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` and no `roadmap_flag` were supplied in this dispatch, so `specs/ROADMAP.md` was
not consulted and no roadmap-review/roadmap-update phases are included.

## Goals & Non-Goals

**Goals**:
- Record, in `FormalSystem/Metalogic/Soundness.lean`'s module docstring, the *verified* set of
  soundness proofs that consume time-shift homogeneity, why that set's size matters to any future
  language extension, and `refute_modal_future` as the realized consequence.
- Mirror a one-line pointer in `FormalSystem/Metalogic/README.md`, and annotate the `ofBase`
  design rationale in `FormalSystem/StarLanguage/README.md` so it agrees with the verified count.
- Relocate the two `StarValidIn` binder-shape adapters to the module whose docstring already
  advertises them, renaming them to the dotted form their L⁺ counterparts use. The two Lean
  declarations this plan commits to producing are `StarValidIn.of_forall_total` and
  `StarValidIn.apply_total`; their exact statements are pinned under
  `## Lean Challenge Statements` below, and that section's identifier set is exactly these two.
- Add machine-pinned `docs/theorem-index.md` coverage for the TM⋆ headline results, with the C14
  baseline entries and `Paper:` declaration-site lines those rows require.

**Non-Goals**:
- No proof edits in `Soundness.lean`. The territory constraint is docstring-only there, and
  nothing in this task requires a proof to change.
- No new mathematics, no new axioms, no `sorry`, no altered axiom set. C14 baseline edits add
  **names** only; every value is measured from the tree.
- No attempt to settle TM⋆ completeness, TM⁺ completeness, or conservativity — those stay OPEN and
  are recorded as such.
- No task-number citations under `FormalSystem/`, `docs/`, or `scripts/` (C9/C9D).
- No new rows on `FormalSystem/MainResults.lean` (which currently names no TM⋆ declaration), so
  C21's subset assertion is untouched.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The recorded invariant repeats the description's "sole consumer" claim uncorrected | H | H | Phase 1 runs the audit *before* writing a word of the docstring, and its own verification criterion is that the written count matches the enumerated grep result, not the description |
| Phase 5 must edit `StarLanguage/Axioms.lean`, `StarLanguage/Derivation.lean` and `Conservativity/Star/Forward.lean`, outside the declared TERRITORY | M | H | Proceed under a stated assumption: the edits are **docstring-only** additions of the `Paper:` line C15 requires, with no declaration, statement or proof touched. Deliverable (4) is unachievable otherwise — C15 would fail on every new row. Record the widened file set explicitly in the implementation summary |
| Adding an axiom-free declaration to `C14_BASELINE` breaks C14 by exact-string mismatch | H | M | Phase 4 measures every candidate with `#print axioms` first and only then writes baseline lines; any declaration printing `does not depend on any axioms` is dropped from both heredocs and its index row omitted or re-pointed at a pinned declaration |
| An import cycle blocks the Phase 3 relocation | M | L | `StarValidIn` is already defined in the destination module and the L⁺ mirror already lives there. If a cycle nonetheless appears, the fallback is mandatory, not optional: correct `Semantics/StarValidity.lean`'s Main Results docstring to stop advertising the adapters, and record the specific cycle as the reason in that same docstring |
| A `docs/theorem-index.md` File-column path or Frame-class cell fails C15's row parse | M | M | Copy an existing row verbatim as the template; the `ROW` regex requires backticked name, backticked path with no line number, and exactly six pipe-delimited cells |
| Renaming the adapters breaks unlisted call sites | M | L | Phase 3 is `interface` tier: grep the whole tree for both old names before and after, and build `Semantics/StarValidity.lean` plus every enumerated dependent |
| `check-module-invariants.sh` is slow enough to tempt a skipped gate | M | M | Use `--no-build` for the fast structural pass during iteration, but the phase-closing and task-closing gate is the full unflagged run, exit 0 |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3 | -- |
| 2 | 2, 4 | 1 (for 2), 3 (for 4) |
| 3 | 5 | 4 |
| 4 | 6 | 2, 5 |

Phases within the same wave can execute in parallel. Phases 1 and 3 touch disjoint files
(`Metalogic/Soundness.lean` vs. `Semantics/StarValidity.lean` +
`Conservativity/Star/StarSoundness.lean`) and may be dispatched together.

---

### Phase 1: Audit the time-shift consumer set and record the invariant [NOT STARTED]

**Goal**: Establish by direct inspection which soundness proofs in the live tree consume time-shift
homogeneity, then write that verified set — not the description's claim — into
`FormalSystem/Metalogic/Soundness.lean`'s module docstring.

**Tasks**:
- [ ] Enumerate every live occurrence of `TimeShift.timeShift_preserves_truth`,
      `timeShift_preserves_truth_total`, and `ConvexHistory.timeShift` under `FormalSystem/`,
      excluding `FormalSystem/Boneyard/` (archived; see ADR-005 and check B0).
- [ ] Partition the occurrences into (a) *soundness* consumers — proofs establishing validity of an
      axiom or a rule, in any object language — and (b) non-soundness consumers (decidability
      bridges, canonical-model constructions, shift-set machinery, the truth-lemma stack).
      Record the partition and the criterion used for it.
- [ ] Confirm or correct the claim that `modal_future_valid` is the sole soundness consumer. At
      minimum, resolve the status of `mf_swap_valid`
      (`FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`) and
      `minusTruthAt_timeShift`
      (`FormalSystem/Metalogic/Conservativity/MinusLanguageSoundness.lean`), both of which the
      plan-time grep surfaced.
- [ ] Write the result into the `Soundness.lean` module docstring as a named subsection (e.g.
      `## The Time-Shift Consumer Set`), stating: the enumerated consumer set with file paths; why
      a small set matters to a language extension (a schema whose validity rests on time-shift
      homogeneity does not survive a semantics that adds a component to the point of evaluation);
      and `refute_modal_future` (`FormalSystem/Semantics/StarNonValidities.lean`) as the realized
      consequence — MF is refuted over `StarFormula`, which is why `StarAxiom` reaches the TM⁺
      block through a single `ofBase` arm.
- [ ] If the count is greater than one, say so plainly in the docstring and reconcile it with the
      existing `**Key Techniques**` bullet, which already reads "Time-shift invariance (MF, TF)".
- [ ] Do not touch any proof, `theorem`, `def`, or `import` line in `Soundness.lean`.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: prose

**Scope Hypothesis**: the description asserts a consumer count of exactly one
(`modal_future_valid`). Plan-time grep suggests at least two soundness-side consumers in the live
tree plus one L⁻ mirror. Confirm at implementation time by the enumeration above; the docstring
must state the confirmed count, and the count that lands there is the one Phase 2 propagates.

**Files to modify**:
- `FormalSystem/Metalogic/Soundness.lean` — module docstring only: one new subsection, plus
  reconciliation of the existing `**Key Techniques**` bullet if the count changes.

**Verification**:
- Diff read-through confirming every changed hunk lies inside the leading `/-! … -/` module
  docstring; no line outside it is touched.
- Every declaration name and file path cited in the new prose resolves (`grep` each one).
- The stated consumer set matches the enumeration recorded in the phase's own audit output,
  name for name.
- `lake build FormalSystem.Metalogic.Soundness` green (a docstring is still elaborated).

---

### Phase 2: Propagate the verified count to the two READMEs [NOT STARTED]

**Goal**: Mirror the invariant as a one-line pointer in `FormalSystem/Metalogic/README.md`, and
annotate the `ofBase` design rationale in `FormalSystem/StarLanguage/README.md` so it agrees with
whatever Phase 1 confirmed.

**Tasks**:
- [ ] Add a one-line pointer under `## Main Results` → `### Soundness — Soundness.lean` in
      `FormalSystem/Metalogic/README.md`, naming the consumer set and pointing at the
      `Soundness.lean` docstring subsection as the authority. Do not restate the count in more
      than one place on that page.
- [ ] Annotate `FormalSystem/StarLanguage/README.md`'s `ofBase` design paragraph (the "one
      structural decision worth naming here" block) and, if the count changed, its MF row in the
      non-validities table, so that neither page asserts a count Phase 1 disproved.
- [ ] Confirm no generated block is disturbed: `FormalSystem/Metalogic/README.md` carries
      `BEGIN GENERATED` inventory blocks owned by
      `bash scripts/check-module-invariants.sh --emit-inventory`. Edit only prose outside them.
- [ ] No task-number citations (C9D applies to `docs/`; C9 to `FormalSystem/`).

**Timing**: 45 minutes

**Depends on**: 1

**Verification Tier**: prose

**Files to modify**:
- `FormalSystem/Metalogic/README.md` — one-line pointer, prose only.
- `FormalSystem/StarLanguage/README.md` — annotation of the `ofBase` rationale, prose only.

**Verification**:
- `bash scripts/check-module-invariants.sh --emit-inventory --check` reports no byte would change
  (i.e. no generated block was edited).
- Every relative markdown link and slash-shaped path added resolves (C12/C13 cover `docs/` and
  `README.md`; check the two new pointers by hand since they sit under `FormalSystem/`).
- The three surfaces (`Soundness.lean` docstring, `Metalogic/README.md`,
  `StarLanguage/README.md`) state a mutually consistent count.

---

### Phase 3: Relocate the `StarValidIn` binder-shape adapters [NOT STARTED]

**Goal**: Move the two adapters into `FormalSystem/Semantics/StarValidity.lean` — the module whose
`## Main Results` docstring already advertises them — under the dotted names their L⁺ counterparts
use, and have `StarSoundness.lean` consume them from there.

**Tasks**:
- [ ] Add `StarValidIn.of_forall_total` and `StarValidIn.apply_total` to
      `FormalSystem/Semantics/StarValidity.lean`, in the `### Binder-shape adapters` block,
      immediately after the `StarValidOnFrames` pair, mirroring
      `PlusValidIn.of_forall_total` / `.apply_total` in `FormalSystem/Semantics/PlusValidity.lean`
      line for line. Statements are pinned under `## Lean Challenge Statements` below.
- [ ] Delete `starValidIn_of_forall_total` and `starValidIn_apply_total` and their
      `/-! ## The `StarValidIn` binder-shape adapters -/` section header from
      `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean`.
- [ ] `grep -rn 'starValidIn_of_forall_total\|starValidIn_apply_total'` across `FormalSystem/` and
      `Tests/` and repoint every call site at the dotted names.
- [ ] Update `StarSoundness.lean`'s module docstring: the `## Main Results` list and any prose
      that described the adapters as living locally.
- [ ] Confirm `Semantics/StarValidity.lean`'s existing `## Main Results` bullet ("and the
      `StarValidIn` forms") is now true as written; adjust wording only if the new names make it
      inaccurate.
- [ ] **Fallback, if and only if `lake build` reports an import cycle**: revert the move, and
      instead correct `Semantics/StarValidity.lean`'s docstring so it no longer advertises the
      adapters, naming the specific cycle (`module A imports … imports A`) as the reason in that
      same docstring. Do not leave the docstring stale under any circumstance.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: the plan-time grep found exactly two call sites, both inside
`StarSoundness.lean` (the adapters' own bodies aside), and predicts no import cycle. Confirm at
implementation time by the tree-wide grep above and by a clean `lake build`; if either prediction
fails, the fallback branch applies and the deviation is recorded in the summary.

**Files to modify**:
- `FormalSystem/Semantics/StarValidity.lean` — two new theorems in the adapters block.
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` — remove the two local
  theorems and their section header; repoint call sites; update the module docstring.

**Verification**:
- `lake build FormalSystem.Semantics.StarValidity` green.
- `lake build FormalSystem.Metalogic.Conservativity.Star.StarSoundness` green (the enumerated
  direct dependent).
- `grep -rn 'starValidIn_of_forall_total\|starValidIn_apply_total' FormalSystem Tests` returns
  nothing.
- No `sorry` introduced: `grep -rn 'sorry' FormalSystem/Semantics/StarValidity.lean
  FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` returns nothing.
- Full `lake build` green before the phase closes.

---

### Phase 4: Measure axiom sets and extend the C14 baseline pair [NOT STARTED]

**Goal**: Measure `#print axioms` for each TM⋆ headline declaration and add the measured entries to
both C14 heredocs in `scripts/check-module-invariants.sh`, so the index rows Phase 5 writes are
machine-pinned rather than prose-only.

**Tasks**:
- [ ] Write a scratch Lean file importing `FormalSystem` with `#print axioms` for each of:
      `FormalSystem.StarLanguage.StarAxiom`, `FormalSystem.StarLanguage.StarDerivationTree`,
      `FormalSystem.Metalogic.Conservativity.star_soundness_validIn`,
      `FormalSystem.Metalogic.Conservativity.starDerivable_ofFormula_iff`,
      `FormalSystem.Metalogic.Conservativity.starConservative_of_plusComplete`,
      `FormalSystem.Metalogic.Conservativity.plusIncomplete_of_starNonconservative`.
      Confirm each fully-qualified name resolves before measuring.
- [ ] Run it through the *same* pipeline C14 uses — `lake env lean FILE 2>&1`, the continuation-line
      rejoin `sed`, then `grep 'depends on axioms'` — so the recorded strings are byte-identical to
      what the check will compare against. Do not hand-type an axiom list.
- [ ] Drop from consideration any declaration whose output does not survive the
      `grep 'depends on axioms'` filter (i.e. prints `does not depend on any axioms`). Such a
      declaration cannot be pinned by C14's exact-string mechanism; record which ones these are,
      and carry the decision into Phase 5's row set.
- [ ] Append the surviving measured lines to `C14_BASELINE` (the `C14BASE` heredoc) and the
      matching `#print axioms` lines to the `C14LEAN` heredoc, **in the same order in both**, as
      the surrounding comment requires. Append at the end of each heredoc; do not reorder or alter
      any existing line.
- [ ] Extend the explanatory comment above `read -r -d '' C14_BASELINE` to say that the block now
      also pins the TM⋆ headline results consumed by `docs/theorem-index.md`.
- [ ] No task-number citations in `scripts/` (C9 covers `scripts/`).

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: full

**Scope Hypothesis**: the description names six declarations plus one OPEN entry, and this plan
assumes all six are pinnable. The two `inductive`s (`StarAxiom`, `StarDerivationTree`) are the
likely exceptions. Confirm by the measurement step above before writing any baseline line; the
confirmed pinnable set — not the six named here — is what Phase 5 turns into rows.

**Files to modify**:
- `scripts/check-module-invariants.sh` — append to the `C14BASE` and `C14LEAN` heredocs; extend the
  block comment above them.

**Verification**:
- `bash scripts/check-module-invariants.sh` exits 0, with C14 reporting PASS.
- The two heredocs list the same declarations in the same order (compare by extracting names from
  each and diffing).
- No existing baseline line was modified: `git diff scripts/check-module-invariants.sh` shows
  additions and the comment edit only.

---

### Phase 5: Add the TM⋆ ledger rows and the declaration-site `Paper:` lines [NOT STARTED]

**Goal**: Add a TM⋆ section to `docs/theorem-index.md` covering the pinnable headline results, add
the `Paper:` lines C15's second assertion requires at each named declaration, and record TM⋆
completeness as an open status in prose.

**Tasks**:
- [ ] Add `Paper: — (formalization-native; the manuscript supplies no proof system for
      `\BL^\star`)` — matching the wording already used at
      `Conservativity/Star/StarSoundness.lean` and `Conservativity/Star/Forward.lean` — to the
      `/--` doc comment of each named declaration that lacks one. Plan-time reading says that is
      `StarAxiom` (`FormalSystem/StarLanguage/Axioms.lean`), `StarDerivationTree`
      (`FormalSystem/StarLanguage/Derivation.lean`), `starConservative_of_plusComplete` and
      `plusIncomplete_of_starNonconservative` (both
      `FormalSystem/Metalogic/Conservativity/Star/Forward.lean`). Verify per declaration rather
      than trusting this list. These are docstring-only additions — see Risks.
- [ ] Add a `### TM⋆ over L⋆ — the store/recall language` section to `docs/theorem-index.md`'s
      `## The ledger`, one row per pinnable declaration from Phase 4, using an existing row as the
      literal template: six pipe-delimited cells, backticked fully-qualified Lean name, backticked
      path with **no** line number, `—` in the Frame class cell where the result is class-generic,
      and `pcq pinned:C14` (or the literal measured axiom list) in the Axioms cell.
- [ ] Record TM⋆ completeness as an open status. It is **not** a table row: C15's row regex
      requires a fully-qualified Lean name, which an open problem has not got. Add a bullet to the
      existing `## Statuses that are refutations, not gaps` section (retitling it if the section
      now carries a genuine gap alongside the refutations), stating that completeness for TM⋆ at
      every frame class is open and not promised, and cross-referencing
      `starConservative_of_plusComplete` / `plusIncomplete_of_starNonconservative` for why the
      conservativity question is equivalent modulo TM⋆ soundness to the recorded TM⁺ completeness
      problem.
- [ ] Add a `Notation and naming` row for L⋆ / TM⋆ if one is absent, matching the existing L⁻ and
      L⁺ rows.
- [ ] No task-number citations under `docs/` or `FormalSystem/` (C9, C9D).

**Timing**: 1 hour 15 minutes

**Depends on**: 4

**Verification Tier**: full

**Commit Mode**: atomic-batch

**Scope Hypothesis**: this phase asserts that exactly four declarations lack a `Paper:` line and
that the new ledger section carries one row per Phase-4-pinnable declaration. Confirm at
implementation time by grepping `Paper: ` in each declaring file and by re-running C15; the row
count is whatever Phase 4's measurement admitted, not a number fixed here.

**Commit-mode rationale**: a `docs/theorem-index.md` row and its declaration-site `Paper:` line are
two halves of one C15 assertion. Committing either half alone leaves the tree red at C15, so the
declared file set below is one objective.

**Files to modify**:
- `docs/theorem-index.md` — new ledger section, an open-status bullet, and a notation row.
- `FormalSystem/StarLanguage/Axioms.lean` — docstring only: `Paper:` line on `StarAxiom`.
- `FormalSystem/StarLanguage/Derivation.lean` — docstring only: `Paper:` line on
  `StarDerivationTree`.
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — docstring only: `Paper:` lines on
  `starConservative_of_plusComplete` and `plusIncomplete_of_starNonconservative`.

**Verification**:
- `bash scripts/check-module-invariants.sh` exits 0, with both C15 assertions reporting PASS and
  the second naming a row count that includes the new rows.
- Every new row parses: it appears in C15's row count, and none of the new declarations shows up in
  the `problems` list.
- Diff read-through confirming every `.lean` hunk lies inside a `/--` block; no declaration,
  statement, or proof line is touched.
- `lake build` green.

---

### Phase 6: Full gate and constraint sweep [NOT STARTED]

**Goal**: Run the complete acceptance bar and confirm every hard constraint holds across the whole
change set.

**Tasks**:
- [ ] `lake build` green from a clean invocation.
- [ ] `bash scripts/check-module-invariants.sh` exits 0; capture the summary line and the C14/C15
      PASS lines as evidence.
- [ ] No new `sorry`: `grep -rn '\bsorry\b' FormalSystem/ scripts/ docs/` shows no addition
      relative to `main`.
- [ ] No task-number citations under `FormalSystem/`, `docs/`, or `scripts/`:
      `bash .claude/scripts/check-task-references.sh` (and C9/C9D within the invariant script).
- [ ] Confirm the C14 baseline edits added names only: `git diff scripts/check-module-invariants.sh`
      shows no altered axiom list on any pre-existing line.
- [ ] Confirm the three prose surfaces state one consistent time-shift consumer count.
- [ ] Record in the summary: the confirmed consumer count and how it differed from the
      description's claim; whether the Phase 3 move succeeded or the docstring-correction fallback
      applied; the file set actually touched, including the three files outside the declared
      TERRITORY and why.

**Timing**: 45 minutes

**Depends on**: 2, 5

**Verification Tier**: full

**Files to modify**: none (verification only; any repair it triggers is charged to the phase that
introduced the defect).

**Verification**:
- Every checklist item above passes, with command output quoted in the summary.

---

## Lean Challenge Statements

The only Lean declarations this plan commits to producing are Phase 3's two relocated adapters.
Every other deliverable is prose, a docstring, or a shell-script baseline. The identifier set below
is exactly the declaration set named under `- **Goals**:`.

```lean
import FormalSystem

namespace FormalSystem.Semantics

open FormalSystem.StarLanguage

/-- `StarValidOnFrames.of_forall_total` at a `FrameClass` tag. -/
theorem StarValidIn.of_forall_total {fc : ProofSystem.FrameClass} {φ : StarFormula}
    (h : ∀ (F : TaskFrame), fc.Sat F → ∀ (M : TaskModel F) (τ : ConvexHistory F),
           τ.IsTotal → ∀ (x : F.Duration) (v : ℕ → F.Duration), StarTruthAt M τ x v φ) :
    StarValidIn fc φ := sorry

/-- `StarValidOnFrames.apply_total` at a `FrameClass` tag. -/
theorem StarValidIn.apply_total {fc : ProofSystem.FrameClass} {φ : StarFormula}
    (h : StarValidIn fc φ) (F : TaskFrame) (hF : fc.Sat F) (M : TaskModel F)
    (τ : ConvexHistory F) (hτ : τ.IsTotal) (x : F.Duration) (v : ℕ → F.Duration) :
    StarTruthAt M τ x v φ := sorry

end FormalSystem.Semantics
```

Both bodies are `sorry` here because this section pins statements only. The real bodies are the
one-line delegations `StarValidOnFrames.of_forall_total h` and
`StarValidOnFrames.apply_total h F hF M τ hτ x v`, exactly as the L⁺ mirrors in
`FormalSystem/Semantics/PlusValidity.lean` are written; no `sorry` reaches the tree.

## Testing & Validation

- [ ] `lake build` green.
- [ ] `bash scripts/check-module-invariants.sh` exits 0.
- [ ] C14 PASS with the new TM⋆ entries in both heredocs, same order.
- [ ] C15 both assertions PASS; the second's row count includes the new TM⋆ rows.
- [ ] C9 / C9D report zero task-number citations under `FormalSystem/`, `docs/`, `scripts/`.
- [ ] `bash scripts/check-module-invariants.sh --emit-inventory --check` reports no byte change
      (generated README blocks untouched).
- [ ] `grep -rn 'starValidIn_of_forall_total\|starValidIn_apply_total' FormalSystem Tests` empty
      (unless the Phase 3 fallback branch applied, in which case the docstring correction is
      verified instead).
- [ ] No new `sorry` anywhere in the diff.

## Artifacts & Outputs

- `specs/574_record_soundness_invariant_and_tmstar_index/plans/01_record-soundness-invariant-tmstar-index.md`
  (this file)
- `specs/574_record_soundness_invariant_and_tmstar_index/summaries/01_record-soundness-invariant-tmstar-index-summary.md`
- `FormalSystem/Metalogic/Soundness.lean` — module docstring subsection recording the time-shift
  consumer set
- `FormalSystem/Metalogic/README.md` — one-line pointer
- `FormalSystem/StarLanguage/README.md` — `ofBase` rationale annotation
- `FormalSystem/Semantics/StarValidity.lean` — `StarValidIn.of_forall_total` / `.apply_total`
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` — adapters removed, call sites
  repointed, docstring updated
- `FormalSystem/StarLanguage/Axioms.lean`, `FormalSystem/StarLanguage/Derivation.lean`,
  `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` — `Paper:` docstring lines
- `docs/theorem-index.md` — TM⋆ ledger section, open-status bullet, notation row
- `scripts/check-module-invariants.sh` — C14 baseline pair extended

## Rollback/Contingency

Every phase is an independent commit, and no phase changes a proof, so `git revert` of any single
phase commit restores a green tree without touching the others. The one coupled pair is Phase 5's
`docs/theorem-index.md` rows and their declaration-site `Paper:` lines (hence
`Commit Mode: atomic-batch`) — reverting that one commit removes both halves together and C15
returns to its pre-phase row count.

If Phase 4's measurement shows a named declaration cannot be C14-pinned, do not invent a baseline
line for it. Omit its index row, and record the omission as a reasoned exclusion on Phase 5 with
the measured `#print axioms` output as evidence.

If Phase 3's move is blocked by an import cycle, take the documented fallback (correct the
`StarValidity.lean` docstring, record the cycle) rather than leaving the tree half-moved; the
phase closes on the fallback, not on the move.
