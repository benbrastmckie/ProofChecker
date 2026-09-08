# Implementation Plan: H/G completeness verdicts at Dense and Dedekind

- **Task**: 545 - Decide whether TM_d (Dense) and TM_dc (Dedekind) are weakly complete
- **Status**: [IMPLEMENTING]
- **Effort**: 9 hours
- **Dependencies**: 544
- **Research Inputs**: `specs/545_hg_completeness_dense_and_dedekind_verdicts/reports/01_hg-completeness-dense-dedekind.md`
- **Artifacts**: plans/01_hg-completeness-dense-dedekind.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

The research dispatch settled the two open H/G rows as far as evidence allows: **Dense is
expected complete with no obstruction found**, and **Dedekind is OPEN with its obstruction named
at declaration granularity**. Neither verdict can be upgraded to a machine-checked completeness
theorem inside this task — the Dense route's residual content is a BL-side canonical model
estimated at 2 500–4 000 lines, and the Dedekind route needs a discharge of Doets D1/D2 from `CO`
alone that nothing in this tree or in Mathlib bears on. This plan therefore lands the **whole of
the de-risking round** sorry-free (the machine-checked evidence that both closed rows'
obstructions fail to transfer, plus the single reusable chain-bundle interface that any future
canonical-model work will consume), records both verdicts as a canonical four-row table in the
`TMCompletenessReduction.lean` module docstring, and scopes the expensive remainder as follow-up
tasks. **Definition of done**: `lake build` green, every new declaration axiom-audited, zero
`sorry` in every file touched, no `TMComplete`/`Forward` theorem stated anywhere, and both
verdicts recorded in-tree with their evidence cited at declaration granularity.

### Research Integration

The plan is a direct execution of the report's Recommendations 1 and 2, with 3/4/5 converted into
scoped follow-up briefs rather than phases. Five findings are load-bearing here:

- **F1** (`□` is the universal modality over the whole model) is what makes the Kripke-to-task-frame
  transfer sound and fixes the box case of the Phase 3 induction. Landed as `bl_box_universal`.
- **F3** (`multiFamTaskFrameGen` / `multiFamGen_total_eq_range` already discharge all four frame
  axioms generically, and the total histories are *exactly* the translates) means the brief's route
  step (3) needs no frame construction at all — only a BL-level truth-transfer induction. Decision
  **D4** is honoured: no phase budgets for building task frames from chains.
- **F4** (the BL side has no time-shift lemma, and it is three lines via `truthAt_tr`) is Phase 1.
- **F5** (neither closed row's obstruction transfers: `Sp` is a TM_d *theorem*; `Z1` is refutable
  on ℚ) is Phase 2, and is the positive evidence behind the Dense verdict.
- **F6/D3** (borrowing the BL⁺ `Chronicle/` machinery *is* forward conservativity, hence circular)
  is a hard prohibition on every phase below. **F8** is the named Dedekind obstruction recorded in
  Phase 5.

Report decision **D6** is carried through unchanged: no completeness or forward-conservativity
theorem is stated anywhere in this round.

### Prior Plan Reference

No prior plan. This is round 01 for this task.

### Roadmap Alignment

No `roadmap_flag` and no `roadmap_path` were supplied in this dispatch's delegation context, so no
roadmap review/update phases are included and `specs/ROADMAP.md` is not modified by any phase. For
context only: the roadmap's Phase 1 records all four *BL⁺* weak-completeness rows as DONE
(`completeness_dense`, `completeness_rtime` among them); this task concerns the **H/G (BL) side**,
which the roadmap does not currently carry a row for. Recommendation 2's canonical four-row table
(Phase 5) is deliberately placed in `TMCompletenessReduction.lean`'s docstring rather than in
`ROADMAP.md`.

## Goals & Non-Goals

**Goals**: land `blTruthAt_timeShift`, `bl_box_universal`, `sp_derivable_dense`,
`sp_derivable_rtime`, `not_blValidDense_z1`, `chainSat`, `chainBundle_truth_lemma`,
`not_blValidIn_of_not_chainSat` — all sorry-free — and record the Dense/Dedekind verdicts in-tree.

**Non-Goals**:
- Proving `TMComplete FrameClass.Dense` or `Forward FrameClass.Dense`. The BL-MCS layer,
  canonicity, bulldozing and ℚ-realization it needs are report Recommendation 3, scoped as a
  follow-up task in Phase 6, not attempted here.
- Any Dedekind-row proof or refutation attempt (report Recommendations 4 and 5).
- Reusing, adapting, or importing any part of `Metalogic/BXCanonical/Chronicle/` for a BL-side
  argument — ruled out as circular by report D3/F6.
- Ingesting Bull 1968 / Burgess / Goldblatt. That is a prerequisite of the *Dedekind* follow-up,
  not of this round.
- Modifying `specs/ROADMAP.md`.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Report Appendix A.1's verbatim `bl_box_universal` names `WorldHistory F`, a type that **does not exist** in this checkout (repo-wide grep finds it only in `Boneyard/` and in a task-535 probe file). Copying it verbatim fails to elaborate. | M | H | Phase 1 substitutes `ConvexHistory F` (the type `BLTruthAt` actually takes) and drops the vestigial `σ₀` binder the report itself flags. Elaborate via `lean_run_code` before writing the file. |
| `TaskModel (multiFamTaskFrameGen D FamIdx)` relies on `instCoeOutFrameOver`, and `M.valuation`'s domain is `FamIdx × ↑D` only up to unfolding `FrameOver.toTaskFrame`. Unification may fail at reducible transparency. | M | M | Phase 3 elaborates the `chainSat`/`chainBundle_truth_lemma` signatures first, before any proof work. `Z1Countermodel.lean` already writes `valuation := fun w _ => 1 ≤ (ofLex w.2).1` at this exact frame, so the pattern is known to work through an `abbrev … : TaskFrame` ascription — reuse that ascription if bare unification fails. |
| The `.Dense` `Z1` countermodel needs `DenselyOrdered` on the duration carrier; `Z1Countermodel.lean`'s existing model is at `ℚ ×ₗ ℤ`, which is **not** densely ordered. | M | M | Phase 2 builds a *new* model at `TemporalOrder.of ℚ` (not a variant of `z1D`), reusing only the `multiFamTaskFrameGen`/`multiFamHistoryGen` scaffolding and the report's F5 valuation `p := {x | 1 ≤ x}`. |
| Bull's theorem (report step 6) is misremembered, or is stated for a different axiom than `CO`. | M | M | No phase asserts it. Phase 5 records the Dedekind verdict as OPEN and flags step 6 as medium-confidence, unverified against source; the literature ingest is gated into the follow-up brief. |
| The H/G logic of ℝ is strictly stronger than TM_dc (separability detectable), flipping Dedekind negative. | M | M | Phase 6's follow-up brief for the refutation probe (report Recommendation 5) is written *before* the positive-route brief, and says so, so the cheaper complete outcome is attempted first. |
| A future reader treats "Dense expected complete" as an asserted theorem. | H | M | Phase 5's docstring states the verdict as *expected, unproved*, names the residual content at declaration granularity, and repeats the `Conservativity.lean` prohibition verbatim. Phase 6 greps that no `theorem` in the diff concludes in `TMComplete _` or `Forward _`. |
| `state.json`'s `file_scope` names `FormalSystem/Semantics/BLTruth.lean` and `FormalSystem/Metalogic/Algebraic/FlowFrame.lean`, but neither is the right home: `BLTruth.lean` cannot see `truthAt_tr` (import direction), and `FlowFrame.lean` does not import BL semantics at all. | L | H | This plan targets `Conservativity/BaseLanguageSoundness.lean` plus two new `Conservativity/` modules, and reports the corrected scope via `proposed_file_scope`. `file_scope` is descriptive, not validated, and is never mutated by status-sync. |
| Adding a `@[simp]` attribute to a new lemma in a widely-imported module silently changes downstream elaboration. | M | L | Explicit constraint on Phases 1–4: no `@[simp]` on any new declaration. If one is genuinely wanted, the phase's Verification Tier escalates to `full`. |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3 | 1 |
| 3 | 4 | 3 |
| 4 | 5 | 2, 4 |
| 5 | 6 | 1, 2, 3, 4, 5 |

Phases within the same wave can execute in parallel.

### Phase 1: BL time-shift and the universal-modality lemma [COMPLETED]

**Goal**: Land the two BL-semantics lemmas the rest of the round depends on — time-homogeneity of
`BLTruthAt`, and the machine-checked statement that `□` is the universal modality over the whole
model (report F1/F4).

**Tasks**:
- [x] Elaborate both signatures against the live project with `lean_run_code` before editing any
      file; confirm `ConvexHistory F` (not `WorldHistory F`) and drop the vestigial `σ₀` binder.
- [x] Add `blTruthAt_timeShift` to `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean`,
      immediately after `truthAt_tr`, proved by the report's F4 chain:
      `(truthAt_tr …).symm` → `TimeShift.timeShift_preserves_truth` → `truthAt_tr`.
      *(deviation: altered — landed immediately after `truthAt_trCtx` rather than between
      `truthAt_tr` and `truthAt_trCtx`, so the bridge and its context-level corollary stay
      adjacent; the F4 chain itself went through as written, as a two-way `rw` through
      `truthAt_tr` rather than a `.symm`/`trans` composition.)*
- [x] Add `bl_box_universal` to the same module, proved by `truthAt_tr` + `Truth.box_const`
      (no induction). Keep `hτ : τ.IsTotal` in the signature — `Truth.box_const` binds it even
      though it does not consume it.
- [x] Write docstrings citing `Semantics/Truth.lean`'s `box_const` and
      `TimeShift.timeShift_preserves_truth`, and stating the consequence (BL over task frames is
      not a product logic in the hard sense).
- [x] Confirm `#print axioms` on both is `[propext]` or a subset of the tree's standard set.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

Additive declarations confined to one module, no existing signature changed. Blind spot the final
gate still covers: downstream `Conservativity/` modules that import this file are not rebuilt
in-phase. **Constraint**: no `@[simp]` attribute on either lemma; adding one escalates this phase
to `full`.

**Commit Mode**: per-substep

**Scope Hypothesis**: ~40 lines, 2 declarations, 1 file. Confirm at implementation time by
`git diff --stat` on `BaseLanguageSoundness.lean` after the phase; if the F4 three-line derivation
does not go through (e.g. `timeShift_preserves_truth`'s `(y - x)` shape resists), fall back to a
native induction on `BLFormula` mirroring `Truth.lean`'s `truthAt_of_truthCorr` route and record
the deviation.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` - add `blTruthAt_timeShift`
  and `bl_box_universal` after `truthAt_tr`; extend the module docstring's declaration list.

**Verification**:
- `lake build FormalSystem.Metalogic.Conservativity.BaseLanguageSoundness` green.
- `#print axioms blTruthAt_timeShift` and `#print axioms bl_box_universal` both clean.
- `grep -c sorry` on the file is 0.

---

### Phase 2: Neither closed row's obstruction transfers to Dense [COMPLETED]

**Goal**: Machine-check report F5 in a new module: `Sp` (the `.Base` dichotomy witness) is a
**TM_d theorem**, and `Z1` (the `.Discrete` witness) is **not `BLValidDense`**. Together these are
the positive evidence behind the Dense verdict — the Dense class does not split into two
H/G-definable subclasses, so no dichotomy witness is available.

**Tasks**:
- [x] Create `FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean` with the
      standard copyright header (`bash scripts/check-copyright-headers.sh` must pass) and a module
      docstring naming this file as the F5 record.
- [x] Land `sp_derivable_dense` from report Appendix A.2. Use `le_refl FrameClass.Dense` and
      `FrameClass.base_le _` for the `minFrameClass` side conditions — the report's Tactic Survey
      records that `by decide` **fails** here (free variables in the expected type); do not
      rediscover this.
- [x] Land `sp_derivable_rtime` by the `Dense ≤ RTime` lift. *(deviation: altered — there is no
      `DerivationTree` frame-class weakening lemma in the tree, so the `.Dense` derivation is
      restated at `.RTime` with `show FrameClass.Dense ≤ FrameClass.RTime from trivial` as the
      side condition, rather than transported along a lift.)*
- [x] Build the ℚ countermodel refuting `Z1` at `.Dense`: `TemporalOrder.of ℚ`,
      `multiFamTaskFrameGen` at `Unit`, valuation `p ↦ 1 ≤ w.2`, history `multiFamHistoryGen () 0`.
      Mirror `Z1Countermodel.lean`'s structure (`_atom_iff`, `_gp_iff`, the three `Z1`-part lemmas)
      but **do not** reuse `z1D = ℚ ×ₗ ℤ`, which is not densely ordered.
- [x] Prove `not_blValidDense_z1 (p : Atom) : ¬ BLValidDense (Conservativity.Z1 (BLFormula.atom p))`
      by exhibiting that countermodel, with the `DenselyOrdered ℚ` instance discharging
      `FrameClass.Sat .Dense`.
- [x] Wire the module into `FormalSystem/Metalogic/Conservativity.lean`'s import list and add a row
      to `FormalSystem/Metalogic/Conservativity/README.md`.

- [x] *(deviation: added — `attribute [nolint defsWithUnderscore] sp_derivable_dense
      sp_derivable_rtime`. The two Challenge signatures are `DerivationTree`-valued, hence `def`s,
      and `check-module-invariants.sh`'s C16 `env_linter` gate rejects snake_case `def` names.
      The plan's signatures are kept verbatim and the exemption is documented in-source with its
      justification; the alternative — restating both at `BaseLanguage.Derivable`, i.e.
      `Nonempty ∘ DerivationTree` — was tried, builds green, and was reverted because it weakens
      the recorded Challenge statement from data to `Prop`.)*

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: interface

The new module changes the import graph of the `Conservativity.lean` aggregator. Enumerated direct
dependents to build: `FormalSystem.Metalogic.Conservativity` (the aggregator) and
`FormalSystem.Metalogic.Conservativity.DenseObstructionTransfer` itself. Blind spot the final gate
still covers: transitive rebuilds beyond the aggregator, and `scripts/check-metalogic-cycles.sh`.

**Commit Mode**: per-substep

**Scope Hypothesis**: ~170 lines in 1 new file + 2 one-line edits (aggregator import, README row).
The 170 is extrapolated from `Z1Countermodel.lean`'s 205 lines minus the parts that do not recur.
Confirm with `wc -l` on the new file at phase end; a result above ~280 means the ℚ countermodel is
not in fact a close mirror of the existing one, and the phase should be re-scoped before
continuing rather than absorbed.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean` - **new**; all four
  declarations plus the ℚ model scaffolding.
- `FormalSystem/Metalogic/Conservativity.lean` - add the import.
- `FormalSystem/Metalogic/Conservativity/README.md` - add the module row.

**Verification**:
- `lake build FormalSystem.Metalogic.Conservativity` green.
- `#print axioms` clean on all four new declarations.
- `bash scripts/check-copyright-headers.sh` and `bash scripts/readme-lint.sh` pass.
- No `sorry` in the new file.

---

### Phase 3: The valuation-only chain-bundle truth lemma [COMPLETED]

**Goal**: Land the single reusable interface any future BL canonical-model work will consume: a
Kripke satisfaction predicate `chainSat` over `FamIdx × ↑D` (with `□` universal, per F1) and the
induction showing BL truth along a translate history matches it pointwise. Report F3/D4: the task
frame itself is already built and generic — only this induction is missing.

**Tasks**:
- [x] Create `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean`, importing
      `Conservativity.BaseLanguageSoundness` (for Phase 1's lemmas) and
      `FormalSystem.Metalogic.Algebraic.FlowFrame`. **Do not** add BL imports to `FlowFrame.lean` —
      it deliberately does not import BL semantics, and inverting that would couple
      `Metalogic/Algebraic/` to the base language.
- [x] Elaborate the `chainSat` and `chainBundle_truth_lemma` signatures with `lean_run_code`
      *before* writing proofs, to settle the `FrameOver`→`TaskFrame` coercion question early.
- [x] Define `chainSat (v : FamIdx × ↑D → Atom → Prop) : FamIdx × ↑D → BLFormula → Prop` with six
      clauses: `atom` = `v q p`; `bot` = `False`; `imp` = implication; **`box` = `∀ q', chainSat v q' φ`
      (universal over all points, both coordinates)**; `allPast`/`allFuture` = quantify the second
      coordinate within the fixed first coordinate by the `↑D` order.
- [x] Prove `chainBundle_truth_lemma` by induction on `φ` generalizing the base point. The
      `allPast`/`allFuture` cases are `BLTruth.past_iff`/`future_iff` plus the `w₀ + t` translation;
      the `box` case is `multiFamGen_total_eq_range` (total histories are exactly the translates)
      composed with Phase 1's `bl_box_universal` (truth is time-blind under `□`).
- [x] Wire into the `Conservativity.lean` aggregator and the `Conservativity/README.md`.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: interface

New module, aggregator import edit. Enumerated direct dependents to build:
`FormalSystem.Metalogic.Conservativity`. Blind spot the final gate still covers: the full
`Metalogic` rebuild and the cycle check.

**Commit Mode**: per-substep

**Scope Hypothesis**: ~140 lines, 1 new file, 2 declarations plus the six-clause `def`. The report
estimates the induction at ~100 lines. Confirm with `wc -l` at phase end. The signatures given in
`## Lean Challenge Statements` below are **plan-time provisional in their binder shape only** —
if `M.valuation`'s domain does not unify with `FamIdx × ↑D` at reducible transparency, introduce an
`abbrev … : TaskFrame` ascription in the style of `Z1Countermodel.lean`'s `z1F` and record the
adjusted signature in the phase notes; the *content* of each statement must not change.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean` - **new**.
- `FormalSystem/Metalogic/Conservativity.lean` - add the import.
- `FormalSystem/Metalogic/Conservativity/README.md` - add the module row.

**Verification**:
- `lake build FormalSystem.Metalogic.Conservativity` green.
- `#print axioms chainBundle_truth_lemma` clean.
- Sanity check: `chainSat`'s `box` clause takes no time argument (it must not, per F1).

---

### Phase 4: The countermodel-transfer corollary at Dense and Dedekind [NOT STARTED]

**Goal**: Expose the one interface the future canonical-model task consumes —
"a chain-model refutation of `φ` refutes `BLValidIn fc φ`" — and instantiate it at ℚ (Dense) and
ℝ (Dedekind), so the transfer step is closed for both rows regardless of which is pursued.

**Tasks**:
- [ ] Prove `not_blValidIn_of_not_chainSat`: given `fc.Sat (multiFamTaskFrameGen D FamIdx)`, a
      valuation `v`, a point `q` and `¬ chainSat v q φ`, conclude `¬ BLValidIn fc φ`. The model is
      just `⟨v⟩` (`TaskModel` has one field); the history is `multiFamHistoryGen`; totality is
      `multiFamHistoryGen_total`; the bridge is Phase 3's truth lemma.
- [ ] Instantiate at `D := TemporalOrder.of ℚ` and check `FrameClass.Sat .Dense` reduces to
      `DenselyOrdered ℚ` (via the `@[reducible]` chain `Sat .Dense ⇝ TaskFrame.IsDense ⇝
      DenselyOrdered`; `sat_intro` is the intended entry point).
- [ ] Instantiate at `D := TemporalOrder.of ℝ` and check `FrameClass.Sat .RTime` reduces to
      `F.IsDense ∧ F.IsComplete`. Record what the `IsComplete` half needs; if it does not fall out
      in under ~40 lines, leave the ℝ instantiation as an explicitly-noted gap in the phase notes
      rather than growing the phase — the Dense row is the one this task's verdict turns on.
- [ ] Add a module-docstring paragraph stating that this corollary, not the frame construction, is
      the brief's route step (3), and that the frame construction was already in-tree (F3/D4).

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

Additive declarations inside the module created in Phase 3; no new imports, no signature changes.
Blind spot the final gate still covers: the aggregator and downstream rebuild.

**Commit Mode**: per-substep

**Scope Hypothesis**: ~70 lines, 1 file, 1 theorem + 2 instantiation lemmas. The ℝ half is the
uncertain part; confirm by attempting `FrameClass.Sat .RTime (multiFamTaskFrameGen (TemporalOrder.of ℝ) Unit)`
via `lean_run_code` *first*, and drop it to a noted gap if it does not close quickly.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean` - add the corollary and the two
  instantiations.

**Verification**:
- `lake build FormalSystem.Metalogic.Conservativity` green.
- `#print axioms not_blValidIn_of_not_chainSat` clean.

---

### Phase 5: Record both verdicts in-tree [NOT STARTED]

**Goal**: Execute report Recommendation 2 — one canonical four-row status table in
`TMCompletenessReduction.lean`'s module docstring, with the Dense verdict stated as
*expected-complete, unproved, no obstruction* and the Dedekind verdict as *OPEN with the F8
obstruction named at declaration granularity*.

**Tasks**:
- [ ] Extend `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean`'s module
      docstring with a four-row table: `.Base` refuted (`SpCountermodel`/CEB), `.ZTime` refuted
      (`tmCompleteZTime_refuted`), `.Dense` expected complete, `.RTime` open.
- [ ] For the `.Dense` row, state: no obstruction found; both closed rows' witnesses provably fail
      to transfer (cite `sp_derivable_dense` and `not_blValidDense_z1` by name); the residual
      content is a BL-side canonical model — a BL-MCS layer over `BLFormula` (the
      `Metalogic/Core/` apparatus is `Formula`-only and does not transfer), canonicity for the
      eleven Base axioms plus DN, bulldozing, and a countable-ℚ realization via
      `Order.iso_of_countable_dense`; the transfer step is already closed by
      `not_blValidIn_of_not_chainSat`.
- [ ] For the `.RTime` row, state the F8 obstruction exactly: `doets_theorem_dense` needs
      `DoetsD1`/`DoetsD2`, whose only existing suppliers (`no_gaps_dense_prior`,
      `reynolds_theorem5`) are discharged through `chronicleMonadic_semanticPriorU/S/Sep`, which
      consume `Axiom.prior_U_gap` / `Axiom.prior_S_gap` / `Axiom.sep` — none of which is
      expressible in `BLFormula` (six constructors, no `untl`/`snce`/`kPlus`/`kMinus`). Note that
      `CO` is not Sahlqvist, so the Dense canonicity route does not carry over, and that the
      `sep`-is-separability signal leaves a **negative** Dedekind verdict live.
- [ ] Repeat the `Conservativity.lean` prohibition verbatim in the same docstring, and state
      explicitly that it forbids `sorry`-ing these theorems, not proving them — `forward` is
      refuted only at `.Base` and `.ZTime`.
- [ ] Add a one-line pointer from `FormalSystem/Metalogic/Conservativity/README.md` to the table
      as its canonical location.
- [ ] **Constraint**: no task numbers anywhere in these docstrings
      (`.claude/rules/no-task-references-in-deliverables.md`) — cite declaration names and file
      paths only. Do not cite the archived TM-completeness-status report by task number either.

**Timing**: 1.5 hours

**Depends on**: 2, 4

**Verification Tier**: local

Lean module docstrings are elaborated, not inert prose, so `prose` is not the right tier here (an
unterminated `/-! … -/` or a stray `--` breaks the build). One-module build is sufficient. Blind
spot the final gate still covers: downstream modules that quote or cross-reference this docstring.

**Commit Mode**: per-substep

**Scope Hypothesis**: ~90 docstring lines across 2 files, zero new declarations. Confirm by
`git diff --stat`; any *code* appearing in this phase's diff is out of scope and belongs in an
earlier phase.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` - module docstring only.
- `FormalSystem/Metalogic/Conservativity/README.md` - pointer line.

**Verification**:
- `lake build FormalSystem.Metalogic.Conservativity.TMCompletenessReduction` green.
- `bash .claude/scripts/check-task-references.sh` (or the equivalent repo lint) reports no
  task-number reference in either file.
- `git diff` on this phase contains no `theorem`, `def`, or `lemma` line.

---

### Phase 6: Final gate, verdict audit, and follow-up scoping [NOT STARTED]

**Goal**: Run the full repository gate set, audit that the round asserted nothing it should not,
and write the three follow-up task briefs the report's Recommendations 3–5 call for.

**Tasks**:
- [ ] `lake build` (full) green.
- [ ] `bash .claude/scripts/lean-sorry-census.sh` — confirm the census is unchanged except for
      zero additions; no `sorry` in any file this task touched.
- [ ] `#print axioms` on all eight new declarations; record the axiom sets in the execution
      summary.
- [ ] **Prohibition audit**: grep the task's whole diff for any `theorem`/`lemma` whose conclusion
      is `TMComplete _`, `Forward _`, `TMCompleteDense`, `ForwardDense`, `TMCompleteRTime`, or
      `ForwardRTime`. There must be none. Record the grep and its empty result as evidence.
- [ ] `bash scripts/check-metalogic-cycles.sh`, `bash scripts/check-module-invariants.sh`,
      `bash scripts/check-copyright-headers.sh`, `bash scripts/readme-lint.sh` — all pass. The two
      new modules are reachable from the `Conservativity.lean` aggregator, so **no**
      `module-invariants-manifest.txt` entry is owed; confirm rather than assume.
- [ ] Write three follow-up task briefs into the execution summary, in this order:
      **(a) the Dedekind refutation probe** (report Rec. 5 — is there an H/G formula valid on ℝ but
      refuted on a Dedekind-complete non-separable dense unbounded chain? A yes is a complete
      outcome at a fraction of the cost, and `not_blValidIn_of_not_chainSat` is the interface it
      consumes); **(b) the Dense canonical model** (Rec. 3, est. 2 500–4 000 lines, with per-phase
      sorry-free milestones: BL-MCS layer → canonical frame → canonicity per axiom → bulldozing →
      ℚ realization, and `TMComplete` stated only in the last); **(c) the Dedekind positive route**
      (Rec. 4, gated on ingesting Burgess or Gabbay–Hodkinson–Reynolds first, and on (b) landing).
- [ ] Note in the summary that (a) is listed before (b) deliberately, because it is the cheaper
      path to a complete outcome and because a positive Dedekind result is not the prior the
      `sep`-is-separability signal supports.

**Timing**: 1 hour

**Depends on**: 1, 2, 3, 4, 5

**Verification Tier**: full

The complete gate set for the repository. Nothing is deferred past this tier.

**Commit Mode**: per-substep

**Scope Hypothesis**: 8 new declarations total across 3 files (1 modified, 2 new), plus 2 docstring
files. Confirm the count mechanically at phase start by grepping the diff for
`^(noncomputable )?(theorem|def|lemma) ` across the task's changed `.lean` files; a count other
than 8 means an earlier phase drifted and must be reconciled before the gate is declared green.

**Files to modify**:
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/summaries/01_hg-completeness-dense-dedekind-summary.md` - **new**; the execution summary carrying the verdicts, the axiom audit, and the three follow-up briefs.

**Verification**:
- Full `lake build` green from a clean-ish state.
- All four repo lint scripts pass.
- The prohibition grep returns empty, with the command and output recorded.

## Lean Challenge Statements

```lean
import FormalSystem.Metalogic.Conservativity.SpWitness
import FormalSystem.Metalogic.Conservativity.Z1Countermodel
import FormalSystem.Metalogic.Algebraic.FlowFrame

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic
open FormalSystem.Metalogic.Algebraic

/-- Phase 1: time-homogeneity of `BLTruthAt`, the BL mirror of
`Semantics.TimeShift.timeShift_preserves_truth`. -/
theorem blTruthAt_timeShift {F : TaskFrame} (M : TaskModel F) (σ : ConvexHistory F)
    (x y : F.Duration) (φ : BLFormula) :
    BLTruthAt M (ConvexHistory.timeShift σ (y - x)) x φ ↔ BLTruthAt M σ y φ := sorry

/-- Phase 1: `□` is the universal modality over the whole model — history-blind by definition,
time-blind by `Truth.box_const`. -/
theorem bl_box_universal {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (t : F.Duration) (hτ : τ.IsTotal) (φ : BLFormula) :
    BLTruthAt M τ t φ.box ↔ ∀ (σ : ConvexHistory F), σ.IsTotal → ∀ s, BLTruthAt M σ s φ := sorry

/-- Phase 2: the `.Base` dichotomy witness `Sp` is a TM_d theorem, so it cannot separate at
`.Dense`. -/
noncomputable def sp_derivable_dense (φ ψ : BLFormula) :
    ⊢ᴮᴸ[FrameClass.Dense] Sp φ ψ := sorry

/-- Phase 2: the same, lifted along `Dense ≤ RTime`. -/
noncomputable def sp_derivable_rtime (φ ψ : BLFormula) :
    ⊢ᴮᴸ[FrameClass.RTime] Sp φ ψ := sorry

/-- Phase 2: the `.Discrete` witness `Z1` is refutable on ℚ, so it is not `.Dense`-valid and
cannot separate either. -/
theorem not_blValidDense_z1 (p : Atom) :
    ¬ BLValidDense (Conservativity.Z1 (BLFormula.atom p)) := sorry

/-- Phase 3: Kripke satisfaction on a disjoint union of `D`-chains, with `□` universal over all
points (both coordinates) and `H`/`G` quantifying the second coordinate within a fixed chain. -/
noncomputable def chainSat {D : TemporalOrder} {FamIdx : Type} [Nonempty FamIdx]
    (v : FamIdx × ↑D → Atom → Prop) (q : FamIdx × ↑D) (φ : BLFormula) : Prop := sorry

/-- Phase 3: BL truth along a translate history of `multiFamTaskFrameGen` matches `chainSat`
pointwise. The `box` case is `multiFamGen_total_eq_range` plus `bl_box_universal`. -/
theorem chainBundle_truth_lemma {D : TemporalOrder} {FamIdx : Type} [Nonempty FamIdx]
    (M : TaskModel (multiFamTaskFrameGen D FamIdx)) (f : FamIdx) (w₀ t : ↑D) (φ : BLFormula) :
    BLTruthAt M (multiFamHistoryGen (D := D) f w₀) t φ ↔ chainSat M.valuation (f, w₀ + t) φ :=
  sorry

/-- Phase 4: the single interface a future BL canonical model consumes — any chain-model
refutation is a task-frame refutation at every `fc` the chain frame satisfies. -/
theorem not_blValidIn_of_not_chainSat {fc : FrameClass} {D : TemporalOrder}
    {FamIdx : Type} [Nonempty FamIdx]
    (hSat : fc.Sat (multiFamTaskFrameGen D FamIdx))
    (v : FamIdx × ↑D → Atom → Prop) (q : FamIdx × ↑D) (φ : BLFormula)
    (h : ¬ chainSat v q φ) : ¬ BLValidIn fc φ := sorry
```

## Testing & Validation

- [ ] Full `lake build` green.
- [ ] Zero `sorry` in every file this task creates or modifies (`.claude/scripts/lean-sorry-census.sh`).
- [ ] `#print axioms` clean on all eight new declarations (`[propext]`, or a subset of
      `[propext, Classical.choice, Quot.sound]`).
- [ ] Prohibition audit: no `theorem`/`lemma` in the task's diff concludes in `TMComplete _`,
      `Forward _`, or any of their four named specializations.
- [ ] `bash scripts/check-metalogic-cycles.sh` passes (the two new `Conservativity/` modules
      introduce no cycle; in particular neither imports `Conservativity.lean` itself).
- [ ] `bash scripts/check-module-invariants.sh` passes with **no** new
      `module-invariants-manifest.txt` entry (both new modules are reachable via the aggregator).
- [ ] `bash scripts/check-copyright-headers.sh` and `bash scripts/readme-lint.sh` pass.
- [ ] No task-number reference in any `FormalSystem/**` file touched.
- [ ] `chainSat`'s `box` clause is verified by inspection to carry no time argument — if it does,
      F1 has been mis-transcribed and Phase 3 must be redone.

## Artifacts & Outputs

- `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` (modified) —
  `blTruthAt_timeShift`, `bl_box_universal`.
- `FormalSystem/Metalogic/Conservativity/DenseObstructionTransfer.lean` (new) —
  `sp_derivable_dense`, `sp_derivable_rtime`, `not_blValidDense_z1`, plus the ℚ countermodel.
- `FormalSystem/Metalogic/Conservativity/ChainBundleTruth.lean` (new) — `chainSat`,
  `chainBundle_truth_lemma`, `not_blValidIn_of_not_chainSat`, plus the ℚ/ℝ instantiations.
- `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` (modified, docstring only) —
  the canonical four-row verdict table.
- `FormalSystem/Metalogic/Conservativity.lean` and
  `FormalSystem/Metalogic/Conservativity/README.md` (modified) — wiring and index rows.
- `specs/545_hg_completeness_dense_and_dedekind_verdicts/summaries/01_hg-completeness-dense-dedekind-summary.md`
  (new) — verdicts, axiom audit, and the three follow-up task briefs.

## Rollback/Contingency

Every phase is a separate commit and the two Lean modules added are new files reachable only
through the `Conservativity.lean` aggregator, so reverting is `git revert` of the phase commits
plus deletion of the two new files; nothing else in the tree depends on them. Phase 1's two
lemmas are the only edits to an existing Lean module with content, and they are purely additive
(no `@[simp]`, no signature change), so reverting them cannot break a downstream proof.

If Phase 3's induction stalls, Phases 1, 2 and 5 still constitute a complete, committable outcome:
the verdicts are recorded and the obstruction-transfer evidence is machine-checked, with the
chain-bundle interface deferred into the Dense-canonical-model follow-up brief. In that case mark
Phase 3 `[PARTIAL]`, drop Phase 4, and say so explicitly in the Phase 5 docstring — do **not**
state the interface as though it existed. Under no circumstance is any completeness or
forward-conservativity theorem stated and discharged with `sorry`; that failure mode is worse than
an abandoned phase.
