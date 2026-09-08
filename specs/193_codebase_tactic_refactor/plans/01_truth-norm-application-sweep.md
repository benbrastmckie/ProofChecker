# Implementation Plan: Task #193

- **Task**: 193 - Codebase tactic refactor (truth-layer simp-normal-form application sweep)
- **Status**: [IMPLEMENTING]
- **Effort**: 7.5 hours
- **Dependencies**: 165, 402, 448, 470, 508, 519, 521, 522 — all archived/completed; verified at plan time
- **Research Inputs**: `specs/193_codebase_tactic_refactor/reports/01_codebase-refactor-seed.md` (2026-05-22 seed report — **superseded**, see Research Integration)
- **Artifacts**: plans/01_truth-norm-application-sweep.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

This is a **mechanical application pass**, not an infrastructure task. Task 521 already defined
the truth-layer simp-normal form (`register_simp_attr truth_norm`, `register_simp_attr swap_norm`,
and eleven new `@[simp, truth_norm]` `Truth.*_iff` lemmas) and rewrote eleven soundness proofs as
its proof of concept. It explicitly left the mechanical sweep to a follow-on task, naming the two
files by name in its summary: *"FrameClassVariants.lean (37 sites) and Decidable.lean (27 sites)
are untouched. The mechanical sweep across them is a separate task's charter."* This task is that
charter, restricted by the 2026-09-01 re-scope to `Metalogic/Soundness.lean` and
`Metalogic/SoundnessLemmas/FrameClassVariants.lean` (Decidable.lean is out of scope).

The deliverable is measured reduction in existing proof text at those two files. The work is
replacing hand-enumerated simp lists with the registered simp sets, verifying each site preserves
the goal, and rewriting the small minority of proof bodies where it does not.

### Research Integration

**The linked seed report is superseded and must not be used as a work list.** It was written
2026-05-22 against the pre-rename `Theories/Bimodal/` tree, targets `Theorems/` with `tm_prove`,
and proposes a 40-hour six-phase refactor of ~120 proofs. Every one of those premises has since
been retracted: `tm_prove` was abandoned, `Theorems/` was ruled out by the codebase tactic survey,
the tree was renamed to `FormalSystem/`, and the 2026-09-01 tactics review (findings A-13, D-06,
D-10, D-20) re-scoped this task to the truth-simp half only. The authoritative charter is the task
description as re-scoped, plus the two grounding sources below.

Grounding actually used, all re-verified against the working tree at plan time:

1. **`FormalSystem/Automation/TruthNormAttr.lean`** declares `truth_norm` and `swap_norm`, and
   records that a `truth_simp` macro *did* exist and **was deliberately retired** to
   `Boneyard/RetiredTactics/` for zero adoption: *"Write the `simp only` out; it is the same
   length and says what it does."* The task description names `truth_simp` as the instrument;
   that macro no longer exists and re-creating it would reverse a recorded decision and
   contradict review finding D-20's argument against tactic macros here. **The instrument for
   this task is `simp only [truth_norm]` / `simp only [swap_norm]`, written out.** This is a
   substitution of vehicle, not of scope: the completion criterion is unchanged.
2. **`FormalSystem/Semantics/Truth.lean`'s "Simp-normal form" docstring section** carries the
   load-bearing mechanical caveat, quoted here because it defines the hard class of sites:
   *"Adding these names to a list that still mentions `Formula.and` / `Formula.or` /
   `Formula.neg` is a no-op: simp rewrites bottom-up, so the syntax-unfolding lemmas fire on the
   argument before the `TruthAt`-headed characterization lemma can match. The syntax lemmas have
   to come **out** of the list as the characterization lemmas go in."*

**Empirical probes run at plan time** (`lean_multi_attempt`, warm build cache, clean tree). These
convert the plan's central assumptions from guesses into facts:

| Probe site | Before | After | Result |
|---|---|---|---|
| `Soundness.lean:159` | `simp only [TruthAt]` | `simp only [truth_norm]` | **identical goal** |
| `Soundness.lean:246` | `simp only [TruthAt, Truth.future_iff]` | `simp only [truth_norm]` | **identical goal** |
| `FrameClassVariants.lean:110` | `simp only [Formula.swap_temporal_all_future, Formula.swapTemporal]` | `simp only [swap_norm, Formula.swapTemporal]` | **identical goal** |
| `FrameClassVariants.lean:294` | `simp only [Formula.swapTemporal, Formula.and, Formula.neg, TruthAt]` | `simp only [Formula.swapTemporal, truth_norm]` | **different goal** (cleaner, but the proof body below no longer applies) |
| `FrameClassVariants.lean:294` | — | `simp only [swap_norm, truth_norm]` | **`simp` made no progress** (error) |

Two further facts established at plan time:

- `truth_norm` and `swap_norm` resolve in **both** target files with **no import change** — both
  reach `TruthNormAttr.lean` transitively through `FormalSystem.Semantics.Validity` → `Truth.lean`.
  The `Soundness.lean:159` probe elaborated cleanly, which is the proof.
- **`truth_norm` currently has zero use sites anywhere in `FormalSystem/` or `Tests/`.** Task 521
  built the set and then rewrote its eleven PoC proofs by naming lemmas individually rather than
  by invoking the set. This task is therefore the set's first adoption, and every site it converts
  is a net-new use.

### Prior Plan Reference

No prior plan for this task. Task 521's plan and summary
(`specs/archive/521_truth_layer_simp_normal_form/`) were read as calibration input, not as a
template. Two lessons carried forward: (a) 521 reported honestly that two of its eleven proofs got
*longer*, so this plan does not promise per-declaration shrinkage, only site-count reduction —
which is what the completion criterion actually measures; (b) 521's own metric ("sites") is broader
than this task's criterion grep, so this plan tracks **both** metrics explicitly rather than
letting them be confused.

### Roadmap Alignment

No `roadmap_path` in the dispatch context and no `roadmap_flag`. Not consulted; no ROADMAP.md
phases added.

## Goals & Non-Goals

**Goals**:

- Drive `simp only [TruthAt` occurrences across `Metalogic/Soundness.lean` and
  `Metalogic/SoundnessLemmas/FrameClassVariants.lean` down by at least 80% from the measured
  baseline of 60, by replacing hand-enumerated lists with `simp only [truth_norm]`.
- Collapse the 13 `Formula.swap_temporal_*`-naming simp lists in `FrameClassVariants.lean` to
  `simp only [swap_norm, …]`.
- Address the syntax-lemma-mixed sites (the Truth.lean caveat class) honestly: convert those that
  can be converted within budget, and record the rest as enumerated, reasoned exclusions.
- Leave `lake build` green, `check-module-invariants.sh` passing, and the C2 axiom baseline for
  the flagship theorems unchanged.

**Non-Goals**:

- Any new tactic, macro, or elaborator — including re-creating the retired `truth_simp` macro.
- `Theorems/` refactoring, `tm_prove`, `modal_search`, or any other search-family tactic.
- `Metalogic/Decidability/Verified/Decidable.lean` (27 sites) — named by 521 as untouched, and
  excluded from this task by the 2026-09-01 re-scope, which names only the two files above.
- `Semantics/Truth.lean` and `Semantics/BLTruth.lean` sites — those *are* the characterization
  proofs; unfolding `TruthAt` there is irreducible, as 521 already recorded.
- Any change to theorem or lemma **statements**. This pass edits proof bodies only.
- Any binder/intro macro (`intros_validity` and friends). Dropped by the re-scope; task 522
  already normalized the intro chains, and both target files now contain **zero**
  `intro F M Omega` occurrences — verified at plan time, so that half of the original charter is
  already discharged and needs no work.

## Measured Baseline

All counts re-verified against the working tree at plan time (clean tree, warm `.lake` cache).

| Metric | Soundness.lean | FrameClassVariants.lean | Total |
|---|---|---|---|
| **Criterion metric**: `grep -c 'simp only \[TruthAt'` | 41 | 19 | **60** |
| Broad metric: any `simp only [...]` list containing `TruthAt` | 46 | 35 | 81 |
| `Formula.swap_temporal_*` named in a `simp only` list | 0 | 13 | 13 |
| `simp only [truth_norm]` occurrences | 0 | 0 | 0 |
| `intro F M Omega` occurrences | 0 | 0 | 0 |
| File length (lines) | 1598 | 836 | 2434 |

**Site classification** (the split that drives the phase structure):

- **Class A — clean drop-in.** The simp list names only `TruthAt` and `Truth.*_iff` lemmas, so
  `simp only [truth_norm]` is goal-identical (both probes above are Class A sites).
  Soundness 37, FrameClassVariants 19 → **56 sites**.
- **Class B — syntax-lemma-mixed (the Truth.lean caveat class).** The list mixes
  `Formula.and` / `Formula.or` / `Formula.neg` / `Formula.top` / `Formula.kPlus` /
  `Formula.kMinus` / `Formula.swapTemporal` with `TruthAt`. Converting changes the goal shape, so
  the proof body below must be rewritten. Soundness 10 (lines 410, 594, 605, 1022, 1027, 1094,
  1099, 1129, 1242, 1254), FrameClassVariants 16 (lines 53, 71, 167, 294, 312, 332, 345, 360,
  382, 408, 445, 501, 519, 578, 787, 802) → **26 sites**.
- **Class C — `swap_norm` collapse.** FrameClassVariants only, **13 sites**. Independent of the
  criterion metric (these lists do not mention `TruthAt`).

**Criterion arithmetic.** Only 4 of the 26 Class B sites (Soundness 1022/1027/1094/1099, the
`kPlus`/`kMinus` ones) lead with `TruthAt` and are therefore inside the criterion metric's 60.
Converting Class A alone takes the metric 60 → 4, a **93% reduction** against a required 80%
(≤ 12). The criterion is therefore satisfiable by Phases 2–4 with margin, and Phase 5 (Class B)
is upside rather than a load-bearing dependency. This margin is deliberate: it is what allows
Phase 5 to record exclusions honestly instead of forcing risky rewrites to hit a number.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|---|---|---|---|
| `truth_norm` is strictly larger than the hand-written list and over-rewrites, breaking the tactic steps below a site | M | M | Class A/B split is exactly this distinction. Convert in small batches (≤10 sites), rebuild the module after each batch, revert any site whose proof no longer closes and reclassify it as Class B |
| Class B conversion changes goal shape and the proof body cannot be re-derived within budget | M | H (confirmed at `FCV:294` by probe) | Class B is isolated in Phase 5, which is explicitly permitted to close as `[COMPLETED WITH EXCLUSIONS]` with each un-converted site enumerated and reasoned. The criterion does not depend on it |
| A proof that closed under a narrow `simp only` closes under `truth_norm` but leaves a differently-shaped hypothesis that a later `exact`/`rw` in the *same* proof depends on | M | M | Per-batch `lake build` of the edited module (tier `local`); full gate at Phase 6 |
| Editing `FrameClassVariants.lean` forces a rebuild of `Soundness.lean` (it is an upstream import), masking which file caused a failure | L | M | Phase order puts FrameClassVariants first and takes it to green before any Soundness edit; phases never edit both files |
| `truth_norm` membership changes simp behavior for downstream modules that inherit the set | L | L | This task adds no `@[truth_norm]` tags and changes no lemma. It only *uses* the existing set at call sites, so no downstream simp set changes |
| Re-creating the retired `truth_simp` macro because the task description names it | L | M | Explicitly forbidden in Non-Goals and restated in the Phase 1 checklist; the retirement rationale is quoted in Research Integration |
| The 2 multi-line simp lists in FrameClassVariants (lines 269, 281) are miscounted by single-line greps | L | M | Phase 1's measurement script reports both a line-count and a form-count so the discrepancy is visible rather than silent |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |
| 5 | 5 | 4 |
| 6 | 6 | 5 |

The chain is linear by design rather than by dependency poverty. Phases 2 and 3 have disjoint file
territory (`FrameClassVariants.lean` vs `Soundness.lean`) and would be territory-safe in parallel,
but `Soundness.lean` imports `FrameClassVariants.lean` and the two share one working tree and one
`.lake` cache, so a parallel run makes a build failure ambiguous between them. Sequencing
FrameClassVariants to green first removes that ambiguity for the cost of no wall-clock that
matters at this size.

---

### Phase 1: Baseline capture and conversion harness [COMPLETED]

**Goal**: Freeze the measured baseline in a reproducible artifact and confirm the preconditions,
so every later phase's claim is checkable rather than asserted.

**Tasks**:
- [x] Write `specs/193_codebase_tactic_refactor/baseline.txt` recording, per file: the criterion
      metric (`grep -c 'simp only \[TruthAt'`), the broad metric (`simp only [...]` lists
      containing `TruthAt`), the `Formula.swap_temporal_*` count, the `truth_norm` count, and the
      file line count. Expect 41/19, 46/35, 0/13, 0/0, 1598/836 *(deviation: altered — criterion 41/19 and swap 0/13 confirmed exactly; observed broad metric is 48/37, not 46/35, a grep-shape difference recorded as authoritative in baseline.txt)*
- [x] Record the enumerated Class B line numbers (Soundness: 410, 594, 605, 1022, 1027, 1094,
      1099, 1129, 1242, 1254; FrameClassVariants: 53, 71, 167, 294, 312, 332, 345, 360, 382, 408,
      445, 501, 519, 578, 787, 802) into `baseline.txt`, re-derived by grep rather than copied
      from this plan *(deviation: altered — re-derivation found 30 Class B sites, not 26: the plan omitted Soundness 354 and 992 and FrameClassVariants 606 and 641. Observed split recorded as authoritative; Soundness Class A is therefore 36, not 37)*
- [x] Run `lake build` and record the job count and error count as the green baseline
- [x] Run `bash scripts/check-module-invariants.sh` and record the result
- [x] Record the C2 axiom baseline for the flagship theorems (`#print axioms`, expected
      `[propext, Classical.choice, Quot.sound]`) and the executable-`sorry` inventory located **by
      content**, not by line number — the description's expected single executable sorry is in
      `FormalSystem/Metalogic/WeakCanonical/Transfer.lean` *(deviation: altered — the description's "1 sorry in Transfer.lean" is stale. By-content search finds ZERO executable sorries outside Boneyard/; Transfer.lean's `sorry` hits are all prose in docstrings. The invariant to preserve is zero, not one. C2/C3 are both asserted by check-module-invariants.sh, which passed)*
- [x] Confirm `truth_norm` and `swap_norm` resolve in both target files with no import edit
      (a one-site `lean_multi_attempt` in each file suffices; do not add imports)

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: The counts in the Measured Baseline table (60 criterion sites, 81 broad, 13
swap, 26 Class B) and the enumerated Class B line numbers are plan-time measurements and are
hypotheses. Confirm by re-running the greps at implementation time and writing the *observed*
numbers into `baseline.txt`. If an observed count differs from this plan, record the observed
number as authoritative, restate the 80%-reduction target against it, and note the discrepancy in
the phase entry — do not edit the observation to match the plan.

**Files to modify**:
- `specs/193_codebase_tactic_refactor/baseline.txt` - new; measurement record (no Lean source touched)

**Verification**:
- `baseline.txt` exists and contains every metric above with its observed value
- `lake build` green, `check-module-invariants.sh` passing, C2 baseline recorded
- No `.lean` file modified in this phase (`git status --short FormalSystem/` empty)

---

### Phase 2: FrameClassVariants.lean — Class A sweep [COMPLETED]

**Goal**: Replace all 19 Class A hand-enumerated lists in `FrameClassVariants.lean` with
`simp only [truth_norm]`, module green.

**Tasks**:
- [x] Convert the 19 Class A sites (lines 90, 111, 144, 196, 210, 223, 235, 247, 259, 271, 283,
      479, 489, 539, 559, 675, 688, 816, 831 — re-derive by grep, line numbers shift as edits land)
      to `simp only [truth_norm]` *(all 19 converted, zero reclassified; re-derived by grep, line numbers matched the plan exactly since every edit is a 1-for-1 line replacement)*
- [x] Work in batches of at most 10 sites; after each batch run
      `lake build FormalSystem.Metalogic.SoundnessLemmas.FrameClassVariants` *(deviation: altered — invoked through the mandatory build guard as `lake-build-guard.sh build --timeout 1800 -- build <module>`, detached. Batch 1 = 10 sites, batch 2 = 9 sites; both green at 876 jobs)*
- [x] For any site whose proof no longer closes: revert that one site, reclassify it as Class B in
      `baseline.txt`, and leave it for Phase 5. Do not force it here *(no site required reverting; zero reclassifications)*
- [x] Commit each green batch (per-substep mandate)

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Scope Hypothesis**: "19 Class A sites at those lines" is a hypothesis. Confirm by
`grep -n 'simp only \[TruthAt' FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`
before starting; the count must match `baseline.txt`. Report the actual number converted and the
actual number reclassified.

**Files to modify**:
- `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean` - Class A simp lists → `simp only [truth_norm]`

**Verification**:
- `lake build FormalSystem.Metalogic.SoundnessLemmas.FrameClassVariants` green
- `grep -c 'simp only \[TruthAt'` on the file is 0, or equals the number of reclassified sites
- No theorem or lemma **statement** changed: `git diff` shows edits inside `by` blocks only

---

### Phase 3: Soundness.lean — Class A sweep, first block [IN PROGRESS]

**Goal**: Convert the 28 Class A sites in the first half of `Soundness.lean` (lines 159–552),
module green.

**Tasks**:
- [ ] Convert the 28 Class A sites at lines 159, 167, 175, 183, 192, 201, 212, 221, 226, 237, 246,
      255, 265, 276, 286, 306, 318, 389, 399, 422, 455, 468, 500, 511, 521, 530, 541, 552 to
      `simp only [truth_norm]` (re-derive by grep; line numbers shift as edits land)
- [ ] Batch at most 10 sites, then `lake build FormalSystem.Metalogic.Soundness`
- [ ] Reclassify-and-revert any site that does not close; leave it for Phase 5
- [ ] Commit each green batch

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Scope Hypothesis**: "28 Class A sites in lines 159–552" is a hypothesis. Confirm against
`baseline.txt` before starting and report the actual converted/reclassified split.

**Files to modify**:
- `FormalSystem/Metalogic/Soundness.lean` - lines ~159–552, Class A simp lists → `simp only [truth_norm]`

**Verification**:
- `lake build FormalSystem.Metalogic.Soundness` green
- `grep -c 'simp only \[TruthAt'` on `Soundness.lean` dropped by the number converted
- No statement changed; `git diff` confined to `by` blocks

---

### Phase 4: Soundness.lean — Class A sweep, second block [NOT STARTED]

**Goal**: Convert the remaining 9 Class A sites in `Soundness.lean` (lines 692–1306), taking the
criterion metric to its target. This is the phase at which the completion criterion should
mechanically pass.

**Tasks**:
- [ ] Convert the 9 Class A sites at lines 692, 702, 792, 992, 1236, 1249, 1269, 1303, 1306 to
      `simp only [truth_norm]` (re-derive by grep)
- [ ] `lake build FormalSystem.Metalogic.Soundness` after the batch
- [ ] Re-run the criterion metric across both files and record the running total in `baseline.txt`.
      Expected: 60 → 4 (93% reduction) if nothing was reclassified
- [ ] If the metric has not reached ≤ 12, identify which sites remain and whether any Class A site
      was reclassified; state the number plainly rather than adjusting the target
- [ ] Commit

**Timing**: 1 hour

**Depends on**: 3

**Verification Tier**: local

**Scope Hypothesis**: "9 Class A sites at lines 692–1306" and "the criterion metric reaches 60 → 4"
are hypotheses. Confirm the first by grep before starting; confirm the second by re-running the
criterion metric across both files after the batch and writing the observed total into
`baseline.txt`.

**Files to modify**:
- `FormalSystem/Metalogic/Soundness.lean` - lines ~692–1306, Class A simp lists → `simp only [truth_norm]`

**Verification**:
- `lake build FormalSystem.Metalogic.Soundness` green
- Combined criterion metric across both files is ≤ 12 (≥80% reduction from 60), with the observed
  number recorded
- No statement changed

---

### Phase 5: Class B caveat sites and `swap_norm` collapse [NOT STARTED]

**Goal**: Collapse the 13 `Formula.swap_temporal_*` lists to `swap_norm` (mechanical, probe-
confirmed), and convert as many of the 26 Class B syntax-lemma-mixed sites as can be re-derived
within budget, enumerating the rest as reasoned exclusions.

**Tasks**:
- [ ] **Class C first** (mechanical, low risk): replace the 13 `Formula.swap_temporal_*` names in
      `FrameClassVariants.lean` simp lists with `swap_norm`, keeping any `Formula.swapTemporal`
      entry in place. Note lines 269 and 281 are multi-line lists. Build and commit
- [ ] **Class B next**: for each site, remove the syntax-unfolding lemmas (`Formula.and`,
      `Formula.or`, `Formula.neg`, `Formula.top`, `Formula.kPlus`, `Formula.kMinus`) from the list
      as `truth_norm` goes in — per the Truth.lean caveat, leaving them in makes the change a
      no-op. Keep `Formula.swapTemporal` where the goal is `.swapTemporal`-headed: `swap_norm`
      does **not** unfold the definition (probe-confirmed at `FCV:294`)
- [ ] Attempt Soundness Class B (10 sites) and FrameClassVariants Class B (16 sites) one site at a
      time, rebuilding the module after each. Time-box each site; a site that does not close within
      its box is reverted, not fought
- [ ] Record every un-converted site in a `#### Reasoned Exclusions` block under this phase: file,
      line, the goal-shape change observed, and why the body rewrite was out of budget
- [ ] Commit each green site or small green group

**Timing**: 2 hours

**Depends on**: 4

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: "13 Class C sites and 26 Class B sites" is a hypothesis, and the assumption
that Class B sites need proof-body rewrites is confirmed for exactly one site (`FCV:294`) and
extrapolated to the rest. Confirm both by grep and by per-site attempt; report how many Class B
sites turned out to be clean drop-ins after all, and how many needed a body rewrite.

**Files to modify**:
- `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean` - 13 Class C + 16 Class B sites
- `FormalSystem/Metalogic/Soundness.lean` - 10 Class B sites

**Verification**:
- `lake build` green for both modules after every site
- All 13 Class C sites converted (this sub-goal is mechanical and is expected to complete fully)
- Every Class B site is either converted or listed in `#### Reasoned Exclusions` with a reason —
  no site is silently skipped
- If any Class B site remains, this phase closes as `[COMPLETED WITH EXCLUSIONS]`, not `[COMPLETED]`

---

### Phase 6: Full gate, measurement report, and summary [NOT STARTED]

**Goal**: Run the complete repository gate set, score the completion criterion against the frozen
baseline, and write the execution summary.

**Tasks**:
- [ ] `lake build` full — green, job count comparable to the Phase 1 baseline, 0 errors
- [ ] `bash scripts/check-module-invariants.sh` — ALL CHECKS PASSED
- [ ] C2 axiom baseline for the flagship theorems unchanged from Phase 1's record
- [ ] Executable `sorry` inventory unchanged, located **by content** (`grep` for a bare `sorry`
      tactic, not by line number); confirm the single executable sorry is still in
      `FormalSystem/Metalogic/WeakCanonical/Transfer.lean` and that no new one was introduced
- [ ] Re-run every metric from `baseline.txt` and produce the before/after table: criterion
      metric, broad metric, `truth_norm` count, `swap_norm` count, per-file line counts
- [ ] Score the completion criterion explicitly: criterion metric fell from 60 by ≥80% (to ≤12)?
      State the observed percentage. If a sub-goal was not met, say so plainly rather than
      re-framing the target
- [ ] Write `specs/193_codebase_tactic_refactor/summaries/01_truth-norm-application-sweep-summary.md`
      per `summary-format.md`, including the exclusions from Phase 5 and any plan deviation
- [ ] Commit

**Timing**: 1 hour

**Depends on**: 5

**Verification Tier**: full

**Files to modify**:
- `specs/193_codebase_tactic_refactor/summaries/01_truth-norm-application-sweep-summary.md` - new
- `specs/193_codebase_tactic_refactor/baseline.txt` - final measurements appended

**Verification**:
- Full gate set green: `lake build`, `check-module-invariants.sh`, C2 baseline, sorry inventory
- Before/after metric table present in the summary with observed numbers
- Completion criterion scored explicitly as met or not met

## Testing & Validation

- [ ] `lake build` green at the end of every phase that edits a `.lean` file, and at the end
- [ ] `bash scripts/check-module-invariants.sh` passes
- [ ] C2 axiom baseline for the flagship theorems unchanged (`[propext, Classical.choice, Quot.sound]`)
- [ ] Executable `sorry` count unchanged, verified by content and not by line number
- [ ] Criterion metric: combined `grep -c 'simp only \[TruthAt'` across the two files falls from
      the observed baseline (60 at plan time) by at least 80%
- [ ] All 13 `Formula.swap_temporal_*` simp lists in `FrameClassVariants.lean` collapsed to `swap_norm`
- [ ] No theorem or lemma statement changed anywhere: every diff hunk lies inside a `by` block
- [ ] No new tactic, macro, elaborator, simp attribute, or `@[truth_norm]` tag introduced

## Artifacts & Outputs

- `specs/193_codebase_tactic_refactor/plans/01_truth-norm-application-sweep.md` (this plan)
- `specs/193_codebase_tactic_refactor/baseline.txt` (measurement record, before and after)
- `specs/193_codebase_tactic_refactor/summaries/01_truth-norm-application-sweep-summary.md`
- Modified: `FormalSystem/Metalogic/Soundness.lean`,
  `FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean`

## Rollback/Contingency

Every phase commits only green states, and no phase edits both target files, so `git revert` of a
phase's commits restores a buildable tree without touching the other file. The pass changes no
statement, no attribute, and no simp-set membership — it only rewrites `by`-block tactic text — so
a revert is complete by construction and cannot leave a downstream module stranded against a
changed interface.

Contingency by failure mode:

- **A Class A site does not close under `truth_norm`**: revert that one site, reclassify it Class
  B, continue. The criterion has 93%-vs-80% margin and absorbs several such reclassifications.
- **A Class B site's body cannot be re-derived**: leave the original list untouched and record it
  in Phase 5's `#### Reasoned Exclusions`. Class B is not load-bearing for the criterion.
- **The criterion metric does not reach ≤12** (only possible if many Class A sites reclassify):
  do not widen the metric or re-target. Complete Phase 6's measurement honestly, mark the task
  `[PARTIAL]` with the observed percentage, and record which sites resisted and why — that list is
  itself the useful output, since it would identify a real gap in the `truth_norm` set.
