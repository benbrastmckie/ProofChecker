# Implementation Summary: Rename FrameClass tags to ZTime/RTime

- **Task**: 546 - Rename frameclass tags to ztime rtime
- **Status**: [COMPLETED]
- **Type**: lean4
- **Plan**: `specs/546_rename_frameclass_tags_to_ztime_rtime/plans/01_ztime-rtime-rename-plan.md`
- **Phases**: 9 of 9 [COMPLETED]
- **Commits**: `7e304b6e9`, `cfb5288a9`, `af845ac39`, `85cd34da0`, `79bd1794f`, `d055fce03`,
  `e30ea6bc6`, `fb608a8a9`

## What changed

`FrameClass.Discrete` and `FrameClass.Dedekind` are now `FrameClass.ZTime` and
`FrameClass.RTime`, and every identifier that names the *frame class* moved with them under one
recorded scheme (PascalCase `ZTime`/`RTime`, lowerCamel `zTime`/`rTime`, snake_case
`ztime`/`rtime`). The frame predicates `TaskFrame.IsSuccArchDiscrete` and `TaskFrame.IsDedekind`
became `TaskFrame.IsZTime` and `TaskFrame.IsRTime`. 152 files changed across `FormalSystem/`
(103), `typst/` (14), `docs/` (14), `specs/` (11), `scripts/` (5), `Tests/` (4) and `README.md`.

The *bare order conditions* were deliberately left alone: `TaskFrame.IsDiscrete`,
`TaskFrame.IsDense`, `TaskFrame.IsComplete`, `ValidComplete`, the five `Axiom.discrete_*`
uniformity constructors, the 560-occurrence Dedekind-INF/SUP API, the discrete-order construction
lemmas, and `layerReynoldsDedekind`. No semantics, proof term, or tactic script changed; the diff
is identifier spelling and prose only.

Execution was strictly leaf-first, so every phase ended on a green build. The one unavoidable
atomic pass — the constructors themselves, 493 `.Discrete` plus 369 `.Dedekind` occurrences over
81 live files — was isolated in Phase 5 as a declared `atomic-batch`.

## Phase-by-phase

| Phase | Scope | Outcome |
|---|---|---|
| 1 | Metalogic class-level statements; `check-module-invariants.sh` C14 baseline + probe pair | 37 `.lean` files; full invariants ALL CHECKS PASSED |
| 2 | BL, Star, Conservativity, tableau rule sets, sat-subset family | 25 files; C14 probe PASS |
| 3 | Validity predicates, decidability instances, `nolints.json` | 36 files; `runLinter` "Linting passed" |
| 4 | Frame predicates and their four satellite lemmas | 18 files + `boneyard-import-waivers.txt` |
| 5 | The constructors — atomic batch | 81 files + `typst-status-counts.sh` greps; full invariants green |
| 6 | String literals, round-trip parsers, Tests rows, generated artifacts | typst Checks 2 and 3 byte-for-byte green |
| 7 | Lean docstring rewrite | prose-only diff, 7 files |
| 8 | Typst prose, 14 docs files, ROADMAP, naming-convention record | `typst-sync-check.sh` PASS all three checks |
| 9 | Final gate | all five gates green |

## Verification

| Gate | Result |
|---|---|
| `lake build` | green, 2591 jobs |
| `lake build BimodalTest` | green, 2642 jobs |
| `scripts/check-module-invariants.sh` (full) | ALL CHECKS PASSED — C1, C2, C3, C11, C14, C15, C16 |
| `scripts/typst-sync-check.sh` | PASS, all three checks |
| `scripts/typst-status-counts.sh` | `ztime_only_count` 3, `rtime_only_count` 3 (a 0 would have meant the greps did not move) |
| Structural sorry inventory (C3) | ZERO across non-Boneyard `FormalSystem/`, unchanged |
| Axioms | 7 `^axiom ` declarations, unchanged from the pre-task tree |
| KEEP-list guard | clean: Dedekind-INF/SUP at 560, bare conditions at 43, axiom constructors at 45 |
| Boneyard | zero `FormalSystem/Boneyard/` paths in the task's 152-file set |
| CLI round-trip | `--frame-class ztime` and `--frame-class discrete` both accepted; both emit `frame_class: "ZTime"`; metadata byte-identical modulo timestamps |

`scripts/typst-sync-check.sh` was **failing before this task began**, with four Check 1
violations. Three were fixed forward in Phase 8 (`04-metalogic.typ` named two `SoundnessLemmas/`
files that do not exist; two bare Aesop attribute spans were whitelisted as exposition) and one,
`ValidDedekindDense`, was a stale name repointed to the real `ValidRTime`. The script is now
green for the first time in this history.

## Plan Deviations

- **Phase 1, altered.** C14 baseline lines 871/873 and probe lines 929/931 name
  `tmCompleteDiscrete_iff_forwardDiscrete` / `tmCompleteDedekind_iff_forwardDedekind`, which
  Phase 2 renames. Moving them in Phase 1 as the plan listed would have broken C14 in that phase,
  so they were deferred to Phase 2 and moved there in the same commit as the declarations.
- **Phase 1, added.** `not_derivable_nil_bot_discrete` -> `not_derivable_nil_bot_ztime`, a
  class-naming soundness-family lemma the plan did not enumerate.
- **Phase 2, altered.** `discreteRules`/`dedekindRules` -> `zTimeRules`/`rTimeRules` per the
  lowerCamel row of the scheme.
- **Phase 3, added.** Local hypothesis `h_valid_discrete` -> `h_valid_ztime`.
- **Phase 5 -> 6, altered.** `typst-status-counts.sh`'s `DISCRETE_ONLY_COUNT`/`DEDEKIND_ONLY_COUNT`
  variables and their JSON keys were renamed in Phase 6 rather than Phase 5, together with the
  `#discrete-only-count`/`#dedekind-only-count` consumers in `typst-sync-check.sh` and two typst
  chapters, so both halves moved in one commit and no `#import` was ever left dangling.
- **Phase 6, added.** `discreteExtraRows`/`dedekindExtraRows` renamed alongside
  `discreteRows`/`dedekindRows`; `resultDiscrete`/`discreteOk` locals and a
  `s!"Discrete={...}"` debug string in `Decidability/Saturation.lean`.
- **Phase 7, added.** `FormalSystem/Semantics.lean:70`, a mirror site the plan's list omitted.
- **Phase 8, added.** Three fix-forward repairs to pre-existing `typst-sync-check.sh` failures
  (see Verification above); `typst/SYNC-MAP.md` and `typst/README.md` rows; and a correction to
  `NAMING_CONVENTION_DEVIATION.md`'s pre-existing claim that `scripts/nolints.json` "was deleted
  from the tree" — the file exists and Phase 3 hand-edited two `docBlame` rows in it.

Phase 8's `#### KEEP-boundary decisions and out-of-scope residuals` table in the plan records
what the sweep deliberately did not cross: `typst/FormalFoundations.typ`'s paper-vocabulary prose,
the Reynolds Dedekind axiom-layer label, module and file names (deferred by the plan's decision 1),
and one pre-existing dead `#leansrc` reference to a `discrete_consequence_not_compact` that has
never existed.

## Deferred, and recorded

Module and file names keep their old spellings — `Metalogic/DedekindNonCompactness.lean`,
`DiscreteNonCompactness.lean`, `BXCanonical/CompletenessDedekind.lean`,
`Theorems/DedekindDerived.lean`, `Theorems/DiscreteUnfolding.lean`,
`BXCanonical/DiscreteCarrierProbe.lean`. Renaming them would churn import lines tree-wide and
invalidate `#leansrc` module citations for no semantic gain. The residual inconsistency is real —
a file named for the old tag can declare identifiers named for the new one, e.g.
`DedekindNonCompactness.lean` declares `notCompactRTime` — and is stated explicitly in
`docs/development/NAMING_CONVENTION_DEVIATION.md`'s "Deferred: module and file names" subsection
rather than left implicit.

## Concurrency note

Another agent was editing `FormalSystem/Metalogic/WeakCanonical/Expressiveness/SplitPoint.lean`
in the same working tree during Phase 7 (an unrelated stale-docstring fix, since landed as
`4758f2225`). It was excluded from this task's commits. All eight commits were audited: every
file in each carries ZTime/RTime rename content, so no cross-contamination occurred.
