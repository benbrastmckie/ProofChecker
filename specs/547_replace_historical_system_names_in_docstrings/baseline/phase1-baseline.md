# Phase 1 Baseline (task 547)

## Build

`bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- build FormalSystem` — exit 0 (green).

## check-module-invariants.sh

Full output saved at `check-module-invariants-baseline.txt`. Exit status 1.

- 1 CHECK GROUP FAILED: **C9** — 1 task-number citation under `FormalSystem/`
  (`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean:12543`).
  Pre-existing and unrelated to this task's file set.
- **C14** PASS (both rows). **C15** PASS: 53 paper-anchor citations resolve; 52 theorem-index rows.
- C19 refined docstring coverage 9624/10425 = 92.32% (floor 90%).

## Census (`grep -rcE 'TM⁺?_(f|c|dc)|BX_(f|c)'`, excluding Boneyard)

74 matching lines total across 19 files.

| File | Lines |
|------|-------|
| FormalSystem/Metalogic/Conservativity/Backward.lean | 11 |
| FormalSystem/Metalogic/Conservativity.lean | 8 |
| FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean | 7 |
| FormalSystem/BaseLanguage/Axioms.lean | 6 |
| FormalSystem/ProofSystem/Axioms.lean | 6 |
| FormalSystem/README.md | 6 |
| FormalSystem/Metalogic/Conservativity/Fragment.lean | 5 |
| FormalSystem/Semantics/FrameClassValidity.lean | 4 |
| docs/theorem-index.md | 4 |
| FormalSystem/BaseLanguage/Derivation.lean | 3 |
| FormalSystem/Semantics/FrameProperty.lean | 3 |
| FormalSystem/Semantics/Validity.lean | 2 |
| README.md | 2 |
| docs/user-guide/architecture.md | 2 |
| FormalSystem/BaseLanguage/AxiomDischarge.lean | 1 |
| FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean | 1 |
| FormalSystem/Theorems/DedekindDerived.lean | 1 |
| FormalSystem/Theorems/DiscreteUnfolding.lean | 1 |
| typst/SYNC-MAP.md | 1 |

`Tests/` and `scripts/` contain zero occurrences (confirms the plan, corrects the task description).

Deviation from the plan's per-file hypothesis: `FormalSystem/README.md`'s 6 lines are at
194, 195, 197, 199, 201, 361 (the plan guessed 174, 182, 194, 195, 201, 202). Same file, same
count, different line numbers; Phase 6 locates by text.

## Safety invariants

- `grep -rnE 'TM⁺?_(f|c|dc)[A-Za-z0-9_]' FormalSystem` — empty (no token is a prefix of a longer word).
- `grep -rnE 'TM⋆_(f|c|dc)' FormalSystem` — empty (`Star/` needs no exclusion).

## Anchor-label baseline (must be invariant at Phase 7)

| Anchor | Count under FormalSystem docs typst README.md |
|--------|-----------------------------------------------|
| `def:TMplus-f` | 18 |
| `def:TMplus-c` | 10 |
| `cor:tm-completeness` | 40 |

## Live-paper facts confirmed against possible_worlds.tex

- `def:BX-z` (L4251): BX = base; BX_z = BX + UZ + Z1. Its closing sentence: UZ and Z1 fail over
  every non-Archimedean discrete order (`prop:archimedean`), and the Archimedean discrete orders
  are exactly ℤ-time, so the discrete task frames over which BX_z and TM_z are sound and complete
  are exactly those over ℤ-time. The old "successor-Archimedean discrete class" sentence is gone.
- `def:BX-d` (L4264): BX + DN + NN.
- `def:BX-r` (L4272): BX_d + PU + SEP, with **CO a derived theorem** (from PU plus the BX axioms),
  explicitly not an axiom. The converse-derivation ℚ-flow sketch is commented out and is only
  conjectured, not asserted.
- `def:TMplus` (L4285): TM = S5 + BX + MF; TM_z, TM_d, TM_r add what distinguishes BX_z, BX_d, BX_r.
- `cor:tm-completeness` (L4294): TM strongly complete over all task frames; TM_d strongly complete
  over the dense frames; TM_z weakly complete over ℤ-time; TM_r weakly complete over ℝ-time.
- **The Past/Future footnote named in the task description does not exist in the live paper.**
  `possible_worlds.tex:1331-1341` is commented out in full, with the editorial note that the
  footnote stays commented "until the BimodalLogic repository establishes that the Past/Future
  language admits no complete axiomatization". The paper therefore names no Past/Future system at
  all — so the mapping prose says the repository's `TM` side has *no* paper counterpart, rather
  than identifying it with a footnote that is not live.
