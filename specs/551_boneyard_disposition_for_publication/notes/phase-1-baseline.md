# Phase 1 Baseline (frozen before-state)

Captured at gate commit `f07c752fe`, before any edit from this task landed.

## Gate: `bash scripts/check-module-invariants.sh` (full, with build)

Result: **1 CHECK GROUP FAILED** — and the failing group is **not** attributable to this task.

```
FAIL  C12  1 unresolved slash-shaped source path(s) in docs/ + README.md
            docs/reference/API_REFERENCE.md:190: FormalSystem/Semantics/WorldHistory.lean
```

`FormalSystem/Semantics/WorldHistory.lean` is being renamed to `ConvexHistory.lean` by an
unrelated, concurrently-in-flight working-tree change (77 modified live `.lean` files plus one
`RM`-staged rename, none of them under `FormalSystem/Boneyard/`). This task touches none of
those files. The pre-existing C12 failure is therefore the baseline, and Phase 10 re-verifies
against *this* state, not against an idealized all-green one.

Every other check passed:

```
PASS  B0   Boneyard exclusion covers exactly 1 directory
            FormalSystem/Boneyard
            excluded 168 archived .lean files (646 total -> 478 live)
PASS  C1   lake build exits 0
PASS  C1   lake build BimodalTest exits 0
PASS  C2   all four flagship axiom sets match baseline
PASS  C3   structural sorry inventory is ZERO across FormalSystem/ (Boneyard/ excluded)
PASS  C4   all 1603 FormalSystem/BimodalTest import lines resolve
PASS  C5   all module-shaped paths in 1351 markdown files resolve (4 allowlisted)
PASS  C6   all 16 unreachable live module(s) are manifested; all 14 manifested still compile
INFO  C7   533 live .lean files (478 FormalSystem / 54 Tests); Metalogic 348
PASS  C8   every FormalSystem/ and Metalogic/ subdirectory has exactly one sibling aggregator
PASS  C9   zero task-number citations under FormalSystem/, lakefile.lean, README.md, scripts/
PASS  C10  zero references to FormalSystem/{docs,latex,typst} outside specs/
PASS  C11  all 536 archived import lines in 168 archived file(s) resolve (7 waived)
PASS  C13  all relative markdown links in 74 markdown files resolve (3 allowlisted)
PASS  C14  no stale axiom or sorry counts documented; every pinned decl matches baseline
PASS  C15  paper anchors resolve
PASS  C18  zero duplicated paragraphs / sentences across the four top-level READMEs
PASS  C19  docstring coverage (refined): 9617/10416 = 92.33% (floor 90%)
PASS  C21  all 27 declarations named in MainResults.lean are pinned
PASS  C22  the two allAxiomNames lists agree (45 names each)
PASS  INV  every generated inventory block is current, every hand-maintained one is exhaustive
TODO  C9D  142 task-number citation(s) under docs/ (not yet enforced)
```

## `.olean` census

| Quantity | Value |
|----------|------:|
| `find .lake/build -name '*.olean'` | 546 |
| `find .lake -path '*Boneyard*' -name '*.olean'` | **0** |

## Live sorry census

C3: **0** structural sorries across `FormalSystem/` with `Boneyard/` excluded.

## Archive census (measured, not documented)

| Quantity | Measured | Documented before this task |
|----------|---------:|----------------------------:|
| Archived `.lean` files | 168 | 163 (`Boneyard/README.md`), 156 (`FormalSystem/README.md:312`), 93 (inventory total row) |
| Archived lines | 91,539 | 90,797 / 58,738 |
| Top-level subdirectories | 39 | 37 |
| Top-level entries in `ls FormalSystem/Boneyard` | 41 (39 dirs + `README.md` + `VacuousKEquiv.lean`) | -- |
| README-only tombstone subtrees | 9 | 9 |
| Subtrees lacking a `README.md` | 6 | -- |
| Archived `.lean` files lacking `#exit` | 12 | -- |
| `.md` files under the archive | 49 | -- |
| `BEGIN GENERATED` / `INVENTORY: hand-maintained` markers under the archive | 0 | -- |

## Citation census (why CUT ENTIRELY is unavailable)

| Quantity | Measured |
|----------|---------:|
| Files outside the archive naming it (excluding `.git`, `.lake`, `specs`, `.claude`) | 96 |
| Live `.lean` files whose docstrings name it | 45 |
| Published LaTeX citations | `latex/subfiles/04-Metalogic.tex:383,389` |
| Entries in `scripts/boneyard-import-waivers.txt` | 49 |

## Concurrency note (recorded during Phase 1, re-checked every phase)

The unrelated `WorldHistory` -> `ConvexHistory` rename landed further while this task was in
Phase 1. Immediately after Phase 1's markdown-only edits, `--no-build` reported three failing
groups, **every one of them naming `WorldHistory`**:

```
FAIL  C5   docs/development/MODULE_ORGANIZATION.md:314: FormalSystem.Semantics.WorldHistory
           docs/reference/API_REFERENCE.md:188:        FormalSystem.Semantics.WorldHistory
           docs/theorem-index.md:34:                    FormalSystem.Semantics.WorldHistory
FAIL  C11  FormalSystem/Boneyard/ChainCompleteness/Bundle/SuccChainWorldHistory.lean:3:
             import FormalSystem.Semantics.WorldHistory -> missing, not waived
FAIL  C12  docs/reference/API_REFERENCE.md:190: FormalSystem/Semantics/WorldHistory.lean
```

None of those files is touched by this task, and none of those failures existed before the
concurrent rename progressed. **The verification rule for every subsequent phase is therefore:
a check is green for this task's purposes when its only remaining findings name `WorldHistory`.**
Phase 10 re-states the residual set explicitly rather than claiming an all-green gate this task
cannot deliver on a tree it does not solely own.
