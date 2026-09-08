# Research Report: Task #547

**Task**: 547 - Replace historical system names in docstrings
**Started**: 2026-09-07T17:13:00Z
**Completed**: 2026-09-07T17:40:00Z
**Effort**: Medium (comment/docstring sweep + ~12 editorial rewrites, no Lean identifier changes)
**Dependencies**: 546 (completed). Blocks 548 (anchor re-pinning).
**Sources/Inputs**: - Codebase grep survey, live paper `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`, `scripts/check-module-invariants.sh` (C14/C15 contracts), `specs/state.json`
**Artifacts**: - `specs/547_replace_historical_system_names_in_docstrings/reports/01_historical-system-name-sweep.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **This is not a pure token swap.** 12 passages carry *claims about the paper* that the z/d/r
  refactor makes false, not merely renames them. The largest are the "TM⁺_c gap" argument
  (`ProofSystem/Axioms.lean:513-522`, duplicated in three more files) and the "the paper bases
  BX_c on the single axiom CO" note (`ProofSystem/Axioms.lean:394-430`). Both are now **obsolete
  in the repository's favour**: the live paper's `def:BX-r` is `BX_d + PU + SEP` with **CO
  derived**, exactly this tree's Reynolds-triple basis, and the paper's `TM_r` is completeness
  over the dense-and-complete class, exactly `FrameClass.RTime`. There is no residual gap and no
  outstanding paper amendment.
- **The dispatch's account of the Past/Future footnote does not match the live paper.** The
  footnote described in the task ("S5 schemata, MF, TK, T4, TB, TA, TL, TD with P and F
  interchanged...") does not exist. `possible_worlds.tex:1331-1341` shows the Past/Future
  footnote **entirely commented out**, pending the non-axiomatizability result that a separate
  open task owns. The mapping paragraph must therefore say the repository's `TM`/`TM_z`/`TM_d`/
  `TM_r` have **no paper name at all** — not that they are "the footnote's Past/Future system".
- **`TM⁺_c` and `TM⁺_dc` both map to `TM⁺_r`**, collapsing a distinction the tree currently
  argues at length in four places. Those paragraphs must be *deleted or rewritten*, never
  sed-replaced (a naive swap yields "this is TM⁺_r, not TM⁺_r").
- **Scope boundary with task 548 is hard**: 547 changes *prose names only*; 548 owns every
  `def:TMplus-f`/`def:TMplus-c` → `def:BX-z`/`def:BX-r` **anchor label** and every entry in
  `specs/paper-definitions-of-record.md`. C15 resolves anchors against the record, so renaming a
  label in 547 turns C15 red until 548 lands. Recommendation: 547 must not touch anchor labels
  or the record.
- **Measured state differs from the dispatch's figures**: `scripts/` has **zero** occurrences
  (dispatch says some); the non-Lean live-scope total is 14 lines (docs/ 6, root README.md 2,
  FormalSystem/README.md 7 — of which 1 overlaps, typst/SYNC-MAP.md 1), plus 4 lines in the
  definitions-of-record that belong to 548.
- **Recommended approach**: two-stage — a scripted literal rename over Class-A sites, then 12
  hand-written passage rewrites (Class B), then two additions (Class C), then a scoped grep gate
  and `lake build FormalSystem`. No sorry, no axiom, no identifier change is involved anywhere.

## Context & Scope

Researched: the complete occurrence set of the historical system names `TM⁺_f`, `TM⁺_c`,
`TM⁺_dc`, `TM_f`, `TM_c`, `TM_dc`, `BX_f`, `BX_c` across live scope; the live paper's current
naming and axiom bases; which passages contain *arguments* that the rename invalidates; and the
interaction with `scripts/check-module-invariants.sh` C14/C15 and with tasks 546/548.

Constraints honoured: comment-and-docstring-only; no identifier changes; `TM⁺` superscript
retained; bare `TM` not renamed; `TM⋆` (`Metalogic/Conservativity/Star/`) untouched.

## Findings

### Codebase Patterns

**Verified occurrence census** (live scope; `Boneyard/`, `specs/archive/`, `.claude/` excluded):

| Pattern | Lean lines | Lean files | Non-Lean live-scope lines |
|---------|-----------|-----------|---------------------------|
| `TM⁺_f`  | 13 | 6 | 3 (`docs/theorem-index.md` 2, `FormalSystem/README.md` 1) |
| `TM⁺_c`  | 11 | 4 | 9 (`FormalSystem/README.md` 5, `docs/user-guide/architecture.md` 2, `docs/theorem-index.md` 2 — plus root `README.md` 1) |
| `TM⁺_dc` | 3  | 2 | 0 |
| `TM_f`   | 25 | 7 | 0 |
| `TM_c`   | 7  | 3 | 1 (`typst/SYNC-MAP.md`) |
| `TM_dc`  | 8  | 3 | 0 |
| `BX_f`   | 2  | 2 | 0 |
| `BX_c`   | 3  | 2 | 2 (`FormalSystem/README.md` 1, root `README.md` 1) |

Additional verified facts:

- **`scripts/` contains zero occurrences.** `grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)|TMplus-(f|c)' scripts/`
  returns nothing. The dispatch's "docs/, scripts/ and the definitions-of-record" over-counts.
- **`Tests/` contains zero occurrences.**
- **No occurrence is a Lean identifier.** All are inside `/-! -/`, `/-- -/`, or `--` comments.
- **Sed-safety verified**: `grep -rnE 'TM⁺?_(f|c|dc)[A-Za-z0-9_]'` over live scope is empty, so
  no token is a prefix of a longer word; literal replacement cannot corrupt an adjacent symbol.
  `TM_dc` does not contain `TM_c` as a substring, so ordering between those two rules is
  irrelevant; `TM⁺_d` and `TM_d` are unchanged by the task and so create no ordering hazard.
- **`TM⋆` is clean**: `grep -rnE 'TM⋆_(f|c|dc)'` over `FormalSystem/` is empty. `Star/` needs no
  exclusion logic beyond not matching.

**Pre-existing inconsistency the rename resolves.** The tree currently contradicts itself:
`FormalSystem/README.md:194` and root `README.md:197` assert "`FrameClass.RTime` *is* the paper's
TM⁺_c … There is no gap", while `ProofSystem/Axioms.lean:513` asserts "The paper's TM⁺_c has no
frame class here, and that is a real gap rather than an omission." Under the new convention both
statements are superseded by a single true one: `FrameClass.RTime` is the paper's `TM⁺_r`.

**Task-546 residue (adjacent, partly co-located).** Six markdown files still name the retired
`FrameClass.Dedekind` / `FrameClass.Discrete` tags: `FormalSystem/README.md` (5, at lines
174/182/194/195/202 — overlapping the paragraphs 547 rewrites), `FormalSystem/ProofSystem/README.md:49`,
`FormalSystem/Theorems/README.md:17`, `FormalSystem/Semantics/Correspondence/README.md:20`,
`FormalSystem/Metalogic/Decidability/BiLasso/README.md:161`,
`docs/development/NAMING_CONVENTION_DEVIATION.md:232`. The `FormalSystem/README.md` ones sit
inside text 547 must rewrite anyway.

### External Resources

**Live paper, verified by direct read** (`possible_worlds.tex`, read 2026-09-07):

| Anchor | Line | Content |
|--------|------|---------|
| `def:BX` | 4260 | Base Burgess–Xu logic **BX** |
| `def:BX-z` | 4269 | **BX_z** = BX + UZ + Z1. Closing sentence: *"Since UZ and Z1 fail over every discrete temporal order that is not Archimedean (`prop:archimedean`), and the Archimedean discrete orders are exactly ℤ-time (§`sub:Extension`), the discrete task frames over which **BX**_z and **TM**_z are sound and complete are exactly those over ℤ-time."* |
| `def:BX-d` | 4282 | **BX_d** = BX + DN + NN |
| `def:BX-r` | 4290 | **BX_r** = **BX_d** + **PU** + **SEP**. CO is a *derived theorem* of BX_r using only PU and the BX axioms, and is **not** an axiom of BX_r |
| `def:TMplus` | 4303 | **TM** = S5 + BX + MF; **TM_z**, **TM_d**, **TM_r** add the axioms distinguishing BX_z, BX_d, BX_r |
| `cor:tm-completeness` | 4312 | TM strongly complete over all task frames; **TM_d strongly** over the dense task frames; **TM_z weakly** over ℤ-time; **TM_r weakly** over ℝ-time |

Three consequences that are *not* renames:

1. **The paper's axiom label is `SEP`, not `SP`.** The dispatch writes "PU and SP"; the paper's
   `\aref` is `SEP`, matching this tree's `Axiom.sep`. Use `SEP` in new prose.
2. **`BX_r` extends `BX_d`, so it carries the density axioms.** The open question recorded at
   root `README.md:199` and `FormalSystem/README.md:201` — "either the paper's BX_c should carry
   the density axioms, or this tree should record that `completeness_rtime` proves a
   stronger-premise statement" — is **answered by the paper**: `BX_r` is built on the dense logic.
   That paragraph should be retired, not renamed.
3. **The paper's "consequence for the repository" note is discharged.**
   `ProofSystem/Axioms.lean:426-430` says correcting the paper "means switching the paper's BX_c
   basis to the Reynolds axioms, … routed through the fix.md C4 process." The paper has done
   exactly that. The note becomes a *resolved* record, not an outstanding item.

**Live paper — Past/Future footnote (critical discrepancy).** `possible_worlds.tex:1331-1341`:
the sentence "Although the perpetuity principles are stated in terms of P and F alone, TM owes
its strength to S and U" **and its entire footnote are commented out**, with an explicit
in-source note: *"footnote commented out until the BimodalLogic repository establishes that the
Past/Future language admits no complete axiomatization; the repository currently shows only that
one particular system in that language is incomplete over ℤ-time."* Greps for `aref{TK}` and for
"interchang" confirm no live axiom-set enumeration for a Past/Future system exists anywhere in
the paper. **The paper names no Past/Future system, in text or footnote.**

**Live paper — commented author line relocated.** `FormalSystem/Metalogic/Conservativity.lean:143`
cites "a commented (non-live) line, `possible_worlds.tex:4614`". That line is now at **4274**,
inside `def:BX-z`, and now reads `TM_z` throughout. The line number and the quoted text are both
stale.

**Live paper — quoted Hölder sentence deleted.** `Semantics/FrameClassValidity.lean:95-96`,
`Semantics/FrameProperty.lean:43-44`, and `Metalogic/Conservativity.lean:137-142` all quote, as
*verbatim live text*, `def:TMplus-f`'s closing sentence "the successor-Archimedean discrete class
to which BX_f and TM⁺_f are sound and complete is exactly ℤ-time". The paper records
`% NEW CHANGE [Hölder consolidation]: the Hölder clause is cut from this definition`. That
sentence **no longer exists**; the replacement (quoted in the table above) drops
"successor-Archimedean" and cites `prop:archimedean`. A verbatim quotation cannot be repaired by
renaming its tokens.

**Live paper — independence conjecture superseded by this repository.** `def:BX-r`'s commented
block conjectures that CO alone does not axiomatize BX_r "via an unformalized pen-and-paper
sketch involving a ℚ-flow with isolated ¬φ points accumulating at an irrational from above; this
independence is not asserted as established." `ProofSystem/Axioms.lean:414-421` records that this
*exact* sketch **was refuted** here, and that the independence is nonetheless **machine-checked**
by a different witness (`Metalogic.Independence.CoNotPriorU`, the periodic-clock model). The
rewritten note should say so: the repository establishes what the paper conjectures, and refutes
the paper's route to it.

**Verification-gate contracts** (`scripts/check-module-invariants.sh`):

- **C15** collects `(def|thm|lem|cor|app|rmk):NAME` citations from `FormalSystem/ Tests/ typst/
  docs/ README.md` (Boneyard excluded) and resolves them **against
  `specs/paper-definitions-of-record.md`**, not against the paper. Renaming `def:TMplus-f` →
  `def:BX-z` in a docstring **fails C15** until the record carries a row for the new anchor. That
  work is task 548's by its own description. **547 must leave every anchor label untouched.**
- **C14** scans `docs/`, `README.md` and `FormalSystem/*.lean` for stale axiom/sorry counts and
  compares `#print axioms` output to a pinned baseline. A comment-only sweep does not perturb it,
  provided no documented count is edited.

### Recommendations

**A sorry-free path exists and is the only path**: this task adds no Lean term, tactic, axiom or
`sorry`. The zero-debt gate is satisfied trivially; the risk is *documentation falsehood*, not
proof debt.

**Recommended decomposition (phase-shaped, for the planner):**

1. **Baseline.** `lake build FormalSystem` green + `bash scripts/check-module-invariants.sh`
   recorded, before any edit. Long build: run detached per
   `context/project/lean4/operations/long-builds.md`.
2. **Class A — mechanical literal rename** (`TM⁺_f`→`TM⁺_z`, `TM_f`→`TM_z`, `BX_f`→`BX_z`,
   `TM_dc`→`TM_r`, `BX_c`→`BX_r`) over files whose occurrences are pure labels:
   `Metalogic/Conservativity/Z1Countermodel.lean`, `.../Fragment.lean`,
   `.../TMCompletenessReduction.lean`, `BaseLanguage/Derivation.lean`, `docs/theorem-index.md`.
   Safe because no token is a prefix of a longer word (verified above).
3. **Class B — editorial rewrites** (12 passages; enumerated in Risks below). Each removes a
   claim that the paper has retracted or resolved. These are hand-written, one file at a time.
4. **Class C — additions**: the mapping paragraph into
   `FormalSystem/Metalogic/Conservativity.lean`'s module docstring and into `docs/README.md`;
   the one-time "these have no paper name" sentence (best placed in
   `BaseLanguage/Axioms.lean`'s system table, where `TM_z/TM_d/TM_r` are first tabulated, with
   the Conservativity paragraph cross-referencing it).
5. **Gate.** Scoped grep + `lake build FormalSystem` + `check-module-invariants.sh` diff against
   the Phase-1 baseline.

**The mapping paragraph, corrected against the live paper.** Recommended substance (wording for
the implementer to polish):

> **Two base systems, and how they map to the paper.** This repository names two proof systems.
> `TM⁺` (`ProofSystem/`), over the full language `BL` with `S`/`U` primitive, **is the paper's
> `TM`** (`def:TMplus`); its extensions `TM⁺_z`, `TM⁺_d`, `TM⁺_r` are the paper's `TM_z`, `TM_d`,
> `TM_r`, named for the class each is complete over (ℤ-time, the dense task frames, ℝ-time), and
> built on the Burgess–Xu cores `BX_z`, `BX_d`, `BX_r` (`def:BX-z`, `def:BX-d`, `def:BX-r`).
> `TM` (`BaseLanguage/`), over the Past/Future fragment with `H`/`G` primitive, and its
> extensions `TM_z`, `TM_d`, `TM_r` (adding `DF`, `DN`, and `DN`+`CO`), **have no paper name**:
> the paper names no Past/Future system, and the footnote that would introduce one is commented
> out pending the non-axiomatizability question. The `z`/`d`/`r` subscripts on the `BaseLanguage`
> side are Lean-only, chosen to run parallel to the `TM⁺` side and to the `FrameClass` tags
> `.ZTime`, `.Dense`, `.RTime`. Do not read `TM_z` as a paper system.

**Per-passage rewrite targets (Class B).** For each, the false claim and its replacement:

| # | Site | Claim now false | Replacement |
|---|------|-----------------|-------------|
| B1 | `ProofSystem/Axioms.lean:394-397` | "`def:TMplus-c` bases BX_c on a single extra axiom CO … rather than on this triple" | `def:BX-r` bases `BX_r` on `BX_d + PU + SEP`; CO is a derived theorem there too. Repo and paper now agree. |
| B2 | `ProofSystem/Axioms.lean:426-430` | "Correcting it means switching the paper's BX_c basis to the Reynolds axioms … amendment routed through fix.md C4" | The amendment has landed; record as resolved. Add that the machine-checked independence (`CoNotPriorU`) establishes what `def:BX-r`'s commented block only conjectures, and that the paper's ℚ-flow sketch is the one refuted here. |
| B3 | `ProofSystem/Axioms.lean:493` | "`FrameClass.RTime` is therefore the paper's **TM⁺_dc** …, not TM⁺_c" | `FrameClass.RTime` is the paper's `TM⁺_r` (`cor:tm-completeness`, ℝ-time row). Delete the contrast. |
| B4 | `ProofSystem/Axioms.lean:513-522` | "The paper's TM⁺_c has no frame class here, and that is a real gap" | No paper system is completeness-simpliciter. `ValidComplete` survives as a **repository-only** predicate (the forgetful-bridge target and the Hölder-dichotomy statement), explicitly *not* the binder set of any paper system. |
| B5 | `Metalogic/Conservativity/Backward.lean:144-155` | CEC "fidelity caveat — this row is TM_dc, not the paper's TM_c" | The caveat evaporates: the row is `TM_r ⟶ TM⁺_r` at `.RTime`, and `TM⁺_r` *is* the paper's `TM_r`. Keep only the still-true content (`.RTime` sits above `.Dense`; CO's translation via `coDerived`). |
| B6 | `BaseLanguage/Axioms.lean:25,121,209` | CO row annotated `TM_c (see the caveat below)` + "at the paper's TM_dc, not at TM_c" | CO row is `TM_r`; delete the caveat, or replace with the one-time "no paper name" sentence. |
| B7 | `BaseLanguage/AxiomDischarge.lean:327` | "**TM_dc**, not TM_c" | Same as B5/B6. |
| B8 | `Semantics/Validity.lean:686-689` | "It is **not** the paper's TM⁺_c: … TM⁺_c is weak completeness over the dense-and-complete class" | "`ValidComplete` is the class of no paper system; `cor:tm-completeness`'s ℝ-time row is `TM_r` (this tree's `TM⁺_r`), whose class is `FrameClass.RTime` / `ValidRTime`." |
| B9 | `Semantics/FrameProperty.lean:32,43-44,192-193` | "`cor:tm-completeness`'s TM⁺_c target" ×2 + the deleted Hölder quotation | `TM⁺_r` target; **de-quote** the Hölder sentence (paraphrase in the tree's own voice) or requote `def:BX-z`'s live closing sentence. |
| B10 | `Semantics/FrameClassValidity.lean:35,42,95-96,102` | Per-constructor anchors: the `TM⁺_c` clause ×2 and the verbatim `def:TMplus-f` quotation | Rewrite anchors in `z`/`r` vocabulary; **de-quote** the ℤ-time sentence. Keep the anchor labels `def:TMplus-f` / `cor:tm-completeness` verbatim (548 renames labels). |
| B11 | `Metalogic/Conservativity.lean:135-152` | "Two live-paper facts": quotes deleted text and cites `possible_worlds.tex:4614` | The Hölder clause was cut from the definition. Restate from the live `def:BX-z` sentence; either update the commented-line citation to line 4274 with its new `TM_z` wording, or drop the line-number citation (it drifts on every paper edit). |
| B12 | `Theorems/DedekindDerived.lean:335` and `Theorems/DiscreteUnfolding.lean:356` | "CO is the extra axiom of the paper's complete-order extension BX_c"; "DF is the axiom distinguishing the paper's TM_f from TM" | CO is *derived* in `BX_r`, not an axiom of it. DF distinguishes this tree's (unnamed-in-paper) `TM_z` from `TM` — drop "the paper's". |

**The verification grep must be scoped.** "No `f`, `c` or `dc` subscript remains outside
`Boneyard/` and the archive" cannot be run repo-wide: `specs/TODO.md` and `specs/state.json`
contain task 547's and 548's own descriptions, which quote every old name by construction, and
`specs/{544,545,530}/**` and `specs/reviews/**` are historical artifacts. Recommended gate:

```bash
grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)' \
  --include='*.lean' --include='*.md' --include='*.typ' --include='*.sh' \
  --exclude-dir=Boneyard \
  FormalSystem Tests typst docs scripts README.md
# expect: no output
```

This is exactly C15's live scope plus `scripts/`, which is the right boundary.

## Decisions

- **547 does not touch `specs/paper-definitions-of-record.md`.** Its 4 occurrences (lines 1013,
  1052 anchor headings; 1228 a historical CHANGE note) are pinned entries with content hashes,
  owned by task 548 (`state.json`: 548 `not_started`, `dependencies: [547]`). Editing a record
  entry without re-hashing breaks the record's own extension procedure.
- **547 does not rename anchor labels.** `def:TMplus-f`/`def:TMplus-c` stay as written; C15
  resolves them today and would fail on `def:BX-z`/`def:BX-r` until 548 pins those rows.
- **Verbatim paper quotations are de-quoted rather than token-swapped.** Three sites quote a
  sentence the paper has deleted. Renaming inside quotation marks would manufacture a quotation
  the paper never contained.
- **The mapping paragraph asserts "no paper name", not "the footnote's Past/Future system".**
  Verified: that footnote is commented out in the live paper.
- **`typst/SYNC-MAP.md:472` is in scope** (`TM_c` → `TM_r`); `typst/` is inside C15's live scope
  and the grep gate above.
- **Task-546 residue inside rewritten paragraphs is fixed opportunistically.**
  `FormalSystem/README.md:194,195,202` (`FrameClass.Dedekind`) are inside text 547 rewrites; the
  other five stale-tag sites are out of scope and should be reported as a follow-up, not silently
  swept.

## Risks & Mitigations

| Risk | Mitigation |
|------|-----------|
| Naive `sed` produces "this is TM⁺_r, not TM⁺_r" in the four collapsed-distinction passages | Class A/Class B split: run the script only over the five Class-A files; hand-edit the 12 Class-B passages first or exclude them from the script |
| Renaming an anchor label turns C15 red | Explicit non-goal; gate on `check-module-invariants.sh` C15 before and after |
| Writing the dispatch's mapping paragraph verbatim asserts a footnote that does not exist | Use the corrected paragraph above; cite `possible_worlds.tex:1331-1341` as the evidence that the footnote is commented out |
| `docs/README.md` structural lints (`scripts/readme-lint.sh`, markdown link allowlists) reject a new section | Run `bash scripts/readme-lint.sh` after the addition |
| Line-number citations to the paper (`possible_worlds.tex:4614`) drift again | Prefer anchor-name citations over line numbers in the rewritten text |
| Scope creep into 548's record work | The grep gate above excludes `specs/`; keep it that way |
| Overlap with 548 on `FrameClassValidity.lean`'s quotation (548's description also claims it) | 547 de-quotes and renames the *system names*; 548 renames the *anchor label*. Record the split in the handoff so 548 does not re-litigate |

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task changes no proof term; no goal state is
  involved, so `lean_multi_attempt`, `lean_state_search` and `lean_hammer_premise` have no
  subject. Verification is `lake build FormalSystem` plus `scripts/check-module-invariants.sh`.

## Context Extension Recommendations

- **Topic**: Paper-name-drift sweeps (repository prose that quotes or characterizes an
  external paper).
- **Gap**: No context file records the recurring failure mode found here — a rename wave whose
  real cost is *retracted arguments*, not tokens: verbatim quotations of deleted text, "gap"
  paragraphs that a paper revision closes, and line-number citations into a paper this repo
  cannot see from CI.
- **Recommendation**: add
  `context/project/lean4/patterns/paper-name-drift-sweep.md` recording the three-class
  triage (mechanical / editorial / additive), the de-quotation rule, the "cite anchors not line
  numbers" rule, and the C15-record-vs-paper resolution boundary.

## Appendix

**Search queries used** (all local; no Mathlib search tool was needed — the task involves no
lemma discovery):

```bash
grep -rnE 'TM⁺?_(f|c|dc)|BX_(f|c)' --include=*.lean FormalSystem/    # census
grep -rnE 'TM⁺?_(f|c|dc)[A-Za-z0-9_]' ...                            # sed-safety (empty)
grep -rnE 'TM⋆_(f|c|dc)' --include=*.lean FormalSystem/              # Star/ safety (empty)
grep -rn 'FrameClass.Dedekind\|FrameClass.Discrete' ...              # task-546 residue
grep -n 'BX_z\|BX_d\|BX_r\|TM_z\|TM_d\|TM_r\|def:BX-\|def:TMplus' possible_worlds.tex
grep -n 'Past/Future\|not_bl_derivable_z1\|BimodalLogic' possible_worlds.tex
grep -n 'aref{TK}' possible_worlds.tex ; grep -n 'interchang' possible_worlds.tex
sed -n '1460,1530p' scripts/check-module-invariants.sh               # C15 contract
```

**References**

- `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` — lines 1264, 1331-1341,
  1401, 1406, 4260-4325
- `scripts/check-module-invariants.sh` — C14 (lines 1128-1456), C15 (lines 1460-1530)
- `specs/state.json` — task 546 `completed`; 547 `researching`; 548 `not_started`, deps `[547]`
- `.claude/context/project/lean4/operations/long-builds.md` — detached build protocol
