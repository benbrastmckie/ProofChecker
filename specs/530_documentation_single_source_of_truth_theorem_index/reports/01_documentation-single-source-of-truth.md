# Research: Documentation Single Source of Truth and Theorem Index

**Task type**: lean4 · **Dispatch**: 4 · **Research date**: 2026-09-04
**Repository HEAD at measurement**: `f6ce84139` (`task 529: complete implementation`)
**Source review**: `specs/reviews/2026-09-01-lean-engineering/` at HEAD `257cad9b8` (2026-09-01)

---

## 1. Headline

Every measured-state claim in the delegation was re-derived against the tree. **Nine of the
sixteen claims are wrong**, and in a consistent direction: the review measured a tree that has
since moved (three tasks landed in between, adding `Metalogic/Conservativity/`,
`FormalSystem/StarLanguage/`, and `Semantics/Star*.lean`), and the review's own grep-derived
counts were low. The recurring scope-hypothesis pattern the delegation warned about repeats
here, most dramatically on item (4): the delegation's **16** `file.lean:NNN` citations are
actually **1,354** in live non-Boneyard scope, of which **110 are provably wrong**.

Three claims are already fixed and should be dropped from scope (E-01, E-02, E-07). Two are
worse than claimed. Four new defects were found that no review names.

The policy work (items 1, 2, 6, 7) is sound and unblocked. The mechanical work (items 4, 5)
needs re-scoping before it can be planned, and §6 proposes the scoping rule.

---

## 2. Measured-state verification

Every row re-derived at HEAD `f6ce84139`. Commands are reproducible; each is a one-liner over
the tree with `Boneyard/` excluded by name glob (the invariant script's convention).

| # | Delegation claim | Verified state | Verdict |
|---|---|---|---|
| 1 | `Metalogic.lean` asserts SORRY-FREE for **37** declarations, C2+C14 pin **8**, so **33** prose-only | **48** declaration-like names carry a SORRY-FREE claim; C2+C14 pin **54** declarations total, of which **13** intersect the claimed set; **35 are prose-only** | **BOTH HALVES STALE** — the gap grew, not shrank |
| 2 | Four-row status ledger in six drifting copies | Confirmed. `Metalogic.lean:46` still says "the two countermodels remain outstanding"; `Conservativity.lean:64,85,192` says CEF is "refuted with both halves machine-checked" | **CONFIRMED** |
| 3 | `Metalogic.lean:110-113` is a dangling edit fragment | Moved to **`:131-132`**: "…obtained by instantiating the reductions / the single `FrameClass`-generic reduction `strongCompleteness_of_compact` with…" | **CONFIRMED** (relocated) |
| 4 | ~40 numeric claims stale across four documents | **40 of 72** per-file line-count claims wrong, across **7** READMEs (not 4). Plus every aggregate rollup | **CONFIRMED, wider** |
| 5 | `Decidability` 19 vs 62; `WeakCanonical` 135 vs 179 | `Metalogic.lean:265,271` still says 19 and 135. Actual: **62** and **179** | **CONFIRMED** |
| 6 | "Ten loose files" above an eleven-row table | `Metalogic/README.md:158` still says "**Ten**" above an 11-row table. Actual = **6** (15 loose − 9 aggregators). Worse: 4 of the 11 rows name files that have **moved** into `Metalogic/Conservativity/` (`BaseLanguageSoundness`, `TMCompletenessReduction`, `SpWitness`, `Z1Countermodel`) and a 5th (`Conservativity.lean`) is now an aggregator | **CONFIRMED as wrong; correction is 6, and 5 rows are phantom** |
| 7 | "two Boneyards" vs the one B0 asserts | `Metalogic.lean:256` still says "exclude BOTH Boneyards (there are two)"; `:269` still says `Kamp/` "has its OWN local `Boneyard/`". B0 passes asserting exactly 1 | **CONFIRMED** |
| 8 | Four paragraphs duplicated verbatim README.md ↔ Metalogic.lean | **Two** survive (`README.md:270`≈`Metalogic.lean:153`; `README.md:283`≈`Metalogic.lean:164`). C18 reports **zero** — see §3.1, C18 structurally cannot see them | **PARTLY STALE + GATE GAP** |
| 9 | 45 lines of refactor archaeology; StrongCompleteness 69% prose, Conservativity 80% | Comment-block share now: StrongCompleteness **75.8%**, SetConsequence **72.7%**, Conservativity **95.9%**, Validity **71.3%**, FrameClassValidity **83.2%**, `Metalogic.lean` **94.8%**. Archaeology-phrase hits: StrongCompleteness 15, SetConsequence 12, Conservativity **1** | **PROSE SHARE HIGHER; archaeology in Conservativity is already cleared** |
| 10 | 19 change-log phrasings on live README surfaces | **46** hits on the same surfaces with a slightly widened pattern (adds `formerly`, `earlier revisions`) | **UNDERCOUNT ×2.4** |
| 11 | 6 of 16 `file.lean:NNN` citations in five metalogic files point at the wrong line | **1,354** citations in live `FormalSystem/ docs/ Tests/ typst/ scripts/ README.md`; **29 out of range**, **81 point at blank lines** (110 provably wrong minimum). **1,083 (80%) are inside `Metalogic/WeakCanonical/**`** | **UNDERCOUNT ×85** — see §6 |
| 12 | `Soundness.lean:76` and `SoundnessLemmas/Core.lean:40` assert a `Set.univ` argument `TruthAt` lacks | `Soundness.lean:75` confirmed live and false (`TruthAt` takes 4 args, `Truth.lean:228`). **`SoundnessLemmas/Core.lean` no longer exists** | **HALF CONFIRMED, half moot** |
| 13 | `Semantics.lean` truth-clause table shows 5-arg `TruthAt` with H/G clauses; lists Nullity as a frame axiom | Confirmed at `:184`, `:204-206`, `:181`. **Additionally**: `:226` is a runnable-looking `#check TruthAt M τ t ht (…)` in a ` ```lean ` fence that would not compile, and `:179` gives the frame as a **three**-tuple `F = (W, G, ·)` against `README.md`'s four-axiom `(W, D, R)` | **CONFIRMED, worse** |
| 14 | Automation/README.md line counts wrong by 2-5x; 13 of 27 modules missing; 26 stale `Bimodal.*` across 14 READMEs | **All 15** line-count claims wrong (worst: `ProofStepExport` 332→1,685, ×5.1); **16 of 31** loose modules missing; 2 listed files do not exist. `Bimodal.*`: **exactly 26 across 14 READMEs** | **CONFIRMED; module gap wider** |
| 15 | Three source files cite an ephemeral `specs/NNN` report path | **17 citation sites across 13 live `.lean` files**, plus 6 in live markdown. C9's regex (`\b(tasks?\s+#?[0-9]+\|task-[0-9]+)\b`) structurally cannot match a `specs/NNN_slug/` path | **UNDERCOUNT ×4-6 + GATE GAP** |
| 16 | Twelve flagship theorems carry no paper anchor at the declaration site | **0 of 20** flagship declarations carry an anchor in their own `/--` block. Additionally `BXCanonical.completeness` has **no `/--` doc comment at all** | **CONFIRMED, worse** |
| 17 | No `docs/theorem-index.md`, no `CITATION.cff`, no `docs/ARCHITECTURE.md`; BibTeX year 2025 vs 2026 | All three absent; `docs/decisions/` also absent. `README.md:332` `year = {2026}` vs `:340` `year = {2025}` | **CONFIRMED** |
| 18 | `README.md:150-152` says `cd ProofChecker` | Confirmed at `:151-152` | **CONFIRMED** |
| 19 | `Independence/README.md:30` cites `co_not_derives_prior_U` | **Already fixed** — the file no longer contains that name | **STALE — drop** |

### 2.1 Already fixed; remove from scope

- **E-01** (`README.md` contradicts the ledger on Dedekind): fixed. `README.md:168` now states
  the refutation with `notStrongCompletenessDedekind` / `notCompactDedekind`.
- **E-02** (`typst/FormalFoundations.typ` reports a `sorryAx`): fixed. All five sites now read
  "no `sorryAx`" (`:681,688,695,704,999`).
- **E-07** (`Semantics/README.md` misses three modules): fixed, and comprehensively —
  `Semantics/README.md`'s Contents table now covers all 24 loose modules plus every
  subdirectory, with real descriptions. **Use it as the template for item (1)'s generated
  tables** (see §4.1).
- **E-18** (`co_not_derives_prior_U`): fixed.
- **B-17** (Conservativity denies its own CEF result): fixed —
  `Conservativity.lean:82` and `Conservativity/Backward.lean:168` both name `ℚ ×_lex ℤ` correctly.

### 2.2 New defects found, named by no review

1. **`FormalSystem/Metalogic/Conservativity/README.md` does not exist** — a 12-file, 2,508-line
   live directory with no README. `readme-lint.sh` Check 1 reports it and **currently exits
   FAIL** on this plus four others: `ForMathlib/Order/`, `Conservativity/Star/`,
   `Semantics/Frames/`, `Semantics/Ultraproduct/`.
2. **`SoundnessLemmas.lean`'s Contents omits `DiscreteOrder.lean`** and the aggregator does not
   import it — the identical defect A-10 recorded for `Separability.lean`, reintroduced one file
   later.
3. **Two distinct declarations share the base name `completeness_dense`** —
   `FormalSystem.Metalogic.BXCanonical.completeness_dense` (`BXCanonical/Completeness.lean:255`)
   and `FormalSystem.Metalogic.completeness_dense` (`StrongCompleteness.lean:987`). Same for
   `completeness_discrete`. Both pairs are pinned (C2 pins the BXCanonical ones, C14 the
   `Metalogic` ones). **The theorem index must use fully-qualified names throughout**, not
   "where ambiguous" — see §4.2.
4. **Three different provenance stamps for one status claim**: `typst/generated/status.typ`
   says commit `29e8d5713` (2026-09-01), `typst/FormalFoundations.typ:980` says the axiom
   reports "were taken at commit `7aae4e51c`", and HEAD is `f6ce84139`. The hand-written table
   at `:987-993` also attributes `completeness_dense`/`completeness_discrete` to
   `BXCanonical/Completeness.lean` — correct for the BXCanonical pair, but the table is
   captioned as covering "the four completeness results", which elsewhere means the
   `Metalogic`-namespace ones.

---

## 3. Interaction with the checks task 529 just landed

### 3.1 C18 cannot see the duplication it was built for — and reports PASS

C18 pools **blank-line-delimited paragraphs**, whitespace-normalises them, and reports any
**exact** normalised paragraph appearing twice. E-13's duplication is *sentence*-level inside
differently-bounded blocks (a `/-!` docstring bullet in `Metalogic.lean` versus a markdown
paragraph in `README.md`, each with different surrounding text). No normalised paragraph is
byte-identical, so C18 prints `PASS C18 zero duplicated paragraph(s)` while two duplicates
stand:

- `README.md:270` ≈ `FormalSystem/Metalogic.lean:153` — "single mechanism by which closure is
  shown: exhibit one formula valid on precisely the class's members"
- `README.md:283` ≈ `FormalSystem/Metalogic.lean:164` — "…`Mod (AxiomSet .Discrete)` and
  `Mod (AxiomSet .Dedekind)` remain open and are not promised"

**Reconciliation for the plan**: C18's zero is a true statement about paragraph-level
duplication and a false negative for the defect E-13 describes. The fix is to add a
**sentence-level** pass (shingle on sentence boundaries, ≥ 15 words, same four files), not to
replace C18 — the paragraph pass is still the right detector for wholesale copy-paste. Treat
this as widening C18, not adding C20.

### 3.2 Check-number collisions between review and tree

The review's §5.1 proposes a "C16 (duplication)" and a "C17 (name resolution in markdown)".
Task 529 assigned C16 = env_linter, C17 = dead-declaration census, C18 = paragraph duplication,
C19 = docstring coverage. So:

| Review label | Tree reality |
|---|---|
| review C16 (duplication) | landed as **C18** (weaker; see §3.1) |
| review C17 (backtick name resolution in markdown) | **not implemented** — no check resolves declaration names cited in `FormalSystem/**/*.md` or `docs/**/*.md` |

The unimplemented review-C17 is the check that would have caught E-03, E-18 and E-20.5.
`scripts/typst-sync-check.sh` already implements exactly this resolver for `typst/**`; the work
is scope-widening, not new logic. **Next free number is C20.**

### 3.3 What 529 gave this task for free

- **C14 now pins 52 declarations** (`check-module-invariants.sh:885-936`), not 4. Combined with
  C2's 4 that is **54 machine-pinned declarations** at exactly
  `[propext, Classical.choice, Quot.sound]` (three exceptions: `setConsequence_of_not_satisfiable`,
  `satisfiableSet_iff_finitelySatisfiable`, `modelExistence_iff_finitelySatisfiable` at
  `[propext]`; `qDepth_qAlpha` at `[propext, Quot.sound]`). Item (1)'s "extend the baseline from
  8 to every flagship declaration" is **already 80% done**; the remaining work is §4.2's list.
- **C9 widened** to `lakefile.lean`, `README.md`, `scripts/` and passes.
- **C14's stale-count regex widened** with a `covers` precision guard.
- **`readme-lint.sh` Check 4** now compares a present `Last verified` stamp against the
  directory's last commit date (reporting-only). It currently reports **9 STALE + 7 MISSING**
  across 47 READMEs.

### 3.4 The one thing blocking a green gate

`bash scripts/check-module-invariants.sh --no-build` exits 1 on **C15 alone**: three paper-anchor
citations resolve to nothing — `app:drift`, `cor:no-characterization`,
`lem:deterministic-singleton`, all from `Metalogic/Independence/`. This is pre-existing, is 529's
named follow-up, and **is inside this task's item (2) territory**: item (2) extends C15, and C15
is red. The plan must decide whether to classify those three anchors (LIVE-UNPINNED vs DANGLING
rows in the record's KNOWN-ANCHORS block) as part of this task or leave C15 red. Classifying
them requires paper-content knowledge; §7 records it as the one genuine open question.

---

## 4. Item-by-item specification

### 4.1 Item (1) — Policy: the three owners

**(a) Axiom sets — owned by C2 + C14.** Already 54 declarations. The SORRY-FREE claims in
`Metalogic.lean` that remain unpinned are exactly these **35**:

```
blCompactBase, blCompactDense, bl_not_derivable_nil_bot,
bl_not_derivable_nil_bot_discrete, bl_soundness, bl_soundness_dedekind,
bl_soundness_dense, bl_soundness_discrete, ceb_backward, cec_backward,
ced_backward, cef_backward, companionChronicle, consequence_completeness_dedekind,
countermodel_discrete, decide, derivable_translate, deterministic_not_starDefinable,
galoisClosed_isDiscrete, galoisClosed_mod, galoisClosed_of_indicator,
galoisClosed_sat_dense, kampPriorExpressiveCompleteness, notCompactDedekind,
notCompactDiscrete, soundness, soundness_dedekind, soundness_dense,
soundness_discrete, star_soundness_validIn, tmFrag_complete_* (four rows),
tmFrag_sound, tm_le_tmFrag, truthAt_tr, uSExpressivelyCompleteOverPrior
```

Notably the **four flagship soundness theorems are unpinned**, as is the whole
Conservativity / BaseLanguage / Star family. Adding them is a mechanical extension of the
existing `C14_BASELINE` heredoc plus matching `#print axioms` lines — the mechanism needs no
change, only rows. Cost: one `lake build`-backed run per iteration (C14's `#print axioms` half
is skipped under `--no-build`), so batch the additions into one phase.

Caveat for the planner: `tmFrag_complete_*` is a family, not a declaration; enumerate its four
members. `decide` is a `def`, not a theorem — `#print axioms` still works but the row reads
oddly; consider whether it belongs in the flagship set at all.

**(b) Counts — owned by a generated block.** Two viable designs:

| | Design A: `check-module-invariants.sh --emit-inventory` (delegation's literal ask) | Design B: promote `scripts/readme-inventory.sh` to the writer, add a C20 no-op check |
|---|---|---|
| Traversal | reuses C7's already-correct Boneyard-excluding walk | must duplicate the walk (readme-inventory.sh currently has no Boneyard exclusion) |
| Script size | adds ~80 lines to an already-1,450-line script | keeps the generator standalone and testable |
| CI wiring | free (already in CI) | needs a new check anyway |

**Recommendation: Design A**, with `readme-inventory.sh` deleted or reduced to a thin
`exec`-shim. It is the delegation's ask, it reuses the one traversal that is already correct,
and `readme-inventory.sh` today is a 41-line paste-helper that emits `<!-- TODO: add
description -->` placeholders, has no Boneyard exclusion, and no in-place write — it is not a
head start.

**Hard design constraint the delegation does not state**: the Description column is
hand-written and must survive regeneration. `Semantics/README.md` (see §2.1) proves the value
of good descriptions — regenerating over them would be a net loss. So the generated block must
regenerate **File and Lines only**, keying on the file name to carry the existing Description
across. A row for a new file gets a `<!-- TODO -->` description; a row whose file disappeared is
dropped.

Block form (matching the delegation): `<!-- BEGIN GENERATED: inventory -->` …
`<!-- END GENERATED -->`. Two modes: `--emit-inventory` writes in place; `--emit-inventory
--check` exits non-zero if a rewrite would change any byte. Only the second belongs in CI.

Registered targets (files that currently carry a hand-maintained count table):
`README.md`, `FormalSystem/README.md`, `FormalSystem/Metalogic/README.md`,
`FormalSystem/Automation/README.md`, `FormalSystem/Syntax/README.md`,
`FormalSystem/Theorems/README.md`, `FormalSystem/Metalogic/SoundnessLemmas/README.md`,
`FormalSystem/Metalogic/Independence/README.md`, `FormalSystem/Automation/Tactics/README.md`.

**Current live inventory** (ground truth for the first generation):

| Scope | Files | Lines |
|---|---:|---:|
| `FormalSystem/` (live) | **459** | **281,222** |
| `Metalogic/` (live) | **330** | **227,266** |
| `Metalogic/` loose `.lean` | **15** | — |
| `Metalogic/` subdirectories | **9** (Conservativity/ is new) | — |

Per-subdirectory: `Algebraic` 5/2,425 · `BXCanonical` 28/23,120 · `Bundle` 9/2,856 ·
`Conservativity` 12/2,508 · `Core` 4/1,838 · `Decidability` 62/52,668 · `Independence` 12/2,987 ·
`SoundnessLemmas` 4/1,458 · `WeakCanonical` 179/132,113.

Against these: `Metalogic/README.md:6-7` says 315 / 226,146; `:213` says "The eight directories
total 296 files. C7's `Metalogic 315` rollup is 19 higher" — wrong on the directory count (nine),
the subdirectory total (315), the rollup (330) and the loose count (15). `README.md:107` says
"413 live .lean files" against 459.

**(c) Per-theorem status — owned by `docs/theorem-index.md`.** See §4.2.

**Delete `Metalogic.lean`'s Module Structure block** (E-04). It is now at **`:253-286`**, not
`:224-256`. Replacing it with three sentences plus pointers to `Metalogic/README.md` and
`scripts/check-module-invariants.sh` also removes the `:256` two-Boneyards contradiction and the
`:269` Kamp-Boneyard claim in one edit.

### 4.2 Item (1c)/(2) — `docs/theorem-index.md`

**Schema** (as E-docs §5.2, with two amendments):

```
| Paper label | Statement (one line) | Lean name | File | Frame class | Axioms |
```

Amendment 1 — **the Lean name column is fully qualified, always**, not "where ambiguous".
`completeness_dense` and `completeness_discrete` each name two distinct live theorems (§2.2.3),
and a reader cannot disambiguate from the File column alone once both files are listed.

Amendment 2 — **the Axioms column is generated**, and the generator is the C2/C14 `#print
axioms` run that already exists. Values: `pcq` for exactly
`[propext, Classical.choice, Quot.sound]`; the literal list otherwise (four declarations differ,
§3.3); `pinned:C2` / `pinned:C14` for the machine-asserted set; `claimed` for prose-only. With
54 declarations pinned, most rows will read `pcq pinned:C14`.

**The E-docs §5.2 seed table cannot be transcribed — four of its sixteen rows name declarations
that no longer exist**, and two more have the wrong File. Verified corrections:

| E-docs §5.2 says | Actual |
|---|---|
| `discrete_consequence_not_compact` | **`notCompactDiscrete`** (`Metalogic/DiscreteNonCompactness.lean:268`) |
| `strongCompletenessDiscrete_refuted` | **`notStrongCompletenessDiscrete`** (`…:287`) |
| `dedekind_consequence_not_compact` | **`notCompactDedekind`** (`Metalogic/DedekindNonCompactness.lean:456`) |
| `strongCompletenessDedekind_refuted` | **`notStrongCompletenessDedekind`** (`…:473`) |
| `completeness_dense` in `BXCanonical/Completeness.lean` | **two** theorems: `…BXCanonical.completeness_dense` there, `…Metalogic.completeness_dense` in `StrongCompleteness.lean:987` |
| `completeness_discrete` in `BXCanonical/Completeness.lean` | same split (`…:296` and `StrongCompleteness.lean:1101`) |
| `deduction_theorem` (`Core/DeductionTheorem.lean`) | **`FormalSystem.ProofSystem.Derivable.deduction`** (`…:467`) |

Every other name in the §5.2 seed and continuation list **was verified present** at the stated
file: `galoisClosed_{mod,of_indicator,sat_dense,isDiscrete}`, `validOn_nextTop_iff{,_isDiscrete}`,
`validOn_{dn_iff_denselyOrdered,df_iff_isDiscrete,co_iff_isComplete}`,
`sat_{dedekind,discrete}_ssubset_mod_axiomSet`, `kampPriorExpressiveCompleteness`,
`countermodel_{dense,discrete,dedekind_dense}`, `sound_of_isValid`, `isValid_sound`,
`co_not_derives_prior_U_gap{,_schema}`, `co_derived`, `modelExistence{Base,Dense}`,
`compact{Base,Dense}`, `strongCompleteness{Base,Dense}`, `consequence_completeness_*`,
`soundness{,_dense,_discrete,_dedekind}`.

**Paper anchors — the availability constraint.** `specs/paper-definitions-of-record.md` pins
**75 distinct anchors**. For the flagship set, the usable ones are `thm:TM-soundness` (the four
soundness rows) and `cor:tm-completeness` (the four weak-completeness rows). The Correspondence
rows already have `app:dense` / `app:discrete` / `app:complete`. **The compactness,
non-compactness and consequence-completeness rows have no paper anchor** — they are the
formalization's own results, and the schema's `—` is the correct value. Any plan phase that
budgets "add an anchor to each of the twelve" will stall on eight of them. State this in the
phase: `Paper: —` with a one-clause reason is the deliverable for those rows, and the C15
extension must accept `—` as a satisfied cell.

**`Paper:` line placement** (item 2). Verified: **0 of 20** flagship declarations carry an
anchor in their own `/--` block, though anchors are plentiful in the module docstrings
(693 anchor-shaped strings live under `FormalSystem/`). Doc-comment sizes at the twenty sites
run 0-21 lines, so a one-line addition is cheap everywhere. Model to copy:
`Semantics/TaskFrame.lean:74` (`def:frame#Spherical`, verbatim) and
`Semantics/Correspondence/DurationFrames.lean:354,419,485`.

`FormalSystem.Metalogic.BXCanonical.completeness` (`BXCanonical/Completeness.lean:196`) has
**no `/--` doc comment at all** — a `/-!` module docstring at `:17-55` covers the file, and the
theorem itself is bare. It needs a doc comment before it can carry an anchor.

**C15 extension** (item 2, second half). C15's current shape: build a resolvable-anchor set from
the record's MANIFEST and KNOWN-ANCHORS blocks, grep all anchor-shaped strings out of live
scope, fail on any unresolved. The extension is a **second, independent assertion** in the same
check: parse `docs/theorem-index.md`'s rows, and for each row assert the named declaration's
doc comment contains either the row's anchor or the literal `Paper: —`. Do not entangle it with
the existing resolution loop — that loop is currently red (§3.4), and a coupled implementation
would make the new assertion unrunnable until the three Independence anchors are classified.

### 4.3 Item (3) — three-register docstring cleanup

Current comment-block share and archaeology-phrase counts (re-measured; the delegation's figures
predate three tasks of edits):

| File | Lines | Comment share | Archaeology hits |
|---|---:|---:|---:|
| `Semantics/Validity.lean` | 1,001 | 71.3% | 19 |
| `Semantics/FrameClassValidity.lean` | 202 | 83.2% | 0 |
| `Metalogic/StrongCompleteness.lean` | 1,125 | 75.8% | 15 |
| `Metalogic/SetConsequence.lean` | 626 | 72.7% | 12 |
| `Metalogic/Conservativity.lean` | 295 | **95.9%** | **1** |
| `Metalogic.lean` | 287 | 94.8% | — |

Two corrections to the delegation's targeting:

1. **`Conservativity.lean` should be dropped from the halve-the-prose list.** Its archaeology is
   already cleared (1 hit) and its 95.9% comment share is *by design* — it is a
   documentation-bearing aggregator whose whole content is the CEB/CEF/CED/CEC status record and
   the standing prohibition on attempting forward conservativity. Halving it would delete the
   record the tree relies on. Target it for **duplication removal only** (its ledger rows
   overlap `Metalogic.lean`'s).
2. **`FrameClassValidity.lean` has zero archaeology hits** but 83.2% comment share; A-18's
   specific complaint (a paragraph on a rejected refactoring, `:56-77`) is a *layering-rationale*
   passage, which is register (b) — it moves to an ADR, it is not deleted.

**ADR destinations** (`docs/decisions/` does not exist; create it). E-12's mapping, re-verified:

| Content | Current sites | ADR |
|---|---|---|
| Archive consolidation / "used to live in two places" | `FormalSystem/README.md:11-33`, `Metalogic/README.md:10-22` | `docs/decisions/single-boneyard.md` |
| "Why there is no physical regroup" + "The declined regroup" | `Metalogic/README.md` | `docs/decisions/metalogic-no-physical-regroup.md` |
| `validity_decidable` retirement (**four** copies) | `README.md`, `FormalSystem/README.md`, `Decidability/README.md`, `Decidability/Verified/README.md` | `docs/decisions/decidability-one-directional.md` |
| `FrameClass` relocation rejected | `FrameClassValidity.lean:56-77` | `docs/decisions/frameclass-validity-seam.md` |

The repo already has `docs/architecture/ADR-001…`/`ADR-004`, so a second directory named
`decisions/` competes with an existing convention. **Recommend `docs/architecture/ADR-005…`
onward** rather than a new `docs/decisions/`, unless the plan deliberately migrates the four
existing ADRs. This is a real fork; the delegation names `docs/decisions/*.md` and the tree
already says `docs/architecture/ADR-NNN`. Flagging rather than deciding.

**A-10's stale claims, re-verified as still live:**

- `Soundness.lean:75` — "`TruthAt`'s remaining set argument is inert and is supplied as
  `Set.univ`". `TruthAt` (`Truth.lean:228`) takes `(M) (τ) (t) : Formula → Prop`. False.
  (`SoundnessLemmas/Core.lean:40`, A-10's second site, no longer exists.)
- `Semantics/Truth.lean:138` — "See SoundnessLemmas.lean for details on the module hierarchy
  restructuring." `SoundnessLemmas.lean` carries no such detail.
- `SoundnessLemmas/FrameClassVariants.lean:699-702` — "This resolves the 3 `temporal_duality`
  sorries in Soundness.lean: `soundness` (line ~877), `soundness_discrete_valid` (~1094),
  `soundness_discrete` (~1151)". Zero sorries exist (C3); all three line numbers wrong.
- `Automation/AesopRules.lean:41-43` — "excluded pending soundness proofs: TL (temp_l)…
  MF (modal_future): soundness incomplete". Both proved in `Soundness.lean`.
- `Semantics/Validity.lean:918` — "matching both `satisfiable` and the binder list of
  `SemanticConsequence`". `SemanticConsequence` is an abbreviation with no binder list.

### 4.4 Item (4) — citation convention, and why it must be re-scoped

The convention itself is right and cheap to state. The enforcement scope is not.

**Ground truth**: 1,354 `file.lean:NNN` citations in live `FormalSystem/ docs/ Tests/ typst/
scripts/ README.md`. Distribution:

| Area | Citations |
|---|---:|
| `FormalSystem/Metalogic/WeakCanonical/**` | **1,083** (80%) |
| `FormalSystem/Metalogic/**` (rest) | 93 |
| `typst/**` | 80 |
| `docs/**` | 85 |
| `FormalSystem/Semantics/`, `Syntax/`, `README.md`, `Tests/`, `scripts/` | 13 |

Provably wrong: **29 out of range**, **81 pointing at blank lines**. The out-of-range set is
concentrated in `Kamp/NfMultiAnchorBridge/` — fifteen sites cite `SharedWitness.lean:806`,
`:9262`, `:12529`, `:12710` and similar against a file that is **87 lines long**, i.e. the
citations survive a file that was split. One is in `docs/`
(`development/PHASED_IMPLEMENTATION.md:77` → `Perpetuity.lean:139`, file has 96 lines).

**Recommended scoping rule** (this is the key planning decision on item 4):

- **Enforce in publication-facing scope**: `README.md`, `docs/**`, `typst/**`, every `README.md`
  under `FormalSystem/**`, and `FormalSystem/*.lean` + `FormalSystem/Metalogic/*.lean` +
  `FormalSystem/Semantics/*.lean` (the aggregators and top-level modules a paper reader lands
  on). That is **184 citations across 32 files** — tractable in one or two phases, and it covers
  every surface doc-gen4 and the paper actually expose.
- **Report, do not gate, in `Metalogic/WeakCanonical/**`**. Those 1,083 are internal
  proof-engineering navigation notes between files a referee will never open. Gating them turns
  a documentation nicety into a 1,000-site refactor with real regression risk.
- **Fix all 110 provably-wrong sites regardless of scope** — an out-of-range or blank-line
  citation is a defect anywhere, and it is machine-detectable, so the fix is verifiable.

The new check (C20) should therefore have two tiers: FAIL on any citation that is out of range
or lands on a blank line (repo-wide, live scope); TODO/report on any citation at all in the
publication-facing scope, with an `ENFORCE_C20=1` flag following the C8/C9/C10 pattern already
in the script.

`docs/reference/API_REFERENCE.md` carries 6 citations and a `**Last Updated**: 2026-01-11`
header against eight months of change — it needs the header fixed in the same pass.

### 4.5 Item (5) — the verifiable mismatch list

Beyond §2 and §4.3, verified and ready to fix:

- `README.md:151-152` — `cd ProofChecker` after cloning `BimodalLogic`.
- `README.md:332` `year = {2026}` vs `:340` `year = {2025}` in the two BibTeX entries.
- `Semantics.lean:179` three-tuple frame; `:181` Nullity as an axiom (README.md:82 calls it
  derived); `:184` five-argument `TruthAt`; `:204-206` `□` as `σ.domain t` (actual: `σ.IsTotal`)
  plus non-existent `H`/`G` clauses; `:226` a `#check` example that would not compile.
- `Automation/README.md` — 15 wrong line counts, 16 missing loose modules, 2 phantom entries
  (`Automation.lean`, `EFGameTactics.lean`).
- **26** `Bimodal.*` references across **14** READMEs (namespace does not exist in any `.lean`).
- **17** `specs/NNN_slug/` path citations across 13 live `.lean` files + 6 in live markdown.
  C9 cannot see them (§2, row 15). Widening C9's regex with `specs/[0-9]{3}_` is a one-line
  change and belongs with this item, not item 4.
- `docs/README.md:273-277` — `lake build :docs` recipe with no `doc-gen4` requirement in
  `lakefile.lean` and zero matches in `lake-manifest.json`. Still broken (E-08).
- `typst/generated/status.typ:22,28` — `sorry-total-excl-boneyard = 0` printed beside
  `("WeakCanonical/", 4)` (E-10). Still present. The generator already computes
  `SORRY_WEAKCANONICAL_LIVE` and `SORRY_KAMP_BONEYARD` separately
  (`typst-status-counts.sh:116-118`), so the two-row split is a three-line change.
- `Metalogic/README.md:158-175` "**Ten** loose files … are not aggregators" above an 11-row
  table — actual **6**, and 5 of the 11 rows are phantoms: `BaseLanguageSoundness.lean`,
  `TMCompletenessReduction.lean`, `SpWitness.lean` and `Z1Countermodel.lean` all moved to
  `Metalogic/Conservativity/`, and `Conservativity.lean` became that directory's aggregator.
  This section is the single most drifted block left in the tree and is a direct casualty of the
  `Conservativity/` extraction that landed after the review.
- **9 stale + 7 missing** `Last verified` stamps across 47 READMEs.
- **5 missing READMEs** making `readme-lint.sh` exit FAIL: `ForMathlib/Order/`,
  `Metalogic/Conservativity/` (12 files!), `Metalogic/Conservativity/Star/`,
  `Semantics/Frames/`, `Semantics/Ultraproduct/`.
- `SoundnessLemmas.lean` Contents and imports omit `DiscreteOrder.lean`.

### 4.6 Item (6) — publication packaging

- **`CITATION.cff`**: absent. Reconcile to `year: 2026` (the article entry, and the current
  date). Note `README.md:299`'s BibTeX key is `proofchecker2025` and `CLAUDE.md`'s title is
  "ProofChecker" while the repository is `BimodalLogic` — pick one name in the `.cff` `title`
  and say the relationship once, per E-17.
- **`docs/ARCHITECTURE.md`**: absent. Must name **both** upward edges in the diagram itself:
  `Semantics → ProofSystem` via `Semantics/FrameClassValidity.lean`, and
  `Decidability → Automation`. Source material: `FormalSystem/README.md:234-269` (six one-row
  layer tables) and `Metalogic/README.md:293-308`. `FormalSystem/README.md`'s Layer 0 now also
  includes `ForMathlib` and `StarLanguage`, which no existing diagram shows.
- **`## Verifying the main theorems` in `README.md`**: `#print axioms` appears **nowhere** in
  `README.md`. The snippet should cover a representative slice of the 54 pinned declarations
  (not all 54) plus the one-line `bash scripts/check-module-invariants.sh`.
- **`## Tags` lines**: **zero** in the tree. G-07's ~30-file target is a judgement call; the
  natural set is the files the theorem index rows point into plus the `Semantics/` and
  `Correspondence/` layers.
- **`references.bib`** (G-09): absent, and worth folding in — Reynolds, Blackburn–de
  Rijke–Venema, Kamp and Prior are already cited in prose (`ProofSystem/Axioms.lean`'s `sep`
  docstring).

### 4.7 Item (7) — generate the typst axiom table

`scripts/typst-status-counts.sh` emits `typst/generated/status.typ` with counts only — no
per-declaration axiom data. The hand-written table lives at
`typst/FormalFoundations.typ:983-996` (5 rows).

The generator already has the harder half solved elsewhere:
`scripts/typst-machine-appendix.sh` runs Lean through `lake env lean --run` and renders JSONL
into a committed `.typ`. **Copy that pattern**: compile a scratch file of `#print axioms`
directives for the pinned set (the same construction C2 and C14 already use at
`check-module-invariants.sh:175-178` and `:885-936`), parse the output, emit
`#let axiom-report-table = (…)` into `status.typ`, and replace the hand table with a
`#for` over it.

Two constraints:
- The generated rows must carry **fully-qualified** names (§2.2.3) or the table will repeat the
  `completeness_dense` ambiguity it currently has.
- The generator needs a built library, so it cannot run under a `--no-build` path. Keep it a
  separate script invocation as today, not a new mode of the invariants script.

Fix the three-way provenance stamp (§2.2.4) in the same pass: `FormalFoundations.typ:980`'s
"taken at commit 7aae4e51c" should read from `status.typ`'s `stamp-commit`.

---

## 5. Recommended phase decomposition

Sized so each phase is one agent run producing a verifiable artifact, and ordered so every
phase after the first can be checked by a gate the previous phase installed.

| # | Phase | Deliverable | Verification |
|---|---|---|---|
| 1 | `--emit-inventory` mechanism | `check-module-invariants.sh --emit-inventory[--check]`, description-preserving; 9 registered targets converted to generated blocks | `--emit-inventory --check` exits 0; `readme-lint.sh` Check 2 count drops |
| 2 | Regenerate + delete the census | All 40 wrong line counts and every rollup fixed by generation; `Metalogic.lean:253-286` deleted and replaced with narrative + pointers | `--check` clean; C14 clean; the two-Boneyards and Kamp-Boneyard claims gone |
| 3 | Theorem index, seeded and verified | `docs/theorem-index.md` — 16 corrected seed rows + continuation + Notation table; fully-qualified names; Axioms column generated | every Lean name resolves; every path exists |
| 4 | C14 baseline extension | the 35 unpinned declarations added to `C14_BASELINE` + directives | `check-module-invariants.sh` (full, with build) passes C14 |
| 5 | Paper anchors + C15 extension | one `Paper:` line at each of the 20 flagship sites (`—` where no anchor exists); a doc comment for `BXCanonical.completeness`; C15's second assertion | C15's new half passes; C15's *existing* half still red unless §7 is resolved |
| 6 | Citation convention + C20 | 184 publication-scope citations converted to declaration names; all 110 provably-wrong sites fixed; C20 two-tier check; C9 regex widened for `specs/NNN_` | C20 tier-1 clean; C9 clean |
| 7 | Docstring three-register pass | `Validity.lean`, `FrameClassValidity.lean`, `StrongCompleteness.lean`, `SetConsequence.lean` halved; four ADRs written; A-10's five stale claims fixed | `lake build` green; C19 coverage does not regress below 90% |
| 8 | Sentence-level duplication (widen C18) | shingle pass over the same four files; the two surviving duplicates removed | C18 reports zero at both granularities |
| 9 | Verifiable-mismatch sweep | §4.5's list; 5 missing READMEs; 9 stale + 7 missing stamps | `readme-lint.sh` exits 0 |
| 10 | Publication packaging | `CITATION.cff`, `docs/ARCHITECTURE.md`, `references.bib`, README `## Verifying`, `## Tags` | files exist; C12/C13 clean |
| 11 | typst axiom table generation | `status.typ` gains the per-declaration table; `FormalFoundations.typ` hand table replaced; provenance unified | `typst-sync-check.sh` passes; typst compiles |

Phases 1-2 and 3-4 are the two hard dependencies. Phases 6, 7, 9, 10 are independent of each
other and parallelisable under territory contracts (6 owns citation text, 7 owns docstring
prose, 9 owns READMEs, 10 owns new files) — but 6 and 7 both edit
`StrongCompleteness.lean`/`SetConsequence.lean`, so they must be serialised or split by line
range.

**Build-cost note**: phases 4, 7 and 11 need a real `lake build` (2,591 jobs at 529's
measurement). Route those through the detached, guarded pattern in
`.claude/context/project/lean4/operations/long-builds.md`. Phases 1-3, 6, 8-10 are all
verifiable under `--no-build`.

---

## 6. Risks

- **R1 — Item (4) is 85× the delegation's estimate.** Unscoped, it is a 1,354-site edit across
  files whose docstrings are load-bearing proof-engineering notes. §4.4's two-tier rule is the
  mitigation; if the plan instead takes the delegation's literal "fix the 16", it will fix 16 of
  110 known-wrong citations and leave the gate unbuildable.
- **R2 — C15 is already red and item (2) extends it.** Phase 5's acceptance criterion cannot be
  "C15 passes" unless §7 is resolved first. Write the criterion as "C15's new assertion passes;
  its pre-existing three-anchor failure is unchanged and separately tracked."
- **R3 — Regenerating inventories over hand-written descriptions.** `Semantics/README.md`'s
  descriptions are the best documentation in the tree (§2.1). A naive generator destroys them.
  §4.1's key-on-filename constraint is non-negotiable.
- **R4 — The `docs/decisions/` vs `docs/architecture/ADR-NNN` fork** (§4.3). Choosing wrong
  creates a second competing convention in a task whose whole purpose is removing duplicate
  authorities.
- **R5 — Scope hypothesis, again.** Every grep-derived count in the delegation that I re-derived
  came out **higher**, never lower (rows 4, 10, 11, 14, 15, 16 in §2). Treat any remaining
  unverified count in the plan as a lower bound and re-derive at phase start.
- **R6 — Deleting `Metalogic.lean:253-286` touches the file C18 watches.** Phase 2 and phase 8
  both edit it; sequence them.

---

## 7. Open question requiring a decision

**The three unresolved paper anchors blocking C15.** `app:drift`,
`cor:no-characterization` and `lem:deterministic-singleton` are cited from
`Metalogic/Independence/{DriftFrame,RealTranslationFrame,StateSetTruth}.lean` and
`Independence/README.md`, and have no row in `specs/paper-definitions-of-record.md`. Resolving
each requires classifying it as **LIVE-UNPINNED** (the anchor exists in the paper but was
deliberately not pinned) or **DANGLING** (retired or never existed) — a judgement that needs the
paper, which this repository cannot see.

This is the sole reason `bash scripts/check-module-invariants.sh` does not print
`ALL CHECKS PASSED`. It is pre-existing, it is 529's recorded follow-up, and it sits squarely
inside item (2)'s territory.

**Recommendation**: carry it as an explicit non-goal of this task with a stated assumption —
plan phase 5 delivers C15's *new* assertion and leaves the three anchors to a separate,
paper-informed pass — unless the user can classify them, in which case fold the three
KNOWN-ANCHORS rows into phase 5 and the task ends with a fully green invariants run. Everything
else in items (1)-(7) proceeds unblocked either way.

---

## 8. Reproduction

Every number above was derived at `f6ce84139` by one of:

```
bash scripts/check-module-invariants.sh --no-build      # C7 inventory, C14/C15/C18/C19 status
bash scripts/readme-lint.sh                             # missing READMEs, stale stamps
find FormalSystem -name '*.lean' -not -path '*/Boneyard/*' | wc -l
grep -rn 'specs/[0-9]' FormalSystem --include=*.lean | grep -v /Boneyard/
grep -rn '\bBimodal\.[A-Z]' --include=*.md FormalSystem docs README.md
awk '/^#print axioms/' scripts/check-module-invariants.sh | wc -l
```

plus two throwaway Python passes (SORRY-FREE name extraction from `Metalogic.lean`; the
`file.lean:NNN` resolver that produced §4.4's table). Neither was retained; both are ten-line
scripts reproducible from the descriptions above.
