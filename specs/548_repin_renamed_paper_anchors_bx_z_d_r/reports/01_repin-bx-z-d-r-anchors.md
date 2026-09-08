# Research Report: Task #548

**Task**: 548 - Re-pin the paper anchors changed by the paper's z/d/r refactor and its removal of the Past/Future fragment
**Started**: 2026-09-07T18:07:00Z
**Completed**: 2026-09-07T18:35:00Z
**Effort**: Medium (mechanical record surgery + 32 docstring citation sites; no Lean proof work)
**Dependencies**: None (the three unrelated unresolved anchors named in the task description are already absorbed — see Findings)
**Sources/Inputs**: - Codebase (`FormalSystem/`, `docs/`, `typst/`, `README.md`), `specs/paper-definitions-of-record.md`, `scripts/check-paper-definitions.sh`, `scripts/check-module-invariants.sh` (C15), live paper `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`
**Artifacts**: - specs/548_repin_renamed_paper_anchors_bx_z_d_r/reports/01_repin-bx-z-d-r-anchors.md
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **C15 is currently GREEN, not red.** All 53 paper-anchor citations in live scope resolve against the record today. The task description's "MEASURED STATE" is stale on this point: the three anchors it names as unrelated leftovers (`app:drift`, `cor:no-characterization`, `lem:deterministic-singleton`) were already absorbed as `LIVE-UNPINNED` rows by the record's own "Anchor classification (2026-09-07)" wave, and `def:TMplus-f/-d/-c` still resolve *because they are still pinned*. The real defect is therefore not a C15 failure but a **record-vs-paper falsehood**: the manifest pins three anchors that no longer exist in the paper.
- **The gate that is actually red is `scripts/check-paper-definitions.sh`** (exit 1): **15 pinned entries drifted** and **9 pinned anchors are dangling**. That is a full drift wave, four to five times larger than the three-anchor rename the task description scopes. The record's own "How to extend this record" step 4 demands a quiet case-(a) pass, so the wave must be absorbed as one unit — exactly the pattern the injected memory ("Absorb a check-paper-definitions drift wave before re-pinning") describes.
- **Ordering is load-bearing and non-obvious.** Renaming the 32 in-tree citation sites from `def:TMplus-f/-d/-c` to `def:BX-z/-d/-r` *before* adding the new manifest rows would turn C15 from green to red mid-implementation. Record first, docstrings second.
- **Three task-description premises are factually wrong against the live paper** and must not be implemented as stated: the Z1 footnote is commented out (not live); `thm:TM-soundness` needs no re-hash; and the third `BX_r` axiom is `SEP`, not `SP`.
- **No sorry-free-proof question arises.** This task writes no Lean proof terms — it edits Markdown, docstrings, and comments only. Zero-debt compliance is trivially satisfiable; the only build risk is docstring syntax breakage, which `lake build` catches.

## Context & Scope

Researched: what the live paper now says at the anchors the task names; what the record currently pins; what C15 and `check-paper-definitions.sh` currently report; and every in-tree citation site that must move. Constraint: the paper is read-only input in a separate repository (`/home/benjamin/Philosophy/Papers/PossibleWorlds`, currently at `f61bbd75` with `JPL/possible_worlds.tex` **dirty/uncommitted**) — the dirty-pin caveat the record already documents applies to this wave too.

## Findings

### Codebase Patterns

**1. C15's current state (measured, not assumed).** Re-running C15's exact pipeline by hand:

```
cited=53  known=67  UNRESOLVED: (none)
```

Confirmed by the real gate — a full `scripts/check-module-invariants.sh` run reports
`PASS  C15  all 53 paper-anchor citation(s) resolve against specs/paper-definitions-of-record.md`
and `PASS  C15  all 52 theorem-index row(s) carry their anchor (or \`Paper: —\`) at the declaration`.

C15 resolves a citation if the anchor has a row in either the MANIFEST block or the KNOWN-ANCHORS block. `def:TMplus-f/-d/-c` all still have manifest rows, so every citation of them resolves. C15 checks *names*, never hashes — it is deliberately insulated from paper edits. Therefore **C15 cannot detect this defect at all**, and "re-run until C15 reports no unresolved anchor" is a check that already passes. The meaningful acceptance gate is `check-paper-definitions.sh` returning 0.

`scripts/check-module-invariants.sh` takes **well over 10 minutes** to run end to end (it was still running at 15+ minutes in this session). Plan around that: the C15 block can be reproduced standalone in about a second by extracting the two sentinel-delimited blocks and `comm`-ing against the `grep -rhoE '\b(def|thm|lem|cor|app|rmk):[A-Za-z0-9][A-Za-z0-9_-]*'` sweep over `FormalSystem Tests typst docs README.md` (excluding `Boneyard`).

**2. The full drift wave.** `scripts/check-paper-definitions.sh` exits 1 with:

*15 drifted entries* (new hashes, already measured — usable verbatim by the implementer):

| anchor | new sha256 |
|---|---|
| `def:frame` | `b5d3bf93cf07486d239afcbc9379883fdbea1194e97d560b391ccbdc128b9d99` |
| `def:world-history` | `550661d3b388c3ef494ffb81c643ab5a550f996a5a86329afc557f41ed7872e7` |
| `thm:extension` | `65811dcff91a3dd840058353b14667d8abfcf5d94c8be9979944f03be5234379` |
| `cor:occurrence` | `231c1d3cd0bf70a323775c623ed36761c6e0c4990bf72106c8323a9fe78842ec` |
| `def:BL-semantics` | `b64b782a61c9a9613b68f37ec2d12229e7df8498043faeb1cf1c2686b8dd5a75` |
| `def:BLplus-language` | `574bc1ad10ca0957a5b76c0d74f7ff5b2ea6a09fa180475c9c22eb6ea5b3e8e2` |
| `def:S5` | `82ec82d7ef3c0e24732fe6216b3326998412c594984ce02639ea4030ceabdb38` |
| `def:BX` | `e1617a218b03206e11ebb9886b9a6a2add44591ce47f719445664e608f39e13e` |
| `def:TMplus` | `c14cad798aac2c73319de9ccc0a34ce6ca07971dbb6427e5107a08f23cc4cea8` |
| `app:discrete` | `23a54c163da3ed991258ccd9647ae153bb2704cd0f86c138c7e5381ac6190e0e` |
| `app:dense` | `751ad28ba753b718dad05beca27b6403a274977ff6e42a53e791d1770041b7d5` |
| `app:complete` | `9d962cf8efb3530cad11939c690d0a704154f4ddaaa7904f21ea9b8226a1f2fe` |
| `def:frame-properties` | `709cefc5c849b2fe6bb950cbde6b1a738181c48eeff25e89df0bb5a457e2f268` |
| `cor:saturation-finite` | `ebf7547b10df6b764b1ccc5d965e0cf5c75cd8b09977ed1572b3d0fba48101c3` |
| `cor:tm-completeness` | `a374007e4006c6ae8388e9e0077e5579fc54d0b032b0369b546be1dfd0271643` |

*9 dangling pinned anchors*: `def:directed`, `def:BLplus-semantics`, `def:BLplus-defined`, `thm:BLplus-PastFuture`, `thm:BLplus-NextPrevious`, `TMP-CO`, `def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c`.

Only three of those nine are in the task's named scope. The other six (`def:directed` folded into `def:frame`'s opening clause; the `BL^+` language/semantics cluster collapsed into `BL`; `TMP-CO` superseded by the plain `\aitem{CO}` at paper line 1369) are the same paper wave and cannot be left pinned if step 4 of "How to extend this record" is to pass. Two of them are also visibly *not* mere renames: `cor:saturation-finite` changed environment (`Cthm` → `Lthm`) and `def:frame` absorbed the `⊇`-directed definition inline while softening "strictly stronger" to "at least as strong as".

**3. The three renamed anchors resolve cleanly.** Measured via the record's own `--resolve` procedure:

| new anchor | kind | sha256 | paper line |
|---|---|---|---|
| `def:BX-z` | `env` | `385f73e873489eb714c7d9ca548dbd20ecb000340af8a3c60f8316eb85909b54` | 4239 |
| `def:BX-d` | `env` | `555db844b3c15ca4f878406540d88c457f372a774bbb59776e3f1b0d0fb76394` | 4252 |
| `def:BX-r` | `env` | `b35751c79a502988f9f77880354c9ed5200e9751361f2f6c209fcc3247721284` | 4260 |

`def:TMplus` (paper line 4273) survives under its own name and now reads "The *Base Logic of Tense and Modality* **TM** for $\BL$ …" with "the discrete **TM**$_\textsc{z}$, dense **TM**$_\textsc{d}$, and dense and complete **TM**$_\textsc{r}$ extensions".

**4. Citation inventory to re-label — 32 occurrences across 17 files.**

`def:TMplus-f` → `def:BX-z` (19 occurrences):
`FormalSystem/Semantics/FrameProperty.lean` (6), `FormalSystem/Metalogic/Conservativity.lean` (3), `FormalSystem/Semantics/FrameClassValidity.lean` (2), and one each in `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/Validity.lean`, `FormalSystem/Semantics/BLValidity.lean`, `FormalSystem/Semantics/Correspondence/Indicator.lean`, `FormalSystem/Semantics/Correspondence/README.md`, `FormalSystem/Metalogic/Independence/LexIntWitness.lean`, `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean`, `docs/theorem-index.md`.

`def:TMplus-d` → `def:BX-d` (2): `FormalSystem/Metalogic/Conservativity.lean`, `docs/theorem-index.md`.

`def:TMplus-c` → `def:BX-r` (11): `README.md` (2), `FormalSystem/README.md` (2), `FormalSystem/ProofSystem/Axioms.lean` (2), and one each in `FormalSystem/Theorems/DedekindDerived.lean`, `FormalSystem/Syntax/Formula.lean`, `FormalSystem/Metalogic/SoundnessLemmas/CoValidity.lean`, `FormalSystem/Metalogic/Conservativity.lean`, `docs/theorem-index.md`.

Bare `def:TMplus` (4 occurrences, `FormalSystem/Metalogic/Conservativity.lean`, `FormalSystem/Metalogic/Conservativity/Fragment.lean`, `typst/chapters/03-proof-theory.typ`, `docs/theorem-index.md`) needs **no label change** — only prose review, since the anchor's *text* changed (TM⁺/BL⁺ → TM/BL, f/d/c → z/d/r).

**5. The tree's prose already anticipates this task.** `FormalSystem/Metalogic/Conservativity.lean:32-34` reads "`BX_z`, `BX_d` and `BX_r` (`def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c` — … relabelled; the record's re-pin is separate work)". A prior wave already migrated the tree's *terminology* to `BX_z`/`BX_d`/`BX_r` and `TM⁺_z`/`TM⁺_d`/`TM⁺_r`; only the anchor labels lag. So this is a label-only migration in most sites, with one genuine quotation to refresh (see next).

**6. The one verbatim quotation that must be re-quoted.** The task description names `Semantics/FrameClassValidity.lean` as quoting the old closing sentence verbatim. Measured: `FrameClassValidity.lean:94-98` and `FrameProperty.lean:131-137` both **paraphrase rather than quote** — `FrameProperty.lean` even says so explicitly ("restated here in the tree's own voice rather than quoted"). Neither contains the literal string "successor-Archimedean discrete class". The substantive fix at both sites is that the paper no longer routes the ℤ-time narrowing through Hölder's theorem inside the definition: `def:BX-z` now cites `prop:archimedean` (paper line 3265, a live `Pthm`) for the failure over non-Archimedean discrete orders, and defers the Hölder step to the §Extensions footnote (paper lines 1408-1411). The tree's parenthetical about Hölder ("where this predicate's name comes from") stays accurate, but "def:TMplus-f's Hölder narrowing" phrasings (6 sites) become misattributions and should read as `def:BX-z`'s narrowing, with `prop:archimedean` as the supporting anchor.

**7. `prop:archimedean` and `def:class-validity` are new live anchors.** Neither is cited in-tree yet (0 hits), so neither needs a row unless the rewritten docstrings start citing them. If the docstring rewrite cites `prop:archimedean` by name — which the correction in finding 6 makes natural — a `LIVE-UNPINNED` KNOWN-ANCHORS row must be added **in the same change**, or C15 goes red. `def:class-validity` is likewise newly referenced from `cor:tm-completeness`'s replacement text.

### External Resources

- Paper `\label` census taken directly from `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` (4468 lines): `prop:fragment` and `rmk:fragment` **do not appear anywhere** — confirming the task's DELETED ANCHORS claim, and confirming they are not pinned and not cited (0 in-tree hits each). **No action is required for them**; do not add DANGLING rows for anchors nothing cites.
- Record header sentinels: `PINNED_COMMIT: fa0dbf7c053e6ecd22e9815180dd91beb2604e61`, `FILE_CHECKSUM: 7303bc9e8529b84f881b17b6f0ef3027f104a6c9ab91315c573a15e00bac0143`. Live paper sha256 is now `93fd9b14d416269b348aee8bdbde871d6d1afed6a37235845fe04b22d28cce1b`; the paper repo is at `f61bbd75` with the file **dirty**. The new pin will again be a checksum over an uncommitted file — the record's "Dirty-pin caveat" section already sanctions this, and should be extended with this wave's date rather than contradicted.

### Recommendations

A sorry-free, gate-green path exists and is fully mechanical. Recommended phase decomposition (each phase is one agent run, each ends green and committable):

1. **Retire + pin in the record.** Retire `def:TMplus-f/-d/-c` (and the six other dangling anchors) from the MANIFEST, keeping their prose entries and marking them `DANGLING` per the record's established convention; add `DANGLING` KNOWN-ANCHORS rows for each. Add three new `### \`def:BX-z\`` / `-d` / `-r` prose entries with the verbatim text and the three hashes in Finding 3, plus three MANIFEST rows. Add a dated "Rename absorption / drift correction (2026-09-07)" narrative section, following the shape of the existing 2026-09-02 and 2026-08-25 sections.
2. **Absorb the remaining 12 drifted entries.** Re-quote and re-hash `def:frame`, `def:world-history`, `thm:extension`, `cor:occurrence`, `def:BL-semantics`, `def:BLplus-language`, `def:S5`, `def:BX`, `def:TMplus`, `app:discrete`, `app:dense`, `app:complete`, `def:frame-properties`, `cor:saturation-finite`, `cor:tm-completeness` using the hashes in Finding 2. Re-run `check-paper-definitions.sh` **with the old `FILE_CHECKSUM` still in place** to force full anchor validation (expect the case-(b) notice pass), per the injected memory's step 3.
3. **Re-pin the sentinels.** Only after phase 2 passes, update `FILE_CHECKSUM` to `93fd9b1…` and `PINNED_COMMIT` to `f61bbd75`, and confirm the quiet case-(a) pass (exit 0, no output).
4. **Re-label the 32 citation sites**, plus prose corrections for the Hölder/`prop:archimedean` shift and the TM⁺/BL⁺ → TM/BL system-naming shift at the 4 bare `def:TMplus` sites. Add a `prop:archimedean|LIVE-UNPINNED|…` row if and only if the rewritten prose cites it.
5. **Verify.** Standalone C15 reproduction (seconds), `check-paper-definitions.sh` (seconds), then a backgrounded `lake build` to confirm no docstring breakage. Full `check-module-invariants.sh` last, backgrounded, budgeting >10 minutes.

Phases 1-3 must precede phase 4. Phases 1 and 2 may be merged if the planner prefers a single record-surgery phase; phase 3 must stay separate so the case-(b) forcing run in phase 2 is meaningful.

## Decisions

- **Treat `check-paper-definitions.sh` exit 0 as the acceptance gate, not C15.** C15 already passes and is structurally incapable of detecting this defect. The plan should still assert C15 stays green (it is the regression risk of phase 4), but must not use it as the completion criterion.
- **Absorb the whole drift wave, not just the three named anchors.** The record's own step 4 requires it, and a partial absorption leaves the repository's one honest paper-drift detector permanently red — which is how the 30-dangling-citation backlog that motivated C15 accumulated in the first place.
- **Do not implement three stale premises in the task description** (see Risks). Record the corrections in the record's narrative section instead.
- **Take no action on `prop:fragment` / `rmk:fragment`.** Nothing pins or cites them; adding rows would violate the record's own "Adding a row here is a decision, not a formality" instruction.

## Risks & Mitigations

- **Risk: ordering inversion turns C15 red.** Re-labelling docstrings before the manifest rows exist breaks the gate. *Mitigation*: enforce phases 1-3 before 4; the plan's phase gate for 4 is "`def:BX-z|env|-|-|385f73…` present in MANIFEST".
- **Risk (task-description defect): the Z1 footnote does not exist as live text.** The description says a Logic-subsection footnote "replaced the fragment proposition" and "cites this repository for the Z1 result (`not_bl_derivable_z1`)". Measured: paper lines 1333-1341 are **entirely commented out**, with an author note at 1334 reading "footnote commented out until the BimodalLogic repository establishes that the Past/Future language admits no complete axiomatization; the repository currently shows only that one particular system in that language is incomplete over Z-time." *Mitigation*: do not record it as live and do not pin it. The live content that replaced it is `prop:archimedean` (a pen-and-paper `Pthm` proof this repository does not check) — which is exactly the "record it as such, do not pin it as verified" treatment the description asks for, applied to the right target.
- **Risk (task-description defect): `thm:TM-soundness` appears to need a re-hash but does not.** It is absent from both the drifted and the dangling lists. The pin covers only the `\begin{Tthm}[Soundness] … \end{Tthm}` statement ("If $\vdash \varphi$, then $\vDash \varphi$."), which is byte-identical; every change the description names (TM-and-its-extensions phrasing, the new since/until/next/previous sentence, the repository footnote) lives in the `\begin{proof}` block *outside* the environment and is therefore not hashed. *Mitigation*: leave the pin and the record entry alone; if the plan wants the new proof-block sentence on record, that is a coverage extension, not a re-hash, and should be called out as such.
- **Risk (task-description defect): the axiom is `SEP`, not `SP`.** `def:BX-r` extends `BX_d` by `\aref{PU}` and `\aref{SEP}` (paper line 4260; the aitems are at 1397-1398). The tree already uses `TMP-SEP` correctly. *Mitigation*: use `SEP` in all new record prose.
- **Risk: `def:derivability` / `def:soundness` have no pin to update.** Both have 0 citations in live scope and appear on exactly one record line — line 1382, inside the "Deliberately not covered" exclusion list. *Mitigation*: the only honest action is to update that exclusion bullet's justification (they are now stated for **TM** and the full language $\BL$ at paper lines 4016 and 4020), or to promote them to the manifest as a deliberate coverage extension. Prefer the former; the exclusion's stated rationale ("proof-theoretic, not semantic") still holds.
- **Risk: `lem:temporal-duality` / `thm:TD-valid` are neither pinned nor cited.** 0 in-tree hits, no manifest rows. The description's note about their new `U`/`S` inductive cases has no repository-side consequence. *Mitigation*: no action; note it in the record narrative so a future reader does not re-derive the finding.
- **Risk: dirty-source pin.** The paper file is uncommitted in its own repository, so `PINNED_COMMIT` will not reproduce `FILE_CHECKSUM`. *Mitigation*: extend the record's existing "Dirty-pin caveat" section rather than pretending the pin is clean.
- **Risk: build-verification cost.** `check-module-invariants.sh` exceeded 15 minutes in this session. *Mitigation*: background it with `Bash(run_in_background: true)` and wait with a single blocking `tail --pid=<pid> -f /dev/null`; never busy-poll.

## Tactic Survey Results

- Not applicable (no tactic survey performed). This task writes no proof terms — it edits Markdown, docstrings, and comments only. `lake build` is used purely to confirm docstring syntax integrity, not to close any goal.

## Context Extension Recommendations

- **Topic**: The C15 / `check-paper-definitions.sh` division of labour.
- **Gap**: Nothing in `.claude/context/project/lean4/` records that C15 checks anchor *names* against the record while `check-paper-definitions.sh` checks anchor *hashes* against the paper, nor that a paper rename is invisible to C15 for exactly as long as the stale manifest row survives. This task's description conflated the two gates, which is the single largest source of scope error in it.
- **Recommendation**: Add `context/project/lean4/domain/paper-anchor-gates.md` capturing the two-gate model, the record-before-docstrings ordering rule, and the drift-absorption procedure (forcing run with the old checksum, then re-pin) that the injected memory already encodes.

## Appendix

Commands used:

- `bash scripts/check-paper-definitions.sh` — full drift report (exit 1; 15 drifted, 9 dangling)
- `bash scripts/check-paper-definitions.sh --resolve 'def:BX-z|env|-|-'` (and `-d`, `-r`) — new text + hashes
- Standalone C15 reproduction: extract MANIFEST and KNOWN-ANCHORS blocks by their HTML-comment sentinels, `cut -d'|' -f1`, `sed 's/#.*//'`, `sort -u`; sweep citations with `grep -rhoE '\b(def|thm|lem|cor|app|rmk):[A-Za-z0-9][A-Za-z0-9_-]*' --include='*.lean' --include='*.md' --include='*.typ' --exclude-dir=Boneyard FormalSystem Tests typst docs README.md | sort -u`; `comm -23`
- `grep -n '\\label{...}'` census over the paper for the live-anchor inventory
- `grep -rnP 'def:TMplus(?![-A-Za-z0-9_])'` to separate bare `def:TMplus` from its suffixed siblings (plain `\b` matches `-`, and over-counts by 15)

References:

- `specs/paper-definitions-of-record.md` §"How to read this file", §"Hashing method", §"How to extend this record", §"Dirty-pin caveat", §"Anchor classification (2026-09-07)"
- `scripts/check-module-invariants.sh` lines 1460-1533 (C15 rationale and implementation)
- `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` lines 1333-1341 (commented fragment footnote), 1367-1398 (aitems), 1408-1413 (Hölder footnote), 3265 (`prop:archimedean`), 4007-4020 (`def:derivability`, `def:soundness`), 4190-4203 (`thm:TM-soundness` + proof), 4239/4252/4260/4273/4282 (`def:BX-z`, `def:BX-d`, `def:BX-r`, `def:TMplus`, `cor:tm-completeness`)
