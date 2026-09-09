# PATH — the execution outline

**Generated** 2026-08-24 from `specs/reviews/review-2026-08-24.md`.
**Last updated** 2026-09-09, after the paper-alignment batch — **562, 571, 572, 573, 574, 575,
576, 577** — closed. The previous edition's Steps A–D are now **history**: every task it
scheduled has completed or been abandoned, and the milestone it was organized around — the
repository's last `sorry` — **has been reached**.
**Companion files**: `specs/TODO.md` (generated waves), `specs/state.json` (machine truth),
`specs/ROADMAP.md` (**rewritten 2026-08-25 by task 468; amended 2026-09-08 — now trustworthy**,
and the authority for full-programme ordering that this file does not restate),
`specs/reviews/review-2026-09-08.md` (the near-term track below is its list, re-checked).

This is a reading order, not a contract. The dependency graph in `state.json` enforces the same
ordering; if the two ever disagree, `state.json` wins and this file is stale.

---

## Where things stand

Machine baseline, verified 2026-09-09 by task 577's implement phase against the current tree:
full `scripts/check-module-invariants.sh` **exit 0, ALL CHECKS PASSED** — the range is now
**C1–C26**, not the C1–C11 of the previous edition. Both `lake build` and `lake build BimodalTest`
exit 0. **573 live `.lean` files** (518 `FormalSystem/` / 55 `Tests/`); 168 archived under
`FormalSystem/Boneyard/` and excluded.

**The tree has zero live structural sorries.** C3 asserts it by content. This is the milestone the
previous edition's Step B was organized to reach, and it was reached by a different route than the
one that edition scheduled — see below.

Four things that matter more than that number:

- **`countermodel_discrete` is proved.** At the `ℚ ×ₗ ℤ` carrier, in
  `WeakCanonical/GroupModel/CountermodelBase.lean`. `DiscreteCarrierProbe.lean` — written by 421
  purely to scout the obligation — now records it as **discharged**. All four flagship theorems
  are axiom-clean; no `sorryAx` reaches any of them.
- **The chronicle route that was going to close it was abandoned, not completed.** **422, 169 and
  95 are all `[ABANDONED]`.** They were the discrete-case chronicle, the Base-weak-completeness
  terminus, and the confirmation pass. **Tasks 477, 478 and 479 closed the obligation first**, so
  all three were retired as superseded rather than worked. **Do not resurrect them from the
  previous edition's Step B** — that table is void.
- **The decidability front closed everything except its one open obligation.** 474 (BiLasso
  wiring) and 475 (carrier normalization) both **completed**. **476 — the box-faithful small-model
  theorem — remains the sole remaining obligation**, and is explicitly deferred as open
  mathematics under the current directive. 468 delivered the programme verdict; 455 was
  **abandoned**, as it predicted.
- **A new front opened and closed inside a single day.** 562 and 571–577 — the paper-alignment
  cluster — were created and completed on 2026-09-09. The four languages `L⁻ / L / L⁺ / L⋆` now
  carry the paper's own names, and 577 abstracted the validity layer and truth clauses over a
  `PointTruth` / `TruthEnv` class pair: **77 proof bodies delegated, 0 statements changed**, with
  a toy fifth language in `Tests/` proving the extension contract works.

---

## What has settled since the 2026-08-24 edition

Each row is a fact now recorded in the tree, not a plan. The previous edition's Steps A–D are
fully resolved by these outcomes and are not restated.

| Task | Verdict |
|---|---|
| **468** | **Programme verdict issued.** `specs/ROADMAP.md` rewritten wholesale 2026-08-25 around the PROVEN vs SORRY-FREE distinction, with decidability/tableau given equal billing and every status claim grounded in a named `check-module-invariants.sh` check. Historical material was split into a `ROADMAP-ARCHIVE.md` companion, since **deleted (2026-09-09)** as a verbatim duplicate of git history — read it at `14e96488d^:specs/ROADMAP.md`. **The previous edition's "do not trust ROADMAP.md" warning is lifted.** |
| **474, 475** | Both **completed**. BiLasso is wired into the live tree and the carrier normalization landed, including the successor-based `archimedean_of_lub` analogue the previous edition flagged as the one genuine lemma. |
| **422, 169, 95** | All **abandoned as superseded** — see above. |
| **472** | **Completed.** The nine false-or-stale documentation claims are corrected. |
| **413, 425, 462, 463, 470** | All **completed**. 413 finally ran, after leaving no trace in the round before. |
| **193** | **Completed.** The soundness-layer tactic macros landed — item 6 of the 2026-09-08 near-term list. |
| **562** | The four languages renamed to the paper's `L⁻ / L / L⁺ / L⋆`. Item 1 of the near-term list; it gates seven other tasks and is now released. |
| **571–576** | The schematic/star proof-theory cluster: `DetPM` and Theorem C, tense-free stability, star proof theory and conservativity, the soundness invariant record, the L⁺ state-locality fragment, and the `ofBase` split that eliminated the `ofPlus`-restricted bridge results. |
| **577** | The validity layer and truth clauses abstracted over `class PointTruth` / `class TruthEnv`. Two new leaf modules under `FormalSystem/Semantics/`, 12 instances, 77 delegated proof bodies, **0 statements changed** — verified by a declaration-header diff against the pre-refactor commit (0 changed, 0 lost, all 242 names resolve). Four declarations *lost* an axiom (`Quot.sound`); none gained one. |

---

## The near-term track

`specs/reviews/review-2026-09-08.md` classified all 48 then-active tasks against the author's own
directive — *finish the foundations and all small results, avoiding open mathematics and long-term
efforts like decidability for now* — and wrote the resulting order into `ROADMAP.md`'s
`## Near-Term Work Plan`. That list is reproduced here **re-checked against state as of
2026-09-09**, with the two completed items struck and one correction.

| # | Task | Status now | Note |
|---|---|---|---|
| 1 | **562** | **DONE** | Released seven dependents. |
| 2 | **540** | eligible | Docstring-coverage floor: class 16.3%, lemma 55.6%, instance 57.6% against a 92.34% aggregate that hides them. |
| 3 | **542** | eligible | C17 flags 989 of 10346 declarations; the census has a known attribute-indirection blind spot, so this is triage, not deletion. |
| 4 | **506** | eligible | Typst display defects via a Playwright visual loop. Fully independent of the Lean tree. |
| 5 | **178** | eligible | Publication examples — the propositional fragment is genuinely decidable today. |
| 6 | **193** | **DONE** | |
| 7 | **568** | eligible | C3/C4 consequence relations promoted from probe to library. |
| 8 | **569** | eligible | Retarget the semantics to a total-by-construction index. **See the sequencing note below.** |
| 9 | **565** | gated on 563 | Wrappers on the already-proved Extension Theorem. |
| 10 | **566** | gated on 563, 565 | Uses the proved `FrameOver.mem_HF_iff_adjacent` hook. |
| 11 | **564** | gated on 563 | Composition step already proved as `glue_seam`. |
| 12 | **563** | eligible | The presheaf skeleton — **infrastructure the four clauses above build on**. |
| 13 | **567** | gated on 563 | Determinism clause plus the separatedness asymmetry. |
| 14 | **543** | **NOT eligible — see below** | |

**Correction to the review's list: 543 is four tasks deep, not near-term.** Its chain is
`543 → 500 → 497 → 502 → 461`. Of these only **502** is eligible today; 497 and 500 are
`not_started` behind it. The same review deferred the Jónsson–Tarski front (125, 497–502, 504)
as long-horizon — so item 14 sits *inside* a front items 1–13 exclude. Its own text already warns
that six external reports must be read before its size is known. **Treat 543 as deferred**, or
schedule `502 → 497 → 500` deliberately first, as a decision about the algebraic front rather
than as a near-term small result.

**Sequencing note — run 569 before 563–567, not alongside.** This is a judgment, not a dependency
the graph records. 569 replaces the truth index: its probe
(`553_.../probes/01_bounded-index-diagnosis.lean`) proves the current bounded-index reading is
**incoherent, not merely unused** — `refute_modal_t_at_bounded_index` shows `□p → p`, a TM axiom,
is *false* at a bounded convex index off its domain, because the atom clause is domain-relative
while the box clause re-indexes to the total `H_F`. Building the presheaf cluster on the index
that correction removes means building it twice. The graph does not encode this because
563–567 do not formally depend on 569.

**Three of these declare no `file_scope` at all** — 563, 568 and 569 have the field empty. Like
413 in the previous edition, they therefore **declare no territory and take no lock**, and the
admission gate cannot see a collision between them or with anything else. Given that 569 rewrites
the semantics index and 563 sites a new cluster below `Truth.lean`, that is worth fixing before
they run concurrently.

**540 and 542 collide with each other and with almost everything.** Both declare `FormalSystem/`
*and* `scripts/check-module-invariants.sh`. The directory-level scope makes them overlap every
Lean task in this list. Run them **sequentially, and on their own** — the gate will defer them
into separate waves anyway, and that is correct behavior, not a fault.

---

## Deferred fronts

Excluded by the author's standing directive, not by lack of readiness. `ROADMAP.md`'s
`## Recommended Priority Order` holds the full-programme resumption plan for when the directive
lifts; it is not restated here.

| Front | Tasks | Why deferred |
|---|---|---|
| Decidability / tableau spine | 410, 411, 412, 428, 429, 430, 464, 465, 481, 482 | The largest open front; several tasks self-labeled open mathematics. 468 ruled on it — consult ROADMAP.md, not the previous edition of this file. |
| Semantic finite model property | **476** | The single remaining obligation for decidability of `ValidDiscrete`. Explicitly OPEN MATHEMATICS, multi-month, and gated behind a literature check (GKWZ 2003, temporal-products chapter) **empowered to refute it outright**. |
| TM⋆ completeness / non-definability | 537 (done), 559, 560, 561 (done) | 559 is a verdict-first research task — report and probes only, no `FormalSystem/` changes. |
| H/G-fragment finite axiomatizability | 534 | Open research question; Kamp/Burgess territory. |
| C3 completeness question | 570 | Explicitly an open research question, not an implementation task. Gated on 568. |
| Jønsson–Tarski algebraic representation | 125, 497, 498, 499, 500, 501, 502, 504 | Capstone plus five-phase groundwork. **502 is the eligible head**; 543 hangs off its far end. |
| Object-language extensions | 127, 128 | ROADMAP's own note recommends ABANDON or park. |
| Documentation final-polish | 177 | Gated on the deferred decidability chain landing. |
| Dataset cluster | 298, 296, 282, 257, 231, 219 | Independent, non-mathematical, small and bounded. **298 is `partial` and eligible, and alone gates 231, 282 and 296** — a live data-integrity defect (`data/bmlogic-c7.jsonl` holds 13,749 records against metadata advertising 77,272) that git cannot see, because `data/` is gitignored. 257 is blocked on *you*: an HF account, org and write token. |

---

## Decisions that are yours, not an agent's

| | |
|---|---|
| **The open-mathematics directive** | Standing since 2026-09-08 and the organizing constraint of this whole edition. Lifting it re-opens 476 and the tableau spine; leaving it in place means the near-term track above is the whole board. Say which. |
| **127, 128** | Still recommended **abandon or park explicitly**. Both extend the object language, multiplying the constructor rule set. Both are dependency-eligible and will keep surfacing as candidates until dispositioned. |
| **543 and the algebraic front** | Either deliberately schedule `502 → 497 → 500 → 543`, or mark 543 deferred so it stops appearing on a near-term list it does not fit. |
| **177's `file_scope`** | It declares `README.md`, `specs/ROADMAP.md`, `FormalSystem/` and `docs/` — coarse enough to raise an idle-overlap advisory against nearly every Lean task. One fired against 577 in this session. Narrow it, or keep ignoring the advisories. |
| **219** | Still `researched` and gated on 231. The previous edition recommended **abandon**: no `data/baselines/`, needs paid runs against now-stale models, no relation to the formalization programme. Unchanged and undispositioned. |
| **The two follow-ups 577 named** | **No task owns either.** (a) The consequence layer and `Metalogic/Deterministic/Validity.lean` adapters, left outside 577's stated territory; (b) `CTruth.*` in `CoarsenedModels.lean` — a **fifth clause-family duplicate the research survey never listed**. Both are now cheap, because 577 built the class layer they would instantiate. File them, or lose the finding. |

---

## Reading the graph yourself

```bash
scripts/check-module-invariants.sh                    # the machine baseline, C1–C26
sed -n '/Dependency Waves/,/^$/p' specs/TODO.md       # current waves
/orchestrate 569,563,568,506 --dry-run                # admission verdicts, read-only
jq -r '.active_projects[] | "\(.project_number) \(.status) deps=\((.dependencies//[])|join(","))"' \
  specs/state.json | sort -n
```

**`orchestrate-dry-run-report.sh` no longer exists** — the previous edition's command is dead.
`/orchestrate ... --dry-run` runs the identical read-only decision pass a live cycle uses, so its
verdicts match what a live run would actually dispatch.

Dependency targets that resolve in **neither** `state.json` nor `archive/state.json` are the only
real dangling edges. **Any lint must union both files, and must read the archive's own keys** —
`specs/archive/state.json` has `archived_projects` and `completed_projects`, **not**
`active_projects`. A union scan that assumes the live file's shape silently returns an empty
archive and reports every archived predecessor as missing. The pre-dispatch review's Class A scan
has exactly this blind spot: it reports archived predecessors as `nonexistent`. **They are not.
Do not "repair" them.**

---

## Cross-repository hazard: tasks whose work lands outside this repo

Unchanged, and still worth re-reading before any `.claude/` edit. `.claude/` here is
**gitignored** and regenerated wholesale on an agent-system reload; `agent-system/` **does not
exist** in this repository — the source store is `/home/benjamin/.config/nvim/agent-system/`, a
separate git repo with its own task tracker. **Anything written to `.claude/` here is destroyed on
the next reload.**

Nothing in the near-term track above is at risk: all of it writes `FormalSystem/`, `Tests/`,
`typst/`, `docs/` or `scripts/` — all tracked.

---

## The next batch — what to orchestrate now

`MAX_TASKS` is 8, but the binding constraint here is collision, not count. Four sequential
batches, in this order:

```
/orchestrate 569,506            # the index correction, plus one fully independent task
/orchestrate 563,568            # presheaf skeleton + consequence relations, on the corrected index
/orchestrate 564,565,566,567    # the four dictionary clauses, all released by 563
/orchestrate 540                # then, separately, /orchestrate 542
```

| Task | Why it is where it is |
|---|---|
| **569** | Goes first because it corrects the truth index everything else in this cluster sits on, and the incoherence it fixes is machine-checked, not suspected. Running it after 563–567 means rebuilding them. |
| **506** | Rides along with anything: it touches `typst/` only and cannot collide with a Lean task. |
| **563** | Infrastructure for 564–567, and the review's own recommendation is to run the cluster as one connected pass rather than seven dispatches. |
| **568** | Independent of 563 by the graph, small, and promotes an already-proved probe. Pairs cleanly. |
| **564, 565, 566, 567** | All released the moment 563 lands. Each is a wrapper or an assembly over something already proved — `glue_seam`, `thm:extension`, `FrameOver.mem_HF_iff_adjacent`, `StarDeterminism.states_eq_of_deterministic`. This is the highest ratio of result to risk on the board. |
| **540, 542** | Last, and separately: both declare `FormalSystem/` plus `scripts/check-module-invariants.sh`, so they collide with each other and with every Lean task above. Neither blocks anything. |

**Before the first batch**: give 563, 568 and 569 a real `file_scope`. They currently declare
none, so the admission gate cannot serialize them against each other, and 569 rewrites the
semantics index that 563 would site a new cluster beneath.

**Not in these batches, and why**: 178 (wait for the semantics index to settle — its examples are
publication-facing and would be written twice); 502 (eligible, but it is the head of the deferred
algebraic front — a scheduling decision, not a near-term small result); 298 (eligible, `partial`,
and the sole gate on three others — worth a batch of its own whenever the dataset track is picked
up, independent of everything above).
