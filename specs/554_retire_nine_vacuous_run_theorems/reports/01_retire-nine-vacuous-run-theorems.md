# Research Report: Task #554

**Task**: 554 - Retire the nine vacuous `_run` theorems in `MintBound.lean`, land the two un-`At` widening lemmas, and amend C9 register entries 24/25 for the corrected count
**Started**: 2026-09-07T00:00:00Z
**Completed**: 2026-09-07T00:00:00Z
**Effort**: ~0.5 hours
**Dependencies**: None outstanding (463 complete, 549 complete)
**Sources/Inputs**: - `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md` (Section 4 delete/keep set, consumed not re-derived); `specs/549_.../probes/{Widen,RevDep,DepTrace2}.lean` (re-run at HEAD); `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean`; `FormalSystem/Metalogic/Decidability/Correctness.lean:192-234`; `docs/architecture/ADR-007-Decidability-One-Directional.md`; `docs/theorem-index.md:109-114`; `.claude/context/project/lean4/operations/long-builds.md`
**Artifacts**: - `specs/554_retire_nine_vacuous_run_theorems/reports/01_retire-nine-vacuous-run-theorems.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **Every delete-set line number from the 549 summary holds unchanged at HEAD `e5cb311af`.** The
  nine theorems sit at `12312, 12331, 12347, 12369, 12386, 12407, 12425, 12449, 12468`; the block
  prose opens at `:12288` and the last proof line is `:12487`. The delete span is one contiguous
  200-line region, `:12288-12487`, with blank lines either side. No re-location by name was needed
  beyond confirmation, but the names — not the numbers — are what the implementer should anchor on.
- **The deletion cannot break the build.** The four internal cross-references among the nine
  (`:12341`, `:12364`, `:12403`, `:12443`, `:12486`) all live inside the delete span. Every
  reference from outside the span is prose inside a `/-- … -/` docstring or a `/-! … -/` section
  comment, which Lean does not resolve. Zero reverse-dependents was re-confirmed by machine at HEAD.
- **The 549 summary's delete set is complete, but its *amend* set is not.** Section 4 names one
  rewrite site (`:5194-5195`). Research found **six** prose sites outside the delete span that go
  stale or false on deletion — three of them (`:12172-12173`, `:12208`, `:12939`) unenumerated
  anywhere in the prior artifacts. Section "Findings > Codebase Patterns" enumerates all six.
- **The two widening lemmas compile clean at HEAD** (`lake env lean` on `probes/Widen.lean`, exit 0,
  axioms `[propext, Classical.choice, Quot.sound]`) — but they **cannot be pasted verbatim**:
  `MintBound.lean` opens only `FormalSystem.Syntax`, never `FormalSystem.ProofSystem`, so
  `FrameClass.Base` must become `FormalSystem.ProofSystem.FrameClass.Base` on landing.
- **Recommended approach: retire with a retirement record, following this repository's own
  established house pattern** — `Correctness.lean:192`'s "`validity_decidable` /
  `validity_has_decision_procedure` — Retired as vacuous" section, sanctioned by ADR-007. This
  dissolves the delete-vs-annotate tension the dispatch flags rather than trading one defect for
  another. No `user_decision` is raised: the codebase already answers the question.
- **Zero-debt outlook is clean.** The task's entire proof content is two already-kernel-checked
  six-line lemmas. There is no new proof obligation anywhere in scope, hence no route by which a
  `sorry` or an axiom could be tempted. Repo baseline re-verified: 0 real `sorry` outside
  `Boneyard/`, 0 real `axiom` declarations in `FormalSystem/`.

## Context & Scope

Research for the retirement of nine vacuous `buildTableauAt_isSome_*_run` theorems in a
15,759-line file, plus two register amendments and a count correction. The disposition (RETIRE)
and the delete/keep boundary were **decided** by the prior dependency trace and are consumed here,
not re-derived, per the dispatch's explicit instruction. What this research adds is:

1. Re-verification of every load-bearing figure at current HEAD (line numbers, name resolution,
   the two regression probes, the widening lemmas' axioms).
2. A **complete edit-site inventory** — the prior artifacts under-enumerate the collateral prose.
3. Mechanical hazards the implementer would otherwise hit (namespace, name collision, a second
   unrelated "nine" in the same file).
4. A landing design for the retirement that satisfies the publication criterion without discarding
   the record, grounded in an existing in-repo precedent.

Explicitly out of scope and confirmed untouched-by-design: the `.ZTime` strengthening,
`docs/theorem-index.md:113`, and any decomposition of `MintBound.lean`.

## Findings

### Codebase Patterns

#### F1. The delete span, verified at HEAD `e5cb311af`

One contiguous region, `MintBound.lean:12288-12487` (200 lines), covering both items of the
summary's delete set with no gap:

| Range | Content |
|-------|---------|
| `12288-12309` | `/-! #### The termini, restated at the narrowed residual … -/` block prose |
| `12310` | blank |
| `12311-12487` | the nine theorems with their docstrings |

Bounded above by two blank lines at `12286-12287` (after the previous proof) and below by two at
`12488-12489` (before `/-! #### Non-vacuity of the narrowed residual`, `:12490`). Collapse to a
single blank-line pair on deletion.

The nine, at their verified declaration lines, with the fuel figure and refuted hypothesis each
carries:

| # | Name | Line | Fuel figure | Refuted hypothesis | Vacuity established at |
|---|------|------|-------------|--------------------|------------------------|
| 1 | `buildTableauAt_isSome_of_budget_run` | 12312 | `mintAwareFuel` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 2 | `buildTableauAt_isSome_of_budget_of_run` | 12331 | `mintAwareFuel` | **`PostBlockingSettles`** | **all four classes** |
| 3 | `buildTableauAt_isSome_at_seed_run` | 12347 | `mintAwareFuel` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 4 | `buildTableauAt_isSome_of_budget_at_run` | 12369 | `mintAwareFuel` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 5 | `buildTableauAt_isSome_at_seed_at_run` | 12386 | `mintAwareFuelAt` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 6 | `buildTableauAt_isSome_of_budget_selfGuarded_run` | 12407 | `mintAwareFuelAt` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 7 | `buildTableauAt_isSome_at_seed_selfGuarded_run` | 12425 | `mintAwareFuelAt` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 8 | `buildTableauAt_isSome_of_budget_fixed_run` (terminus) | 12449 | `mintAwareFuelAt` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |
| 9 | `buildTableauAt_isSome_at_seed_fixed_run` | 12468 | `mintAwareFuelAt` | `PostBlockingSettlesRun` | `.Base`, `.Dense`, `.RTime` |

Rows 1 and 3-9 are **undecided but equally undelivering, with zero dependents**, at `.ZTime`. Row 2
alone is unconditionally vacuous at all four. The dispatch's precision requirement is reproduced
here verbatim so the implementer does not have to travel back to the 549 summary for it.

#### F2. The deletion is closed under name resolution — it cannot break elaboration

Every use of the nine, repo-wide (excluding `specs/**`), is in `MintBound.lean`. Inside the file:

- **Inside the delete span** (removed with it): `:12341`, `:12364` (`_of_budget_run`), `:12403`
  (`_of_budget_at_run`), `:12443` (`_of_budget_selfGuarded_run`), `:12486` (`_of_budget_fixed_run`).
- **Outside the delete span**: `:5194`, `:5195`, `:12740`, `:12935` — **all four are prose inside a
  docstring or section comment**. Lean performs no name resolution on docstring backticks, so none
  of them is a compile obligation. They are correctness obligations for the reader, not the kernel.

No file under `docs/`, `Tests/`, or elsewhere in `FormalSystem/` mentions any of the nine.

#### F3. Complete edit-site inventory (the prior artifacts enumerate only site A)

Six prose sites outside the delete span go stale, false, or under-counted on deletion. Sites B, C
and E are **not named in the 549 summary, the 549 report, or the dispatch**.

| Site | Line(s) | Current text (abridged) | Why it must change |
|------|---------|-------------------------|--------------------|
| **A** | `5194-5195` | "`buildTableauAt_isSome_of_budget_run` and its siblings are the termini stated at it, and `buildTableauAt_isSome_of_budget_of_run` certifies the strengthening" | Names two deleted theorems. **Rewrite, do not excise** — the surrounding sentence about `postBlockingSettlesRun_of_postBlockingSettles` fixing the direction stays true and is worth keeping. (This is the one site Section 4 names.) |
| **B** | `12172-12173` | "the landed termini are untouched, and **the restatements below** are additive siblings carrying `ArmSettlement` … together with the narrowed residual" | *New.* Inside the `PostBlockingSettles` §C12 intro prose. After deletion there are no restatements below. The sentence becomes a forward reference to nothing. |
| **C** | `12208` | "it is a **false** hypothesis at those three classes, so **the termini carrying it** are vacuous there" | *New.* Inside the `PostBlockingSettlesRun` docstring. Historically true; after deletion no terminus in the file carries it. Needs past-tense/retirement-pointer phrasing. |
| **D** | `12740-12741` | "`buildTableauAt_isSome_of_budget_fixed_run` and **its five `_run` siblings** carry `PostBlockingSettlesRun fc (mintAwareFuelAt …)`" | Names a deleted theorem **and** carries the six-count undercount. This is the primary target of scope item 5. Note it also says `mintAwareFuelAt` only — amendment (a) widens it. |
| **E** | `12939` | "This is the representative restatement, not the family: **the other five `_run` termini are left as they stand**, and widening to them is deliberately deferred rather than forgotten." | *New, and the highest-risk omission.* This sits in the docstring of `buildTableauAt_isSome_of_budget_fixed_seedRun` — an explicit **KEEP**-set item. After deletion the sentence is flatly false (nothing is left standing) and it under-counts. Missing this leaves a false statement inside a surviving headline theorem. |
| **F** | `15649-15652` | C9 entry 23: "The narrowed residual covers only the second, so **the restated termini name `ArmSettlement`** instead of manufacturing it from a refuted predicate." | Present-tense description of the deleted block, inside the register. |

#### F4. Orphaned-but-kept declarations (no build impact; docstring notes warranted)

Lean emits no warning for an unused theorem, so none of these breaks the build. They are
readability obligations:

| Declaration | Line | Consumers before | Consumers after |
|-------------|------|------------------|-----------------|
| `buildTableauAt_isSome_of_settlesRun` (the bridge) | 12260 | 4 (`:12323`, `:12380`, `:12419`, `:12461`) | **0** |
| `postBlockingSettlesRun_of_postBlockingSettles` | 12228 | 1 (`:12343`) | **0** |
| `armSettlement_of_postBlockingSettles` | 5210 | 5 | 4 (`:5296`, `:6353`, `:10014`, `:11004`) — unaffected |
| `postBlockingSettlesRun_zero` | 12249 | 0 (prose only) | 0 — unaffected |

Both zero-consumer survivors are named by C9 entry 23 (`:15639`, `:15644`) and by prose at `:5192`
and `:12891`, so both are correctly in the keep set. A one-clause docstring note ("retained as the
record of the narrowing; its consumers were retired — see the retirement record at §C12") keeps
them legible.

#### F5. In-repo precedent: this project already has a house pattern for retiring vacuous theorems

`FormalSystem/Metalogic/Decidability/Correctness.lean:192-234` carries a section headed
"`validity_decidable` / `validity_has_decision_procedure` — Retired as vacuous". Two theorems were
**deleted**; a prose section stands in their place and states, in order: what stood there, why the
names claimed more than the proofs contained, what actually holds and is proved, what has since
landed, and what is still owed. `docs/architecture/ADR-007-Decidability-One-Directional.md:51-53`
sanctions the shape and adds the discipline that the record lives **once**, with pointers rather
than copies elsewhere. Four further surfaces point at it (`Decidability.lean:151`,
`Decidability/README.md:18`, `Verified/README.md:68`, `Correctness.lean:25`).

The register itself states the same principle in its own voice at C9 entry 24: the superseded
clause "is corrected rather than deleted so the sequence of findings stays legible."

#### F6. Namespace hazard on landing the widening lemmas — verbatim paste will not compile

`MintBound.lean` declares `namespace FormalSystem.Metalogic.Decidability` (`:57`) and opens
**only** `FormalSystem.Syntax` (`:59`). It never opens `FormalSystem.ProofSystem`. `probes/Widen.lean`
does open it, and therefore writes the bare `FrameClass.Base`.

Consequences for landing:

- `postBlockingSettlesRun_mintAwareFuel_false`'s `FrameClass.Base` must be written
  `FormalSystem.ProofSystem.FrameClass.Base`, matching its sibling
  `postBlockingSettlesRun_terminusFuel_false` (`:12753`) exactly.
- This is not hypothetical fussiness: the file already carries a scar from precisely this class of
  bug, recorded in a comment at `:12980-12982` — "inside this namespace the `.Dense` shorthand
  resolves elsewhere, and the probe silently reported an unexpanded run until the names were
  qualified." That failure was **silent**, not a compile error.
- `one_le_mintAwareFuel'` needs no qualification (all-`Nat` signature).

#### F7. Landing site and naming for the widening lemmas

The two lemmas' dependencies (`fuelFigure_pos` `:3688`, `mintPathBound` `:4976`, `mintAwareFuel`
`:4983`, `postBlockingSettlesRun_false_succ` `:12722`) are all in scope by `:12730`. The natural
sites, which put each lemma beside its `At`-sibling:

- `one_le_mintAwareFuel` immediately after `one_le_mintAwareFuelAt` (`:12730-12732`).
- `postBlockingSettlesRun_mintAwareFuel_false` immediately after
  `postBlockingSettlesRun_terminusFuel_false` (`:12750-12759`).

**Naming**: `probes/Widen.lean` calls the first `one_le_mintAwareFuel'`. In Lean/Mathlib a primed
name conventionally marks a *variant of* an unprimed original; here the un-`At` figure is the
**primary** one and `mintAwareFuelAt` is the derived variant, so the prime reads backwards. There
is no `one_le_mintAwareFuel` in `FormalSystem/` to collide with (verified). Recommend landing it
as **`one_le_mintAwareFuel`**, unprimed, symmetric with `one_le_mintAwareFuelAt`. Zero references
to the primed name exist outside the probe file, so the rename is free.

#### F8. Collision hazard — there is a *second, unrelated* "nine" in this file

`MintBound.lean:14282` and C9 entry 21 at `:15388` both say "**the nine** `hlab` carriers" — nine
statements carrying `hlab : UnorderedSuccessorLabelClosed fc L`, vacuous at every nonempty `L` by
`unorderedSuccessorLabelClosed_nonempty_false`. That set is **disjoint** from this task's nine
(none of the nine `_run` theorems takes an `hlab` argument) and is entirely out of scope. A
count-correction pass driven by grepping for "nine" or "vacuous" will hit these; they must not be
edited.

Similarly out of scope, verified as false positives for the count correction: "the six restated
termini" (`:15350`) and "the two seed-level termini" (`:15316`) refer to the
`MintPaysForTimeStable`/`_at` chain, not to the `_run` block; the generic "`PostBlockingSettles` or
`PostBlockingSettlesRun`"-carrying termini clauses at `:14286` and `:15391` stay true after
deletion (the landed `PostBlockingSettles` termini survive) and need no edit.

### External Resources

No Mathlib search was warranted and none was performed: the task introduces no new mathematical
content. The two lemmas to be landed are already proved, and every other operation is a deletion or
a prose edit. `lean_leansearch` / `lean_loogle` / `lean_leanfinder` were deliberately not called —
spending a rate-limited budget searching for lemmas that are not needed would be noise, not rigor.
The lean-lsp verification that *was* useful (name resolution, axiom check, environment closure) was
obtained more directly and more cheaply by re-running the prior task's committed probe scripts under
`lake env lean` against warm oleans (~15s each).

### Recommendations

#### R1. Retire with a retirement record (the primary recommendation)

Replace `:12288-12487` with a `/-! #### The termini restated at the narrowed residual — retired as
vacuous -/` section modelled on `Correctness.lean:192`. It should state, in that order:

1. **What stood here**: the nine, named in full, so the names remain greppable in-file and a reader
   arriving from `git log` or from an external citation finds them.
2. **Why they were vacuous**: each carried `PostBlockingSettlesRun` (or, for
   `buildTableauAt_isSome_of_budget_of_run`, the unrestricted `PostBlockingSettles`) at a fuel
   figure at which that predicate is refuted, naming
   `postBlockingSettlesRun_terminusFuel_false` / `postBlockingSettlesRun_mintAwareFuel_false` /
   `postBlockingSettles_fuel_zero_false` as the refutations.
3. **The frame-class split, unflattened**: rows 1 and 3-9 established vacuous at `.Base`, `.Dense`,
   `.RTime`, and undecided-but-equally-undelivering at `.ZTime`; row 2 unconditionally vacuous at
   all four.
4. **What survives and why**: `PostBlockingSettlesRun` itself, the refutation apparatus, the bridge,
   and the `PostBlockingSettlesSeedRun` successor line.
5. **Cost of removal**: zero reverse-dependents, machine-verified.

**Why this and not a silent deletion.** The dispatch frames the choice as retire-vs-annotate and
flags that a human may prefer to make it. Research finds the codebase has already made an
equivalent call, twice-documented (F5): delete the *theorem*, keep the *record*. That satisfies the
publication criterion the dispatch names — a reader no longer meets nine headline-shaped results
that deliver nothing — while satisfying the register's own stated principle that the sequence of
findings stay legible. Section 7's annotate-in-place fallback remains strictly worse on the
publication criterion; a silent deletion is worse on legibility. This third shape dominates both,
and it is the repository's convention rather than a novel invention, so no `user_decision` is
raised.

**Cost**: roughly 25-35 lines of prose replacing 200 lines of prose-plus-theorem. Net removal of
~165 lines and, critically, of nine declarations from the library's public surface.

#### R2. Execute the six prose edits of F3 as a distinct, checkable objective

Sites B, C and E in particular are easy to miss because nothing in the prior artifacts names them.
Recommend the plan give them their own phase objective with a mechanical exit check:

```
grep -n "buildTableauAt_isSome_of_budget_run\|buildTableauAt_isSome_of_budget_of_run\|\
buildTableauAt_isSome_at_seed_run\|buildTableauAt_isSome_of_budget_at_run\|\
buildTableauAt_isSome_at_seed_at_run\|buildTableauAt_isSome_of_budget_selfGuarded_run\|\
buildTableauAt_isSome_at_seed_selfGuarded_run\|buildTableauAt_isSome_of_budget_fixed_run\|\
buildTableauAt_isSome_at_seed_fixed_run" FormalSystem/.../MintBound.lean
```

After the edits, every surviving hit must be inside the new retirement record of R1 (which names
them deliberately) — nowhere else.

And for the count correction, `grep -n "five \`_run\`" MintBound.lean` must return empty, with the
`grep -n "\bnine\b"` hits confined to the retirement record, the amended C9 entries, and the two
pre-existing `hlab`-carrier sites of F8.

#### R3. Land the widening as two lemmas, qualified, unprimed, beside their `At`-siblings

Per F6 and F7. Verified compilable at HEAD; no proof work required, only relocation and
qualification. Recommend the implementer *not* re-derive the proofs — they are byte-for-byte
transplants apart from the `FrameClass` qualification and the name.

**Optional and NOT recommended for this task**: `.Dense` and `.RTime` refutations at the un-`At`
figure are each a four-line composition of `postBlockingSettlesRun_false_dense` / `_rtime` (`:12821`,
`:12827`) with `one_le_mintAwareFuel`. The dispatch asks for two lemmas, the deleted theorems no
longer need them, and adding them is scope creep. Named here only so a reader does not mistake
their absence for an oversight.

#### R4. Register amendments — the exact target sentences

- **Amendment (a)**, entry 25 at `:15696`: the sentence "that figure is always at least one
  (`one_le_mintAwareFuelAt`, off `mintPathBound`'s trailing `+ 1` through `fuelFigure_pos`)" is
  where the un-`At` figure joins. Both figures now have positivity lemmas; both are refuted at
  `.Base`. The claim widens from `mintAwareFuelAt` to *both* fuel figures the retired block used.
  The corresponding sentence at `:12740-12741` (site D) must move in step or the file contradicts
  its own register.
- **Amendment (b)**, entry 25's closing `.ZTime` paragraph at `:15749-15757`: it currently reads as
  a uniform caveat over the whole block. Row 2 must be split out — refuted by
  `postBlockingSettles_fuel_zero_false` at all four classes, hence outside the `.ZTime` caveat
  entirely.
- **Entry 24** at `:15661`: update the count (nine, not six) and re-point its description of the
  restated termini to the retirement record rather than to live theorems.
- **Entry 23** at `:15649-15652` (site F): present tense to past.
- **Entry 22 stays untouched.** It is about `PostBlockingSettles` as literally stated; nothing in
  this task changes it.

#### R5. Verification, in the order that makes failures cheap

1. `lake env lean` on the two widening lemmas *in situ* is not available (they are inside a
   15k-line file), so verification is the full build. Run it **detached and guarded**, exactly as
   `.claude/context/project/lean4/operations/long-builds.md` mandates:
   `Bash(run_in_background: true)` on
   `bash .claude/scripts/lake-build-guard.sh build --timeout 1800 -- <lake args>`. A foreground
   `lake build` on this repository will livelock, not merely time out.
2. `lake env lean specs/549_.../probes/DepTrace2.lean` must still report
   `constants from MintBound reached by decide: 0`. This is the **meaningful** regression check.
3. `probes/RevDep.lean` will report 0 trivially once the names stop resolving, and worse — it will
   `logError` on unresolved names. Expect it to fail loudly rather than to pass; that failure is the
   *expected* outcome, not a regression. Do not treat it as evidence either way.
4. `#print axioms` unchanged for surviving `Decidability` results: `MainResults.lean` already emits
   these as build-time obligations, so a green build is the check.
5. `grep` gates of R2.

#### R6. Zero-debt compliance

There is no approach under consideration that could require a `sorry`, and none is recommended. The
entire proof surface of this task is two lemmas that are already kernel-checked at
`[propext, Classical.choice, Quot.sound]`. No axiom is added. If a `sorry` appears during
implementation it indicates the implementer attempted something outside this task's scope — most
likely the explicitly-excluded `.ZTime` strengthening — and the correct response is to stop and
re-read the dispatch's OUT OF SCOPE section, not to defer the `sorry`.

## Decisions

- **Consume the 549 summary's Section 4 delete/keep set rather than re-deriving it**, per the
  dispatch's explicit instruction. Research verified it at HEAD instead of re-litigating it; every
  figure held.
- **Extend the amend set from one site to six** (F3). The delete set was complete; the collateral
  prose inventory was not. Site E in particular puts a false sentence inside a surviving keep-set
  theorem's docstring, which is exactly the class of defect this task exists to remove.
- **Recommend retirement-with-a-record over both silent deletion and Section 7's
  annotate-in-place** (R1, F5). Grounded in `Correctness.lean:192` and ADR-007, both in this
  repository. Recorded as a research decision, not escalated as a `user_decision`: the
  user-decision contract excludes choices the existing codebase already answers, and this one is
  answered twice over.
- **Recommend renaming `one_le_mintAwareFuel'` to `one_le_mintAwareFuel` on landing** (F7). Low
  risk (zero external references), and the prime reads backwards for the primary figure. An
  implementer who prefers to preserve the probe file's name verbatim may keep the prime; nothing
  else depends on the choice.
- **No Mathlib search performed**, deliberately (see "External Resources"). Recorded so its absence
  is not read as an omission.
- **No `.Dense`/`.RTime` un-`At` variants recommended** (R3), as scope creep against a dispatch that
  names exactly two lemmas.

## Risks & Mitigations

| Risk | Severity | Mitigation |
|------|----------|------------|
| Line numbers drift between this report and implementation (the 549 trace found research line numbers stale once already) | Medium | Every site in F3 and F4 is given by **name and quoted text**, not only by number. Re-locate by the quoted string. |
| Site E (`:12939`) missed, leaving a false sentence in a surviving theorem's docstring | High | Called out as the highest-risk omission; R2 supplies a `grep` gate that catches it mechanically. |
| Verbatim paste of `Widen.lean` fails, or worse, resolves to a different `FrameClass` silently | Medium-High | F6; qualify to `FormalSystem.ProofSystem.FrameClass.Base`. The file already documents one silent instance of this exact bug at `:12980`. |
| Count-correction pass edits the unrelated "nine `hlab` carriers" (`:14282`, `:15388`) | Medium | F8 names both sites as out of scope, plus the three further false positives at `:15316`, `:15350`, `:14286`/`:15391`. |
| Foreground `lake build` livelocks the implementation phase | High | R5.1 — detached + guarded is mandatory, not advisory, on this repository. |
| `RevDep.lean` re-run interpreted as a regression failure | Low | R5.3 — its failure is the expected outcome once the names stop resolving; `DepTrace2.lean` is the real check. |
| The nine's names vanish from the file entirely, breaking future citations from external artifacts (`specs/433_*`, `specs/463_*`, `specs/549_*` all cite them by name) | Medium | R1 keeps all nine names greppable inside the retirement record. |
| Concurrent write collision on `MintBound.lean` | None currently | `state.json` checked: 463 and 549 are `completed`; the only in-flight task (547, `implementing`) has a 21-path `file_scope` with no overlap on this file. |

## Tactic Survey Results

A tactic survey was performed and found no goal to survey against. The task's entire proof content
is two lemmas that are already proved, kernel-checked, and axiom-clean; every other operation is a
deletion or a prose edit. There is no open goal in scope for `lean_multi_attempt`,
`lean_state_search`, or `lean_hammer_premise`, and invoking them would produce noise rather than
findings.

| Goal | Tactic | Result | Premises/Config |
|------|--------|--------|-----------------|
| `1 ≤ mintAwareFuel Ucard Tmax mintBudget D β` | `fuelFigure_pos (by simp only [mintPathBound]; omega)` | **success** — already landed in `probes/Widen.lean`, re-verified at HEAD `e5cb311af`, exit 0 | `fuelFigure_pos`, `mintPathBound`; axioms `[propext, Classical.choice, Quot.sound]` |
| `¬ PostBlockingSettlesRun .Base (mintAwareFuel U.card Tmax mintBudget D β)` | `obtain … Nat.exists_eq_succ_of_ne_zero` + `rw` + `exact postBlockingSettlesRun_false_succ n` | **success** — same provenance and verification | `Nat.exists_eq_succ_of_ne_zero`, `Nat.one_le_iff_ne_zero`, `one_le_mintAwareFuel`, `postBlockingSettlesRun_false_succ`; axioms `pcq` |

## Context Extension Recommendations

- **Topic**: Retiring vacuous theorems from a publication-facing Lean library.
- **Gap**: This repository has developed a distinctive, twice-documented pattern — delete the
  declaration, leave a named "Retired as vacuous" prose record stating what stood there, why it was
  vacuous, what actually holds, and what is still owed (`Correctness.lean:192`, sanctioned by
  ADR-007). It is currently discoverable only by stumbling on the one instance. Task 549's
  disposition analysis had to reason the retire-vs-annotate question out from first principles, and
  this report had to rediscover the precedent independently.
- **Recommendation**: Add `agent-system/extensions/lean/context/project/lean4/patterns/retiring-vacuous-theorems.md`
  to the **source store** (never `.claude/**` directly — see `.claude/rules/source-store-deploy-boundary.md`),
  capturing the record's five-part shape, the "record lives once, everything else points at it"
  discipline from ADR-007, and the deletion-safety checklist this report used (reverse-dependency
  scan; closure of internal cross-references; docstring references are not compile obligations;
  orphaned-but-kept declarations).
- **Related, already proposed**: task 549's Brief B (a dependency-tracing recipe at
  `.../patterns/dependency-tracing.md`) is a natural companion — the reverse-dependency scan is the
  first step of the retirement checklist above. Neither is a blocker for this task.

## Appendix

### Commands run (all at HEAD `e5cb311af`, warm oleans)

| Command | Result |
|---------|--------|
| `lake env lean specs/549_.../probes/Widen.lean` | exit 0; `postBlockingSettlesRun_mintAwareFuel_false depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `lake env lean specs/549_.../probes/RevDep.lean` | exit 0; `direct reverse-dependents across the whole FormalSystem env: 0` |
| `lake env lean specs/549_.../probes/DepTrace2.lean` | exit 0; `constants from MintBound reached by decide: 0`; `decide reaches buildTableauAt? false`; `mintAwareFuel? false`; `mintAwareFuelAt? false`; module idx `DecisionProcedure 3724 < MintBound 3755` |
| Repo-wide grep for each of the nine names, `specs/**` excluded | hits only in `MintBound.lean` |
| `grep -rnE "^axiom [A-Za-z]" FormalSystem/` | 8 hits, all wrapped prose lines beginning with the word "axiom"; **0 real axiom declarations** |
| `grep -rn "\bsorry\b" FormalSystem/` minus `Boneyard/` | 331 hits, **0** in tactic or term position (all backticked prose, `sorry-free` claims, and section titles) |
| `jq` over `specs/state.json` | 463 `completed`, 549 `completed`, 547 `implementing` with no `MintBound.lean` in its `file_scope` |

### References

- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/summaries/01_decide-dependency-verdict-disposition-summary.md` §1-§7
- `specs/549_trace_decide_dependency_on_vacuous_run_theorems/probes/{Widen,RevDep,DepTrace2}.lean`, `probes/probe-evidence.md`
- `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` — `:57`, `:59`, `:3688`, `:4976`, `:4983`, `:5190-5195`, `:5210`, `:11636`, `:12172-12213`, `:12228`, `:12249`, `:12260`, `:12288-12487`, `:12490-12533`, `:12696`, `:12722`, `:12730`, `:12740-12759`, `:12821`, `:12827`, `:12897`, `:12935-12939`, `:12980-12982`, `:14282`, `:15551`, `:15649-15652`, `:15661`, `:15692-15757`
- `FormalSystem/Metalogic/Decidability/Correctness.lean:25`, `:192-234`
- `docs/architecture/ADR-007-Decidability-One-Directional.md:36-66`
- `docs/theorem-index.md:109-114` (confirmed unchanged; out of scope by mandate)
- `.claude/context/project/lean4/operations/long-builds.md`
- `.claude/rules/source-store-deploy-boundary.md`
- `.claude/context/standards/user-decision-contract.md`
