# Implementation Plan: Algebraic/ Modernisation (propDecide, Mathlib Filters)

- **Task**: 528 - Algebraic/ modernisation: `propDecide` in `BooleanStructure.lean`,
  `SetMaximalConsistent.ultrafilterEquiv` as a named `Equiv`, the bespoke `Ultrafilter` structure
  reconciled with Mathlib's `Order.Ideal`/`IsMaximal`, `fold_le_of_derives` over `Multiset.inf`
- **Status**: [NOT STARTED]
- **Effort**: 12 hours
- **Dependencies**: 518, 526 (both landed)
- **Research Inputs**: `specs/528_algebraic_modernisation_propdecide_mathlib_filters/reports/01_algebraic-modernisation-verification.md`
- **Artifacts**: plans/01_algebraic-modernisation-propdecide-mathlib.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

`FormalSystem/Metalogic/Algebraic/` carries ~430 lines of hand-built Boolean-algebra derivations
and a bespoke `Ultrafilter` structure that shadows Mathlib's. Tasks 497 and 125 (the
Jonsson-Tarski representation front) build directly on this layer and would otherwise inherit
both. This plan modernises the layer in eight phases: wire the already-existing `propDecide`
tactic into `BooleanStructure.lean` and collapse the closed-tautology `*_quot` proofs onto it;
extend the same technique to the three hypothesis-driven `*_quot` lemmas via tautology + pairing +
modus ponens; fix and extend the `propDecide` regression tests; promote the existential
`ultrafilter_correspondence` to a named `Equiv`; restate `fold_le_of_derives` over `Multiset.inf`;
de-shadow the bespoke `Ultrafilter`; bridge it to Mathlib's maximal-ideal API; and refresh
`Algebraic/README.md`.

Definition of done: the acceptance criteria in "Acceptance Criteria" below, with `lake build`
green and the `scripts/check-module-invariants.sh` C2 axiom baseline unchanged at every phase
boundary. **C2 drift is a HARD STOP**, never a re-baseline.

The plan is built against the research report's corrections, not against the task description.
Where the two disagree, the report wins.

### Research Integration

Findings from the report that materially shaped this plan:

- **The core `propDecide` claim is empirically verified, not inherited.** The report added two
  scratch `example`s to `BooleanStructure.lean`, ran a real `lake build`, confirmed both compiled,
  and reverted (tree confirmed clean). The exact `le_sup_inf_quot` distributivity shape closes
  under `induction … using Quotient.ind; rename_i …; change Derives …; unfold Derives; propDecide`,
  and De Morgan closes via `and`/`or` directly with no manual unfolding.
- **Only ~10 of the 15 `*_quot` lemmas fit the bare pattern.** `propDecide`'s
  `tautologyDerivableFc'` mechanism proves *closed* schematic tautologies; its only input is the
  reified goal formula, so it cannot consume a hypothesis derivation as a side premise.
- **Three lemmas are hypothesis-driven** (`le_trans_quot`, `le_inf_quot`, `sup_le_quot`) and need
  the tautology + `Combinators.pairing` + `modus_ponens` extension, not the bare pattern.
  `le_antisymm_quot` proves an *equality* via `Quotient.sound` and is not `Derives`-shaped at all —
  `propDecide` cannot touch it under any encoding.
- **`Order.Ideal.ofPFilterCompl` does not exist in Mathlib** (grep across the full pinned
  `v4.33.0-rc1` checkout, zero hits), and Mathlib defines `IsMaximal` only for `Order.Ideal`, never
  for `Order.PFilter` (which has only `IsPrime`). The PFilter option is dropped from consideration.
- **The `LindenbaumQuotient.provEquiv_*` congruence extension resolves to "nothing fits."** Every
  non-trivial congruence is conditional on a `≈ₚ` hypothesis rather than a closed tautology;
  `provEquiv_box_congr` additionally needs `necessitation` and `provEquiv_all_past_congr` needs
  `Perpetuity.pastMono`, neither of which is propositional. No phase budget is allocated to it.
- **The `Finset` detour for `fold_le_of_derives` is unnecessary.** `Multiset.inf`,
  `Multiset.inf_coe`, `Multiset.le_inf`, and `Multiset.inf_le` all exist as auto-generated
  `@[to_dual]` duals of `Multiset.sup`, requiring only `[SemilatticeInf α] [OrderTop α]`, both of
  which `LindenbaumAlg`'s `BooleanAlgebra` instance provides.
- **`PropDecideTest.lean`'s De Morgan docstring is verified wrong.** The docstring (now at
  `:39-42`, shifted from the task description's `:44-46`) claims and/or-shaped goals are "out of
  scope for the pure imp/bot reflection skeleton"; `PropDecide.reify`'s `whnf` call unfolds
  `and`/`or`/`neg` automatically and the report closed the De Morgan goal directly.
- **Line-anchor correction (feasibility unchanged).** After `unfold Derives` the goal is
  `Derivable`-shaped, so dispatch reaches `PropDecide.extractDerivableGoal` at
  `PropDecide.lean:100`, not `extractDerivationGoal` at `Helpers.lean:524`. Both branches are wired
  and tested.

### Facts established during planning that the report did not measure

Checked while sizing phases; each changes a scope estimate or a risk:

1. **The `*_quot` baseline is 286 proof-body lines under a defined metric** (see "Acceptance
   Criteria" for the metric and the exact command). The report's "~430 lines" is the whole-file
   figure (441). The per-lemma inclusive proof-body spans are: `le_refl_quot` 4, `le_trans_quot` 6,
   `le_antisymm_quot` 5, `inf_le_left_quot` 8, `inf_le_right_quot` 8, `le_inf_quot` 13,
   `le_sup_left_quot` 11, `le_sup_right_quot` 13, `sup_le_quot` 39, `bot_le_quot` 6,
   `le_top_quot` 12, `le_sup_inf_quot` 110, `inf_compl_le_bot_quot` 28, `top_le_sup_compl_quot` 14,
   `sup_comm_quot` 9. These are the *proof* spans (theorem line through last proof line); the
   report's larger per-lemma figures include leading docstrings and section comments.
2. **The "under 100 lines" bar is tighter than the report's 95-110 estimate.** Summing optimistic
   post-refactor targets gives **~109**, not under 100 — see "Decision D2" for the arithmetic and
   the fallback figures. This is the single most likely acceptance-criterion miss in the plan.
3. **`Ultrafilter`'s 16 hits in `Metalogic/Bundle/LimitMCS.lean` are Mathlib's `Ultrafilter`,
   not the bespoke one.** `LimitMCS.lean` imports `Mathlib.Order.Filter.Ultrafilter.Basic` and never
   imports any `Metalogic.Algebraic` module; every hit is `Ultrafilter Rat` / `Ultrafilter.of`.
   The same holds for the `Semantics/Ultraproduct/` hits and the two prose mentions in
   `Chronicle/ChronicleRealExtension.lean`. The report's "no live consumer" claim survives this
   check — but it is exactly the kind of claim that must be re-verified per-declaration at
   implementation time, not assumed.
4. **The bespoke `Ultrafilter`'s only non-`UltrafilterMCS.lean` consumers are four Boneyard files,
   all behind `#exit`.** `Boneyard/UltrafilterFrame/{AlgebraicCompleteness,UltrafilterFrame}.lean`
   and `Boneyard/StrictSemanticsLegacy/Algebraic/UltrafilterChain.lean` import
   `Algebraic.UltrafilterMCS`, and `Boneyard/UltrafilterFrame/TenseS5Algebra.lean` imports
   `Algebraic.BooleanStructure` — each with its `#exit` at lines 27, 54, 46, and 37 respectively,
   *before* every `open`/`Ultrafilter` occurrence. Renaming or replacing the structure therefore
   cannot break them, but invariant **C11** (every Boneyard import resolves) still applies to the
   import lines themselves, which are unaffected.
5. **`UltrafilterMCS.lean` is itself the layer's largest consumer**: 63 `Ultrafilter` occurrences
   and 46 `carrier` occurrences across 1,071 lines. This is the fact that reverses the report's
   lean on Decision D1 — see below.
6. **`fold_le_of_derives` has exactly one call site**, at `UltrafilterMCS.lean:718`, in the same
   file. Zero external references (grep, live tree).
7. **`Combinators.pairing` exists** at `Theorems/Combinators.lean:555` with signature
   `⊢[fc] A.imp (B.imp (A.and B))`, and `DerivationTree.modus_ponens` is already used inside
   `BooleanStructure.lean` (e.g. `:198`, `:206`, `:211`). The Phase 2 extension needs no new
   imports.
8. **The `Algebraic/README.md` "Last verified" stamp is genuinely absent**; the file ends with
   `*Last updated: 2026-08-26*`, a different field. The house convention for the new field is
   visible at `FormalSystem/BaseLanguage/README.md:69` (`**Last verified**: YYYY-MM-DD`) and
   `FormalSystem/Automation/README.md:107` (`*Last verified: YYYY-MM-DD*`); Phase 8 should match
   whichever form the majority of sibling `Metalogic/*/README.md` files use.

### Prior Plan Reference

No prior plan. This is the first plan for this task.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as a roadmap input for this dispatch and carries no
item naming the algebraic layer, `propDecide`, or the ultrafilter correspondence (grep: one
incidental line at `:744` recording that only the algebraic/canonical route is pursued for
completeness). No roadmap phases are added and ROADMAP.md is not modified.

## Goals & Non-Goals

**Goals**:
- Collapse the closed-tautology `*_quot` proofs in `BooleanStructure.lean` onto `propDecide`.
- Extend the same technique to the three hypothesis-driven `*_quot` lemmas via
  tautology + `Combinators.pairing` + `modus_ponens`.
- Correct the verified-wrong `PropDecideTest.lean` De Morgan docstring and add De Morgan and
  distributivity regression cases.
- Promote `ultrafilter_correspondence` from an existential statement to a named
  `SetMaximalConsistent.ultrafilterEquiv : {Γ // SetMaximalConsistent Γ} ≃ Ultrafilter LindenbaumAlg`,
  with `ultrafilter_correspondence` derived as a corollary and both round-trip theorems consumed
  as its fields.
- Restate `fold_le_of_derives` over `((L.map toQuot : List _) : Multiset _).inf`, removing the
  hand-rolled `fold_from_x` reassociation `have`.
- Remove the `Ultrafilter` name collision with Mathlib and give the structure a proved bridge to
  Mathlib's maximal-ideal API.
- Refresh `Algebraic/README.md`, including a "Last verified" stamp and the Decision D1 rationale.

**Non-Goals**:
- **The `LindenbaumQuotient.provEquiv_*` congruence extension is explicitly out of scope.** The
  report read all nine congruence lemmas and found every non-trivial one is conditional on a
  `≈ₚ` hypothesis rather than a closed tautology (`provEquiv_box_congr` needs `necessitation`,
  `provEquiv_all_past_congr` needs `Perpetuity.pastMono`); the one that would fit, `derives_refl`,
  is already a 3-line proof via `Combinators.identity` and gains nothing. "Where it fits" resolves
  to "nowhere non-trivial fits." No phase budget is allocated.
- **`le_antisymm_quot` is explicitly excluded from the `propDecide` rewrite.** Its conclusion is an
  equality proved by `Quotient.sound`, not a `Derives`/`Derivable` goal; `propDecide` cannot apply
  under any encoding. It stays at 5 lines.
- **The `Order.PFilter` / `Order.Ideal.ofPFilterCompl` encoding is dropped, not deferred.** The
  bridge function does not exist in the pinned Mathlib and `PFilter` has no `IsMaximal`.
- No changes to `FlowFrame.lean` or `InteriorOperators.lean` beyond whatever a rename mechanically
  requires (expected: none — neither references the bespoke `Ultrafilter`).
- No Jonsson-Tarski representation work (tasks 497/125). This task only removes the obstacles.
- No new `sorry` anywhere. C3 (zero structural sorries) must stay green.

## Open Decisions

Two decisions are surfaced rather than silently baked in. Both have a plan default so
implementation is never blocked; both are reversible at a named phase boundary.

### Decision D1: `BAUltrafilter` rename + bridge `Equiv` (option b), *contra* the report's lean

**Plan default: option (b).** Rename the bespoke `structure Ultrafilter` to `BAUltrafilter`, keep
its API, and prove one bridge `BAUltrafilter α ≃ {I : Order.Ideal α // I.IsMaximal}`.

The research report leaned toward option (a) — replacing the structure outright with
`{I : Order.Ideal LindenbaumAlg // I.IsMaximal}` — on the grounds that the layer has no live
consumer, and explicitly declined to settle it. Planning-time measurement reverses that lean on
three grounds:

1. **"No live consumer" is true externally and false internally.** `UltrafilterMCS.lean` is itself
   a 1,071-line consumer with 63 `Ultrafilter` and 46 `carrier` occurrences. Under option (a) every
   one of those becomes an ideal-membership statement with a complement flip (`a ∈ U` becomes
   `aᶜ ∈ I`), which is a mathematical re-derivation of `mcsToUltrafilter`'s six field proofs and the
   two round trips, not a rename. That is several agent runs, not one.
2. **Option (a) strictly contains option (b)'s work.** The complement-flip mathematics — showing
   `{a | aᶜ ∈ I}` satisfies the six ultrafilter axioms and conversely — is exactly the content of
   the bridge `Equiv`. Option (a) is that proof *plus* rewriting ~500 lines of consumer around it.
   Option (b) buys the same Mathlib access for strictly less work.
3. **The motivating consumers want the filter side.** Jonsson-Tarski's embedding is
   `η(a) = {U | a ∈ U}` over ultra*filters*. Because Mathlib has no `PFilter.IsMaximal`, the
   Ideal-side encoding forces a complement flip into every downstream statement in tasks 497/125 —
   an ergonomic tax on precisely the consumers this task exists to serve.

Option (b) still satisfies the acceptance criterion as written ("no declaration named `Ultrafilter`
outside Mathlib in the live tree, **or** a documented `BAUltrafilter` with a bridge `Equiv`"), and
Phase 7 additionally *reduces* the duplicated axiom surface by re-deriving what Mathlib supplies
through the bridge rather than leaving hand-proved duplicates standing.

**Reversal point**: end of Phase 6. If the user prefers option (a), Phases 6 and 7 are replaced by
an option-(a) phase group; Phases 1-5 and 8 are unaffected. Estimated switch cost: +6 to +10 hours.

### Decision D2: what "under 100 lines" means, and what the bar comes to if Phase 2 is hard

The acceptance criterion "BooleanStructure.lean's `*_quot` lemmas total under 100 lines" needs a
metric before it can be checked. The plan adopts: **the sum of inclusive proof-body spans (theorem
declaration line through last proof line) for all 15 `*_quot` theorems, excluding leading
docstrings and section comments** — the exact command is in "Acceptance Criteria" below.

Under that metric the measured baseline is **286**. Projected outcomes:

| Scenario | Projected total | Under 100? |
|----------|-----------------|------------|
| Phase 1 only (10 tautology lemmas rewritten, ~7 lines each) | ~147 | No |
| Phases 1 + 2, optimistic (`sup_le_quot` 39→~12, `le_inf_quot` 13→~10, `le_trans_quot` unchanged at 6) | **~109** | **No — narrowly** |
| Phases 1 + 2 + per-lemma line-shaving (inline `Quotient.ind` binders via `with \| _ φ =>`, saving one `rename_i` line on each of ~10 lemmas) | **~99** | **Yes — knife-edge** |
| Phase 2 fails on `sup_le_quot` only | ~136 | No |
| Phase 2 fails on all three hypothesis-driven lemmas | ~139 | No |

So: the bar is reachable, but only with **both** the Phase 2 extension **and** the line-shaving,
and the margin is a single line. The report's "achievable but tight" is if anything optimistic.

**Recommendation**: treat **under 100 as the stretch target** and **≤ 115 with the measured number
recorded in the phase's completion note as the accept bar**. Churning on formatting to buy the last
ten lines is not a good use of an agent run, and a `[COMPLETED WITH EXCLUSIONS]` close on Phase 2
recording the measured figure is the honest outcome if it lands in 100-115. The final call on the
bar is the user's; implementation must not silently relax it, and must not silently claim it either.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The new `BooleanStructure.lean` → `Automation.Tactics.PropDecide` import edge creates a cycle | H | L | Report verified by grep that nothing under `Metalogic/Decidability/`, `Metalogic/Core/`, or `Theorems/` imports any `Algebraic.*` module; re-confirmed at plan time (only `Metalogic.lean`, `Algebraic.lean`, `InteriorOperators.lean`, `UltrafilterMCS.lean`, and Boneyard import `Algebraic.BooleanStructure`/`UltrafilterMCS`). Phase 1's first task re-runs the grep and adds the import in isolation with a build before touching any proof. |
| The "under 100 lines" bar is missed | M | **H** | Decision D2 states the arithmetic and the accept-bar recommendation up front. Phase 2 measures and records rather than churning. |
| The Phase 2 pairing+MP extension does not close `sup_le_quot` | M | M | Phase 2's first task is a single-lemma spike on `sup_le_quot` before touching the other two; if the spike fails, the phase closes `[COMPLETED WITH EXCLUSIONS]` with the existing 39-line proof retained and D2's "fails on `sup_le_quot` only" row (~136) recorded as the outcome. |
| A "dead"/"unused" scope assumption fails on re-verification (the sibling task's failure mode: five Reasoned Exclusions, line target missed) | M | M | Every phase that asserts something is unused makes per-declaration re-verification its **first task**, with the grep recorded in the phase's completion note. Scope hypotheses in this plan are deliberately stated smaller than the optimistic reading. |
| Adding a Mathlib import (`Order.Ideal`, `Order.PrimeIdeal`) shifts the C2 axiom baseline | H | L | C2 records `#print axioms` for four flagship theorems; new imports do not change proof terms of existing theorems. Phase 7 runs the full invariant script and treats any C2 delta as a HARD STOP requiring investigation, never a re-baseline. |
| The `BAUltrafilter` rename breaks a Boneyard import (C11) | M | L | Planning confirmed all four Boneyard consumers place `#exit` *before* every `Ultrafilter` occurrence, and none imports a renamed *module*. Phase 6 re-verifies the `#exit` line positions before renaming. |
| `Multiset.inf` restatement changes `fold_le_of_derives`'s statement in a way the single call site cannot absorb | M | L | The call site is in-file at `:718` and is edited in the same phase; the phase declares `atomic-batch` so the intermediate red state is expected. |
| Docstring/README counts drift and fail C14 | M | M | Phase 8 runs the full `scripts/check-module-invariants.sh` (not `--no-build`), which exercises C5, C12, C13, and C14. |

## Acceptance Criteria

Checked at task close, not per phase:

1. **`*_quot` line total.** Metric and command:
   ```bash
   awk '/^theorem [a-zA-Z_]*_quot/ {start=NR; inproof=1; next}
        { if (inproof && ($0 ~ /^theorem |^instance |^\/--|^\/-!|^end |^@\[/)) { total += NR-start; n++; inproof=0 } }
        END { print "lemmas:", n, "total_body_lines:", total }' \
     FormalSystem/Metalogic/Algebraic/BooleanStructure.lean
   ```
   Baseline: `lemmas: 15 total_body_lines: 286`. Target: under 100 (stretch) / ≤ 115 with the
   measured number recorded (accept) — see Decision D2. The lemma count must still read 15.
2. **No `Ultrafilter` shadow.** `grep -rn 'structure Ultrafilter\|def Ultrafilter' FormalSystem/ --include=*.lean | grep -v Boneyard` returns nothing, **or** a documented `BAUltrafilter` exists with a proved bridge `Equiv` to `{I : Order.Ideal α // I.IsMaximal}` (the plan default, Decision D1).
3. **`ultrafilterEquiv` exists and is consumed.** `SetMaximalConsistent.ultrafilterEquiv` is
   declared, and `ultrafilter_correspondence` is derived from it rather than proved from scratch;
   both round-trip theorems appear as its fields.
4. **`fold_le_of_derives`** is stated over a `Multiset.inf` and the `fold_from_x` reassociation
   `have` is gone.
5. **`lake build` green** and **`bash scripts/check-module-invariants.sh` all-pass**, with the C2
   axiom baseline unchanged. C2 drift is a HARD STOP.
6. **Zero new sorries** (C3 stays green).

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 4 | -- |
| 2 | 2, 5 | 1 (for 2), 4 (for 5) |
| 3 | 6 | 4, 5 |
| 4 | 7 | 6 |
| 5 | 8 | 2, 3, 7 |

Phases within the same wave can execute in parallel. Wave-1 territory contract: Phase 1 owns
`BooleanStructure.lean`, Phase 3 owns `Tests/BimodalTest/Metalogic/PropDecideTest.lean`, Phase 4
owns `UltrafilterMCS.lean`. Phase 1 changes proof bodies only — no `*_quot` statement changes — so
Phase 4's dependence on `BooleanStructure`'s exports is unaffected.

Every phase, regardless of Verification Tier, closes on: `lake build` exits 0 **and**
`bash scripts/check-module-invariants.sh` reports the C2 axiom baseline unchanged. C2 drift is a
HARD STOP: stop, report, do not re-baseline.

---

### Phase 1: Wire `propDecide` into `BooleanStructure.lean` and rewrite the closed-tautology `*_quot` lemmas [NOT STARTED]

**Goal**: `BooleanStructure.lean` imports `propDecide` with no import cycle, and every `*_quot`
lemma whose statement is a closed propositional tautology is proved by the four-line pattern.

**Tasks**:
- [ ] **Re-verify first**: re-run `grep -rn 'import FormalSystem.Metalogic.Algebraic' FormalSystem/ Tests/ --include=*.lean` and confirm nothing under `Metalogic/Decidability/`, `Metalogic/Core/`, `Theorems/`, or `Automation/` imports any `Algebraic.*` module. Record the output in the completion note.
- [ ] **Re-verify second**: enumerate the `*_quot` theorems and re-confirm the count is 15 and that each candidate below takes no derivation hypothesis. Record the per-declaration verdict (amenable / hypothesis-driven / not `Derives`-shaped).
- [ ] Add `import FormalSystem.Automation.Tactics.PropDecide` to `BooleanStructure.lean` and build **before** touching any proof. If the build fails, stop and report — do not work around a cycle.
- [ ] Rewrite each confirmed closed-tautology lemma as `induction … using Quotient.ind` (one per quotient argument) / `rename_i …` / `change Derives …` / `unfold Derives` / `propDecide`. Expected set: `le_refl_quot`, `inf_le_left_quot`, `inf_le_right_quot`, `le_sup_left_quot`, `le_sup_right_quot`, `bot_le_quot`, `le_top_quot`, `le_sup_inf_quot`, `inf_compl_le_bot_quot`, `top_le_sup_compl_quot`.
- [ ] Where `induction a using Quotient.ind with | _ φ =>` binds the representative inline, prefer it over a separate `rename_i` line (Decision D2's line-shaving; one line saved per lemma).
- [ ] Leave `le_antisymm_quot`, `le_trans_quot`, `le_inf_quot`, `sup_le_quot`, and `sup_comm_quot` untouched in this phase.
- [ ] Measure and record the acceptance-criterion-1 figure after the rewrite.

**Timing**: 2 hours

**Depends on**: none

**Verification Tier**: full

*Rationale*: this phase adds an import edge into a module with downstream dependents
(`InteriorOperators.lean`, `UltrafilterMCS.lean`, `Algebraic.lean`, and four Boneyard files subject
to C11), which is a build-graph change, not a local one.

**Commit Mode**: per-substep

*Each rewritten lemma that builds green is its own commit; the import addition is a commit of its
own, taken before any proof is touched.*

**Scope Hypothesis**: exactly 10 of the 15 `*_quot` lemmas are closed tautologies amenable to the
bare pattern, and rewriting them takes the metric from 286 to roughly 147. **Confirm at
implementation time** by, for each of the 10, reading its statement and checking it binds no
`Derives`/`≤` hypothesis before attempting the rewrite; and by re-running the
acceptance-criterion-1 command after the phase. If a lemma in the expected set turns out to bind a
hypothesis, move it to Phase 2 and record the move rather than forcing the bare pattern. If the
resulting figure differs from ~147, record the actual figure — the projection is a hypothesis, not
a fact.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — add the `PropDecide` import; replace
  ~10 proof bodies. No statement changes.

**Verification**:
- `lake build` exits 0.
- `bash scripts/check-module-invariants.sh` — C1, C2, C3 green; C2 baseline unchanged (HARD STOP on drift).
- The `*_quot` lemma count still reads 15.
- `git diff` shows no change to any `theorem …_quot` signature line.

---

### Phase 2: Tautology + pairing + MP extension for the three hypothesis-driven `*_quot` lemmas [NOT STARTED]

**Goal**: `sup_le_quot`, `le_inf_quot`, and `le_trans_quot` are proved by stating their conditional
form as a closed tautology over opaque atoms, closing it with `propDecide`, and combining with the
actual hypotheses via `Combinators.pairing` + `DerivationTree.modus_ponens`.

**Tasks**:
- [ ] **Re-verify first**: confirm `Combinators.pairing` (`Theorems/Combinators.lean:555`,
      `⊢[fc] A.imp (B.imp (A.and B))`) and `DerivationTree.modus_ponens` are reachable from
      `BooleanStructure.lean`'s existing imports without adding one. Record the check.
- [ ] **Spike `sup_le_quot` first, alone.** It is the largest of the three (39 lines) and the one
      the line-count bar depends on. Target shape: `propDecide` closes the constructive-dilemma
      tautology `⊢ ((φ.imp χ).and (ψ.imp χ)).imp ((φ.or ψ).imp χ)`, then `pairing` builds
      `(φ.imp χ).and (ψ.imp χ)` from `hac`/`hbc` and two `modus_ponens` steps discharge it.
- [ ] If the spike closes, commit it, then apply the same shape to `le_inf_quot`
      (`⊢ ((φ.imp ψ).and (φ.imp χ)).imp (φ.imp (ψ.and χ))`).
- [ ] Evaluate `le_trans_quot` (currently 6 lines via `derives_trans`). It is **already minimal**;
      rewrite it only if the result is strictly shorter *and* no less readable. Recording "left as
      is, already minimal" is an acceptable outcome, not a miss.
- [ ] Re-measure the acceptance-criterion-1 figure and record it explicitly in the completion note,
      against Decision D2's table.
- [ ] If the figure lands in 100-115, close the phase `[COMPLETED WITH EXCLUSIONS]` with a
      `#### Reasoned Exclusions` record naming the shortfall, the measured number, and the evidence
      (the command output). Do not churn on formatting to buy the last few lines.

**Timing**: 2 hours

**Depends on**: 1

**Verification Tier**: local

*Rationale*: edits confined to `BooleanStructure.lean` with no statement changes and no new import.
Blind spot accepted: downstream semantic behaviour — covered by the phase's own closing `lake build`
and C2 check.

**Commit Mode**: per-substep

**Scope Hypothesis**: the extension takes `sup_le_quot` 39→~12 and `le_inf_quot` 13→~10, landing
the metric at ~109 (Decision D2 row 2), or ~99 if Phase 1's line-shaving held. **Confirm at
implementation time** by running the acceptance-criterion-1 command and comparing against D2's
table; report which row the actual outcome matches. Treat 109 as the expected case and under-100 as
the stretch, per D2 — a phase that lands at 109 and says so is a success, one that claims under 100
without the command output is not.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — up to three proof bodies.

**Verification**:
- `lake build` exits 0.
- `bash scripts/check-module-invariants.sh` — C2 baseline unchanged (HARD STOP on drift).
- Acceptance-criterion-1 command run and its output recorded verbatim in the completion note.
- No `*_quot` statement changed.

---

### Phase 3: Fix the `PropDecideTest.lean` docstring and add De Morgan + distributivity regressions [NOT STARTED]

**Goal**: the verified-wrong "out of scope" claim is removed and replaced by passing regression
cases that exercise `and`/`or`-shaped goals directly.

**Tasks**:
- [ ] **Re-verify first**: read the current docstring in place (report locates it at `:39-42`, the
      task description said `:44-46` — use the content, not the line number, as the anchor) and
      confirm it still makes the "out of scope for the pure imp/bot reflection skeleton" claim.
- [ ] Replace the docstring with an accurate one: `PropDecide.reify`'s `whnf` call unfolds
      `and`/`or`/`neg` into the `imp`/`bot` skeleton automatically, so and/or-shaped goals are in
      scope.
- [ ] Add the De Morgan case the report verified:
      `example (A B : Formula) : ⊢ (A.and B).neg.imp (A.neg.or B.neg) := by propDecide`.
- [ ] Add a distributivity regression matching the `le_sup_inf_quot` shape:
      `example (A B C : Formula) : ⊢ ((A.or B).and (A.or C)).imp (A.or (B.and C)) := by propDecide`.
- [ ] Keep the existing contrapositive-flavoured example — it tests a different path and its
      removal is not required by anything.

**Timing**: 0.5 hours

**Depends on**: none

**Verification Tier**: local

*Rationale*: edits confined to one test module, no signature exposed to any other module.

**Commit Mode**: per-substep

**Scope Hypothesis**: none asserted beyond the docstring's continued presence, which the first task
re-verifies by content.

**Files to modify**:
- `Tests/BimodalTest/Metalogic/PropDecideTest.lean` — docstring correction plus two new `example`s.

**Verification**:
- `lake build` exits 0 (the test library is a build target, so a failing `example` fails the build).
- Both new examples elaborate with no `sorry` and no error.
- `bash scripts/check-module-invariants.sh` — C2 baseline unchanged.

---

### Phase 4: `SetMaximalConsistent.ultrafilterEquiv` as a named `Equiv` [NOT STARTED]

**Goal**: the MCS/ultrafilter bijection is a named `Equiv` whose fields are the two existing
round-trip theorems, and `ultrafilter_correspondence` is a one-line corollary of it.

**Tasks**:
- [ ] **Re-verify first, per declaration**: re-run the reference greps and confirm (a)
      `ultrafilter_correspondence` (`:782`) is referenced only by `ultrafilter_mcs_round_trip`
      (`:983`), (b) `mcs_ultrafilter_round_trip` (`:1056`) is referenced nowhere outside its own
      declaration, (c) neither is referenced from `docs/`, `README.md`, or any live `.lean` file
      outside `UltrafilterMCS.lean`. Record each grep's output. **Do not proceed on the report's
      claim alone** — this is the exact assumption class that cost the sibling task its line target.
- [ ] Declare
      `noncomputable def SetMaximalConsistent.ultrafilterEquiv : {Γ // SetMaximalConsistent Γ} ≃ Ultrafilter LindenbaumAlg`
      with `toFun := mcsToUltrafilter` (`:524`), `invFun := ultrafilterToMcs` (`:969`),
      `left_inv := ultrafilter_mcs_round_trip`, `right_inv := mcs_ultrafilter_round_trip`.
      Adapt the existing round-trip statements to `Function.LeftInverse`/`RightInverse` shape if
      their current form does not defeq-match; prefer adapting the `Equiv` field term over
      restating the theorems.
- [ ] Replace `ultrafilter_correspondence`'s 127-line from-scratch proof with the corollary
      `⟨e.toFun, e.invFun, e.left_inv, e.right_inv⟩` (or the `Equiv`-projection spelling that
      elaborates). **The statement of `ultrafilter_correspondence` must not change** — it stays the
      existential, so any future consumer is unaffected.
- [ ] Simplify `ultrafilter_mcs_round_trip` only if it becomes trivially derivable; if it is now the
      `Equiv`'s field, leave it as the proved lemma it is. Do not delete either round-trip theorem.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

*Rationale*: one new `def` plus one proof-body replacement inside `UltrafilterMCS.lean`; no existing
signature changes. Blind spot accepted: nothing outside the file references either theorem, which
the first task re-verifies rather than assumes.

**Commit Mode**: per-substep

**Scope Hypothesis**: `ultrafilter_correspondence` has exactly one reference (from
`ultrafilter_mcs_round_trip`) and `mcs_ultrafilter_round_trip` has zero; both are therefore free to
be restructured. **Confirm at implementation time** with the per-declaration greps in the first
task, output recorded. If a reference exists that the report did not see, keep the existing proof
and restrict the phase to adding `ultrafilterEquiv` alongside it.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — add `ultrafilterEquiv`; replace
  `ultrafilter_correspondence`'s proof body.

**Verification**:
- `lake build` exits 0.
- `#check SetMaximalConsistent.ultrafilterEquiv` elaborates at the stated type.
- `ultrafilter_correspondence`'s statement line is byte-identical to its pre-phase form
  (`git diff` shows a proof-body change only).
- `bash scripts/check-module-invariants.sh` — C2 baseline unchanged, C3 green.

---

### Phase 5: Restate `fold_le_of_derives` over `Multiset.inf` [NOT STARTED]

**Goal**: `fold_le_of_derives` is stated over `((L.map toQuot : List _) : Multiset _).inf` and the
hand-rolled `fold_from_x` reassociation `have` is gone.

**Tasks**:
- [ ] **Re-verify first**: confirm `Multiset.inf`, `Multiset.inf_coe`, `Multiset.le_inf`, and
      `Multiset.inf_le` resolve at the pinned Mathlib with the `[SemilatticeInf α] [OrderTop α]`
      instances `LindenbaumAlg` provides (`#check` each, or `lean_hover_info`). Record the four
      signatures.
- [ ] **Re-verify second**: re-confirm `fold_le_of_derives` has exactly one call site
      (`UltrafilterMCS.lean:718`) and zero references elsewhere in the live tree. Record the grep.
- [ ] Restate the theorem over the multiset coercion. Do **not** route through `Finset` — the
      report verified `Multiset.le_inf`/`Multiset.inf_le` give both directions directly.
- [ ] Delete the inlined `fold_from_x` reassociation `have`.
- [ ] Update the single call site at `:718` in the same commit.

**Timing**: 1.5 hours

**Depends on**: 4

*Same file as Phase 4; serialized to avoid a merge conflict, not because of a logical dependency.*

**Verification Tier**: interface

*Rationale*: the theorem's statement changes. The dependent set is enumerated and is exactly one
in-file call site, so the "build the changed module plus its enumerated direct dependents" tier is
satisfied by building `UltrafilterMCS.lean` — but the tier is declared `interface`, not `local`,
because a signature genuinely changes and the enumeration must be re-verified rather than assumed.

**Commit Mode**: atomic-batch

*The restated theorem and its call-site update are one objective; the intermediate state (statement
changed, call site not yet updated) is expected red and MUST NOT be committed.*

**Scope Hypothesis**: `fold_le_of_derives` has exactly one call site, all four `Multiset` lemmas
exist at the pinned Mathlib, and the restatement removes the `fold_from_x` `have` entirely.
**Confirm at implementation time** by the two re-verification tasks above (grep output and four
`#check`s recorded). If a second call site exists, add it to the atomic batch and say so.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — theorem statement and proof at `:565`;
  call site at `:718`.

**Verification**:
- `lake build` exits 0.
- `grep -c 'fold_from_x' FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` returns 0.
- `bash scripts/check-module-invariants.sh` — C2 baseline unchanged, C3 green.

---

### Phase 6: Rename the bespoke `Ultrafilter` to `BAUltrafilter` [NOT STARTED]

**Goal**: no declaration named `Ultrafilter` shadows Mathlib's in the live tree.

**Tasks**:
- [ ] **Re-verify first, per file**: re-run
      `grep -rn 'Ultrafilter' FormalSystem/ Tests/ --include=*.lean` and classify every hit as
      *bespoke* or *Mathlib's*. Planning found the bespoke set is confined to
      `UltrafilterMCS.lean` (63 hits), with `Bundle/LimitMCS.lean` (16),
      `Semantics/Ultraproduct/*` (12), `Chronicle/ChronicleRealExtension.lean` (2 prose), and
      `Semantics.lean`/`DependentUltraproductProbe.lean` all being Mathlib's `Ultrafilter` on
      filters. **Re-derive this classification; do not inherit it.**
- [ ] **Re-verify second**: confirm each of the four Boneyard consumers places `#exit` *before* its
      first `Ultrafilter` occurrence (`Boneyard/UltrafilterFrame/AlgebraicCompleteness.lean:27`,
      `Boneyard/UltrafilterFrame/UltrafilterFrame.lean:54`,
      `Boneyard/StrictSemanticsLegacy/Algebraic/UltrafilterChain.lean:46`,
      `Boneyard/UltrafilterFrame/TenseS5Algebra.lean:37`). Record the check — C11 requires their
      *import* lines to keep resolving, and no module is being renamed, so they should be unaffected.
- [ ] Rename `structure Ultrafilter` → `BAUltrafilter`, together with `instMembershipUltrafilter`,
      `Ultrafilter.ext`, `Ultrafilter.empty_not_mem`, and every other `Ultrafilter.*` declaration in
      `UltrafilterMCS.lean`, and every use site in that file.
- [ ] Update `Algebraic/README.md`'s API sketch (`:149-150`) and the `Algebraic.lean` aggregator
      docstring if either names the type.
- [ ] Add a docstring on `BAUltrafilter` stating the name's reason (avoiding the Mathlib collision)
      and pointing forward to the Phase 7 bridge.

**Timing**: 1 hour

**Depends on**: 4, 5

**Verification Tier**: interface

*Rationale*: a type's name changes; call sites are enumerated and (per the re-verification) confined
to `UltrafilterMCS.lean` plus two markdown/docstring references.*

**Commit Mode**: atomic-batch

*The rename is one objective across `UltrafilterMCS.lean`, `Algebraic/README.md`, and possibly
`Algebraic.lean`; partial per-file states are expected red and MUST NOT be committed.*

**Scope Hypothesis**: the bespoke `Ultrafilter` has 63 occurrences, all in `UltrafilterMCS.lean`,
plus documentation mentions in `Algebraic/README.md`; the remaining ~40 tree-wide `Ultrafilter` hits
are Mathlib's and must not be touched. **Confirm at implementation time** by the per-file
classification in the first task, with the classified grep recorded. Touching a Mathlib
`Ultrafilter` site is a defect, not a scope expansion.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — rename throughout.
- `FormalSystem/Metalogic/Algebraic/README.md` — API sketch lines.
- `FormalSystem/Metalogic/Algebraic.lean` — docstring, if it names the type.

**Verification**:
- `lake build` exits 0.
- `grep -rn 'structure Ultrafilter\|Ultrafilter\.' FormalSystem/Metalogic/Algebraic/ --include=*.lean`
  returns no bespoke hits.
- `bash scripts/check-module-invariants.sh` — C2 unchanged, C5/C11/C12/C13 green.

---

### Phase 7: Bridge `BAUltrafilter` to Mathlib's maximal-ideal API [NOT STARTED]

**Goal**: one proved `Equiv` connects the bespoke structure to `{I : Order.Ideal α // I.IsMaximal}`,
and the hand-proved axioms Mathlib already supplies are derived through it rather than duplicated.

**Tasks**:
- [ ] **Re-verify first**: `#check` each Mathlib name the phase depends on against the pinned
      checkout — `Order.Ideal.IsMaximal`, `Order.Ideal.IsProper.exists_le_maximal`,
      `Order.Ideal.IsMaximal.isPrime`, `Order.Ideal.IsPrime.isMaximal`,
      `Order.Ideal.IsPrime.mem_or_compl_mem`, `Order.Ideal.IsPrime.compl_mem_of_notMem`. Record the
      six signatures. Confirm again that no `Order.PFilter.IsMaximal` exists (the dropped option).
- [ ] Add `import Mathlib.Order.Ideal` and `import Mathlib.Order.PrimeIdeal` to
      `UltrafilterMCS.lean` and build **before** writing any proof.
- [ ] Prove `BAUltrafilter α ≃ {I : Order.Ideal α // I.IsMaximal}` for `[BooleanAlgebra α]`, with
      `toFun` sending `U` to the ideal `{a | aᶜ ∈ U}` and `invFun` sending `I` to the carrier
      `{a | aᶜ ∈ I}`. Use `IsMaximal.isPrime` + `IsPrime.mem_or_compl_mem` for the `compl_or`
      direction and `IsPrime.compl_mem_of_notMem` for `compl_not`; use `IsPrime.isMaximal` for the
      reverse.
- [ ] **Reduce, don't duplicate**: where a `BAUltrafilter` field or downstream lemma is now
      derivable through the bridge from a Mathlib lemma, derive it. Keep the structure's fields
      (they define the type) but delete hand-proved *consequences* that Mathlib now supplies.
      Enumerate what was deleted in the completion note.
- [ ] Add a docstring on the bridge naming `IsProper.exists_le_maximal` as the algebra-level
      Lindenbaum extension lemma now reachable from this layer — this is the concrete payoff for
      tasks 497/125.

**Timing**: 2.5 hours

**Depends on**: 6

**Verification Tier**: full

*Rationale*: two new Mathlib imports change the build graph and the elaboration surface of a module
with downstream dependents, including four Boneyard files under C11.

**Commit Mode**: per-substep

*The import addition is its own commit, taken before any proof; the bridge `Equiv` is a second; each
derived-and-deleted duplicate is its own.*

**Scope Hypothesis**: all six Mathlib names exist at the pinned `v4.33.0-rc1` and the bridge needs
zero new bridge code beyond the `Equiv` itself. **Confirm at implementation time** by the six
`#check`s in the first task. If a name is absent or has a different signature, stop and report
rather than substituting a guess — the report already found one non-existent name
(`Order.Ideal.ofPFilterCompl`) in this exact area.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — two imports; one new `Equiv`; deletions
  of now-derivable duplicates.

**Verification**:
- `lake build` exits 0.
- The bridge `Equiv` elaborates and `#print axioms` on it shows no `sorryAx`.
- `bash scripts/check-module-invariants.sh` — **C2 baseline unchanged (HARD STOP on drift)**,
  C3 green, C11 green.

---

### Phase 8: Refresh `Algebraic/README.md` and record the Decision D1 rationale [NOT STARTED]

**Goal**: the README describes the modernised layer accurately, carries a "Last verified" stamp, and
records why the `BAUltrafilter` + bridge encoding was chosen over the Ideal-side replacement.

**Tasks**:
- [ ] **Re-verify first**: re-read the README against the post-Phase-7 tree and list every stale
      claim — line counts (`UltrafilterMCS.lean` is currently documented as 1,071 and will have
      changed), the `mcsToUltrafilter`/`ultrafilterToSet` API sketch at `:149-150`, the file table at
      `:40-56`, and any sorry/axiom counts C14 asserts. Record the list before editing.
- [ ] Update the API sketch to name `BAUltrafilter`, `SetMaximalConsistent.ultrafilterEquiv`, and the
      Mathlib bridge.
- [ ] Add a short "Design decisions" subsection recording Decision D1's rationale: the PFilter option
      was dropped because `Order.Ideal.ofPFilterCompl` does not exist and `PFilter` has no
      `IsMaximal`; the Ideal-side outright replacement was declined because it forces a complement
      flip into every downstream Jonsson-Tarski statement and strictly contains the bridge's work.
- [ ] Note the `propDecide` dependency: `BooleanStructure.lean` now imports
      `Automation/Tactics/PropDecide.lean`, and the layering rationale (no cycle).
- [ ] Add the "Last verified" stamp using the form the majority of sibling `Metalogic/*/README.md`
      files use (`FormalSystem/BaseLanguage/README.md:69` uses `**Last verified**: YYYY-MM-DD`;
      `FormalSystem/Automation/README.md:107` uses `*Last verified: YYYY-MM-DD*`). Keep the existing
      `*Last updated:*` footer and update its date too.
- [ ] Record the final acceptance-criterion-1 measurement in the README's status section.

**Timing**: 1 hour

**Depends on**: 2, 3, 7

**Verification Tier**: prose

*Rationale*: all edits are in a markdown file with zero compile surface. Blind spot accepted: broken
cross-references and stale documented counts — both are covered by the C5/C12/C13/C14 checks in this
phase's verification, which is why the full invariant script (not `--no-build`) is required here.

**Commit Mode**: per-substep

**Scope Hypothesis**: no count or file list asserted beyond the stale-claim list, which the first
task produces by direct re-reading rather than by inheriting a plan-time enumeration.

**Files to modify**:
- `FormalSystem/Metalogic/Algebraic/README.md`

**Verification**:
- `bash scripts/check-module-invariants.sh` (full, **not** `--no-build`) — C5, C12, C13, C14 green;
  C2 unchanged.
- No task-number citations introduced (`.claude/rules/no-task-references-in-deliverables.md`;
  C9 enforces this under `FormalSystem/`).

---

## Testing & Validation

- [ ] `lake build` exits 0 at every phase boundary.
- [ ] `bash scripts/check-module-invariants.sh` all-pass at task close; C2 axiom baseline byte-identical to its pre-task value.
- [ ] C3: zero structural `sorry` — no new sorry introduced by any phase.
- [ ] `Tests/BimodalTest/Metalogic/PropDecideTest.lean` compiles with the two new regression examples.
- [ ] Acceptance-criterion-1 command run and its output recorded, with the outcome mapped to a row of Decision D2's table.
- [ ] `#check SetMaximalConsistent.ultrafilterEquiv` elaborates; `#print axioms` on it shows no `sorryAx`.
- [ ] `grep -rn 'structure Ultrafilter' FormalSystem/ --include=*.lean | grep -v Boneyard` returns nothing.
- [ ] `grep -c 'fold_from_x' FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` returns 0.

## Artifacts & Outputs

- `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — `propDecide`-backed `*_quot` proofs.
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — `ultrafilterEquiv`, `Multiset.inf`-based
  `fold_le_of_derives`, `BAUltrafilter`, Mathlib bridge `Equiv`.
- `FormalSystem/Metalogic/Algebraic/README.md` — refreshed, with "Last verified" stamp and the
  Decision D1 rationale.
- `Tests/BimodalTest/Metalogic/PropDecideTest.lean` — corrected docstring, De Morgan and
  distributivity regressions.
- `FormalSystem/Metalogic/Algebraic.lean` — docstring touch-up if it names the renamed type.
- `specs/528_algebraic_modernisation_propdecide_mathlib_filters/summaries/01_*-summary.md` —
  execution summary, including the acceptance-criterion-1 measurement and any Reasoned Exclusions.

## Rollback/Contingency

- Every phase is a separate commit (or atomic batch), so `git revert` of a phase's commit range
  restores the prior state without touching other phases.
- **Phase 1 import addition**: if adding the `PropDecide` import creates a cycle the planning greps
  missed, revert that single commit; Phases 3-8 are unaffected and the task still delivers items
  2-5 of the acceptance criteria.
- **Phase 2 failure**: retain the existing 39-line `sup_le_quot`, close
  `[COMPLETED WITH EXCLUSIONS]`, and record ~136 as the measured figure per Decision D2.
- **Decision D1 reversal**: if the user chooses option (a) after seeing this plan, Phases 6 and 7 are
  replaced wholesale; Phases 1-5 and 8 stand unchanged. Estimated +6 to +10 hours.
- **C2 drift at any phase**: HARD STOP. Do not re-baseline. Revert the phase's commits, report the
  divergence with the `#print axioms` diff, and mark the task `[BLOCKED]`.
