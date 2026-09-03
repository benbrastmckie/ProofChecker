# Implementation Plan: Algebraic/ Modernisation (propDecide, Mathlib Prime Filters)

- **Task**: 528 - Algebraic/ modernisation: `propDecide` in `BooleanStructure.lean`,
  `SetMaximalConsistent.ultrafilterEquiv` as a named `Equiv`, the bespoke `Ultrafilter` structure
  replaced by a Mathlib-native prime filter, `fold_le_of_derives` over `Multiset.inf`
- **Status**: [IMPLEMENTING]
- **Effort**: 9.5 hours
- **Dependencies**: 518, 526 (both landed)
- **Research Inputs**:
  - `specs/528_algebraic_modernisation_propdecide_mathlib_filters/reports/01_algebraic-modernisation-verification.md`
  - `specs/528_algebraic_modernisation_propdecide_mathlib_filters/reports/02_pfilter-maximality-design-spike.md`
  - `specs/528_algebraic_modernisation_propdecide_mathlib_filters/reports/03_literature-source-acquisition-dossier.md`
- **Artifacts**: plans/03_algebraic-modernisation-prime-filter.md (this file)
- **Revision history**: v3 (2026-09-03) — rationale/citation refinement from report 03; option (c),
  the phase structure, phase contents and acceptance criteria are unchanged from v2. v2 (2026-09-03) —
  option (c) from report 02. v1 (2026-09-03) — from report 01.
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: true

## Overview

`FormalSystem/Metalogic/Algebraic/` carries ~430 lines of hand-built Boolean-algebra derivations
and a bespoke seven-field `Ultrafilter` structure that shadows Mathlib's. The Jonsson-Tarski
representation front builds directly on this layer and would otherwise inherit both. This plan
modernises the layer in seven phases: wire the already-existing `propDecide` tactic into
`BooleanStructure.lean` and collapse the closed-tautology `*_quot` proofs onto it; extend the same
technique to the three hypothesis-driven `*_quot` lemmas; fix and extend the `propDecide` regression
tests; restate `fold_le_of_derives` over `Multiset.inf`; land a Mathlib-shaped generic prime-filter
layer under a new `FormalSystem/ForMathlib/`; port `UltrafilterMCS.lean` onto it, deleting the
bespoke structure outright and building `SetMaximalConsistent.ultrafilterEquiv` on the Mathlib type;
and refresh `Algebraic/README.md`.

Definition of done: the acceptance criteria in "Acceptance Criteria" below, with `lake build` green
and the `scripts/check-module-invariants.sh` C2 axiom baseline unchanged at every phase boundary.
**C2 drift is a HARD STOP**, never a re-baseline.

The plan is built against the three research reports' corrections, not against the task description.
Where they disagree, the later report wins. Report 03 (the literature source-acquisition dossier)
changes no design decision and no phase content; it supplies verified citations for Decisions D-A and
D-B, one pre-step for Phase 5's optional corollary, and two citable facts for Phase 7's README
subsection. Its §7 concludes that no further `--lit` research round is warranted before
implementation.

### Research Integration

Reports integrated into this plan version:

| Report | Integrated in | Role |
|--------|---------------|------|
| `reports/01_algebraic-modernisation-verification.md` | v1 | `propDecide` feasibility, `Multiset.inf` availability, the docstring defect |
| `reports/02_pfilter-maximality-design-spike.md` | v2 | Resolves Decision D1 as option (c); corrects the `ultrafilterEquiv` target type; supplies already-compiled code |
| `reports/03_literature-source-acquisition-dossier.md` | **v3 (this plan)** | Replaces the unsourced "community convention" in D-A with verified project-tree citations; records the `abbrev`-subtype vs `SetLike`-template trade-off in D-B; adds an upstream-diff pre-step to Phase 5's optional corollary; supplies textbook and Mathlib-coverage citations for Phase 7's "Design decisions" subsection; concludes (§7) that no further `--lit` round is warranted before implementation |

Findings from report 01 that still shape this plan, unchanged from v1:

- **The core `propDecide` claim is empirically verified, not inherited.** Two scratch `example`s
  were added to `BooleanStructure.lean`, a real `lake build` was run, both compiled, and the tree
  was reverted clean. The exact `le_sup_inf_quot` distributivity shape closes under
  `induction … using Quotient.ind; rename_i …; change Derives …; unfold Derives; propDecide`, and
  De Morgan closes via `and`/`or` directly with no manual unfolding.
- **Only ~10 of the 15 `*_quot` lemmas fit the bare pattern.** `propDecide`'s
  `tautologyDerivableFc'` mechanism proves *closed* schematic tautologies; its only input is the
  reified goal formula, so it cannot consume a hypothesis derivation as a side premise.
- **Three lemmas are hypothesis-driven** (`le_trans_quot`, `le_inf_quot`, `sup_le_quot`) and need
  the tautology + `Combinators.pairing` + `modus_ponens` extension. `le_antisymm_quot` proves an
  *equality* via `Quotient.sound` and is not `Derives`-shaped at all.
- **The `LindenbaumQuotient.provEquiv_*` congruence extension resolves to "nothing fits."** Every
  non-trivial congruence is conditional on a `≈ₚ` hypothesis rather than a closed tautology.
- **The `Finset` detour for `fold_le_of_derives` is unnecessary.** `Multiset.inf`,
  `Multiset.inf_coe`, `Multiset.le_inf`, and `Multiset.inf_le` all exist as auto-generated
  `@[to_dual]` duals of `Multiset.sup`, requiring only `[SemilatticeInf α] [OrderTop α]`.
- **`PropDecideTest.lean`'s De Morgan docstring is verified wrong.** `PropDecide.reify`'s `whnf`
  call unfolds `and`/`or`/`neg` automatically and the report closed the De Morgan goal directly.
- **Line-anchor correction (feasibility unchanged).** After `unfold Derives` the goal is
  `Derivable`-shaped, so dispatch reaches `PropDecide.extractDerivableGoal` at `PropDecide.lean:100`.

Findings from report 02 that reshape this plan:

- **Mathlib's `Ultrafilter α` extends `Filter α` — it is an ultrafilter on `Set α`, not on an
  arbitrary Boolean algebra.** `≃ Ultrafilter LindenbaumAlg` (task description, v1 Phase 4,
  report 01 item 2) is therefore mathematically wrong; it would only typecheck by shadowing, the
  exact hazard this task exists to remove.
- **`Order.PFilter.IsPrime` alone is ultrafilter-hood on a Boolean algebra.** Its single field
  `compl_ideal : IsIdeal (F : Set P)ᶜ` bundles `IsIdeal.Nonempty`, so `IsPrime` implies proper
  (`IsPrime.toIsProper`, 3 lines). The gap is **not** `IsProper`, and no phase budget is spent
  treating `IsProper` as a prerequisite.
- **All seven bespoke fields derive; none resisted.** `carrier`/`mem_of_le`/`inf_mem`/`top_mem`
  come straight from Mathlib; `bot_not_mem`/`compl_or`/`compl_not` are 3 + 6 + 2 new lines.
- **The bridge v1 would have hand-written already exists in Mathlib**: for `U : PrimeFilter P`,
  `U.2.toPrimePair.I` is the complement ideal (`Order/PrimeIdeal.lean:207`), which on a Boolean
  algebra is exactly `{a | aᶜ ∈ U}`.
- **The 1,071-line consumer ports mechanically.** The hardest site, the 100-line
  `ultrafilterToSet_mcs`, ported by textual substitution with **zero proof-step changes**; the five
  `mcsToSet_*` witness lemmas are reused as-is.
- **~60 duplicated lines collapse to three.** The `LeftInverse` half of `ultrafilter_correspondence`
  (`:782`) and the whole of `ultrafilter_mcs_round_trip` (`:983`) each hand-prove
  `toQuot φ ∈ mcsToSet Γ → φ ∈ Γ`; with Core's `implication_property`
  (`Core/MCSProperties.lean:160`) and `theorem_in_mcs` (`Core/MaximalConsistent.lean:462`) already
  imported, it is a 3-line `toQuot_mem_mcsToSet_iff`.
- **The generic layer and the project port already exist, compiled and sorry-free**, in report 02's
  Appendix A (202 lines: 163 generic + 39 bundling) and Appendix B (160 lines). Evidence log in
  Appendix C: E1/E2/E3 each exit 0; `#print axioms` on `ultrafilterEquiv` and
  `IsProper.exists_le_prime` show only `propext, Classical.choice, Quot.sound`.

Findings from report 03 that refine this plan's rationale (none changes a decision, a phase, or an
acceptance criterion):

- **D-A's "community convention" is now sourced.** Report 03 §2.2 verified, by fetching the
  repository trees on 2026-09-03, that `teorth/pfr` uses `PFR/ForMathlib/…`,
  `UCSCFormalMethods/LeanLTL` uses `LeanLTL/ForMathlib.lean`, `leanprover-community/sphere-eversion`
  uses `SphereEversion/ToMathlib/…`, and `ImperialCollegeLondon/FLT` uses `FLT/Mathlib/…`. The
  convention exists and is dominant but has three spellings; `ForMathlib/` is the right one. The
  Mathlib style guide itself (`contribute/style.html`, fetched) says nothing about downstream
  `ForMathlib` files — the convention is **project precedent, not a Mathlib rule**.
- **D-B's `abbrev` subtype departs from Mathlib's bundled-subobject template.**
  `Data/SetLike/Basic.lean:33-74` prescribes a `structure` with a `carrier`, a `SetLike` instance,
  `PartialOrder := .ofSetLike`, an `@[ext]` lemma, and a `copy` constructor; `Order/Ideal.lean:114`
  follows it, and `PrimeSpectrum` (`RingTheory/Spectrum/Prime/Defs.lean:28-36`) is a `structure`
  with `equivSubtype` at `:69` as a *bridge to* the subtype, not as the definition. This is a
  seen-and-accepted trade-off for a project-local type; it does not change option (c) and does not
  block Phase 5.
- **Upstream `Order/PrimeSeparator.lean` moved after the pin.** Its last commit is 2026-08-24
  (`79d0395a` is earlier); the `TODO: Define prime filters in Mathlib … := by sorry` at `:124-126`
  was still open on 2026-09-03. Phase 5's optional E3 corollary must diff upstream master against
  the pinned copy before assuming the TODO's exact statement.
- **The corpus owns a textbook statement of Stone representation in prime-filter vocabulary.**
  `chagrovzakharyaschev_1997_modallogic` Part III §8.2 (printed pp. 241-243), Theorem 8.14, defines
  the Stone space as the set of prime filters and invokes Corollary 7.42 (prime-filter separation).
  It is registered in `specs/literature-index.json` with a `relevance` note as of 2026-09-03. It is
  DJVU-derived OCR — a locator only; read the page images for any formula.
- **The pinned Mathlib has no Stone representation theorem and no Priestley duality.**
  `Order/Birkhoff.lean:40` scopes itself to finite Stone duality; `Topology/Order/Priestley.lean`
  defines only the `PriestleySpace` mixin; `Order/PrimeSeparator.lean:14-16` (van Gool, 2024)
  states its purpose as "a crucial ingredient to Stone's duality for bounded distributive
  lattices". The `ForMathlib` layer is therefore the natural next brick in a direction a Mathlib
  author has already begun — which raises the value of keeping Appendix A PR-shaped.
- **No further `--lit` round is warranted** (report 03 §7): D-A/D-B/D-C are decided by Mathlib
  source, Mathlib convention documents, and downstream-project precedent, none of which a book in
  the corpus or on the shortlist would change. Report 03's acquisition recommendations (§4, §6) are
  foundation work scheduled beside other tasks, not a gate on this plan.

### Facts established during planning that neither report measured

Checked while sizing phases; each changes a scope estimate or a risk. Items 1-8 are carried forward
from v1 (still current); items 9-11 were new to v2 and are unchanged in v3, which adds none.

1. **The `*_quot` baseline is 286 proof-body lines under a defined metric** (see "Acceptance
   Criteria" for the metric and the exact command). Report 01's "~430 lines" is the whole-file
   figure (441). The per-lemma inclusive proof-body spans are: `le_refl_quot` 4, `le_trans_quot` 6,
   `le_antisymm_quot` 5, `inf_le_left_quot` 8, `inf_le_right_quot` 8, `le_inf_quot` 13,
   `le_sup_left_quot` 11, `le_sup_right_quot` 13, `sup_le_quot` 39, `bot_le_quot` 6,
   `le_top_quot` 12, `le_sup_inf_quot` 110, `inf_compl_le_bot_quot` 28, `top_le_sup_compl_quot` 14,
   `sup_comm_quot` 9.
2. **The "under 100 lines" bar is tighter than report 01's 95-110 estimate.** Summing optimistic
   post-refactor targets gives **~109**, not under 100 — see Decision D2.
3. **`Ultrafilter`'s 16 hits in `Metalogic/Bundle/LimitMCS.lean` are Mathlib's `Ultrafilter`,
   not the bespoke one.** `LimitMCS.lean` imports `Mathlib.Order.Filter.Ultrafilter.Basic` and never
   imports any `Metalogic.Algebraic` module. The same holds for the `Semantics/Ultraproduct/` hits
   and the two prose mentions in `Chronicle/ChronicleRealExtension.lean`. This must still be
   re-verified per-declaration at implementation time, not assumed.
4. **The bespoke `Ultrafilter`'s only non-`UltrafilterMCS.lean` consumers are four Boneyard files,
   all behind `#exit`.** `Boneyard/UltrafilterFrame/{AlgebraicCompleteness,UltrafilterFrame}.lean`
   and `Boneyard/StrictSemanticsLegacy/Algebraic/UltrafilterChain.lean` import
   `Algebraic.UltrafilterMCS`, and `Boneyard/UltrafilterFrame/TenseS5Algebra.lean` imports
   `Algebraic.BooleanStructure` — each with its `#exit` at lines 27, 54, 46, and 37 respectively,
   *before* every `open`/`Ultrafilter` occurrence. **Deleting** the structure therefore cannot break
   them (invariant C11 checks their *import* lines, and no module is renamed).
5. **`UltrafilterMCS.lean` is itself the layer's largest consumer**: 63 `Ultrafilter` occurrences
   and 46 `carrier` occurrences across 1,071 lines.
6. **`fold_le_of_derives` has exactly one call site**, at `UltrafilterMCS.lean:718`, in the same
   file. Zero external references (grep, live tree). Note that `:718` falls *inside* the
   `:674-773` span of `ultrafilterToSet_mcs`, the site Phase 6 rewrites — hence the file-ownership
   serialization between Phases 4 and 6.
7. **`Combinators.pairing` exists** at `Theorems/Combinators.lean:555` with signature
   `⊢[fc] A.imp (B.imp (A.and B))`, and `DerivationTree.modus_ponens` is already used inside
   `BooleanStructure.lean`. The Phase 2 extension needs no new imports.
8. **The `Algebraic/README.md` "Last verified" stamp is genuinely absent**; the file ends with
   `*Last updated: 2026-08-26*`. The house convention is visible at
   `FormalSystem/BaseLanguage/README.md:69` (`**Last verified**: YYYY-MM-DD`) and
   `FormalSystem/Automation/README.md:107` (`*Last verified: YYYY-MM-DD*`).
9. **The Lake root aggregator is `FormalSystem/FormalSystem.lean`, not the repo-root
   `FormalSystem.lean`.** The root file contains only `import FormalSystem.FormalSystem`; the
   eight real submodule imports live in `FormalSystem/FormalSystem.lean:8-15`. Report 02 §8.1 says
   "`FormalSystem.lean` gains `import FormalSystem.ForMathlib`" without disambiguating. The new
   import belongs in **`FormalSystem/FormalSystem.lean`**; Phase 5 re-verifies this rather than
   inheriting it.
10. **C8's aggregator scan covers only the immediate children of `FormalSystem/` and
    `FormalSystem/Metalogic/`** (`check-module-invariants.sh`, the `for parent in ("FormalSystem",
    "FormalSystem/Metalogic")` loop). So `FormalSystem/ForMathlib.lean` beside
    `FormalSystem/ForMathlib/` is **required** by C8; a nested `FormalSystem/ForMathlib/Order.lean`
    beside `ForMathlib/Order/` is **not** checked by C8 and is a house-style choice, not an
    invariant obligation. Report 02's parenthetical ("C8 requires a sibling for every immediate
    subdirectory of `FormalSystem/`") is correct as written but is easy to over-read.
11. **`FormalSystem/README.md` carries three separate enumerations that a new top-level directory
    touches**: an aggregator/line-count table (`:219-226`), a layer table (`:247-257`), and a
    subdirectory/README table (`:273-276`). Report 02 §8.1 names only the root `CLAUDE.md` and
    `.claude/context/repo/project-overview.md`. Phase 5 must find every such enumeration by
    re-reading, not by inheriting this list. Separately, **`.claude/` is gitignored in this repo**
    and `context/repo/project-overview.md` is listed in `.syncprotect`, so the project-overview
    line is a safe but non-tracked, optional courtesy edit — the load-bearing, repo-tracked doc
    edits are `CLAUDE.md` and `FormalSystem/README.md`.

### Prior Plan Reference

**This plan supersedes `plans/02_algebraic-modernisation-prime-filter.md` (v2), which superseded
`plans/01_algebraic-modernisation-propdecide-mathlib.md` (v1).** No phase of v1 or v2 was ever
executed — every phase was `[NOT STARTED]` — so nothing is preserved-because-completed and nothing
is discarded that had been done.

What changed from v2 to v3, and why — a rationale/citation refinement, not a redesign. Option (c),
the phase structure, every phase's tasks, timing, tier, commit mode, scope hypothesis and
verification, and all seven acceptance criteria are carried forward verbatim:

| v2 | v3 | Why |
|----|----|-----|
| Decision D-A cites "the community's standard signal" (unsourced) | D-A cites four verified project trees (`teorth/pfr`, `UCSCFormalMethods/LeanLTL`, `leanprover-community/sphere-eversion`, `ImperialCollegeLondon/FLT`, all checked 2026-09-03) and records that the Mathlib style guide is silent on downstream `ForMathlib` files | Report 03 §2.2: the convention is project precedent, not a Mathlib rule, and should be cited as such |
| Decision D-B says the subtype is "lighter than Mathlib's `PrimeSpectrum`-style bundled structure" | D-B records the `abbrev`-subtype vs `SetLike`-template trade-off as seen and accepted, and names it as the one predictable upstream-review pushback point | Report 03 §2.2 (Finding 2.3): `Data/SetLike/Basic.lean:33-74`, `Order/Ideal.lean:114`, `RingTheory/Spectrum/Prime/Defs.lean:28-36,69`. The `abbrev` stays |
| Phase 5 optional E3 corollary assumes the pinned `Order/PrimeSeparator.lean:123-125` TODO | A pre-step diffs upstream master (last commit 2026-08-24, after the pin) against the pinned copy first | Report 03 §2.2 and Recommendation 6 |
| Phase 7 "Design decisions" subsection cites only Mathlib source | May additionally cite Chagrov-Zakharyaschev Part III §8.2, Theorem 8.14 (the textbook statement in prime-filter vocabulary) and may note that the pinned Mathlib has no Stone representation or Priestley duality | Report 03 §2.3 and §3.2; the CZ entry now carries a `relevance` note in `specs/literature-index.json` |
| Research Integration lists reports 01-02 | Lists reports 01-03 and records report 03 §7's verdict that no further `--lit` round is warranted | Report 03 Recommendation 1 |

What changed from v1 to v2, and why (unchanged from v2's own record):

| v1 | v2 | Why |
|----|----|-----|
| **Decision D1 open**, defaulting to option (b): rename `Ultrafilter` → `BAUltrafilter` and hand-write a bridge `Equiv` to `{I : Order.Ideal α // I.IsMaximal}` | **D1 RESOLVED as option (c)** (2026-09-03): encode as a Mathlib-native prime filter; no bridge lemma is written | The design spike verified option (c) by real compiles. It lands at v1's Phase 6+7 budget, leaves **one** representation in the tree instead of two, and writes **zero** bridge lemmas — the bridge v1 would have hand-written is Mathlib's `IsPrime.toPrimePair`. Measured against the user's standard (long-term infrastructure of the highest quality, avoiding bridge lemmas, systematic refactoring toward a stronger foundation), (c) dominates (b) on every axis at equal cost. |
| Target type `≃ Ultrafilter LindenbaumAlg` | Target type `≃ Order.PrimeFilter LindenbaumAlg` | v1's type is **mathematically wrong**: Mathlib's `Ultrafilter α extends Filter α` is a filter on `Set α`, not an ultrafilter of an arbitrary Boolean algebra. Acceptance criterion 3 is restated accordingly. |
| Non-Goal: "the `Order.PFilter` / `Order.Ideal.ofPFilterCompl` encoding is dropped, not deferred" | **Withdrawn.** `PFilter` is now the chosen encoding | Report 01 drew the wrong conclusion from a correct fact. `Order.Ideal.ofPFilterCompl` genuinely does not exist and Mathlib genuinely has no `PFilter.IsMaximal` — but `Order.PFilter.IsPrime` does exist and is *already sufficient* on a Boolean algebra. |
| A phase budget shaped around supplying `IsProper` as the missing prerequisite | No such budget | `IsPrime.toIsProper` is a 3-line instance derived from `IsPrime`'s own `compl_ideal.Nonempty` field. `IsProper` is a consequence, not a prerequisite. |
| **Phase 4** (build `ultrafilterEquiv` on the bespoke type) | **Absorbed into Phase 6** | The `Equiv` must be built *on* the new type. Building it on the old type first and re-typing it later is pure churn. |
| **Phase 6** (rename to `BAUltrafilter`) + **Phase 7** (hand-written bridge `Equiv`) | **Phase 5** (land the generic `ForMathlib` layer) + **Phase 6** (port the consumer) | Report 02 §12's 6′/7′ phase group, sized and ordered as that section gives them. |
| v1 Phases 1, 2, 3, 5, 8 | **v2 Phases 1, 2, 3, 4, 7** — substantively intact, renumbered | The `propDecide` work, the test-docstring fix, the `Multiset.inf` restatement, and the README refresh are unaffected by D1 and were well-founded. |
| Effort 12 h | Effort 9.5 h | The absorbed Phase 4 (1.5 h) disappears, and the D1 group's proof-discovery cost is already spent (report 02 Appendices A/B). Not an optimism adjustment — a scope reduction with compiled evidence behind it. |
| Decision **D2 open** | **Decision D2 remains open, unchanged** | The user has not ruled on the `*_quot` line-count bar. The D1 resolution does not bleed into it. |

Also carried forward from v1 unchanged: every phase's own Verification Tier, Commit Mode, Scope
Hypothesis, "Files to modify" list, and green criteria; and the per-declaration re-verification
discipline (any phase asserting something is dead, unused, or mechanically rewritable makes
verification with recorded grep output its literal *first* task, and each Scope Hypothesis names
the smaller verified reading plus the fallback if it fails). That discipline came from a sibling
task closing with five exclusions and a missed line target; it is retained deliberately.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as a roadmap input for this dispatch and carries no
item naming the algebraic layer, `propDecide`, or the ultrafilter correspondence. No roadmap phases
are added and ROADMAP.md is not modified.

## Goals & Non-Goals

**Goals**:
- Collapse the closed-tautology `*_quot` proofs in `BooleanStructure.lean` onto `propDecide`.
- Extend the same technique to the three hypothesis-driven `*_quot` lemmas via
  tautology + `Combinators.pairing` + `modus_ponens`.
- Correct the verified-wrong `PropDecideTest.lean` De Morgan docstring and add De Morgan and
  distributivity regression cases.
- Restate `fold_le_of_derives` over `((L.map toQuot : List _) : Multiset _).inf`, removing the
  hand-rolled `fold_from_x` reassociation `have`.
- Land a Mathlib-shaped generic prime-filter layer at `FormalSystem/ForMathlib/Order/PFilter.lean`
  in namespace `Order.PFilter`, supplying the `IsProper`/`IsMaximal`/Boolean-section API Mathlib
  lacks on the filter side.
- **Delete** the bespoke `structure Ultrafilter` and port `UltrafilterMCS.lean` onto
  `Order.PrimeFilter LindenbaumAlg`, with `SetMaximalConsistent.ultrafilterEquiv` built on the
  Mathlib type and `ultrafilter_correspondence` derived from it as a corollary.
- Refresh `Algebraic/README.md`, including a "Last verified" stamp and the D1 rationale.

**Non-Goals**:
- **The `LindenbaumQuotient.provEquiv_*` congruence extension is explicitly out of scope.** Report
  01 read all nine congruence lemmas and found every non-trivial one is conditional on a `≈ₚ`
  hypothesis rather than a closed tautology (`provEquiv_box_congr` needs `necessitation`,
  `provEquiv_all_past_congr` needs `Perpetuity.pastMono`); the one that would fit, `derives_refl`,
  is already a 3-line proof via `Combinators.identity`. "Where it fits" resolves to "nowhere
  non-trivial fits." No phase budget is allocated.
- **`le_antisymm_quot` is explicitly excluded from the `propDecide` rewrite.** Its conclusion is an
  equality proved by `Quotient.sound`, not a `Derives`/`Derivable` goal. It stays at 5 lines.
- **No `Lattice (PFilter P)` is supplied.** Mathlib gives `PFilter` no lattice
  (`Max (PFilter P)` does not exist; `Ideal` has one under `[SemilatticeSup P]
  [IsCodirectedOrder P]`, `Order/Ideal.lean:390`). The downstream ultrafilter-frame work will need
  `F ⊔ principal x` and can get it as a five-line dual transport `⟨F.dual ⊔ G.dual⟩` — but that
  transport is **not** written here. Phase 7 records the gap in the README so the next consumer
  meets it as a documented five-line job, not a surprise.
- **No upstream Mathlib PR is opened by this task.** Report 02 §9 establishes that the generic
  layer is PR-shaped and that upstream master (fetched 2026-09-03) still lacks all of it. The PR
  shape is preserved as a *property the phases must not break* (namespace `Order.PFilter`, lemma
  names one-for-one with their `Order/Ideal.lean` duals, `*_iff_dual` for transports, no
  `FormalSystem.*` import under `ForMathlib/`), which costs nothing extra. Submitting it is
  separate work.
- No changes to `FlowFrame.lean` or `InteriorOperators.lean` beyond whatever the port mechanically
  requires (expected: none — neither references the bespoke `Ultrafilter`).
- No Jonsson-Tarski representation work. This task only removes the obstacles.
- No new `sorry` anywhere. C3 (zero structural sorries) must stay green.

## Decisions

### Decision D1: encode as a Mathlib-native prime filter — RESOLVED, option (c) [RESOLVED 2026-09-03]

**Chosen**: delete the bespoke `structure Ultrafilter` and encode Boolean-algebra ultrafilters as
`Order.PrimeFilter P := {F : Order.PFilter P // F.IsPrime}`, supplying the missing
`IsProper`/`IsMaximal`/Boolean-section API in a Mathlib-shaped `ForMathlib/` file.

**Rationale**: the design spike (`reports/02_pfilter-maximality-design-spike.md`) verified option
(c) by real compiles against the pinned tree (Lean `v4.33.0-rc1`, Mathlib `79d0395a`). Against the
user's stated standard — long-term infrastructure of the highest quality, avoiding bridge lemmas,
preferring systematic refactoring toward a stronger foundation, with mathematical virtue and
clarity primary — (c) dominates:

| | (a) Ideal-side replacement | (b) `BAUltrafilter` + bridge (v1 default) | **(c) `PFilter` + `IsPrime` (chosen)** |
|---|---|---|---|
| Representations left in tree | 1 (ideal) | **2** (bespoke + Mathlib, joined by a lemma) | **1** (Mathlib) |
| Bridge lemmas hand-written | the complement flip *is* the bridge | 1 hand-written `Equiv` | **0** — the ideal is `IsPrime.toPrimePair` |
| Downstream `η`, `R_G`, `R_Box`, `R_H` | complement on both sides | verbatim, but on a non-Mathlib type | verbatim, on a Mathlib type |
| New generic code | 0 | ~50 lines, to be written | ~200 lines, **already compiled** (report 02 Appendix A) |
| Consumer work | full re-derivation, "several agent runs" | rename ~63 sites | substitution pass ~110 sites, **zero proof-step changes** |
| Cost | +6 to +10 h over (b) | 3.5 h | **≈ 3.5 h** |

Option (b)'s decisive defect is the second row of that table read together with the third: it pays
for a hand-written bridge in order to keep a bespoke type that Mathlib already subsumes, and the
bridge it writes by hand is a Mathlib projection. Option (a)'s defect is the fourth row of §3 of the
spike: its duality is the Boolean complement, not the order dual, so it inverts every downstream
statement — an ergonomic tax on precisely the consumers this task exists to serve.

**Rejected alternatives**: (a) replace with `{I : Order.Ideal α // I.IsMaximal}` — rejected for the
complement inversion; (b) `BAUltrafilter` + hand-written bridge — rejected for leaving two
representations and writing by hand what Mathlib supplies.

### Decision D-A: location of the generic layer — `FormalSystem/ForMathlib/Order/PFilter.lean` [RESOLVED 2026-09-03]

**Chosen**: a new top-level `FormalSystem/ForMathlib/` directory holding
`ForMathlib/Order/PFilter.lean`, with the C8-required sibling aggregator
`FormalSystem/ForMathlib.lean`, in namespace **`Order.PFilter`** — exactly Mathlib's, so that when
the layer is upstreamed the file is deleted and no consumer changes a name.

**Rationale**: the layer is about arbitrary preorders, distributive lattices and Boolean algebras.
Nothing in it mentions formulas, derivations or `LindenbaumAlg`. The `ForMathlib/` convention is
the dominant downstream-project signal for "Mathlib-shaped, intended to be deleted on upstreaming",
and the user's standard for this task is upstream-bound infrastructure. Its cost is documentation
lines; its benefit is that the "this is a Mathlib extension" signal is explicit and the dependency
rule (nothing under `ForMathlib/` imports `FormalSystem.*`) is structurally visible.

**Sources for the convention** (report 03 §2.2; repository trees fetched and verified 2026-09-03):

| Project | Location of Mathlib-bound code |
|---------|--------------------------------|
| `teorth/pfr` | `PFR/ForMathlib/…` |
| `UCSCFormalMethods/LeanLTL` | `LeanLTL/ForMathlib.lean` |
| `leanprover-community/sphere-eversion` | `SphereEversion/ToMathlib/…` |
| `ImperialCollegeLondon/FLT` | `FLT/Mathlib/…` (mirroring Mathlib's own directory tree beneath it) |

The convention has three spellings; `ForMathlib/` is the most common and is the one adopted. **The
Mathlib style guide itself says nothing about downstream `ForMathlib` files** (`contribute/style.html`
fetched and confirmed absent) — this is project precedent, not a Mathlib rule, and the plan cites it
as such. **Dependency rule**, restated as the invariant Phase 5 enforces: nothing under
`FormalSystem/ForMathlib/` imports the project; the import direction is strictly
`Mathlib → ForMathlib → Metalogic/Algebraic/UltrafilterMCS → downstream`.

**Rejected alternative**: `FormalSystem/Metalogic/Algebraic/PrimeFilter.lean`, project-local, same
namespace, no new directory. Cheaper on documentation (no new `CLAUDE.md` / `FormalSystem/README.md`
rows, no aggregator, no root import), and C8 accepts it. Rejected because it files a
Boolean-algebra fact under the logic's metatheory — the same category error the bespoke
`Ultrafilter` structure made — and leaves the upstreaming intent implicit.

### Decision D-B: the bundled type is `Order.PrimeFilter` [RESOLVED 2026-09-03]

**Chosen**: `abbrev Order.PrimeFilter (P) [Preorder P] := {F : PFilter P // F.IsPrime}`, with
`SetLike`, an `IsPrime` instance projection, `mem_iff`, and an `@[ext]` lemma.

**Rationale**: honest on any preorder, equal to the ultrafilters on a Boolean algebra (say so in the
docstring). The subtype form is lighter than Mathlib's `PrimeSpectrum`-style bundled structure and
needs no `ext` boilerplate of its own. Downstream statements read exactly as the archived
ultrafilter-frame seed writes them (`x ∈ U`, `PFilter.inf_mem hx hy`, `U.2.mem_or_compl_mem`), and
`def eta (a : P) : Set (PrimeFilter P) := {U | a ∈ U}` compiles as written.

**Seen-and-accepted trade-off: `abbrev` subtype vs Mathlib's `SetLike` template** (report 03 §2.2,
Finding 2.3). Mathlib's prescriptive template for a bundled subobject (`Data/SetLike/Basic.lean:33-74`)
is a `structure` with a `carrier` field, a `SetLike` instance, `PartialOrder := .ofSetLike`, an
`@[ext]` lemma, and a `copy` constructor "to fix definitional equalities". `Order/Ideal.lean:114`
follows it (`instance : PartialOrder (Ideal P) := .ofSetLike (Ideal P) P`), and `PrimeSpectrum`
(`RingTheory/Spectrum/Prime/Defs.lean:28-36`) is likewise a `structure`, supplying
`equivSubtype : PrimeSpectrum R ≃o {I : Ideal R // I.IsPrime}` (`:69`) as a *bridge to* the subtype
rather than as the definition. The `abbrev` subtype chosen here departs from that template. For a
**project-local type** this is defensible and is accepted: it costs no boilerplate, and every
downstream statement reads as the ultrafilter-frame seed already writes it. It is, however, **the one
place where a Mathlib reviewer would predictably push back on upstreaming**, and therefore the most
likely spot where the bundling half of report 02 Appendix A (the 39-line `Order.PrimeFilter` block)
would be reshaped into a `structure` + `equivSubtype` in a PR. This is not a reversal: the `abbrev`
stays; the generic 163-line half of Appendix A is unaffected either way; and Phase 5's task list is
unchanged. The trade-off is worth one sentence in the file's module docstring so the implementer and
any future PR author see it was chosen, not overlooked.

**This satisfies acceptance criterion 2's FIRST disjunct outright** — no declaration named
`Ultrafilter` survives outside Mathlib in the live tree — so **no documented exception is needed**,
and none should be written.

**Rejected alternative**: keep a project-namespaced `Ultrafilter` abbrev for readability. Rejected:
it reintroduces exactly the shadow this task exists to remove.

### Decision D-C: define `IsMaximal` — yes [RESOLVED 2026-09-03]

**Chosen**: define `Order.PFilter.IsMaximal` (~12 lines: the `@[mk_iff] class`, `isMaximal_iff_dual`,
`IsProper.exists_le_maximal`) even though `IsPrime` alone suffices for ultrafilter-hood on a Boolean
algebra.

**Rationale**: `IsMaximal` is the transport target for `Order.Ideal.IsProper.exists_le_maximal`
(`Order/Ideal.lean:642`) — i.e. Lindenbaum's lemma on the filter side, the concrete payoff for the
Jonsson-Tarski front — and it is what a Mathlib PR mirroring the ideal file must contain (report 02
§9, PR shape item 1). It is deliberately **not** put in the type: the type's predicate is `IsPrime`.

**Rejected alternative**: `IsProper` + `IsPrime` only, with `exists_le_prime` proved by inlining the
transport. Saves 12 lines, loses the general-lattice statement and breaks the PR shape.

## Open Decisions

One decision remains open. It has a plan default so implementation is never blocked.

### Decision D2 [OPEN]: what "under 100 lines" means, and what the bar comes to if Phase 2 is hard

**The user has not ruled on this. It is unchanged from v1 and the D1 resolution does not touch it.**

The acceptance criterion "BooleanStructure.lean's `*_quot` lemmas total under 100 lines" needs a
metric before it can be checked. The plan adopts: **the sum of inclusive proof-body spans (theorem
declaration line through last proof line) for all 15 `*_quot` theorems, excluding leading docstrings
and section comments** — the exact command is in "Acceptance Criteria" below.

Under that metric the measured baseline is **286**. Projected outcomes:

| Scenario | Projected total | Under 100? |
|----------|-----------------|------------|
| Phase 1 only (10 tautology lemmas rewritten, ~7 lines each) | ~147 | No |
| Phases 1 + 2, optimistic (`sup_le_quot` 39→~12, `le_inf_quot` 13→~10, `le_trans_quot` unchanged at 6) | **~109** | **No — narrowly** |
| Phases 1 + 2 + per-lemma line-shaving (inline `Quotient.ind` binders via `with \| _ φ =>`, saving one `rename_i` line on each of ~10 lemmas) | **~99** | **Yes — knife-edge** |
| Phase 2 fails on `sup_le_quot` only | ~136 | No |
| Phase 2 fails on all three hypothesis-driven lemmas | ~139 | No |

So: the bar is reachable, but only with **both** the Phase 2 extension **and** the line-shaving, and
the margin is a single line. Report 01's "achievable but tight" is if anything optimistic.

**Recommendation**: treat **under 100 as the stretch target** and **≤ 115 with the measured number
recorded in the phase's completion note as the accept bar**. Churning on formatting to buy the last
ten lines is not a good use of an agent run, and a `[COMPLETED WITH EXCLUSIONS]` close on Phase 2
recording the measured figure is the honest outcome if it lands in 100-115. The final call on the
bar is the user's; implementation must not silently relax it, and must not silently claim it either.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The new `BooleanStructure.lean` → `Automation.Tactics.PropDecide` import edge creates a cycle | H | L | Report 01 verified by grep that nothing under `Metalogic/Decidability/`, `Metalogic/Core/`, or `Theorems/` imports any `Algebraic.*` module; re-confirmed at plan time. Phase 1's first task re-runs the grep and adds the import in isolation with a build before touching any proof. |
| The "under 100 lines" bar is missed | M | **H** | Decision D2 states the arithmetic and the accept-bar recommendation up front. Phase 2 measures and records rather than churning. |
| The Phase 2 pairing+MP extension does not close `sup_le_quot` | M | M | Phase 2's first task is a single-lemma spike on `sup_le_quot` before touching the other two; if the spike fails, the phase closes `[COMPLETED WITH EXCLUSIONS]` with the existing 39-line proof retained and D2's "fails on `sup_le_quot` only" row (~136) recorded. |
| A "dead"/"unused" scope assumption fails on re-verification (the sibling task's failure mode: five Reasoned Exclusions, line target missed) | M | M | Every phase that asserts something is unused makes per-declaration re-verification its **first task**, with the grep recorded in the phase's completion note. Scope hypotheses in this plan are deliberately stated smaller than the optimistic reading. |
| The new `ForMathlib` module is invisible to the aggregator and C6/C7 count it unreachable | M | M | Phase 5 re-verifies which file is the Lake root aggregator (planning found `FormalSystem/FormalSystem.lean:8-15`, **not** the repo-root `FormalSystem.lean`) before adding the import, and runs the **full** invariant script (not `--no-build`) so C6's reachability and compile-check both fire. |
| C8 fails for want of the `ForMathlib.lean` sibling aggregator | M | L | Planning read C8's implementation: it scans only immediate children of `FormalSystem/` and `FormalSystem/Metalogic/`, so `FormalSystem/ForMathlib.lean` is required and `ForMathlib/Order.lean` is optional. Phase 5 creates the required sibling in the same commit as the directory. |
| New Mathlib leaf imports (`Order.PrimeIdeal`, `Order.PrimeSeparator`) shift the C2 axiom baseline | H | L | C2 records `#print axioms` for four flagship theorems; new imports do not change proof terms of existing theorems, and report 02 measured the new declarations' axioms as exactly `propext, Classical.choice, Quot.sound`. Phase 5 and Phase 6 each treat any C2 delta as a HARD STOP requiring investigation, never a re-baseline. |
| Deleting the bespoke `Ultrafilter` breaks a Boneyard import (C11) | M | L | The module is **not renamed** — only declarations inside it change — so every Boneyard import line still resolves. Planning also confirmed all four Boneyard consumers place `#exit` before every `Ultrafilter` occurrence. Phase 6 re-verifies both facts before deleting. |
| The `ofDual (toDual a)` residue or the implicit-argument pin blocks the port | L | M | Both frictions were met and fixed during the spike and are pre-loaded as explicit Phase 6 tasks: `show a = toQuot φ from h_eq` for the residue (one site, in `right_inv`), `(x := toQuot φ)` for the pin (one site, in `ultrafilter_neg_iff'`). If a *third* friction appears, record it — do not silently improvise around it. |
| The `overlappingInstances` linter trips on mixed typeclass assumptions in the generic layer | L | M | Report 02 hit this once in E1 and fixed it by sectioning. Phase 5 keeps `[Preorder P]`, `[OrderBot P]`, `[DistribLattice P]`, `[BooleanAlgebra P]` in separate `section`s, as Appendix A does. |
| `Multiset.inf` restatement changes `fold_le_of_derives`'s statement in a way the single call site cannot absorb | M | L | The call site is in-file at `:718` and is edited in the same phase; the phase declares `atomic-batch` so the intermediate red state is expected. |
| Phases 4 and 6 collide in `UltrafilterMCS.lean` | M | M | They are serialized (6 depends on 4), and the ordering is deliberate: Phase 4 runs against the file's current shape, where its line anchors (`:565`, `:718`) still hold, before Phase 6's large deletions shift everything. |
| Docstring/README counts drift and fail C14; a task number leaks into `FormalSystem/` and fails C9 | M | M | Phase 5 and Phase 7 each run the full `scripts/check-module-invariants.sh` (not `--no-build`), which exercises C5, C9, C12, C13, and C14. Phase 7's task list explicitly requires durable anchors (filenames, section headings) rather than task-number citations when describing downstream consumers. |

## Acceptance Criteria

Checked at task close, not per phase.

1. **`*_quot` line total.** Metric and command:
   ```bash
   awk '/^theorem [a-zA-Z_]*_quot/ {start=NR; inproof=1; next}
        { if (inproof && ($0 ~ /^theorem |^instance |^\/--|^\/-!|^end |^@\[/)) { total += NR-start; n++; inproof=0 } }
        END { print "lemmas:", n, "total_body_lines:", total }' \
     FormalSystem/Metalogic/Algebraic/BooleanStructure.lean
   ```
   Baseline: `lemmas: 15 total_body_lines: 286`. Target: under 100 (stretch) / ≤ 115 with the
   measured number recorded (accept) — see Decision D2. The lemma count must still read 15.

2. **No `Ultrafilter` shadow — first disjunct, outright.**
   ```bash
   grep -rn 'structure Ultrafilter\|def Ultrafilter' FormalSystem/ --include=*.lean | grep -v Boneyard
   ```
   returns nothing, **and**
   ```bash
   grep -rn 'structure Ultrafilter\|namespace Ultrafilter' FormalSystem/Metalogic/Algebraic/ --include=*.lean
   ```
   returns nothing. **No documented exception is needed or permitted** — Decision D-B satisfies the
   criterion's first disjunct directly. (`Order.PrimeFilter` is not named `Ultrafilter`; the
   surviving `mcsToUltrafilter` / `ultrafilterToSet` / `ultrafilterEquiv` /
   `ultrafilter_correspondence` names are lowercase-initial and match neither grep.)

3. **`ultrafilterEquiv` exists at the corrected type and is consumed.**
   ```lean
   noncomputable def SetMaximalConsistent.ultrafilterEquiv :
       {Γ : Set Formula // SetMaximalConsistent (fc := FrameClass.Base) Γ} ≃
         Order.PrimeFilter LindenbaumAlg
   ```
   is declared, `#print axioms` on it shows no `sorryAx`, and `ultrafilter_correspondence` is
   proved **from** it rather than from scratch. *(Restated from v1, which named the mathematically
   wrong `≃ Ultrafilter LindenbaumAlg` — see report 02 §2 and §10 item 4.)*

4. **`fold_le_of_derives`** is stated over a `Multiset.inf` and the `fold_from_x` reassociation
   `have` is gone: `grep -c 'fold_from_x' FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean`
   returns 0.

5. **`lake build` green** and **`bash scripts/check-module-invariants.sh` all-pass**, with the C2
   axiom baseline unchanged. C2 drift is a HARD STOP. C6/C7/C8 must accept the new `ForMathlib`
   module as reachable and correctly aggregated; C11 must stay green.

6. **Zero new sorries** (C3 stays green).

7. **`UltrafilterMCS.lean` materially shrinks.** Report 02 §6 projects 1,071 → roughly 780 lines
   with the same theorem content plus a named `Equiv`. This is a **hypothesis to be recorded, not a
   bar to be hit** — record the measured figure in the completion note and say which way it went.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 3, 4, 5 | -- |
| 2 | 2, 6 | 1 (for 2); 4, 5 (for 6) |
| 3 | 7 | 2, 3, 6 |

Phases within the same wave can execute in parallel.

**Wave-1 territory contract** (file ownership; a phase MUST NOT write outside its own list):

| Phase | Owns |
|-------|------|
| 1 (and 2, wave 2) | `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` |
| 3 | `Tests/BimodalTest/Metalogic/PropDecideTest.lean` |
| 4 (and 6, wave 2) | `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` |
| 5 | `FormalSystem/ForMathlib.lean`, `FormalSystem/ForMathlib/Order/PFilter.lean`, `FormalSystem/FormalSystem.lean`, `CLAUDE.md`, `FormalSystem/README.md` |
| 7 | `FormalSystem/Metalogic/Algebraic/README.md`, `FormalSystem/Metalogic/Algebraic.lean` (docstring only) |

Phase 1 changes proof bodies only — no `*_quot` statement changes — so nothing else in wave 1
depends on its output. Phase 5 creates new files and edits three files no other phase touches.
Phases 4 and 6 share a file and are therefore serialized (6 depends on 4), in that order so that
Phase 4 runs against the line anchors that currently hold.

Every phase, regardless of Verification Tier, closes on: `lake build` exits 0 **and**
`bash scripts/check-module-invariants.sh` reports the C2 axiom baseline unchanged. C2 drift is a
HARD STOP: stop, report, do not re-baseline.

---

### Phase 1: Wire `propDecide` into `BooleanStructure.lean` and rewrite the closed-tautology `*_quot` lemmas [COMPLETED]

- **Goal:** `BooleanStructure.lean` imports `propDecide` with no import cycle, and every `*_quot`
  lemma whose statement is a closed propositional tautology is proved by the four-line pattern.

- **Tasks:**
  - [x] **Re-verify first**: re-run `grep -rn 'import FormalSystem.Metalogic.Algebraic' FormalSystem/ Tests/ --include=*.lean` and confirm nothing under `Metalogic/Decidability/`, `Metalogic/Core/`, `Theorems/`, or `Automation/` imports any `Algebraic.*` module. Record the output in the completion note.
  - [x] **Re-verify second**: enumerate the `*_quot` theorems and re-confirm the count is 15 and that each candidate below takes no derivation hypothesis. Record the per-declaration verdict (amenable / hypothesis-driven / not `Derives`-shaped).
  - [x] Add `import FormalSystem.Automation.Tactics.PropDecide` to `BooleanStructure.lean` and build **before** touching any proof. If the build fails, stop and report — do not work around a cycle.
  - [x] Rewrite each confirmed closed-tautology lemma as `induction … using Quotient.ind` (one per quotient argument) / `rename_i …` / `change Derives …` / `unfold Derives` / `propDecide`. Expected set: `le_refl_quot`, `inf_le_left_quot`, `inf_le_right_quot`, `le_sup_left_quot`, `le_sup_right_quot`, `bot_le_quot`, `le_top_quot`, `le_sup_inf_quot`, `inf_compl_le_bot_quot`, `top_le_sup_compl_quot`.
  - [x] Where `induction a using Quotient.ind with | _ φ =>` binds the representative inline, prefer it over a separate `rename_i` line (Decision D2's line-shaving; one line saved per lemma).
  - [x] Leave `le_antisymm_quot`, `le_trans_quot`, `le_inf_quot`, `sup_le_quot`, and `sup_comm_quot` untouched in this phase.
  - [x] Measure and record the acceptance-criterion-1 figure after the rewrite.

- **Completion note (2026-09-03):**
  - Re-verify 1 (import cycle): `grep -rn 'import FormalSystem.Metalogic.Algebraic' FormalSystem/ Tests/ --include=*.lean` —
    live importers are `Metalogic.lean`, `Metalogic/Algebraic.lean`, the intra-`Algebraic/` edges, and
    six `FlowFrame` consumers under `BXCanonical/`, `Conservativity/`, `WeakCanonical/`; the rest are
    Boneyard. Nothing under `Metalogic/Decidability/`, `Metalogic/Core/`, `Theorems/` or `Automation/`
    imports any `Algebraic.*` module; `PropDecide.lean` imports only `Decidability.Propositional.Kalmar`
    and `Automation.Tactics.Helpers`. Import added in isolation, full `lake build` exit 0 (commit `f0a75a3f0`).
  - Re-verify 2 (enumeration): 15 `*_quot` theorems. Amenable (closed tautology, no hypothesis): `le_refl_quot`,
    `inf_le_left_quot`, `inf_le_right_quot`, `le_sup_left_quot`, `le_sup_right_quot`, `bot_le_quot`,
    `le_top_quot`, `le_sup_inf_quot`, `inf_compl_le_bot_quot`, `top_le_sup_compl_quot` (10).
    Hypothesis-driven: `le_trans_quot`, `le_inf_quot`, `sup_le_quot` (3, Phase 2). Not `Derives`-shaped:
    `le_antisymm_quot` (equality via `Quotient.sound`), `sup_comm_quot` (equality via `le_antisymm`) (2).
  - All 10 rewritten with the inline-binder form `induction a using Quotient.ind with | _ φ =>` /
    `change Derives …` / `unfold Derives` / `propDecide`; each its own green commit (phase 1.2-1.11).
  - Acceptance-criterion-1 command after the phase: `lemmas: 15 total_body_lines: 139` (baseline 286;
    the plan's ~147 projection was slightly pessimistic). `git diff` shows no `theorem …_quot` signature change.
  - `bash scripts/check-module-invariants.sh` (full): see the phase-close log; C2 baseline unchanged.

- **Timing:** 2 hours
- **Depends on:** none
- **Verification Tier:** full

  *Rationale*: this phase adds an import edge into a module with downstream dependents
  (`InteriorOperators.lean`, `UltrafilterMCS.lean`, `Algebraic.lean`, and four Boneyard files
  subject to C11), which is a build-graph change, not a local one.

- **Commit Mode:** per-substep

  *Each rewritten lemma that builds green is its own commit; the import addition is a commit of its
  own, taken before any proof is touched.*

- **Scope Hypothesis:** exactly 10 of the 15 `*_quot` lemmas are closed tautologies amenable to the
  bare pattern, and rewriting them takes the metric from 286 to roughly 147. **Confirm at
  implementation time** by, for each of the 10, reading its statement and checking it binds no
  `Derives`/`≤` hypothesis before attempting the rewrite; and by re-running the
  acceptance-criterion-1 command after the phase. If a lemma in the expected set turns out to bind a
  hypothesis, move it to Phase 2 and record the move rather than forcing the bare pattern. If the
  resulting figure differs from ~147, record the actual figure — the projection is a hypothesis, not
  a fact.

- **Files to modify:**
  - `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — add the `PropDecide` import; replace
    ~10 proof bodies. No statement changes.

- **Verification:**
  - `lake build` exits 0.
  - `bash scripts/check-module-invariants.sh` — C1, C2, C3 green; C2 baseline unchanged (HARD STOP on drift).
  - The `*_quot` lemma count still reads 15.
  - `git diff` shows no change to any `theorem …_quot` signature line.

---

### Phase 2: Tautology + pairing + MP extension for the three hypothesis-driven `*_quot` lemmas [COMPLETED WITH EXCLUSIONS]

- **Goal:** `sup_le_quot`, `le_inf_quot`, and `le_trans_quot` are proved by stating their conditional
  form as a closed tautology over opaque atoms, closing it with `propDecide`, and combining with the
  actual hypotheses via `Combinators.pairing` + `DerivationTree.modus_ponens`.

- **Tasks:**
  - [x] **Re-verify first**: confirm `Combinators.pairing` (`Theorems/Combinators.lean:555`,
        `⊢[fc] A.imp (B.imp (A.and B))`) and `DerivationTree.modus_ponens` are reachable from
        `BooleanStructure.lean`'s existing imports without adding one. Record the check.
  - [x] **Spike `sup_le_quot` first, alone.** It is the largest of the three (39 lines) and the one
        the line-count bar depends on. Target shape: `propDecide` closes the constructive-dilemma
        tautology `⊢ ((φ.imp χ).and (ψ.imp χ)).imp ((φ.or ψ).imp χ)`, then `pairing` builds
        `(φ.imp χ).and (ψ.imp χ)` from `hac`/`hbc` and two `modus_ponens` steps discharge it.
  - [x] If the spike closes, commit it, then apply the same shape to `le_inf_quot`
        (`⊢ ((φ.imp ψ).and (φ.imp χ)).imp (φ.imp (ψ.and χ))`).
  - [x] Evaluate `le_trans_quot` (currently 6 lines via `derives_trans`). It is **already minimal**;
        rewrite it only if the result is strictly shorter *and* no less readable. Recording "left as
        is, already minimal" is an acceptable outcome, not a miss. *(left as is, already minimal: any tautology+MP rewrite is >= 6 lines)*
  - [x] Re-measure the acceptance-criterion-1 figure and record it explicitly in the completion note,
        against Decision D2's table.
  - [x] If the figure lands in 100-115, close the phase `[COMPLETED WITH EXCLUSIONS]` with a
        `#### Reasoned Exclusions` record naming the shortfall, the measured number, and the evidence
        (the command output). Do not churn on formatting to buy the last few lines.

- **Completion note (2026-09-03):**
  - Re-verify 1: `Combinators.pairing` is `def pairing {fc} (A B : Formula) : ⊢[fc] A.imp (B.imp (A.and B))`
    (`Theorems/Combinators.lean:555`); `DerivationTree.modus_ponens` was already used at three sites in the
    file and `Theorems.Combinators` is imported transitively via `LindenbaumQuotient.lean:10`. No new import.
  - `sup_le_quot` spike closed on the first attempt with exactly the plan's shape (tautology
    `((φ.imp χ).and (ψ.imp χ)).imp ((φ.or ψ).imp χ)` by `propDecide`, `pairing` + three `modus_ponens`):
    39 -> 8 source lines (commit phase 2.1). `le_inf_quot` by the same shape: 13 -> 8 (phase 2.2).
  - `le_trans_quot` left as is (6 lines via `derives_trans`): a tautology+MP rewrite is 3 `induction`
    lines + obtains + tautology + `exact` = at least 7, so not strictly shorter.
  - Acceptance-criterion-1 command output, verbatim: `lemmas: 15 total_body_lines: 105`. Per lemma
    (inclusive span as the command counts it, which includes the one blank line following each proof):
    le_refl 6, le_trans 6, le_antisymm 5, inf_le_left 7, inf_le_right 7, le_inf 9, le_sup_left 7,
    le_sup_right 7, sup_le 9, bot_le 6, le_top 6, le_sup_inf 9, inf_compl_le_bot 6, top_le_sup_compl 6,
    sup_comm 9. Matches Decision D2's row 2 (~109 expected; landed at 105): **accept bar (≤ 115) met,
    stretch bar (< 100) not met**. Note for the user's D2 ruling: the command counts the trailing
    blank line of every lemma; the plan's prose definition ("declaration line through last proof
    line") gives 90. The plan says the command is the metric, so 105 is the recorded figure.
  - No `*_quot` statement changed (`git diff` on `^theorem` lines is empty).

#### Reasoned Exclusions

| Item | Reason | Evidence |
|------|--------|----------|
| Under-100 stretch target for acceptance criterion 1 | Landed at 105, inside D2's 100-115 accept band; the remaining 6 lines are only reachable by formatting churn (removing per-lemma blank lines or joining tactic lines), which D2 explicitly rules out. All 13 rewritable lemmas are at the plan's four-to-eight-line shape; `le_antisymm_quot` and `sup_comm_quot` are out of scope by Non-Goals. Decided, not deferred. | `lemmas: 15 total_body_lines: 105` (command output above); per-lemma spans listed above |
| Rewrite of `le_trans_quot` | Already minimal at 6 lines; the extension shape is not strictly shorter | current proof: `induction` x3 + `exact derives_trans hab hbc` |

- **Timing:** 2 hours
- **Depends on:** 1
- **Verification Tier:** local

  *Rationale*: edits confined to `BooleanStructure.lean` with no statement changes and no new import.
  Blind spot accepted: downstream semantic behaviour — covered by the phase's own closing `lake build`
  and C2 check.

- **Commit Mode:** per-substep

- **Scope Hypothesis:** the extension takes `sup_le_quot` 39→~12 and `le_inf_quot` 13→~10, landing
  the metric at ~109 (Decision D2 row 2), or ~99 if Phase 1's line-shaving held. **Confirm at
  implementation time** by running the acceptance-criterion-1 command and comparing against D2's
  table; report which row the actual outcome matches. Treat 109 as the expected case and under-100 as
  the stretch, per D2 — a phase that lands at 109 and says so is a success, one that claims under 100
  without the command output is not.

- **Files to modify:**
  - `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — up to three proof bodies.

- **Verification:**
  - `lake build` exits 0.
  - `bash scripts/check-module-invariants.sh` — C2 baseline unchanged (HARD STOP on drift).
  - Acceptance-criterion-1 command run and its output recorded verbatim in the completion note.
  - No `*_quot` statement changed.

---

### Phase 3: Fix the `PropDecideTest.lean` docstring and add De Morgan + distributivity regressions [NOT STARTED]

- **Goal:** the verified-wrong "out of scope" claim is removed and replaced by passing regression
  cases that exercise `and`/`or`-shaped goals directly.

- **Tasks:**
  - [ ] **Re-verify first**: read the current docstring in place (report 01 locates it at `:39-42`, the
        task description said `:44-46` — use the content, not the line number, as the anchor) and
        confirm it still makes the "out of scope for the pure imp/bot reflection skeleton" claim.
  - [ ] Replace the docstring with an accurate one: `PropDecide.reify`'s `whnf` call unfolds
        `and`/`or`/`neg` into the `imp`/`bot` skeleton automatically, so and/or-shaped goals are in
        scope.
  - [ ] Add the De Morgan case report 01 verified:
        `example (A B : Formula) : ⊢ (A.and B).neg.imp (A.neg.or B.neg) := by propDecide`.
  - [ ] Add a distributivity regression matching the `le_sup_inf_quot` shape:
        `example (A B C : Formula) : ⊢ ((A.or B).and (A.or C)).imp (A.or (B.and C)) := by propDecide`.
  - [ ] Keep the existing contrapositive-flavoured example — it tests a different path and its
        removal is not required by anything.

- **Timing:** 0.5 hours
- **Depends on:** none
- **Verification Tier:** local

  *Rationale*: edits confined to one test module, no signature exposed to any other module.

- **Commit Mode:** per-substep

- **Scope Hypothesis:** none asserted beyond the docstring's continued presence, which the first task
  re-verifies by content.

- **Files to modify:**
  - `Tests/BimodalTest/Metalogic/PropDecideTest.lean` — docstring correction plus two new `example`s.

- **Verification:**
  - `lake build` exits 0 (the test library is a build target, so a failing `example` fails the build).
  - Both new examples elaborate with no `sorry` and no error.
  - `bash scripts/check-module-invariants.sh` — C2 baseline unchanged.

---

### Phase 4: Restate `fold_le_of_derives` over `Multiset.inf` [NOT STARTED]

- **Goal:** `fold_le_of_derives` is stated over `((L.map toQuot : List _) : Multiset _).inf` and the
  hand-rolled `fold_from_x` reassociation `have` is gone.

- **Tasks:**
  - [ ] **Re-verify first**: confirm `Multiset.inf`, `Multiset.inf_coe`, `Multiset.le_inf`, and
        `Multiset.inf_le` resolve at the pinned Mathlib with the `[SemilatticeInf α] [OrderTop α]`
        instances `LindenbaumAlg` provides (`#check` each, or `lean_hover_info`). Record the four
        signatures.
  - [ ] **Re-verify second**: re-confirm `fold_le_of_derives` has exactly one call site
        (`UltrafilterMCS.lean:718`) and zero references elsewhere in the live tree. Record the grep.
  - [ ] Restate the theorem over the multiset coercion. Do **not** route through `Finset` — report 01
        verified `Multiset.le_inf`/`Multiset.inf_le` give both directions directly.
  - [ ] Delete the inlined `fold_from_x` reassociation `have`.
  - [ ] Update the single call site at `:718` in the same commit.

- **Timing:** 1.5 hours
- **Depends on:** none

  *This phase and Phase 6 share `UltrafilterMCS.lean`; Phase 6 depends on this one so that this
  phase runs first, against the line anchors (`:565`, `:718`) that currently hold, before Phase 6's
  deletions shift the file. `fold_le_of_derives` is untouched by Decision D1 (report 02 §8.2) — the
  ordering is file-ownership serialization, not a logical dependency.*

- **Verification Tier:** interface

  *Rationale*: the theorem's statement changes. The dependent set is enumerated and is exactly one
  in-file call site, so the "build the changed module plus its enumerated direct dependents" tier is
  satisfied by building `UltrafilterMCS.lean` — but the tier is declared `interface`, not `local`,
  because a signature genuinely changes and the enumeration must be re-verified rather than assumed.

- **Commit Mode:** atomic-batch

  *The restated theorem and its call-site update are one objective; the intermediate state (statement
  changed, call site not yet updated) is expected red and MUST NOT be committed.*

- **Scope Hypothesis:** `fold_le_of_derives` has exactly one call site, all four `Multiset` lemmas
  exist at the pinned Mathlib, and the restatement removes the `fold_from_x` `have` entirely.
  **Confirm at implementation time** by the two re-verification tasks above (grep output and four
  `#check`s recorded). If a second call site exists, add it to the atomic batch and say so.

- **Files to modify:**
  - `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — theorem statement and proof at `:565`;
    call site at `:718`.

- **Verification:**
  - `lake build` exits 0.
  - `grep -c 'fold_from_x' FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` returns 0.
  - `bash scripts/check-module-invariants.sh` — C2 baseline unchanged, C3 green.

---

### Phase 5: Land the generic prime-filter layer at `FormalSystem/ForMathlib/Order/PFilter.lean` [NOT STARTED]

- **Goal:** a Mathlib-shaped, upstream-ready `Order.PFilter` extension exists, is reachable from the
  Lake root, is sorry-free, and imports nothing from `FormalSystem.*`.

- **Tasks:**
  - [ ] **Re-verify first**: confirm which file is the Lake root aggregator that must gain
        `import FormalSystem.ForMathlib`. Planning found the repo-root `FormalSystem.lean` contains
        only `import FormalSystem.FormalSystem`, and the eight real submodule imports live in
        `FormalSystem/FormalSystem.lean:8-15` — so the new import belongs in the latter. Confirm by
        reading both files and record the verdict. Adding it to the wrong one leaves the module
        unreachable and C6 will say so.
  - [ ] **Re-verify second**: confirm C8's scope by reading `scripts/check-module-invariants.sh`'s
        C8 block (`for parent in ("FormalSystem", "FormalSystem/Metalogic")`). Planning read it as
        requiring `FormalSystem/ForMathlib.lean` and **not** requiring
        `FormalSystem/ForMathlib/Order.lean`. Record which sibling aggregators you create and why.
  - [ ] **Re-verify third**: `#check` the Mathlib names the layer builds on against the pinned
        checkout — `Order.PFilter`, `Order.PFilter.IsPrime`, `Order.PFilter.mem_of_le`,
        `Order.PFilter.inf_mem`, `Order.PFilter.top_mem`, `Order.Ideal.IsProper`,
        `Order.Ideal.IsMaximal`, `Order.Ideal.IsProper.exists_le_maximal`,
        `Order.Ideal.IsMaximal.isPrime`, `Order.Ideal.IsPrime.mem_or_compl_mem`,
        `Order.Ideal.isProper_of_notMem`, `Order.IsPFilter.of_def`, `Order.IsPFilter.toPFilter`.
        Record the signatures. If a name is absent or differs, **stop and report** rather than
        substituting a guess — report 01 already found one non-existent name
        (`Order.Ideal.ofPFilterCompl`) in this exact area.
  - [ ] Create `FormalSystem/ForMathlib/Order/PFilter.lean` **from report 02 Appendix A**, which is
        already compiled and sorry-free (202 lines: 163 generic + 39 bundling). Transcribe it; do
        not re-derive it. Keep its section structure verbatim — `[Preorder P]`, `[OrderBot P]`,
        `[DistribLattice P]`, `[BooleanAlgebra P]` in **separate `section`s** (mixing them trips the
        `overlappingInstances` linter; this was hit once during the spike and fixed by sectioning).
  - [ ] Import only `Mathlib.Order.PrimeIdeal`. **Nothing under `ForMathlib/` may import
        `FormalSystem.*`** — state this dependency rule in the file header. Direction is strictly
        `Mathlib → ForMathlib → Metalogic/Algebraic/UltrafilterMCS → downstream`.
  - [ ] Preserve the upstream-PR shape as a property of the file, at no extra cost: namespace
        `Order.PFilter` exactly (so upstreaming deletes the file and renames nothing); lemma names
        one-for-one with their `Order/Ideal.lean` / `Order/PrimeIdeal.lean` duals; `*_iff_dual` for
        transport lemmas; the genuinely-new names `IsPrime.toIsProper`, `IsProper.exists_le_prime`.
        Report 02 Appendix A carries the name correspondence in its right margin — keep it as
        comments.
  - [ ] Create the C8-required sibling aggregator `FormalSystem/ForMathlib.lean` importing
        `FormalSystem.ForMathlib.Order.PFilter`, with a module docstring stating the
        delete-on-upstreaming intent and the dependency rule.
  - [ ] Add `import FormalSystem.ForMathlib` to the aggregator identified in the first task, and
        build **before** proceeding.
  - [ ] **Optional, decided by measurement, not by default**: report 02 §5 shows
        `DistribLattice.prime_filter_of_disjoint_filter_ideal` (the Zorn-free prime-filter separator,
        Mathlib's own commented-out TODO in `Order/PrimeSeparator.lean:123-125`) is a four-line
        theorem once `isPrime_iff_dual` exists. It requires the extra leaf import
        `Mathlib.Order.PrimeSeparator`. Include it only if the import costs no measurable build time
        (report 02 §13 flags this as unmeasured); otherwise omit it and say so — nothing in this
        task consumes it.
        - **Pre-step, required if the corollary is attempted** (report 03 §2.2, Recommendation 6):
          diff upstream `mathlib4` master `Mathlib/Order/PrimeSeparator.lean` against the pinned
          copy under `.lake/` **before** assuming the TODO's exact statement. Upstream's last commit
          to that file is 2026-08-24, *after* the `79d0395a` pin; as of 2026-09-03 the commented
          `TODO: Define prime filters in Mathlib … := by sorry` at upstream `:124-126` was still
          open, but the surrounding statement may have moved or been reworded. Record the diff (or
          "no diff") in the completion note. If upstream has since landed a prime-filter statement,
          match its name and shape rather than report 02 §5's, and say so.
  - [ ] **Re-verify fourth**: re-read, rather than inherit, every documentation enumeration that
        lists `FormalSystem/` subdirectories or aggregators. Planning found three in
        `FormalSystem/README.md` (aggregator/line-count table `:219-226`, layer table `:247-257`,
        subdirectory/README table `:273-276`) plus the root `CLAUDE.md` "Project Structure" bullet
        list. Record the list you find before editing. Add a `ForMathlib/` row or bullet to each.
  - [ ] `.claude/context/repo/project-overview.md` is a **non-tracked courtesy edit**: `.claude/` is
        gitignored in this repo and `context/repo/project-overview.md` is listed in `.syncprotect`,
        so the edit persists locally but is not part of the deliverable. Make it if convenient;
        never let it gate the phase.
  - [ ] Record the observed `lake build` wall-clock delta from the new Mathlib leaf import(s) —
        report 02 §13 lists this as explicitly not measured.

- **Timing:** 0.5 hours

  *The 0.5 h assumes report 02 Appendix A is transcribed, not re-derived: the proof-discovery cost
  is already spent (E1 compiled it, exit 0, zero warnings). Wall-clock for the `lake build` cycles
  over a new Mathlib leaf import is not included and is unmeasured.*

- **Depends on:** none
- **Verification Tier:** full

  *Rationale*: a new top-level module and a new root-aggregator import change the build graph and
  the reachability set that C6/C7/C8 compute. This is not a local edit.

- **Commit Mode:** per-substep

  *The generic file plus its sibling aggregator plus the root import are one commit (the module is
  unreachable until all three exist, so splitting them commits a red C6). The documentation rows are
  a second commit.*

- **Scope Hypothesis:** the generic layer is ~202 lines transcribed from report 02 Appendix A with
  zero proof changes; C8 requires exactly one new aggregator (`ForMathlib.lean`); four documentation
  enumerations need a new row. **Confirm at implementation time** by the four re-verification tasks
  above, each with its output recorded. If Appendix A does not compile as transcribed against the
  live tree, record the exact diff needed rather than rewriting the layer — a divergence between the
  spike's scratch environment and the live tree is itself the finding.

- **Files to modify:**
  - `FormalSystem/ForMathlib/Order/PFilter.lean` — new.
  - `FormalSystem/ForMathlib.lean` — new (C8-required sibling aggregator).
  - `FormalSystem/FormalSystem.lean` — one new import line (confirm this is the right file first).
  - `FormalSystem/README.md` — new rows in the enumerations found by the fourth re-verification task.
  - `CLAUDE.md` — one new bullet in the "Project Structure" list.

- **Verification:**
  - `lake build` exits 0.
  - `bash scripts/check-module-invariants.sh` (full, **not** `--no-build`) — C4 green (imports
    resolve), **C6 sees the new module as reachable** (it must not appear in
    `scripts/module-invariants-manifest.txt`), C8 green, C5/C12/C13 green for the new doc rows,
    C2 baseline unchanged (HARD STOP on drift), C3 zero sorry.
  - `#print axioms Order.PFilter.IsProper.exists_le_prime` shows exactly
    `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
  - `grep -rn 'import FormalSystem' FormalSystem/ForMathlib/` returns nothing (the dependency rule).

---

### Phase 6: Port `UltrafilterMCS.lean` onto `Order.PrimeFilter` and delete the bespoke structure [NOT STARTED]

- **Goal:** the bespoke `structure Ultrafilter` is gone, `UltrafilterMCS.lean` states its content
  over `Order.PrimeFilter LindenbaumAlg`, `SetMaximalConsistent.ultrafilterEquiv` exists at the
  corrected type, and `ultrafilter_correspondence` is its corollary.

- **Tasks:**
  - [ ] **Re-verify first, per file**: re-run `grep -rn 'Ultrafilter' FormalSystem/ Tests/ --include=*.lean` and classify every hit as *bespoke* or *Mathlib's*. Planning found the bespoke set confined to `UltrafilterMCS.lean` (63 hits), with `Bundle/LimitMCS.lean` (16), `Semantics/Ultraproduct/*` (12), `Chronicle/ChronicleRealExtension.lean` (2 prose), and `Semantics.lean`/`DependentUltraproductProbe.lean` all being Mathlib's `Ultrafilter` on filters. **Re-derive this classification; do not inherit it.** Touching a Mathlib `Ultrafilter` site is a defect, not a scope expansion.
  - [ ] **Re-verify second**: confirm the module is **not** being renamed (only declarations inside it change), and confirm each of the four Boneyard consumers places `#exit` *before* its first `Ultrafilter` occurrence (`Boneyard/UltrafilterFrame/AlgebraicCompleteness.lean:27`, `Boneyard/UltrafilterFrame/UltrafilterFrame.lean:54`, `Boneyard/StrictSemanticsLegacy/Algebraic/UltrafilterChain.lean:46`, `Boneyard/UltrafilterFrame/TenseS5Algebra.lean:37`). Record the check — C11 requires their *import* lines to keep resolving.
  - [ ] **Re-verify third, per declaration**: re-run the reference greps and confirm (a) `ultrafilter_correspondence` (`:782`) is referenced only by `ultrafilter_mcs_round_trip` (`:983`), (b) `mcs_ultrafilter_round_trip` (`:1056`) is referenced nowhere outside its own declaration, (c) neither is referenced from `docs/`, `README.md`, or any live `.lean` file outside `UltrafilterMCS.lean`. Record each grep's output. **Do not proceed on the reports' claims alone** — this is the exact assumption class that cost a sibling task its line target.
  - [ ] Add `import FormalSystem.ForMathlib.Order.PFilter` and `import Mathlib.Order.PrimeIdeal`, and build **before** writing any proof.
  - [ ] Add `toQuot_mem_mcsToSet_iff` (report 02 §6, three lines via `SetMaximalConsistent.implication_property` at `Core/MCSProperties.lean:160` and `theorem_in_mcs` at `Core/MaximalConsistent.lean:462`). This is the dedup that collapses ~60 duplicated lines across `:782` and `:983`; it is worth taking independently of the encoding choice.
  - [ ] Add `mcsToSet_isPFilter`, `mcsToPFilter`, `mem_mcsToPFilter_iff`, the two instances (`mcsToPFilter_isProper`, `mcsToPFilter_isPrime`) and the new `mcsToUltrafilter`, **from report 02 Appendix B** — already compiled. The five existing `mcsToSet_*` witness lemmas are **reused unchanged**; do not restate them.
  - [ ] Re-type `ultrafilterToSet` and `ultrafilterToSet_mcs` by **textual substitution only** (report 02 §6): `U.carrier` → `U` (x18), `U.top_mem` → `PFilter.top_mem`, `U.inf_mem` → `PFilter.inf_mem`, `U.mem_of_le` → `PFilter.mem_of_le`, `U.bot_not_mem` → `U.2.toIsProper.bot_notMem`, the `cases U.compl_or` block → `U.2.compl_mem_of_notMem hφ`. **Zero proof-step changes.** If a proof step needs changing, that is a finding — record it, do not absorb it silently.
  - [ ] Add `SetMaximalConsistent.ultrafilterEquiv` at the corrected type (acceptance criterion 3), from Appendix B. **Friction 1 is pre-loaded**: the `right_inv` branch leaves an `ofDual (toDual a)` residue in a destructured hypothesis; fix it with the one-line `show a = toQuot φ from h_eq`, exactly as the spike did.
  - [ ] Restate `ultrafilter_correspondence` as the corollary `⟨ultrafilterEquiv, ultrafilterEquiv.symm, ultrafilterEquiv.left_inv, ultrafilterEquiv.right_inv⟩`. **Its statement must not change** — it stays the existential, so any future consumer is unaffected.
  - [ ] Replace `Ultrafilter.compl_xor`, `mem_iff_compl_not_mem`, `not_mem_iff_compl_mem` (`:910-947`) — these **are** `IsPrime.mem_iff_compl_notMem` / `compl_mem_iff_notMem` in the generic layer — and collapse `ultrafilter_neg_iff` / `ultrafilter_neg_iff'` (`:950-966`) to the two one-liners. **Friction 2 is pre-loaded**: `U.2.compl_mem_iff_notMem` cannot infer `x` from `⟦φ.neg⟧ ∈ U` (the unifier will not invert `toQuot φ.neg` to `(toQuot φ)ᶜ`); pass `(x := toQuot φ)`. One site.
  - [ ] Delete: `structure Ultrafilter` + its `Membership` instance + `ext` + `empty_not_mem` (`:44-81`), the old `mcsToUltrafilter` and `mcsToUltrafilter_carrier` / `mem_mcsToUltrafilter_iff` (`:538-556`, now `Iff.rfl`), `ultrafilter_mcs_round_trip` (`:983-1053`, subsumed by `Equiv.left_inv`), and `mcs_ultrafilter_round_trip` (`:1056-1069`, subsumed by `Equiv.right_inv`). Enumerate every deletion in the completion note.
  - [ ] Measure and record the resulting file line count against the ~780 projection (acceptance criterion 7).
  - [ ] **If a third friction appears** beyond the two pre-loaded above, record it explicitly in the completion note rather than improvising around it — the spike's claim is "four frictions, all handled"; a fifth is new information.

- **Timing:** 2 hours
- **Depends on:** 4, 5

  *4 for file ownership (same file, ordered so Phase 4's line anchors still hold); 5 because the port
  consumes `Order.PrimeFilter` and the `Order.PFilter` API.*

- **Verification Tier:** full

  *Rationale*: a public type disappears, two new imports enter a module with downstream dependents
  including four Boneyard files under C11, and the module's elaboration surface changes throughout.

- **Commit Mode:** per-substep

  *The two imports are their own commit, taken before any proof. Then, in order and each on its own
  green commit: `toQuot_mem_mcsToSet_iff`; the `mcsToPFilter` group; the `ultrafilterToSet` /
  `ultrafilterToSet_mcs` substitution pass; `ultrafilterEquiv`; the `ultrafilter_correspondence`
  corollary; the `:910-966` replacement; the deletions. The deletions come last so that every
  intermediate state builds.*

- **Scope Hypothesis:** all ~63 `Ultrafilter` and ~46 `carrier` occurrences in `UltrafilterMCS.lean`
  are either type ascriptions (→ `PrimeFilter LindenbaumAlg`) or `x ∈ U.carrier` (→ `x ∈ U`), so
  **no mathematical re-derivation is needed anywhere**; the file goes 1,071 → roughly 780 lines.
  **Confirm at implementation time** by the three re-verification tasks above, and by checking after
  the substitution pass that `git diff` on `ultrafilterToSet_mcs` shows only ascription and
  projection changes — no tactic added, removed, or reordered. If a genuine re-derivation is needed
  at any site, stop, record which site and why, and treat the remainder of the phase as
  `[PARTIAL]` rather than pushing through: report 02's central empirical claim would be false, and
  that is worth surfacing rather than absorbing.

- **Files to modify:**
  - `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — two imports; new lemmas and defs from
    report 02 Appendix B; substitution pass; deletions.

- **Verification:**
  - `lake build` exits 0.
  - `bash scripts/check-module-invariants.sh` — **C2 baseline unchanged (HARD STOP on drift)**,
    C3 zero sorry, C4 green, **C11 green** (module name unchanged, Boneyard imports still resolve).
  - `grep -rn 'structure Ultrafilter\|namespace Ultrafilter' FormalSystem/Metalogic/Algebraic/ --include=*.lean`
    returns nothing (acceptance criterion 2).
  - `#check SetMaximalConsistent.ultrafilterEquiv` elaborates at
    `{Γ : Set Formula // SetMaximalConsistent (fc := FrameClass.Base) Γ} ≃ Order.PrimeFilter LindenbaumAlg`,
    and `#print axioms` on it shows no `sorryAx`.
  - `ultrafilter_correspondence`'s statement line is byte-identical to its pre-phase form
    (`git diff` shows a proof-body change only).
  - The measured file line count is recorded in the completion note.

---

### Phase 7: Refresh `Algebraic/README.md` and record the D1 rationale [NOT STARTED]

- **Goal:** the README describes the modernised layer accurately, carries a "Last verified" stamp,
  and records why the Mathlib-native prime-filter encoding was chosen.

- **Tasks:**
  - [ ] **Re-verify first**: re-read the README against the post-Phase-6 tree and list every stale
        claim — line counts (`UltrafilterMCS.lean` is currently documented as 1,071 and will have
        changed), the `mcsToUltrafilter`/`ultrafilterToSet` API sketch at `:149-150`, the file table
        at `:40-56`, and any sorry/axiom counts C14 asserts. Record the list before editing.
  - [ ] Update the module table row for `UltrafilterMCS.lean`: new line count, "sorry-free", and
        that it now consumes `FormalSystem/ForMathlib/Order/PFilter.lean`.
  - [ ] Update the API sketch to name `Order.PrimeFilter LindenbaumAlg`,
        `SetMaximalConsistent.ultrafilterEquiv` at its corrected type, and `mcsToPFilter`.
  - [ ] Add the `ForMathlib` node to the dependency flowchart, showing the direction
        `Mathlib → ForMathlib → Metalogic/Algebraic/UltrafilterMCS → downstream`.
  - [ ] Add a "Design decisions" subsection recording D1 = option (c) with: the **two-dualities**
        argument (the order dual is free — `mem_dual_iff`, `le_iff_dual_le`, `lt_iff_dual_lt`,
        `coe_eq_univ_iff` are all `Iff.rfl` — whereas the Boolean-complement duality of the
        ideal-side encoding inverts every downstream statement); the **`IsPrime`-suffices** fact
        (`IsPrime`'s `compl_ideal` field bundles `IsIdeal.Nonempty`, so `IsPrime.toIsProper` is a
        3-line instance and `IsProper` is a consequence, not a prerequisite); and that **no bridge
        lemma was written** because the ideal is `IsPrime.toPrimePair`.
  - [ ] **Optional textbook citation for the `Order.PrimeFilter` vocabulary** (report 03 §3.2): the
        subsection may cite Chagrov & Zakharyaschev, *Modal Logic* (1997), Part III §8.2 "The Stone
        and Jónsson-Tarski theorems" (printed pp. 241-243), **Theorem 8.14** — Stone's representation
        with the Stone space defined as the set of all *prime filters* and `f_A(a) = {∇ : a ∈ ∇}`,
        via Corollary 7.42 (prime-filter separation) — as the textbook statement behind naming the
        bundled type by prime filters rather than ultrafilters (on a Boolean algebra the two coincide,
        `Order/PrimeIdeal.lean:133,174`). The corpus entry is `chagrovzakharyaschev_1997_modallogic`,
        registered in `specs/literature-index.json` with a `relevance` note naming §8.2. **It is
        DJVU-derived OCR** (fraktur A reads as `21`, `∈` as `G`, `f_A` as `/a`): use it as a
        locator only and read the page images before transcribing any formula into the README.
        Cite by author, year, part/section, theorem number and printed page — never by task number.
  - [ ] **Optional Mathlib-coverage note** (report 03 §2.3): the subsection may record that the
        pinned Mathlib (`v4.33.0-rc1`, `79d0395a`) has **no** Stone representation theorem for
        Boolean algebras and **no** Priestley duality — `Order/Birkhoff.lean:40` scopes itself to
        finite Stone duality, `Topology/Order/Priestley.lean` defines only the `PriestleySpace`
        mixin, `Order/Category/BoolAlg.lean` is the bare category — and that
        `Order/PrimeSeparator.lean:14-16` (van Gool, 2024) names Stone duality for bounded
        distributive lattices as its purpose. The `ForMathlib` layer is therefore the natural next
        brick in a direction a Mathlib author has already begun; say so in one sentence, as
        motivation for keeping the file PR-shaped. Re-verify the three Mathlib anchors against the
        pinned checkout before writing them into the README.
  - [ ] Note the `propDecide` dependency: `BooleanStructure.lean` now imports
        `Automation/Tactics/PropDecide.lean`, and the layering rationale (no cycle).
  - [ ] Record the **documented gap** for the downstream representation work: Mathlib gives `PFilter`
        no lattice, so `F ⊔ principal x` needs a five-line dual transport `⟨F.dual ⊔ G.dual⟩` that
        this task deliberately does not write.
  - [ ] **Use durable anchors, never task numbers.** When describing what the layer now unblocks,
        name the declarations (`Order.PFilter.IsProper.exists_le_maximal`, `.exists_le_prime`,
        `Order.Ideal.PrimePair` via `U.2.toPrimePair`) and the file paths, not "task 497" or
        "task 125" — C9 enforces zero task-number citations under `FormalSystem/`, and
        `.claude/rules/no-task-references-in-deliverables.md` is the governing rule.
  - [ ] Add the "Last verified" stamp using the form the majority of sibling `Metalogic/*/README.md`
        files use (`FormalSystem/BaseLanguage/README.md:69` uses `**Last verified**: YYYY-MM-DD`;
        `FormalSystem/Automation/README.md:107` uses `*Last verified: YYYY-MM-DD*`). Keep the
        existing `*Last updated:*` footer and update its date too.
  - [ ] Record the final acceptance-criterion-1 measurement in the README's status section.
  - [ ] Touch `FormalSystem/Metalogic/Algebraic.lean`'s docstring only if it names the deleted
        `Ultrafilter` structure; re-verify by grep before editing.

- **Timing:** 1 hour
- **Depends on:** 2, 3, 6
- **Verification Tier:** prose

  *Rationale*: all edits are in a markdown file (plus at most one Lean docstring) with zero compile
  surface. Blind spot accepted: broken cross-references, stale documented counts, and a leaked task
  number — all three are covered by the C5/C9/C12/C13/C14 checks in this phase's verification, which
  is why the full invariant script (not `--no-build`) is required here.

- **Commit Mode:** per-substep

- **Scope Hypothesis:** no count or file list asserted beyond the stale-claim list, which the first
  task produces by direct re-reading rather than by inheriting a plan-time enumeration.

- **Files to modify:**
  - `FormalSystem/Metalogic/Algebraic/README.md`
  - `FormalSystem/Metalogic/Algebraic.lean` — docstring only, and only if it names the deleted type.

- **Verification:**
  - `bash scripts/check-module-invariants.sh` (full, **not** `--no-build`) — C5, C9, C12, C13, C14
    green; C2 unchanged.
  - `grep -rn 'task [0-9]' FormalSystem/Metalogic/Algebraic/README.md` returns nothing.

---

## Testing & Validation

- [ ] `lake build` exits 0 at every phase boundary.
- [ ] `bash scripts/check-module-invariants.sh` all-pass at task close; C2 axiom baseline byte-identical to its pre-task value.
- [ ] C3: zero structural `sorry` — no new sorry introduced by any phase.
- [ ] C6: the new `FormalSystem/ForMathlib/Order/PFilter.lean` is **reachable** (absent from `scripts/module-invariants-manifest.txt`); C8 green for the `ForMathlib.lean` sibling aggregator.
- [ ] C11 green: every Boneyard import still resolves (the module is not renamed).
- [ ] `Tests/BimodalTest/Metalogic/PropDecideTest.lean` compiles with the two new regression examples.
- [ ] Acceptance-criterion-1 command run and its output recorded, with the outcome mapped to a row of Decision D2's table.
- [ ] `#check SetMaximalConsistent.ultrafilterEquiv` elaborates at `≃ Order.PrimeFilter LindenbaumAlg`; `#print axioms` on it shows no `sorryAx`.
- [ ] `#print axioms Order.PFilter.IsProper.exists_le_prime` shows exactly `[propext, Classical.choice, Quot.sound]`.
- [ ] `grep -rn 'structure Ultrafilter\|def Ultrafilter' FormalSystem/ --include=*.lean | grep -v Boneyard` returns nothing.
- [ ] `grep -rn 'import FormalSystem' FormalSystem/ForMathlib/` returns nothing.
- [ ] `grep -c 'fold_from_x' FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` returns 0.

## Artifacts & Outputs

- `FormalSystem/ForMathlib/Order/PFilter.lean` — new: the generic `Order.PFilter` extension
  (`IsProper`, `IsMaximal`, the `*_iff_dual` transports, the Boolean section, `Order.PrimeFilter`).
- `FormalSystem/ForMathlib.lean` — new: C8-required sibling aggregator.
- `FormalSystem/FormalSystem.lean` — one new import line.
- `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` — `propDecide`-backed `*_quot` proofs.
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` — `Multiset.inf`-based `fold_le_of_derives`;
  ported onto `Order.PrimeFilter`; `ultrafilterEquiv` at the corrected type; bespoke structure
  deleted.
- `FormalSystem/Metalogic/Algebraic/README.md` — refreshed, with "Last verified" stamp and the D1
  rationale.
- `FormalSystem/README.md`, `CLAUDE.md` — `ForMathlib/` rows/bullet.
- `Tests/BimodalTest/Metalogic/PropDecideTest.lean` — corrected docstring, De Morgan and
  distributivity regressions.
- `FormalSystem/Metalogic/Algebraic.lean` — docstring touch-up if it names the deleted type.
- `specs/528_algebraic_modernisation_propdecide_mathlib_filters/summaries/01_*-summary.md` —
  execution summary, including the acceptance-criterion-1 measurement, the `UltrafilterMCS.lean`
  line-count measurement, and any Reasoned Exclusions.

## Rollback/Contingency

- Every phase is a separate commit (or atomic batch), so `git revert` of a phase's commit range
  restores the prior state without touching other phases.
- **Phase 1 import addition**: if adding the `PropDecide` import creates a cycle the planning greps
  missed, revert that single commit; Phases 3-7 are unaffected and the task still delivers
  acceptance criteria 2-7.
- **Phase 2 failure**: retain the existing 39-line `sup_le_quot`, close
  `[COMPLETED WITH EXCLUSIONS]`, and record ~136 as the measured figure per Decision D2.
- **Phase 5 failure (Appendix A does not transcribe cleanly)**: the generic layer is self-contained
  and imports nothing from `FormalSystem.*`, so reverting its three-file commit leaves the tree
  exactly as Phases 1-4 left it. Phase 6 then cannot run; Phase 7 runs with the D1 subsection
  omitted. Record the exact compile divergence — it contradicts report 02's E1 evidence and is the
  finding, not a nuisance.
- **Phase 6 partial (a site needs genuine re-derivation)**: stop at that site, keep every green
  sub-step commit taken so far, close the phase `[PARTIAL]` naming the site, and leave the bespoke
  structure in place until the re-derivation is planned. Do **not** delete the structure while any
  consumer is unported.
- **C2 drift at any phase**: HARD STOP. Do not re-baseline. Revert the phase's commits, report the
  divergence with the `#print axioms` diff, and mark the task `[BLOCKED]`.
- **Decision D1 reversal**: D1 is resolved, not defaulted. Reversing it would discard the spike's
  compiled evidence and reintroduce a second representation; it should be treated as a new decision
  requiring its own justification, not as exercising a reversal point left open by this plan.
