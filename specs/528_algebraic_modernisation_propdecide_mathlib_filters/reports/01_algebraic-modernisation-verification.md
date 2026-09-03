# Research Report: Algebraic/ Modernisation (propDecide, Mathlib filters)

## Scope

Re-measure every anchor in the dispatch brief against the live tree (post- Core MCS API
consolidation and the sibling Bundle/-modernisation task, both of which landed after the
2026-09-01 review and are known to have drifted the review's anchors elsewhere in this batch),
and empirically verify the load-bearing claim that `propDecide` closes the
`le_sup_inf_quot`-shaped distributivity goal via the proposed
`induction … using Quotient.ind; change Derives …; unfold Derives; propDecide` pattern.

File scope: `FormalSystem/Metalogic/Algebraic/`, `FormalSystem/Metalogic/Algebraic.lean`,
`FormalSystem/Metalogic/Algebraic/README.md`, `FormalSystem/Automation/Tactics/PropDecide.lean`,
`Tests/BimodalTest/Metalogic/PropDecideTest.lean`.

## Measured-State Verification (all anchors re-checked against the live tree)

All brief anchors below were re-measured directly and confirmed accurate — **no material drift**
was found on this task, unlike the sibling task in this batch:

- **`BooleanStructure.lean`**: 441 lines (README says 441; brief's "~430" is a close
  approximation). Exactly **15** `*_quot` theorem declarations (grep-counted:
  `le_refl_quot`, `le_trans_quot`, `le_antisymm_quot`, `inf_le_left_quot`, `inf_le_right_quot`,
  `le_inf_quot`, `le_sup_left_quot`, `le_sup_right_quot`, `sup_le_quot`, `bot_le_quot`,
  `le_top_quot`, `le_sup_inf_quot`, `inf_compl_le_bot_quot`, `top_le_sup_compl_quot`,
  `sup_comm_quot`).
- **`le_sup_inf_quot`** at `BooleanStructure.lean:242`, spans to line 357 (116 body lines),
  contains **31** `have` steps (grep-counted) — brief's "119 lines, 31 haves" is accurate to
  within a few lines of section-comment slack.
- **`propDecide`** (`Automation/Tactics/PropDecide.lean:123`, the `elab "propDecide"` block) has
  two dispatch branches: `extractDerivationGoal` (`Helpers.lean:524`, matches raw
  `DerivationTree fc ctx φ` goals, i.e. `⊢`/`⊢[fc]`) and a **second**, locally-defined
  `PropDecide.extractDerivableGoal` (`PropDecide.lean:100`, matches `Derivable fc ctx φ`, i.e.
  `|-!`/`|-![fc]`). **Correction to the brief**: `Derives φ ψ` (`LindenbaumQuotient.lean:46`) is
  defined as `Derivable FrameClass.Base [] (φ.imp ψ)`, i.e. `Nonempty (DerivationTree …)` — so
  after `unfold Derives`, the goal is `Derivable`-shaped, reaching `PropDecide.extractDerivableGoal`
  at `PropDecide.lean:100`, **not** `extractDerivationGoal` at `Helpers.lean:524` as the brief
  states. This is a naming/line-anchor correction only; the tactic dispatches correctly either
  way (both branches are wired and tested — see empirical verification below).
- **No import cycle**: confirmed by direct grep — nothing under `Metalogic/Decidability/`,
  `Metalogic/Core/`, or `Theorems/` imports `Algebraic.BooleanStructure` or
  `Algebraic.LindenbaumQuotient`. `PropDecide.lean` can safely import `Kalmar.lean`'s chain, and
  `BooleanStructure.lean` can safely import `PropDecide.lean`.
- **`UltrafilterMCS.lean`**: 1,071 lines (README confirms). `structure Ultrafilter (α)
  [BooleanAlgebra α]` at line 44, 6 property fields plus `carrier` (`top_mem`, `bot_not_mem`,
  `mem_of_le`, `inf_mem`, `compl_or`, `compl_not`) — matches the brief exactly. Only consumer
  anywhere in the tree is the sibling aggregator `Algebraic.lean` (compiled, not depended on) —
  confirmed by grep; the whole Boolean-algebra/ultrafilter layer genuinely has **no current
  consumer**, per the directory's own README.
- **`ultrafilter_correspondence`** (`SetMaximalConsistent.ultrafilter_correspondence`) at line
  782 (brief: 782, 127 lines — confirmed, spans to line ~908/909 region before
  `ultrafilter_mcs_round_trip`'s doc comment). **`ultrafilter_mcs_round_trip`** at line 983,
  spans 983–1055 (73 lines; brief said 72 — accurate to a line). Grep confirms
  `ultrafilter_correspondence` is referenced **exactly once** anywhere in the tree: by
  `ultrafilter_mcs_round_trip` itself (which destructures `⟨f, g, h_left, _⟩`, discards `g` and
  `h_right`, and re-derives the left round trip from scratch rather than just returning `h_left`
  suitably coerced). A **second** round-trip theorem, `mcs_ultrafilter_round_trip` (the
  `RightInverse` direction, not named in the brief's line anchors but implied by "both
  round-trip theorems"), sits at line 1056–1069 (~16 lines). **Both round-trip theorems are
  confirmed referenced nowhere else in the tree** (grep, zero hits outside their own
  definitions) — D-16's claim is accurate, not drifted.
- **`fold_le_of_derives`** at line 565 (brief: 565), spans to line 656 (~92 lines including its
  leading docstring; brief's "102 lines" is a reasonable rounding). Uses a `List.foldl (fun acc
  φ => acc ⊓ toQuot φ) ⊤ L` accumulator with a hand-proved `fold_from_x` reassociation lemma
  inlined as a `have`; one call site at line 718.
- **`Algebraic/README.md`**: confirmed **no** "Last verified" stamp anywhere (grep, zero hits);
  it has a `*Last updated: 2026-08-26*` footer instead, a different field. Brief's claim is
  accurate.

## Empirical Verification of the Core propDecide Claim (item 1's prerequisite)

Per the dispatch instruction to verify this myself rather than inherit it: I added two scratch
`example`s directly into `BooleanStructure.lean` (with a temporary `import
FormalSystem.Automation.Tactics.PropDecide`), ran a full `lake build` via the `lean_build` MCP
tool, confirmed both compiled with `✔ Built FormalSystem.Metalogic.Algebraic.BooleanStructure`
and zero errors, then reverted both edits (file diff confirmed clean afterward; no scratch code
was left in the tree).

1. **The exact `le_sup_inf_quot` shape**, using precisely the pattern the brief proposes:
   ```lean
   example (a b c : LindenbaumAlg) :
       andQuot (orQuot a b) (orQuot a c) ≤ orQuot a (andQuot b c) := by
     induction a using Quotient.ind
     induction b using Quotient.ind
     induction c using Quotient.ind
     rename_i φ ψ χ
     change Derives ((φ.or ψ).and (φ.or χ)) (φ.or (ψ.and χ))
     unfold Derives
     propDecide
   ```
   **Confirmed: closes the goal.** This validates D-08 directly, not just by inheritance from
   the prior `lean_multi_attempt` claim.

2. **The De Morgan/and-or docstring claim**: `PropDecideTest.lean:40-42` (line numbers shifted
   slightly from the brief's 44-46, but the same docstring) says testing And/Or-shaped goals
   directly is "out of scope for the pure imp/bot reflection skeleton," while in the same breath
   correctly noting `and`/`or` are themselves defined via `imp`/`neg`. This is self-contradictory
   and, per the brief, wrong. I verified this directly:
   ```lean
   example (A B : Formula) :
       Derivable FrameClass.Base [] ((A.and B).neg.imp (A.neg.or B.neg)) := by propDecide
   ```
   **Confirmed: closes the goal** (De Morgan via `and`/`or`, no manual unfolding needed —
   `PropDecide.reify`'s `whnf` call unfolds `and`/`or`/`neg` into the `imp`/`bot` skeleton
   automatically). The docstring's "out of scope" claim is confirmed wrong and should be fixed
   as part of item 1; add this exact De Morgan-via-and/or case as a regression test replacing
   the current contrapositive-flavoured workaround example.

## Correction / Refinement to Item 1's Scope: Not All 15 `*_quot` Lemmas Fit the Bare Pattern

The brief's item 1 ("rewrite the `*_quot` bodies as `induction …; change Derives …; unfold
Derives; propDecide`") implicitly treats all 15 lemmas uniformly. Having read every one, **the
bare four-line pattern applies only to lemmas whose statement is a closed propositional
tautology with no derivation-hypothesis inputs** — `propDecide`'s `tautologyDerivableFc'`
mechanism proves *closed* schematic tautologies; it cannot consume a hypothesis derivation
(`hab : Derives a b`) as a side premise, since its only input is the reified goal formula itself.

**Directly amenable (closed tautologies, ~10 of 15)** — each reduces to a ~7-line
`induction/rename_i/change/unfold/propDecide` block:
`le_refl_quot`, `inf_le_left_quot`, `inf_le_right_quot`, `le_sup_left_quot`,
`le_sup_right_quot`, `bot_le_quot`, `le_top_quot`, `le_sup_inf_quot` (**116 → ~8 lines, the
single largest win**), `inf_compl_le_bot_quot` (28 → ~7 lines), `top_le_sup_compl_quot`
(13 → ~7 lines).

**Not directly amenable — hypothesis-driven (4 of 15)**: `le_trans_quot` (~7 lines, already
minimal via `derives_trans`), `le_antisymm_quot` (~5 lines — its conclusion is an *equality*
proved via `Quotient.sound`, not a `Derives`/`Derivable` goal at all, so `propDecide` cannot
apply to it under any encoding), `le_inf_quot` (~13 lines, takes `hab hac` as hypotheses),
`sup_le_quot` (**33 lines**, the second-largest hand-built derivation in the file, takes `hac
hbc` as hypotheses — this is disjunction elimination built from `bCombinator` +
`classicalMerge`).

**Recommended refinement for the plan**: for the three hypothesis-driven `Derives`-shaped
lemmas (`le_trans_quot`, `le_inf_quot`, `sup_le_quot`), state the *conditional* form as a closed
tautology over opaque atoms — e.g. for `sup_le_quot`: `⊢ ((φ.imp χ).and (ψ.imp χ)).imp
((φ.or ψ).imp χ)` (constructive dilemma) is itself a closed tautology, provable by `propDecide`
in one line — then combine with the actual hypotheses `hac`/`hbc` via
`Combinators.pairing` + `modus_ponens` (both already used elsewhere in this file). This shrinks
`sup_le_quot` from 33 lines to roughly 10–12 and is a natural, in-scope extension of the same
technique, not a new approach. `le_antisymm_quot` should be left as-is (5 lines, not
`Derives`-shaped). With this refinement, summing all 15 post-refactor body lengths lands at
roughly 95–110 lines depending on formatting choices — the "under 100 lines" acceptance bar is
**achievable but tight**; flag to the planner that hitting it cleanly requires the
pairing+MP extension on at least `sup_le_quot`, not just the bare four-liner on the tautology
subset.

`sup_comm_quot` (8 lines) is already minimal (derived from `sup_le_quot` +
`le_sup_left/right_quot`) and needs no change.

## LindenbaumQuotient's `provEquiv_*` Congruences: Item 1's Extension Does Not Apply

The brief's item 1 also asks to "apply the same to LindenbaumQuotient's `provEquiv_*`
congruences where it fits." Having read all of them
(`provEquiv_refl`, `provEquiv_symm`, `provEquiv_trans`, `provEquiv_neg_congr`,
`provEquiv_box_congr`, `provEquiv_all_past_congr`, `provEquiv_imp_congr`,
`provEquiv_and_congr`, `provEquiv_or_congr`): **none of the substantive ones fit.** Every
congruence lemma is conditional on a given `φ ≈ₚ ψ` hypothesis (i.e. given derivations
`d_fwd`/`d_bwd`), not a closed tautology — `provEquiv_box_congr` additionally uses
`DerivationTree.necessitation` (not purely propositional) and `provEquiv_all_past_congr` uses
`Perpetuity.pastMono` (not propositional at all). The one lemma that *could* trivially take the
pattern, `derives_refl` (`Derives φ φ`, a closed tautology), is already a 3-line proof via
`Combinators.identity` and gains nothing from rewriting. **Recommendation: skip this extension
entirely** — report to the planner that "where it fits" resolves to "nowhere non-trivial fits,"
so no phase budget should be allocated to it.

## Item 2: `ultrafilterEquiv` — Shape Is Sound

`SetMaximalConsistent.ultrafilter_correspondence`'s existing statement (`∃ f g, LeftInverse g f
∧ RightInverse g f`) already carries exactly the two functions and two round-trip facts needed
to populate an `Equiv`. The refactor is mechanical: state
`noncomputable def SetMaximalConsistent.ultrafilterEquiv :
{Γ // SetMaximalConsistent Γ} ≃ Ultrafilter LindenbaumAlg` with `toFun := mcsToUltrafilter`,
`invFun := ultrafilterToMcs`, `left_inv := ultrafilter_mcs_round_trip`,
`right_inv := mcs_ultrafilter_round_trip` (both already proved, just currently unconsumed), then
derive `ultrafilter_correspondence` as a one-line corollary (`⟨e.toFun, e.invFun, e.left_inv,
e.right_inv⟩`) instead of the current from-scratch existential proof. This also resolves D-16
for free: both round-trip theorems become the `Equiv`'s fields, i.e. consumed.

## Item 3: Reconciling the Bespoke `Ultrafilter` with Mathlib — Concrete Finding

**The brief's suggested `Order.Ideal.ofPFilterCompl` does not exist anywhere in Mathlib**
(grep across the full pinned Mathlib checkout, zero hits) — it was a speculative name in the
brief, correctly hedged with "(or the dual prime-ideal form)". Verified directly against
`Mathlib.Order.Ideal`, `Mathlib.Order.PFilter`, and `Mathlib.Order.PrimeIdeal` (the pinned
`v4.33.0-rc1` Mathlib):

- `Order.Ideal.IsMaximal` (class, `Ideal.lean:189`) and `Order.Ideal.IsProper.exists_le_maximal`
  (`Ideal.lean:642`, `∃ J, I ≤ J ∧ J.IsMaximal`) both exist exactly as the brief states — this
  **is** the algebra-level Lindenbaum extension lemma.
- `Order.Ideal.IsPrime` (`PrimeIdeal.lean:82`), and, in a `[BooleanAlgebra P]` section:
  `IsMaximal.isPrime` (instance, priority 100, `PrimeIdeal.lean:133` — **exact name match** to
  the brief's claim for `compl_or`'s provenance) and its converse `IsPrime.isMaximal`
  (`PrimeIdeal.lean:174`), plus `IsPrime.mem_or_compl_mem` (exactly the `compl_or` field shape:
  `x ∈ I ∨ xᶜ ∈ I`) and `IsPrime.compl_mem_of_notMem` (exactly `compl_not`'s contrapositive).
- **No `Order.Ideal.IsMaximal` analogue exists on the `PFilter` side** — only
  `Order.PFilter.IsPrime` (its complement is an ideal) is defined for filters; there is no
  `PFilter.IsMaximal`. `Order.PFilter.mem_of_le` (`PFilter.lean:88`) and
  `Order.PFilter.inf_mem` (`PFilter.lean:141`, under `[SemilatticeInf P]`) both exist and match
  the bespoke structure's fields by name, confirming the brief's claim precisely.

**Conclusion for the planner**: the *Ideal* side, not the *PFilter* side, is where Mathlib's
machinery actually concentrates (`IsMaximal` is only defined for `Ideal`). The tractable
encoding is `{I : Order.Ideal LindenbaumAlg // I.IsMaximal}` (brief's "dual prime-ideal form"),
**not** a `PFilter`-plus-invented-bridge encoding — recommend dropping the `PFilter`/
`ofPFilterCompl` option from consideration rather than assessing it further, since the bridge
function it depends on does not exist and would have to be built from scratch, while the
Ideal-side encoding needs zero new bridge code. Two remaining live choices for the planner: (a)
replace the bespoke `Ultrafilter` outright with `{I : Order.Ideal LindenbaumAlg // I.IsMaximal}`
and rewrap the existing `mcsToUltrafilter`/`ultrafilterToMcs`/round-trip development around it
(carrier becomes `{a | aᶜ ∈ I}`, i.e. the complement), or (b) keep the bespoke structure renamed
`BAUltrafilter` for readability and prove `BAUltrafilter α ≃ {I : Order.Ideal α // I.IsMaximal}`
once, per the brief's fallback. Given the layer has **no live consumer** today (confirmed above)
and tasks 497/125 are the first real consumers, (a) is lower long-term maintenance (one
representation, not two, and it inherits every future Mathlib `Ideal`/`IsPrime`/`IsMaximal`
lemma for free) but is a larger diff over the ~500 lines of `UltrafilterMCS.lean` that reference
`Ultrafilter`/`.carrier`/`∈`/`instMembershipUltrafilter` today; (b) is a smaller diff (one new
`Equiv` proof) but leaves the shadowing name and duplicated axiom surface in place. Recommend
the planner choose (a) given no live consumer currently depends on the exact bespoke API shape,
but this is a judgment call worth surfacing to the user rather than deciding unilaterally in
research.

## Item 4: `fold_le_of_derives` via `Multiset.inf` — Confirmed Available

Checked directly via `lean_run_code` against the pinned Mathlib: `Multiset.inf`,
`Multiset.inf_coe` (`(↑l).inf = List.foldr (⊓) ⊤ l`), `Multiset.le_inf`, and `Multiset.inf_le`
all exist exactly as named (auto-generated as the `@[to_dual]` dual of `Multiset.sup` in
`Mathlib.Data.Multiset.Lattice`), requiring only `[SemilatticeInf α] [OrderTop α]` —
`LindenbaumAlg`'s `BooleanAlgebra` instance provides both. **Correction to the brief**: the
`Finset.inf_le`/`Finset.le_inf` detour it names is unnecessary — `Multiset.le_inf`/
`Multiset.inf_le` already give both directions directly on the `Multiset`, no `Finset`
conversion needed. Restating as `((L.map toQuot : List _) : Multiset _).inf ≤ toQuot ψ` and
proving by `Multiset.le_inf`/induction-free reasoning over `Multiset.inf_coe` removes the
hand-rolled `fold_from_x` reassociation `have` entirely.

## Recommendation Summary for the Planner

1. Item 1 (propDecide in `BooleanStructure.lean`): proceed — empirically confirmed on the
   flagship `le_sup_inf_quot` case and on the De Morgan regression case. Scope to the ~10
   closed-tautology lemmas directly, and to `sup_le_quot`/`le_trans_quot`/`le_inf_quot` via the
   tautology+pairing+MP extension (not the bare four-liner) to hit the line-count bar. Skip
   `le_antisymm_quot` (not `Derives`-shaped) and skip the `LindenbaumQuotient.provEquiv_*`
   extension entirely (nothing non-trivial fits). Fix the `PropDecideTest.lean` docstring and
   add the De Morgan-via-and/or case verified above as a regression test.
2. Item 2 (`ultrafilterEquiv`): proceed as specified — mechanical, low-risk, resolves D-16.
3. Item 3 (Mathlib reconciliation): drop the `PFilter`/`ofPFilterCompl` option (the bridge name
   doesn't exist); choose between the Ideal-side replacement (a) or the `BAUltrafilter` rename +
   bridge `Equiv` (b) — recommend (a) given no live consumer, but flag as a decision point for
   the user/planner rather than settling it here.
4. Item 4 (`fold_le_of_derives`): proceed as specified; `Multiset.inf`/`inf_coe`/`le_inf`/
   `inf_le` cover it directly, no `Finset` detour needed.
5. README refresh: add a "Last verified" stamp (currently absent, confirmed) alongside whichever
   choice is made in item 3.

## Files Read

- `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` (full, 441 lines)
- `FormalSystem/Metalogic/Algebraic/LindenbaumQuotient.lean` (relevant sections, ~1-260)
- `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` (targeted: structure def, correspondence
  theorems, `fold_le_of_derives`, both round-trip theorems)
- `FormalSystem/Metalogic/Algebraic/README.md` (full)
- `FormalSystem/Automation/Tactics/PropDecide.lean` (full, 158 lines)
- `FormalSystem/Automation/Tactics/Helpers.lean` (targeted: `extractDerivationGoal`,
  `isNilContext`)
- `Tests/BimodalTest/Metalogic/PropDecideTest.lean` (full)
- `.lake/packages/mathlib/Mathlib/Order/Ideal.lean`, `Mathlib/Order/PFilter.lean`,
  `Mathlib/Order/PrimeIdeal.lean` (targeted: `IsMaximal`, `IsPrime`, `PFilter` axioms)
- `.lake/packages/mathlib/Mathlib/Data/Multiset/Lattice.lean` (full, 90 lines) plus
  `lean_run_code` `#check` confirmation of the auto-generated `inf` duals
