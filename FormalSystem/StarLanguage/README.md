# StarLanguage — the language L⋆ (L⁺ plus the time store/recall operators)

This directory defines a **fourth object language** for the tree, **L⋆**, obtained from L⁺
(`FormalSystem/PlusLanguage/`) by adding the manuscript's two hybrid **time registers**:

```
φ, ψ ::= pᵢ | ⊥ | φ → ψ | □φ | φ U ψ | φ S ψ | ⊡φ | ↑ⁱφ | ↓ⁱφ
```

`↑ⁱ` (`timeStore i`) writes the present time into register `i`; `↓ⁱ` (`timeRecall i`) moves the
point of evaluation to the time register `i` holds. This is the manuscript's `\BL^\star` in the
presentation `def:BLstar-semantics` gives it for the deterministic-frame appendix: points are
`(τ, x, v⃗)` with `v⃗` a vector of stored **times**, and the world registers `↑_M`/`↓_M` are
suppressed.

L⋆ is a **separate inductive** (`StarFormula`) with a constructor-to-constructor embedding
`ofPlus : PlusFormula → StarFormula`, following the landed `MinusLanguage/` and `PlusLanguage/`
pattern. Every derived operator has `PlusFormula`'s right-hand side verbatim, so the embedding
commutes with each of them by `rfl`.

## Why the operators are not added to `PlusFormula`

The atomization route to TM⁺ soundness
(`Metalogic/Conservativity/Plus/Atomization.lean`) rests on `stab_state_only`
(`Semantics/PlusTruth.lean`): `⊡φ`'s truth depends on the world state **alone**, at any time.
That invariant is **false inside a recall scope** — `⊡↓ⁱφ` reaches back to a time the register
names, which the present world state does not determine — so adding `timeStore`/`timeRecall` to
`PlusFormula` would silently invalidate a landed conservativity result. Breaking the invariant is
the whole point of this language, and it must be broken in a *separate* type.

## Modules

| File | Description |
|------|-------------|
| `Formula.lean` | `StarFormula`, the derived operators (with `PlusFormula`'s right-hand sides), the `⊡`-specific `dstab`/`Will`/`will`/`Could`/`could`, `swapTemporal` (`stab ↦ stab`, and both registers structural) with `swap_temporal_involution` and the `swap_temporal_*` push-through family, and the embedding `ofPlus`/`ofStarCtx` with `ofPlus_injective`, `ofPlus_ne_timeStore`, `ofPlus_ne_timeRecall`, `ofPlus_swapTemporal` and the `rfl` commutation pins |
| `Axioms.lean` | `StarAxiom` — TM⋆'s axiom set: one `ofBase` arm carrying every TM⁺ schema at its `ofPlus` instances, plus the sixteen register schemata of the store/recall block; `StarAxiom.minFrameClass` |
| `Derivation.lean` | `StarDerivationTree` (the seven TM⁺ rules, verbatim), the notation `⊢⋆[fc]`, `StarDerivable` with `StarDerivable.mono`, the structural apparatus `lift`/`height`/`ofWeakeningNil`, and the derived `stabNecessitationOfPlus` |

The sibling aggregator is `FormalSystem/StarLanguage.lean`.

## The proof system TM⋆: `StarAxiom` is declared

`StarAxiom` (`Axioms.lean`) is TM⋆'s axiom set. The manuscript supplies no proof system for
`\BL^\star` — every result this component was originally built for is semantic — so TM⋆ is a
formalization-native system, built to the shape of `PlusAxiom`/`PlusDerivationTree` so that the
two are structurally comparable and the L⁺ ⊂ L⋆ questions can be *stated*.

The one structural decision worth naming here is the **`ofBase` embedding**. `PlusAxiom`
re-declares the 45 TM schemata over `PlusFormula`; `StarAxiom` does not re-declare them over
`StarFormula`, because one of them — `modal_future`, `□φ → □Gφ` — is *refuted* there
(`refute_modal_future`, `Semantics/StarNonValidities.lean`). MF is the only schema in the TM
block whose soundness proof consumes time-shift homogeneity, and the L⋆ time-shift lemma shifts
the stored-time vector with the history. A single `ofBase` constructor therefore carries every
TM⁺ schema at exactly the `ofPlus` instances where it is sound. **The recorded cost**: TM⋆'s
inherited temporal schemata are available only at register-free instances.

`StarDerivationTree`, the notation `⊢⋆[fc]` and the name TM⋆ for the resulting system are
declared in `Derivation.lean`: the same seven inference rules as TM⁺ and TM, constructor for
constructor, with `StarAxiom` in the `axiom` rule.

**One consequence of `ofBase` worth stating in the open.** In TM⁺, `⊡`-necessitation
(`⊢ φ ⟹ ⊢ ⊡φ`) is derivable at every formula, via `necessitation` and MS (`□φ → ⊡φ`). In TM⋆ the
derivation reaches only embedded formulas — `stabNecessitationOfPlus` is stated at exactly that
strength — because MS arrives only as `StarAxiom.ofBase _ (PlusAxiom.box_stab _)`. At a
register-containing `φ` the rule is still **sound** (the `stab` clause merely restricts the `box`
clause's quantifier) but is not derivable from this axiom set. Nothing in the metatheory below
consumes it; it is recorded rather than repaired by a native `box_stab` schema, which would be
sound but would widen `StarAxiom` beyond one embedding arm plus the register block.

## Where the L⋆ semantics lives

Nothing in this directory defines truth, validity, or a frame. The semantics sits on the far side
of the permitted import edge:

| File | What it carries |
|------|-----------------|
| `FormalSystem/Semantics/StarTruth.lean` | `StarTruthAt` over `(τ, x, v⃗)`; the `StarTruth.*` clause lemmas; `starTruthAt_ofPlus`; the transport layer `star_truth_congr_ext`, `update_shift_comm`, `starTruthAt_timeShift` |
| `FormalSystem/Semantics/StarValidity.lean` | `TaskFrame.StarValidOn`, `StarValidOnFrames`, `StarValidIn`, `StarValid`; `starValidOn_ofPlus`; `settledDisj`, `sentDet`, `sentDet_unfold`, `not_starValidOn_sentDet` |
| `FormalSystem/Semantics/StarDeterminism.lean` | `star_congr_of_deterministic`, `sentDet_of_deterministic`, `detPM`, `detPM_unfold`, `detPM_of_deterministic`, `deterministic_of_detPM`, `deterministic_starDefinable` |
| `FormalSystem/Semantics/StarNonValidities.lean` | `refute_sentDet`, `not_starValid_sentDet` |
| `FormalSystem/Semantics/StarStateLocal.lean` | `StarFormula.StateLocal` (syntactic) and `IsStateLocal` (semantic); `isStateLocal_box`, `isStateLocal_stab`, `isStateLocal_of_stateLocal`; `not_isStateLocal_someFuture`, `not_isStateLocal_somePast`, `not_isStateLocal_timeRecall`; `stateLocal_stab_iff`, `stateLocal_starValid_iff_stab` |
| `FormalSystem/Metalogic/Independence/StarDiscrimination.lean` | `driftLinear`, `fzero_refutes_sentDet`, `f1_sentDet`, `sentDet_discriminates`, `star_discriminates_where_plus_cannot` |
| `FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean` | `fnRel`, `FN`, `fn_forwardDeterministic`, `fn_not_deterministic`, `states_eq_of_forwardDeterministic`, `fn_sentDet_stateLocal`, `fn_separates`, `fn_refutes_sentDet_somePast`, `fn_sentDet_bounds` |

## Paper-label correspondence

Every manuscript `\label` this component touches, mapped to a Lean declaration or to an explicit
exclusion. Anchors are cited by `\label` only, never by line number.

| Paper anchor | Claim | Lean |
|---|---|---|
| `def:BLstar-semantics` (store/recall clauses) | `M,τ,x,v⃗ ⊨ ↑ⁱφ` iff `M,τ,x,v⃗[x/vᵢ] ⊨ φ`; `M,τ,x,v⃗ ⊨ ↓ⁱφ` iff `M,τ,vᵢ,v⃗ ⊨ φ` | `Semantics/StarTruth.lean` — the `timeStore`/`timeRecall` clauses of `StarTruthAt`, with `StarTruth.timeStore_iff` / `StarTruth.timeRecall_iff` |
| `def:BLstar-semantics` (world registers `↑_M`, `↓_M`) | — | **Excluded**: world registers are suppressed on the main path, exactly as the deterministic-frame appendix suppresses them. A single-world-register `Det-m` was declared optional at plan time and is not built |
| `lem:deterministic-singleton` (⇒) | Deterministic ⟹ `⟨τ⟩_x = {τ}` | `states_eq_of_deterministic` (`Semantics/PlusDeterminism.lean`), restated at the predicate as `singletonClasses_of_deterministic` (`Semantics/DeterministicBridge.lean`); choice-free |
| `lem:deterministic-singleton` (⇐) | `⟨τ⟩_x = {τ}` ⟹ Deterministic | `deterministic_of_singletonClasses` (`Semantics/DeterministicBridge.lean`); a theorem of **ZFC**, via `thm:extension` |
| `lem:deterministic-singleton` (biconditional) | the two together | `deterministic_iff_singletonClasses` |
| `sent:det` | `↑¹\Future↑²↓¹(⊡↓²¬φ ∨ ⊡↓²φ)` | `sentDet` (`Semantics/StarValidity.lean`); `\Future` is the manuscript's **universal** future, so the tree's `allFuture` |
| `app:deterministic-future` (`(∗)` chain) | the four-line unfolding | `sentDet_unfold` |
| `app:deterministic-future` (positive half) | `sent:det` valid over every deterministic frame | `sentDet_of_deterministic` (`Semantics/StarDeterminism.lean`) |
| `app:deterministic-future` (negative half) | `sent:det` invalid over some non-deterministic frame | `refute_sentDet` (`Semantics/StarNonValidities.lean`), over `NF` — the manuscript's own reused countermodel |
| footnote after `app:deterministic-future` | store/recall discriminate `F°` from `F¹` | `fzero_refutes_sentDet`, `f1_sentDet`, `sentDet_discriminates`, `star_discriminates_where_plus_cannot` (`Metalogic/Independence/StarDiscrimination.lean`) |
| `app:drift` | `F°` is a non-deterministic frame validating *Determined* | already landed: `Metalogic/Independence/DriftFrame.lean`, `DeterminismUndefinable.lean` |
| `cor:no-characterization` | no store/recall-free sentence set characterizes the deterministic frames | already landed: `deterministic_not_plusDefinable` (`Metalogic/Independence/DeterminismUndefinable.lean`) |
| `cor:saturation-finite` (finite-**fibres** variant) | *Saturation* from finite fibres | `TaskFrame.saturation_of_fib_finite` (`Semantics/TaskFrame.lean`) — not a paper result; the paper's corollary is the finite-**carrier** one, which does not reach `FN` |
| Theorem C, `Det-pm` half (report-level) | `Det-pm` defines the deterministic frames, as a three-way equivalence: `Det-pm`'s validity at bare sentence letters already **forces** determinism, and determinism **delivers** `Det-pm` at every `StarFormula` | `detPM` (schematic), `deterministic_starDefinable` (`Semantics/StarDeterminism.lean`) |
| Theorem C, `Det-m` half (report-level) | `Det-m` defines the deterministic frames | **Excluded**: needs a world register, declared optional at plan time and not built |
| `sent:det` defines only *forward* determinism (report-level) | separating frame `F^N`, with the validity widened from sentence letters to the whole **state-locality** fragment and the two-sided bound recorded as one object | `FN`, `fn_forwardDeterministic`, `fn_not_deterministic`, `fn_sentDet_stateLocal`, `fn_separates`, `fn_sentDet_bounds` (`Metalogic/Independence/ForwardDeterministicFrame.lean`) |
| state-locality of L⋆ (no paper anchor) | a state-local `φ` is already `⊡`-stable: `φ ↔ ⊡φ` is valid on the fragment, and `□`/`⊡` belong to it for an *arbitrary* argument | `StarFormula.StateLocal`, `isStateLocal_of_stateLocal`, `stateLocal_starValid_iff_stab` (`Semantics/StarStateLocal.lean`) — **not a manuscript result**; it is the structural closure of the reason the sentence-letter form gave for itself |
| TM⋆ (a proof system for L⋆) | — | **Excluded**: the manuscript supplies none, and every deliverable here is semantic. `StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are reserved, unbuilt names |

**Report-level results are cited as such.** `Det-pm`, `Det-m`, and the forward-determinism
sharpening are recorded in the PossibleWorlds repository's determinism-axiom-correspondence
report (`reports/02_determinism-axiom-correspondence.md`, §3.2, §3.3, §4) and are **pending paper
integration**. They are never cited as manuscript text and never as conjectures.

**One recorded divergence from that report's Theorem A, now bounded from both sides.**
`fn_sentDet_stateLocal` is stated at every **state-local** instance, not schematically. The
schematic form is *refutable* over `F^N`, and `fn_refutes_sentDet_somePast` is the
machine-checked refutation: forward determinism settles the future and says nothing about the
past, so a past-looking instance such as `P p` distinguishes two possible worlds of the same
stability class at a *future* time. Theorem A itself is stated at the sentence-letter level (it
runs the singleton valuation `|p| = {τ(y)}`), so nothing in the report is contradicted — the
Lean statement is *stronger* than Theorem A on the positive side, and the schematic reading must
still not be assumed.

The restriction is no longer an artifact. The sentence-letter form gave as its reason "an atom's
truth depends on nothing but the state at the time of evaluation" — a reason about
state-locality, not about atoms. `StarFormula.StateLocal` (`Semantics/StarStateLocal.lean`) is
that reason cut as a syntactic fragment, and `fn_sentDet_bounds` records the resulting two-sided
bound as a single machine-checked object: valid at every state-local instance, refuted at `P p`,
which the middle conjunct certifies lies outside the fragment.

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
Checkable by `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/`. The invariant
is directional, exactly as for `MinusLanguage/` and `PlusLanguage/`; the converse edge is
permitted and is how L⋆ acquires its semantics.

## References

* JPL paper `possible_worlds.tex` — `def:BLstar-semantics`, `sub:Extension`, `sent:det`,
  `app:deterministic-future`, `app:drift`, `cor:no-characterization`,
  `lem:deterministic-singleton`, `thm:extension`
* `FormalSystem/PlusLanguage/README.md` — L⁺, the language this one extends
* The PossibleWorlds `02_determinism-axiom-correspondence.md` report — Theorem C and the
  forward-determinism sharpening, both pending paper integration
