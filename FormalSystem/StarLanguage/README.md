# StarLanguage — the language L⋆ (L⁺ plus the stability modal `⊡`) and its logic TM⋆

This directory defines a **third object language** for the tree, **L⋆**, obtained from the
until/since-primitive language L⁺ (`FormalSystem/Syntax/Formula.lean`) by adding one primitive
unary operator, the **stability modal** `⊡` (paper `possible_worlds.tex`, line 1114):

```
φ, ψ ::= pᵢ | ⊥ | φ → ψ | □φ | φ U ψ | φ S ψ | ⊡φ
```

`⊡φ` holds at `(τ, x)` iff `φ` holds at `(σ, x)` for every world `σ` sharing `τ`'s world state
at `x`. The paper's own `\BL^\star` (line 1374) additionally carries store/recall operators;
those are **out of scope** — L⋆ here is L⁺ plus `⊡` only.

L⋆ is a **separate inductive** (`StarFormula`) with a constructor-to-constructor embedding
`ofFormula : Formula → StarFormula`, following the landed `BaseLanguage/` pattern
(`BLFormula` and `tr`). Every derived operator has `Formula`'s right-hand side verbatim, so the
embedding commutes with each of them by `rfl` — the contract the proof-system embedding and the
atomization transfer rely on.

## Modules

| File | Description |
|------|-------------|
| `Formula.lean` | `StarFormula`, the derived operators (with `Formula`'s right-hand sides), the `⊡`-specific `dstab`/`Will`/`will`/`Could`/`could`, `swapTemporal` (`stab ↦ stab`), the purity predicates `IsPureFuture`/`IsPurePast` with their `swapTemporal` exchange lemmas, and the embedding `ofFormula`/`ofCtx` with `ofFormula_injective`, `ofFormula_ne_stab`, `ofFormula_swapTemporal` |
| `Axioms.lean` | `StarAxiom`, the **closed** inductive of TM⋆ schemata: the 45 TM⁺ schemata re-declared with `StarFormula` parameters, plus eight `⊡` schemata — SK, ST, S4, S5 (S5 for `⊡`), MS `□φ → ⊡φ`, AS `p → ⊡p` for atoms, and the two pasting schemata PS `⟐φ⁺ → (⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻))` and US `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)` with pure-future/pure-past side conditions; `StarAxiom.minFrameClass` |
| `Derivation.lean` | `StarDerivationTree` (the seven rules of TM⁺, constructor for constructor), `StarDerivable`, `⊢⋆[fc]` notation, the derived `⊡`-necessitation rule `stabNecessitation`, and the backward conservativity bridge `StarAxiom.ofPlus` / `StarDerivationTree.ofPlus` / `starDerivable_of_derivable`: `TM⁺ ⊢[fc] φ ⟹ TM⋆ ⊢[fc] ofFormula φ` |

The sibling aggregator is `FormalSystem/StarLanguage.lean`.

## Why the TM⁺ schemata are re-declared

An embedding constructor `Axiom φ → StarAxiom (ofFormula φ)` would yield only `⊡`-free instances;
TM⋆ needs, for instance, MF at `⊡p` (`□⊡p → □G⊡p`). So the 45 schemata range over all of
`StarFormula`, and `StarAxiom.ofPlus` is a *function* used only for the backward bridge — each
of its arms is `rfl`-shaped, so any drift between the two inductives fails to typecheck there.

## Where the L⋆ semantics and metatheory live

Nothing in this directory defines truth, validity, or a frame. The semantics sits on the far
side of the permitted import edge:

| File | What it carries |
|------|-----------------|
| `FormalSystem/Semantics/StarTruth.lean` | `SameStateAt` (the paper's `⟨τ⟩_x`) and `StarTruthAt`, the seven-clause truth recursion; the S5 validities of `⊡`; `stab_state_only` |
| `FormalSystem/Semantics/StarValidity.lean` | `StarValidOnFrames`, `StarValidIn`, `StarValid`; `starTruthAt_ofFormula` and `starValidIn_ofFormula_iff` (semantic conservativity at every class) |
| `FormalSystem/Semantics/StarPasting.lean` | the history-pasting lemma and the pasting validities PS/US/FS/GS with their past mirrors |
| `FormalSystem/Semantics/StarNonValidities.lean` | the five refutations on `natFrame` over ℤ that bound the axiom set |
| `FormalSystem/Metalogic/Conservativity/Star.lean` | soundness of TM⋆ at all four classes and conservativity of TM⋆ over TM⁺ in both directions |

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
Checkable by `grep -rn 'FormalSystem.Semantics' FormalSystem/StarLanguage/`: only prose matches.
The invariant is directional, exactly as for `BaseLanguage/`; the converse edge is permitted and
is how L⋆ acquires its semantics.

## Extension recipe: adding a `StarAxiom` constructor

`StarAxiom` is closed, and exactly three declarations pattern-match on its constructors:

1. `StarAxiom.minFrameClass` (`Axioms.lean`);
2. `starAxiom_validIn_min` (`FormalSystem/Metalogic/Conservativity/Star/AxiomValidity.lean`);
3. `starAxiom_swap_validIn_min` (same file).

Neither dispatch lemma has a wildcard arm. Adding a constructor therefore means one constructor
line, one `minFrameClass` arm, and one arm in each dispatch lemma (a validity proof and a
swap-validity proof, typically a `StarValid` from `Semantics/`); every other module —
`StarDerivationTree`, `ofPlus`, the soundness recursion, the conservativity theorems — refers to
`StarAxiom` only through `minFrameClass` and the two lifted forms `starAxiom_validIn` /
`starAxiom_swap_validIn`, and recompiles unchanged. A schema valid only over a restricted frame
class no `FrameClass` tag denotes (for instance *Determined* `φ → ⊡φ`, refuted at `.Base`) must
**not** be added here; state its validity through `StarValidOnFrames` over that predicate
instead.

## Related Documentation

- [FormalSystem README](../README.md)
- [BaseLanguage README](../BaseLanguage/README.md) — the pattern this component follows
- [Syntax README](../Syntax/README.md) — the L⁺ side being embedded
- [Semantics README](../Semantics/README.md) — where the `Star*.lean` semantics modules live
- [Metalogic README](../Metalogic/README.md) — where `Conservativity/Star/` lives

---

*Last verified: 2026-09-07*
