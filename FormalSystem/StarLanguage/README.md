# StarLanguage — the language L⋆ (L⁺ plus the stability modal `⊡`)

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
embedding commutes with each of them by `rfl`.

## Modules

| File | Description |
|------|-------------|
| `Formula.lean` | `StarFormula`, the derived operators (with `Formula`'s right-hand sides), the `⊡`-specific `dstab`/`Will`/`will`/`Could`/`could`, `swapTemporal` (`stab ↦ stab`), the purity predicates `IsPureFuture`/`IsPurePast` with their `swapTemporal` exchange lemmas, and the embedding `ofFormula`/`ofCtx` with `ofFormula_injective`, `ofFormula_ne_stab`, `ofFormula_swapTemporal` |

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
The invariant is directional, exactly as for `BaseLanguage/`: the converse edge is permitted,
and it is how L⋆ acquires its semantics (`FormalSystem/Semantics/StarTruth.lean` imports
`Formula.lean` to define `StarTruthAt` natively on the seven constructors).

## Related Documentation

- [FormalSystem README](../README.md)
- [BaseLanguage README](../BaseLanguage/README.md) — the pattern this component follows
- [Syntax README](../Syntax/README.md) — the L⁺ side being embedded
