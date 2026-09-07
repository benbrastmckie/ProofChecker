# Metalogic/Conservativity/Star

The stability extension L⋆ = L⁺ plus the paper's stability modal `⊡`, and its logic TM⋆.

This is the mirror image of L ⊂ L⁺ with the **hard direction available**. Forward conservativity
fails for L ⊂ L⁺ because TM is incomplete; for L⁺ ⊂ L⋆ the same composition succeeds, because
TM⁺ *is* complete at every class carrying a `WeakCompleteness` engine: forward is TM⋆ soundness
plus the truth-transfer bridge `starValidIn_ofFormula_iff` plus that engine.

TM⋆'s axioms are the 45 TM⁺ schemata re-declared over `StarFormula` (so `□⊡p → □G⊡p` is an MF
instance), plus S5 for `⊡`, `□φ → ⊡φ`, `p → ⊡p` for atoms, and two pasting schemata with
pure-future / pure-past side conditions (`Semantics/StarPasting.lean`). The five refutations in
`Semantics/StarNonValidities.lean` bound that set from above.

TM⋆ **completeness and decidability are open** and are not asserted anywhere. One durable fact
bears on any attempt: the countermodels of all four completeness engines are *deterministic*, so
on them `⊡` is the identity and none of the engines transfers to L⋆.

## Modules

<!-- BEGIN GENERATED: inventory dir=FormalSystem/Metalogic/Conservativity/Star -->
| File | Lines | Description |
|------|------:|-------------|
| `Atomization.lean` | 241 | <!-- TODO: add description --> |
| `AxiomValidity.lean` | 276 | <!-- TODO: add description --> |
| `Forward.lean` | 167 | <!-- TODO: add description --> |
| `StarSoundness.lean` | 189 | <!-- TODO: add description --> |
<!-- END GENERATED -->

## Key Results

- `star_soundness_validIn` — soundness of TM⋆ at every frame class, with TD discharged
  semantically by the companion recursion and the TM⁺ schemata over L⋆ handled by atomization
- `starDerivable_ofFormula_iff` — proof-theoretic conservativity of TM⋆ over TM⁺ in **both**
  directions, at all four classes

## Related Documentation

- [Conservativity README](../README.md)
- [`FormalSystem/StarLanguage/`](../../../StarLanguage/README.md) — `StarFormula`, `StarAxiom`,
  `StarDerivationTree`, `ofFormula`
- [`Semantics/StarTruth.lean`](../../../Semantics/StarTruth.lean) — the L⋆ truth recursion
- [`docs/theorem-index.md`](../../../../docs/theorem-index.md) — per-theorem status

---

*Last verified: 2026-09-07*
