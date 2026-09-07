# Metalogic/Conservativity

The three conservativity questions this development answers, and the one it refuses to attempt.

| Extension | Direction | Status |
|-----------|-----------|--------|
| L ⊂ L⁺ (TM into TM⁺, via `tr`) | backward | **proved** — `derivable_translate` and the four row corollaries |
| L ⊂ L⁺ | forward | **refuted** at `.Base` and `.ZTime`, open at `.Dense` and `.RTime` |
| L⁺ ⊂ L⋆ (TM⁺ into TM⋆, via `ofFormula`) | both | **proved** at all four classes — `starDerivable_ofFormula_iff` |

Per-theorem status — statement, frame class, machine-pinned axiom set — is in
[`docs/theorem-index.md`](../../../docs/theorem-index.md), the single ledger. The standing
prohibition on attempting or `sorry`-ing the forward direction of L ⊂ L⁺, with the CEB/CEF/CED/CEC
row analysis that grounds it, is in the aggregator
[`../Conservativity.lean`](../Conservativity.lean) and is not repeated here.

**Do not state a forward-conservativity theorem for L ⊂ L⁺.** It is provably false at
`fc := .Base` and `fc := .ZTime`, so a `sorry` on it would be an unsound placeholder rather
than deferred debt.

## Modules

<!-- BEGIN GENERATED: inventory dir=FormalSystem/Metalogic/Conservativity -->
| File | Lines | Description |
|------|------:|-------------|
| `Backward.lean` | 208 | <!-- TODO: add description --> |
| `BaseLanguageSoundness.lean` | 547 | <!-- TODO: add description --> |
| `Fragment.lean` | 180 | <!-- TODO: add description --> |
| `FragmentCompactness.lean` | 150 | <!-- TODO: add description --> |
| `SpWitness.lean` | 128 | <!-- TODO: add description --> |
| `Star.lean` | 65 | <!-- TODO: add description --> |
| `TMCompletenessReduction.lean` | 192 | <!-- TODO: add description --> |
| `Z1Countermodel.lean` | 202 | <!-- TODO: add description --> |
| `Star/` | — | <!-- TODO: add description --> |
<!-- END GENERATED -->

## Key Results

- `translate` / `derivable_translate` — the backward bridge, by structural recursion over TM
  derivations, parameterized by `FrameClass` so the paper's four rows are four instantiations
- `ceb_backward`, `cef_backward`, `ced_backward`, `cec_backward` — the four row corollaries
- `bl_soundness{,_dense,_ztime,_rtime}` — soundness of BL against the **native** `BLTruthAt`
  semantics, obtained by composing `translate` with the TM⁺ soundness theorems across the
  truth-transfer bridge `Semantics.truthAt_tr`
- `TMFrag` and its metatheory — the H/G-fragment of TM⁺ is the complete logic of base-language
  validity, which TM itself is not
- `tmCompleteBase_iff_forwardBase` and its `.ZTime` mirror — equivalences between two unasserted
  `Prop`s, proving neither side
- `starDerivable_ofFormula_iff` — conservativity of TM⋆ over TM⁺ in both directions

## Related Documentation

- [Metalogic README](../README.md)
- [`Star/`](Star/README.md) — the L⋆ half
- [`../Conservativity.lean`](../Conservativity.lean) — the aggregator and the standing prohibition
- [`docs/theorem-index.md`](../../../docs/theorem-index.md) — per-theorem status

---

*Last verified: 2026-09-07*
