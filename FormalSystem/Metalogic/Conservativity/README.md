# Metalogic/Conservativity

The three conservativity questions this development answers, and the one it refuses to attempt.

| Extension | Direction | Status |
|-----------|-----------|--------|
| L ⊂ L⁺ (TM into TM⁺, via `tr`) | backward | **proved** — `derivable_translate` and the four row corollaries |
| L ⊂ L⁺ | forward | **refuted** at `.Base` and `.ZTime` — both rows machine-checked (`tmCompleteBase_refuted`, `tmCompleteZTime_refuted`); open at `.Dense` and `.RTime` |
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
| `Backward.lean` | 211 | <!-- TODO: add description --> |
| `BaseLanguageSoundness.lean` | 613 | <!-- TODO: add description --> |
| `DenseObstructionTransfer.lean` | 287 | Machine-checked evidence that neither closed row's separating witness transfers to the dense classes: `Sp` is a theorem of both `TM_d` and `TM_dc` (`sp_derivable_dense`, `sp_derivable_rtime`), and `Z1` is refuted on the flow frame over ℚ (`not_blValidDense_z1`) |
| `Fragment.lean` | 190 | <!-- TODO: add description --> |
| `FragmentCompactness.lean` | 150 | <!-- TODO: add description --> |
| `SpCountermodel.lean` | 390 | CEB's failing half: native BL soundness for TM against `Semantics/BLFrame.lean`'s `TaskFrame`-free semantics (`blFrameValid_of_axiom`, `blFrameValid_of_derivation`), the two-fibre countermodel `ℤ ⊕ ℝ`, and the deliverables `not_derivable_sp` and `tmCompleteBase_refuted` |
| `SpWitness.lean` | 138 | <!-- TODO: add description --> |
| `Star.lean` | 65 | <!-- TODO: add description --> |
| `TMCompletenessReduction.lean` | 192 | <!-- TODO: add description --> |
| `Z1Countermodel.lean` | 205 | <!-- TODO: add description --> |
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
- `not_derivable_sp` / `tmCompleteBase_refuted` — the CEB row's failing half: the schema `(Sp)`
  is not a TM-theorem, refuted on the disjoint sum `ℤ ⊕ ℝ` over the native, `TaskFrame`-free
  `BLFrame` semantics, with `blFrameValid_of_derivation` supplying the soundness
  step the composition route could not
- `not_bl_derivable_z1` / `tmCompleteZTime_refuted` — the same for the CEF row over ℤ-time
- `sp_derivable_dense` / `sp_derivable_rtime` / `not_blValidDense_z1` — the two closed rows'
  separating witnesses provably fail to transfer to `.Dense` and `.RTime`: `Sp` is a *theorem* of
  both open systems, and `Z1` is not a validity of the dense class. Evidence about the two open
  rows, and **not** a completeness result; the four-row status is in
  `TMCompletenessReduction.lean`'s module docstring
- `starDerivable_ofFormula_iff` — conservativity of TM⋆ over TM⁺ in both directions

## Related Documentation

- [Metalogic README](../README.md)
- [`Star/`](Star/README.md) — the L⋆ half
- [`../Conservativity.lean`](../Conservativity.lean) — the aggregator and the standing prohibition
- [`docs/theorem-index.md`](../../../docs/theorem-index.md) — per-theorem status

---

*Last verified: 2026-09-07*
