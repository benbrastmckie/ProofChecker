# Tactics

Custom Lean 4 tactic implementations for TM bimodal logic proof development.

This subdirectory contains the tactic elaboration code and helper utilities that
implement the `apply_axiom`, `modal_t`, `tm_auto`, and related tactics.

## Modules

<!-- BEGIN GENERATED: inventory dir=FormalSystem/Automation/Tactics -->
| File | Lines | Description |
|------|-------|-------------|
| `Commands.lean` | 755 | Tactic command elaborators: `apply_axiom`, `modal_t`, `tm_auto`, `assumption_search` |
| `Deduction.lean` | 150 | `deduction`, `deduction n` and `undischarge`: frame-class-polymorphic applications of `Metalogic.Core.deductionTheorem` to derivability goals |
| `Helpers.lean` | 1,210 | Tactic helper infrastructure: term construction, goal manipulation, MetaM utilities |
| `PropDecide.lean` | 158 | `propDecide`: reflective tautology tactic closing any derivability goal whose imp/bot skeleton is a propositional tautology, schematic in the reification environment |
<!-- END GENERATED -->

## Key Definitions

- `apply_axiom`: Macro-based tactic that applies a TM axiom by name
- `modal_t`: Elaboration rule for reflexivity (Modal T axiom application)
- `tm_auto`: Comprehensive automation via Aesop with TMLogic rule set
- `assumption_search`: Search for a matching formula in the current context

## Dependencies

- **Imports from**: `FormalSystem.ProofSystem`, `FormalSystem.Automation.AesopRules`
- **Used by**: `FormalSystem.Automation` (re-exported), downstream proofs

## Related Documentation

- [Automation README](../README.md)
- [ProofSearch subdirectory](../ProofSearch/README.md)

---

*Last verified: 2026-09-07*
