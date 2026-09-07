# ProofSearch

Bounded proof search infrastructure for TM bimodal logic.

This subdirectory contains the core search engine and search strategies used by the
Automation layer to find derivations up to a given depth bound.

## Modules

| File | Lines | Description |
|------|-------|-------------|
| `Core.lean` | 1018 | Proof search core engine: depth-limited derivation search, term enumeration |
| `Strategies.lean` | 379 | Search strategies: heuristic ordering, pruning rules, backtracking policies |

## Key Definitions

- Core search functions for bounded derivation discovery
- Strategy combinators for guiding proof search
- Integration point for `tm_auto` and other high-level tactics

## Dependencies

- **Imports from**: `FormalSystem.ProofSystem`, `FormalSystem.Syntax`
- **Used by**: `FormalSystem.Automation.Tactics` (provides the `modal_search` search engine)

## Related Documentation

- [Automation README](../README.md)
- [Tactics subdirectory](../Tactics/README.md)

---

*Last verified: 2026-09-07*
