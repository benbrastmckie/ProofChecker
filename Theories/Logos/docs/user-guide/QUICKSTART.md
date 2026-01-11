# Logos Quick Start

Getting started with Logos logic.

## Current Implementation Status

Logos currently **re-exports Bimodal** TM (Tense and Modality) logic. This means:

- All Logos imports resolve to Bimodal implementations
- Logos provides the same propositional intensional logic as Bimodal
- The Logos namespace is a compatibility layer for future extensions

## Getting Started

Since Logos re-exports Bimodal, follow the Bimodal quick start guide:

**→ [Bimodal Quick Start](../../../Bimodal/docs/user-guide/QUICKSTART.md)**

## Using Logos vs Bimodal

### When to Import Logos

Use Logos imports if:
- You want future compatibility with hyperintensional extensions
- Your code should work with both propositional and (future) second-order logic
- You're developing modules that will integrate with planned extensions

```lean
import Logos
-- Currently equivalent to: import Bimodal
```

### When to Import Bimodal

Use Bimodal imports if:
- You specifically need propositional intensional logic
- You don't need compatibility with future extensions
- You want to be explicit about which theory you're using

```lean
import Bimodal
```

## Future Extensions

Logos will eventually extend beyond Bimodal with:

| Extension | Description | Status |
|-----------|-------------|--------|
| Epistemic | Knowledge and belief operators | Stub only |
| Normative | Obligation and permission operators | Stub only |
| Explanatory | Explanation and grounding operators | Stub only |

For details on planned extensions, see [CURRENT_STATUS.md](CURRENT_STATUS.md).

## Next Steps

1. Follow [Bimodal Quick Start](../../../Bimodal/docs/user-guide/QUICKSTART.md)
2. Read [Current Status](CURRENT_STATUS.md) for Logos-specific development
3. See [Theory Comparison](../../../docs/research/theory-comparison.md) for differences

## See Also

- [Bimodal Documentation](../../../Bimodal/docs/) - Working implementation
- [Theory Comparison](../../../docs/research/theory-comparison.md) - Bimodal vs Logos
- [Roadmap](../project-info/ROADMAP.md) - Development plans
