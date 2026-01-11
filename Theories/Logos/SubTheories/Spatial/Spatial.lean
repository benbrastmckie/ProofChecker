/-!
# Logos.Spatial - Layer 4 (Spatial Extension)

This layer extends Core TM logic with spatial operators:
- Location operators (`Here`, `Somewhere`, `Everywhere`)
- Proximity operators (`Near`)

## Frame Extension

The spatial frame extends the core frame with:
- **Location space** L = set of spatial locations
- **Spatial relations**: adjacency, containment, distance

**Open Question**: Should locations be mereological (with parts) or set-theoretic?

## Operators

| Operator | Reading |
|----------|---------|
| `Here(A)` | A holds at the current location |
| `Somewhere(A)` | A holds at some location |
| `Everywhere(A)` | A holds at all locations |
| `Near(A)` | A holds at an adjacent location |

**Status**: Planned for future development
**Prerequisites**: Explanatory Extension (Core) completion

See: docs/Research/layer-extensions.md Section 5
-/

namespace Logos.SubTheories.Spatial
  -- Layer 4 implementation to be added
  -- Extension point: Formula type will extend Core.Syntax.Formula
  -- Extension point: Semantics will use LocationSpace
  -- Extension point: Frame will add spatial relations (adjacency, containment, distance)
end Logos.SubTheories.Spatial
