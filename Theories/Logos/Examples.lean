import Bimodal.Examples

/-!
# Logos Examples Aggregator

Imports examples from all Logos layers.

## Current Examples

- `Bimodal.Examples` - TM Logic (Layer 0) examples
  - Bimodal proof examples (perpetuity principles)
  - Temporal proof strategy tutorials
  - Temporal structure examples

Note: Basic modal/temporal proof exercises (ModalProofs, ModalProofStrategies,
TemporalProofs) were moved to Boneyard/Examples/ by Task 760 to reduce sorry
count in the main codebase.

## Future Layer Examples

- `Logos.Dynamics.Examples` (Layer 1) - Causal reasoning examples
- `Logos.Epistemic.Examples` (Layer 2) - Knowledge reasoning examples
- `Logos.Normative.Examples` (Layer 3) - Normative reasoning examples

## Usage

Import all examples:
```lean
import Logos.Examples
```

Import specific example categories:
```lean
import Bimodal.Examples.BimodalProofs
import Bimodal.Examples.TemporalProofStrategies
```

For archived examples with exercises:
```lean
import Bimodal.Boneyard.Examples.ModalProofs
import Bimodal.Boneyard.Examples.TemporalProofs
```
-/

namespace Logos.Examples
-- Intentionally empty: importing this module provides the example namespaces.
-- Examples are now provided via Bimodal.Examples.
end Logos.Examples
