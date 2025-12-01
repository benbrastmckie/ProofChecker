/-!
# ProofChecker Counterexamples

This directory contains counterexample constructions that demonstrate the limits
and boundaries of the bimodal logic TM and its task semantics.

## Overview

The Counterexamples directory follows the mathlib4 pattern of providing
carefully constructed counterexamples that illustrate:
- **Invalidity**: Formulas that are not theorems of TM
- **Independence**: Axioms that cannot be derived from others
- **Edge Cases**: Subtle semantic distinctions in task semantics
- **Boundaries**: Limits of what can be proven in the system

## Purpose

Counterexamples serve several important purposes:
- **Verification**: Ensuring the proof system is not too strong
- **Understanding**: Clarifying semantic subtleties
- **Completeness**: Demonstrating the proof system captures exactly the valid formulas
- **Education**: Teaching what cannot be proven and why

## Example Categories

### Invalidity Demonstrations
- Formulas that are satisfiable but not valid
- Modal axioms that fail in task semantics
- Temporal formulas that are contingent

### Independence Results
- Showing axioms are independent (cannot be derived from others)
- Demonstrating necessity of inference rules

### Edge Cases
- Subtle distinctions in task relations
- World history construction edge cases
- Convexity requirements for temporal operators

## Usage

Import specific counterexample modules:
```lean
import Counterexamples.Invalidity
import Counterexamples.EdgeCases
```

Or import the entire counterexamples library:
```lean
import Counterexamples
```
-/

-- Re-export counterexample modules when implemented
-- import Counterexamples.Invalidity
-- import Counterexamples.EdgeCases

namespace Counterexamples

def version : String := "0.1.0"

end Counterexamples
