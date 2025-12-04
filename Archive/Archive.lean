-- Re-export archive modules
import Archive.ModalProofs
import Archive.TemporalProofs
import Archive.BimodalProofs
import Archive.TemporalStructures

/-!
# ProofChecker Archive

This directory contains pedagogical examples, famous proofs, and historical
examples demonstrating the ProofChecker library's capabilities.

## Overview

The Archive follows the mathlib4 pattern of providing well-documented examples
that illustrate key concepts and theorems in the bimodal logic TM. These examples
are intended for:
- **Learning**: Understanding how to use ProofChecker effectively
- **Reference**: Showing idiomatic proof patterns
- **Demonstration**: Illustrating the power of the proof system

## Examples Categories

### Modal Logic Examples
- **ModalProofs.lean**: S5 modal logic theorems and proof patterns
  - Axiom K (modal distribution)
  - Axiom T (reflexivity)
  - Axiom 4 (transitivity)
  - Axiom B (symmetry)

### Temporal Logic Examples
- **TemporalProofs.lean**: Linear temporal logic theorems
  - Past and future operators
  - Temporal duality principles
  - Temporal axioms (TA, TL)

### Bimodal Examples
- **BimodalProofs.lean**: Combined modal-temporal reasoning
  - Perpetuity principles (P1-P6)
  - Modal-temporal interactions
  - Task semantics applications

### Temporal Structures Examples
- **TemporalStructures.lean**: Polymorphic temporal type examples
  - Integer time frames (discrete temporal logic)
  - Rational time frames (dense temporal reasoning)
  - Real time frames (continuous time modeling)
  - Demonstrates polymorphic `TaskFrame T` and `WorldHistory F`

## Usage

Import specific examples:
```lean
import Archive.ModalProofs
import Archive.TemporalProofs
import Archive.BimodalProofs
```

Or import the entire archive:
```lean
import Archive
```
-/

namespace Archive

def version : String := "0.1.0"

end Archive
