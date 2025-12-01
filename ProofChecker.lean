/-!
# ProofChecker Library Root

This is the main entry point for the ProofChecker library, which implements
an axiomatic proof system for the bimodal logic TM (Tense and Modality) with
task semantics.

## Overview

ProofChecker provides:
- **Bimodal Logic TM**: Combining S5 modal logic (metaphysical necessity/possibility)
  with linear temporal logic (past/future operators)
- **Task Semantics**: Possible worlds as functions from times to world states
  constrained by task relations
- **Layered Architecture**: Layer 0 (Core TM) with planned extensions
- **Complete Metalogic**: Soundness and completeness proofs
- **Perpetuity Principles**: P1-P6 derived theorems

## Module Structure

The library is organized into the following submodules:

- `ProofChecker.Syntax`: Formula types, parsing, DSL
- `ProofChecker.ProofSystem`: Axioms and inference rules
- `ProofChecker.Semantics`: Task frame semantics
- `ProofChecker.Metalogic`: Soundness and completeness proofs
- `ProofChecker.Theorems`: Key theorems (perpetuity principles, etc.)
- `ProofChecker.Automation`: Proof automation tactics

## Usage

Import the entire library:
```lean
import ProofChecker
```

Or import specific modules:
```lean
import ProofChecker.Syntax.Formula
import ProofChecker.ProofSystem.Axioms
```
-/

-- Re-export public API when modules are implemented
-- import ProofChecker.Syntax
-- import ProofChecker.ProofSystem
-- import ProofChecker.Semantics
-- import ProofChecker.Metalogic
-- import ProofChecker.Theorems
-- import ProofChecker.Automation

namespace ProofChecker

-- Version information
def version : String := "0.1.0"

end ProofChecker
