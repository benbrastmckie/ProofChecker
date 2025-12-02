/-!
# Syntax Module

This module provides the syntax foundation for ProofChecker's bimodal logic TM.

## Exports

- `Formula`: Core formula type with 6 constructors
- `Context`: Type alias for `List Formula`
- Derived operators: negation, conjunction, disjunction, modal diamond, temporal operators
- Helper functions: complexity measure, temporal duality

## Usage

```lean
import ProofChecker.Syntax

open ProofChecker.Syntax

-- Create formulas
def p := Formula.atom "p"
def q := Formula.atom "q"
def modal_t := p.box.imp p

-- Use contexts
def assumptions : Context := [p, q]
```
-/

import ProofChecker.Syntax.Formula
import ProofChecker.Syntax.Context

namespace ProofChecker

-- Re-export Syntax namespace for convenient access
namespace Syntax
end Syntax

end ProofChecker
