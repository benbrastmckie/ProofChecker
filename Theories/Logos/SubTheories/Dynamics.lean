import Logos.SubTheories.Dynamics.Frame
import Logos.SubTheories.Dynamics.Syntax
import Logos.SubTheories.Dynamics.Truth

/-!
# Logos Dynamics Foundation Layer

This module exports the Dynamics Foundation for Logos, providing
task-based intensional semantics with modal, temporal, and counterfactual operators.

## Overview

The Dynamics Foundation provides:
- Temporal structure (totally ordered abelian group)
- Task relation with mereological constraints
- State modality concepts (possible, compatible, maximal, world-state)
- World-history structures for temporal evaluation
- Modal, temporal, and counterfactual operators

## Submodules

- `Dynamics.Frame`: Frame with task relation and state modality
- `Dynamics.Syntax`: Formula type
- `Dynamics.Truth`: Truth evaluation

## Usage

```lean
import Logos.SubTheories.Dynamics

open Logos.SubTheories.Dynamics
```

## References

- Logos/docs/Research/recursive-semantics.md - Full specification
- Logos/docs/Research/layer-extensions.md - Extension architecture
-/
