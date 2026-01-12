# Logos

A hyperintensional logic for truthmaker semantics, implementing exact verification and falsification conditions over a mereological state space with bilateral propositions.

## About Logos

Logos is a **hyperintensional logic system** that goes beyond standard intensional (possible-worlds) semantics. Where intensional logics identify necessarily equivalent propositions, Logos distinguishes them by their exact verification and falsification conditions. This enables formal reasoning about:

- **Truthmaker semantics**: What makes a proposition true or false
- **Constitutive relations**: Essence and grounding between propositions
- **Bilateral propositions**: Verifier/falsifier pairs rather than truth-value assignments

Logos is developed in parallel across two implementations:
- **Proof-checker** (this repository): Lean 4 formal verification of logical axioms and inference rules
- **Model-checker**: [ModelChecker](https://github.com/benbrastmckie/ModelChecker) - Z3-based semantic verification for countermodel search

## Philosophy

### Why Hyperintensionality?

Standard modal logic treats propositions as sets of possible worlds. This identifies all necessarily true propositions (they're all true at every world) and all necessarily false ones. But intuitively:

- "2 + 2 = 4" and "Every bachelor is unmarried" are distinct truths
- Mathematical necessities differ from logical necessities
- Fine-grained propositional content matters for explanation

Logos addresses this by using **states** (sub-world-sized entities) as semantic primitives. A bilateral proposition is an ordered pair of verifier and falsifier sets, capturing what would make it exactly true vs exactly false.

### Extension Architecture

Logos follows a layered semantic architecture:

```
┌──────────────────────────────────────────────────┐
│            Constitutive Foundation               │
│          (hyperintensional base layer)           │
└────────────────────────┬─────────────────────────┘
                         │ required
                         ▼
┌──────────────────────────────────────────────────┐
│             Explanatory Extension                │
│    (modal, temporal, counterfactual, causal)     │
└────────────────────────┬─────────────────────────┘
                         │
       ┌─────────────────┼─────────────────┐
       │ optional        │ optional        │ optional
       ▼                 ▼                 ▼
┌──────────────┐ ┌──────────────┐ ┌──────────────┐
│  Epistemic   │ │  Normative   │ │   Spatial    │
│  Extension   │ │  Extension   │ │  Extension   │
│ (belief,     │ │ (obligation, │ │ (location,   │
│  knowledge,  │ │  permission, │ │  spatial     │
│  probability)│ │  preference) │ │  relations)  │
└──────┬───────┘ └──────┬───────┘ └──────┬───────┘
       │                │                │
       └────────────────┼────────────────┘
                        │ at least one required
                        ▼
┌──────────────────────────────────────────────────┐
│              Agential Extension                  │
│            (multi-agent reasoning)               │
└────────────────────────┬─────────────────────────┘
                         │ inherits from Epistemic
                         ▼
┌──────────────────────────────────────────────────┐
│             Reflection Extension                 │
│    (metacognition, self-modeling, I operator)    │
└──────────────────────────────────────────────────┘
```

1. **Constitutive Foundation** (required) - Hyperintensional semantics with bilateral propositions over mereological state spaces
2. **Explanatory Extension** (required) - Adds temporal structure and task relation for modal, temporal, and counterfactual reasoning
3. **Middle Extensions** (optional) - Epistemic, Normative, and Spatial modules that can be combined
4. **Agential Extension** - Multi-agent reasoning (requires at least one middle extension)
5. **Reflection Extension** - Metacognition and self-modeling (inherits from Epistemic)

See [recursive-semantics.md](docs/research/recursive-semantics.md) for the full dependency diagram and formal semantic specifications.

## Core Concepts

### Bilateral Propositions

A *bilateral proposition* is an ordered pair (V, F) where:
- V = set of verifier states (what makes it true)
- F = set of falsifier states (what makes it false)

Both sets must be closed under fusion (mereological sum). Propositions are **exclusive** (no state both verifies and falsifies) and **exhaustive** (every possible state is compatible with some verifier or falsifier).

### State Space

The semantic foundation is a **constitutive frame** (S, sqsubseteq) where:
- S is a nonempty set of states
- sqsubseteq is a parthood relation making (S, sqsubseteq) a complete lattice

This provides:
- **Null state**: Bottom element (empty fusion)
- **Full state**: Top element (fusion of all states)
- **Fusion**: Least upper bound operation

### Task Relation

The Explanatory Extension adds a **task relation** s =>_d t constraining how states can evolve:
- "There is a task from state s to state t with duration d"
- Enables defining possibility, compatibility, and world-states
- Satisfies compositionality, parthood, and containment constraints

### World-Histories

A *world-history* is a function tau : X -> W assigning world-states to times where:
- X is a convex subset of the temporal order
- tau respects the task relation: tau(x) =>_{y-x} tau(y) for x <= y

World-histories provide the intensional evaluation contexts for modal and temporal operators.

## Implementation Status

| Component | Status | Description |
|-----------|--------|-------------|
| **Foundation** | Complete | ConstitutiveFrame, lattice operations, bilateral propositions, Semantics (verifies/falsifies) |
| **Explanatory/Frame** | Complete | CoreFrame with task relation, state modality definitions |
| **Explanatory/WorldHistory** | Complete | Convex domains, task-respecting functions |
| **Explanatory/Truth** | Complete | All operators except causal (stub) |
| **Causal operator** | Stub | Awaiting specification |
| **Epistemic** | Stub | Placeholder namespace |
| **Normative** | Stub | Placeholder namespace |
| **Spatial** | Stub | Placeholder namespace |
| **Reflection** | Stub | Placeholder namespace |

*Note: Parallel implementation in [ModelChecker](https://github.com/benbrastmckie/ModelChecker) covers Constitutive Foundation and Explanatory Extension.*

## Directory Structure

```
SubTheories/
+-- Foundation/           # Constitutive Foundation layer
|   +-- Frame.lean        # ConstitutiveFrame: complete lattice state space
|   +-- Syntax.lean       # ConstitutiveFormula: atoms, predicates, connectives, identity
|   +-- Semantics.lean    # verifies/falsifies mutual recursion
|   +-- Proposition.lean  # BilateralProp type
|   +-- Interpretation.lean # Interpretation function I
|   +-- Basic.lean        # Common definitions
|
+-- Explanatory/          # Explanatory Extension layer
|   +-- Frame.lean        # CoreFrame: task relation, state modality
|   +-- Syntax.lean       # Formula type with modal/temporal operators
|   +-- Truth.lean        # truthAt evaluation with world-histories
|
+-- Epistemic/            # Epistemic Extension (stub)
|   +-- Epistemic.lean    # Belief, knowledge operators (placeholder)
|
+-- Normative/            # Normative Extension (stub)
|   +-- Normative.lean    # Deontic operators (placeholder)
|
+-- Spatial/              # Spatial Extension (stub)
|   +-- Spatial.lean      # Location operators (placeholder)
|
+-- Reflection/           # Reflection Extension (stub)
    +-- Reflection.lean   # Metacognition, I operator (placeholder)
```

## Operators Reference

*This section provides a quick reference for commonly-used operators. See [recursive-semantics.md](docs/research/recursive-semantics.md) for complete formal definitions and truth conditions.*

### Modal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Necessity | `□A` or `Box A` | "Necessarily A" - true at all world-histories |
| Possibility | `◇A` or `Dia A` | "Possibly A" - true at some world-history |

### Temporal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Always Past | `H A` | "It has always been that A" |
| Always Future | `G A` | "It will always be that A" |
| Some Past | `P A` | "It was the case that A" |
| Some Future | `F A` | "It will be the case that A" |
| Since | `A S B` | "A since B" - B was true, A ever since |
| Until | `A U B` | "A until B" - A until B becomes true |

### Counterfactual Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Would-counterfactual | `A □→ B` | "If A were the case, then B" |

### Store/Recall Operators

| Operator | Symbol | Effect |
|----------|--------|--------|
| Store | `↑ⁱ` | Store current time in index i |
| Recall | `↓ⁱ` | Evaluate at stored time i |

### Propositional Identity

| Operator | Symbol | Reading |
|----------|--------|---------|
| Identity | `A ≡ B` | "A is the same proposition as B" |
| Essence | `A ⊑ B` | "A is essential to B" (defined: A ∧ B ≡ B) |
| Ground | `A ≤ B` | "A grounds B" (defined: A ∨ B ≡ B) |

### Derived Temporal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Always | `Alw A` | "At all times A" - H A ∧ A ∧ G A |
| Sometimes | `Som A` | "At some time A" - P A ∨ A ∨ F A |

### Quantifiers and Predicates

| Operator | Symbol | Reading |
|----------|--------|---------|
| Universal | `∀y.A` | "For all states y, A holds" |
| Actuality | `Act(t)` | "t is part of the current world-state" |

### Causal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Causation | `A ⦿→ B` | "A causes B" (stub - awaiting specification) |

## Building and Testing

```bash
# Build entire Logos module
lake build Logos

# Build entire project
lake build

# Type-check specific SubTheories file
lake env lean Theories/Logos/SubTheories/Foundation/Frame.lean
lake env lean Theories/Logos/SubTheories/Explanatory/Truth.lean

# Interactive mode
lake env lean --run
```

## Related Documentation

### Specification

- **[recursive-semantics.md](docs/research/recursive-semantics.md)** - Complete semantic specification with formal definitions, truth clauses, and axiom schemata
- **[layer-extensions.md](docs/research/layer-extensions.md)** - Extension architecture overview with application examples

### Theory Documentation

- [docs/](docs/README.md) - Logos-specific documentation hub
- [docs/reference/GLOSSARY.md](docs/reference/GLOSSARY.md) - Term definitions
- [docs/user-guide/METHODOLOGY.md](docs/user-guide/METHODOLOGY.md) - Philosophical methodology

### Academic Sources

- Fine, K. (2017). "Truthmaker Semantics" - Foundation for hyperintensional propositions
- Brast-McKie, B. "Possible Worlds" (JPL) - Task semantics, bimodal logic
- Brast-McKie, B. "Counterfactual Worlds" (JPL) - Counterfactual conditional semantics

### Related Projects

- **[ModelChecker](https://github.com/benbrastmckie/ModelChecker)** - Python/Z3 implementation for semantic verification and countermodel search

## Navigation

- **Project Root**: [../../](../..)
- **Theory Docs**: [docs/](docs/)
- **Tests**: [LogosTest/](../LogosTest/)
