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

The semantics proceeds through increasingly expressive layers:

```
+--------------------------------------------------+
|            Constitutive Foundation               |
|          (hyperintensional base layer)           |
+------------------------+-------------------------+
                         | required
                         v
+--------------------------------------------------+
|             Explanatory Extension                |
|    (modal, temporal, counterfactual, causal)     |
+------------------------+-------------------------+
                         |
       +-----------------+-----------------+
       | optional        | optional        | optional
       v                 v                 v
+--------------+ +--------------+ +--------------+
|  Epistemic   | |  Normative   | |   Spatial    |
|  Extension   | |  Extension   | |  Extension   |
| (belief,     | | (obligation, | | (location,   |
|  knowledge,  | |  permission, | |  spatial     |
|  probability)| |  preference) | |  relations)  |
+------+-------+ +------+-------+ +------+-------+
       |                |                |
       +----------------+----------------+
                        | at least one required
                        v
+--------------------------------------------------+
|              Agential Extension                  |
|            (multi-agent reasoning)               |
+--------------------------------------------------+
```

The Constitutive Foundation and Explanatory Extension form the required base. Higher extensions are modular plugins.

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
| **Foundation** | Complete | ConstitutiveFrame, lattice operations, bilateral propositions |
| **Foundation/Semantics** | Complete | verifies/falsifies mutual recursion over formula structure |
| **Explanatory/Frame** | Complete | CoreFrame with task relation, state modality definitions |
| **Explanatory/WorldHistory** | Complete | Convex domains, task-respecting functions |
| **Explanatory/truthAt** | Complete | All operators except causal (stub) |
| **Causal operator** | Stub | Awaiting specification |
| **Epistemic** | Stub | Placeholder namespace |
| **Normative** | Stub | Placeholder namespace |
| **Spatial** | Stub | Placeholder namespace |

## Directory Structure

```
Logos/SubTheories/
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
    +-- Spatial.lean      # Location operators (placeholder)
```

## Operators Reference

### Modal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Necessity | box | "Necessarily A" - true at all world-histories |
| Possibility | diamond | "Possibly A" - true at some world-history |

### Temporal Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Always Past | H | "It has always been that A" |
| Always Future | G | "It will always be that A" |
| Some Past | P | "It was the case that A" |
| Some Future | F | "It will be the case that A" |
| Since | A triangleleft B | "A since B" - B was true, A ever since |
| Until | A triangleright B | "A until B" - A until B becomes true |

### Counterfactual Operators

| Operator | Symbol | Reading |
|----------|--------|---------|
| Would-counterfactual | box-arrow | "If A were the case, then B" |

### Store/Recall Operators

| Operator | Symbol | Effect |
|----------|--------|--------|
| Store | uparrow^i | Store current time in index i |
| Recall | downarrow^i | Evaluate at stored time i |

### Propositional Identity

| Operator | Symbol | Reading |
|----------|--------|---------|
| Identity | equiv | "A is the same proposition as B" |
| Essence | A sqsubseteq B | "A is essential to B" (defined: A and B equiv B) |
| Ground | A leq B | "A grounds B" (defined: A or B equiv B) |

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
