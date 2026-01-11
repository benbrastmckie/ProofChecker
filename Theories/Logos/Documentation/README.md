# Logos Documentation

Theory-specific documentation hub for the Logos second-order hyperintensional logic.

> **Note**: For project-wide documentation applicable to all theories, see
> [docs/](../../docs/README.md).

## About Logos Logic

Logos is a **planned second-order hyperintensional logic** that will extend beyond Bimodal.

| Aspect | Current State |
|--------|---------------|
| **Type** | Second-order hyperintensional logic (planned) |
| **Current status** | Re-exports Bimodal TM logic |
| **Semantic primitives** | States (more fine-grained than worlds) |
| **Logical level** | Second-order with first and second-order variables |

**Current Implementation**: Logos currently re-exports Bimodal's propositional intensional
logic. For working functionality, see [Bimodal/docs/](../../Bimodal/docs/).

For comparison with Bimodal propositional logic, see
[theory-comparison.md](../../docs/Research/theory-comparison.md).

## Documentation Organization

Documentation is organized into four categories:

### UserGuide/

User-facing documentation for working with Logos:

- [README.md](UserGuide/README.md) - Directory overview
- [QUICKSTART.md](UserGuide/QUICKSTART.md) - Getting started (redirects to Bimodal)
- [CURRENT_STATUS.md](UserGuide/CURRENT_STATUS.md) - Logos development status
- [METHODOLOGY.md](UserGuide/METHODOLOGY.md) - Logos layer architecture methodology

**Audience**: Users of the library, learners

### Reference/

Reference materials for Logos logic:

- [README.md](Reference/README.md) - Directory overview
- [AXIOM_REFERENCE.md](Reference/AXIOM_REFERENCE.md) - Axioms (redirects to Bimodal)
- [EXTENSION_STUBS.md](Reference/EXTENSION_STUBS.md) - Planned extension modules
- [GLOSSARY.md](Reference/GLOSSARY.md) - Logos terminology and operator definitions

**Audience**: All users

### Research/

Research and design documents for Logos:

- [README.md](Research/README.md) - Research overview
- [recursive-semantics.md](Research/recursive-semantics.md) - Full semantic specification
- [layer-extensions.md](Research/layer-extensions.md) - Extension architecture
- [conceptual-engineering.md](Research/conceptual-engineering.md) - Philosophical foundations

**Audience**: Researchers, contributors

### ProjectInfo/

Logos-specific project status:

- [README.md](ProjectInfo/README.md) - Directory overview
- [IMPLEMENTATION_STATUS.md](ProjectInfo/IMPLEMENTATION_STATUS.md) - Logos module status
- [KNOWN_LIMITATIONS.md](ProjectInfo/KNOWN_LIMITATIONS.md) - Current limitations
- [ROADMAP.md](ProjectInfo/ROADMAP.md) - Development roadmap

**Audience**: Contributors, maintainers

## Quick Links

Most-referenced documents:

- [Quick Start](UserGuide/QUICKSTART.md) - Get started (via Bimodal)
- [Current Status](UserGuide/CURRENT_STATUS.md) - Development status
- [Extension Stubs](Reference/EXTENSION_STUBS.md) - Planned extensions
- [Methodology](UserGuide/METHODOLOGY.md) - Layer architecture
- [Recursive Semantics](Research/recursive-semantics.md) - Full semantic specification
- [Roadmap](ProjectInfo/ROADMAP.md) - Future development

## Relationship to Project Documentation

**Logos-Specific** (unique to this theory):
- [CURRENT_STATUS](UserGuide/CURRENT_STATUS.md) - Logos development status
- [METHODOLOGY](UserGuide/METHODOLOGY.md) - Layer architecture methodology
- [EXTENSION_STUBS](Reference/EXTENSION_STUBS.md) - Planned extensions
- [GLOSSARY](Reference/GLOSSARY.md) - Terminology and operators
- [RECURSIVE_SEMANTICS](Research/recursive-semantics.md) - Semantic specification
- [LAYER_EXTENSIONS](Research/layer-extensions.md) - Extension architecture
- [CONCEPTUAL_ENGINEERING](Research/conceptual-engineering.md) - Philosophical foundations
- [ROADMAP](ProjectInfo/ROADMAP.md) - Development roadmap

**Redirects to Bimodal** (re-exported functionality):
- [QUICKSTART](UserGuide/QUICKSTART.md) → Bimodal/docs/UserGuide/QUICKSTART.md
- [AXIOM_REFERENCE](Reference/AXIOM_REFERENCE.md) → Bimodal axioms

**Project-Wide** (in [docs/](../../docs/)):
- [STYLE_GUIDE](../../docs/Development/LEAN_STYLE_GUIDE.md) - Coding style
- [TESTING](../../docs/Development/TESTING_STANDARDS.md) - Test standards

## Navigation

- **Up**: [Logos/](../)
- **Project Documentation**: [docs/](../../docs/)
- **Bimodal Documentation**: [Bimodal/docs/](../../Bimodal/docs/)
- **Theory Comparison**: [theory-comparison.md](../../docs/Research/theory-comparison.md)
