# ProofChecker

A LEAN 4 implementation of an axiomatic proof system for the bimodal logic **TM** (Tense and Modality) with task semantics.

## Features

- **Bimodal Logic TM**: Combines S5 modal logic with linear temporal logic
- **Task Semantics**: Possible worlds as functions from times to world states
- **Partial Metalogic**: Core soundness cases proven (5/8 axioms, 4/7 rules), completeness infrastructure defined
- **Perpetuity Principles**: P1-P3 proven, P4-P6 partial implementation
- **Layered Architecture**: Core TM (Layer 0) MVP complete with planned extensions for counterfactual, epistemic, and normative operators

## Logic TM

The logic TM is a bimodal system combining:

### Operators
- **Modal**: `□` (necessity), `◇` (possibility) - S5 modal logic
- **Temporal**: `Past` (universal past), `Future` (universal future), `past` (sometime past), `future` (sometime future)
- **Combined**: `always`/`△` (henceforth), `sometimes`/`▽` (eventually)

### Axioms
- **S5 Modal**: MT (`□φ → φ`), M4 (`□φ → □□φ`), MB (`φ → □◇φ`)
- **Temporal**: T4 (`Future φ → Future Future φ`), TA (`φ → Future past φ`), TL (`always φ → Future Past φ`)
- **Bimodal Interaction**: MF (`□φ → □Future φ`), TF (`□φ → Future □φ`)

### Perpetuity Principles (Key Theorems)
- **P1**: `□φ → △φ` (what is necessary is always the case)
- **P2**: `▽φ → ◇φ` (what is sometimes the case is possible)
- **P3**: `□φ → □△φ` (necessity of perpetuity)
- **P4**: `◇▽φ → ◇φ` (possibility of occurrence)
- **P5**: `◇▽φ → △◇φ` (persistent possibility)
- **P6**: `▽□φ → □△φ` (occurrent necessity is perpetual)

## Implementation Status

**MVP Status**: Layer 0 (Core TM) MVP complete with partial metalogic implementation

### Completed Modules ✓
- **Syntax**: Formula types, contexts, DSL (100% complete)
- **ProofSystem**: All 8 axioms and 7 inference rules defined (100% complete)
- **Semantics**: Task frames, models, truth evaluation, validity (100% complete)
- **Perpetuity**: P1-P3 proven (P1-P2 use propositional helpers with sorry)

### Partial Modules ⚠️
- **Metalogic/Soundness**: 5/8 axiom validity proofs (MT, M4, MB, T4, TA proven; TL, MF, TF incomplete)
- **Metalogic/Soundness**: 4/7 rule cases proven (axiom, assumption, modus_ponens, weakening; modal_k, temporal_k, temporal_duality incomplete)
- **Perpetuity**: P4-P6 use sorry (require complex modal-temporal reasoning)

### Infrastructure Only 🏗️
- **Metalogic/Completeness**: Type signatures defined, no proofs (uses `axiom` keyword)
- **Automation/Tactics**: Function declarations only, no implementations

### Planned 📋
- **Decidability**: Not yet started
- **Layer 1/2/3**: Counterfactual, epistemic, normative operators

**For detailed status**: See [IMPLEMENTATION_STATUS.md](docs/IMPLEMENTATION_STATUS.md)
**For limitations and workarounds**: See [KNOWN_LIMITATIONS.md](docs/KNOWN_LIMITATIONS.md)

**Sorry Count**:
- Soundness: 15 placeholders (3 axioms incomplete, 3 rules incomplete)
- Perpetuity: 14 placeholders (propositional reasoning + complex modal-temporal)
- Tactics: 12 stubs (all tactics are declarations only)

**Estimated Completion Effort**: 155-215 hours for full Layer 0 completion

## Installation

### Requirements
- LEAN 4 v4.14.0 or later
- Lake (included with LEAN 4)
- VS Code with lean4 extension (recommended)

### Setup

```bash
# Clone the repository
git clone https://github.com/yourusername/ProofChecker.git
cd ProofChecker

# Build the project
lake build

# Run tests
lake test
```

## Quick Start

```lean
import ProofChecker

-- Define a formula: `□p → p` (axiom MT)
def mt_instance : Formula := Formula.box (Formula.atom "p") |>.imp (Formula.atom "p")

-- Prove the formula using axiom MT
example : ⊢ mt_instance := by
  apply Derivable.axiom
  apply Axiom.modal_t

-- Use DSL syntax for readable formulas
example : ⊢ (□"p" → "p") := by
  apply Derivable.axiom
  apply Axiom.modal_t

-- Prove perpetuity principle P1
example (φ : Formula) : ⊢ (φ.box.imp (always φ)) := perpetuity_1 φ
```

## Documentation

### User Documentation
- [Architecture Guide](docs/ARCHITECTURE.md) - System design and TM logic specification
- [Implementation Status](docs/IMPLEMENTATION_STATUS.md) - Module-by-module status tracking
- [Known Limitations](docs/KNOWN_LIMITATIONS.md) - Gaps, explanations, and workarounds
- [Logical Operators Glossary](docs/glossary/logical-operators.md) - Formal symbols reference
- [Tutorial](docs/TUTORIAL.md) - Getting started with ProofChecker
- [Examples](docs/EXAMPLES.md) - Modal, temporal, and bimodal examples
- [Contributing](docs/CONTRIBUTING.md) - How to contribute
- [API Reference](.lake/build/doc/) - Generated API documentation (run `lake build :docs` to generate)

### Developer Standards
- [LEAN Style Guide](docs/development/LEAN_STYLE_GUIDE.md) - Coding conventions
- [Module Organization](docs/development/MODULE_ORGANIZATION.md) - Project structure
- [Testing Standards](docs/development/TESTING_STANDARDS.md) - Test requirements
- [Tactic Development](docs/development/TACTIC_DEVELOPMENT.md) - Custom tactics

## Project Structure

```
ProofChecker/
├── ProofChecker.lean           # Library root (re-exports all public modules)
├── ProofChecker/               # Main source directory
│   ├── Syntax/                 # Formula types, parsing, DSL
│   │   ├── Formula.lean        # Core formula inductive type
│   │   ├── Context.lean        # Proof context (premise lists)
│   │   └── DSL.lean            # Domain-specific syntax
│   ├── ProofSystem/            # Axioms and inference rules
│   │   ├── Axioms.lean         # TM axiom schemata
│   │   ├── Rules.lean          # Inference rules (MP, MK, TK, TD)
│   │   └── Derivation.lean     # Derivability relation
│   ├── Semantics/              # Task frame semantics
│   │   ├── TaskFrame.lean      # Task frame structure
│   │   ├── WorldHistory.lean   # World history definition
│   │   ├── TaskModel.lean      # Model with valuation
│   │   ├── Truth.lean          # Truth evaluation
│   │   └── Validity.lean       # Validity and consequence
│   ├── Metalogic/              # Soundness and completeness
│   │   ├── Soundness.lean      # Soundness theorem
│   │   ├── Completeness.lean   # Completeness theorem
│   │   └── Decidability.lean   # Decision procedures
│   ├── Theorems/               # Key theorems
│   │   └── Perpetuity.lean     # P1-P6 perpetuity principles
│   └── Automation/             # Proof automation
│       ├── Tactics.lean        # Custom tactics
│       └── ProofSearch.lean    # Automated proof search
├── ProofCheckerTest/           # Test suite
│   ├── ProofCheckerTest.lean   # Test library root
│   ├── Syntax/                 # Tests for formula construction
│   ├── ProofSystem/            # Tests for axioms and rules
│   ├── Semantics/              # Tests for semantics
│   ├── Integration/            # Cross-module tests
│   └── Metalogic/              # Soundness/completeness tests
├── Archive/                    # Pedagogical examples
│   ├── Archive.lean            # Archive library root
│   ├── ModalProofs.lean        # S5 modal logic examples
│   ├── TemporalProofs.lean     # Temporal reasoning examples
│   └── BimodalProofs.lean      # Combined examples
├── Counterexamples/            # Invalidity demonstrations
│   └── Counterexamples.lean    # Counterexamples library root
├── docs/                       # User documentation
│   ├── ARCHITECTURE.md         # System design and TM spec
│   ├── TUTORIAL.md             # Getting started guide
│   ├── EXAMPLES.md             # Usage examples
│   ├── CONTRIBUTING.md         # Contribution guidelines
│   ├── INTEGRATION.md          # Model-Checker integration
│   ├── VERSIONING.md           # Semantic versioning policy
│   ├── glossary/               # Formal symbols glossary
│   │   └── logical-operators.md # Modal, temporal, meta-logical symbols
│   └── development/            # Developer standards
│       ├── LEAN_STYLE_GUIDE.md     # Coding conventions
│       ├── MODULE_ORGANIZATION.md  # Directory structure
│       ├── TESTING_STANDARDS.md    # Test requirements
│       ├── TACTIC_DEVELOPMENT.md   # Custom tactic patterns
│       └── QUALITY_METRICS.md      # Quality targets
├── lakefile.toml               # LEAN 4 build configuration
├── lean-toolchain              # LEAN version pinning
├── .gitignore                  # Git exclusions
└── .github/workflows/ci.yml    # CI/CD pipeline
```

## Related Projects

- **Logos** - Parent project for formal logic tools
- **FormalizedFormalLogic/Foundation** - LEAN 4 modal logic library (patterns adopted)
- **Mathlib4** - LEAN 4 mathematics library (style conventions followed)

## License

MIT License - see [LICENSE](LICENSE) for details.

## Citation

If you use ProofChecker in your research, please cite:

```bibtex
@software{proofchecker2025,
  title = {ProofChecker: LEAN 4 Proof System for Bimodal Logic TM},
  author = {Your Name},
  year = {2025},
  url = {https://github.com/yourusername/ProofChecker}
}
```

## Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](docs/CONTRIBUTING.md) for guidelines.

### Development Setup

```bash
# Install LEAN 4 (elan recommended)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Clone and build
git clone https://github.com/yourusername/ProofChecker.git
cd ProofChecker
lake build

# Run tests before submitting PR
lake test
lake lint
```

## Status

- **Layer 0 (Core TM)**: MVP Complete (partial soundness/completeness, see [IMPLEMENTATION_STATUS.md](docs/IMPLEMENTATION_STATUS.md))
- **Layer 1 (Explanatory)**: Planned
- **Layer 2 (Epistemic)**: Planned
- **Layer 3 (Normative)**: Planned

**Note**: ProofChecker MVP is functional for core TM reasoning despite partial metalogic implementation. See [KNOWN_LIMITATIONS.md](docs/KNOWN_LIMITATIONS.md) for workarounds and [IMPLEMENTATION_STATUS.md](docs/IMPLEMENTATION_STATUS.md) for detailed module status.
