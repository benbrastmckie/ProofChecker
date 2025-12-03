# ProofChecker: Formal Verification for Transparent AI Reasoning

ProofChecker provides syntactic verification for the Logos, a comprehensive framework for transparent AI reasoning in interpreted formal languages with an extensible range of operators for planning and evaluating actions in coordination with other agents. The system implements a four-layer logical framework: Layer 0 (Core TM) establishes the foundational bimodal logic combining tense and modality, currently under active development. Three planned extensions build progressively on this foundation: Layer 1 (Explanatory) adds counterfactual, causal, and constitutive operators; Layer 2 (Epistemic) introduces belief, probability, epistemic modals, and indicative conditionals; Layer 3 (Normative) provides deontic, preference, and normative explanatory operators.

Built on LEAN 4, the ProofChecker provides an RL signal for training AI systems to reason in the Logos with mathematical certainty, providing scalable oversight through computation rather than human annotation. The system implements a hyperintensional task semantics (possible worlds as functions from times to world-states) and complements semantic verification via the [Model-Checker](https://github.com/benbrastmckie/ModelChecker) to create comprehensive training signals.

For implementation details of the Model-Checker, see the [GitHub repository](https://github.com/benbrastmckie/ModelChecker) and [PyPI package](https://pypi.org/project/model-checker/). For a compressed overview of the TM logic subsystems, see the [LogicNotes](https://github.com/benbrastmckie/LogicNotes).

## Logos: Tense and Modal Reasoning

Layer 0 implements the foundational bimodal logic TM (Tense and Modality), combining S5 modal logic with linear temporal logic. This core layer establishes the semantic and syntactic infrastructure upon which explanatory, epistemic, and normative extensions will be built.

### Operators

- **Modal**: `□` (necessity), `◇` (possibility) - S5 modal logic
- **Temporal**: `Past` (universal past), `Future` (universal future), `past` (sometime past), `future` (sometime future), `always`/`△` (at all times), `sometimes`/`▽` (at a time)

### Axioms

- **S5 Modal**: MT (`□φ → φ`), M4 (`□φ → □□φ`), MB (`φ → □◇φ`)
- **Temporal**: T4 (`Future φ → Future Future φ`), TA (`φ → Future past φ`), TL (`△ φ → Future Past φ`)
- **Bimodal Interaction**: MF (`□φ → □Future φ`), TF (`□φ → Future □φ`)

### Perpetuity Principles (Key Theorems)

- **P1**: `□φ → △φ` (what is necessary is always the case)
- **P2**: `▽φ → ◇φ` (what is sometimes the case is possible)
- **P3**: `□φ → □△φ` (necessity of perpetuity)
- **P4**: `◇▽φ → ◇φ` (possibility of occurrence)
- **P5**: `◇▽φ → △◇φ` (persistent possibility)
- **P6**: `▽□φ → □△φ` (occurrent necessity is perpetual)

## Core Capabilities

### 1. Transparent Reasoning Infrastructure
- **Mathematical Certainty**: LEAN 4 proof receipts provide verifiable justifications
- **Auditable Inferences**: Every reasoning step can be independently checked
- **Explicit Semantics**: Task models make world states and temporal evolution explicit
- **Accountability**: Formal proofs enable trustworthy AI decision-making

### 2. Self-Supervised Training Data Generation
- **Unlimited Theorems**: Systematic derivation from TM axioms generates infinite training data
- **No Human Annotation**: Proof receipts serve as training signals directly
- **Positive Reinforcement**: Valid inferences rewarded with mathematical certainty
- **Systematic Pattern Mastery**: Enables learning logical reasoning systematically

### 3. Integrated Verification Architecture
- **Dual Checking**: Syntactic proofs (ProofChecker) + semantic validation (Model-Checker)
- **Rapid Prototyping**: Model-Checker tests theorems before proof attempts
- **Counterexample Learning**: Invalid reasoning generates corrective training signals
- **Scalable Oversight**: Verification scales with computation, not human effort

### 4. Progressive Extension Strategy
ProofChecker's layered architecture enables incremental extension from core TM logic to explanatory, epistemic, and normative reasoning. Each extension provides independent value while building toward comprehensive AI reasoning capabilities (see Architecture & Extensibility for roadmap).

### 5. Theoretical Innovation
- **Task Semantics**: Compositional account of possible worlds from [Possible Worlds paper](https://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf)
- **Perpetuity Principles**: Novel theorems connecting modal and temporal operators
- **Hyperintensional Foundation**: Supports explanatory reasoning extensions from [recent research](https://link.springer.com/article/10.1007/s10992-025-09793-8)
- **LEAN 4 Implementation**: First complete formalization of TM bimodal logic

## Implementation Status

**MVP Status**: Layer 0 (Core TM) MVP complete with partial metalogic implementation

### ✓ Completed Modules (4/8 - 50%)

- **Syntax**: Formula types, contexts (100% complete; DSL planned)
- **ProofSystem**: All 8 axioms and 7 inference rules defined (100% complete)
- **Semantics**: Task frames, models, truth evaluation, validity (100% complete)
- **Perpetuity**: P1-P3 proven (P1-P2 use propositional helpers with sorry)

### ⚠ Partial Modules (2/8 - 25%)

- **Metalogic/Soundness**: 5/8 axiom validity proofs (MT, M4, MB, T4, TA proven; TL, MF, TF incomplete)
- **Metalogic/Soundness**: 4/7 rule cases proven (axiom, assumption, modus_ponens, weakening; modal_k, temporal_k, temporal_duality incomplete)
- **Perpetuity**: P4-P6 use sorry (require complex modal-temporal reasoning)

### ⚠ Infrastructure Only (2/8 - 25%)

- **Metalogic/Completeness**: Type signatures defined, no proofs (uses `axiom` keyword)
- **Automation/Tactics**: Function declarations only, no implementations

### Planned

- **Decidability**: Not yet started (Metalogic/Decidability.lean)
- **DSL**: Domain-specific syntax for formulas (Syntax/DSL.lean)
- **Archive Examples**: ModalProofs.lean and TemporalProofs.lean (imports commented in Archive.lean)
- **Future Layers**: See Architecture & Extensibility for extension roadmap

**For detailed status**: See [IMPLEMENTATION_STATUS.md](Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md)
**For limitations and workarounds**: See [KNOWN_LIMITATIONS.md](Documentation/ProjectInfo/KNOWN_LIMITATIONS.md)

**Sorry Count**:

- Soundness: 15 placeholders (3 axioms incomplete, 3 rules incomplete)
- Perpetuity: 14 placeholders (propositional reasoning + complex modal-temporal)
- Tactics: 12 stubs (all tactics are declarations only)

**Estimated Completion Effort**: 155-215 hours for full Layer 0 completion

## Architecture & Extensibility

### Logos Ecosystem Integration

ProofChecker is the third package in the Logos architecture, providing **syntactic verification** complementing:

1. **Model-Builder** (Design Phase): Transforms natural language → formal semantic models
   - Extracts formal language fragments (FLF)
   - Constructs semantic model structures (SMS)
   - Generates salient inferences (SRI)

2. **Model-Checker** ([v1.2.12](https://github.com/benbrastmckie/ModelChecker)): Semantic verification via Z3
   - Implements hyperintensional semantics
   - Generates counterexamples for invalid inferences
   - Provides corrective RL training signals

3. **ProofChecker**: Syntactic verification via LEAN 4
   - Derives valid theorems from TM axioms
   - Provides proof receipts with mathematical certainty
   - Generates positive RL training signals

**Dual Verification Architecture**: ProofChecker's syntactic proofs and Model-Checker's semantic countermodels create comprehensive learning signals for AI training without human annotation. This enables scalable oversight through computation rather than labor.

**For complete TM logic specification**: See [ARCHITECTURE.md](Documentation/UserGuide/ARCHITECTURE.md)

### Theoretical Foundations

ProofChecker implements formal semantics developed in recent research:

**Task Semantics for Possible Worlds**:
- **Paper**: ["The Construction of Possible Worlds"](https://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf) (Brast-McKie, 2025)
  - Compositional semantics drawing on non-deterministic dynamical systems theories
  - Complete implementation in `Semantics/` package (TaskFrame, WorldHistory, TaskModel, Truth evaluation)

**Hyperintensional Semantics Foundation**:
- **Papers**: ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w) (2021), ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8) (2025)
  - State-based semantics enabling fine-grained distinctions for constitutive explanatory reasoning
  - Foundation for planned extensions (counterfactual, causal, constitutive operators)

### Layered Operator Strategy

ProofChecker implements a progressive four-layer architecture, each layer extending the logic with additional reasoning capabilities:

- **Layer 0 (Core TM - Current)**: Boolean, modal, and temporal operators - MVP Complete
- **Layer 1 (Explanatory - Planned)**: Counterfactual, causal, and constitutive operators
- **Layer 2 (Epistemic - Future)**: Belief, knowledge, and probability operators
- **Layer 3 (Normative - Future)**: Deontic, preference, and ought operators

Each layer builds on the previous while providing independent value. The current Layer 0 implementation establishes the syntactic and semantic foundation for all future extensions.

**For detailed roadmap**: See [IMPLEMENTATION_STATUS.md](Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md)

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

## Documentation

### Getting Started (New Users)

- [Tutorial](Documentation/UserGuide/TUTORIAL.md) - Getting started with ProofChecker
- [Examples](Documentation/UserGuide/EXAMPLES.md) - Modal, temporal, and bimodal examples
- [Logical Operators Glossary](Documentation/Reference/OPERATORS.md) - Formal symbols reference

### Architecture & Design

- [Architecture Guide](Documentation/UserGuide/ARCHITECTURE.md) - System design and TM logic specification
- [Integration Guide](Documentation/UserGuide/INTEGRATION.md) - Model-Checker integration

### Development (Contributing)

- [Contributing](Documentation/ProjectInfo/CONTRIBUTING.md) - How to contribute
- [LEAN Style Guide](Documentation/Development/LEAN_STYLE_GUIDE.md) - Coding conventions
- [Testing Standards](Documentation/Development/TESTING_STANDARDS.md) - Test requirements
- [Tactic Development](Documentation/Development/TACTIC_DEVELOPMENT.md) - Custom tactics

### Project Status

- [Implementation Status](Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md) - Module-by-module status tracking
- [Known Limitations](Documentation/ProjectInfo/KNOWN_LIMITATIONS.md) - Gaps, explanations, and workarounds
- [Versioning Policy](Documentation/ProjectInfo/VERSIONING.md) - Semantic versioning policy

### Advanced Topics

- [Metaprogramming Guide](Documentation/Development/METAPROGRAMMING_GUIDE.md) - LEAN 4 metaprogramming and tactic development
- [Quality Metrics](Documentation/Development/QUALITY_METRICS.md) - Quality targets and standards
- [Module Organization](Documentation/Development/MODULE_ORGANIZATION.md) - Project structure
- [Phased Implementation](Documentation/Development/PHASED_IMPLEMENTATION.md) - Wave-based implementation roadmap
- [Directory README Standard](Documentation/Development/DIRECTORY_README_STANDARD.md) - Directory-level documentation requirements
- [Documentation Quality Checklist](Documentation/Development/DOC_QUALITY_CHECKLIST.md) - Quality assurance checklist

### API Reference

- [Generated API Documentation](.lake/build/doc/) - Run `lake build :docs` to generate

## Project Structure

```
ProofChecker/
├── ProofChecker.lean           # Library root (re-exports all public modules)
├── ProofChecker/               # Main source directory (see ProofChecker/README.md)
│   ├── Syntax/                 # Formula types, parsing, DSL
│   │   ├── Formula.lean        # Core formula inductive type
│   │   └── Context.lean        # Proof context (premise lists)
│   ├── ProofSystem/            # Axioms and inference rules
│   │   ├── Axioms.lean         # TM axiom schemata
│   │   └── Derivation.lean     # Derivability relation and inference rules
│   ├── Semantics/              # Task frame semantics
│   │   ├── TaskFrame.lean      # Task frame structure
│   │   ├── WorldHistory.lean   # World history definition
│   │   ├── TaskModel.lean      # Model with valuation
│   │   ├── Truth.lean          # Truth evaluation
│   │   └── Validity.lean       # Validity and consequence
│   ├── Metalogic/              # Soundness and completeness
│   │   ├── Soundness.lean      # Soundness theorem
│   │   └── Completeness.lean   # Completeness theorem (canonical model)
│   ├── Theorems/               # Key theorems
│   │   └── Perpetuity.lean     # P1-P6 perpetuity principles
│   └── Automation/             # Proof automation
│       ├── Tactics.lean        # Custom tactics
│       └── ProofSearch.lean    # Automated proof search
├── ProofCheckerTest/           # Test suite (see ProofCheckerTest/README.md)
│   ├── ProofCheckerTest.lean   # Test library root
│   ├── Syntax/                 # Tests for formula construction
│   ├── ProofSystem/            # Tests for axioms and rules
│   ├── Semantics/              # Tests for semantics
│   ├── Integration/            # Cross-module tests
│   └── Metalogic/              # Soundness/completeness tests
├── Archive/                    # Pedagogical examples (see Archive/README.md)
│   ├── Archive.lean            # Archive library root
│   └── BimodalProofs.lean      # Combined modal-temporal examples
├── Documentation/              # User documentation (see Documentation/README.md)
│   ├── UserGuide/              # User-facing documentation
│   │   ├── ARCHITECTURE.md         # System design and TM logic specification
│   │   ├── TUTORIAL.md             # Getting started guide
│   │   ├── EXAMPLES.md             # Usage examples
│   │   └── INTEGRATION.md          # Model-Checker integration
│   ├── ProjectInfo/            # Project status and contribution info
│   │   ├── IMPLEMENTATION_STATUS.md  # Module-by-module status tracking
│   │   ├── KNOWN_LIMITATIONS.md      # Gaps, explanations, workarounds
│   │   ├── CONTRIBUTING.md           # Contribution guidelines
│   │   └── VERSIONING.md             # Semantic versioning policy
│   ├── Development/            # Developer standards
│   │   ├── DIRECTORY_README_STANDARD.md # Directory-level documentation requirements
│   │   ├── DOC_QUALITY_CHECKLIST.md     # Quality assurance checklist
│   │   ├── LEAN_STYLE_GUIDE.md          # Coding conventions
│   │   ├── METAPROGRAMMING_GUIDE.md     # LEAN 4 metaprogramming and tactics
│   │   ├── MODULE_ORGANIZATION.md       # Directory structure
│   │   ├── PHASED_IMPLEMENTATION.md     # Wave-based implementation roadmap
│   │   ├── QUALITY_METRICS.md           # Quality targets
│   │   ├── TACTIC_DEVELOPMENT.md        # Custom tactic patterns
│   │   └── TESTING_STANDARDS.md         # Test requirements
│   └── Reference/              # Reference materials
│       └── OPERATORS.md              # Formal symbols reference
├── lakefile.toml               # LEAN 4 build configuration
├── lean-toolchain              # LEAN version pinning
├── .gitignore                  # Git exclusions
└── .github/workflows/ci.yml    # CI/CD pipeline
```

## Related Projects

- **[Logos](https://github.com/benbrastmckie/Logos)** - Parent project for transparent AI reasoning with formal logic tools
- **[Model-Checker](https://github.com/benbrastmckie/ModelChecker)** - Z3-based semantic verification implementing hyperintensional semantics (v1.2.12)
- **Model-Builder** - Natural language to formal logic interface (design phase)
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

Contributions are welcome! Please read [CONTRIBUTING.md](Documentation/ProjectInfo/CONTRIBUTING.md) for guidelines.

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
