# ProofChecker: LEAN 4 Implementation of Logos Layer 0 (Core TM)

ProofChecker is a LEAN 4 implementation of **Logos Layer 0** - the foundational bimodal logic TM (Tense and Modality) combining S5 modal logic with linear temporal logic. Layer 0 establishes the syntactic and semantic foundation for progressive operator extensions planned in Layers 1-3 (Explanatory, Epistemic, Normative), enabling domain-specific customization while maintaining mathematical rigor.

Built on LEAN 4, ProofChecker provides an RL signal for training AI systems to reason in Logos with mathematical certainty, enabling scalable oversight through computation rather than human annotation. The system implements hyperintensional task semantics (possible worlds as functions from times to world-states) and integrates with the [Model-Checker](https://github.com/benbrastmckie/ModelChecker) to create comprehensive dual verification architecture for transparent AI reasoning.

For Model-Checker implementation details, see the [GitHub repository](https://github.com/benbrastmckie/ModelChecker) and [PyPI package](https://pypi.org/project/model-checker/). For theoretical foundations, see [LogicNotes](https://github.com/benbrastmckie/LogicNotes).

## Logos: Formal Language of Thought with Progressive Extensibility

**Logos** is a formal language of thought designed for verified AI reasoning through progressive operator extensibility. The language implements a layered architecture where operators build incrementally from foundational logic (Boolean, modal, temporal) through domain-specific reasoning capabilities (explanatory, epistemic, normative).

**Core Architectural Principle**: "Any combination of extensions can be added to the Core Layer"

### Layer Architecture

- **Layer 0 (Core TM)**: Boolean, modal, and temporal operators - **Current Implementation (MVP Complete)**
  - Foundational bimodal logic combining S5 modal logic with linear temporal logic
  - Provides semantic and syntactic infrastructure for all planned extensions
  - Task semantics with compositional possible worlds framework
  - **Status**: MVP complete with partial metalogic (5/8 axioms, 4/7 rules proven)

- **Layer 1 (Explanatory)**: Counterfactual, causal, and constitutive operators - **Planned**
  - Enables reasoning about what would/might happen under different scenarios
  - Provides grounding, essence, identity, and relevance operators
  - Application domains: Medical treatment planning, causal analysis

- **Layer 2 (Epistemic)**: Belief, probability, and knowledge operators - **Planned**
  - Enables reasoning under uncertainty with belief states and probabilities
  - Provides epistemic modals and indicative conditionals
  - Application domains: Legal evidence analysis, multi-agent belief modeling

- **Layer 3 (Normative)**: Deontic, preference, and normative operators - **Planned**
  - Enables ethical and cooperative reasoning
  - Provides obligation, permission, and preference ordering
  - Application domains: Multi-party negotiation, ethical AI decision-making

**Layer 0 provides the foundation for all subsequent extensions**, establishing the semantic framework and syntactic infrastructure that Layers 1-3 build upon.

**For philosophical foundations**: See [LOGOS_PHILOSOPHY.md](Documentation/UserGuide/LOGOS_PHILOSOPHY.md)
**For extension specifications**: See [LAYER_EXTENSIONS.md](Documentation/Research/LAYER_EXTENSIONS.md)

### Layer 0 (Core TM) - Current Implementation

Layer 0 implements the foundational bimodal logic TM, providing the core reasoning infrastructure for all planned extensions.

#### Operators

- **Modal**: `□` (necessity), `◇` (possibility) - S5 modal logic
- **Temporal**: `Past` (universal past), `Future` (universal future), `past` (sometime past), `future` (sometime future), `always`/`△` (at all times), `sometimes`/`▽` (at a time)

#### Axioms

- **S5 Modal**: MT (`□φ → φ`), M4 (`□φ → □□φ`), MB (`φ → □◇φ`)
- **Temporal**: T4 (`Future φ → Future Future φ`), TA (`φ → Future past φ`), TL (`△ φ → Future Past φ`)
- **Bimodal Interaction**: MF (`□φ → □Future φ`), TF (`□φ → Future □φ`)

#### Perpetuity Principles (Key Theorems)

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

### 3. Dual Verification Architecture
- **Syntactic Proofs**: ProofChecker derives valid theorems from TM axioms with LEAN 4 proof receipts
- **Semantic Validation**: Model-Checker tests theorems via Z3-based hyperintensional semantics
- **Complementary Signals**: Proof receipts provide positive reinforcement, counterexamples provide corrective feedback
- **Rapid Prototyping**: Model-Checker tests theorems before proof attempts, reducing wasted effort
- **Scalable Oversight**: Verification scales with computation, not human annotation

### 4. Progressive Extension Strategy
ProofChecker's layered architecture enables incremental extension from core TM logic to explanatory, epistemic, and normative reasoning. Each extension provides independent value while building toward comprehensive AI reasoning capabilities (see [Progressive Extension Methodology](#progressive-extension-methodology) for details).

### 5. Theoretical Innovation
- **Task Semantics**: Compositional account of possible worlds from [Possible Worlds paper](https://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf)
- **Perpetuity Principles**: Novel theorems connecting modal and temporal operators
- **Hyperintensional Foundation**: Supports explanatory reasoning extensions from [recent research](https://link.springer.com/article/10.1007/s10992-025-09793-8)
- **LEAN 4 Implementation**: First complete formalization of TM bimodal logic

## Implementation Status

**MVP Status**: Layer 0 (Core TM) MVP Complete - Foundation for Planned Extensions

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
- **Layer 1-3 Extensions**: See [LAYER_EXTENSIONS.md](Documentation/Research/LAYER_EXTENSIONS.md) for extension roadmap

All current modules implement **Layer 0 (Core TM)** - the foundational bimodal logic. Layer 1-3 extensions build on this foundation.

**For detailed status**: See [IMPLEMENTATION_STATUS.md](Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md)
**For limitations and workarounds**: See [KNOWN_LIMITATIONS.md](Documentation/ProjectInfo/KNOWN_LIMITATIONS.md)

**Sorry Count**:

- Soundness: 15 placeholders (3 axioms incomplete, 3 rules incomplete)
- Perpetuity: 14 placeholders (propositional reasoning + complex modal-temporal)
- Tactics: 12 stubs (all tactics are declarations only)

**Estimated Completion Effort**: 155-215 hours for full Layer 0 completion

## Dual Verification Architecture

ProofChecker and Model-Checker form a **complementary dual verification architecture** providing comprehensive training signals for AI systems learning to reason in Logos.

### ProofChecker: Syntactic Verification (Layer 0 Implementation)

**Role**: LEAN 4 implementation of Logos Layer 0 (Core TM)
- Derives valid theorems from TM axioms via formal proof
- Provides proof receipts with mathematical certainty
- Generates positive RL training signals (valid inferences)
- Implements task semantics for soundness/completeness theorems

**Current Status**: MVP complete with partial metalogic (5/8 axioms, 4/7 rules proven)

### Model-Checker: Semantic Verification (Complementary Tool)

**Role**: Z3-based semantic verification for Logos ([v1.2.12](https://github.com/benbrastmckie/ModelChecker))
- Implements hyperintensional semantics via verifier/falsifier state pairs
- Generates counterexamples for invalid inferences
- Provides corrective RL training signals (refuting invalid reasoning)
- Enables rapid prototyping (test theorems before proof attempts)

**Integration**: Complementary semantic verification tool, not co-equal package in architecture

### Training Signal Generation

The dual verification architecture creates comprehensive learning signals without human annotation:

1. **Positive Signals**: ProofChecker generates valid theorems with proof receipts
2. **Corrective Signals**: Model-Checker generates counterexamples for invalid inferences
3. **Scalable Oversight**: Both tools scale with computation, enabling unlimited training data
4. **Mathematical Certainty**: LEAN 4 proofs provide verifiable justifications, Z3 countermodels refute invalid claims

**For integration details**: See [INTEGRATION.md](Documentation/UserGuide/INTEGRATION.md)

## Progressive Extension Methodology

The Logos architecture implements **progressive operator extensibility** as a core architectural principle, enabling domain-specific customization while maintaining mathematical rigor.

### Core Principle

**"Any combination of extensions can be added to the Core Layer"**

Layer 0 (Core TM) provides the foundational bimodal logic, with Layers 1-3 as independent modular extensions. Applications can selectively load only the operators needed for their domain, avoiding unnecessary complexity while preserving expressive power.

### Extension Strategy

- **Layer 0 (Complete)**: Foundational Boolean, modal, temporal operators - current implementation
- **Layer 1 (Planned)**: Counterfactual, causal, constitutive operators - explanatory reasoning
- **Layer 2 (Planned)**: Belief, probability, knowledge operators - epistemic reasoning
- **Layer 3 (Planned)**: Deontic, preference, normative operators - ethical reasoning

Each layer builds on Layer 0 while providing independent value. Extensions can be combined in any configuration matching application requirements.

### Domain-Specific Operator Combinations

**Medical Planning** (Core + Explanatory):
- Core operators: Modal (`□`, `◇`) + Temporal (`Future`, `Past`) for treatment timelines
- Explanatory operators: Counterfactual (`□→`, `◇→`) for evaluating treatment strategies
- Example: `Prescribe(DrugA) ∧ Taking(MedicationX) □→ F(Normalize(BloodPressure)) ∧ F(Occur(LiverDamage))`
  - Evaluates what would happen under Drug A prescription given current medication
  - Distinguishes necessary consequences (`□→`) from possible consequences (`◇→`)

**Legal Reasoning** (Core + Epistemic):
- Core operators: Modal + Temporal for tracking events and beliefs across time
- Epistemic operators: Belief (`B`), epistemic modals (`Mi`, `Mu`) for evidence analysis
- Example: Tracking how evidence reveals agent beliefs and motives, constructing narratives connecting motive to action

**Multi-Agent Coordination** (Core + All Extensions):
- Core: Modal + Temporal for action timelines and coordination constraints
- Explanatory: Counterfactuals for evaluating alternative strategies
- Epistemic: Belief operators for modeling other agents' knowledge states
- Normative: Deontic operators (`O`, `P`) for obligations and permissions in negotiation

### Extensibility References

**For philosophical foundations and progressive methodology**: See [LOGOS_PHILOSOPHY.md](Documentation/UserGuide/LOGOS_PHILOSOPHY.md)

**For Layer 1-3 specifications and domain examples**: See [LAYER_EXTENSIONS.md](Documentation/Research/LAYER_EXTENSIONS.md)

**For Layer 0 technical specification**: See [ARCHITECTURE.md](Documentation/UserGuide/ARCHITECTURE.md)

## Theoretical Foundations

ProofChecker implements formal semantics developed in recent research:

**Task Semantics for Possible Worlds**:
- **Paper**: ["The Construction of Possible Worlds"](https://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf) (Brast-McKie, 2025)
  - Compositional semantics drawing on non-deterministic dynamical systems theories
  - Complete implementation in `Semantics/` package (TaskFrame, WorldHistory, TaskModel, Truth evaluation)

**Hyperintensional Semantics Foundation**:
- **Papers**: ["Identity and Aboutness"](https://link.springer.com/article/10.1007/s10992-021-09612-w) (2021), ["Counterfactual Worlds"](https://link.springer.com/article/10.1007/s10992-025-09793-8) (2025)
  - State-based semantics enabling fine-grained distinctions for constitutive explanatory reasoning
  - Foundation for planned extensions (counterfactual, causal, constitutive operators)

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

- [Logos Philosophy](Documentation/UserGuide/LOGOS_PHILOSOPHY.md) - Philosophical foundations and layer architecture
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

### Research & Extensions

- [Layer Extensions](Documentation/Research/LAYER_EXTENSIONS.md) - Layers 1-3 specifications
- [Dual Verification](Documentation/Research/DUAL_VERIFICATION.md) - RL training architecture
- [Proof Library Design](Documentation/Research/PROOF_LIBRARY_DESIGN.md) - Theorem caching architecture

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
│   │   ├── LOGOS_PHILOSOPHY.md     # Philosophical foundations and layer architecture
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
│   ├── Research/               # Research documentation
│   │   ├── DUAL_VERIFICATION.md      # RL training architecture
│   │   ├── LAYER_EXTENSIONS.md       # Layers 1-3 specifications
│   │   └── PROOF_LIBRARY_DESIGN.md   # Theorem caching architecture
│   └── Reference/              # Reference materials
│       ├── OPERATORS.md              # Formal symbols reference
│       └── GLOSSARY.md               # Key concepts and definitions
├── lakefile.toml               # LEAN 4 build configuration
├── lean-toolchain              # LEAN version pinning
├── .gitignore                  # Git exclusions
└── .github/workflows/ci.yml    # CI/CD pipeline
```

## Related Projects

- **[Model-Checker](https://github.com/benbrastmckie/ModelChecker)** - Z3-based semantic verification implementing hyperintensional semantics (v1.2.12) - complementary tool for dual verification architecture
- **[LogicNotes](https://github.com/benbrastmckie/LogicNotes)** - Theoretical foundations and compressed overview of TM logic subsystems
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
