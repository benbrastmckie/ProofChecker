# File Structure Reorganization Research Report

## Metadata
- **Date**: 2025-12-02
- **Agent**: research-specialist
- **Topic**: File structure reorganization and naming consistency
- **Report Type**: Codebase analysis
- **Complexity**: 3

## Executive Summary

The ProofChecker project exhibits several structural inconsistencies between documentation and actual file organization. Key issues include: (1) "aggregator" files (e.g., `Syntax.lean`, `Semantics.lean`) in `ProofChecker/ProofChecker/` that re-export subdirectory modules, creating parallel structures that confuse the directory hierarchy; (2) missing DSL.lean and other files documented in README.md and CLAUDE.md but not present in codebase; (3) inconsistent directory naming where `docs/` uses lowercase while most project directories use PascalCase; (4) test files in `ProofCheckerTest/` following the same aggregator pattern as source files. These issues create navigation confusion and violate the principle of single source of truth for module organization.

## Findings

### Current State Analysis

#### 1. Aggregator Files in ProofChecker/ProofChecker/

**Location**: `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker/`

**Observed Pattern**: The main source directory contains both subdirectories AND top-level files with matching names:

```
ProofChecker/ProofChecker/
├── Syntax/                  # Subdirectory with actual implementations
│   ├── Formula.lean
│   └── Context.lean
├── Syntax.lean             # Aggregator file that imports from Syntax/
├── ProofSystem/            # Subdirectory
│   ├── Axioms.lean
│   └── Derivation.lean
├── ProofSystem.lean        # Aggregator file
├── Semantics/              # Subdirectory
│   ├── TaskFrame.lean
│   ├── WorldHistory.lean
│   ├── TaskModel.lean
│   ├── Truth.lean
│   └── Validity.lean
├── Semantics.lean          # Aggregator file
├── Metalogic/              # Subdirectory
│   ├── Soundness.lean
│   └── Completeness.lean
├── Metalogic.lean          # Aggregator file
├── Theorems/               # Subdirectory
│   └── Perpetuity.lean
├── Theorems.lean           # Aggregator file
├── Automation/             # Subdirectory
│   ├── Tactics.lean
│   └── ProofSearch.lean
└── Automation.lean         # Aggregator file
```

**Evidence from Syntax.lean** (lines 1-40):
```lean
import ProofChecker.Syntax.Formula
import ProofChecker.Syntax.Context

/-!
# Syntax Module

This module provides the syntax foundation for ProofChecker's bimodal logic TM.

## Exports

- `Formula`: Core formula type with 6 constructors
- `Context`: Type alias for `List Formula`
...
-/

namespace ProofChecker

-- Re-export Syntax namespace for convenient access
namespace Syntax
end Syntax

end ProofChecker
```

**Analysis**: These aggregator files serve as re-export points for their corresponding subdirectories. This is a valid LEAN 4 pattern for organizing module hierarchies, but creates the appearance of duplicate structure.

#### 2. Missing Files Documented But Not Present

**Documentation References**: Both README.md and CLAUDE.md reference files that don't exist:

**From README.md** (lines 183-185):
```
│   ├── Syntax/                 # Formula types, parsing, DSL
│   │   ├── Formula.lean        # Core formula inductive type
│   │   ├── Context.lean        # Proof context (premise lists)
│   │   └── DSL.lean            # Domain-specific syntax
```

**From CLAUDE.md** (lines 53-56):
```
│   ├── Syntax/                 # Formula types, parsing, DSL
│   │   ├── Formula.lean        # Core formula inductive type
│   │   ├── Context.lean        # Proof context (premise lists)
│   │   └── DSL.lean            # Domain-specific syntax
```

**From MODULE_ORGANIZATION.md** (lines 11-15):
```
│   ├── Syntax/                    # Formula types, parsing, DSL
│   │   ├── Formula.lean           # Core formula inductive type
│   │   ├── Context.lean           # Proof context (premise lists)
│   │   ├── Operators.lean         # Derived operators
│   │   └── DSL.lean               # Domain-specific syntax macros
```

**Actual State** (`ls ProofChecker/Syntax/`):
```
Context.lean
Formula.lean
```

**Missing Files**:
- `DSL.lean` - Domain-specific syntax macros
- `Operators.lean` - Derived operators (mentioned in MODULE_ORGANIZATION.md)

**Other Documentation Mismatches**:
- `ProofSystem/Rules.lean` - documented but not present (functionality merged into Derivation.lean)
- `Semantics/Canonical.lean` - documented in MODULE_ORGANIZATION.md but not present
- `Metalogic/Decidability.lean` - documented but empty/stub
- `Metalogic/Interpolation.lean` - documented in MODULE_ORGANIZATION.md but not present
- `Theorems/Basic.lean` - documented in MODULE_ORGANIZATION.md but not present
- `Automation/Templates.lean` - documented in MODULE_ORGANIZATION.md but not present

#### 3. Test Directory Parallel Structure

**Location**: `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofCheckerTest/`

**Observed Pattern**: Test directory mirrors the aggregator pattern:

```
ProofCheckerTest/
├── Syntax/                 # Test subdirectory
│   ├── FormulaTest.lean
│   └── ContextTest.lean
├── Syntax.lean            # Test aggregator
├── ProofSystem/           # Test subdirectory
│   ├── AxiomsTest.lean
│   └── DerivationTest.lean
├── ProofSystem.lean       # Test aggregator
├── Semantics/             # Test subdirectory
│   ├── TaskFrameTest.lean
│   └── TruthTest.lean
├── Semantics.lean         # Test aggregator
└── ...
```

**From ProofCheckerTest/Syntax.lean** (lines 1-12):
```lean
import ProofCheckerTest.Syntax.FormulaTest
import ProofCheckerTest.Syntax.ContextTest

/-!
# Syntax Test Module

Tests for the Syntax module (Formula and Context).
-/

namespace ProofCheckerTest.Syntax
end ProofCheckerTest.Syntax
```

**Analysis**: The test suite replicates the same aggregator pattern as the main source. This is consistent but adds to the confusion about which files are "real" implementations vs. organizational conveniences.

#### 4. Directory Naming Inconsistency

**Issue**: The `docs/` directory uses lowercase naming while most project directories use PascalCase or specific naming conventions.

**Current Directory Naming**:
- `ProofChecker/` - PascalCase (LEAN library convention)
- `ProofCheckerTest/` - PascalCase (LEAN library convention)
- `Archive/` - PascalCase (LEAN library convention)
- `Counterexamples/` - PascalCase (LEAN library convention)
- `docs/` - lowercase (common convention for documentation)
- `docs/development/` - lowercase subdirectory
- `docs/glossary/` - lowercase subdirectory

**User Concern**: Request to rename `docs/` to `Documentation/` for consistency.

**Standard Practice Analysis**:
- Most projects use lowercase `docs/` (GitHub recognizes it automatically)
- PascalCase for LEAN library directories is LEAN 4 convention
- Mixing conventions is common: code uses language conventions, docs use ecosystem conventions

#### 5. Documentation Files Living in Root of docs/

**Current Structure** (`ls docs/`):
```
ARCHITECTURE.md
CONTRIBUTING.md
EXAMPLES.md
IMPLEMENTATION_STATUS.md
INTEGRATION.md
KNOWN_LIMITATIONS.md
TUTORIAL.md
VERSIONING.md
development/
glossary/
```

**User Concern**: Files in `Documentation/` should live in a subdirectory.

**Analysis**: The current structure has documentation files at root level with only specialized content in subdirectories (`development/`, `glossary/`). This is standard practice (e.g., GitHub automatically displays README.md, docs/ is for additional docs).

**Potential Organization**:
```
Documentation/
├── User/               # or Guide/ or Guides/
│   ├── ARCHITECTURE.md
│   ├── TUTORIAL.md
│   ├── EXAMPLES.md
│   └── ...
├── Development/
│   ├── LEAN_STYLE_GUIDE.md
│   ├── MODULE_ORGANIZATION.md
│   └── ...
├── Reference/
│   └── glossary/
│       └── logical-operators.md
└── Contributing/
    ├── CONTRIBUTING.md
    └── VERSIONING.md
```

### Import System Analysis

**How LEAN 4 Handles Aggregator Files**:

From analyzing import statements in the codebase:

1. **Library Root** (`ProofChecker.lean` lines 1-7):
```lean
-- Re-export public API
import ProofChecker.Syntax
import ProofChecker.ProofSystem
import ProofChecker.Semantics
import ProofChecker.Metalogic
import ProofChecker.Theorems
import ProofChecker.Automation
```

The root file imports the aggregator files, which in turn import the subdirectory files.

2. **Aggregator Pattern** (`ProofChecker/Semantics.lean` lines 1-5):
```lean
import ProofChecker.Semantics.TaskFrame
import ProofChecker.Semantics.WorldHistory
import ProofChecker.Semantics.TaskModel
import ProofChecker.Semantics.Truth
import ProofChecker.Semantics.Validity
```

3. **Direct Imports in Implementation Files**:
Most implementation files import directly from subdirectories, bypassing aggregators:

- `ProofChecker/Semantics/Truth.lean` lines 1-3:
```lean
import ProofChecker.Semantics.TaskModel
import ProofChecker.Semantics.WorldHistory
import ProofChecker.Syntax.Formula
```

- `ProofChecker/Metalogic/Soundness.lean` lines 1-2:
```lean
import ProofChecker.ProofSystem.Derivation
import ProofChecker.Semantics.Validity
```

**Conclusion**: The aggregator files are organizational conveniences for the public API. Internal implementation files import directly from subdirectories. This is standard LEAN 4 practice.

### Lake Build Configuration

**From lakefile.toml** (lines 1-21):
```toml
name = "ProofChecker"
version = "0.1.0"
keywords = ["logic", "modal-logic", "temporal-logic", "proof-system", "lean4"]
license = "MIT"

[[lean_lib]]
name = "ProofChecker"

[[lean_lib]]
name = "ProofCheckerTest"

[[lean_lib]]
name = "Archive"

[[lean_lib]]
name = "Counterexamples"

[[lean_exe]]
name = "test"
root = "ProofCheckerTest.Main"
```

**Analysis**: Lake recognizes libraries by top-level directory names. The aggregator pattern is transparent to Lake - it only cares about the library name matching the directory.

## Recommendations

### 1. Clarify Aggregator File Purpose in Documentation

**Action**: Update README.md, CLAUDE.md, and MODULE_ORGANIZATION.md to explicitly explain the aggregator pattern.

**Rationale**: The current confusion stems from documentation showing directory structure without explaining that files like `Syntax.lean` and subdirectories like `Syntax/` serve different purposes (public API vs. implementation).

**Suggested Addition to Documentation**:
```markdown
### File Organization Pattern

ProofChecker uses LEAN 4's aggregator pattern for module organization:

- **Subdirectories** (e.g., `ProofChecker/Syntax/`) contain actual implementations
- **Aggregator files** (e.g., `ProofChecker/Syntax.lean`) re-export subdirectory modules for public API
- **Library root** (`ProofChecker.lean`) imports all aggregator files

Example:
- `ProofChecker/Syntax/Formula.lean` - Implementation of Formula type
- `ProofChecker/Syntax.lean` - Re-exports Formula and other Syntax modules
- `ProofChecker.lean` - Re-exports all top-level modules

Users can import either:
- `import ProofChecker` - Everything via aggregators (recommended for external use)
- `import ProofChecker.Syntax.Formula` - Specific module (for internal development)
```

### 2. Audit and Sync Documentation with Actual Files

**Action**: Remove references to non-existent files from all documentation or mark them as "Planned" with explanation.

**Files to Address**:
- `DSL.lean` - Either implement or remove from docs
- `Operators.lean` - Either implement or remove from docs
- `Rules.lean` - Update docs to reflect merger into Derivation.lean
- `Decidability.lean` - Mark as stub/planned in docs
- `Canonical.lean`, `Interpolation.lean`, `Basic.lean`, `Templates.lean` - Remove from MODULE_ORGANIZATION.md or mark as planned

**Recommended Approach**: Add a "Planned Files" section to documentation that lists future additions with justification.

### 3. Document Missing DSL Implementation

**Issue**: DSL.lean is prominently mentioned but doesn't exist. The Syntax module description claims to provide DSL functionality.

**Investigation Needed**:
- Is DSL functionality implemented elsewhere (e.g., in Formula.lean)?
- Should DSL.lean be created with macros/notation?
- Or should documentation be updated to remove DSL references?

**Evidence of DSL References**:
- README.md line 184: "└── DSL.lean            # Domain-specific syntax"
- CLAUDE.md line 55: "└── DSL.lean            # Domain-specific syntax"
- ProofChecker/Syntax.lean lines 10-13: Mentions "Derived operators" and "Helper functions"

### 4. Consider Documentation Directory Reorganization

**Option A: Keep Current Structure (Minimal Change)**
- Rename `docs/` to `Documentation/` for consistency
- Keep current flat structure with top-level documentation files
- Maintain existing `development/` and `glossary/` subdirectories

**Option B: Reorganize Into Subdirectories (More Structure)**
```
Documentation/
├── UserGuide/
│   ├── ARCHITECTURE.md
│   ├── TUTORIAL.md
│   ├── EXAMPLES.md
│   └── INTEGRATION.md
├── ProjectInfo/
│   ├── IMPLEMENTATION_STATUS.md
│   ├── KNOWN_LIMITATIONS.md
│   ├── CONTRIBUTING.md
│   └── VERSIONING.md
├── Development/
│   ├── LEAN_STYLE_GUIDE.md
│   ├── MODULE_ORGANIZATION.md
│   ├── TESTING_STANDARDS.md
│   ├── TACTIC_DEVELOPMENT.md
│   └── QUALITY_METRICS.md
└── Reference/
    └── Glossary/
        └── logical-operators.md
```

**Recommendation**: **Option A** for now. The current structure is functional and widely understood. Adding subdirectories would require updating many internal documentation links and provide marginal benefit. The rename to `Documentation/` addresses the naming consistency concern without disrupting navigation.

### 5. Add Aggregator Pattern to MODULE_ORGANIZATION.md

**Action**: Update `docs/development/MODULE_ORGANIZATION.md` to include section on aggregator files.

**Rationale**: This document is the authoritative source for understanding project structure. It should explicitly document the aggregator pattern to prevent future confusion.

**Suggested Section**:
```markdown
## Aggregator Files vs Implementation Files

ProofChecker uses two types of `.lean` files:

### Implementation Files (in subdirectories)
- Contain actual type definitions, functions, theorems
- Located in subdirectories: `ProofChecker/Syntax/`, `ProofChecker/Semantics/`, etc.
- Imported directly by other implementation files

### Aggregator Files (in parent directories)
- Re-export modules from subdirectories
- Located at: `ProofChecker/Syntax.lean`, `ProofChecker/Semantics.lean`, etc.
- Provide convenient single-import access to all submodules
- Used by library root and external consumers

### Example Structure
```
ProofChecker/
├── Syntax.lean           ← Aggregator: imports from Syntax/ subdirectory
├── Syntax/               ← Implementation directory
│   ├── Formula.lean      ← Implementation: defines Formula type
│   └── Context.lean      ← Implementation: defines Context type
```
```

### 6. Update README.md Project Structure Section

**Action**: Revise the project structure diagram in README.md to clarify aggregator vs implementation files.

**Current Issue** (README.md lines 176-238): The structure diagram lists both aggregator files and subdirectories but doesn't explain their relationship.

**Suggested Revision**: Add annotations or footnote explaining:
```markdown
## Project Structure

```
ProofChecker/
├── ProofChecker.lean           # Library root (re-exports all public modules)
├── ProofChecker/               # Main source directory
│   ├── Syntax.lean             # [1] Aggregator for Syntax modules
│   ├── Syntax/                 # Implementation directory
│   │   ├── Formula.lean        # Core formula inductive type
│   │   └── Context.lean        # Proof context (premise lists)
...
```

[1] **Aggregator Files**: Files like `Syntax.lean`, `Semantics.lean` re-export their subdirectory modules for convenient importing. See [Module Organization](docs/development/MODULE_ORGANIZATION.md#aggregator-files-vs-implementation-files) for details.
```

### 7. Consider Whether docs/ → Documentation/ Rename Is Worth It

**Pros of Renaming**:
- Consistent with PascalCase used in LEAN directories
- Matches user's preference for uniform styling
- Clear that it's a project directory, not external docs

**Cons of Renaming**:
- `docs/` is conventional and recognized by many tools (GitHub, documentation generators)
- Requires updating many internal links in CLAUDE.md, README.md, and all documentation files
- Mixed naming conventions (LEAN code = PascalCase, infrastructure = lowercase) is standard in polyglot projects
- Risk of broken links if not updated comprehensively

**Evidence of Link Volume**:
- CLAUDE.md has ~25 references to `docs/` paths
- README.md has ~15 references to `docs/` paths
- All files in `docs/development/` reference each other
- Total estimated: 60+ links to update

**Recommendation**: **Delay this change** unless there's a compelling technical reason. The naming inconsistency is cosmetic and follows common conventions. If proceeding, use automated link updates and thorough testing.

### 8. Archive or Complete Missing Files

**Immediate Action Required**:

For each documented-but-missing file, make a decision:

1. **DSL.lean**:
   - **If needed**: Create with notation/macro definitions for readable formula construction
   - **If not needed**: Remove all references from documentation
   - **Evidence**: README.md line 148 shows DSL usage: `example : ⊢ (□"p" → "p")`

2. **Operators.lean**:
   - Check if derived operators (`¬`, `∧`, `∨`, `◇`) are defined in Formula.lean
   - If yes: Remove Operators.lean references from MODULE_ORGANIZATION.md
   - If no: Consider creating for organizational clarity

3. **Rules.lean**:
   - Documentation shows Rules.lean but functionality is in Derivation.lean
   - **Action**: Update all docs to show `Derivation.lean` only, remove Rules.lean references

4. **Decidability.lean**:
   - File exists but is stub/planned
   - **Action**: Add "## Implementation Status" section to IMPLEMENTATION_STATUS.md showing file is planned

5. **Other missing files** (Canonical.lean, Interpolation.lean, Basic.lean, Templates.lean):
   - These appear in MODULE_ORGANIZATION.md as ideal future structure
   - **Action**: Create "Aspirational Structure" section in MODULE_ORGANIZATION.md distinguishing current vs. planned

## References

### Files Analyzed

**Documentation Files**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/README.md` (lines 1-291)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/CLAUDE.md` (lines 1-267)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/docs/development/MODULE_ORGANIZATION.md` (lines 1-422)

**Source Structure**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker/` (directory tree)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker/Syntax.lean` (lines 1-40)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker/Semantics.lean` (lines 1-40)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker/ProofSystem/Derivation.lean` (lines 1-50)

**Test Structure**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofCheckerTest/` (directory tree)
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofCheckerTest/Syntax.lean` (lines 1-12)

**Build Configuration**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/lakefile.toml` (lines 1-21)

**Import Analysis**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/ProofChecker.lean` (lines 1-58)
- Import statements across 20+ LEAN files in ProofChecker/ directory

### External References

**LEAN 4 Conventions**:
- LEAN 4 uses aggregator files for module organization
- Standard pattern: subdirectories contain implementations, parent files re-export
- Lake build system recognizes top-level library directories

**Documentation Conventions**:
- `docs/` directory is standard across GitHub projects
- Mixed casing (code conventions + infrastructure conventions) is normal in polyglot projects
- Flat documentation structure is common for projects with <20 doc files
