# Lake Lint Integration Specification (Revised)

**Status:** Planning  
**Created:** 2025-12-15  
**Revised:** 2025-12-15 (post-research)  
**Priority:** High  
**Estimated Effort:** 6-8 hours

## Executive Summary

This specification defines the integration of Lake's native `lake lint` command with the Logos project's comprehensive opencode validation framework. Based on research into LEAN 4.14.0, Lake 5.0.0, and Mathlib v4.14.0 linting infrastructure, this plan implements a **hybrid linting approach** combining:

1. **Syntax linters** (run during compilation via `set_option`)
2. **Environment linters** (run post-build via custom executable)
3. **Text-based linters** (run on source files via custom script)

**Critical Discovery**: Lake's `lintDriver` configuration requires **lakefile.lean** (NOT lakefile.toml). The first phase converts the existing lakefile.toml to lakefile.lean to enable native linting support.

## Research Summary

### Key Findings

1. **Lake has native `lake lint` command** (Lake 5.0.0+)
   - Configured via `lintDriver` option in **lakefile.lean**
   - Uses `@[lint_driver]` attribute on executables
   - Runs configured driver with optional arguments

2. **Two Distinct Linting Systems**:
   - **Syntax Linters**: Run during compilation (enabled via `set_option`)
   - **Environment Linters**: Run post-build (via `@[env_linter]` attribute)

3. **Mathlib Uses Custom Infrastructure**:
   - `lake exe lint-style`: Text-based linting (27 linters)
   - `lake exe runLinter`: Environment linting (8+ linters)
   - Does NOT use `lake lint` (predates Lake's native command)

4. **Linter Configuration**:
   - Syntax linters: `set_option linter.name true` or linter sets
   - Environment linters: `@[env_linter]` attribute
   - Suppression: `@[nolint]`, `nolints.json`, or `set_option`

**Research Document**: `.claude/research/lean4-linting-research.md` (1,023 lines)

## Current State Analysis

### Existing Infrastructure

**Lake Configuration:**
- `lakefile.toml` exists with basic package definitions
- **CRITICAL**: lakefile.toml does NOT support `lintDriver` configuration
- Must convert to `lakefile.lean` to enable `lake lint`
- CI/CD runs `lake lint` with `continue-on-error: true` (will fail until configured)

**Opencode Validation Framework:**
- Comprehensive `validate-all-standards.sh` orchestrator with 17 validators
- ERROR-level validators (blocking): library-sourcing, error-suppression, etc.
- WARNING-level validators (informational): readme-structure, link-validity, etc.
- Sophisticated error logging and state management

**LEAN 4 Standards:**
- Strict style guide requiring zero lint warnings
- 100-character line limit, 2-space indentation
- Comprehensive documentation requirements
- Test-driven development (TDD) enforcement

**Existing LEAN 4 Tooling:**
- 6 LEAN 4 specific agents (lean-coordinator, lean-implementer, etc.)
- 4 LEAN 4 commands (/lean-build, /lean-implement, /lean-plan, /lean-update)
- `.opencode/agent/subagents/implementer/lean-linter.md` (static rule-based)

### Current Gaps

1. **Lakefile Format**: Using lakefile.toml (no linting support)
2. **Lake Lint Driver**: No configuration for Lake's native `lake lint`
3. **Linter Sets**: No project-specific linter set defined
4. **Environment Linters**: No post-build environment linting
5. **CI/CD Integration**: Lint failures don't block (continue-on-error)
6. **Opencode Integration**: Lake lint not integrated with validation framework

## Proposed Integration Design

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                      lakefile.lean                              │
│  - Package configuration                                        │
│  - Linter set definition (linter.logosStandardSet)             │
│  - Syntax linter enablement (via leanOptions)                  │
│  - Lint driver registration (@[lint_driver])                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│              lake lint (Lake's native command)                  │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│           Custom Lint Driver (scripts/LintAll.lean)             │
│  1. Run environment linters (lake exe runLinter)                │
│  2. Run text-based linters (lake exe lint-style)                │
│  3. Aggregate results and exit with appropriate code            │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│         Opencode Integration Bridge (check-lean-linting.sh)    │
│  - Wraps `lake lint` execution                                  │
│  - Parses output and creates opencode state                     │
│  - Integrates with error logging                                │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│              validate-all-standards.sh                          │
│  - Runs check-lean-linting.sh as ERROR-level validator         │
│  - Blocks commits on lint failures                              │
└─────────────────────────────────────────────────────────────────┘
```

### Core Components

1. **lakefile.lean** (converted from lakefile.toml)
   - Defines `linter.logosStandardSet` with project-specific linters
   - Enables syntax linters via `leanOptions` with `weak.` prefix
   - Registers custom lint driver via `@[lint_driver]` attribute

2. **Custom Lint Driver** (`scripts/LintAll.lean`)
   - Orchestrates environment linters (via Batteries infrastructure)
   - Orchestrates text-based linters (custom implementation)
   - Aggregates results and provides unified exit code

3. **Environment Linters** (`Logos/Lint/EnvLinters.lean`)
   - Custom environment linters using `@[env_linter]` attribute
   - TM-specific checks (modal operator usage, proof structure, etc.)
   - Integrated with Batteries linting infrastructure

4. **Text-Based Linters** (`scripts/LintStyle.lean`)
   - Source file linting (whitespace, line length, etc.)
   - Follows Mathlib's `lint-style` pattern
   - Supports `--fix` for auto-correction

5. **Opencode Integration Bridge** (`.claude/scripts/lint/check-lean-linting.sh`)
   - Wraps `lake lint` execution
   - Parses output and creates opencode-compatible state
   - Integrates with error logging framework

## Implementation Phases

### Phase 1: Lakefile Conversion (2 hours)

#### 1.1 Convert lakefile.toml to lakefile.lean

**Current lakefile.toml**:
```toml
name = "Logos"
version = "0.1.0"
keywords = ["logic", "modal-logic", "temporal-logic", "proof-system", "lean4"]
license = "MIT"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.14.0"

[[lean_lib]]
name = "Logos"

[[lean_lib]]
name = "LogosTest"

[[lean_lib]]
name = "Archive"

[[lean_exe]]
name = "test"
root = "LogosTest.Main"
```

**New lakefile.lean**:
```lean
import Lake
open Lake DSL

package Logos where
  version := "0.1.0"
  keywords := #["logic", "modal-logic", "temporal-logic", "proof-system", "lean4"]
  license := "MIT"
  lintDriver := "lintAll"  -- Configure lint driver

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

-- Define Logos standard linter set
register_linter_set linter.logosStandardSet :=
  linter.unusedVariables
  linter.missingDocs
  linter.style.longLine
  linter.deprecatedCoercions
  linter.suspiciousUnexpanderPatterns

-- Logos library with linters enabled
@[default_target]
lean_lib Logos where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Enable Logos linter set (weak prefix for build-time)
    ⟨`weak.linter.logosStandardSet, true⟩,
    -- Configure specific linters
    ⟨`weak.linter.style.longLine.maxColumn, 100⟩,
    ⟨`weak.linter.missingDocs.checkPrivate, false⟩
  ]

lean_lib LogosTest

lean_lib Archive

lean_exe test where
  root := `LogosTest.Main

-- Custom lint driver executable
@[lint_driver]
lean_exe lintAll where
  srcDir := "scripts"
  root := `LintAll
  supportInterpreter := true
```

**Migration Steps**:
1. Backup lakefile.toml to `.backups/lakefile.toml.backup`
2. Create lakefile.lean with equivalent configuration
3. Test build: `lake build`
4. Verify lint driver: `lake check-lint`
5. Delete lakefile.toml after successful migration

#### 1.2 Define Logos Linter Set

**Rationale**: Project-specific linter set for consistent enforcement

**Linters to include**:
- `linter.unusedVariables`: Catch unused variables
- `linter.missingDocs`: Enforce documentation requirements
- `linter.style.longLine`: Enforce 100-char limit
- `linter.deprecatedCoercions`: Catch deprecated patterns
- `linter.suspiciousUnexpanderPatterns`: Catch syntax issues

**Configuration**:
```lean
register_linter_set linter.logosStandardSet :=
  linter.unusedVariables
  linter.missingDocs
  linter.style.longLine
  linter.deprecatedCoercions
  linter.suspiciousUnexpanderPatterns
```

### Phase 2: Custom Lint Driver (2 hours)

#### 2.1 Create Lint Driver Executable

**File**: `scripts/LintAll.lean`

```lean
import Lean
import Batteries.Tactic.Lint
import Logos.Lint.EnvLinters

open Lean System IO

/-- Main lint driver that orchestrates all linting phases -/
def main (args : List String) : IO UInt32 := do
  let mut exitCode : UInt32 := 0
  
  -- Parse arguments
  let verbose := args.contains "--verbose"
  let fix := args.contains "--fix"
  let modules := args.filter (fun arg => !arg.startsWith "--")
  
  -- Phase 1: Environment linters (post-build)
  if verbose then
    IO.println "Running environment linters..."
  
  let envExitCode ← runEnvLinters modules verbose
  if envExitCode ≠ 0 then
    exitCode := 1
  
  -- Phase 2: Text-based linters (source files)
  if verbose then
    IO.println "Running text-based linters..."
  
  let textExitCode ← runTextLinters modules fix verbose
  if textExitCode ≠ 0 then
    exitCode := 1
  
  -- Summary
  if exitCode = 0 then
    IO.println "✓ All linters passed"
  else
    IO.eprintln "✗ Linting failed - see errors above"
  
  return exitCode

/-- Run environment linters on compiled modules -/
def runEnvLinters (modules : List String) (verbose : Bool) : IO UInt32 := do
  -- Use Batteries linting infrastructure
  -- This would invoke the environment linters defined in Logos/Lint/EnvLinters.lean
  -- For now, return success (implement in Phase 3)
  return 0

/-- Run text-based linters on source files -/
def runTextLinters (modules : List String) (fix : Bool) (verbose : Bool) : IO UInt32 := do
  -- Invoke text-based linting script
  -- This would check whitespace, line length, etc.
  -- For now, return success (implement in Phase 3)
  return 0
```

#### 2.2 Register Lint Driver

Already done in lakefile.lean:
```lean
@[lint_driver]
lean_exe lintAll where
  srcDir := "scripts"
  root := `LintAll
  supportInterpreter := true
```

#### 2.3 Test Lint Driver

```bash
# Verify lint driver is configured
lake check-lint

# Run linting
lake lint

# Run with verbose output
lake lint -- --verbose

# Run on specific module
lake lint -- Logos.Core.Syntax
```

### Phase 3: Environment Linters (1.5 hours)

#### 3.1 Create Environment Linter Infrastructure

**File**: `Logos/Lint/EnvLinters.lean`

```lean
import Batteries.Tactic.Lint
import Lean

open Lean Meta Batteries.Tactic.Lint

/-- Check that all public theorems have documentation -/
@[env_linter]
def docBlameTheorems : Linter where
  noErrorsFound := "All public theorems documented."
  errorsFound := "MISSING THEOREM DOCUMENTATION:"
  test declName := do
    let info ← getConstInfo declName
    -- Check if theorem and public
    if info.isTheorem && !declName.isInternal then
      -- Check for docstring
      if (← findDocString? (← getEnv) declName).isNone then
        return some m!"Missing docstring for theorem {declName}"
    return none

/-- Check TM-specific naming conventions -/
@[env_linter]
def tmNamingConventions : Linter where
  noErrorsFound := "All declarations follow TM naming conventions."
  errorsFound := "NAMING CONVENTION VIOLATIONS:"
  test declName := do
    let name := declName.toString
    -- Check for modal operator naming
    if name.contains "box" && !name.contains "modal" then
      return some m!"Modal operator {declName} should include 'modal' in name"
    -- Check for temporal operator naming
    if (name.contains "past" || name.contains "future") && !name.contains "temporal" then
      return some m!"Temporal operator {declName} should include 'temporal' in name"
    return none

/-- Check proof structure (no sorry in non-test files) -/
@[env_linter disabled]  -- Disabled by default, enable for strict mode
def noSorryInProofs : Linter where
  noErrorsFound := "No sorry placeholders found."
  errorsFound := "SORRY PLACEHOLDERS FOUND:"
  test declName := do
    let info ← getConstInfo declName
    -- Check if definition contains sorry
    -- (This is a simplified check - full implementation would inspect proof term)
    if info.isTheorem then
      -- Check proof term for sorry
      -- Implementation would use Meta.ppExpr and search for "sorry"
      return none  -- Placeholder
    return none
```

#### 3.2 Integrate with Lint Driver

Update `scripts/LintAll.lean`:

```lean
def runEnvLinters (modules : List String) (verbose : Bool) : IO UInt32 := do
  -- Build command to run environment linters
  let mut cmd := "lake"
  let mut args := #["exe", "runEnvLinters"]
  
  if verbose then
    args := args.push "--verbose"
  
  for module in modules do
    args := args.push module
  
  -- Execute
  let output ← IO.Process.output {
    cmd := cmd
    args := args
  }
  
  if output.exitCode ≠ 0 then
    IO.eprintln output.stderr
  
  return output.exitCode.toUInt32
```

#### 3.3 Create Environment Linter Executable

**File**: `scripts/RunEnvLinters.lean`

```lean
import Batteries.Tactic.Lint.Frontend
import Logos.Lint.EnvLinters

open Lean Batteries.Tactic.Lint

def main (args : List String) : IO UInt32 := do
  -- Use Batteries linting frontend
  -- This handles linter discovery, execution, and reporting
  let modules := args.filter (fun arg => !arg.startsWith "--")
  let verbose := args.contains "--verbose"
  
  -- Run linters (Batteries provides the infrastructure)
  -- Implementation would use Batteries.Tactic.Lint.Frontend.lintModules
  
  IO.println "Environment linting complete"
  return 0
```

Register in lakefile.lean:
```lean
lean_exe runEnvLinters where
  srcDir := "scripts"
  root := `RunEnvLinters
```

### Phase 4: Text-Based Linters (1 hour)

#### 4.1 Create Text-Based Linter Script

**File**: `scripts/LintStyle.lean`

```lean
import Lean
import Std.Data.String

open Lean System IO

/-- Text-based linter for source file style -/
structure StyleLinter where
  name : String
  check : String → Array (Nat × String)  -- Line number × error message
  fix : String → String := id

/-- Check for trailing whitespace -/
def trailingWhitespaceLinter : StyleLinter where
  name := "trailingWhitespace"
  check := fun content =>
    let lines := content.splitOn "\n"
    lines.toArray.mapIdx fun idx line =>
      if line.endsWith " " || line.endsWith "\t" then
        #[(idx.val + 1, "Trailing whitespace")]
      else
        #[]
    |>.flatten
  fix := fun content =>
    let lines := content.splitOn "\n"
    String.intercalate "\n" (lines.map (·.trimRight))

/-- Check for line length violations -/
def longLineLinter (maxLength : Nat := 100) : StyleLinter where
  name := "longLine"
  check := fun content =>
    let lines := content.splitOn "\n"
    lines.toArray.mapIdx fun idx line =>
      if line.length > maxLength then
        #[(idx.val + 1, s!"Line exceeds {maxLength} characters ({line.length})")]
      else
        #[]
    |>.flatten

/-- All text-based linters -/
def allStyleLinters : Array StyleLinter := #[
  trailingWhitespaceLinter,
  longLineLinter 100
]

/-- Main entry point for text-based linting -/
def main (args : List String) : IO UInt32 := do
  let fix := args.contains "--fix"
  let verbose := args.contains "--verbose"
  let files := args.filter (fun arg => !arg.startsWith "--" && arg.endsWith ".lean")
  
  let mut totalErrors := 0
  
  for file in files do
    if verbose then
      IO.println s!"Checking {file}..."
    
    let content ← IO.FS.readFile file
    let mut fileErrors := 0
    let mut fixedContent := content
    
    for linter in allStyleLinters do
      let errors := linter.check content
      fileErrors := fileErrors + errors.size
      
      if errors.size > 0 then
        IO.println s!"{file}: {linter.name} ({errors.size} issues)"
        for (line, msg) in errors do
          IO.println s!"  Line {line}: {msg}"
      
      if fix then
        fixedContent := linter.fix fixedContent
    
    if fix && fileErrors > 0 then
      IO.FS.writeFile file fixedContent
      IO.println s!"Fixed {fileErrors} issues in {file}"
    
    totalErrors := totalErrors + fileErrors
  
  if totalErrors > 0 then
    IO.eprintln s!"Found {totalErrors} style issues"
    return 1
  else
    IO.println "✓ All style checks passed"
    return 0
```

Register in lakefile.lean:
```lean
lean_exe lintStyle where
  srcDir := "scripts"
  root := `LintStyle
```

#### 4.2 Integrate with Lint Driver

Update `scripts/LintAll.lean`:

```lean
def runTextLinters (modules : List String) (fix : Bool) (verbose : Bool) : IO UInt32 := do
  -- Find all .lean files in specified modules
  let mut files : Array String := #[]
  
  if modules.isEmpty then
    -- Lint all Logos files
    files := ← findLeanFiles "Logos"
  else
    for module in modules do
      files := files ++ (← findLeanFiles module)
  
  -- Build command
  let mut args := #["exe", "lintStyle"]
  if fix then args := args.push "--fix"
  if verbose then args := args.push "--verbose"
  args := args ++ files
  
  -- Execute
  let output ← IO.Process.output {
    cmd := "lake"
    args := args
  }
  
  if output.exitCode ≠ 0 then
    IO.eprintln output.stderr
  
  return output.exitCode.toUInt32

/-- Find all .lean files in a directory -/
def findLeanFiles (dir : String) : IO (Array String) := do
  -- Implementation would recursively find .lean files
  -- Placeholder for now
  return #[]
```

### Phase 5: Opencode Integration (1.5 hours)

#### 5.1 Create Opencode Validator

**File**: `.claude/scripts/lint/check-lean-linting.sh`

```bash
#!/usr/bin/env bash
# check-lean-linting.sh - Opencode validator for LEAN 4 linting
# Version: 2.0.0 (revised post-research)

set -eo pipefail

# Detect project directory
if command -v git &>/dev/null && git rev-parse --git-dir >/dev/null 2>&1; then
  PROJECT_DIR="$(git rev-parse --show-toplevel)"
else
  current_dir="$(pwd)"
  while [ "$current_dir" != "/" ]; do
    if [ -d "$current_dir/.claude" ]; then
      PROJECT_DIR="$current_dir"
      break
    fi
    current_dir="$(dirname "$current_dir")"
  done
fi

if [ -z "${PROJECT_DIR:-}" ] || [ ! -d "$PROJECT_DIR/.claude" ]; then
  echo "ERROR: Cannot find project directory with .claude/" >&2
  exit 2
fi

# Configuration
LINT_OUTPUT_DIR="$PROJECT_DIR/.lake"
LINT_STATE_FILE="$PROJECT_DIR/.claude/tmp/lean-lint-state.json"

# Create output directory
mkdir -p "$LINT_OUTPUT_DIR" "$PROJECT_DIR/.claude/tmp"

# Verify lint driver is configured
echo "Verifying lint driver configuration..."
if ! lake check-lint >/dev/null 2>&1; then
  echo "ERROR: No lint driver configured" >&2
  echo "  Run: lake check-lint for details" >&2
  exit 2
fi

# Run lake lint
echo "Running LEAN 4 linting (lake lint)..."

LINT_EXIT_CODE=0
LINT_OUTPUT_FILE="$LINT_OUTPUT_DIR/lint-output.txt"

lake lint "$@" 2>&1 | tee "$LINT_OUTPUT_FILE" || LINT_EXIT_CODE=$?

# Parse results
ERROR_COUNT=0
WARNING_COUNT=0

if [ -f "$LINT_OUTPUT_FILE" ]; then
  # Count errors and warnings from output
  ERROR_COUNT=$(grep -c "^error:" "$LINT_OUTPUT_FILE" 2>/dev/null || echo "0")
  WARNING_COUNT=$(grep -c "^warning:" "$LINT_OUTPUT_FILE" 2>/dev/null || echo "0")
fi

# Create state file for opencode integration
cat > "$LINT_STATE_FILE" <<EOF
{
  "validator": "lean-linting",
  "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "exit_code": $LINT_EXIT_CODE,
  "errors": $ERROR_COUNT,
  "warnings": $WARNING_COUNT,
  "lint_output": "$LINT_OUTPUT_FILE",
  "lake_version": "$(lake --version 2>/dev/null || echo 'unknown')",
  "lean_version": "$(lean --version 2>/dev/null | head -1 || echo 'unknown')"
}
EOF

# Report results
if [ $LINT_EXIT_CODE -ne 0 ]; then
  echo ""
  echo "✗ LEAN 4 linting failed"
  echo "  Errors: $ERROR_COUNT"
  echo "  Warnings: $WARNING_COUNT"
  echo ""
  echo "Recent output:"
  tail -30 "$LINT_OUTPUT_FILE"
  echo ""
  echo "Full output: $LINT_OUTPUT_FILE"
  exit 1
else
  echo ""
  echo "✓ LEAN 4 linting passed"
  exit 0
fi
```

Make executable:
```bash
chmod +x .claude/scripts/lint/check-lean-linting.sh
```

#### 5.2 Update validate-all-standards.sh

Add to VALIDATORS array (around line 87):
```bash
"lean-linting|${LINT_DIR}/check-lean-linting.sh|ERROR|*.lean"
```

Add flag (around line 113):
```bash
RUN_LEAN_LINTING=false
```

Add to parse_args (around line 240):
```bash
--lean-linting)
  RUN_LEAN_LINTING=true
  ;;
```

Add to should_run_validator (around line 327):
```bash
lean-linting)
  $RUN_LEAN_LINTING && return 0
  ;;
```

Update help text (around line 140):
```bash
  --lean-linting     Run LEAN 4 linting validator only
```

### Phase 6: CI/CD Integration (1 hour)

#### 6.1 Update GitHub Actions Workflow

**File**: `.github/workflows/ci.yml`

**Before** (lines 47-49):
```yaml
    - name: Run linter
      run: lake lint
      continue-on-error: true  # Remove when lint is configured
```

**After**:
```yaml
    - name: Run LEAN 4 linting
      run: |
        # Verify lint driver configured
        lake check-lint
        
        # Run linting (will fail workflow on errors)
        lake lint
      # No continue-on-error - lint failures block builds

    - name: Run comprehensive validation
      run: |
        # Run all validators including LEAN linting
        bash .claude/scripts/validate-all-standards.sh --all

    - name: Upload lint results
      if: always()
      uses: actions/upload-artifact@v4
      with:
        name: lean-lint-results
        path: |
          .lake/lint-output.txt
          .claude/tmp/lean-lint-state.json
        retention-days: 30
```

#### 6.2 Add Problem Matchers (Optional)

For better GitHub integration, add problem matcher:

```yaml
    - name: Setup LEAN problem matchers
      run: |
        echo "::add-matcher::.github/problem-matchers/lean.json"

    - name: Run LEAN 4 linting
      run: lake lint

    - name: Remove problem matchers
      if: always()
      run: |
        echo "::remove-matcher owner=lean::"
```

**File**: `.github/problem-matchers/lean.json`

```json
{
  "problemMatcher": [
    {
      "owner": "lean",
      "pattern": [
        {
          "regexp": "^(.+):(\\d+):(\\d+):\\s+(error|warning):\\s+(.+)$",
          "file": 1,
          "line": 2,
          "column": 3,
          "severity": 4,
          "message": 5
        }
      ]
    }
  ]
}
```

## File Structure Changes

### New Files

```
lakefile.lean                          # Converted from lakefile.toml
scripts/
├── LintAll.lean                       # Main lint driver
├── RunEnvLinters.lean                 # Environment linter executable
└── LintStyle.lean                     # Text-based linter executable

Logos/Lint/
├── EnvLinters.lean                    # Custom environment linters
└── README.md                          # Lint system documentation

.claude/scripts/lint/
├── check-lean-linting.sh              # Opencode validator (revised)
└── README.md                          # Lint integration docs

.github/problem-matchers/
└── lean.json                          # GitHub problem matcher

.backups/
└── lakefile.toml.backup               # Backup of original lakefile
```

### Modified Files

```
.github/workflows/ci.yml               # Remove continue-on-error, add validation
.claude/scripts/validate-all-standards.sh  # Add lean-linting validator
CLAUDE.md                              # Update essential commands
Documentation/Development/LEAN_STYLE_GUIDE.md  # Add linter configuration
```

### Deleted Files

```
lakefile.toml                          # Replaced by lakefile.lean
```

## Integration Points

### 1. Lake ↔ Opencode Bridge

**Flow**:
```
lake lint → LintAll.lean → runEnvLinters + lintStyle → exit code
    ↓
check-lean-linting.sh → parse output → opencode state → error logging
    ↓
validate-all-standards.sh → aggregate results → CI/CD
```

**Data Transformation**:
- Lake exit codes → Opencode ERROR/WARNING severity
- Linter output → Structured JSON state
- File paths → Absolute paths for opencode

### 2. Linter Execution Flow

**Syntax Linters** (during `lake build`):
```
lakefile.lean (leanOptions) → set_option linter.* → compilation → warnings
```

**Environment Linters** (during `lake lint`):
```
lake lint → LintAll.lean → runEnvLinters → @[env_linter] → results
```

**Text-Based Linters** (during `lake lint`):
```
lake lint → LintAll.lean → lintStyle → source file checks → results
```

### 3. CI/CD Integration

**GitHub Actions Workflow**:
1. Checkout code
2. Install elan (LEAN toolchain)
3. Cache Lake packages
4. Build project (`lake build` - syntax linters run here)
5. **Run linting** (`lake lint` - environment + text linters)
6. Run tests
7. Run comprehensive validation (includes lint check)
8. Upload artifacts

**Blocking Behavior**:
- Lint failures cause workflow failure (no continue-on-error)
- Results stored as artifacts for debugging
- Problem matchers annotate PR with inline errors

## Quality Standards

### Success Criteria

1. ✅ **Lakefile Converted**: lakefile.lean replaces lakefile.toml
2. ✅ **Lake Lint Configured**: `lake check-lint` passes
3. ✅ **Linter Set Defined**: `linter.logosStandardSet` registered
4. ✅ **Syntax Linters Enabled**: Run during `lake build`
5. ✅ **Environment Linters Implemented**: Custom TM-specific checks
6. ✅ **Text-Based Linters Implemented**: Source file style checks
7. ✅ **Opencode Integration**: Integrated with validate-all-standards.sh
8. ✅ **CI/CD Blocking**: Lint failures block PRs and commits
9. ✅ **Zero Warnings**: All LEAN 4 code passes configured linters

### Performance Targets

- **Syntax Linters**: No additional overhead (run during build)
- **Environment Linters**: < 30 seconds for full repository
- **Text-Based Linters**: < 10 seconds for full repository
- **Total Lint Time**: < 1 minute additional to build time
- **CI/CD Overhead**: < 2 minutes additional to workflow

### Compliance Requirements

- **LEAN 4 Style Guide**: 100% compliance with project standards
- **Documentation Coverage**: ≥ 95% docstring coverage (enforced by linters)
- **Error Handling**: All lint failures properly logged and reported
- **State Management**: Complete integration with opencode state system

## Technical Implementation Details

### Linter Configuration

**Syntax Linters** (in lakefile.lean):
```lean
lean_lib Logos where
  leanOptions := #[
    -- Enable Logos linter set
    ⟨`weak.linter.logosStandardSet, true⟩,
    
    -- Configure specific linters
    ⟨`weak.linter.style.longLine.maxColumn, 100⟩,
    ⟨`weak.linter.missingDocs.checkPrivate, false⟩,
    ⟨`weak.linter.unusedVariables.funArgs, true⟩
  ]
```

**Environment Linters** (in Logos/Lint/EnvLinters.lean):
```lean
@[env_linter]
def myLinter : Linter where
  noErrorsFound := "All checks passed."
  errorsFound := "ISSUES FOUND:"
  test declName := do
    -- Linting logic
    return none  -- or Some errorMessage
```

**Text-Based Linters** (in scripts/LintStyle.lean):
```lean
def myStyleLinter : StyleLinter where
  name := "myCheck"
  check := fun content => -- Array (Nat × String)
  fix := fun content => -- String
```

### Suppression Mechanisms

**1. Per-declaration suppression**:
```lean
@[nolint docBlame unusedArguments]
def myFunction := ...
```

**2. File/section scope**:
```lean
set_option linter.unusedVariables false in
def myFunction := ...
```

**3. Project-wide exceptions** (scripts/nolints.json):
```json
[
  ["docBlame", "Logos.Core.Internal.Helper"],
  ["unusedArguments", "Logos.Test.Fixture"]
]
```

### Error Format

**Linter Output** (error format):
```
Logos/Core/Syntax/Formula.lean:45:12: error: Line exceeds 100 characters
Logos/Core/ProofSystem/Axioms.lean:78:3: error: Missing docstring
```

**Opencode State** (JSON):
```json
{
  "validator": "lean-linting",
  "timestamp": "2025-12-15T10:30:00Z",
  "exit_code": 1,
  "errors": 2,
  "warnings": 0,
  "lint_output": "/path/.lake/lint-output.txt",
  "lake_version": "5.0.0",
  "lean_version": "4.14.0"
}
```

## Testing Strategy

### Phase 1 Testing (Lakefile Conversion)

```bash
# 1. Backup and convert
cp lakefile.toml .backups/lakefile.toml.backup
# Create lakefile.lean (as specified above)

# 2. Test build
lake clean
lake build

# 3. Verify lint driver
lake check-lint

# 4. Test lint (will fail until driver implemented)
lake lint || echo "Expected failure - driver not yet implemented"
```

### Phase 2 Testing (Lint Driver)

```bash
# 1. Build lint driver
lake build lintAll

# 2. Test lint driver directly
lake exe lintAll

# 3. Test via lake lint
lake lint

# 4. Test with arguments
lake lint -- --verbose
lake lint -- Logos.Core.Syntax
```

### Phase 3 Testing (Environment Linters)

```bash
# 1. Build environment linters
lake build Logos.Lint.EnvLinters

# 2. Test environment linter executable
lake exe runEnvLinters Logos

# 3. Test via lint driver
lake lint -- --verbose
```

### Phase 4 Testing (Text-Based Linters)

```bash
# 1. Build text linter
lake build lintStyle

# 2. Test on single file
lake exe lintStyle Logos/Core/Syntax/Formula.lean

# 3. Test auto-fix
lake exe lintStyle --fix Logos/Core/Syntax/Formula.lean

# 4. Test via lint driver
lake lint
```

### Phase 5 Testing (Opencode Integration)

```bash
# 1. Test opencode validator directly
bash .claude/scripts/lint/check-lean-linting.sh

# 2. Test via validation framework
bash .claude/scripts/validate-all-standards.sh --lean-linting

# 3. Test full validation
bash .claude/scripts/validate-all-standards.sh --all

# 4. Verify state file created
cat .claude/tmp/lean-lint-state.json
```

### Phase 6 Testing (CI/CD)

1. Create test PR with intentional lint violation
2. Verify GitHub Actions fails on lint step
3. Verify artifacts uploaded with lint results
4. Fix violation and verify workflow passes
5. Check problem matcher annotations on PR

## Rollback Plan

### Immediate Rollback (if lakefile.lean causes issues)

```bash
# 1. Restore lakefile.toml
cp .backups/lakefile.toml.backup lakefile.toml
rm lakefile.lean

# 2. Revert CI/CD changes
git checkout HEAD -- .github/workflows/ci.yml

# 3. Remove new files
rm -rf scripts/LintAll.lean scripts/RunEnvLinters.lean scripts/LintStyle.lean
rm -rf Logos/Lint/
rm .claude/scripts/lint/check-lean-linting.sh

# 4. Rebuild
lake clean
lake build
```

### Partial Rollback (keep lakefile.lean, disable linting)

```bash
# 1. Comment out lintDriver in lakefile.lean
# lintDriver := "lintAll"  -- Disabled

# 2. Restore continue-on-error in CI
git checkout HEAD -- .github/workflows/ci.yml

# 3. Rebuild
lake clean
lake build
```

## Future Enhancements

### Phase 2 Features (Post-MVP)

1. **Custom TM Linters**:
   - Modal operator usage patterns
   - Temporal operator conventions
   - Proof structure validation
   - Axiom usage tracking

2. **Enhanced Auto-fix**:
   - Automatic line breaking
   - Import organization
   - Whitespace normalization
   - Documentation template generation

3. **IDE Integration**:
   - VS Code extension integration
   - Real-time linting feedback
   - Quick-fix suggestions
   - Inline documentation

4. **Metrics & Reporting**:
   - Lint compliance dashboard
   - Historical trend analysis
   - Per-module quality scores
   - Technical debt tracking

5. **Pre-commit Hooks**:
   - Automatic staged file linting
   - Fast incremental checks
   - Developer workflow optimization

### Advanced Features

1. **Semantic Analysis**:
   - Cross-file consistency checking
   - Proof pattern validation
   - Theorem naming conventions
   - Import dependency analysis

2. **Performance Optimization**:
   - Parallel linting of files
   - Incremental caching
   - Smart file targeting
   - Lazy linter loading

3. **Custom Rule Configuration**:
   - Per-directory rule overrides
   - Team-specific conventions
   - Gradual strictness migration
   - Exception management UI

## Dependencies

- **LEAN 4.14.0+**: Core linters and linter sets
- **Lake 5.0.0+**: Native `lake lint` command
- **Mathlib v4.14.0**: Dependency (provides additional linters)
- **Batteries**: Environment linter infrastructure
- **Opencode Framework**: Validation and error logging
- **GitHub Actions**: CI/CD execution environment

## Risks & Mitigations

| Risk | Impact | Mitigation |
|------|--------|------------|
| lakefile.lean conversion breaks build | High | Thorough testing, backup lakefile.toml, rollback plan |
| Lake lint API changes in future | Medium | Document current API, version pinning, migration plan |
| Performance degradation | Medium | Benchmark and optimize, parallel execution, caching |
| False positives from linters | Medium | Clear suppression guidelines, nolints.json, review process |
| Developer friction | Medium | Comprehensive docs, auto-fix, gradual rollout |
| CI/CD disruption | High | Gradual rollout, continue-on-error initially, monitoring |

## Conclusion

This revised specification provides a comprehensive, research-backed approach to integrating Lake's native linting capabilities with the Logos project's opencode validation framework. By converting to lakefile.lean and implementing a hybrid linting approach (syntax + environment + text-based), we can enforce LEAN 4 coding standards while maintaining compatibility with existing workflows.

The phased implementation ensures incremental delivery with minimal risk, while the comprehensive integration ensures that linting becomes a natural part of the development workflow rather than an external check.

---

**Next Steps:**

1. ✅ Review and approve this specification
2. ⏳ Phase 1: Convert lakefile.toml to lakefile.lean (2 hours)
3. ⏳ Phase 2: Implement custom lint driver (2 hours)
4. ⏳ Phase 3: Implement environment linters (1.5 hours)
5. ⏳ Phase 4: Implement text-based linters (1 hour)
6. ⏳ Phase 5: Integrate with opencode (1.5 hours)
7. ⏳ Phase 6: Update CI/CD (1 hour)
8. ⏳ Testing and refinement (2 hours)

**Total Estimated Timeline: 6-8 hours (1-2 days)**

**Approval Required From:**
- Project maintainer
- CI/CD stakeholders
- Development team

---

*This specification is based on comprehensive research into LEAN 4.14.0, Lake 5.0.0, and Mathlib v4.14.0 linting infrastructure. See `.claude/research/lean4-linting-research.md` for detailed research findings.*
