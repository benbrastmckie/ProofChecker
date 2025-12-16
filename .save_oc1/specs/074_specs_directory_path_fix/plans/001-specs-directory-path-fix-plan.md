# Plan 074: .opencode System Independence - Complete Migration from .claude

**Created**: 2025-12-15
**Revised**: 2025-12-15 (Expanded to full independence)
**Status**: Ready for Implementation
**Priority**: Critical
**Complexity**: 4 (Multi-phase migration with extensive testing)

## Problem Statement

The `.opencode/` system is currently completely dependent on `.claude/` infrastructure:
- **Specs created in wrong location**: New specs go to `.claude/specs/` instead of `.opencode/specs/`
- **Library dependency**: All commands source ~400,000 lines of shell libraries from `.claude/lib/`
- **Path references**: Hundreds of hardcoded `.claude/` paths throughout the system
- **Command duplication**: Overlapping commands in both `.claude/commands/` and `.opencode/command/`

**Goal**: Make `.opencode/` completely independent of `.claude/`, enabling eventual removal of the `.claude/` directory.

## Root Cause Analysis

### Primary Issue: Library Dependency

`.opencode/lib/` does not exist. All commands and workflows depend on:
- `.claude/lib/core/` - 12 essential libraries (~200K lines)
- `.claude/lib/workflow/` - 13 workflow libraries (~200K lines)
- `.claude/lib/plan/`, `.claude/lib/todo/`, `.claude/lib/artifact/` - Supporting libraries

### Secondary Issue: Specs Path Priority

In `.claude/lib/workflow/workflow-initialization.sh` (lines 463-471), specs detection prioritizes `.claude/specs` over `.opencode/specs`.

### Tertiary Issues

- Command duplication (18 in `.claude/commands/` vs 16 in `.opencode/command/`)
- Agent duplication (32 in `.claude/agents/` vs 9 in `.opencode/agent/`)
- Documentation references to `.claude/` paths

## Current State

| Component | .claude/ | .opencode/ | Dependency |
|-----------|----------|------------|------------|
| **Libraries** | 1.1M (~400K lines) | None | **Complete** |
| **Specs** | 4.8M (46 specs) | ~100K (1 spec) | High |
| **Commands** | 18 commands | 16 commands | Medium |
| **Agents** | 32 agents | 9 agents | Low |
| **Context** | Minimal | Rich LEAN 4 | None (✓) |
| **Documentation** | Scattered | Organized | None (✓) |

## Solution Design - Multi-Phase Migration

### Phase 1: Library Migration (CRITICAL - 4-6 hours)

**Objective**: Create `.opencode/lib/` with all essential libraries

**Actions**:

1. **Create directory structure**:
   ```bash
   mkdir -p .opencode/lib/{core,workflow,plan,todo,artifact,convert,lean,util}
   ```

2. **Copy core libraries** (12 files, ~200K lines):
   ```bash
   cp .claude/lib/core/*.sh .opencode/lib/core/
   ```
   
   Files:
   - `error-handling.sh` (75,927 lines) - Error logging, trapping
   - `state-persistence.sh` (44,957 lines) - Workflow state
   - `unified-location-detection.sh` (26,793 lines) - Project detection
   - `unified-logger.sh` (21,695 lines) - Structured logging
   - `library-version-check.sh` (6,538 lines) - Dependency validation
   - `detect-project-dir.sh` (1,540 lines) - Project root
   - `summary-formatting.sh` (2,320 lines) - Console output
   - `timestamp-utils.sh` (3,087 lines) - Timestamps
   - `base-utils.sh` (1,532 lines) - Basic utilities
   - `library-sourcing.sh` (3,974 lines) - Library loading
   - `source-libraries.sh` (2,803 lines) - Sourcing
   - `source-libraries-inline.sh` (5,434 lines) - Inline sourcing

3. **Copy workflow libraries** (13 files, ~200K lines):
   ```bash
   cp .claude/lib/workflow/*.sh .opencode/lib/workflow/
   ```
   
   Files:
   - `workflow-state-machine.sh` (46,286 lines) - State machine
   - `workflow-initialization.sh` (42,087 lines) - **KEY FILE** (path init)
   - `checkpoint-utils.sh` (42,364 lines) - Checkpoints
   - `validation-utils.sh` (20,958 lines) - Validation
   - `metadata-extraction.sh` (19,886 lines) - Metadata
   - `workflow-llm-classifier.sh` (25,026 lines) - LLM classification
   - `context-pruning.sh` (15,218 lines) - Context optimization
   - `workflow-scope-detection.sh` (6,420 lines) - Scope detection
   - `barrier-utils.sh` (5,908 lines) - Hard barriers
   - `argument-capture.sh` (6,711 lines) - Argument parsing
   - `workflow-bootstrap.sh` (3,381 lines) - Bootstrap
   - `workflow-detection.sh` (2,981 lines) - Detection
   - `workflow-init.sh` (16,000 lines) - Initialization

4. **Copy supporting libraries**:
   ```bash
   cp -r .claude/lib/plan/*.sh .opencode/lib/plan/
   cp -r .claude/lib/todo/*.sh .opencode/lib/todo/
   cp -r .claude/lib/artifact/*.sh .opencode/lib/artifact/
   cp -r .claude/lib/convert/*.sh .opencode/lib/convert/
   cp -r .claude/lib/lean/*.sh .opencode/lib/lean/
   cp -r .claude/lib/util/*.sh .opencode/lib/util/
   ```

5. **Create README files**:
   ```bash
   # Document library purpose and dependencies
   cat > .opencode/lib/README.md <<'EOF'
   # .opencode Library System
   
   Shell libraries supporting the .opencode command and agent infrastructure.
   
   ## Directory Structure
   
   - `core/` - Essential utilities (error handling, state, logging)
   - `workflow/` - Workflow orchestration (state machine, initialization)
   - `plan/` - Plan management utilities
   - `todo/` - TODO management
   - `artifact/` - Artifact creation
   - `convert/` - Document conversion
   - `lean/` - LEAN 4 specific utilities
   - `util/` - General utilities
   
   ## Migration Note
   
   These libraries were migrated from `.claude/lib/` on 2025-12-15 as part of
   Plan 074 to make `.opencode/` independent of `.claude/`.
   
   Original source: `.claude/lib/` (deprecated, will be removed)
   EOF
   ```

**Verification**:
```bash
# Check all files copied
find .opencode/lib -name "*.sh" | wc -l  # Should be ~50 files
du -sh .opencode/lib  # Should be ~1.1M
```

### Phase 2: Update Library Path References (CRITICAL - 2-3 hours)

**Objective**: Update all `.opencode/` files to source from `.opencode/lib/`

**Actions**:

1. **Update workflow-initialization.sh** (KEY FILE):
   
   File: `.opencode/lib/workflow/workflow-initialization.sh`
   
   Lines 463-471 (specs directory detection):
   ```bash
   # Determine specs directory
   # CRITICAL: Check OPENCODE_SPECS_ROOT override first (for test isolation)
   local specs_root
   if [ -n "${OPENCODE_SPECS_ROOT:-}" ] && [ -d "${OPENCODE_SPECS_ROOT}" ]; then
     specs_root="${OPENCODE_SPECS_ROOT}"
     if [[ "$OPENCODE_SPECS_ROOT" == /tmp/* ]] && [[ "${OPENCODE_PROJECT_DIR:-}" != /tmp/* ]]; then
       echo "WARNING: OPENCODE_SPECS_ROOT is temporary but OPENCODE_PROJECT_DIR is not." >&2
     fi
   # PRIORITY 1: Check for .opencode/specs (PRIMARY LOCATION)
   elif [ -d "${project_root}/.opencode/specs" ]; then
     specs_root="${project_root}/.opencode/specs"
   # PRIORITY 2: Check for .claude/specs (DEPRECATED - legacy read-only)
   elif [ -d "${project_root}/.claude/specs" ]; then
     specs_root="${project_root}/.claude/specs"
     echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
     echo "WARNING: Using DEPRECATED .claude/specs directory" >&2
     echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━" >&2
     echo "" >&2
     echo "New specs should be created in .opencode/specs/" >&2
     echo "The .claude/ directory will be removed in a future release." >&2
     echo "" >&2
     echo "Migration: Move specs to .opencode/specs/ when convenient" >&2
     echo "" >&2
   # PRIORITY 3: Check for specs/ (alternative location)
   elif [ -d "${project_root}/specs" ]; then
     specs_root="${project_root}/specs"
   else
     # Default to .opencode/specs and create it
     specs_root="${project_root}/.opencode/specs"
     mkdir -p "$specs_root"
   fi
   ```

2. **Update all library cross-references**:
   
   Find and replace in all `.opencode/lib/**/*.sh` files:
   ```bash
   # Find all source statements referencing .claude/lib
   grep -r "source.*\.claude/lib" .opencode/lib/ --include="*.sh"
   
   # Replace with .opencode/lib
   find .opencode/lib -name "*.sh" -exec sed -i 's|\.claude/lib|.opencode/lib|g' {} \;
   ```

3. **Update environment variable names**:
   
   Replace `CLAUDE_*` with `OPENCODE_*` in library files:
   ```bash
   # In workflow-initialization.sh and other files
   CLAUDE_PROJECT_DIR → OPENCODE_PROJECT_DIR
   CLAUDE_SPECS_ROOT → OPENCODE_SPECS_ROOT
   ```
   
   **Note**: Keep backward compatibility by checking both:
   ```bash
   project_root="${OPENCODE_PROJECT_DIR:-${CLAUDE_PROJECT_DIR}}"
   ```

4. **Update detect-project-dir.sh**:
   
   File: `.opencode/lib/core/detect-project-dir.sh`
   
   Update to detect `.opencode/` directory:
   ```bash
   # Detect project directory by looking for .opencode/ or .claude/ (legacy)
   if command -v git &>/dev/null && git rev-parse --git-dir >/dev/null 2>&1; then
     OPENCODE_PROJECT_DIR="$(git rev-parse --show-toplevel)"
   else
     current_dir="$(pwd)"
     while [ "$current_dir" != "/" ]; do
       if [ -d "$current_dir/.opencode" ]; then
         OPENCODE_PROJECT_DIR="$current_dir"
         break
       elif [ -d "$current_dir/.claude" ]; then
         # Legacy fallback
         OPENCODE_PROJECT_DIR="$current_dir"
         echo "WARNING: Using .claude/ for project detection (deprecated)" >&2
         break
       fi
       current_dir="$(dirname "$current_dir")"
     done
   fi
   
   export OPENCODE_PROJECT_DIR
   # Backward compatibility
   export CLAUDE_PROJECT_DIR="$OPENCODE_PROJECT_DIR"
   ```

**Verification**:
```bash
# Check no .claude/lib references remain in .opencode/lib
grep -r "\.claude/lib" .opencode/lib/ --include="*.sh" | wc -l  # Should be 0
```

### Phase 3: Update Command Files (CRITICAL - 2-3 hours)

**Objective**: Update all `.opencode/command/*.md` files to source from `.opencode/lib/`

**Actions**:

1. **Identify commands with library dependencies**:
   ```bash
   grep -l "source.*\.claude/lib" .opencode/command/*.md
   ```

2. **Update each command file**:
   
   Find and replace pattern:
   ```bash
   # OLD
   source "${CLAUDE_PROJECT_DIR}/.claude/lib/core/error-handling.sh"
   
   # NEW
   source "${OPENCODE_PROJECT_DIR}/.opencode/lib/core/error-handling.sh"
   ```
   
   Automated replacement:
   ```bash
   find .opencode/command -name "*.md" -exec sed -i \
     -e 's|CLAUDE_PROJECT_DIR|OPENCODE_PROJECT_DIR|g' \
     -e 's|\.claude/lib|.opencode/lib|g' \
     {} \;
   ```

3. **Update project directory detection in commands**:
   
   Replace detection logic:
   ```bash
   # OLD
   if [ -z "$CLAUDE_PROJECT_DIR" ] || [ ! -d "$CLAUDE_PROJECT_DIR/.claude" ]; then
     echo "ERROR: Failed to detect project directory" >&2
     exit 1
   fi
   
   # NEW
   if [ -z "$OPENCODE_PROJECT_DIR" ] || [ ! -d "$OPENCODE_PROJECT_DIR/.opencode" ]; then
     echo "ERROR: Failed to detect project directory" >&2
     exit 1
   fi
   ```

4. **Update temp file paths**:
   ```bash
   # OLD
   mkdir -p "${HOME}/.claude/tmp"
   TEMP_FILE="${HOME}/.claude/tmp/research_arg_$(date +%s%N).txt"
   
   # NEW
   mkdir -p "${HOME}/.opencode/tmp"
   TEMP_FILE="${HOME}/.opencode/tmp/research_arg_$(date +%s%N).txt"
   ```

**Verification**:
```bash
# Check no .claude references in command files
grep -r "\.claude" .opencode/command/ --include="*.md" | grep -v "# OLD" | wc -l
```

### Phase 4: Update Agent Files (HIGH - 1-2 hours)

**Objective**: Update all `.opencode/agent/**/*.md` files to reference `.opencode/` paths

**Actions**:

1. **Update agent file path references**:
   ```bash
   find .opencode/agent -name "*.md" -exec sed -i \
     -e 's|\.claude/agents|.opencode/agent|g' \
     -e 's|\.claude/specs|.opencode/specs|g' \
     -e 's|\.claude/lib|.opencode/lib|g' \
     {} \;
   ```

2. **Update agent invocation patterns**:
   
   Example in research-coordinator equivalent:
   ```markdown
   # OLD
   Read and follow ALL behavioral guidelines from:
   ${CLAUDE_PROJECT_DIR}/.claude/agents/research-specialist.md
   
   # NEW
   Read and follow ALL behavioral guidelines from:
   ${OPENCODE_PROJECT_DIR}/.opencode/agent/subagents/researcher/research-specialist.md
   ```

**Verification**:
```bash
grep -r "\.claude" .opencode/agent/ --include="*.md" | wc -l  # Should be minimal
```

### Phase 5: Update Documentation (HIGH - 2-3 hours)

**Objective**: Update all documentation to reference `.opencode/` paths

**Actions**:

1. **Update CLAUDE.md**:
   
   Line 21:
   ```markdown
   # OLD
   | [.claude/TODO.md](.claude/TODO.md) | Implementation plans in `.claude/specs/` | After `/create-plan`, `/research`, `/todo` |
   
   # NEW
   | [.opencode/TODO.md](.opencode/TODO.md) | Implementation plans in `.opencode/specs/` | After `/create-plan`, `/research`, `/todo` |
   ```
   
   Lines 202, 204 (axiom refactoring references):
   ```markdown
   # OLD
   See `.claude/specs/070_axiom_refactoring_efq_peirce/` for details.
   
   # NEW
   See `.opencode/specs/070_axiom_refactoring_efq_peirce/` for details.
   (Note: Legacy specs remain in `.claude/specs/` until migrated)
   ```

2. **Update Documentation/ProjectInfo/MAINTENANCE.md**:
   
   Replace all `.claude/specs/` with `.opencode/specs/`:
   ```bash
   sed -i 's|\.claude/specs|.opencode/specs|g' Documentation/ProjectInfo/MAINTENANCE.md
   ```

3. **Update Documentation/Development/MAINTENANCE.md**:
   ```bash
   sed -i 's|\.claude/specs|.opencode/specs|g' Documentation/Development/MAINTENANCE.md
   ```

4. **Update TODO.md**:
   
   Line 16:
   ```markdown
   # OLD
   - Implementation plans (use `.claude/specs/` directories)
   
   # NEW
   - Implementation plans (use `.opencode/specs/` directories)
   ```

5. **Create migration guide**:
   
   File: `.opencode/docs/MIGRATION_FROM_CLAUDE.md`
   ```markdown
   # Migration Guide: .claude → .opencode
   
   ## Overview
   
   As of 2025-12-15, the `.opencode/` system is fully independent of `.claude/`.
   The `.claude/` directory is deprecated and will be removed in a future release.
   
   ## What Changed
   
   - **Libraries**: Moved from `.claude/lib/` to `.opencode/lib/`
   - **Specs**: New specs created in `.opencode/specs/` (legacy in `.claude/specs/`)
   - **Commands**: Use `.opencode/command/` (`.claude/commands/` deprecated)
   - **Agents**: Use `.opencode/agent/` (`.claude/agents/` deprecated)
   
   ## Migration Steps for Users
   
   1. **Update environment variables** (optional):
      ```bash
      # Add to ~/.bashrc or ~/.zshrc
      export OPENCODE_PROJECT_DIR="$HOME/path/to/project"
      ```
   
   2. **Move custom specs** (optional):
      ```bash
      mv .claude/specs/NNN_my_spec .opencode/specs/
      ```
   
   3. **Update custom scripts**:
      - Replace `.claude/lib/` with `.opencode/lib/`
      - Replace `CLAUDE_PROJECT_DIR` with `OPENCODE_PROJECT_DIR`
   
   ## Backward Compatibility
   
   - Legacy `.claude/specs/` remain accessible (read-only)
   - `CLAUDE_PROJECT_DIR` still works (aliased to `OPENCODE_PROJECT_DIR`)
   - Warnings displayed when using deprecated paths
   
   ## Timeline
   
   - **2025-12-15**: Migration complete, `.claude/` deprecated
   - **2026-01-15**: Stronger deprecation warnings
   - **2026-03-15**: `.claude/` directory removed (tentative)
   ```

**Verification**:
```bash
# Check documentation updated
grep -r "\.claude/specs" Documentation/ CLAUDE.md TODO.md | wc -l
```

### Phase 6: Testing and Validation (CRITICAL - 4-5 hours)

**Objective**: Ensure no regressions, all workflows functional

**Test Suite**:

#### Test 1: Library Loading
```bash
# Test that libraries load without errors
source .opencode/lib/core/error-handling.sh
source .opencode/lib/core/state-persistence.sh
source .opencode/lib/workflow/workflow-initialization.sh

# Verify functions exist
declare -f log_command_error >/dev/null && echo "✓ error-handling loaded"
declare -f append_workflow_state >/dev/null && echo "✓ state-persistence loaded"
declare -f initialize_workflow_paths >/dev/null && echo "✓ workflow-initialization loaded"
```

#### Test 2: Specs Directory Creation
```bash
# Test new spec creation in .opencode/specs
cd /tmp
mkdir test_project
cd test_project
mkdir -p .opencode/specs

# Simulate workflow
export OPENCODE_PROJECT_DIR="$(pwd)"
source .opencode/lib/workflow/workflow-initialization.sh

# Should create in .opencode/specs
initialize_workflow_paths "test workflow" "research-only" 2 ""

# Verify
test -d .opencode/specs/001_test_workflow && echo "✓ Spec created in .opencode/specs"
```

#### Test 3: Legacy Specs Access
```bash
# Test that legacy .claude/specs are still accessible
test -d .claude/specs/072_deduction_theorem_completion && echo "✓ Legacy specs accessible"

# Verify warning displayed
# (manual verification - check stderr output)
```

#### Test 4: Command Execution
```bash
# Test /research command
/research "test topic for validation"

# Verify:
# 1. Spec created in .opencode/specs/
# 2. No errors in library loading
# 3. State persistence works
# 4. Report created successfully
```

#### Test 5: State Persistence
```bash
# Test workflow state across bash blocks
# (Integration test - run full workflow and verify state files)

# Check state file location
ls -la .opencode/tmp/workflow_*.sh

# Verify state variables persist
```

#### Test 6: Environment Variable Compatibility
```bash
# Test backward compatibility
export CLAUDE_PROJECT_DIR="/path/to/project"
source .opencode/lib/core/detect-project-dir.sh

# Verify OPENCODE_PROJECT_DIR set
test -n "$OPENCODE_PROJECT_DIR" && echo "✓ Backward compatibility works"
```

#### Test 7: Error Handling
```bash
# Test error logging to .opencode/tmp/errors.jsonl
# (Trigger intentional error and verify logging)

# Check error log exists
test -f .opencode/tmp/errors.jsonl && echo "✓ Error logging works"
```

#### Test 8: Full Workflow Integration
```bash
# Test complete workflow: research → plan → implement
/prove "test theorem: 1 + 1 = 2"

# Verify:
# 1. Research reports in .opencode/specs/NNN_*/reports/
# 2. Plan in .opencode/specs/NNN_*/plans/
# 3. Implementation artifacts created
# 4. No errors in any phase
```

**Verification Checklist**:
- [ ] All libraries load without errors
- [ ] Specs created in `.opencode/specs/` by default
- [ ] Legacy specs in `.claude/specs/` accessible with warning
- [ ] Commands execute successfully
- [ ] State persistence works across bash blocks
- [ ] Environment variables compatible (CLAUDE_* → OPENCODE_*)
- [ ] Error logging works
- [ ] Full workflows complete end-to-end

### Phase 7: Deprecation and Cleanup (LOW - Ongoing)

**Objective**: Mark `.claude/` as deprecated, plan eventual removal

**Actions**:

1. **Add deprecation notice to .claude/README.md**:
   ```markdown
   # ⚠️ DEPRECATED: .claude Directory
   
   **This directory is deprecated as of 2025-12-15.**
   
   All functionality has been migrated to `.opencode/`.
   
   ## Migration
   
   - Libraries: `.claude/lib/` → `.opencode/lib/`
   - Specs: `.claude/specs/` → `.opencode/specs/` (new specs only)
   - Commands: `.claude/commands/` → `.opencode/command/`
   - Agents: `.claude/agents/` → `.opencode/agent/`
   
   ## Timeline
   
   - **2025-12-15**: Migration complete, this directory deprecated
   - **2026-01-15**: Stronger warnings added
   - **2026-03-15**: This directory will be removed (tentative)
   
   ## What to Do
   
   1. Update any custom scripts to use `.opencode/` paths
   2. Move custom specs to `.opencode/specs/` when convenient
   3. See `.opencode/docs/MIGRATION_FROM_CLAUDE.md` for details
   ```

2. **Add .claude/ to .gitignore** (optional, after migration period):
   ```bash
   # After 2-3 months, consider adding:
   echo ".claude/" >> .gitignore
   ```

3. **Create removal script** (for future use):
   
   File: `.opencode/scripts/remove-claude-directory.sh`
   ```bash
   #!/usr/bin/env bash
   # Script to safely remove .claude/ directory after migration period
   
   set -e
   
   echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
   echo "WARNING: This will remove the .claude/ directory"
   echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
   echo ""
   echo "This action is IRREVERSIBLE."
   echo ""
   echo "Before proceeding, ensure:"
   echo "  1. All custom specs moved to .opencode/specs/"
   echo "  2. All custom scripts updated to use .opencode/"
   echo "  3. All workflows tested and working"
   echo ""
   read -p "Are you sure you want to continue? (yes/no): " confirm
   
   if [ "$confirm" != "yes" ]; then
     echo "Aborted."
     exit 0
   fi
   
   # Create backup
   echo "Creating backup..."
   tar -czf ".claude-backup-$(date +%Y%m%d).tar.gz" .claude/
   echo "Backup created: .claude-backup-$(date +%Y%m%d).tar.gz"
   
   # Remove directory
   echo "Removing .claude/ directory..."
   rm -rf .claude/
   
   echo "✓ .claude/ directory removed"
   echo "✓ Backup available: .claude-backup-$(date +%Y%m%d).tar.gz"
   ```

**Timeline**:
- **Month 1 (Dec 2025)**: Complete migration, add deprecation notices
- **Month 2-3 (Jan-Feb 2026)**: Monitor for issues, fix bugs
- **Month 4 (Mar 2026)**: Add stronger warnings
- **Month 5-6 (Apr-May 2026)**: Final migration of any remaining dependencies
- **Month 7 (Jun 2026)**: Remove `.claude/` directory (optional)

## Implementation Steps

### Critical Path (Must Complete)

- [ ] **Phase 1**: Library Migration (4-6 hours)
  - [ ] Create `.opencode/lib/` directory structure
  - [ ] Copy all core libraries (12 files)
  - [ ] Copy all workflow libraries (13 files)
  - [ ] Copy supporting libraries (plan, todo, artifact, etc.)
  - [ ] Create README files

- [ ] **Phase 2**: Update Library Path References (2-3 hours)
  - [ ] Update `workflow-initialization.sh` specs detection
  - [ ] Update all library cross-references
  - [ ] Update environment variable names
  - [ ] Update `detect-project-dir.sh`

- [ ] **Phase 3**: Update Command Files (2-3 hours)
  - [ ] Identify commands with dependencies
  - [ ] Update source statements
  - [ ] Update project directory detection
  - [ ] Update temp file paths

- [ ] **Phase 6**: Testing and Validation (4-5 hours)
  - [ ] Test library loading
  - [ ] Test specs directory creation
  - [ ] Test legacy specs access
  - [ ] Test command execution
  - [ ] Test state persistence
  - [ ] Test environment variable compatibility
  - [ ] Test error handling
  - [ ] Test full workflow integration

### High Priority (Should Complete)

- [ ] **Phase 4**: Update Agent Files (1-2 hours)
  - [ ] Update agent path references
  - [ ] Update agent invocation patterns

- [ ] **Phase 5**: Update Documentation (2-3 hours)
  - [ ] Update CLAUDE.md
  - [ ] Update MAINTENANCE.md files
  - [ ] Update TODO.md
  - [ ] Create migration guide

### Low Priority (Optional)

- [ ] **Phase 7**: Deprecation and Cleanup (Ongoing)
  - [ ] Add deprecation notice to `.claude/README.md`
  - [ ] Create removal script
  - [ ] Plan removal timeline

## Success Criteria

### Critical Success Criteria

- ✅ `.opencode/lib/` exists with all essential libraries
- ✅ New specs created in `.opencode/specs/` by default
- ✅ All commands source from `.opencode/lib/`
- ✅ All workflows execute without errors
- ✅ State persistence works across bash blocks
- ✅ No regressions in existing functionality

### High Priority Success Criteria

- ✅ Legacy specs in `.claude/specs/` accessible with warning
- ✅ Documentation updated to reference `.opencode/`
- ✅ Migration guide created
- ✅ Agent files updated

### Low Priority Success Criteria

- ✅ Deprecation notice added to `.claude/`
- ✅ Removal script created
- ✅ Timeline documented

## Rollback Plan

If critical issues arise:

1. **Immediate Rollback** (< 1 hour):
   ```bash
   # Revert library changes
   rm -rf .opencode/lib
   
   # Revert command changes
   git checkout .opencode/command/
   
   # Revert agent changes
   git checkout .opencode/agent/
   ```

2. **Partial Rollback** (keep libraries, revert commands):
   ```bash
   # Keep .opencode/lib but revert command changes
   git checkout .opencode/command/
   ```

3. **Document Issues**:
   - Add issue to this plan
   - Create bug report in `.opencode/specs/074_*/reports/`
   - Plan fix for next iteration

## Risk Assessment

### High Risk Areas

1. **Library Migration** (400K lines of code)
   - **Risk**: Broken dependencies, missing files
   - **Mitigation**: Copy all files, verify checksums, test thoroughly

2. **State Persistence** (complex bash arrays)
   - **Risk**: State corruption, lost workflow data
   - **Mitigation**: Test state persistence extensively, keep backups

3. **Path References** (hundreds of locations)
   - **Risk**: Missed references, broken workflows
   - **Mitigation**: Systematic find-and-replace, grep verification

4. **Backward Compatibility** (existing workflows)
   - **Risk**: Breaking changes for users
   - **Mitigation**: Keep `.claude/` as fallback, add warnings

### Medium Risk Areas

1. **Command Duplication** (overlapping commands)
   - **Risk**: Confusion about which command to use
   - **Mitigation**: Document authoritative versions

2. **Agent Duplication** (overlapping agents)
   - **Risk**: Inconsistent behavior
   - **Mitigation**: Deprecate duplicates clearly

### Low Risk Areas

1. **Context System** (already in `.opencode/`)
   - **Risk**: None (already migrated)

2. **Documentation** (straightforward updates)
   - **Risk**: Minimal (find-and-replace)

## Estimated Effort

| Phase | Effort | Priority | Risk |
|-------|--------|----------|------|
| Phase 1: Library Migration | 4-6 hours | Critical | High |
| Phase 2: Path References | 2-3 hours | Critical | High |
| Phase 3: Command Files | 2-3 hours | Critical | Medium |
| Phase 4: Agent Files | 1-2 hours | High | Low |
| Phase 5: Documentation | 2-3 hours | High | Low |
| Phase 6: Testing | 4-5 hours | Critical | High |
| Phase 7: Deprecation | Ongoing | Low | Low |
| **Total Critical Path** | **12-17 hours** | - | - |
| **Total All Phases** | **15-22 hours** | - | - |

## Dependencies

**None** - This is a self-contained migration.

**Prerequisite**: Git commit before starting (for easy rollback)

## Follow-up Tasks

- [ ] Monitor for issues in first 2 weeks
- [ ] Create automated tests for library loading
- [ ] Add linting rule to detect new `.claude/` references
- [ ] Plan eventual removal of `.claude/` directory
- [ ] Update CI/CD pipelines to use `.opencode/` paths
- [ ] Notify users of migration (if applicable)

## Notes

- **Backward Compatibility**: Maintained via environment variable aliasing and legacy path fallbacks
- **Migration Period**: 2-3 months before considering `.claude/` removal
- **Testing**: Critical - allocate sufficient time for thorough testing
- **Documentation**: Keep migration guide updated as issues discovered

## Related Files

### Files to Create
- `.opencode/lib/` (entire directory structure)
- `.opencode/docs/MIGRATION_FROM_CLAUDE.md`
- `.opencode/scripts/remove-claude-directory.sh`
- `.claude/README.md` (deprecation notice)

### Files to Modify
- `.opencode/lib/workflow/workflow-initialization.sh` (specs path priority)
- `.opencode/lib/core/detect-project-dir.sh` (project detection)
- All `.opencode/command/*.md` files (source statements)
- All `.opencode/agent/**/*.md` files (path references)
- `CLAUDE.md` (documentation)
- `Documentation/ProjectInfo/MAINTENANCE.md` (documentation)
- `Documentation/Development/MAINTENANCE.md` (documentation)
- `TODO.md` (documentation)

### Files to Deprecate
- `.claude/lib/` (entire directory - keep as backup)
- `.claude/commands/` (keep as backup)
- `.claude/agents/` (keep as backup)
- `.claude/specs/` (keep as read-only legacy)

## Conclusion

This plan transforms `.opencode/` from a dependent subsystem into a fully independent, self-sufficient development environment. The migration is complex but systematic, with clear phases, comprehensive testing, and robust rollback procedures.

**Key Success Factors**:
1. Systematic approach (one phase at a time)
2. Comprehensive testing (no regressions)
3. Backward compatibility (smooth transition)
4. Clear documentation (user guidance)

**Timeline**: 15-22 hours total effort, spread over 1-2 weeks for thorough testing and validation.

**Outcome**: `.opencode/` becomes the primary system, `.claude/` deprecated and eventually removed.
