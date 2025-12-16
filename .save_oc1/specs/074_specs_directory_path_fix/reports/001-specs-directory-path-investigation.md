# Research Report: Specs Directory Path Priority Issue

**Date**: 2025-12-15
**Investigator**: General Agent
**Issue**: Specs created in `.claude/specs/` instead of `.opencode/specs/`

## Executive Summary

The research and planning commands (`/research`, `/create-plan`) are creating spec directories in `.claude/specs/` instead of the intended `.opencode/specs/` location. This is caused by incorrect priority order in the specs directory detection logic in `workflow-initialization.sh`.

**Root Cause**: Lines 463-471 of `.claude/lib/workflow/workflow-initialization.sh` check for `.claude/specs` before `.opencode/specs`, causing the legacy location to be preferred.

**Impact**: 
- User confusion (specs appearing in wrong location)
- Inconsistent project structure
- Documentation references incorrect paths

**Solution**: Reorder priority to check `.opencode/specs` first, add warning for legacy usage, change default to `.opencode/specs`.

## Investigation Process

### 1. Initial Observation

User reported seeing output like:
```
$ mkdir -p /home/benjamin/Documents/Philosophy/Projects/ProofChecker/.claude/specs/072_deduction_theorem_completion
```

Expected location: `.opencode/specs/`
Actual location: `.claude/specs/`

### 2. File Analysis

#### Research Command (.claude/commands/research.md)

Lines 21-22 show expected output location:
```markdown
**Expected Output**: Research reports in .claude/specs/NNN_topic/reports/
```

This is **incorrect** - should reference `.opencode/specs/`.

#### OpenCode Research Command (.opencode/command/research.md)

Simple command definition, delegates to researcher agent. No path configuration.

#### Research Coordinator Agent (.claude/agents/research-coordinator.md)

Lines 69-74 show example input with `.claude/specs`:
```yaml
report_dir: /home/user/.config/.claude/specs/028_lean/reports/
topic_path: /home/user/.config/.claude/specs/028_lean
```

This is **documentation only** (examples), not the source of the bug.

#### Researcher Agent (.opencode/agent/researcher.md)

Simple agent definition, no path configuration.

### 3. Root Cause Identification

#### workflow-initialization.sh (Lines 453-471)

```bash
# Determine specs directory
# CRITICAL: Check CLAUDE_SPECS_ROOT override first (for test isolation)
local specs_root
if [ -n "${CLAUDE_SPECS_ROOT:-}" ] && [ -d "${CLAUDE_SPECS_ROOT}" ]; then
  specs_root="${CLAUDE_SPECS_ROOT}"
  # Warn if override seems like a test but CLAUDE_PROJECT_DIR points to real project
  if [[ "$CLAUDE_SPECS_ROOT" == /tmp/* ]] && [[ "${CLAUDE_PROJECT_DIR:-}" != /tmp/* ]]; then
    echo "WARNING: CLAUDE_SPECS_ROOT is temporary but CLAUDE_PROJECT_DIR is not. This may cause isolation issues." >&2
  fi
elif [ -d "${project_root}/.claude/specs" ]; then  # ← BUG: Checked BEFORE .opencode/specs
  specs_root="${project_root}/.claude/specs"
elif [ -d "${project_root}/specs" ]; then
  specs_root="${project_root}/specs"
else
  # Default to .claude/specs and create it
  specs_root="${project_root}/.claude/specs"  # ← BUG: Wrong default
  mkdir -p "$specs_root"
fi
```

**Problems**:
1. `.claude/specs` checked before `.opencode/specs` (line 463)
2. `.opencode/specs` not checked at all
3. Default creation uses `.claude/specs` (line 469)

### 4. Current State Analysis

```bash
$ ls -1 .opencode/specs/
073_lake_lint_enhancements
[... other files ...]

$ ls -1 .claude/specs/ | head -10
001_proof_checker_package_docs
002_lean4_proof_checker_best_practices
005_lean4_language_research
007_rl_proof_reasoning_lean
008_lean_rust_python_integration_research
012_readme_broken_links_fix
019_research_todo_implementation_plan
021_lean4_bimodal_logic_best_practices
024_readme_narrative_organization_fix
027_temporal_duality_sorry_resolution
```

**Counts**:
- `.opencode/specs/`: 1 spec directory
- `.claude/specs/`: 46 spec directories

**Conclusion**: Both directories exist, but `.claude/specs` is prioritized due to detection order.

## Findings

### Finding 1: Incorrect Priority Order

**Location**: `.claude/lib/workflow/workflow-initialization.sh:463-471`

**Issue**: Detection logic checks `.claude/specs` before `.opencode/specs`, causing legacy location to be preferred.

**Evidence**:
```bash
elif [ -d "${project_root}/.claude/specs" ]; then
  specs_root="${project_root}/.claude/specs"
```

**Impact**: All new specs created in legacy location.

### Finding 2: Missing .opencode/specs Check

**Location**: `.claude/lib/workflow/workflow-initialization.sh:463-471`

**Issue**: No explicit check for `.opencode/specs` directory.

**Evidence**: Code only checks:
1. `CLAUDE_SPECS_ROOT` (test override)
2. `.claude/specs` (legacy)
3. `specs/` (alternative)
4. Default to `.claude/specs`

**Impact**: `.opencode/specs` never selected even if it exists.

### Finding 3: Incorrect Default

**Location**: `.claude/lib/workflow/workflow-initialization.sh:469`

**Issue**: Default creation path is `.claude/specs` instead of `.opencode/specs`.

**Evidence**:
```bash
else
  # Default to .claude/specs and create it
  specs_root="${project_root}/.claude/specs"
  mkdir -p "$specs_root"
fi
```

**Impact**: Fresh projects start with wrong directory structure.

### Finding 4: Documentation Inconsistencies

**Locations**: Multiple files reference `.claude/specs/`

**Files Affected**:
- `CLAUDE.md:21` - References `.claude/specs/`
- `Documentation/ProjectInfo/MAINTENANCE.md` - Multiple references
- `Documentation/Development/MAINTENANCE.md` - Multiple references
- `TODO.md:16` - References `.claude/specs/`

**Impact**: Documentation misleads users about correct location.

### Finding 5: Legacy Specs Exist

**Location**: `.claude/specs/`

**Issue**: 46 existing spec directories in legacy location.

**Evidence**:
```bash
$ find .claude/specs -type d -name "[0-9][0-9][0-9]*" | wc -l
46
```

**Impact**: Migration strategy needed (or dual-location support).

## Recommendations

### Recommendation 1: Fix Priority Order (Critical)

**Action**: Reorder detection logic to check `.opencode/specs` first.

**Implementation**:
```bash
# PRIORITY 1: Check for .opencode/specs (new standard location)
elif [ -d "${project_root}/.opencode/specs" ]; then
  specs_root="${project_root}/.opencode/specs"
# PRIORITY 2: Check for .claude/specs (legacy location, read-only)
elif [ -d "${project_root}/.claude/specs" ]; then
  specs_root="${project_root}/.claude/specs"
  echo "WARNING: Using legacy .claude/specs directory. New specs should be created in .opencode/specs/" >&2
```

**Rationale**: Ensures new standard location is preferred.

### Recommendation 2: Change Default (Critical)

**Action**: Change default creation path to `.opencode/specs`.

**Implementation**:
```bash
else
  # Default to .opencode/specs and create it (NEW DEFAULT)
  specs_root="${project_root}/.opencode/specs"
  mkdir -p "$specs_root"
fi
```

**Rationale**: Fresh projects should use correct structure.

### Recommendation 3: Add Warning (High)

**Action**: Warn when using legacy `.claude/specs` location.

**Implementation**: See Recommendation 1 code snippet.

**Rationale**: Alerts users to migration path.

### Recommendation 4: Update Documentation (High)

**Action**: Replace all `.claude/specs/` references with `.opencode/specs/`.

**Files**:
- `CLAUDE.md`
- `Documentation/ProjectInfo/MAINTENANCE.md`
- `Documentation/Development/MAINTENANCE.md`
- `TODO.md`

**Rationale**: Documentation should reflect correct usage.

### Recommendation 5: Leave Legacy Specs in Place (Medium)

**Action**: Do NOT migrate existing `.claude/specs/` directories.

**Rationale**:
- Avoids breaking existing references
- Reduces migration risk
- Simpler implementation
- Backward compatibility maintained

**Alternative**: If migration desired, create symlinks for compatibility.

## Testing Strategy

### Test Case 1: New Spec Creation

**Objective**: Verify new specs created in `.opencode/specs/`.

**Steps**:
1. Run `/research "test topic"`
2. Check created directory location

**Expected**: Spec created in `.opencode/specs/075_test_topic/`

### Test Case 2: Legacy Spec Access

**Objective**: Verify legacy specs remain accessible.

**Steps**:
1. Read file from `.claude/specs/072_deduction_theorem_completion/`
2. Verify no errors

**Expected**: File reads successfully, warning displayed.

### Test Case 3: Test Override

**Objective**: Verify `CLAUDE_SPECS_ROOT` override still works.

**Steps**:
1. Set `export CLAUDE_SPECS_ROOT=/tmp/test_specs`
2. Run workflow
3. Check spec location

**Expected**: Spec created in `/tmp/test_specs/`

### Test Case 4: Default Creation

**Objective**: Verify default directory creation.

**Steps**:
1. Remove `.opencode/specs/`
2. Run `/research "test default"`
3. Check created directory

**Expected**: `.opencode/specs/` created automatically.

## Implementation Complexity

**Estimated Effort**: ~50 minutes

**Breakdown**:
- Code changes: 15 minutes (simple priority reorder)
- Documentation updates: 15 minutes (find/replace)
- Testing: 20 minutes (4 test cases)

**Risk Level**: Low
- Simple configuration change
- Backward compatible
- No breaking changes

## Dependencies

None - standalone fix.

## Follow-up Tasks

1. Consider adding `.claude/specs/` to `.gitignore` (if migrating)
2. Document dual-location pattern in architecture docs
3. Add linting rule to detect new `.claude/specs/` usage
4. Monitor for any broken references after deployment

## Conclusion

The specs directory path issue is caused by incorrect priority order in `workflow-initialization.sh`. The fix is straightforward: reorder detection logic to prioritize `.opencode/specs`, change the default, and add warnings for legacy usage. No migration of existing specs is required, maintaining backward compatibility while establishing the correct standard for new work.

**Next Steps**: Implement Plan 074 to apply these fixes.
