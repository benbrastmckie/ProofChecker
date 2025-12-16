# Research Report: .opencode System Independence Analysis

**Date**: 2025-12-15
**Investigator**: General Agent
**Objective**: Analyze dependencies between `.opencode/` and `.claude/` systems to enable complete independence

## Executive Summary

The `.opencode/` system is currently heavily dependent on `.claude/` infrastructure, particularly:
- **Shell libraries** (~12,872 lines in `.claude/lib/core/` and `.claude/lib/workflow/`)
- **Specs directory** (46 legacy specs in `.claude/specs/`)
- **Commands** (18 commands in `.claude/commands/` vs 16 in `.opencode/command/`)
- **Agents** (32 agents in `.claude/agents/` vs 9 in `.opencode/agent/`)

**Recommendation**: Create a phased migration plan to copy essential libraries to `.opencode/lib/`, update all path references, and establish `.opencode/` as the primary system with `.claude/` as deprecated legacy.

## Current State Analysis

### Directory Structure Comparison

| Component | .claude/ | .opencode/ | Status |
|-----------|----------|------------|--------|
| **Commands** | 18 commands | 16 commands | Partial overlap |
| **Agents** | 32 agents | 9 agents | .opencode focused on LEAN 4 |
| **Libraries** | 1.1M (core + workflow) | 0 bytes | **Complete dependency** |
| **Specs** | 4.8M (46 specs) | ~100K (1 spec) | Legacy in .claude |
| **Context** | Minimal | Rich LEAN 4 context | .opencode is primary |
| **Documentation** | Scattered | Organized in docs/ | .opencode is better |

### Critical Dependencies

#### 1. Shell Libraries (.claude/lib/)

**Core Libraries** (12 files, essential):
- `error-handling.sh` (75,927 lines) - Error logging, trapping, diagnostics
- `state-persistence.sh` (44,957 lines) - Workflow state management
- `unified-location-detection.sh` (26,793 lines) - Project/topic detection
- `unified-logger.sh` (21,695 lines) - Structured logging
- `library-version-check.sh` (6,538 lines) - Dependency validation
- `detect-project-dir.sh` (1,540 lines) - Project root detection
- `summary-formatting.sh` (2,320 lines) - Console output formatting
- `timestamp-utils.sh` (3,087 lines) - Timestamp generation
- `base-utils.sh` (1,532 lines) - Basic utilities
- `library-sourcing.sh` (3,974 lines) - Library loading
- `source-libraries.sh` (2,803 lines) - Library sourcing
- `source-libraries-inline.sh` (5,434 lines) - Inline sourcing

**Workflow Libraries** (13 files, essential):
- `workflow-state-machine.sh` (46,286 lines) - State machine implementation
- `workflow-initialization.sh` (42,087 lines) - Path initialization (THE KEY FILE)
- `checkpoint-utils.sh` (42,364 lines) - Checkpoint management
- `validation-utils.sh` (20,958 lines) - Validation helpers
- `metadata-extraction.sh` (19,886 lines) - Metadata parsing
- `workflow-llm-classifier.sh` (25,026 lines) - LLM classification
- `context-pruning.sh` (15,218 lines) - Context optimization
- `workflow-scope-detection.sh` (6,420 lines) - Scope detection
- `barrier-utils.sh` (5,908 lines) - Hard barrier pattern
- `argument-capture.sh` (6,711 lines) - Argument parsing
- `workflow-bootstrap.sh` (3,381 lines) - Bootstrap logic
- `workflow-detection.sh` (2,981 lines) - Workflow detection
- `workflow-init.sh` (16,000 lines) - Initialization

**Total**: ~400,000 lines of critical infrastructure

**Other Libraries** (plan/, todo/, artifact/, convert/, lean/):
- `plan/` - 8 files for plan management
- `todo/` - 1 file for TODO management
- `artifact/` - 5 files for artifact creation
- `convert/` - 5 files for document conversion
- `lean/` - 1 file for LEAN phase classification

#### 2. Command Dependencies

**Commands using .claude/lib/** (100+ source statements found):
- `/research` - Sources 7 libraries from .claude/lib
- `/create-plan` - Sources 8+ libraries
- `/todo` - Sources 3 libraries
- `/revise` - Sources 5+ libraries
- `/repair` - Sources 6+ libraries
- `/setup` - Sources 2 libraries
- All other commands have similar dependencies

**Pattern**: Every command in `.claude/commands/` sources libraries from `.claude/lib/`

#### 3. Specs Directory Usage

**Current State**:
- `.claude/specs/`: 46 spec directories (4.8M)
- `.opencode/specs/`: 1 spec directory (073_lake_lint_enhancements)

**References to .claude/specs** in .opencode files:
- `lake-lint-phase5-implementation-summary.md` - 15 references
- `lake-lint-integration.md` - 5 references
- Other spec files reference `.claude/specs/` paths

#### 4. Agent Dependencies

**Agent Distribution**:
- `.claude/agents/`: 32 agents (research-coordinator, plan-architect, etc.)
- `.opencode/agent/`: 9 agents (orchestrator, researcher, planner, etc.)

**Overlap**: Some agents exist in both locations with different implementations

### .opencode System Strengths

**What .opencode has that .claude doesn't**:

1. **Rich Context System** (`.opencode/context/`):
   - LEAN 4 domain knowledge
   - Theorem proving guidelines
   - Style guides and templates
   - Process documentation
   - Well-organized, hierarchical structure

2. **Better Documentation** (`.opencode/docs/`):
   - System overview
   - Architecture guide
   - Agents guide
   - Commands reference
   - Context management guide
   - Workflows guide
   - Testing guide

3. **Focused Mission**: LEAN 4 development suite vs general-purpose

4. **Cleaner Structure**: More organized, less legacy cruft

### Migration Challenges

#### Challenge 1: Library Size and Complexity

**Problem**: ~400,000 lines of shell code in `.claude/lib/`

**Options**:
1. **Copy all libraries** to `.opencode/lib/` (simple but bloated)
2. **Extract only essential libraries** (complex but cleaner)
3. **Refactor and simplify** (ideal but time-consuming)

**Recommendation**: Option 1 (copy all) for Phase 1, then Option 3 (refactor) in Phase 2

#### Challenge 2: Path References

**Problem**: Hundreds of hardcoded `.claude/` paths in:
- Command files (100+ source statements)
- Library files (cross-references)
- Agent files (path references)
- Documentation (examples)

**Solution**: Systematic find-and-replace with validation

#### Challenge 3: Backward Compatibility

**Problem**: Existing workflows may depend on `.claude/` structure

**Solution**: 
- Keep `.claude/` as deprecated legacy (read-only)
- Add warnings when using legacy paths
- Document migration path for users

#### Challenge 4: Testing

**Problem**: No test suite for library migration

**Solution**: 
- Create integration tests for critical workflows
- Test each command after migration
- Validate state persistence across migration

## Findings

### Finding 1: Complete Library Dependency

**Evidence**: `.opencode/lib/` does not exist, all commands source from `.claude/lib/`

**Impact**: .opencode cannot function independently

**Severity**: Critical

### Finding 2: Specs Directory Split

**Evidence**: 46 specs in `.claude/specs/`, 1 in `.opencode/specs/`

**Impact**: Confusion about where to create new specs

**Severity**: High

### Finding 3: Command Duplication

**Evidence**: 
- `.claude/commands/research.md` (982 lines)
- `.opencode/command/research.md` (42 lines)

**Impact**: Inconsistent behavior, maintenance burden

**Severity**: Medium

### Finding 4: Agent Duplication

**Evidence**: Some agents exist in both locations

**Impact**: Unclear which agent is authoritative

**Severity**: Medium

### Finding 5: Context System is .opencode-only

**Evidence**: Rich context in `.opencode/context/`, minimal in `.claude/`

**Impact**: .opencode has better domain knowledge

**Severity**: Low (positive finding)

## Recommendations

### Phase 1: Library Migration (Critical)

**Objective**: Make `.opencode/` self-sufficient

**Actions**:
1. Create `.opencode/lib/` directory structure
2. Copy all libraries from `.claude/lib/` to `.opencode/lib/`
3. Update all source statements in `.opencode/command/` files
4. Update all source statements in `.opencode/agent/` files
5. Test each command after migration

**Estimated Effort**: 4-6 hours

**Files to Create**:
```
.opencode/lib/
├── core/
│   ├── error-handling.sh
│   ├── state-persistence.sh
│   ├── unified-location-detection.sh
│   ├── unified-logger.sh
│   ├── library-version-check.sh
│   ├── detect-project-dir.sh
│   ├── summary-formatting.sh
│   ├── timestamp-utils.sh
│   ├── base-utils.sh
│   ├── library-sourcing.sh
│   ├── source-libraries.sh
│   └── source-libraries-inline.sh
├── workflow/
│   ├── workflow-state-machine.sh
│   ├── workflow-initialization.sh (KEY FILE - update specs path here)
│   ├── checkpoint-utils.sh
│   ├── validation-utils.sh
│   ├── metadata-extraction.sh
│   ├── workflow-llm-classifier.sh
│   ├── context-pruning.sh
│   ├── workflow-scope-detection.sh
│   ├── barrier-utils.sh
│   ├── argument-capture.sh
│   ├── workflow-bootstrap.sh
│   ├── workflow-detection.sh
│   └── workflow-init.sh
├── plan/
│   └── (8 files)
├── todo/
│   └── todo-functions.sh
├── artifact/
│   └── (5 files)
└── README.md
```

### Phase 2: Path Reference Updates (Critical)

**Objective**: Update all `.claude/` references to `.opencode/`

**Actions**:
1. Update `workflow-initialization.sh` to prioritize `.opencode/specs/`
2. Update all command files to source from `.opencode/lib/`
3. Update all agent files to reference `.opencode/` paths
4. Update documentation to reference `.opencode/` paths
5. Add deprecation warnings for `.claude/` usage

**Estimated Effort**: 2-3 hours

**Key Changes**:
- `workflow-initialization.sh:463-471` - Prioritize `.opencode/specs/`
- All command files - Replace `.claude/lib/` with `.opencode/lib/`
- All agent files - Replace `.claude/` paths with `.opencode/`
- Documentation - Update all examples

### Phase 3: Specs Migration Strategy (High)

**Objective**: Establish `.opencode/specs/` as primary location

**Options**:

**Option A: Leave Legacy in Place (Recommended)**
- Keep 46 specs in `.claude/specs/` (read-only)
- All new specs go to `.opencode/specs/`
- Add warning when accessing `.claude/specs/`
- **Pros**: Safe, no breaking changes
- **Cons**: Two locations to check

**Option B: Migrate All Specs**
- Move all 46 specs to `.opencode/specs/`
- Create symlinks for backward compatibility
- Update all references
- **Pros**: Single source of truth
- **Cons**: Risk of breaking references, complex

**Recommendation**: Option A for safety

### Phase 4: Command Consolidation (Medium)

**Objective**: Resolve command duplication

**Actions**:
1. Identify overlapping commands (research, implement, test, etc.)
2. Choose authoritative version (prefer `.opencode/` for LEAN 4)
3. Deprecate `.claude/` versions
4. Document migration path

**Estimated Effort**: 3-4 hours

### Phase 5: Agent Consolidation (Medium)

**Objective**: Resolve agent duplication

**Actions**:
1. Identify overlapping agents
2. Choose authoritative version
3. Deprecate duplicates
4. Update routing logic

**Estimated Effort**: 2-3 hours

### Phase 6: Testing and Validation (Critical)

**Objective**: Ensure no regressions

**Actions**:
1. Create integration test suite
2. Test each command in `.opencode/`
3. Test state persistence
4. Test specs creation
5. Test library loading
6. Validate error handling

**Estimated Effort**: 4-5 hours

**Test Cases**:
- `/research "test topic"` - Verify spec created in `.opencode/specs/`
- `/prove "test theorem"` - Verify full workflow
- State persistence across bash blocks
- Library version checking
- Error logging and recovery
- Checkpoint creation and restoration

### Phase 7: Documentation Updates (High)

**Objective**: Update all documentation

**Actions**:
1. Update CLAUDE.md to reference `.opencode/`
2. Update all README files
3. Update MAINTENANCE.md files
4. Update TODO.md
5. Create migration guide for users
6. Document deprecation timeline for `.claude/`

**Estimated Effort**: 2-3 hours

### Phase 8: Deprecation Plan (Low Priority)

**Objective**: Plan eventual removal of `.claude/`

**Timeline**:
- **Month 1**: Complete Phases 1-7, announce deprecation
- **Month 2-3**: Monitor for issues, fix bugs
- **Month 4**: Add stronger warnings for `.claude/` usage
- **Month 5-6**: Final migration of any remaining dependencies
- **Month 7**: Remove `.claude/` directory (optional)

**Rollback Plan**: Keep `.claude/` as backup for 6 months

## Implementation Complexity

### Total Estimated Effort

| Phase | Effort | Priority |
|-------|--------|----------|
| Phase 1: Library Migration | 4-6 hours | Critical |
| Phase 2: Path Updates | 2-3 hours | Critical |
| Phase 3: Specs Strategy | 1 hour | High |
| Phase 4: Command Consolidation | 3-4 hours | Medium |
| Phase 5: Agent Consolidation | 2-3 hours | Medium |
| Phase 6: Testing | 4-5 hours | Critical |
| Phase 7: Documentation | 2-3 hours | High |
| Phase 8: Deprecation | Ongoing | Low |
| **Total** | **18-27 hours** | - |

### Risk Assessment

**High Risk Areas**:
1. Library migration (400K lines of code)
2. State persistence (complex bash arrays)
3. Path references (hundreds of locations)
4. Backward compatibility (existing workflows)

**Mitigation**:
- Incremental migration (one library at a time)
- Comprehensive testing after each phase
- Keep `.claude/` as fallback
- Document all changes

**Low Risk Areas**:
1. Context system (already in `.opencode/`)
2. Documentation (straightforward updates)
3. Specs strategy (leave legacy in place)

## Conclusion

Making `.opencode/` independent of `.claude/` is feasible but requires systematic migration of ~400,000 lines of shell libraries and hundreds of path references. The recommended approach is:

1. **Phase 1-2** (Critical): Copy libraries and update paths (6-9 hours)
2. **Phase 3** (High): Establish `.opencode/specs/` as primary (1 hour)
3. **Phase 6** (Critical): Test thoroughly (4-5 hours)
4. **Phase 7** (High): Update documentation (2-3 hours)
5. **Phases 4-5, 8** (Medium/Low): Consolidate and deprecate over time

**Total Critical Path**: ~13-18 hours for core independence

**Key Success Factors**:
- Systematic approach (one phase at a time)
- Comprehensive testing (no regressions)
- Backward compatibility (keep `.claude/` as fallback)
- Clear documentation (migration guide for users)

**Next Steps**: Revise Plan 074 to include full library migration strategy.
