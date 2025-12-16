# Spec 074: .opencode System Independence

**Status**: Ready for Implementation
**Priority**: Critical
**Created**: 2025-12-15
**Estimated Effort**: 15-22 hours

## Quick Summary

This spec contains the complete plan to make the `.opencode/` system fully independent of `.claude/`, enabling eventual removal of the `.claude/` directory.

## Problem

The `.opencode/` system currently depends entirely on `.claude/` infrastructure:
- No libraries (all sourced from `.claude/lib/`)
- Specs created in wrong location (`.claude/specs/` instead of `.opencode/specs/`)
- Hundreds of hardcoded `.claude/` path references

## Solution

Multi-phase migration to copy all essential libraries to `.opencode/lib/`, update all path references, and establish `.opencode/` as the primary system.

## Documents

### Plans
- **[001-specs-directory-path-fix-plan.md](plans/001-specs-directory-path-fix-plan.md)** - Complete implementation plan with 7 phases

### Reports
- **[001-specs-directory-path-investigation.md](reports/001-specs-directory-path-investigation.md)** - Initial investigation of specs path issue
- **[002-opencode-independence-analysis.md](reports/002-opencode-independence-analysis.md)** - Comprehensive dependency analysis

## Implementation Phases

### Critical Path (12-17 hours)
1. **Phase 1**: Library Migration (4-6 hours) - Copy ~400K lines of shell libraries
2. **Phase 2**: Path References (2-3 hours) - Update all `.claude/` → `.opencode/` references
3. **Phase 3**: Command Files (2-3 hours) - Update all command source statements
4. **Phase 6**: Testing (4-5 hours) - Comprehensive validation

### High Priority (4-6 hours)
5. **Phase 4**: Agent Files (1-2 hours) - Update agent path references
6. **Phase 5**: Documentation (2-3 hours) - Update all docs and create migration guide

### Low Priority (Ongoing)
7. **Phase 7**: Deprecation (Ongoing) - Mark `.claude/` as deprecated, plan removal

## Key Changes

### Files to Create
- `.opencode/lib/` - Complete library system (~1.1M, 50+ files)
- `.opencode/docs/MIGRATION_FROM_CLAUDE.md` - User migration guide
- `.opencode/scripts/remove-claude-directory.sh` - Future cleanup script

### Files to Modify
- `.opencode/lib/workflow/workflow-initialization.sh` - Prioritize `.opencode/specs/`
- All `.opencode/command/*.md` - Update source statements
- All `.opencode/agent/**/*.md` - Update path references
- Documentation files - Update all `.claude/` references

### Files to Deprecate
- `.claude/lib/` - Keep as backup
- `.claude/specs/` - Keep as read-only legacy
- `.claude/commands/` - Keep as backup
- `.claude/agents/` - Keep as backup

## Success Criteria

- ✅ `.opencode/lib/` exists with all essential libraries
- ✅ New specs created in `.opencode/specs/` by default
- ✅ All commands source from `.opencode/lib/`
- ✅ All workflows execute without errors
- ✅ Legacy `.claude/specs/` accessible with warning
- ✅ Documentation updated
- ✅ Migration guide created

## Timeline

- **Week 1**: Phases 1-3 (library migration, path updates, command updates)
- **Week 2**: Phases 4-6 (agents, docs, testing)
- **Ongoing**: Phase 7 (deprecation, eventual removal)

## Next Steps

1. Review the complete plan: [plans/001-specs-directory-path-fix-plan.md](plans/001-specs-directory-path-fix-plan.md)
2. Create git commit before starting (for rollback)
3. Begin Phase 1: Library Migration
4. Test thoroughly after each phase
5. Update documentation as you go

## Rollback Plan

If issues arise:
```bash
# Immediate rollback
rm -rf .opencode/lib
git checkout .opencode/command/ .opencode/agent/
```

## Notes

- Backward compatibility maintained throughout
- `.claude/` kept as fallback during migration period
- Comprehensive testing required (8 test cases)
- Migration guide for users included
