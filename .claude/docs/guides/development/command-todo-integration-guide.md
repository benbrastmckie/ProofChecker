# Command-TODO Integration Guide

## Overview

This guide documents the signal-triggered delegation pattern for automatic TODO.md updates across commands that create or modify plans and reports. The pattern maintains separation of concerns by delegating all TODO.md generation logic to the `/todo` command while providing immediate visibility for newly created or modified artifacts.

**Key Principle**: Commands emit standardized signals when creating/modifying artifacts, then delegate to `/todo` for consistent TODO.md updates.

## Scope

Seven commands implement automatic TODO.md updates:

| Command | Trigger Points | Signal/Action | Section Transition |
|---------|---------------|---------------|-------------------|
| `/build` | START (after marking IN PROGRESS) | `update_plan_status()` | Not Started → In Progress |
| `/build` | COMPLETION (after marking COMPLETE) | `update_plan_status()` | In Progress → Completed |
| `/plan` | After plan creation | `PLAN_CREATED` signal | → Not Started |
| `/research` | After report creation | `REPORT_CREATED` signal | → Research Reports |
| `/debug` | After debug report creation | `DEBUG_REPORT_CREATED` signal | → Debug Reports |
| `/repair` | After repair plan creation | `PLAN_CREATED` signal | → Not Started |
| `/errors` | After error analysis report (report mode) | `trigger_todo_update()` | → Research Reports |
| `/revise` | After plan modification | `PLAN_REVISED` signal | Status unchanged |

## Signal-Triggered Delegation Pattern

All commands use the same standardized pattern for TODO.md updates:

### Pattern A: /plan Command (New Plan Creation)

```bash
# After plan file created and PLAN_CREATED signal emitted
echo "PLAN_CREATED: $PLAN_PATH"

# Delegate to /todo for TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

### Pattern B: /build Command at START (Status: → IN PROGRESS)

```bash
# After update_plan_status marks plan as IN PROGRESS
if update_plan_status "$PLAN_FILE" "IN PROGRESS" 2>/dev/null; then
  echo "Marked plan as [IN PROGRESS]"

  # Delegate to /todo for TODO.md update
  bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
  echo "✓ Updated TODO.md"
fi
```

### Pattern C: /build Command at COMPLETION (Status: → COMPLETE)

```bash
# After all phases complete and update_plan_status marks plan as COMPLETE
if check_all_phases_complete "$PLAN_FILE"; then
  update_plan_status "$PLAN_FILE" "COMPLETE" 2>/dev/null && \
    echo "Plan metadata status updated to [COMPLETE]"

  # Delegate to /todo for TODO.md update
  bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
  echo "✓ Updated TODO.md"
fi
```

### Pattern D: /research Command (Report Creation)

```bash
# After research report created and REPORT_CREATED signal emitted
echo "REPORT_CREATED: $REPORT_PATH"

# Delegate to /todo for TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

### Pattern E: /debug Command (Debug Report Creation)

```bash
# After debug report created and DEBUG_REPORT_CREATED signal emitted
echo "DEBUG_REPORT_CREATED: $DEBUG_REPORT_PATH"

# Delegate to /todo for TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

### Pattern F: /repair Command (Repair Plan Creation)

```bash
# After repair plan created and PLAN_CREATED signal emitted
echo "PLAN_CREATED: $REPAIR_PLAN_PATH"

# Delegate to /todo for TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

### Pattern G: /revise Command (Plan Modification)

```bash
# After plan revision complete and PLAN_REVISED signal emitted
echo "PLAN_REVISED: $EXISTING_PLAN_PATH"

# Delegate to /todo for TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

## Pattern Components

### 1. Signal Emission (Already Exists)

Commands already emit standardized signals with absolute paths:
- `PLAN_CREATED: /absolute/path/to/plan.md`
- `REPORT_CREATED: /absolute/path/to/report.md`
- `DEBUG_REPORT_CREATED: /absolute/path/to/debug_report.md`
- `PLAN_REVISED: /absolute/path/to/plan.md`

### 2. Delegation Call

```bash
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
```

**Components**:
- `bash -c "..."` - Subshell for isolation
- `cd "$CLAUDE_PROJECT_DIR"` - Change to project root (required for /todo command)
- `.claude/commands/todo.md` - Invoke /todo command
- `2>/dev/null` - Suppress output (Output Formatting Standards compliance)
- `|| true` - Graceful degradation (non-critical operation)

### 3. Checkpoint Output

```bash
echo "✓ Updated TODO.md"
```

Single line checkpoint after TODO.md update completes.

## Design Rationale

### Why Delegation?

**Separation of Concerns**:
- `/todo` remains single source of truth for TODO.md generation logic
- Commands only responsible for artifact creation, not TODO.md formatting
- Changes to TODO.md format only require updating `/todo`, not all commands

**Consistency**:
- All TODO.md updates use same classification/formatting logic
- Eliminates divergent implementations across commands
- Ensures uniform section placement and entry format

**Simplicity**:
- No new `/todo` features needed (full scan is fast: 2-3 seconds)
- No topic extraction or targeted update logic
- No file locking (single-user, sequential execution)
- Just 2-3 lines per integration point

**Maintainability**:
- Leverages existing, well-tested `todo-functions.sh` library
- Reduces surface area for bugs (one implementation)
- Easier to debug and extend

### Why Full Scan?

**Performance**:
- Full scan takes 2-3 seconds for 50 topics
- Acceptable overhead for signal-triggered updates
- User sees single checkpoint (non-blocking)

**Reliability**:
- TODO.md always reflects complete project state
- No risk of stale entries or missed artifacts
- No complex targeted update logic to debug

**Simplicity**:
- No topic name extraction from paths
- No incremental update logic
- No state management for partial updates

## Standards Compliance

This integration pattern aligns with project standards:

### Output Formatting Standards

From [Output Formatting Standards](/home/benjamin/.config/.claude/docs/reference/standards/output-formatting.md):
- Suppress `/todo` output with `2>/dev/null`
- Single checkpoint after operation: `✓ Updated TODO.md`
- No interim console output for background TODO update

### Command Authoring Standards

From [Command Authoring Standards](/home/benjamin/.config/.claude/docs/reference/standards/command-authoring.md):
- Block consolidation: Integration adds 2-3 lines per trigger point
- Checkpoint format: Single line summary per major operation
- Error handling: Graceful degradation with `|| true`

### TODO Organization Standards

From [TODO Organization Standards](/home/benjamin/.config/.claude/docs/reference/standards/todo-organization-standards.md):
- Delegates to `/todo` for section hierarchy and status classification
- Preserves Backlog and Saved sections (manual curation)
- Ensures consistent entry format and checkbox conventions

## Testing Approach

### Integration Tests

Verify TODO.md contains expected entries after command execution:

```bash
# Test /plan updates TODO.md (Pattern A)
rm .claude/TODO.md
/plan "test feature for todo integration"
grep -q "test feature for todo integration" .claude/TODO.md
grep -q "Not Started" .claude/TODO.md

# Test /build START updates TODO.md (Pattern B)
/build .claude/specs/*/plans/001-*.md
grep -q "In Progress" .claude/TODO.md

# Test /build COMPLETION updates TODO.md (Pattern C)
# After all phases complete
grep -q "Completed" .claude/TODO.md

# Test /research updates TODO.md (Pattern D)
/research "test research topic"
# Verify research reports reflected in TODO.md

# Test /revise updates TODO.md (Pattern G)
/revise "revise plan at .claude/specs/*/plans/001-*.md based on new insights"
# Verify plan modifications reflected in TODO.md
```

### Graceful Degradation Tests

Verify commands succeed even if `/todo` fails:

```bash
# Simulate /todo failure
mv .claude/commands/todo.md .claude/commands/todo.md.bak
/plan "test graceful degradation" || echo "FAIL: plan should succeed even if /todo fails"
mv .claude/commands/todo.md.bak .claude/commands/todo.md
```

### Section Transition Tests

Verify TODO.md section transitions during `/build` workflow:

```bash
# Verify transition: Not Started → In Progress → Completed
grep -A5 "## Not Started" .claude/TODO.md | grep -q "test_plan"  # Initially Not Started
/build .claude/specs/test_topic/plans/001-test_plan.md
grep -A5 "## In Progress" .claude/TODO.md | grep -q "test_plan"  # Now In Progress
# After completion
grep -A20 "## Completed" .claude/TODO.md | grep -q "test_plan"  # Now Completed
```

## Anti-Patterns

### Don't Implement Targeted/Incremental Updates

**Wrong**:
```bash
# Don't extract topic name and update specific entry
topic_name=$(extract_topic_from_path "$PLAN_PATH")
update_todo_entry "$topic_name" "In Progress"
```

**Right**:
```bash
# Delegate full scan to /todo
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
```

**Why**: Full scan is fast enough (2-3 seconds) and eliminates complex topic extraction logic.

### Don't Add Complex Error Handling

**Wrong**:
```bash
# Don't implement retry logic or error reporting
if ! bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md"; then
  echo "WARNING: TODO.md update failed, retrying..." >&2
  sleep 1
  bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" || log_error "TODO.md update failed"
fi
```

**Right**:
```bash
# Simple graceful degradation
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

**Why**: TODO.md updates are non-critical. User can manually run `/todo` if needed.

### Don't Modify todo-functions.sh

**Wrong**:
```bash
# Don't add new functions to todo-functions.sh for targeted updates
add_function_to_library() {
  echo "update_single_entry() { ... }" >> .claude/lib/todo/todo-functions.sh
}
```

**Right**:
```bash
# Reuse existing functions via /todo delegation
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
```

**Why**: Existing infrastructure is complete and well-tested. No modifications needed.

### Don't Add File Locking

**Wrong**:
```bash
# Don't implement lock files for concurrent access
flock /tmp/todo.lock bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md"
```

**Right**:
```bash
# Simple delegation without locking
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
```

**Why**: Single-user workflows make race conditions negligible. Lock complexity not justified.

## Implementation Checklist

When adding TODO.md updates to a command:

- [ ] Identify signal emission point or status transition action
- [ ] Add delegation call immediately after signal/action
- [ ] Use standardized pattern: `bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true`
- [ ] Add checkpoint output: `echo "✓ Updated TODO.md"`
- [ ] Suppress `/todo` output with `2>/dev/null`
- [ ] Test integration: verify TODO.md contains expected entry
- [ ] Test graceful degradation: verify command succeeds if `/todo` fails
- [ ] Update command documentation to note automatic TODO.md updates

## Performance Considerations

**Overhead per Command**:
- Delegation call: 2-3 seconds (full scan)
- Total command impact: <5% for typical workflows

**When to Optimize**:
- Only if user reports noticeable delays (unlikely)
- Profile first: measure actual impact before optimizing
- Consider targeted updates only if full scan exceeds 5 seconds

**Current Decision**:
- Full scan sufficient for all commands (fast enough)
- Premature optimization avoided (simplicity prioritized)

## Related Documentation

- [TODO Organization Standards](/home/benjamin/.config/.claude/docs/reference/standards/todo-organization-standards.md) - TODO.md structure, sections, status classification
- [Command Authoring Standards](/home/benjamin/.config/.claude/docs/reference/standards/command-authoring.md) - Block consolidation, checkpoint format
- [Output Formatting Standards](/home/benjamin/.config/.claude/docs/reference/standards/output-formatting.md) - Output suppression, console summaries
- [Command Reference](/home/benjamin/.config/.claude/docs/reference/standards/command-reference.md) - All commands with automatic TODO.md updates

## Examples

### Full /plan Integration

```bash
# In .claude/commands/plan.md, after plan creation:

# Create plan file
cat > "$PLAN_FILE" <<EOF
# Implementation Plan
...
EOF

# Emit signal
echo "PLAN_CREATED: $PLAN_FILE"

# Delegate TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"

# Continue with rest of command workflow
```

### Full /build Integration (Two Points)

```bash
# In .claude/commands/build.md, at START:

# Mark plan as IN PROGRESS
if update_plan_status "$PLAN_FILE" "IN PROGRESS" 2>/dev/null; then
  echo "Marked plan as [IN PROGRESS]"

  # Delegate TODO.md update
  bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
  echo "✓ Updated TODO.md"
fi

# Execute implementation phases...
# ...

# In .claude/commands/build.md, at COMPLETION:

# Check if all phases complete
if check_all_phases_complete "$PLAN_FILE"; then
  # Mark plan as COMPLETE
  update_plan_status "$PLAN_FILE" "COMPLETE" 2>/dev/null && \
    echo "Plan metadata status updated to [COMPLETE]"

  # Delegate TODO.md update
  bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
  echo "✓ Updated TODO.md"
fi
```

### Full /research Integration

```bash
# In .claude/commands/research.md, after report creation:

# Create research report
cat > "$REPORT_FILE" <<EOF
# Research Report
...
EOF

# Emit signal
echo "REPORT_CREATED: $REPORT_FILE"

# Delegate TODO.md update
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md" 2>/dev/null || true
echo "✓ Updated TODO.md"
```

## Troubleshooting

### TODO.md Not Updated After Command

**Symptoms**: Command completes successfully but TODO.md unchanged.

**Diagnosis**:
```bash
# Check if /todo command exists
test -f .claude/commands/todo.md && echo "EXISTS" || echo "MISSING"

# Check if delegation call present in command
grep -q "bash -c.*todo.md" .claude/commands/plan.md
```

**Solution**: Add delegation call after signal emission using standardized pattern.

### TODO.md Missing Entries

**Symptoms**: Some artifacts not appearing in TODO.md.

**Diagnosis**:
```bash
# Run /todo manually to see full scan output
.claude/commands/todo.md

# Check if artifact paths match expected structure
ls -la .claude/specs/*/plans/
ls -la .claude/specs/*/reports/
```

**Solution**: Verify artifact paths follow Directory Protocols. Run `/todo` manually to refresh.

### Command Fails After Adding Integration

**Symptoms**: Command exits with error after adding delegation call.

**Diagnosis**:
```bash
# Test delegation call in isolation
bash -c "cd \"$CLAUDE_PROJECT_DIR\" && .claude/commands/todo.md"
echo $?  # Should be 0 or ignored by || true
```

**Solution**: Ensure `|| true` appended for graceful degradation. Verify `CLAUDE_PROJECT_DIR` set.

## Summary

The signal-triggered delegation pattern provides:
- **Consistency**: All commands use same TODO.md generation logic
- **Simplicity**: 2-3 lines per integration point, no new infrastructure
- **Reliability**: Leverages well-tested `/todo` command and `todo-functions.sh`
- **Maintainability**: Single source of truth for TODO.md formatting
- **Performance**: Full scan fast enough for all use cases (2-3 seconds)

All seven commands (`/build`, `/plan`, `/research`, `/debug`, `/repair`, `/errors`, `/revise`) use identical delegation patterns, ensuring uniform behavior and easy maintenance.

## Helper Function: trigger_todo_update()

For simpler integration, commands can use the `trigger_todo_update()` helper function from `todo-functions.sh`:

```bash
source "${CLAUDE_PROJECT_DIR}/.claude/lib/todo/todo-functions.sh"

# After creating/modifying artifact
trigger_todo_update "repair plan created"
```

This function:
- Delegates to `/todo` command silently
- Outputs "✓ Updated TODO.md (reason)" on success
- Logs warning on failure but does not block the calling command (non-blocking)
- Follows the same delegation pattern as direct `bash -c` calls
