# Lean Plan Command Guide

## Overview

The `/lean-plan` command creates Lean-specific implementation plans for theorem proving projects with theorem-level granularity, Mathlib research, proof strategies, and dependency tracking.

**When to Use**:
- Planning Lean 4 formalization projects
- Designing theorem proving workflows
- Structuring large proof developments
- Preparing for wave-based parallel proving with `/lean`

**When NOT to Use**:
- General software implementation (use `/plan` instead)
- Single theorem proving (use `/lean` directly)
- Non-Lean programming tasks

---

## Syntax

```bash
/lean-plan "<feature-description>" [--file <path>] [--complexity 1-4] [--project <path>]
```

### Arguments

- **`<feature-description>`** (required): Natural language description of formalization goal
  - Example: `"formalize group homomorphism properties"`
  - Example: `"prove basic arithmetic commutativity theorems"`

- **`--file <path>`** (optional): Path to file with detailed formalization prompt
  - Use when formalization description is too long for command line
  - File content replaces `<feature-description>`
  - Path can be absolute or relative to current directory

- **`--complexity 1-4`** (optional, default: 3): Research depth level
  - **1** (Quick): Minimal Mathlib search, 2-3 namespaces
  - **2** (Standard): 5-7 namespaces, basic WebSearch
  - **3** (Deep): 10+ namespaces, comprehensive documentation search
  - **4** (Exhaustive): Full Mathlib survey, advanced pattern analysis

- **`--project <path>`** (optional): Explicit Lean project path
  - Auto-detected if omitted (searches for `lakefile.toml` upward from cwd)
  - Use when working outside project directory
  - Path can be absolute or relative

---

## Usage Examples

### Example 1: Basic Usage

```bash
cd ~/ProofChecker
/lean-plan "formalize basic arithmetic commutativity theorems"
```

**Result**:
- Auto-detects Lean project in current directory
- Creates research reports with Mathlib theorem discoveries
- Creates implementation plan with theorem specifications
- Default complexity level 3 (deep research)

### Example 2: Using `--file` Flag (Long Prompt)

```bash
# Create detailed prompt file
cat > formalization-spec.md <<EOF
# Group Homomorphism Formalization

Formalize the following theorems about group homomorphisms:

1. Identity preservation: f(0) = 0
2. Operation preservation: f(a + b) = f(a) + f(b)
3. Inverse preservation: f(-a) = -f(a)
4. Kernel properties

Include proofs that compose and relate these properties.
EOF

/lean-plan --file formalization-spec.md --complexity 3
```

**Result**:
- Reads detailed prompt from file
- Archives prompt file in `specs/NNN_topic/prompts/`
- Creates comprehensive research reports
- Creates plan with dependency tracking for related theorems

### Example 3: Using `--project` Flag (Explicit Project)

```bash
# Working from different directory
cd ~/Documents
/lean-plan "prove list reversal properties" --project ~/ProofChecker
```

**Result**:
- Uses Lean project at `~/ProofChecker` (not current directory)
- Searches for existing proofs in that project
- Creates specs in `.claude/specs/` within ProofChecker project

### Example 4: Using `--complexity` Flag

```bash
# Quick plan for simple theorems (complexity 2)
/lean-plan "prove Nat.add_comm using Mathlib" --complexity 2

# Exhaustive research for complex formalization (complexity 4)
/lean-plan "formalize category theory functors" --complexity 4
```

**Result (complexity 2)**:
- Quick Mathlib search (5-7 namespaces)
- Faster planning (2-3 minutes)

**Result (complexity 4)**:
- Comprehensive Mathlib survey
- Deep pattern analysis
- Longer planning (10-15 minutes)

### Example 5: Complete Workflow (Plan → Execute)

```bash
# Step 1: Create plan
/lean-plan "formalize ring homomorphism theorems" --complexity 3

# Step 2: Review plan
cat .claude/specs/*/plans/*.md

# Step 3: Execute plan with /lean
/lean .claude/specs/*/plans/*.md --prove-all

# Step 4: Iterate if needed
/lean .claude/specs/*/plans/*.md --max-iterations=5
```

---

## Integration with /lean Workflow

The `/lean-plan` command is designed to integrate seamlessly with the `/lean` execution command:

### Planning Phase: `/lean-plan`

**Responsibilities**:
1. Mathlib theorem discovery (via lean-research-specialist)
2. Proof pattern analysis
3. Theorem dependency graph generation
4. Proof strategy formulation
5. Wave structure creation for parallel proving

**Outputs**:
- Research reports in `specs/NNN_topic/reports/`
- Implementation plan in `specs/NNN_topic/plans/`
- Theorem specifications with Goals, Strategies, Complexity

### Execution Phase: `/lean`

**Responsibilities**:
1. Tier 1 discovery: Read **Lean File** metadata from plan
2. Wave-based orchestration: Parse phase dependencies
3. Parallel proving: Execute independent theorems concurrently (40-60% time savings)
4. Progress tracking: Update `[NOT STARTED]` → `[IN PROGRESS]` → `[COMPLETE]`

**Input**: Plan file created by `/lean-plan`

**Execution**:
```bash
# Prove all theorems in plan
/lean path/to/plan.md --prove-all

# Verify only (no new proofs)
/lean path/to/plan.md --verify

# Iterate with retries
/lean path/to/plan.md --max-attempts=3 --max-iterations=5
```

---

## Plan Format Explanation

### Metadata Section

Plans created by `/lean-plan` include standard metadata plus Lean-specific fields:

```markdown
## Metadata
- **Date**: 2025-12-03
- **Feature**: Formalize group homomorphism properties
- **Status**: [NOT STARTED]
- **Estimated Hours**: 8-12 hours
- **Standards File**: /home/user/project/CLAUDE.md
- **Research Reports**:
  - [Mathlib Research](../reports/001-mathlib-research.md)
  - [Proof Patterns](../reports/002-proof-patterns.md)
- **Lean File**: /home/user/ProofChecker/ProofChecker/GroupHom.lean
- **Lean Project**: /home/user/ProofChecker/
```

**Lean-Specific Fields**:
- **Lean File**: Absolute path to target .lean file (enables Tier 1 discovery in `/lean`)
- **Lean Project**: Absolute path to Lean project root (lakefile.toml location)

### Theorem Phase Structure

Each phase represents one or more theorems with specifications:

```markdown
### Phase 1: Identity Preservation [NOT STARTED]
dependencies: []

**Objective**: Prove group homomorphisms preserve identity element

**Complexity**: Low

**Theorems**:
- [ ] `theorem_hom_preserves_zero`: Prove f(0) = 0 for group homomorphisms
  - Goal: `∀ (f : G → H), IsGroupHom f → f 0 = 0`
  - Strategy: Use `GroupHom.map_zero` from Mathlib via `exact` tactic
  - Complexity: Simple (direct application)
  - Estimated: 0.5 hours

**Testing**:
```bash
lake build
grep -c "sorry" ProofChecker/GroupHom.lean
```

**Expected Duration**: 0.5 hours

---
```

**Key Components**:
- **Goal**: Formal Lean 4 type signature (what to prove)
- **Strategy**: Proof approach with specific tactics and Mathlib theorems
- **Complexity**: Simple/Medium/Complex effort estimate
- **Dependencies**: Phase prerequisite tracking for wave execution

### Dependency Syntax

Phase dependencies enable wave-based parallel execution:

```markdown
### Phase 1: Basic Properties [NOT STARTED]
dependencies: []

### Phase 2: Derived Properties [NOT STARTED]
dependencies: [1]  # Depends on Phase 1

### Phase 3: Composition [NOT STARTED]
dependencies: [1, 2]  # Depends on both Phases 1 and 2
```

**Wave Execution**:
- **Wave 1**: Phase 1 (no dependencies)
- **Wave 2**: Phase 2 (depends on Wave 1 completion)
- **Wave 3**: Phase 3 (depends on Waves 1 and 2 completion)

Phases within same wave execute in parallel for 40-60% time savings.

---

## Troubleshooting

### Error: No Lean project found

**Symptom**:
```
ERROR: No Lean project found
No lakefile.toml detected in current directory or parent directories
Use --project flag to specify Lean project path
```

**Cause**: Not in a Lean project directory and no `--project` flag

**Solutions**:
1. Change to project directory: `cd ~/ProofChecker`
2. Use `--project` flag: `/lean-plan "formalize theorems" --project ~/ProofChecker`
3. Create Lean project: `lake init ProofChecker`

### Error: Invalid Lean project structure

**Symptom**:
```
ERROR: Invalid Lean project structure: /path/to/project
No lakefile.toml or lakefile.lean found in project directory
```

**Cause**: Specified path is not a valid Lean project

**Solutions**:
1. Verify path: `ls /path/to/project/lakefile.toml`
2. Initialize project: `cd /path/to/project && lake init`

### Warning: Plan missing **Lean File** metadata

**Symptom**:
```
WARNING: Plan missing **Lean File** metadata (Tier 1 discovery will fail)
```

**Cause**: lean-plan-architect didn't include **Lean File** field in metadata

**Impact**: `/lean` command will fall back to Tier 2 discovery (slower)

**Solutions**:
1. Manually add to plan:
   ```markdown
   - **Lean File**: /absolute/path/to/file.lean
   ```
2. Re-run `/lean-plan` to regenerate plan

### Error: Circular dependencies detected

**Symptom**:
```
ERROR: Circular theorem dependencies detected
Phase 2 depends on Phase 3 which depends on Phase 2
```

**Cause**: Plan has circular phase dependencies

**Impact**: Wave-based execution cannot determine order

**Solutions**:
1. Review dependency structure in plan
2. Break dependency cycle by reordering theorems
3. Manually edit plan to fix `dependencies:` fields

### Warning: Not all theorems have goal specifications

**Symptom**:
```
WARNING: Not all theorems have goal specifications (5/8)
```

**Cause**: Some theorems missing `- Goal:` field

**Impact**: `/lean` cannot generate formal Lean types for proving

**Solutions**:
1. Manually add goal specifications:
   ```markdown
   - [ ] `theorem_name`: Description
     - Goal: `∀ a b : Nat, a + b = b + a`
   ```
2. Re-run `/lean-plan` with higher complexity for better specifications

### Research phase failures

**Symptom**:
```
ERROR: Research phase failed to create report files
```

**Cause**: lean-research-specialist agent encountered errors

**Solutions**:
1. Check error log: `/errors --command /lean-plan --type agent_error --limit 5`
2. Verify Lean project structure
3. Re-run with lower complexity: `/lean-plan "..." --complexity 2`
4. Check network connectivity (WebSearch failures)

### Empty or incomplete research reports

**Symptom**:
```
ERROR: Research report(s) too small (< 100 bytes)
```

**Cause**: Mathlib search failed or agent error

**Solutions**:
1. Check agent output for errors
2. Try higher complexity level for deeper research
3. Manually add Mathlib references to research reports

---

## Advanced Usage

### Custom Lean Style Guide Integration

If your project has `LEAN_STYLE_GUIDE.md`, it's automatically extracted and provided to lean-plan-architect:

```bash
# Create style guide in Lean project root
cat > ~/ProofChecker/LEAN_STYLE_GUIDE.md <<EOF
# Lean Style Guide

## Theorem Naming
- Use snake_case: theorem_add_comm
- Include operation: theorem_mul_assoc
- Include property: theorem_distributivity

## Proof Style
- Use exact for direct applications
- Prefer simp over manual rewrites
- Document complex tactics
EOF

# Run /lean-plan (style guide automatically used)
/lean-plan "formalize theorems" --project ~/ProofChecker
```

### Multi-File Formalization

For large formalizations spanning multiple Lean files, plan one file at a time:

```bash
# File 1: Basic properties
/lean-plan "formalize basic group properties in Groups/Basic.lean" --complexity 3

# File 2: Homomorphisms (depends on Basic)
/lean-plan "formalize group homomorphisms in Groups/Hom.lean" --complexity 3

# File 3: Quotients (depends on both)
/lean-plan "formalize quotient groups in Groups/Quotient.lean" --complexity 4
```

Each plan includes **Lean File** metadata pointing to different files.

### Incremental Planning

Start with low complexity, iterate with higher complexity:

```bash
# Quick initial plan (complexity 2)
/lean-plan "formalize ring theorems" --complexity 2

# Review plan
cat .claude/specs/*/plans/*.md

# If more detail needed, revise with higher complexity
/revise .claude/specs/*/plans/*.md "Add more Mathlib references and proof strategies" --complexity 4
```

---

## See Also

- [Lean Command Guide](.claude/docs/guides/commands/lean-command-guide.md) - Executing Lean plans
- [Plan Command Guide](.claude/docs/guides/commands/plan-command-guide.md) - General planning workflow
- [Lean Infrastructure Research](.claude/specs/032_lean_plan_command/reports/001-lean-infrastructure-research.md) - Lean planning research
- [Blueprint Methodology](https://leanprover-community.github.io/blueprint/) - Theorem-level formalization approach
