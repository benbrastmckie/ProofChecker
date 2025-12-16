# Implementer Agent Subagent Optimization Plan

**Status**: Proposed  
**Priority**: High  
**Estimated Effort**: 4-6 hours  
**Impact**: 60-80% context window reduction for primary agent  

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Problem Statement](#problem-statement)
3. [Current Architecture Analysis](#current-architecture-analysis)
4. [Root Cause Analysis](#root-cause-analysis)
5. [Proposed Solution](#proposed-solution)
6. [Implementation Phases](#implementation-phases)
7. [Detailed Changes](#detailed-changes)
8. [Testing Strategy](#testing-strategy)
9. [Success Metrics](#success-metrics)
10. [Rollback Plan](#rollback-plan)
11. [References](#references)

---

## Executive Summary

### The Problem

The Implementer agent is consuming excessive context window space because it's doing all implementation work directly instead of properly delegating to its specialized subagents (`tactic-selector`, `code-generator`, `lean-linter`).

### The Solution

Refactor the Implementer agent to:
1. Explicitly enable the `task` tool for delegation
2. Add clear instructions to use subagents via the `task` tool
3. Fix subagent routing paths to use correct OpenCode conventions
4. Optimize subagent output formats for clean integration

### Expected Outcome

- **60-80% reduction** in Implementer agent context window usage
- **Faster execution** due to smaller context per agent
- **Better code quality** through specialist subagents
- **Improved scalability** for complex proofs

---

## Problem Statement

### Current Behavior

When the `/implement` command is invoked or the Implementer agent is used:

1. The Implementer agent loads all context:
   - Full proof plan
   - All LEAN 4 tactic knowledge
   - Code generation patterns
   - Linting rules
   - Style guidelines

2. The Implementer does all work itself:
   - Selects tactics manually
   - Generates code manually
   - Performs linting manually

3. Context window fills up quickly:
   - Estimated 15,000+ tokens per invocation
   - Limits ability to handle complex proofs
   - Slower LLM processing

### Desired Behavior

The Implementer should act as a **manager/orchestrator**:

1. Receive proof plan
2. Delegate tactic selection to `@tactic-selector` (Level 1 context)
3. Delegate code generation to `@code-generator` (Level 1 context)
4. Delegate linting to `@lean-linter` (Level 2 context)
5. Coordinate results and return final output

Each subagent uses minimal, focused context:
- Implementer: ~3,000 tokens (coordination only)
- Tactic Selector: ~1,000 tokens (tactic mapping)
- Code Generator: ~1,000 tokens (code writing)
- Lean Linter: ~2,000 tokens (linting rules)

**Total distributed**: ~7,000 tokens across 4 agents  
**Primary agent savings**: 80% reduction

---

## Current Architecture Analysis

### File Structure

```
.opencode/agent/
├── implementer.md                           # Primary manager agent
└── subagents/
    └── implementer/
        ├── tactic-selector.md               # Tactic selection specialist
        ├── code-generator.md                # Code generation specialist
        └── lean-linter.md                   # Linting specialist
```

### Current Implementer Agent Configuration

**File**: `.opencode/agent/implementer.md`

**Frontmatter**:
```yaml
---
description: "Manages a team of subagents to write, lint, and verify LEAN 4 code"
mode: primary
temperature: 0.1
# NOTE: 'task' tool not explicitly enabled
---
```

**Routing Section** (lines 133-154):
```markdown
<routing_intelligence>
  <execute_routing>
    <route to="@tactic-selector" when="...">
      <context_level>Level 1</context_level>
      <pass_data>...</pass_data>
      <expected_return>...</expected_return>
    </route>
    <route to="@code-generator" when="...">
      <context_level>Level 1</context_level>
      <pass_data>...</pass_data>
      <expected_return>...</expected_return>
    </route>
    <route to="@lean-linter" when="...">
      <context_level>Level 2</context_level>
      <pass_data>...</pass_data>
      <expected_return>...</expected_return>
    </route>
  </execute_routing>
</routing_intelligence>
```

### Issues Identified

1. **Missing Explicit Task Tool Permission**
   - `task: true` not in frontmatter
   - May be implicitly available, but not guaranteed

2. **Routing Paths May Be Incorrect**
   - Uses `@tactic-selector` pattern
   - Should use `subagents/implementer/tactic-selector` per OpenCode docs

3. **No Explicit Task Tool Invocation Instructions**
   - Workflow describes WHAT to do
   - Doesn't explicitly say HOW (use `task` tool)
   - LLM may interpret as "do it yourself" instead of "delegate"

4. **Workflow Section Lacks Tool Usage Examples**
   - Lines 85-100 describe process
   - Don't show actual `task()` tool calls
   - Ambiguous whether to delegate or execute directly

---

## Root Cause Analysis

### Why the Implementer Isn't Delegating

Based on OpenCode documentation and agent analysis:

1. **Implicit vs Explicit Tool Usage**
   - The `task` tool may be available but not explicitly enabled
   - Without explicit `task: true`, the agent may not know it can delegate

2. **Ambiguous Instructions**
   - Current workflow says "delegate to @tactic-selector"
   - Doesn't explicitly say "use the task tool to invoke..."
   - LLM interprets this as a suggestion, not a requirement

3. **Missing Tool Call Examples**
   - No concrete examples of `task()` invocations
   - LLM doesn't know the exact syntax to use
   - Falls back to doing work itself

4. **Routing Path Confusion**
   - `@tactic-selector` may not resolve correctly
   - Should be `subagents/implementer/tactic-selector`
   - Incorrect path = failed delegation = fallback to self-execution

### Evidence from OpenCode Documentation

From https://opencode.ai/docs/agents/:

> **Subagents can be invoked:**
> - Automatically by primary agents for specialized tasks based on their descriptions.
> - Manually by @ mentioning a subagent in your message.

From the Creating Subagents guide:

> **Agent name = file path from `agent/` directory (minus `.md`)**
> 
> Examples:
> - File: `.opencode/agent/subagents/core/task-manager.md`
>   - Name: `subagents/core/task-manager`

**Conclusion**: The routing should use full paths, not `@` shortcuts.

---

## Proposed Solution

### Three-Pronged Approach

#### 1. Enable Task Tool Explicitly

Add `task: true` to Implementer frontmatter:

```yaml
---
description: "Manages a team of subagents to write, lint, and verify LEAN 4 code"
mode: primary
temperature: 0.1
tools:
  task: true      # ← ADD THIS
  read: true
  write: true
  edit: true
  bash: false
---
```

#### 2. Fix Subagent Routing Paths

Update routing section to use correct paths:

```markdown
<routing_intelligence>
  <execute_routing>
    <route to="subagents/implementer/tactic-selector" when="...">
      <!-- Changed from @tactic-selector -->
    </route>
    <route to="subagents/implementer/code-generator" when="...">
      <!-- Changed from @code-generator -->
    </route>
    <route to="subagents/implementer/lean-linter" when="...">
      <!-- Changed from @lean-linter -->
    </route>
  </execute_routing>
</routing_intelligence>
```

#### 3. Add Explicit Task Tool Instructions

Update workflow section with concrete examples:

```markdown
<workflow_execution>
  <stage id="2" name="TacticalImplementation">
    <action>Implement each step using specialized subagents</action>
    <process>
      1. For each step in the proof plan:
         
         a. **INVOKE TACTIC SELECTOR** using the task tool:
            ```
            task(
              subagent_type="subagents/implementer/tactic-selector",
              description="Select LEAN 4 tactic for proof step",
              prompt="Given step description: '{step_description}' and proof state: '{proof_state}', 
                      return the appropriate LEAN 4 tactic string."
            )
            ```
         
         b. **INVOKE CODE GENERATOR** using the task tool:
            ```
            task(
              subagent_type="subagents/implementer/code-generator",
              description="Generate LEAN 4 code line",
              prompt="Generate LEAN 4 code using tactic: '{tactic}' in context: '{proof_context}'"
            )
            ```
         
         c. Validate the generated line compiles
         d. If compilation fails, STOP and report error
         e. If compilation succeeds, proceed to next step
      
      2. After all steps complete, **INVOKE LINTER** using the task tool:
         ```
         task(
           subagent_type="subagents/implementer/lean-linter",
           description="Lint generated LEAN 4 code",
           prompt="Lint this LEAN 4 file and return suggestions: {file_content}"
         )
         ```
    </process>
    <checkpoint>All proof steps implemented via subagent delegation</checkpoint>
  </stage>
</workflow_execution>
```

---

## Implementation Phases

### Phase 1: Preparation (30 minutes)

**Objective**: Backup current state and verify subagent structure

**Tasks**:
1. Create backup of current `implementer.md`
2. Verify all three subagents exist and are properly configured
3. Review subagent output formats
4. Document current behavior for comparison

**Deliverables**:
- Backup file: `.opencode/agent/implementer.md.backup`
- Subagent verification checklist
- Baseline behavior documentation

**Success Criteria**:
- All files backed up
- Subagents confirmed working independently
- Current behavior documented

---

### Phase 2: Core Refactoring (2 hours)

**Objective**: Update Implementer agent to properly delegate to subagents

#### Step 2.1: Update Frontmatter (15 minutes)

**File**: `.opencode/agent/implementer.md`

**Changes**:
```yaml
---
description: "Manages a team of subagents to write, lint, and verify LEAN 4 code based on a formal proof plan."
mode: primary
temperature: 0.1
tools:
  task: true      # ← ADD: Enable delegation to subagents
  read: true      # ← ADD: Read proof plans and context
  write: true     # ← ADD: Write final output files
  edit: true      # ← ADD: Edit files if needed
  bash: false     # ← ADD: No bash needed (subagents handle compilation)
---
```

**Validation**:
- YAML is valid
- All tools explicitly listed
- `task: true` is present

#### Step 2.2: Update Routing Paths (30 minutes)

**File**: `.opencode/agent/implementer.md` (lines 133-154)

**Before**:
```markdown
<routing_intelligence>
  <execute_routing>
    <route to="@tactic-selector" when="...">
```

**After**:
```markdown
<routing_intelligence>
  <execute_routing>
    <route to="subagents/implementer/tactic-selector" when="the correct LEAN 4 tactic for a specific proof step needs to be chosen.">
      <context_level>Level 1</context_level>
      <pass_data>
        - step_description: High-level description of the proof step
        - proof_state: Current LEAN 4 proof state (hypotheses and goal)
      </pass_data>
      <expected_return>
        A single LEAN 4 tactic string (e.g., "rw [mul_comm]", "apply h_gt_zero")
      </expected_return>
      <integration>
        Pass the returned tactic to the code-generator subagent
      </integration>
    </route>
    
    <route to="subagents/implementer/code-generator" when="a line of LEAN 4 code needs to be written based on a chosen tactic.">
      <context_level>Level 1</context_level>
      <pass_data>
        - tactic: The LEAN 4 tactic to use
        - proof_context: Current proof context and state
      </pass_data>
      <expected_return>
        A single line of valid LEAN 4 code
      </expected_return>
      <integration>
        Append the line to the proof being constructed and validate it compiles
      </integration>
    </route>
    
    <route to="subagents/implementer/lean-linter" when="the generated LEAN 4 code needs to be checked for style and best practices.">
      <context_level>Level 2</context_level>
      <pass_data>
        - file_content: The complete generated LEAN 4 file
      </pass_data>
      <expected_return>
        A list of linting suggestions with line numbers and messages
      </expected_return>
      <integration>
        Apply the suggestions to improve code quality before finalizing
      </integration>
    </route>
  </execute_routing>
</routing_intelligence>
```

**Validation**:
- All paths use `subagents/implementer/` prefix
- Context levels are appropriate (Level 1 for isolation, Level 2 for linter)
- Pass data is clearly specified
- Expected returns are well-defined

#### Step 2.3: Add Explicit Task Tool Instructions (1 hour)

**File**: `.opencode/agent/implementer.md` (lines 74-131)

**Insert new section before workflow_execution**:

```markdown
<critical_instructions priority="highest">
  <instruction id="use_task_tool">
    You MUST use the `task` tool to invoke subagents. DO NOT perform their work yourself.
    
    **Correct approach**:
    ```
    task(
      subagent_type="subagents/implementer/tactic-selector",
      description="Select tactic",
      prompt="For step: '{step}', select the appropriate LEAN 4 tactic"
    )
    ```
    
    **Incorrect approach** (DO NOT DO THIS):
    - Selecting tactics yourself
    - Generating code yourself
    - Performing linting yourself
    
    Your role is COORDINATION, not execution. Delegate all specialized work.
  </instruction>
  
  <instruction id="delegation_pattern">
    For each proof step, follow this exact pattern:
    
    1. Invoke tactic-selector → receive tactic string
    2. Invoke code-generator with that tactic → receive code line
    3. Validate the code line compiles
    4. If success, continue to next step
    5. If failure, STOP and report error
    
    After all steps, invoke lean-linter → receive suggestions → apply them
  </instruction>
</critical_instructions>
```

**Update workflow_execution section**:

```markdown
<workflow_execution>
  <stage id="1" name="PlanInterpretation">
    <action>Parse the proof plan and prepare for code generation.</action>
    <process>
      1. Read the "Goal", "Dependencies", and "Proof Steps" from the plan.
      2. Generate the necessary `import` statements for all dependencies.
      3. Create the theorem's signature (e.g., `theorem my_theorem (h : hypothesis) : conclusion := by`).
    </process>
    <checkpoint>The basic structure of the `.lean` file is created, including imports and the theorem signature.</checkpoint>
  </stage>

  <stage id="2" name="TacticalImplementation">
    <action>Implement each step of the proof plan by delegating to specialized subagents.</action>
    <process>
      For each step in the proof plan:
      
      **Step A: Select Tactic**
      Use the task tool to invoke the tactic selector:
      ```
      task(
        subagent_type="subagents/implementer/tactic-selector",
        description="Select LEAN 4 tactic for proof step {step_number}",
        prompt="Given the proof step description: '{step_description}' 
                and the current proof state: '{proof_state}',
                return the appropriate LEAN 4 tactic string.
                
                Example step: 'Apply the hypothesis h_positive'
                Example state: 'h_positive : 0 < x ⊢ x ≠ 0'
                Expected return: 'apply h_positive'"
      )
      ```
      Store the returned tactic string.
      
      **Step B: Generate Code**
      Use the task tool to invoke the code generator:
      ```
      task(
        subagent_type="subagents/implementer/code-generator",
        description="Generate LEAN 4 code line for step {step_number}",
        prompt="Generate a single line of LEAN 4 code using the tactic: '{tactic}'
                in the context of: '{proof_context}'.
                
                Return only the code line, properly formatted and indented."
      )
      ```
      Store the returned code line.
      
      **Step C: Incremental Validation**
      Append the code line to the proof and attempt to compile.
      
      If compilation FAILS:
        - STOP immediately
        - Report error to orchestrator with:
          * Failed step number
          * Compilation error message
          * Suggested plan revision
        - DO NOT attempt to auto-fix
      
      If compilation SUCCEEDS:
        - Proceed to next step
      
      Repeat for all steps in the plan.
    </process>
    <checkpoint>All proof steps implemented via subagent delegation and incrementally validated.</checkpoint>
  </stage>

  <stage id="3" name="ValidationAndLinting">
    <action>Verify the generated code and ensure it meets quality standards.</action>
    <process>
      1. Compile the complete `.lean` file to check for errors.
      
      2. If compilation succeeds, invoke the linter:
         ```
         task(
           subagent_type="subagents/implementer/lean-linter",
           description="Lint generated LEAN 4 code",
           prompt="Lint the following LEAN 4 file and return a list of style suggestions:
                   
                   {file_content}
                   
                   Return suggestions in YAML format with line numbers, rule names, and messages."
         )
         ```
      
      3. Review linting suggestions.
      
      4. Apply non-breaking suggestions (formatting, naming, etc.).
    </process>
    <decision>
      <if test="compilation fails">
        STOP. Report error to @orchestrator with:
        - Complete compilation error message
        - Line number and context of failure
        - Suggested plan revision or tactic adjustment
        DO NOT attempt to auto-fix without approval.
      </if>
      <else>Proceed to finalize the file.</else>
    </decision>
    <checkpoint>The generated code is syntactically correct, compiles, and adheres to linting standards.</checkpoint>
  </stage>

  <stage id="4" name="Finalize">
    <action>Deliver the final `.lean` file.</action>
    <process>
      1. Ensure the file is well-commented and clean.
      2. Return the complete file content to the @orchestrator.
    </process>
    <checkpoint>The final `.lean` file is ready for use.</checkpoint>
  </stage>
</workflow_execution>
```

**Validation**:
- Task tool invocations are explicit and concrete
- Examples show exact syntax
- Instructions emphasize delegation over self-execution
- Error handling is clear

#### Step 2.4: Add Tool Usage Documentation (15 minutes)

**File**: `.opencode/agent/implementer.md`

**Insert after `<task>` section**:

```markdown
<tool_usage>
  <task_tool>
    **Primary tool for this agent**. Use to delegate all specialized work to subagents.
    
    **When to use**:
    - Selecting tactics → invoke tactic-selector
    - Generating code → invoke code-generator
    - Linting code → invoke lean-linter
    
    **How to use**:
    ```
    task(
      subagent_type="subagents/implementer/[subagent-name]",
      description="Brief description of what subagent should do",
      prompt="Detailed instructions with all necessary context and examples"
    )
    ```
    
    **Never**:
    - Do the subagent's work yourself
    - Skip delegation for "simple" tasks
    - Assume you can do it better than the specialist
  </task_tool>
  
  <read_tool>
    Use to read proof plans, context files, and existing code.
  </read_tool>
  
  <write_tool>
    Use to write the final `.lean` file after all subagents have completed their work.
  </write_tool>
  
  <edit_tool>
    Use to apply linting suggestions to the generated code.
  </edit_tool>
</tool_usage>
```

**Validation**:
- Tool usage is clear and actionable
- Examples are concrete
- Warnings about what NOT to do are included

---

### Phase 3: Subagent Optimization (1.5 hours)

**Objective**: Ensure subagents have clean input/output contracts

#### Step 3.1: Optimize Tactic Selector Output (30 minutes)

**File**: `.opencode/agent/subagents/implementer/tactic-selector.md`

**Update output specification** (lines 78-87):

**Before**:
```markdown
<output_specification>
  <format>
    ```yaml
    tactic: "rw [mul_comm]"
    ```
  </format>
  <error_handling>
    If the step description is ambiguous or cannot be mapped to a known tactic, return an error message in the `tactic` field.
  </error_handling>
</output_specification>
```

**After**:
```markdown
<output_specification>
  <format>
    Return ONLY the tactic string, nothing else. No YAML, no markdown, no explanations.
    
    **Correct output**:
    ```
    rw [mul_comm]
    ```
    
    **Incorrect output** (DO NOT DO THIS):
    ```yaml
    tactic: "rw [mul_comm]"
    ```
    
    ```
    The tactic you should use is: rw [mul_comm]
    ```
  </format>
  
  <error_handling>
    If the step description is ambiguous or cannot be mapped to a known tactic:
    
    Return: `ERROR: [brief description of the problem]`
    
    Example: `ERROR: Step description too vague - cannot determine if 'simplify' means simp, omega, or ring`
  </error_handling>
</output_specification>

<examples>
  <example_1>
    <input>
      step_description: "Rewrite using the commutativity of multiplication"
      proof_state: "⊢ a * b = b * a"
    </input>
    <output>rw [mul_comm]</output>
  </example_1>
  
  <example_2>
    <input>
      step_description: "Apply the hypothesis that x is positive"
      proof_state: "h_pos : 0 < x ⊢ x ≠ 0"
    </input>
    <output>apply h_pos</output>
  </example_2>
  
  <example_3>
    <input>
      step_description: "Simplify the goal"
      proof_state: "⊢ x + 0 = x"
    </input>
    <output>simp</output>
  </example_3>
</examples>
```

**Validation**:
- Output format is unambiguous
- Examples show exact expected format
- Error handling is clear

#### Step 3.2: Optimize Code Generator Output (30 minutes)

**File**: `.opencode/agent/subagents/implementer/code-generator.md`

**Update output specification** (lines 82-103):

**Before**:
```markdown
<output_specification>
  <format>
    ```yaml
    file_content: |
      -- Copyright (c) 2024. All rights reserved.
      ...
    ```
  </format>
</output_specification>
```

**After**:
```markdown
<output_specification>
  <format>
    Return ONLY the generated code line, nothing else. No YAML, no markdown code blocks, no explanations.
    
    **Correct output**:
    ```
      rw [mul_comm]
    ```
    (Note: Include proper indentation)
    
    **Incorrect output** (DO NOT DO THIS):
    ```yaml
    file_content: "  rw [mul_comm]"
    ```
    
    ```
    The code line you should use is:
      rw [mul_comm]
    ```
  </format>
  
  <indentation>
    - Use 2 spaces for each indentation level
    - Tactic lines inside `by` blocks should be indented
    - Match the indentation of surrounding code
  </indentation>
  
  <error_handling>
    If inputs are invalid or incomplete:
    
    Return: `ERROR: [brief description]`
    
    Example: `ERROR: Tactic string is empty`
  </error_handling>
</output_specification>

<examples>
  <example_1>
    <input>
      tactic: "rw [mul_comm]"
      proof_context: "Inside theorem proof, first tactic"
    </input>
    <output>  rw [mul_comm]</output>
  </example_1>
  
  <example_2>
    <input>
      tactic: "apply h_positive"
      proof_context: "Second tactic in proof"
    </input>
    <output>  apply h_positive</output>
  </example_2>
</examples>
```

**Validation**:
- Output format is simple and clean
- Indentation rules are clear
- Examples show exact format

#### Step 3.3: Optimize Lean Linter Output (30 minutes)

**File**: `.opencode/agent/subagents/implementer/lean-linter.md`

**Update output specification** (lines 78-95):

**After**:
```markdown
<output_specification>
  <format>
    Return linting results in YAML format with this exact structure:
    
    ```yaml
    status: "success" | "no_issues"
    suggestions:
      - line_number: 12
        rule: "line-length"
        severity: "warning"
        message: "Line exceeds 100 characters."
        suggestion: "Consider breaking the tactic block into multiple lines."
      - line_number: 15
        rule: "naming-convention"
        severity: "warning"
        message: "Theorem name 'MyTheorem' should be 'my_theorem'."
        suggestion: "Rename the theorem to follow snake_case."
    ```
    
    If no issues found:
    ```yaml
    status: "no_issues"
    suggestions: []
    ```
  </format>
  
  <severity_levels>
    - "error": Must be fixed (syntax errors, invalid names)
    - "warning": Should be fixed (style violations, long lines)
    - "info": Consider fixing (minor style suggestions)
  </severity_levels>
  
  <error_handling>
    If the file content is invalid or cannot be parsed:
    
    ```yaml
    status: "error"
    error:
      code: "INVALID_INPUT"
      message: "File content is empty or malformed"
    ```
  </error_handling>
</output_specification>

<examples>
  <example_1>
    <input>
      file_content: |
        theorem my_theorem (a b : ℕ) : a + b = b + a := by
          rw [Nat.add_comm]
    </input>
    <output>
      status: "no_issues"
      suggestions: []
    </output>
  </example_1>
  
  <example_2>
    <input>
      file_content: |
        theorem MyTheorem (a b : ℕ) : a + b = b + a := by
          rw [Nat.add_comm]  -- This line is exactly 101 characters long which exceeds our 100 character limit
    </input>
    <output>
      status: "success"
      suggestions:
        - line_number: 1
          rule: "naming-convention"
          severity: "warning"
          message: "Theorem name 'MyTheorem' should be 'my_theorem'"
          suggestion: "Rename to follow snake_case convention"
        - line_number: 2
          rule: "line-length"
          severity: "warning"
          message: "Line exceeds 100 characters (101 chars)"
          suggestion: "Break comment into multiple lines or shorten"
    </output>
  </example_2>
</examples>
```

**Validation**:
- YAML structure is well-defined
- Severity levels are clear
- Examples show both success and warning cases

---

### Phase 4: Testing & Validation (1.5 hours)

**Objective**: Verify changes work correctly and measure improvements

#### Step 4.1: Unit Test Each Subagent (30 minutes)

**Test Tactic Selector**:

Create test file: `.opencode/specs/implementer-optimization/test-tactic-selector.md`

```markdown
# Tactic Selector Test Cases

## Test 1: Simple Rewrite
**Input**:
- step_description: "Rewrite using commutativity"
- proof_state: "⊢ a * b = b * a"

**Expected Output**: `rw [mul_comm]`

## Test 2: Apply Hypothesis
**Input**:
- step_description: "Apply the positivity hypothesis"
- proof_state: "h_pos : 0 < x ⊢ x ≠ 0"

**Expected Output**: `apply h_pos`

## Test 3: Simplification
**Input**:
- step_description: "Simplify the goal"
- proof_state: "⊢ x + 0 = x"

**Expected Output**: `simp`

## Test 4: Error Case
**Input**:
- step_description: "Do something"
- proof_state: "⊢ complicated_goal"

**Expected Output**: `ERROR: Step description too vague`
```

**Test Code Generator**:

Create test file: `.opencode/specs/implementer-optimization/test-code-generator.md`

```markdown
# Code Generator Test Cases

## Test 1: Simple Tactic
**Input**:
- tactic: "rw [mul_comm]"
- proof_context: "First tactic in proof"

**Expected Output**: `  rw [mul_comm]`

## Test 2: Apply Tactic
**Input**:
- tactic: "apply h_positive"
- proof_context: "Second tactic"

**Expected Output**: `  apply h_positive`
```

**Test Lean Linter**:

Create test file: `.opencode/specs/implementer-optimization/test-lean-linter.md`

```markdown
# Lean Linter Test Cases

## Test 1: Clean Code
**Input**:
```lean
theorem my_theorem (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
```

**Expected Output**:
```yaml
status: "no_issues"
suggestions: []
```

## Test 2: Naming Violation
**Input**:
```lean
theorem MyTheorem (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
```

**Expected Output**:
```yaml
status: "success"
suggestions:
  - line_number: 1
    rule: "naming-convention"
    severity: "warning"
    message: "Theorem name 'MyTheorem' should be 'my_theorem'"
```
```

**Execution**:
1. Manually test each subagent with test cases
2. Verify outputs match expected formats
3. Document any discrepancies
4. Fix issues before proceeding

#### Step 4.2: Integration Test (45 minutes)

**Create test proof outline**:

File: `.opencode/specs/implementer-optimization/test-proof-outline.md`

```markdown
# Test Proof Outline: Commutativity of Addition

## Goal
Prove that addition is commutative for natural numbers.

## Theorem Statement
```lean
theorem add_comm (a b : ℕ) : a + b = b + a
```

## Dependencies
- Mathlib.Data.Nat.Basic

## Proof Steps

### Step 1: Induction on a
**Description**: Use induction on the first argument `a`.
**Expected Tactic**: `induction a with`

### Step 2: Base Case
**Description**: For `a = 0`, rewrite using `Nat.zero_add`.
**Expected Tactic**: `rw [Nat.zero_add, Nat.add_zero]`

### Step 3: Inductive Step
**Description**: For `a = succ a'`, use the inductive hypothesis.
**Expected Tactic**: `rw [Nat.succ_add, ih, Nat.add_succ]`
```

**Test Execution**:

1. Run `/implement test-proof-outline.md`
2. Monitor session logs for:
   - Task tool invocations
   - Subagent calls
   - Context window usage
3. Verify:
   - Tactic selector is invoked for each step
   - Code generator is invoked for each step
   - Linter is invoked at the end
   - Final code compiles
   - Final code is well-formatted

**Success Criteria**:
- All subagents are invoked via `task` tool
- No direct implementation by Implementer
- Generated code is correct
- Linting suggestions are applied

#### Step 4.3: Performance Measurement (15 minutes)

**Metrics to Collect**:

1. **Context Window Usage**:
   - Before: Implementer context size
   - After: Implementer context size
   - Target: 60-80% reduction

2. **Execution Time**:
   - Before: Time to implement proof
   - After: Time to implement proof
   - Note: May be slightly slower due to delegation overhead

3. **Code Quality**:
   - Before: Linting violations
   - After: Linting violations
   - Target: Same or better

4. **Correctness**:
   - Before: Compilation success rate
   - After: Compilation success rate
   - Target: 100% (no regression)

**Measurement Process**:

Create file: `.opencode/specs/implementer-optimization/performance-results.md`

```markdown
# Performance Measurement Results

## Test Date
[Date]

## Test Case
Simple proof: Commutativity of addition

## Metrics

### Context Window Usage
- **Before**: [X] tokens
- **After**: [Y] tokens
- **Reduction**: [Z]%

### Execution Time
- **Before**: [X] seconds
- **After**: [Y] seconds
- **Change**: [+/-Z]%

### Code Quality
- **Before**: [X] linting violations
- **After**: [Y] linting violations
- **Change**: [+/-Z] violations

### Correctness
- **Before**: [Pass/Fail]
- **After**: [Pass/Fail]
- **Compilation**: [Success/Failure]

## Observations
[Notes about behavior changes, improvements, issues]

## Conclusion
[Pass/Fail] - [Reasoning]
```

---

### Phase 5: Documentation & Rollout (30 minutes)

**Objective**: Document changes and prepare for production use

#### Step 5.1: Update Documentation (15 minutes)

**Update files**:

1. `.opencode/docs/AGENTS_GUIDE.md`
   - Add section on Implementer agent delegation pattern
   - Explain subagent architecture
   - Provide examples

2. `.opencode/README.md`
   - Update Implementer agent description
   - Note that it uses subagents for efficiency

3. `.opencode/command/implement.md`
   - Add note about subagent delegation
   - Explain context window benefits

**Example addition to AGENTS_GUIDE.md**:

```markdown
## Implementer Agent Architecture

The Implementer agent uses a **manager-worker pattern** with specialized subagents:

### Subagents

1. **Tactic Selector** (`subagents/implementer/tactic-selector`)
   - Selects appropriate LEAN 4 tactics for proof steps
   - Uses Level 1 context (complete isolation)
   - Returns: Single tactic string

2. **Code Generator** (`subagents/implementer/code-generator`)
   - Generates LEAN 4 code from tactics
   - Uses Level 1 context (complete isolation)
   - Returns: Single code line

3. **Lean Linter** (`subagents/implementer/lean-linter`)
   - Validates and lints generated code
   - Uses Level 2 context (filtered context)
   - Returns: List of linting suggestions

### Benefits

- **60-80% context window reduction** for Implementer agent
- **Faster execution** due to smaller context per agent
- **Better code quality** through specialist subagents
- **Improved scalability** for complex proofs

### Usage

The Implementer automatically delegates to subagents. No user action required.

```bash
/implement proof-outline.md
```

The Implementer will:
1. Parse the proof plan
2. For each step, invoke tactic-selector and code-generator
3. Validate incrementally
4. Invoke lean-linter for final validation
5. Return polished LEAN 4 code
```

#### Step 5.2: Create Migration Guide (15 minutes)

**Create file**: `.opencode/specs/implementer-optimization/MIGRATION_GUIDE.md`

```markdown
# Implementer Agent Migration Guide

## Overview

The Implementer agent has been refactored to use a manager-worker pattern with specialized subagents. This improves context window efficiency and code quality.

## What Changed

### Before
- Implementer did all work itself
- Loaded all context (tactics, code generation, linting)
- Context window: ~15,000 tokens

### After
- Implementer delegates to subagents
- Each subagent has minimal, focused context
- Total context: ~7,000 tokens (distributed)
- Implementer context: ~3,000 tokens (80% reduction)

## User Impact

### No Breaking Changes
- `/implement` command works the same
- Input format unchanged
- Output format unchanged

### Performance Improvements
- Faster execution (smaller context)
- Better code quality (specialist subagents)
- Can handle larger proofs

## Rollback Procedure

If issues arise, restore the backup:

```bash
cp .opencode/agent/implementer.md.backup .opencode/agent/implementer.md
```

## Support

For issues or questions, see:
- `.opencode/specs/implementer-optimization/performance-results.md`
- `.opencode/docs/AGENTS_GUIDE.md`
```

---

## Detailed Changes

### File: `.opencode/agent/implementer.md`

#### Change 1: Frontmatter (Lines 1-5)

**Before**:
```yaml
---
description: "Manages a team of subagents to write, lint, and verify LEAN 4 code based on a formal proof plan."
mode: primary
temperature: 0.1
---
```

**After**:
```yaml
---
description: "Manages a team of subagents to write, lint, and verify LEAN 4 code based on a formal proof plan."
mode: primary
temperature: 0.1
tools:
  task: true      # Enable delegation to subagents
  read: true      # Read proof plans and context
  write: true     # Write final output files
  edit: true      # Edit files if needed
  bash: false     # No bash needed (subagents handle compilation)
---
```

**Rationale**: Explicitly enable the `task` tool for delegation and clarify which tools are needed.

#### Change 2: Add Critical Instructions (After line 28, before workflow_execution)

**Insert**:
```markdown
<critical_instructions priority="highest">
  <instruction id="use_task_tool">
    You MUST use the `task` tool to invoke subagents. DO NOT perform their work yourself.
    
    **Correct approach**:
    ```
    task(
      subagent_type="subagents/implementer/tactic-selector",
      description="Select tactic",
      prompt="For step: '{step}', select the appropriate LEAN 4 tactic"
    )
    ```
    
    **Incorrect approach** (DO NOT DO THIS):
    - Selecting tactics yourself
    - Generating code yourself
    - Performing linting yourself
    
    Your role is COORDINATION, not execution. Delegate all specialized work.
  </instruction>
  
  <instruction id="delegation_pattern">
    For each proof step, follow this exact pattern:
    
    1. Invoke tactic-selector → receive tactic string
    2. Invoke code-generator with that tactic → receive code line
    3. Validate the code line compiles
    4. If success, continue to next step
    5. If failure, STOP and report error
    
    After all steps, invoke lean-linter → receive suggestions → apply them
  </instruction>
</critical_instructions>

<tool_usage>
  <task_tool>
    **Primary tool for this agent**. Use to delegate all specialized work to subagents.
    
    **When to use**:
    - Selecting tactics → invoke tactic-selector
    - Generating code → invoke code-generator
    - Linting code → invoke lean-linter
    
    **How to use**:
    ```
    task(
      subagent_type="subagents/implementer/[subagent-name]",
      description="Brief description of what subagent should do",
      prompt="Detailed instructions with all necessary context and examples"
    )
    ```
    
    **Never**:
    - Do the subagent's work yourself
    - Skip delegation for "simple" tasks
    - Assume you can do it better than the specialist
  </task_tool>
  
  <read_tool>
    Use to read proof plans, context files, and existing code.
  </read_tool>
  
  <write_tool>
    Use to write the final `.lean` file after all subagents have completed their work.
  </write_tool>
  
  <edit_tool>
    Use to apply linting suggestions to the generated code.
  </edit_tool>
</tool_usage>
```

**Rationale**: Provide explicit, unambiguous instructions on how to use the task tool and when to delegate.

#### Change 3: Update Workflow Execution (Lines 74-131)

**Replace entire `<workflow_execution>` section** with the detailed version from Phase 2, Step 2.3 above.

**Key changes**:
- Add explicit `task()` invocations with examples
- Show exact syntax for each subagent call
- Emphasize delegation over self-execution
- Include error handling for failed delegations

#### Change 4: Update Routing Intelligence (Lines 133-154)

**Before**:
```markdown
<routing_intelligence>
  <execute_routing>
    <route to="@tactic-selector" when="...">
```

**After**:
```markdown
<routing_intelligence>
  <execute_routing>
    <route to="subagents/implementer/tactic-selector" when="the correct LEAN 4 tactic for a specific proof step needs to be chosen.">
      <context_level>Level 1</context_level>
      <pass_data>
        - step_description: High-level description of the proof step
        - proof_state: Current LEAN 4 proof state (hypotheses and goal)
      </pass_data>
      <expected_return>
        A single LEAN 4 tactic string (e.g., "rw [mul_comm]", "apply h_gt_zero")
      </expected_return>
      <integration>
        Pass the returned tactic to the code-generator subagent
      </integration>
    </route>
    
    <route to="subagents/implementer/code-generator" when="a line of LEAN 4 code needs to be written based on a chosen tactic.">
      <context_level>Level 1</context_level>
      <pass_data>
        - tactic: The LEAN 4 tactic to use
        - proof_context: Current proof context and state
      </pass_data>
      <expected_return>
        A single line of valid LEAN 4 code
      </expected_return>
      <integration>
        Append the line to the proof being constructed and validate it compiles
      </integration>
    </route>
    
    <route to="subagents/implementer/lean-linter" when="the generated LEAN 4 code needs to be checked for style and best practices.">
      <context_level>Level 2</context_level>
      <pass_data>
        - file_content: The complete generated LEAN 4 file
      </pass_data>
      <expected_return>
        A list of linting suggestions with line numbers and messages
      </expected_return>
      <integration>
        Apply the suggestions to improve code quality before finalizing
      </integration>
    </route>
  </execute_routing>
</routing_intelligence>
```

**Rationale**: Use correct subagent paths and provide detailed routing specifications.

---

### Files: Subagent Output Specifications

See Phase 3 above for detailed changes to:
- `.opencode/agent/subagents/implementer/tactic-selector.md`
- `.opencode/agent/subagents/implementer/code-generator.md`
- `.opencode/agent/subagents/implementer/lean-linter.md`

---

## Testing Strategy

### Test Levels

1. **Unit Tests**: Test each subagent independently
2. **Integration Tests**: Test Implementer with subagents
3. **System Tests**: Test via `/implement` command
4. **Performance Tests**: Measure context window usage

### Test Cases

#### TC-1: Simple Proof (Unit Test)
**Objective**: Verify tactic-selector works independently

**Input**:
```
step_description: "Rewrite using commutativity"
proof_state: "⊢ a * b = b * a"
```

**Expected Output**: `rw [mul_comm]`

**Pass Criteria**: Output matches expected format exactly

#### TC-2: Code Generation (Unit Test)
**Objective**: Verify code-generator works independently

**Input**:
```
tactic: "rw [mul_comm]"
proof_context: "First tactic in proof"
```

**Expected Output**: `  rw [mul_comm]`

**Pass Criteria**: Output is properly indented and formatted

#### TC-3: Linting (Unit Test)
**Objective**: Verify lean-linter works independently

**Input**:
```lean
theorem MyTheorem (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]
```

**Expected Output**:
```yaml
status: "success"
suggestions:
  - line_number: 1
    rule: "naming-convention"
    severity: "warning"
    message: "Theorem name 'MyTheorem' should be 'my_theorem'"
```

**Pass Criteria**: Naming violation detected

#### TC-4: Full Implementation (Integration Test)
**Objective**: Verify Implementer delegates to all subagents

**Input**: Test proof outline (see Phase 4, Step 4.2)

**Expected Behavior**:
1. Implementer invokes tactic-selector for each step
2. Implementer invokes code-generator for each step
3. Implementer validates incrementally
4. Implementer invokes lean-linter at end
5. Final code compiles and is well-formatted

**Pass Criteria**:
- All subagents invoked via `task` tool
- No direct implementation by Implementer
- Final code compiles
- Context window usage reduced by 60-80%

#### TC-5: Error Handling (Integration Test)
**Objective**: Verify error handling when compilation fails

**Input**: Proof outline with invalid tactic

**Expected Behavior**:
1. Implementer invokes tactic-selector
2. Tactic-selector returns tactic
3. Code-generator generates code
4. Compilation fails
5. Implementer STOPS and reports error
6. Error includes step number, error message, suggestion

**Pass Criteria**:
- Implementer stops on error
- Error is reported to orchestrator
- No auto-fix attempted

### Test Execution Plan

1. **Day 1**: Unit tests for all subagents
2. **Day 2**: Integration tests for Implementer
3. **Day 3**: System tests via `/implement` command
4. **Day 4**: Performance measurement and analysis
5. **Day 5**: Bug fixes and refinement

### Test Environment

- **Repository**: ProofChecker
- **Branch**: `feature/implementer-optimization`
- **Test Files**: `.opencode/specs/implementer-optimization/test-*.md`
- **Results**: `.opencode/specs/implementer-optimization/test-results.md`

---

## Success Metrics

### Primary Metrics

1. **Context Window Reduction**
   - **Target**: 60-80% reduction in Implementer context
   - **Measurement**: Token count before/after
   - **Success**: ≥60% reduction

2. **Delegation Rate**
   - **Target**: 100% of specialized work delegated
   - **Measurement**: Count of `task` tool invocations
   - **Success**: All tactics, code generation, and linting delegated

3. **Code Quality**
   - **Target**: No regression in linting violations
   - **Measurement**: Linting violation count before/after
   - **Success**: Same or fewer violations

4. **Correctness**
   - **Target**: 100% compilation success
   - **Measurement**: Compilation pass/fail
   - **Success**: All generated code compiles

### Secondary Metrics

1. **Execution Time**
   - **Target**: No significant slowdown
   - **Measurement**: Time to implement proof
   - **Acceptable**: <20% increase (due to delegation overhead)

2. **Error Handling**
   - **Target**: Proper error reporting
   - **Measurement**: Error messages include context
   - **Success**: All errors have step number, message, suggestion

3. **User Experience**
   - **Target**: No breaking changes
   - **Measurement**: User workflow unchanged
   - **Success**: `/implement` works identically from user perspective

### Measurement Process

1. **Baseline**: Measure current performance on 5 test proofs
2. **Implementation**: Apply changes
3. **Post-implementation**: Measure new performance on same 5 proofs
4. **Analysis**: Compare metrics and validate success criteria
5. **Documentation**: Record results in performance-results.md

---

## Rollback Plan

### Trigger Conditions

Rollback if any of the following occur:

1. **Context window reduction <40%**: Not achieving efficiency goals
2. **Compilation failures**: Generated code doesn't compile
3. **Execution time increase >50%**: Unacceptable performance degradation
4. **Breaking changes**: User workflow disrupted

### Rollback Procedure

#### Step 1: Restore Backup (5 minutes)

```bash
# Navigate to agent directory
cd .opencode/agent

# Restore implementer from backup
cp implementer.md.backup implementer.md

# Verify restoration
git diff implementer.md
```

#### Step 2: Verify Functionality (10 minutes)

```bash
# Test with simple proof
/implement test-proof-outline.md

# Verify it works
# Check compilation
# Check output quality
```

#### Step 3: Document Rollback (5 minutes)

Create file: `.opencode/specs/implementer-optimization/ROLLBACK_REPORT.md`

```markdown
# Rollback Report

## Date
[Date and time]

## Reason
[Why rollback was necessary]

## Metrics at Rollback
- Context window reduction: [X]%
- Compilation success: [Y]%
- Execution time change: [Z]%

## Issues Encountered
1. [Issue 1]
2. [Issue 2]

## Lessons Learned
[What went wrong and how to fix it]

## Next Steps
[Plan for addressing issues before retry]
```

#### Step 4: Communicate (5 minutes)

- Update project team
- Document in git commit
- Plan for retry with fixes

### Prevention

To minimize rollback risk:

1. **Incremental changes**: Apply changes in phases
2. **Test after each phase**: Validate before proceeding
3. **Keep backups**: Maintain backup at each phase
4. **Monitor metrics**: Track metrics continuously

---

## References

### OpenCode Documentation

1. **Agents Guide**: https://opencode.ai/docs/agents/
   - Primary vs subagent modes
   - Tool configuration
   - Agent invocation patterns

2. **Tools Guide**: https://opencode.ai/docs/tools/
   - Task tool usage
   - Tool permissions
   - Tool configuration

3. **Creating Subagents**: `/home/benjamin/Documents/Philosophy/Projects/OpenAgents/docs/guides/creating-subagents.md`
   - Subagent patterns
   - Delegation patterns
   - File structure and naming

### Internal Documentation

1. **Agents Guide**: `.opencode/docs/AGENTS_GUIDE.md`
   - Current agent architecture
   - Agent descriptions

2. **Architecture**: `.opencode/docs/ARCHITECTURE.md`
   - System architecture
   - Agent coordination

3. **Workflows**: `.opencode/docs/WORKFLOWS.md`
   - Workflow patterns
   - Agent interactions

### Related Specifications

1. **Agent Comparison**: `.opencode/specs/agent-comparison-coder-vs-lean-implementer.md`
   - Implementer vs Coder agent analysis

2. **Integration Analysis**: `.opencode/specs/coder-to-lean-implementer-integration-analysis.md`
   - Integration patterns

### Research Papers

1. **Anthropic XML Prompting**: Research on XML structure optimization
   - +25% consistency improvement
   - Hierarchical context organization

2. **Stanford Agent Patterns**: Manager-worker delegation patterns
   - Context efficiency
   - Specialist subagents

---

## Appendix A: File Checklist

### Files to Modify

- [ ] `.opencode/agent/implementer.md` (main changes)
- [ ] `.opencode/agent/subagents/implementer/tactic-selector.md` (output format)
- [ ] `.opencode/agent/subagents/implementer/code-generator.md` (output format)
- [ ] `.opencode/agent/subagents/implementer/lean-linter.md` (output format)

### Files to Create

- [ ] `.opencode/agent/implementer.md.backup` (backup)
- [ ] `.opencode/specs/implementer-optimization/test-tactic-selector.md`
- [ ] `.opencode/specs/implementer-optimization/test-code-generator.md`
- [ ] `.opencode/specs/implementer-optimization/test-lean-linter.md`
- [ ] `.opencode/specs/implementer-optimization/test-proof-outline.md`
- [ ] `.opencode/specs/implementer-optimization/performance-results.md`
- [ ] `.opencode/specs/implementer-optimization/test-results.md`
- [ ] `.opencode/specs/implementer-optimization/MIGRATION_GUIDE.md`

### Files to Update

- [ ] `.opencode/docs/AGENTS_GUIDE.md` (add delegation pattern section)
- [ ] `.opencode/README.md` (update Implementer description)
- [ ] `.opencode/command/implement.md` (add delegation note)

---

## Appendix B: Timeline

### Week 1: Implementation

- **Day 1 (2 hours)**: Phase 1 - Preparation
  - Create backups
  - Verify subagents
  - Document baseline

- **Day 2 (4 hours)**: Phase 2 - Core Refactoring
  - Update Implementer frontmatter
  - Fix routing paths
  - Add task tool instructions
  - Add tool usage documentation

- **Day 3 (3 hours)**: Phase 3 - Subagent Optimization
  - Optimize tactic-selector output
  - Optimize code-generator output
  - Optimize lean-linter output

- **Day 4 (3 hours)**: Phase 4 - Testing
  - Unit test subagents
  - Integration test Implementer
  - Performance measurement

- **Day 5 (1 hour)**: Phase 5 - Documentation
  - Update documentation
  - Create migration guide
  - Finalize specification

### Week 2: Validation

- **Day 1-2**: Extended testing with real proofs
- **Day 3**: Performance analysis and optimization
- **Day 4**: Bug fixes and refinement
- **Day 5**: Final validation and deployment

---

## Appendix C: Risk Assessment

### High Risk

1. **Breaking existing workflows**
   - **Mitigation**: Maintain backup, test thoroughly
   - **Impact**: High (user disruption)
   - **Probability**: Low (no API changes)

2. **Subagent invocation failures**
   - **Mitigation**: Test each subagent independently
   - **Impact**: High (no code generation)
   - **Probability**: Medium (new delegation pattern)

### Medium Risk

1. **Performance degradation**
   - **Mitigation**: Measure and optimize
   - **Impact**: Medium (slower execution)
   - **Probability**: Low (smaller context should be faster)

2. **Output format incompatibilities**
   - **Mitigation**: Standardize output formats
   - **Impact**: Medium (parsing errors)
   - **Probability**: Medium (format changes)

### Low Risk

1. **Documentation gaps**
   - **Mitigation**: Comprehensive documentation plan
   - **Impact**: Low (confusion, not breakage)
   - **Probability**: Low (detailed docs planned)

2. **Context window not reduced enough**
   - **Mitigation**: Iterative optimization
   - **Impact**: Low (still some improvement)
   - **Probability**: Low (clear delegation pattern)

---

## Appendix D: Questions & Answers

### Q1: Will this break existing proofs?

**A**: No. The `/implement` command interface remains unchanged. Input and output formats are identical. Only the internal implementation changes.

### Q2: What if a subagent fails?

**A**: The Implementer will catch the error and report it to the orchestrator with context (step number, error message, suggestion). No auto-fix will be attempted.

### Q3: Can I still use the Implementer directly?

**A**: Yes. The Implementer can still be invoked directly via `@implementer` or `/implement`. The delegation to subagents is automatic and transparent.

### Q4: Will this work with custom proof plans?

**A**: Yes. As long as the proof plan follows the expected format (Goal, Dependencies, Proof Steps), the Implementer will delegate appropriately.

### Q5: What if I want to disable delegation?

**A**: You can restore the backup file to revert to the old behavior. However, this is not recommended as it defeats the purpose of the optimization.

### Q6: How do I monitor subagent invocations?

**A**: Check the session logs for `task` tool invocations. Each delegation will be logged with the subagent type and prompt.

### Q7: Can I customize subagent behavior?

**A**: Yes. Each subagent is a separate file that can be modified independently. Just ensure the output format remains compatible with the Implementer's expectations.

### Q8: What if context window reduction is less than 60%?

**A**: Investigate which context is still being loaded. Optimize subagent context loading. Consider adding more specialized subagents for specific tasks.

---

## Conclusion

This implementation plan provides a comprehensive roadmap for optimizing the Implementer agent to use subagents effectively. The changes are incremental, well-tested, and designed to minimize risk while maximizing context window efficiency.

**Expected outcomes**:
- 60-80% context window reduction
- Faster execution
- Better code quality
- Improved scalability

**Next steps**:
1. Review and approve this plan
2. Begin Phase 1 (Preparation)
3. Execute phases incrementally with testing
4. Measure and validate improvements
5. Document and deploy

---

**Document Version**: 1.0  
**Last Updated**: 2025-12-15  
**Author**: AI Assistant  
**Status**: Awaiting Review
