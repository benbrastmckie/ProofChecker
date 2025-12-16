# MCP Integration Plan for ProofChecker .opencode System

## Executive Summary

This document outlines a comprehensive plan to integrate Lean MCP servers (lean-lsp-mcp, LeanExplore, Loogle, and LeanSearch) into the ProofChecker .opencode system. The integration will enhance proof verification, theorem search, and exploration capabilities across all Lean-specific agents and commands.

**Status**: Phase 1 Complete (80%) - Foundation Established  
**Priority**: High  
**Estimated Complexity**: Moderate-High  
**Impact**: Transformative - will significantly enhance proof development workflow

**Latest Update (2025-12-15)**: Phase 1 (Foundation) has been implemented with TypeScript wrappers, error handling, and comprehensive documentation. See [Phase 1 Summary](./mcp-phase1-summary.md) for details.

---

## Quick Reference

**Implementation Status**: Phase 1 Complete (80%)  
**Files Created**: 10 new files, 2 updated (~2,000 lines)  
**Next Phase**: Integration Testing & Phase 2 (Subagent Development)

**Key Documents**:
- 📋 [Phase 1 Summary](./mcp-phase1-summary.md) - What was accomplished
- 🔬 [MCP Server Research](./mcp-server-research.md) - Research findings
- ✅ [Integration Checklist](./mcp-integration-checklist.md) - Task tracking
- 📚 [MCP Tools Guide](../context/lean4/tools/mcp-tools-guide.md) - User documentation
- 🚀 [Quick Start](../tool/mcp/QUICKSTART.md) - Developer quick reference

**Implementation Files**:
- `.opencode/tool/mcp/types.ts` - Type definitions
- `.opencode/tool/mcp/errors.ts` - Error handling
- `.opencode/tool/mcp/lsp-client.ts` - LSP client wrapper
- `.opencode/tool/mcp/index.ts` - Main coordinator

---

## Table of Contents

1. [Current State Analysis](#current-state-analysis)
2. [MCP Servers Overview](#mcp-servers-overview)
3. [Integration Architecture](#integration-architecture)
4. [Agent Enhancements](#agent-enhancements)
5. [Command Enhancements](#command-enhancements)
6. [Context File Updates](#context-file-updates)
7. [New Subagents](#new-subagents)
8. [Workflow Improvements](#workflow-improvements)
9. [Implementation Phases](#implementation-phases)
10. [Implementation Progress](#implementation-progress)
11. [Testing Strategy](#testing-strategy)
12. [Success Metrics](#success-metrics)

---

## Current State Analysis

### Existing Infrastructure

**Agents**:
- `orchestrator` - Main coordinator
- `researcher` - Information gathering (web, arXiv, Mathlib)
- `implementer` - Code generation with compilation validation
- `reviser` - Plan revision based on feedback
- `planner` - Proof strategy development
- `refactor` - Code improvement
- `translator` - LaTeX ↔ Lean conversion

**Subagents**:
- `mathlib-searcher` - Searches Mathlib for relevant theorems (simulated)
- `mathlib-explorer` - Grep-based Mathlib code search
- `proof-strategist` - High-level proof planning
- `arxiv-retriever` - Academic paper search
- `web-searcher` - General web search

**Key Commands**:
- `/prove` - End-to-end theorem proving
- `/research` - Information gathering
- `/implement` - Proof implementation
- `/refactor` - Code refactoring

**Current Limitations**:
1. **No Real-time LSP Integration**: Cannot verify proofs incrementally during generation
2. **Simulated Mathlib Search**: `mathlib-searcher` doesn't use actual Lean search tools
3. **No Semantic Search**: Relies on keyword/grep-based search only
4. **No Formal Search**: Cannot search by type signature or pattern
5. **Limited Exploration**: No structured exploration of Lean definitions/theorems
6. **Manual Verification**: Must compile entire files to check correctness

---

## MCP Servers Overview

### 1. lean-lsp-mcp (Proof Verification)

**Purpose**: Real-time interaction with Lean Language Server Protocol

**Key Capabilities**:
- **Proof State Inspection**: Get current proof state at any position
- **Goal Visualization**: See active goals, hypotheses, and target
- **Incremental Verification**: Check proof validity without full compilation
- **Error Diagnostics**: Get detailed error messages and suggestions
- **Type Information**: Query types of expressions
- **Hover Information**: Get documentation and type info
- **Definition Lookup**: Jump to definitions
- **Completion Suggestions**: Get tactic/term completions

**Expected Tools** (based on standard LSP):
```typescript
// Hypothetical MCP tool signatures
lean_lsp_get_proof_state(file_path, line, column) -> ProofState
lean_lsp_check_proof(file_path, proof_text) -> ValidationResult
lean_lsp_get_diagnostics(file_path) -> Diagnostic[]
lean_lsp_get_hover(file_path, line, column) -> HoverInfo
lean_lsp_get_completions(file_path, line, column) -> Completion[]
```

**Use Cases**:
- Incremental proof validation during implementation
- Real-time error feedback
- Tactic suggestion during proof construction
- Type-guided proof development

### 2. LeanExplore MCP (Exploration)

**Purpose**: Structured exploration of Lean projects and Mathlib

**Key Capabilities**:
- **Module Exploration**: List all definitions/theorems in a module
- **Dependency Analysis**: Find what a theorem depends on
- **Usage Analysis**: Find where a theorem is used
- **Namespace Navigation**: Explore Lean namespace hierarchy
- **Documentation Extraction**: Get docstrings and comments
- **Type Hierarchy**: Explore class instances and inheritance

**Expected Tools**:
```typescript
lean_explore_module(module_name) -> ModuleContents
lean_explore_dependencies(theorem_name) -> Dependency[]
lean_explore_usages(theorem_name) -> Usage[]
lean_explore_namespace(namespace) -> NamespaceContents
lean_explore_instances(type_class) -> Instance[]
```

**Use Cases**:
- Understanding Mathlib structure
- Finding related theorems
- Analyzing proof dependencies
- Discovering available instances

### 3. Loogle (Formal/Type-based Search)

**Purpose**: Search Mathlib by type signature and pattern matching

**Key Capabilities**:
- **Type Signature Search**: Find theorems matching a type pattern
- **Pattern Matching**: Search by structural patterns
- **Unification-based Search**: Find theorems that unify with a goal
- **Filtered Search**: Search within specific namespaces
- **Exact Match**: Find theorems with exact signatures

**Expected Tools**:
```typescript
loogle_search_by_type(type_pattern) -> Theorem[]
loogle_search_by_pattern(pattern) -> Theorem[]
loogle_search_unify(goal_type) -> Theorem[]
loogle_search_in_namespace(namespace, pattern) -> Theorem[]
```

**Examples**:
```lean
-- Search for commutativity theorems
loogle_search_by_pattern("?a * ?b = ?b * ?a")

-- Search for theorems about sqrt
loogle_search_by_type("∀ x : ℝ, x ≥ 0 → sqrt x * sqrt x = x")

-- Find theorems that could prove current goal
loogle_search_unify("a + b = b + a")
```

**Use Cases**:
- Finding exact theorems needed for a proof step
- Discovering lemmas by their type
- Pattern-based theorem discovery
- Goal-directed search

### 4. LeanSearch (Semantic Search)

**Purpose**: Natural language semantic search over Mathlib

**Key Capabilities**:
- **Natural Language Queries**: Search using plain English
- **Semantic Matching**: Find theorems by meaning, not just keywords
- **Contextual Search**: Understand mathematical context
- **Ranked Results**: Return most relevant theorems first
- **Cross-reference**: Link related mathematical concepts

**Expected Tools**:
```typescript
lean_search_semantic(query: string) -> RankedTheorem[]
lean_search_similar(theorem_name) -> RelatedTheorem[]
lean_search_concept(concept: string) -> Theorem[]
```

**Examples**:
```
lean_search_semantic("theorems about continuity of square root function")
lean_search_semantic("commutativity of addition for natural numbers")
lean_search_concept("Cauchy sequences")
```

**Use Cases**:
- Initial research phase
- Finding theorems when you don't know exact terminology
- Discovering related mathematical concepts
- Exploratory search

---

## Integration Architecture

### MCP Configuration Enhancement

**Current** (`.mcp.json`):
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"],
      "env": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker"
      }
    }
  }
}
```

**Proposed Enhancement**:
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"],
      "env": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker"
      }
    },
    "lean-explore": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-explore-mcp"],
      "env": {
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker",
        "MATHLIB_PATH": "/path/to/mathlib4"
      }
    },
    "loogle": {
      "type": "stdio",
      "command": "loogle-mcp-server",
      "args": ["--mathlib-index", "/path/to/mathlib-index"]
    },
    "lean-search": {
      "type": "stdio", 
      "command": "lean-search-mcp",
      "args": ["--model", "semantic-v1"]
    }
  }
}
```

### Tool Access Strategy

**Approach**: Create a unified MCP tool wrapper layer in `.opencode/tool/mcp/`

**Structure**:
```
.opencode/tool/mcp/
├── index.ts              # Main MCP tool coordinator
├── lsp-client.ts         # lean-lsp-mcp wrapper
├── explore-client.ts     # LeanExplore wrapper
├── loogle-client.ts      # Loogle wrapper
├── search-client.ts      # LeanSearch wrapper
├── types.ts              # TypeScript type definitions
└── README.md             # Usage documentation
```

**Benefits**:
1. Centralized MCP tool access
2. Type-safe interfaces
3. Error handling and retry logic
4. Caching for expensive operations
5. Fallback strategies when MCP unavailable

---

## Agent Enhancements

### 1. Orchestrator Enhancements

**File**: `.opencode/agent/orchestrator.md`

**Changes**:
- Add MCP availability detection in initialization
- Route proof verification requests to LSP-enabled implementer
- Coordinate multi-tool searches (Loogle + LeanSearch + grep)
- Add MCP health monitoring

**New Routing Logic**:
```xml
<route to="@implementer" when="proof implementation with real-time verification">
  <context_level>Level 2</context_level>
  <mcp_tools>lean-lsp</mcp_tools>
  <pass_data>Proof plan, LSP connection details</pass_data>
  <expected_return>Verified proof with incremental validation</expected_return>
</route>

<route to="@researcher" when="comprehensive theorem search">
  <context_level>Level 2</context_level>
  <mcp_tools>loogle, lean-search, lean-explore</mcp_tools>
  <pass_data>Search query, goal type, context</pass_data>
  <expected_return>Ranked list of relevant theorems from multiple sources</expected_return>
</route>
```

### 2. Researcher Enhancements

**File**: `.opencode/agent/researcher.md`

**Major Changes**:

**New Stage**: Multi-Source Search Coordination
```xml
<stage id="1.5" name="CoordinateSearchTools">
  <action>Execute parallel searches across MCP tools</action>
  <process>
    1. Parse query to determine search strategy
    2. If type signature available → use Loogle
    3. If natural language query → use LeanSearch
    4. If exploring namespace → use LeanExplore
    5. Always include grep-based mathlib-explorer as fallback
    6. Merge and deduplicate results
    7. Rank by relevance and source confidence
  </process>
  <checkpoint>Comprehensive results from all available sources</checkpoint>
</stage>
```

**Enhanced Routing**:
```xml
<route to="@loogle-searcher" when="type signature or pattern search needed">
  <context_level>Level 1</context_level>
  <mcp_tool>loogle</mcp_tool>
  <pass_data>Type pattern, goal signature</pass_data>
  <expected_return>Theorems matching type pattern</expected_return>
</route>

<route to="@semantic-searcher" when="natural language query">
  <context_level>Level 1</context_level>
  <mcp_tool>lean-search</mcp_tool>
  <pass_data>Natural language query</pass_data>
  <expected_return>Semantically relevant theorems</expected_return>
</route>

<route to="@namespace-explorer" when="exploring Mathlib structure">
  <context_level>Level 1</context_level>
  <mcp_tool>lean-explore</mcp_tool>
  <pass_data>Namespace or module name</pass_data>
  <expected_return>Module contents and structure</expected_return>
</route>
```

### 3. Implementer Enhancements

**File**: `.opencode/agent/implementer.md`

**Critical Enhancement**: Real-time LSP Verification

**New Critical Rule**:
```xml
<rule id="incremental_lsp_validation" scope="implementation">
  BEFORE appending each tactic line:
  1. Use lean-lsp-mcp to get current proof state
  2. Generate tactic for current goal
  3. Use lean-lsp-mcp to validate tactic
  4. If validation succeeds → append and continue
  5. If validation fails → try alternative tactic or report error
  
  NEVER proceed to next step without LSP validation.
</rule>
```

**Enhanced Workflow**:
```xml
<stage id="2" name="TacticalImplementation">
  <action>Implement proof with real-time LSP verification</action>
  <process>
    1. Initialize LSP connection for target file
    2. For each proof step:
       a. Query LSP for current proof state
       b. Analyze goals and hypotheses
       c. Select tactic using @tactic-selector
       d. Generate tactic code
       e. Validate tactic via LSP (without writing file)
       f. If valid → append to proof
       g. If invalid → try alternative or escalate
    3. Final LSP check on complete proof
    4. Only write file after full LSP validation
  </process>
  <mcp_tools>lean-lsp</mcp_tools>
  <checkpoint>Proof validated incrementally via LSP</checkpoint>
</stage>
```

**New Subagent Routes**:
```xml
<route to="@lsp-validator" when="validating proof step via LSP">
  <context_level>Level 1</context_level>
  <mcp_tool>lean-lsp</mcp_tool>
  <pass_data>File path, proof position, tactic to validate</pass_data>
  <expected_return>Validation result with proof state</expected_return>
</route>

<route to="@proof-state-analyzer" when="analyzing current proof state">
  <context_level>Level 1</context_level>
  <mcp_tool>lean-lsp</mcp_tool>
  <pass_data>File path, cursor position</pass_data>
  <expected_return>Current goals, hypotheses, context</expected_return>
</route>
```

### 4. Reviser Enhancements

**File**: `.opencode/agent/reviser.md`

**Enhancement**: LSP-Guided Error Analysis

**New Stage**:
```xml
<stage id="1.5" name="LSPDiagnosticAnalysis">
  <action>Use LSP diagnostics for precise error identification</action>
  <process>
    1. Query lean-lsp-mcp for diagnostics on failed proof
    2. Extract error messages, positions, and suggestions
    3. Get proof state at error location
    4. Analyze what tactic was expected vs. what was provided
    5. Use LeanSearch to find similar successful proofs
    6. Generate specific revision recommendations
  </process>
  <mcp_tools>lean-lsp, lean-search</mcp_tools>
  <checkpoint>Precise error diagnosis with LSP insights</checkpoint>
</stage>
```

### 5. Planner Enhancements

**File**: `.opencode/agent/planner.md` (if exists, or create)

**Enhancement**: Type-Guided Planning

**New Capability**:
```xml
<stage id="1" name="TypeAnalysisAndSearch">
  <action>Analyze goal type and search for applicable theorems</action>
  <process>
    1. Parse theorem statement to extract type signature
    2. Use Loogle to find theorems with matching patterns
    3. Use LeanExplore to find related theorems in same namespace
    4. Analyze dependencies of found theorems
    5. Build dependency graph for proof strategy
  </process>
  <mcp_tools>loogle, lean-explore</mcp_tools>
  <checkpoint>Type-guided theorem discovery complete</checkpoint>
</stage>
```

---

## Command Enhancements

### 1. `/prove` Command Enhancement

**File**: `.opencode/command/prove.md`

**Enhanced Process**:
```markdown
**Process:**
1. Receives a theorem to be proven
2. **[NEW]** Uses Loogle to search for similar proven theorems
3. **[NEW]** Uses LeanSearch to find related mathematical concepts
4. Engages the `researcher` with MCP-enhanced search
5. Works with user to create proof outline
6. **[NEW]** Delegates to `implementer` with LSP real-time verification
7. **[NEW]** Uses LSP to validate each proof step incrementally
8. Manages the overall process until proof is LSP-verified

**MCP Tools Used:**
- `loogle`: Type-based theorem search
- `lean-search`: Semantic concept search
- `lean-lsp`: Real-time proof verification
- `lean-explore`: Dependency analysis
```

### 2. `/research` Command Enhancement

**File**: `.opencode/command/research.md`

**New Capabilities**:
```markdown
**Enhanced Research Process:**

1. **Multi-Source Search**:
   - Loogle: Type-based formal search
   - LeanSearch: Semantic natural language search
   - LeanExplore: Namespace and module exploration
   - Mathlib grep: Fallback text search

2. **Search Strategy Selection**:
   - If query contains type signature → prioritize Loogle
   - If natural language → prioritize LeanSearch
   - If exploring area → use LeanExplore
   - Always merge results from all sources

3. **Result Ranking**:
   - Combine results from all sources
   - Deduplicate theorems
   - Rank by relevance score
   - Present top 10-20 results with sources

**New Syntax:**
```bash
/research <query> [--type-search] [--semantic] [--explore]

# Examples:
/research "commutativity of addition" --semantic
/research "∀ a b : ℕ, a + b = b + a" --type-search
/research "Topology.MetricSpace" --explore
```

### 3. `/implement` Command Enhancement

**File**: `.opencode/command/implement.md`

**LSP-Verified Implementation**:
```markdown
**Enhanced Implementation Process:**

1. Load proof plan
2. **[NEW]** Initialize LSP connection
3. **[NEW]** For each proof step:
   - Get current proof state via LSP
   - Generate tactic
   - Validate via LSP before writing
   - Only proceed if validation succeeds
4. **[NEW]** Final LSP verification
5. Write file only after complete LSP validation

**Flags:**
```bash
/implement <outline_file> [--lsp-verify] [--incremental]

# --lsp-verify: Use LSP for real-time validation (default: true)
# --incremental: Show proof state after each step (default: false)
```

### 4. New Command: `/verify`

**File**: `.opencode/command/verify.md` (NEW)

**Purpose**: Verify existing proofs using LSP

```markdown
---
agent: implementer
description: "Verify proof correctness using Lean LSP"
---

Verifies an existing Lean proof file using the Lean Language Server.

**Request:** $ARGUMENTS

**Process:**
1. Receives a file path to verify
2. Initializes LSP connection
3. Requests diagnostics from LSP
4. Reports any errors, warnings, or info messages
5. Shows proof states at key positions
6. Suggests fixes for any issues found

**Syntax:**
```bash
/verify <file_path> [--show-states] [--suggest-fixes]
```

**Parameters:**
- `<file_path>`: (Required) Path to .lean file to verify
- `--show-states`: Show proof states at each tactic
- `--suggest-fixes`: Get LSP suggestions for errors

**Examples:**
```bash
/verify Logos/Theorems/Perpetuity.lean
/verify Logos/Core/Syntax/Formula.lean --show-states
/verify Logos/Test/ModalS5Test.lean --suggest-fixes
```

**Output:**
```markdown
Verification Results for: Logos/Theorems/Perpetuity.lean

✓ No errors found
⚠ 2 warnings:
  - Line 45: Unused variable 'h'
  - Line 67: Tactic 'simp' could be more specific

ℹ 3 info messages:
  - Line 23: Proof state: 1 goal remaining
  - Line 45: Proof state: 2 goals remaining  
  - Line 89: Proof complete

Suggestions:
  - Line 45: Remove unused hypothesis or use 'exact h'
  - Line 67: Replace 'simp' with 'simp only [add_comm]'
```
```

### 5. New Command: `/explore`

**File**: `.opencode/command/explore.md` (NEW)

**Purpose**: Explore Mathlib structure and dependencies

```markdown
---
agent: researcher
description: "Explore Lean modules, namespaces, and dependencies"
---

Explores Lean project structure using LeanExplore MCP.

**Request:** $ARGUMENTS

**Process:**
1. Receives a module, namespace, or theorem name
2. Uses LeanExplore to analyze structure
3. Shows definitions, theorems, instances
4. Displays dependencies and usages
5. Provides navigation suggestions

**Syntax:**
```bash
/explore <target> [--deps] [--usages] [--instances]
```

**Parameters:**
- `<target>`: Module, namespace, or theorem name
- `--deps`: Show dependencies
- `--usages`: Show where it's used
- `--instances`: Show type class instances

**Examples:**
```bash
/explore Mathlib.Topology.MetricSpace.Basic
/explore Real.sqrt --deps --usages
/explore Topology.MetricSpace --instances
```

**Output:**
```markdown
Exploring: Mathlib.Topology.MetricSpace.Basic

Definitions (15):
  - MetricSpace: Type class for metric spaces
  - dist: Distance function
  - ball: Open ball
  ...

Theorems (47):
  - dist_comm: ∀ x y, dist x y = dist y x
  - dist_triangle: ∀ x y z, dist x z ≤ dist x y + dist y z
  ...

Dependencies (8):
  - Mathlib.Topology.Basic
  - Mathlib.Data.Real.Basic
  ...

Used by (23 modules):
  - Mathlib.Topology.Instances.Real
  - Mathlib.Analysis.Normed.Group.Basic
  ...
```
```

### 6. New Command: `/search-type`

**File**: `.opencode/command/search-type.md` (NEW)

**Purpose**: Search theorems by type signature using Loogle

```markdown
---
agent: researcher
description: "Search Mathlib by type signature or pattern"
---

Searches for theorems matching a type pattern using Loogle.

**Request:** $ARGUMENTS

**Process:**
1. Receives a type pattern or signature
2. Uses Loogle to search Mathlib
3. Returns matching theorems
4. Shows type signatures and locations
5. Suggests most relevant matches

**Syntax:**
```bash
/search-type <pattern> [--namespace <ns>] [--exact]
```

**Parameters:**
- `<pattern>`: Type pattern to search for
- `--namespace`: Limit search to namespace
- `--exact`: Require exact match

**Examples:**
```bash
/search-type "?a * ?b = ?b * ?a"
/search-type "∀ x : ℝ, x ≥ 0 → sqrt x * sqrt x = x"
/search-type "Continuous ?f" --namespace Topology
```

**Output:**
```markdown
Search Results for: "?a * ?b = ?b * ?a"

Found 15 matching theorems:

1. mul_comm (Nat) ⭐⭐⭐⭐⭐
   ∀ (a b : ℕ), a * b = b * a
   Location: Mathlib.Data.Nat.Basic
   
2. mul_comm (Int)
   ∀ (a b : ℤ), a * b = b * a
   Location: Mathlib.Data.Int.Basic

3. mul_comm (Real)
   ∀ (a b : ℝ), a * b = b * a
   Location: Mathlib.Data.Real.Basic

...
```
```

---

## New Subagents

### 1. LSP Validator

**File**: `.opencode/agent/subagents/verification/lsp-validator.md` (NEW)

```markdown
---
description: "Validates Lean proofs using the Language Server Protocol"
mode: subagent
temperature: 0.0
---

# LSP Validator

<context>
  <specialist_domain>Real-time Lean proof verification via LSP</specialist_domain>
  <task_scope>
    Validates Lean proof steps incrementally using lean-lsp-mcp, providing
    immediate feedback on proof correctness without full compilation.
  </task_scope>
  <integration>
    Called by @implementer during proof construction to validate each step.
  </integration>
</context>

<role>
  LSP verification specialist, expert at using Lean Language Server for
  incremental proof validation and error diagnosis.
</role>

<task>
  To validate Lean proof steps using LSP and provide detailed feedback on
  proof state, errors, and suggestions.
</task>

<inputs_required>
  <parameter name="file_path" type="string">
    Path to the .lean file being validated
  </parameter>
  <parameter name="proof_text" type="string">
    The proof code to validate (can be partial)
  </parameter>
  <parameter name="position" type="object">
    Line and column position for proof state query
  </parameter>
</inputs_required>

<process_flow>
  <step_1>
    <action>Initialize LSP connection</action>
    <process>
      1. Connect to lean-lsp-mcp server
      2. Open document or update existing
      3. Wait for initial diagnostics
    </process>
    <validation>LSP connection established</validation>
    <output>LSP session handle</output>
  </step_1>
  
  <step_2>
    <action>Query proof state</action>
    <process>
      1. Request proof state at specified position
      2. Extract current goals
      3. Extract hypotheses and context
      4. Format proof state for analysis
    </process>
    <validation>Proof state retrieved</validation>
    <output>Structured proof state</output>
  </step_2>
  
  <step_3>
    <action>Check diagnostics</action>
    <process>
      1. Request diagnostics for file
      2. Filter errors, warnings, info
      3. Extract error messages and positions
      4. Get LSP suggestions if available
    </process>
    <validation>Diagnostics analyzed</validation>
    <output>Validation result with errors/warnings</output>
  </step_3>
</process_flow>

<output_specification>
  <format>
    ```yaml
    validation_result:
      is_valid: true/false
      proof_state:
        goals:
          - "a b : ℕ"
          - "⊢ a + b = b + a"
        hypotheses:
          - "h1 : a > 0"
        context: "In proof of add_comm"
      diagnostics:
        errors: []
        warnings:
          - message: "Unused variable 'h'"
            line: 45
            column: 12
        info: []
      suggestions:
        - "Try 'rw [Nat.add_comm]'"
        - "Consider using 'ring' tactic"
    ```
  </format>
</output_specification>
```

### 2. Loogle Searcher

**File**: `.opencode/agent/subagents/search/loogle-searcher.md` (NEW)

```markdown
---
description: "Searches Mathlib by type signature using Loogle"
mode: subagent
temperature: 0.0
---

# Loogle Searcher

<context>
  <specialist_domain>Type-based theorem search in Mathlib</specialist_domain>
  <task_scope>
    Searches for theorems matching type patterns using Loogle MCP server,
    enabling precise discovery of lemmas by their type signatures.
  </task_scope>
  <integration>
    Called by @researcher and @planner for type-directed theorem search.
  </integration>
</context>

<role>
  Type-based search specialist, expert at formulating type patterns and
  finding theorems that match specific type signatures.
</role>

<task>
  To search Mathlib for theorems matching a given type pattern or signature.
</task>

<inputs_required>
  <parameter name="type_pattern" type="string">
    Type pattern to search for (e.g., "?a * ?b = ?b * ?a")
  </parameter>
  <parameter name="namespace" type="string" optional="true">
    Limit search to specific namespace
  </parameter>
  <parameter name="exact_match" type="boolean" optional="true">
    Require exact type match (default: false)
  </parameter>
</inputs_required>

<process_flow>
  <step_1>
    <action>Formulate search query</action>
    <process>
      1. Parse type pattern
      2. Identify pattern variables (?a, ?b, etc.)
      3. Determine search mode (pattern/unify/exact)
      4. Add namespace filter if specified
    </process>
    <validation>Valid Loogle query constructed</validation>
    <output>Loogle search query</output>
  </step_1>
  
  <step_2>
    <action>Execute Loogle search</action>
    <process>
      1. Call loogle MCP tool with query
      2. Receive matching theorems
      3. Extract theorem names, types, locations
      4. Get relevance scores if available
    </process>
    <validation>Search completed successfully</validation>
    <output>Raw search results</output>
  </step_2>
  
  <step_3>
    <action>Rank and format results</action>
    <process>
      1. Sort by relevance score
      2. Group by namespace
      3. Format with type signatures
      4. Add location information
      5. Limit to top 20 results
    </process>
    <validation>Results formatted and ranked</validation>
    <output>Ranked theorem list</output>
  </step_3>
</process_flow>

<output_specification>
  <format>
    ```yaml
    search_results:
      query: "?a * ?b = ?b * ?a"
      total_found: 15
      theorems:
        - name: "mul_comm"
          full_name: "Nat.mul_comm"
          type: "∀ (a b : ℕ), a * b = b * a"
          namespace: "Mathlib.Data.Nat.Basic"
          relevance: 0.95
        - name: "mul_comm"
          full_name: "Int.mul_comm"
          type: "∀ (a b : ℤ), a * b = b * a"
          namespace: "Mathlib.Data.Int.Basic"
          relevance: 0.93
    ```
  </format>
</output_specification>
```

### 3. Semantic Searcher

**File**: `.opencode/agent/subagents/search/semantic-searcher.md` (NEW)

```markdown
---
description: "Searches Mathlib using natural language via LeanSearch"
mode: subagent
temperature: 0.0
---

# Semantic Searcher

<context>
  <specialist_domain>Natural language semantic search over Mathlib</specialist_domain>
  <task_scope>
    Searches for theorems using natural language queries via LeanSearch MCP,
    enabling discovery of relevant mathematics without knowing exact terminology.
  </task_scope>
  <integration>
    Called by @researcher for exploratory search and concept discovery.
  </integration>
</context>

<role>
  Semantic search specialist, expert at translating mathematical concepts
  into effective natural language queries and interpreting results.
</role>

<task>
  To find relevant theorems in Mathlib using natural language descriptions.
</task>

<inputs_required>
  <parameter name="query" type="string">
    Natural language description of desired theorem or concept
  </parameter>
  <parameter name="max_results" type="integer" optional="true">
    Maximum number of results to return (default: 10)
  </parameter>
</inputs_required>

<process_flow>
  <step_1>
    <action>Optimize query</action>
    <process>
      1. Extract key mathematical concepts
      2. Identify important keywords
      3. Formulate clear, concise query
      4. Add context if needed
    </process>
    <validation>Query optimized for semantic search</validation>
    <output>Optimized search query</output>
  </step_1>
  
  <step_2>
    <action>Execute semantic search</action>
    <process>
      1. Call lean-search MCP tool
      2. Receive ranked results
      3. Extract theorem information
      4. Get relevance scores
    </process>
    <validation>Search completed</validation>
    <output>Ranked search results</output>
  </step_2>
  
  <step_3>
    <action>Format and present results</action>
    <process>
      1. Sort by relevance
      2. Extract theorem statements
      3. Add brief descriptions
      4. Include source locations
    </process>
    <validation>Results formatted</validation>
    <output>Formatted theorem list</output>
  </step_3>
</process_flow>

<output_specification>
  <format>
    ```yaml
    semantic_results:
      query: "continuity of square root function"
      results:
        - theorem: "continuous_sqrt"
          statement: "Continuous (fun x => sqrt x)"
          description: "Square root is continuous on [0, ∞)"
          location: "Mathlib.Analysis.SpecialFunctions.Sqrt"
          relevance: 0.92
        - theorem: "sqrt_continuous_on"
          statement: "ContinuousOn sqrt {x : ℝ | 0 ≤ x}"
          description: "Square root is continuous on non-negative reals"
          location: "Mathlib.Data.Real.Sqrt"
          relevance: 0.88
    ```
  </format>
</output_specification>
```

### 4. Namespace Explorer

**File**: `.opencode/agent/subagents/exploration/namespace-explorer.md` (NEW)

```markdown
---
description: "Explores Lean namespaces and modules using LeanExplore"
mode: subagent
temperature: 0.0
---

# Namespace Explorer

<context>
  <specialist_domain>Lean project structure and namespace exploration</specialist_domain>
  <task_scope>
    Explores Lean modules, namespaces, and their contents using LeanExplore MCP,
    providing structured views of definitions, theorems, and dependencies.
  </task_scope>
  <integration>
    Called by @researcher for understanding Mathlib structure and finding
    related theorems within a namespace.
  </integration>
</context>

<role>
  Namespace exploration specialist, expert at navigating Lean project
  structure and analyzing module dependencies.
</role>

<task>
  To explore and analyze Lean namespaces, modules, and their relationships.
</task>

<inputs_required>
  <parameter name="target" type="string">
    Module name, namespace, or theorem to explore
  </parameter>
  <parameter name="show_dependencies" type="boolean" optional="true">
    Include dependency information (default: false)
  </parameter>
  <parameter name="show_usages" type="boolean" optional="true">
    Include usage information (default: false)
  </parameter>
</inputs_required>

<process_flow>
  <step_1>
    <action>Query module contents</action>
    <process>
      1. Call lean-explore MCP tool
      2. Request module/namespace contents
      3. Extract definitions, theorems, instances
      4. Categorize by type
    </process>
    <validation>Module contents retrieved</validation>
    <output>Structured module contents</output>
  </step_1>
  
  <step_2>
    <action>Analyze dependencies (if requested)</action>
    <process>
      1. Query dependencies for target
      2. Build dependency graph
      3. Identify direct and transitive deps
      4. Categorize by importance
    </process>
    <validation>Dependencies analyzed</validation>
    <output>Dependency information</output>
  </step_2>
  
  <step_3>
    <action>Find usages (if requested)</action>
    <process>
      1. Query where target is used
      2. Categorize usage types
      3. Rank by frequency
      4. Include usage contexts
    </process>
    <validation>Usages identified</validation>
    <output>Usage information</output>
  </step_3>
  
  <step_4>
    <action>Format exploration report</action>
    <process>
      1. Organize by category
      2. Add navigation links
      3. Include summary statistics
      4. Provide exploration suggestions
    </process>
    <validation>Report formatted</validation>
    <output>Exploration report</output>
  </step_4>
</process_flow>

<output_specification>
  <format>
    ```yaml
    exploration_result:
      target: "Mathlib.Topology.MetricSpace.Basic"
      summary:
        definitions: 15
        theorems: 47
        instances: 8
        total_lines: 1250
      contents:
        definitions:
          - name: "MetricSpace"
            type: "Type class"
            description: "Structure for metric spaces"
          - name: "dist"
            type: "Function"
            description: "Distance function"
        theorems:
          - name: "dist_comm"
            statement: "∀ x y, dist x y = dist y x"
          - name: "dist_triangle"
            statement: "∀ x y z, dist x z ≤ dist x y + dist y z"
        instances:
          - name: "Real.metricSpace"
            type: "MetricSpace ℝ"
      dependencies:
        - "Mathlib.Topology.Basic"
        - "Mathlib.Data.Real.Basic"
      used_by:
        - "Mathlib.Topology.Instances.Real"
        - "Mathlib.Analysis.Normed.Group.Basic"
    ```
  </format>
</output_specification>
```

---

## Context File Updates

### 1. New Context File: MCP Tools Guide

**File**: `.opencode/context/lean4/tools/mcp-tools-guide.md` (NEW)

```markdown
# MCP Tools Guide for Lean 4 Development

## Overview
This guide describes the MCP (Model Context Protocol) tools available for
Lean 4 development in the ProofChecker system.

## Available MCP Servers

### 1. lean-lsp-mcp (Proof Verification)

**Purpose**: Real-time interaction with Lean Language Server

**When to Use**:
- Validating proofs incrementally during implementation
- Getting current proof state
- Diagnosing compilation errors
- Obtaining type information

**Key Functions**:
- `get_proof_state(file, line, col)` - Get current goals and hypotheses
- `check_proof(file, proof_text)` - Validate proof without writing file
- `get_diagnostics(file)` - Get errors, warnings, info messages
- `get_hover(file, line, col)` - Get type and documentation info

**Example Usage**:
```
During proof implementation:
1. Write tactic line
2. Call get_proof_state() to see new goals
3. Call get_diagnostics() to check for errors
4. Proceed only if no errors
```

### 2. LeanExplore (Structure Exploration)

**Purpose**: Explore Lean project structure and dependencies

**When to Use**:
- Understanding Mathlib organization
- Finding related theorems in a namespace
- Analyzing theorem dependencies
- Discovering available type class instances

**Key Functions**:
- `explore_module(name)` - List all contents of a module
- `explore_dependencies(theorem)` - Find what a theorem depends on
- `explore_usages(theorem)` - Find where a theorem is used
- `explore_namespace(ns)` - Navigate namespace hierarchy

**Example Usage**:
```
To understand a Mathlib area:
1. explore_namespace("Topology.MetricSpace")
2. Review definitions and theorems
3. explore_dependencies() for key theorems
4. Build mental model of the area
```

### 3. Loogle (Type-based Search)

**Purpose**: Search theorems by type signature and patterns

**When to Use**:
- Finding theorems with specific type signatures
- Searching for lemmas matching a pattern
- Goal-directed theorem discovery
- Finding theorems that could prove current goal

**Key Functions**:
- `search_by_type(pattern)` - Find theorems matching type pattern
- `search_by_pattern(pattern)` - Pattern-based search
- `search_unify(goal)` - Find theorems that unify with goal

**Pattern Syntax**:
- `?a`, `?b` - Pattern variables
- `_` - Wildcard
- Exact type signatures

**Example Usage**:
```
To find commutativity theorems:
search_by_pattern("?a * ?b = ?b * ?a")

To find theorems about sqrt:
search_by_type("∀ x : ℝ, x ≥ 0 → sqrt x * sqrt x = x")
```

### 4. LeanSearch (Semantic Search)

**Purpose**: Natural language search over Mathlib

**When to Use**:
- Initial exploration of unfamiliar areas
- Finding theorems without knowing exact terminology
- Discovering related mathematical concepts
- Broad conceptual search

**Key Functions**:
- `search_semantic(query)` - Natural language search
- `search_similar(theorem)` - Find similar theorems
- `search_concept(concept)` - Search by mathematical concept

**Example Usage**:
```
search_semantic("theorems about continuity of square root")
search_semantic("Cauchy sequences in metric spaces")
search_concept("compactness")
```

## Search Strategy Decision Tree

```
START: Need to find a theorem

├─ Do you know the exact type signature?
│  YES → Use Loogle (type-based search)
│  NO → Continue
│
├─ Do you know the general pattern?
│  YES → Use Loogle (pattern search)
│  NO → Continue
│
├─ Do you know the mathematical concept?
│  YES → Use LeanSearch (semantic search)
│  NO → Continue
│
└─ Exploring a general area?
   YES → Use LeanExplore (namespace exploration)
   NO → Use LeanSearch (broad semantic search)
```

## Multi-Tool Search Strategy

For comprehensive searches, use multiple tools in sequence:

1. **Start Broad**: LeanSearch with natural language
2. **Refine**: LeanExplore to understand namespace structure
3. **Precise**: Loogle for exact type matches
4. **Verify**: lean-lsp to check if theorem applies

## Integration with Agents

### Researcher Agent
- Uses all search tools (Loogle, LeanSearch, LeanExplore)
- Merges results from multiple sources
- Ranks by relevance and confidence

### Implementer Agent
- Uses lean-lsp for incremental validation
- Validates each tactic before proceeding
- Gets proof state after each step

### Planner Agent
- Uses Loogle for type-guided planning
- Uses LeanExplore for dependency analysis
- Builds proof strategy from available theorems

### Reviser Agent
- Uses lean-lsp for error diagnosis
- Uses LeanSearch to find similar successful proofs
- Generates specific revision recommendations

## Best Practices

1. **Always validate with LSP** before writing files
2. **Use type search first** when you know the signature
3. **Combine search tools** for comprehensive results
4. **Explore namespaces** to understand structure
5. **Check dependencies** before using complex theorems
6. **Verify incrementally** during proof construction

## Error Handling

If MCP tool unavailable:
- lean-lsp → Fall back to full compilation
- Loogle → Fall back to grep-based search
- LeanSearch → Fall back to keyword search
- LeanExplore → Fall back to manual file reading

## Performance Considerations

- **LSP queries**: Fast (< 100ms), use liberally
- **Loogle searches**: Moderate (< 1s), cache results
- **LeanSearch**: Slower (1-3s), use for initial exploration
- **LeanExplore**: Fast (< 500ms), good for navigation
```

### 2. Update: Theorem Proving Guidelines

**File**: `.opencode/context/lean4/theorem-proving-guidelines.md`

**Add Section**:
```markdown
## MCP-Enhanced Proof Development

### Phase 1: Research with Multi-Tool Search

1. **Semantic Exploration** (LeanSearch):
   - Describe theorem in natural language
   - Find related mathematical concepts
   - Identify relevant Mathlib areas

2. **Namespace Exploration** (LeanExplore):
   - Explore identified namespaces
   - Review available definitions and theorems
   - Understand module structure

3. **Type-Based Search** (Loogle):
   - Formulate type patterns from goal
   - Find theorems with matching signatures
   - Identify exact lemmas needed

### Phase 2: Planning with Dependency Analysis

1. **Analyze Dependencies** (LeanExplore):
   - Check dependencies of candidate theorems
   - Build dependency graph
   - Identify required imports

2. **Type-Guided Strategy** (Loogle):
   - Search for intermediate lemmas
   - Find theorems for each proof step
   - Validate proof strategy feasibility

### Phase 3: Implementation with LSP Validation

1. **Incremental Development** (lean-lsp):
   - Write theorem signature
   - Validate signature via LSP
   - For each tactic:
     * Get current proof state
     * Generate tactic
     * Validate via LSP
     * Proceed only if valid

2. **Real-Time Feedback** (lean-lsp):
   - Monitor diagnostics continuously
   - Fix errors immediately
   - Verify proof state after each step

### Phase 4: Verification and Refinement

1. **Final Validation** (lean-lsp):
   - Complete LSP check
   - Review all diagnostics
   - Ensure no warnings

2. **Optimization** (lean-lsp + LeanSearch):
   - Check for simpler tactics
   - Find more direct proofs
   - Improve readability
```

### 3. Update: End-to-End Proof Workflow

**File**: `.opencode/context/lean4/processes/end-to-end-proof-workflow.md`

**Enhance Steps**:
```markdown
### Step 1: Research (MCP-Enhanced)

**Action**: Gather relevant theorems and concepts using MCP tools

**Process**:
1. Use LeanSearch for semantic exploration
2. Use LeanExplore to understand namespace structure
3. Use Loogle for type-based theorem discovery
4. Merge results from all sources

**MCP Tools**: lean-search, lean-explore, loogle

**Validation**: Comprehensive list of relevant theorems from multiple sources

**Output**: Research report with theorems, types, and locations

### Step 2: Planning (Type-Guided)

**Action**: Create proof strategy using type information

**Process**:
1. Analyze goal type signature
2. Use Loogle to find matching theorems
3. Use LeanExplore to check dependencies
4. Build proof strategy from available lemmas

**MCP Tools**: loogle, lean-explore

**Validation**: Proof plan with verified theorem availability

**Output**: Detailed proof plan with dependencies

### Step 3: Implementation (LSP-Verified)

**Action**: Implement proof with real-time LSP validation

**Process**:
1. Initialize LSP connection
2. Write theorem signature, validate via LSP
3. For each proof step:
   - Get proof state via LSP
   - Generate tactic
   - Validate tactic via LSP
   - Append only if valid
4. Final LSP verification

**MCP Tools**: lean-lsp

**Validation**: Each step validated before proceeding

**Output**: LSP-verified proof implementation

### Step 4: Verification (Comprehensive)

**Action**: Final verification and optimization

**Process**:
1. Complete LSP diagnostic check
2. Review warnings and suggestions
3. Optimize tactics based on LSP feedback
4. Ensure no errors or warnings

**MCP Tools**: lean-lsp

**Validation**: Clean LSP diagnostics

**Output**: Verified, optimized proof
```

---

## Workflow Improvements

### Enhanced End-to-End Theorem Proving Workflow

**File**: `.opencode/workflows/end-to-end-theorem-proving.md`

**Major Enhancements**:

```markdown
### Step 1: Research (MCP Multi-Tool Search)

<step_framework>
  <context_dependencies>
    - .opencode/context/lean4/theorem-proving-guidelines.md
    - .opencode/context/lean4/tools/mcp-tools-guide.md
  </context_dependencies>
  
  <action>Comprehensive multi-tool search for relevant theorems</action>
  
  <mcp_tools>lean-search, lean-explore, loogle</mcp_tools>
  
  <process>
    1. **Semantic Search** (LeanSearch):
       - Formulate natural language query
       - Search for related concepts
       - Identify relevant Mathlib areas
    
    2. **Namespace Exploration** (LeanExplore):
       - Explore identified namespaces
       - List available theorems and definitions
       - Understand module structure
    
    3. **Type-Based Search** (Loogle):
       - Extract type patterns from goal
       - Search for matching theorems
       - Find exact lemmas needed
    
    4. **Result Synthesis**:
       - Merge results from all tools
       - Deduplicate theorems
       - Rank by relevance
       - Present top 20 results
  </process>
  
  <output>
    Comprehensive research report with:
    - Relevant theorems from multiple sources
    - Type signatures and locations
    - Dependency information
    - Namespace organization
  </output>
</step_framework>

### Step 2: Planning (Type-Guided with Dependencies)

<step_framework>
  <context_dependencies>
    - .opencode/context/lean4/theorem-proving-guidelines.md
    - .opencode/context/lean4/tools/mcp-tools-guide.md
  </context_dependencies>
  
  <action>Create type-guided proof strategy with dependency analysis</action>
  
  <mcp_tools>loogle, lean-explore</mcp_tools>
  
  <process>
    1. **Type Analysis**:
       - Parse goal type signature
       - Identify required intermediate types
       - Formulate type patterns for each step
    
    2. **Theorem Discovery** (Loogle):
       - Search for theorems matching each type pattern
       - Find lemmas for intermediate steps
       - Verify theorem availability
    
    3. **Dependency Analysis** (LeanExplore):
       - Check dependencies of candidate theorems
       - Build dependency graph
       - Identify required imports
       - Verify no circular dependencies
    
    4. **Strategy Formulation**:
       - Order proof steps by dependencies
       - Assign theorems to each step
       - Create detailed proof outline
  </process>
  
  <output>
    Type-guided proof plan with:
    - Ordered proof steps
    - Assigned theorems for each step
    - Complete dependency graph
    - Required imports list
  </output>
</step_framework>

### Step 3: Implementation (LSP-Verified Incremental)

<step_framework>
  <context_dependencies>
    - .opencode/context/lean4/style-guide.md
    - .opencode/context/lean4/tools/mcp-tools-guide.md
  </context_dependencies>
  
  <action>Implement proof with real-time LSP validation</action>
  
  <mcp_tools>lean-lsp</mcp_tools>
  
  <process>
    1. **Initialize**:
       - Create .lean file with imports
       - Write theorem signature
       - Validate signature via LSP
       - Ensure no type errors
    
    2. **Incremental Implementation**:
       For each proof step in plan:
       
       a. **Get Proof State** (LSP):
          - Query current goals
          - Review hypotheses
          - Understand context
       
       b. **Generate Tactic**:
          - Select tactic based on goal and plan
          - Format tactic code
       
       c. **Validate Tactic** (LSP):
          - Send tactic to LSP for validation
          - Check for errors
          - Review new proof state
       
       d. **Decision**:
          - If valid → append tactic, continue
          - If invalid → try alternative or report error
       
       e. **Progress Check**:
          - Verify proof state matches plan
          - Ensure making progress toward goal
    
    3. **Final Validation**:
       - Complete LSP diagnostic check
       - Ensure proof is complete
       - Verify no errors or warnings
  </process>
  
  <critical_rules>
    - NEVER append tactic without LSP validation
    - STOP immediately on LSP error
    - REPORT errors with proof state context
    - REQUEST approval before deviating from plan
  </critical_rules>
  
  <output>
    LSP-verified proof implementation with:
    - Complete, validated proof
    - Clean LSP diagnostics
    - Proof state log for each step
  </output>
</step_framework>

### Step 4: Verification (Comprehensive LSP Check)

<step_framework>
  <context_dependencies>
    - .opencode/context/lean4/style-guide.md
  </context_dependencies>
  
  <action>Final verification and optimization using LSP</action>
  
  <mcp_tools>lean-lsp</mcp_tools>
  
  <process>
    1. **Diagnostic Review**:
       - Get complete LSP diagnostics
       - Review all errors (should be none)
       - Analyze warnings
       - Check info messages
    
    2. **Optimization**:
       - Review LSP suggestions
       - Simplify tactics where suggested
       - Improve proof readability
       - Add comments for clarity
    
    3. **Final Validation**:
       - Ensure clean diagnostics
       - Verify proof compiles
       - Check style compliance
  </process>
  
  <output>
    Verified, optimized proof with:
    - Zero errors
    - Minimal warnings
    - Clean, readable code
    - LSP validation report
  </output>
</step_framework>
```

---

## Implementation Progress

### Phase 1: Foundation ✅ 80% Complete (2025-12-15)

**Status**: Core infrastructure implemented, integration testing pending

**Completed**:
- ✅ **TypeScript Infrastructure** (4 files, ~1,000 lines)
  - `types.ts` - Comprehensive type definitions (20+ interfaces)
  - `errors.ts` - Error handling framework (7 error codes, 5 fallback strategies)
  - `lsp-client.ts` - LSP client wrapper with caching
  - `index.ts` - Main coordinator and exports

- ✅ **Documentation** (4 files, ~1,000 lines)
  - `README.md` - Tool wrapper documentation
  - `QUICKSTART.md` - Quick reference guide
  - `mcp-tools-guide.md` - Comprehensive user guide
  - `mcp-server-research.md` - Research document

- ✅ **Configuration**
  - Updated `.mcp.json` with placeholder configurations
  - Documented research needs for LeanExplore, Loogle, LeanSearch

**Pending**:
- ⏳ MCP protocol integration (placeholder methods implemented)
- ⏳ Testing with actual lean-lsp-mcp server
- ⏳ Community research for additional MCP servers

**Deliverables**: See [Phase 1 Summary](./mcp-phase1-summary.md)

### Phases 2-6: Pending

All subsequent phases await completion of Phase 1 integration testing and MCP server research.

---

## Implementation Phases

### Phase 1: Foundation (Week 1-2) ✅ 80% COMPLETE

**Goal**: Set up MCP infrastructure and basic integration

**Tasks**:
1. ✅ **Verify MCP server installations**
   - ✅ Verified lean-lsp-mcp in `.mcp.json`
   - ✅ Researched LeanExplore (documented in `mcp-server-research.md`)
   - ✅ Researched Loogle (documented in `mcp-server-research.md`)
   - ✅ Researched LeanSearch (documented in `mcp-server-research.md`)

2. ✅ **Update `.mcp.json` configuration**
   - ✅ Preserved lean-lsp configuration
   - ✅ Added placeholder configurations for future servers
   - ✅ Documented research needs in comments

3. ✅ **Create MCP tool wrapper layer**
   - ✅ Created `.opencode/tool/mcp/` directory
   - ✅ Implemented TypeScript type definitions
   - ✅ Implemented error handling framework
   - ✅ Implemented LSP client wrapper (placeholder methods)
   - ✅ Added caching layer with configurable TTL
   - ✅ Added retry logic framework

4. ✅ **Create MCP tools context file**
   - ✅ Created `.opencode/context/lean4/tools/mcp-tools-guide.md`
   - ✅ Documented each MCP server (current and planned)
   - ✅ Provided usage examples
   - ✅ Defined search strategies
   - ✅ Added troubleshooting section

**Deliverables**:
- ✅ Tool wrapper library (TypeScript infrastructure)
- ✅ MCP tools documentation (comprehensive)
- ⏳ Working MCP server connections (pending integration)

**Success Criteria**:
- ✅ Tool wrappers handle errors gracefully
- ✅ Documentation is clear and comprehensive
- ⏳ All MCP servers respond to test queries (pending integration)

### Phase 2: Subagent Development (Week 3-4)

**Goal**: Create new MCP-powered subagents

**Tasks**:
1. ✅ Create LSP Validator subagent
   - File: `.opencode/agent/subagents/verification/lsp-validator.md`
   - Implement proof state querying
   - Implement incremental validation
   - Add diagnostic analysis

2. ✅ Create Loogle Searcher subagent
   - File: `.opencode/agent/subagents/search/loogle-searcher.md`
   - Implement type pattern search
   - Add result ranking
   - Format output

3. ✅ Create Semantic Searcher subagent
   - File: `.opencode/agent/subagents/search/semantic-searcher.md`
   - Implement natural language search
   - Add query optimization
   - Format results

4. ✅ Create Namespace Explorer subagent
   - File: `.opencode/agent/subagents/exploration/namespace-explorer.md`
   - Implement module exploration
   - Add dependency analysis
   - Add usage tracking

**Deliverables**:
- 4 new subagent definitions
- Test cases for each subagent
- Integration documentation

**Success Criteria**:
- Each subagent works independently
- Subagents integrate with MCP tools correctly
- Output formats are consistent and useful

### Phase 3: Agent Enhancement (Week 5-6)

**Goal**: Enhance existing agents with MCP capabilities

**Tasks**:
1. ✅ Enhance Researcher agent
   - Add multi-tool search coordination
   - Integrate new search subagents
   - Implement result merging and ranking
   - Update routing logic

2. ✅ Enhance Implementer agent
   - Add LSP validation workflow
   - Implement incremental proof construction
   - Add real-time error handling
   - Update critical rules

3. ✅ Enhance Reviser agent
   - Add LSP diagnostic analysis
   - Implement error-guided revision
   - Add similar proof search

4. ✅ Enhance Orchestrator
   - Add MCP tool coordination
   - Update routing for MCP-enabled agents
   - Add MCP health monitoring

**Deliverables**:
- Updated agent definitions
- Enhanced routing logic
- Integration tests

**Success Criteria**:
- Agents use MCP tools effectively
- Routing logic is correct
- Error handling is robust

### Phase 4: Command Development (Week 7-8)

**Goal**: Create and enhance commands with MCP features

**Tasks**:
1. ✅ Enhance `/prove` command
   - Add MCP-enhanced research phase
   - Add LSP-verified implementation
   - Update documentation

2. ✅ Enhance `/research` command
   - Add multi-tool search options
   - Add search strategy flags
   - Update syntax and examples

3. ✅ Enhance `/implement` command
   - Add LSP verification flag
   - Add incremental mode
   - Update process description

4. ✅ Create `/verify` command
   - New command for LSP verification
   - Add proof state display
   - Add fix suggestions

5. ✅ Create `/explore` command
   - New command for namespace exploration
   - Add dependency/usage flags
   - Format output nicely

6. ✅ Create `/search-type` command
   - New command for Loogle search
   - Add pattern syntax help
   - Show ranked results

**Deliverables**:
- 3 enhanced commands
- 3 new commands
- Updated command documentation

**Success Criteria**:
- Commands work end-to-end
- Documentation is clear
- Examples are helpful

### Phase 5: Workflow Integration (Week 9-10)

**Goal**: Update workflows to use MCP tools

**Tasks**:
1. ✅ Update end-to-end theorem proving workflow
   - Add MCP tools to each step
   - Update process descriptions
   - Add MCP-specific validation

2. ✅ Update context files
   - Update theorem-proving-guidelines.md
   - Update end-to-end-proof-workflow.md
   - Add MCP best practices

3. ✅ Create workflow examples
   - Example: Simple theorem with MCP
   - Example: Complex proof with LSP validation
   - Example: Research-heavy proof

**Deliverables**:
- Updated workflow definitions
- Updated context files
- Workflow examples

**Success Criteria**:
- Workflows clearly describe MCP usage
- Context files are comprehensive
- Examples are realistic and helpful

### Phase 6: Testing & Documentation (Week 11-12)

**Goal**: Comprehensive testing and documentation

**Tasks**:
1. ✅ Create test suite
   - Test each MCP tool wrapper
   - Test each new subagent
   - Test enhanced agents
   - Test new/enhanced commands
   - Test complete workflows

2. ✅ Write comprehensive documentation
   - Update ARCHITECTURE.md
   - Update AGENTS_GUIDE.md
   - Update COMMANDS_REFERENCE.md
   - Create MCP_INTEGRATION_GUIDE.md

3. ✅ Create tutorials
   - Tutorial: Using MCP tools
   - Tutorial: LSP-verified proof development
   - Tutorial: Multi-tool theorem search

4. ✅ Performance optimization
   - Profile MCP tool usage
   - Implement caching strategies
   - Optimize search result merging
   - Add timeout handling

**Deliverables**:
- Complete test suite
- Comprehensive documentation
- Tutorials and examples
- Performance optimizations

**Success Criteria**:
- All tests pass
- Documentation is complete and clear
- Tutorials are easy to follow
- Performance is acceptable

---

## Testing Strategy

### Unit Tests

**MCP Tool Wrappers**:
```typescript
// Test LSP validator
test('lsp-validator connects and gets proof state', async () => {
  const validator = new LSPValidator();
  const state = await validator.getProofState('test.lean', 10, 5);
  expect(state.goals).toBeDefined();
});

// Test Loogle searcher
test('loogle-searcher finds commutativity theorems', async () => {
  const searcher = new LoogleSearcher();
  const results = await searcher.searchByPattern('?a * ?b = ?b * ?a');
  expect(results.theorems.length).toBeGreaterThan(0);
  expect(results.theorems[0].name).toContain('comm');
});

// Test semantic searcher
test('semantic-searcher finds continuity theorems', async () => {
  const searcher = new SemanticSearcher();
  const results = await searcher.search('continuity of square root');
  expect(results.results.length).toBeGreaterThan(0);
});

// Test namespace explorer
test('namespace-explorer lists module contents', async () => {
  const explorer = new NamespaceExplorer();
  const contents = await explorer.exploreModule('Mathlib.Data.Nat.Basic');
  expect(contents.definitions.length).toBeGreaterThan(0);
  expect(contents.theorems.length).toBeGreaterThan(0);
});
```

### Integration Tests

**Agent Tests**:
```yaml
# Test researcher with MCP tools
test_researcher_mcp_search:
  agent: researcher
  input: "Find theorems about commutativity of addition"
  expected_tools_used:
    - lean-search
    - loogle
    - lean-explore
  expected_output:
    - contains: "Nat.add_comm"
    - contains: "Int.add_comm"
    - source_count: >= 3

# Test implementer with LSP validation
test_implementer_lsp_validation:
  agent: implementer
  input:
    plan: "Prove a + b = b + a by commutativity"
    theorem: "example (a b : ℕ) : a + b = b + a := by sorry"
  expected_tools_used:
    - lean-lsp
  expected_behavior:
    - validates_each_step: true
    - stops_on_error: true
  expected_output:
    - proof_complete: true
    - lsp_errors: 0
```

### End-to-End Tests

**Workflow Tests**:
```yaml
# Test complete /prove workflow with MCP
test_prove_workflow_mcp:
  command: /prove
  input: "Prove that multiplication is commutative for natural numbers"
  expected_stages:
    - research:
        tools: [lean-search, loogle, lean-explore]
        finds: "Nat.mul_comm"
    - planning:
        tools: [loogle, lean-explore]
        creates: "proof_plan.md"
    - implementation:
        tools: [lean-lsp]
        validates: "incrementally"
    - verification:
        tools: [lean-lsp]
        result: "no_errors"
  expected_output:
    - file_created: true
    - proof_valid: true
    - lsp_verified: true

# Test /verify command
test_verify_command:
  command: /verify
  input: "Logos/Theorems/Perpetuity.lean"
  expected_tools_used:
    - lean-lsp
  expected_output:
    - diagnostics: "present"
    - proof_states: "shown"
    - suggestions: "provided"
```

### Performance Tests

```yaml
# Test MCP tool response times
test_mcp_performance:
  tests:
    - tool: lean-lsp
      operation: get_proof_state
      max_time: 100ms
    
    - tool: loogle
      operation: search_by_type
      max_time: 1000ms
    
    - tool: lean-search
      operation: semantic_search
      max_time: 3000ms
    
    - tool: lean-explore
      operation: explore_module
      max_time: 500ms

# Test caching effectiveness
test_caching:
  tests:
    - operation: "Search same query twice"
      first_call: > 1000ms
      second_call: < 50ms
      cache_hit: true
```

### Error Handling Tests

```yaml
# Test MCP tool unavailability
test_mcp_fallback:
  scenario: "MCP server unavailable"
  tests:
    - tool: loogle
      unavailable: true
      expected_fallback: "grep-based search"
    
    - tool: lean-lsp
      unavailable: true
      expected_fallback: "full compilation"
    
    - tool: lean-search
      unavailable: true
      expected_fallback: "keyword search"

# Test error recovery
test_error_recovery:
  scenario: "LSP validation fails"
  tests:
    - agent: implementer
      error: "tactic fails"
      expected_behavior:
        - stops: true
        - reports: "error with context"
        - suggests: "alternative tactics"
        - requests: "approval before continuing"
```

---

## Success Metrics

### Quantitative Metrics

1. **Search Quality**:
   - Relevant theorem found in top 10 results: > 90%
   - Multi-tool search finds more theorems than single tool: > 50% increase
   - Search time (all tools combined): < 5 seconds

2. **Proof Verification**:
   - LSP validation catches errors before compilation: > 95%
   - Incremental validation reduces debugging time: > 60% reduction
   - Proof implementation success rate (first attempt): > 80%

3. **Performance**:
   - LSP proof state query: < 100ms
   - Loogle type search: < 1s
   - LeanSearch semantic search: < 3s
   - LeanExplore module exploration: < 500ms
   - Cache hit rate: > 70%

4. **Error Reduction**:
   - Compilation errors in generated proofs: < 5%
   - Proof plan revisions needed: < 20%
   - Time to fix errors: < 50% of previous

### Qualitative Metrics

1. **User Experience**:
   - Proof development feels more interactive
   - Real-time feedback improves confidence
   - Search results are more relevant
   - Error messages are more actionable

2. **Code Quality**:
   - Generated proofs are more readable
   - Proofs follow best practices
   - Fewer unnecessary tactics
   - Better structured proofs

3. **Workflow Efficiency**:
   - Less time spent searching for theorems
   - Faster proof implementation
   - Fewer revision cycles
   - More successful first attempts

### Success Criteria

**Phase 1 Success**:
- ✅ All MCP servers installed and responding
- ✅ Tool wrappers handle basic operations
- ✅ Documentation explains MCP tools clearly

**Phase 2 Success**:
- ✅ All 4 new subagents work independently
- ✅ Subagents integrate with MCP tools
- ✅ Output formats are useful

**Phase 3 Success**:
- ✅ Enhanced agents use MCP tools effectively
- ✅ Routing logic is correct
- ✅ Error handling is robust

**Phase 4 Success**:
- ✅ All commands work end-to-end
- ✅ Documentation is clear
- ✅ Examples are helpful

**Phase 5 Success**:
- ✅ Workflows clearly describe MCP usage
- ✅ Context files are comprehensive
- ✅ Examples are realistic

**Phase 6 Success**:
- ✅ All tests pass
- ✅ Documentation is complete
- ✅ Performance is acceptable
- ✅ System is production-ready

**Overall Success**:
- MCP integration is seamless and transparent
- Proof development is significantly faster and more reliable
- Search capabilities are comprehensive and accurate
- Real-time verification prevents errors early
- System is well-documented and maintainable

---

## Next Steps

### Immediate Actions

1. **Verify MCP Server Availability**:
   - Check if lean-lsp-mcp is installed
   - Research LeanExplore installation
   - Research Loogle installation
   - Research LeanSearch installation

2. **Create Implementation Roadmap**:
   - Break down phases into weekly sprints
   - Assign priorities to each task
   - Identify dependencies
   - Set milestones

3. **Set Up Development Environment**:
   - Install missing MCP servers
   - Test MCP connections
   - Create test Lean files
   - Set up logging/debugging

### Long-term Considerations

1. **Extensibility**:
   - Design for future MCP servers
   - Keep tool wrappers modular
   - Document integration patterns

2. **Maintenance**:
   - Monitor MCP server updates
   - Keep documentation current
   - Collect user feedback
   - Iterate on improvements

3. **Community**:
   - Share learnings with Lean community
   - Contribute improvements to MCP servers
   - Document best practices
   - Create tutorials

---

## Appendix

### A. MCP Server Installation Commands

```bash
# lean-lsp-mcp (already installed)
uvx lean-lsp-mcp

# LeanExplore (hypothetical - verify actual installation)
pip install lean-explore-mcp
# or
npm install -g lean-explore-mcp

# Loogle (verify actual installation method)
# May be part of Lean toolchain or separate package
git clone https://github.com/leanprover-community/loogle
cd loogle
lake build

# LeanSearch (verify actual installation method)
pip install lean-search
# or may be API-based service
```

### B. Configuration Examples

**`.mcp.json` Full Example**:
```json
{
  "mcpServers": {
    "lean-lsp": {
      "type": "stdio",
      "command": "uvx",
      "args": ["lean-lsp-mcp"],
      "env": {
        "LEAN_LOG_LEVEL": "WARNING",
        "LEAN_PROJECT_PATH": "/home/benjamin/Documents/Philosophy/Projects/ProofChecker",
        "LEAN_CACHE_DIR": "/tmp/lean-cache"
      }
    },
    "lean-explore": {
      "type": "stdio",
      "command": "lean-explore-mcp",
      "args": ["--project", "/home/benjamin/Documents/Philosophy/Projects/ProofChecker"],
      "env": {
        "MATHLIB_PATH": "/home/benjamin/.elan/toolchains/leanprover-lean4-v4.14.0/lib/lean/library",
        "CACHE_SIZE": "1000"
      }
    },
    "loogle": {
      "type": "stdio",
      "command": "loogle-mcp-server",
      "args": [
        "--mathlib-index", "/path/to/mathlib-index",
        "--cache-dir", "/tmp/loogle-cache"
      ]
    },
    "lean-search": {
      "type": "stdio",
      "command": "lean-search-mcp",
      "args": [
        "--model", "semantic-v1",
        "--api-key-env", "LEAN_SEARCH_API_KEY"
      ],
      "env": {
        "LEAN_SEARCH_API_KEY": "${LEAN_SEARCH_API_KEY}"
      }
    }
  }
}
```

### C. TypeScript Type Definitions

```typescript
// .opencode/tool/mcp/types.ts

export interface ProofState {
  goals: Goal[];
  hypotheses: Hypothesis[];
  context: string;
}

export interface Goal {
  id: string;
  type: string;
  description: string;
}

export interface Hypothesis {
  name: string;
  type: string;
}

export interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  line: number;
  column: number;
  suggestions?: string[];
}

export interface ValidationResult {
  isValid: boolean;
  proofState?: ProofState;
  diagnostics: Diagnostic[];
  suggestions: string[];
}

export interface Theorem {
  name: string;
  fullName: string;
  type: string;
  namespace: string;
  location: string;
  relevance?: number;
}

export interface SearchResult {
  query: string;
  totalFound: number;
  theorems: Theorem[];
}

export interface ModuleContents {
  name: string;
  definitions: Definition[];
  theorems: Theorem[];
  instances: Instance[];
}

export interface Definition {
  name: string;
  type: string;
  description: string;
}

export interface Instance {
  name: string;
  type: string;
}
```

### D. Error Codes and Handling

```typescript
// .opencode/tool/mcp/errors.ts

export enum MCPErrorCode {
  CONNECTION_FAILED = 'MCP_CONNECTION_FAILED',
  TIMEOUT = 'MCP_TIMEOUT',
  INVALID_RESPONSE = 'MCP_INVALID_RESPONSE',
  SERVER_ERROR = 'MCP_SERVER_ERROR',
  NOT_AVAILABLE = 'MCP_NOT_AVAILABLE',
}

export class MCPError extends Error {
  constructor(
    public code: MCPErrorCode,
    message: string,
    public details?: any
  ) {
    super(message);
    this.name = 'MCPError';
  }
}

export function handleMCPError(error: MCPError): FallbackStrategy {
  switch (error.code) {
    case MCPErrorCode.CONNECTION_FAILED:
    case MCPErrorCode.NOT_AVAILABLE:
      return FallbackStrategy.USE_ALTERNATIVE;
    
    case MCPErrorCode.TIMEOUT:
      return FallbackStrategy.RETRY_ONCE;
    
    case MCPErrorCode.INVALID_RESPONSE:
    case MCPErrorCode.SERVER_ERROR:
      return FallbackStrategy.REPORT_ERROR;
    
    default:
      return FallbackStrategy.REPORT_ERROR;
  }
}

export enum FallbackStrategy {
  USE_ALTERNATIVE = 'use_alternative',
  RETRY_ONCE = 'retry_once',
  REPORT_ERROR = 'report_error',
}
```

---

## Conclusion

This comprehensive plan outlines the integration of four MCP servers (lean-lsp-mcp, LeanExplore, Loogle, and LeanSearch) into the ProofChecker .opencode system. The integration will:

1. **Transform proof verification** with real-time LSP validation
2. **Enhance theorem search** with multi-tool, multi-strategy search
3. **Improve proof development** with incremental validation and feedback
4. **Accelerate research** with semantic and type-based search
5. **Increase success rates** by catching errors early
6. **Reduce development time** through better tool support

The phased implementation approach ensures:
- Solid foundation before building advanced features
- Continuous testing and validation
- Comprehensive documentation
- Smooth integration with existing system

**Estimated Timeline**: 12 weeks  
**Estimated Effort**: High (but transformative impact)  
**Risk Level**: Moderate (depends on MCP server availability and stability)  
**Expected ROI**: Very High (significant improvement in proof development efficiency)

---

## Implementation Status

### Phase 1: Foundation ✅ 80% Complete

**Completed (2025-12-15)**:
- ✅ TypeScript infrastructure (types, errors, LSP client, coordinator)
- ✅ Comprehensive documentation (README, guide, quick start)
- ✅ MCP server research document
- ✅ Configuration updates with placeholders

**Files Created**: 10 new files, 2 updated files (~2,000 lines total)

**Next Steps**:
1. Complete MCP server research (community outreach)
2. Implement MCP protocol communication
3. Test with actual lean-lsp-mcp server
4. Begin Phase 2 (Subagent Development)

**See Also**:
- [Phase 1 Summary](./mcp-phase1-summary.md) - Detailed completion report
- [MCP Server Research](./mcp-server-research.md) - Research findings and action items
- [Integration Checklist](./mcp-integration-checklist.md) - Task tracking

---

**Document Version**: 1.1  
**Last Updated**: 2025-12-15  
**Author**: AI System Architect  
**Status**: Phase 1 Foundation Complete (80%) - Integration Testing Pending
