# MCP Integration Architecture

Visual architecture diagrams for the MCP integration into ProofChecker .opencode system.

---

## System Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                         User Interface                               │
│  Commands: /prove, /research, /implement, /verify, /explore, etc.  │
└────────────────────────────┬────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      Orchestrator Agent                              │
│  • Analyzes requests                                                 │
│  • Routes to appropriate agents                                      │
│  • Coordinates MCP tool usage                                        │
│  • Monitors MCP health                                               │
└────────────┬────────────────┬────────────────┬───────────────────────┘
             │                │                │
             ▼                ▼                ▼
    ┌────────────┐   ┌────────────┐   ┌────────────┐
    │ Researcher │   │Implementer │   │  Reviser   │
    │   Agent    │   │   Agent    │   │   Agent    │
    └─────┬──────┘   └─────┬──────┘   └─────┬──────┘
          │                │                │
          ▼                ▼                ▼
    ┌─────────────────────────────────────────────┐
    │         MCP Tool Coordinator                 │
    │  (.opencode/tool/mcp/index.ts)              │
    │  • Manages connections                       │
    │  • Handles caching                           │
    │  • Implements fallbacks                      │
    └────┬────────┬────────┬────────┬─────────────┘
         │        │        │        │
         ▼        ▼        ▼        ▼
    ┌────────┐┌────────┐┌────────┐┌────────┐
    │lean-lsp││Lean    ││Loogle  ││Lean    │
    │  MCP   ││Explore ││  MCP   ││Search  │
    │        ││  MCP   ││        ││  MCP   │
    └────────┘└────────┘└────────┘└────────┘
         │        │        │        │
         ▼        ▼        ▼        ▼
    ┌─────────────────────────────────────┐
    │      Lean 4 Project & Mathlib       │
    │  • Source files (.lean)             │
    │  • Mathlib library                  │
    │  • LSP server                       │
    └─────────────────────────────────────┘
```

---

## Researcher Agent MCP Integration

```
┌──────────────────────────────────────────────────────────────┐
│                    Researcher Agent                           │
│  Manages multi-source theorem search                          │
└────────┬─────────────┬─────────────┬────────────────────────┘
         │             │             │
         ▼             ▼             ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│  Semantic   │ │   Loogle    │ │  Namespace  │
│  Searcher   │ │  Searcher   │ │  Explorer   │
│  Subagent   │ │  Subagent   │ │  Subagent   │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │
       ▼               ▼               ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│ LeanSearch  │ │   Loogle    │ │ LeanExplore │
│    MCP      │ │    MCP      │ │    MCP      │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │
       └───────────────┴───────────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Result Merger   │
              │ • Deduplicate   │
              │ • Rank          │
              │ • Format        │
              └────────┬────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Research Report │
              │ • Theorems      │
              │ • Types         │
              │ • Locations     │
              └─────────────────┘
```

### Search Strategy Flow

```
User Query: "Find theorems about commutativity"
    │
    ▼
┌─────────────────────────────────────────┐
│ Query Analysis                          │
│ • Extract keywords: "commutativity"     │
│ • Identify type pattern: "?a ⊕ ?b = ?b ⊕ ?a" │
│ • Determine search strategy             │
└────────┬────────────────────────────────┘
         │
         ├──────────────────┬──────────────────┬─────────────────┐
         ▼                  ▼                  ▼                 ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────┐ ┌──────────────┐
│ LeanSearch      │ │ Loogle          │ │ LeanExplore │ │ Grep Fallback│
│ "commutativity" │ │ "?a*?b=?b*?a"   │ │ "Algebra.*" │ │ "comm"       │
└────────┬────────┘ └────────┬────────┘ └──────┬──────┘ └──────┬───────┘
         │                   │                  │               │
         │ 15 results        │ 23 results       │ 8 modules     │ 45 matches
         │                   │                  │               │
         └───────────────────┴──────────────────┴───────────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ Merge & Rank    │
                    │ • Remove dupes  │
                    │ • Score by:     │
                    │   - Relevance   │
                    │   - Source      │
                    │   - Confidence  │
                    └────────┬────────┘
                             │
                             ▼
                    ┌─────────────────┐
                    │ Top 20 Results  │
                    │ 1. Nat.mul_comm │
                    │ 2. Int.mul_comm │
                    │ 3. ...          │
                    └─────────────────┘
```

---

## Implementer Agent LSP Integration

```
┌──────────────────────────────────────────────────────────────┐
│                    Implementer Agent                          │
│  Manages LSP-verified proof construction                      │
└────────────────────────┬─────────────────────────────────────┘
                         │
                         ▼
                ┌─────────────────┐
                │ Initialize LSP  │
                │ Connection      │
                └────────┬────────┘
                         │
                         ▼
        ┌────────────────────────────────────┐
        │ For Each Proof Step in Plan:      │
        └────────┬───────────────────────────┘
                 │
                 ▼
        ┌─────────────────┐
        │ Get Proof State │ ◄─────┐
        │ via LSP         │       │
        └────────┬────────┘       │
                 │                │
                 ▼                │
        ┌─────────────────┐       │
        │ Generate Tactic │       │
        │ (via subagent)  │       │
        └────────┬────────┘       │
                 │                │
                 ▼                │
        ┌─────────────────┐       │
        │ Validate Tactic │       │
        │ via LSP         │       │
        └────────┬────────┘       │
                 │                │
            ┌────┴────┐           │
            │ Valid?  │           │
            └────┬────┘           │
                 │                │
        ┌────────┴────────┐       │
        │                 │       │
       YES               NO       │
        │                 │       │
        ▼                 ▼       │
┌───────────────┐  ┌──────────────┐
│ Append Tactic │  │ Try Alt or   │
│ Continue      │  │ Report Error │
└───────┬───────┘  └──────────────┘
        │
        └──────────────────────────┘
                 │
                 ▼
        ┌─────────────────┐
        │ All Steps Done? │
        └────────┬────────┘
                 │
            ┌────┴────┐
            │         │
           YES       NO
            │         │
            │         └─────────────┐
            │                       │
            ▼                       │
   ┌─────────────────┐              │
   │ Final LSP Check │              │
   │ • Diagnostics   │              │
   │ • Completeness  │              │
   └────────┬────────┘              │
            │                       │
            ▼                       │
   ┌─────────────────┐              │
   │ Write File      │              │
   │ (only if valid) │              │
   └─────────────────┘              │
                                    │
                                    └─── Loop back
```

### LSP Validation Detail

```
Proof Step: "rw [Nat.add_comm]"
    │
    ▼
┌─────────────────────────────────────────┐
│ LSP Validator Subagent                  │
└────────┬────────────────────────────────┘
         │
         ├──────────────┬──────────────┬──────────────┐
         ▼              ▼              ▼              ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│ Get Current │ │ Apply       │ │ Check       │ │ Get New     │
│ Proof State │ │ Tactic      │ │ Diagnostics │ │ Proof State │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │               │
       ▼               ▼               ▼               ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│ Goals:      │ │ Tactic:     │ │ Errors: []  │ │ Goals:      │
│ a + b = b+a │ │ rw [...]    │ │ Warnings:[] │ │ (none)      │
│             │ │             │ │ Info: [✓]   │ │ ✓ Complete  │
└─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘
       │               │               │               │
       └───────────────┴───────────────┴───────────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Validation      │
              │ Result:         │
              │ ✓ Valid         │
              │ ✓ Progress made │
              │ ✓ No errors     │
              └─────────────────┘
```

---

## Multi-Tool Search Coordination

```
User: /research "continuity of square root"
    │
    ▼
┌─────────────────────────────────────────┐
│ Researcher Agent                        │
│ Analyzes query and coordinates search   │
└────────┬────────────────────────────────┘
         │
         ▼
┌─────────────────────────────────────────┐
│ Parallel Search Execution               │
└────┬────────┬────────┬──────────────────┘
     │        │        │
     │        │        └──────────────────┐
     │        │                           │
     ▼        ▼                           ▼
┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐
│LeanSearch│ │  Loogle  │ │  Lean    │ │   Grep   │
│  (NL)    │ │  (Type)  │ │ Explore  │ │(Fallback)│
└────┬─────┘ └────┬─────┘ └────┬─────┘ └────┬─────┘
     │            │            │            │
     │ 8 results  │ 12 results │ 5 modules  │ 23 matches
     │            │            │            │
     └────────────┴────────────┴────────────┘
                  │
                  ▼
         ┌─────────────────┐
         │ Result Merger   │
         │ • Deduplicate   │
         │ • Cross-ref     │
         │ • Score         │
         └────────┬────────┘
                  │
                  ▼
         ┌─────────────────┐
         │ Ranking Engine  │
         │ Score by:       │
         │ • Relevance     │
         │ • Source trust  │
         │ • Type match    │
         │ • Recency       │
         └────────┬────────┘
                  │
                  ▼
         ┌─────────────────┐
         │ Top 20 Results  │
         │ with metadata:  │
         │ • Source        │
         │ • Confidence    │
         │ • Type sig      │
         │ • Location      │
         └─────────────────┘
```

---

## MCP Tool Wrapper Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                  Agent (e.g., Implementer)                   │
└────────────────────────┬────────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────────┐
│              MCP Tool Coordinator                            │
│              (.opencode/tool/mcp/index.ts)                   │
│  • Connection pooling                                        │
│  • Request routing                                           │
│  • Caching layer                                             │
│  • Health monitoring                                         │
└────┬────────┬────────┬────────┬─────────────────────────────┘
     │        │        │        │
     ▼        ▼        ▼        ▼
┌─────────┐┌─────────┐┌─────────┐┌─────────┐
│   LSP   ││ Explore ││ Loogle  ││ Search  │
│ Client  ││ Client  ││ Client  ││ Client  │
│ Wrapper ││ Wrapper ││ Wrapper ││ Wrapper │
└────┬────┘└────┬────┘└────┬────┘└────┬────┘
     │          │          │          │
     │  ┌───────┴──────────┴──────────┘
     │  │
     ▼  ▼
┌─────────────────────────────────────┐
│      Common Infrastructure          │
│  • Error handling                   │
│  • Retry logic                      │
│  • Timeout management               │
│  • Response validation              │
│  • Type conversion                  │
└────┬────────┬────────┬──────────────┘
     │        │        │
     ▼        ▼        ▼
┌─────────┐┌─────────┐┌─────────┐
│  Cache  ││ Logger  ││ Metrics │
│  Layer  ││         ││         │
└─────────┘└─────────┘└─────────┘
```

### Request Flow with Caching

```
Agent Request: "Get proof state at line 45"
    │
    ▼
┌─────────────────┐
│ MCP Coordinator │
└────────┬────────┘
         │
         ▼
    ┌────────┐
    │ Cache? │
    └───┬────┘
        │
   ┌────┴────┐
   │         │
  HIT       MISS
   │         │
   │         ▼
   │    ┌─────────────┐
   │    │ LSP Client  │
   │    │ Wrapper     │
   │    └──────┬──────┘
   │           │
   │           ▼
   │    ┌─────────────┐
   │    │ lean-lsp    │
   │    │ MCP Server  │
   │    └──────┬──────┘
   │           │
   │           ▼
   │    ┌─────────────┐
   │    │ Response    │
   │    │ Validation  │
   │    └──────┬──────┘
   │           │
   │           ▼
   │    ┌─────────────┐
   │    │ Store in    │
   │    │ Cache       │
   │    └──────┬──────┘
   │           │
   └───────────┘
         │
         ▼
┌─────────────────┐
│ Return Result   │
│ to Agent        │
└─────────────────┘
```

---

## Error Handling & Fallback Strategy

```
MCP Tool Request
    │
    ▼
┌─────────────────┐
│ Try Primary     │
│ MCP Server      │
└────────┬────────┘
         │
    ┌────┴────┐
    │ Success?│
    └────┬────┘
         │
    ┌────┴────┐
    │         │
   YES       NO
    │         │
    │         ▼
    │    ┌─────────────┐
    │    │ Error Type? │
    │    └──────┬──────┘
    │           │
    │      ┌────┴────┬────────┬──────────┐
    │      │         │        │          │
    │   TIMEOUT  UNAVAIL  INVALID   SERVER
    │      │         │        │      ERROR
    │      │         │        │          │
    │      ▼         ▼        ▼          ▼
    │   ┌─────┐  ┌─────┐  ┌─────┐   ┌─────┐
    │   │Retry│  │Fall │  │Report│  │Report│
    │   │Once │  │back │  │Error │  │Error │
    │   └──┬──┘  └──┬──┘  └─────┘   └─────┘
    │      │        │
    │      │        ▼
    │      │   ┌──────────────┐
    │      │   │ Use Alt Tool │
    │      │   │ • LSP → Full │
    │      │   │   Compile    │
    │      │   │ • Loogle →   │
    │      │   │   Grep       │
    │      │   │ • Search →   │
    │      │   │   Keywords   │
    │      │   └──────┬───────┘
    │      │          │
    │      └──────────┘
    │           │
    └───────────┘
         │
         ▼
┌─────────────────┐
│ Return Result   │
│ (with metadata) │
│ • Source used   │
│ • Fallback?     │
│ • Confidence    │
└─────────────────┘
```

---

## Complete Proof Development Flow

```
User: /prove "∀ (a b : ℕ), a + b = b + a"
    │
    ▼
┌─────────────────────────────────────────┐
│ PHASE 1: Research (Multi-Tool Search)   │
└────────┬────────────────────────────────┘
         │
         ├──────────────┬──────────────┬──────────────┐
         ▼              ▼              ▼              ▼
    LeanSearch      Loogle       LeanExplore      Grep
    "addition       "?a+?b=      "Nat.Add"        "add_comm"
    commutativity"  ?b+?a"
         │              │              │              │
         └──────────────┴──────────────┴──────────────┘
                        │
                        ▼
               ┌─────────────────┐
               │ Found:          │
               │ • Nat.add_comm  │
               │ • Nat.add_assoc │
               │ • Nat.zero_add  │
               │ • Nat.add_zero  │
               └────────┬────────┘
                        │
                        ▼
┌─────────────────────────────────────────┐
│ PHASE 2: Planning (Type-Guided)         │
└────────┬────────────────────────────────┘
         │
         ├─ Analyze goal type
         ├─ Search dependencies (LeanExplore)
         ├─ Build proof strategy
         │
         ▼
    ┌─────────────────┐
    │ Proof Plan:     │
    │ 1. Induction    │
    │ 2. Base case    │
    │ 3. Inductive    │
    │    step         │
    └────────┬────────┘
             │
             ▼
┌─────────────────────────────────────────┐
│ PHASE 3: Implementation (LSP-Verified)   │
└────────┬────────────────────────────────┘
         │
         ▼
    ┌─────────────────┐
    │ Initialize LSP  │
    └────────┬────────┘
             │
             ▼
    ┌─────────────────┐
    │ Write theorem   │
    │ signature       │
    │ ✓ LSP validates │
    └────────┬────────┘
             │
             ▼
    ┌─────────────────┐
    │ For each step:  │
    │ • Get state     │◄───┐
    │ • Gen tactic    │    │
    │ • Validate LSP  │    │
    │ • Append if ✓   │    │
    └────────┬────────┘    │
             │             │
        ┌────┴────┐        │
        │ More?   │        │
        └────┬────┘        │
             │             │
        ┌────┴────┐        │
        │         │        │
       YES       NO        │
        │         │        │
        └─────────┘        │
                  │
                  ▼
         ┌─────────────────┐
         │ Final LSP Check │
         │ ✓ No errors     │
         │ ✓ Complete      │
         └────────┬────────┘
                  │
                  ▼
┌─────────────────────────────────────────┐
│ PHASE 4: Verification (LSP Diagnostics)  │
└────────┬────────────────────────────────┘
         │
         ▼
    ┌─────────────────┐
    │ Get diagnostics │
    │ • Errors: 0     │
    │ • Warnings: 0   │
    │ • Info: ✓       │
    └────────┬────────┘
             │
             ▼
    ┌─────────────────┐
    │ Write file      │
    │ ✓ Success!      │
    └─────────────────┘
```

---

## Data Flow: Theorem Search

```
Query: "Find theorems about sqrt continuity"
    │
    ▼
┌─────────────────────────────────────────┐
│ Researcher Agent                        │
│ • Parses query                          │
│ • Determines search strategy            │
│ • Coordinates subagents                 │
└────────┬────────────────────────────────┘
         │
         ├──────────────┬──────────────┬──────────────┐
         │              │              │              │
         ▼              ▼              ▼              ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│  Semantic   │ │   Loogle    │ │  Namespace  │ │   Mathlib   │
│  Searcher   │ │  Searcher   │ │  Explorer   │ │  Explorer   │
│  Subagent   │ │  Subagent   │ │  Subagent   │ │  Subagent   │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │               │
       ▼               ▼               ▼               ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│ LeanSearch  │ │   Loogle    │ │ LeanExplore │ │    Grep     │
│    MCP      │ │    MCP      │ │    MCP      │ │   (local)   │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │               │
       │               │               │               │
       ▼               ▼               ▼               ▼
┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐
│ Results:    │ │ Results:    │ │ Results:    │ │ Results:    │
│ 8 theorems  │ │ 12 theorems │ │ 5 modules   │ │ 23 matches  │
│ (semantic)  │ │ (type-based)│ │ (structure) │ │ (text)      │
└──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘
       │               │               │               │
       └───────────────┴───────────────┴───────────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Result Merger   │
              │ • Deduplicate   │
              │ • Cross-ref     │
              │ • Enrich        │
              └────────┬────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Ranking Engine  │
              │ Weights:        │
              │ • Type match:40%│
              │ • Semantic: 30% │
              │ • Structure:20% │
              │ • Text:     10% │
              └────────┬────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Top 20 Results  │
              │ 1. continuous_  │
              │    sqrt (0.95)  │
              │ 2. sqrt_cont... │
              │    (0.88)       │
              │ ...             │
              └────────┬────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Format Report   │
              │ • Theorem names │
              │ • Type sigs     │
              │ • Locations     │
              │ • Sources       │
              │ • Confidence    │
              └────────┬────────┘
                       │
                       ▼
              ┌─────────────────┐
              │ Return to User  │
              └─────────────────┘
```

---

## Performance & Caching Strategy

```
┌─────────────────────────────────────────┐
│          Request Timeline                │
└─────────────────────────────────────────┘

First Request (Cold):
├─ LSP Query:        50ms  ████
├─ Loogle Search:   800ms  ████████████████
├─ LeanSearch:     2500ms  ██████████████████████████████████████████████████
├─ LeanExplore:     400ms  ████████
└─ Total:          3750ms

Second Request (Warm - Cached):
├─ LSP Query:        50ms  ████
├─ Loogle Search:    20ms  █ (cached)
├─ LeanSearch:       30ms  █ (cached)
├─ LeanExplore:      25ms  █ (cached)
└─ Total:           125ms

Cache Strategy:
┌─────────────────────────────────────────┐
│ Cache Layer                             │
│ • TTL: 1 hour for search results       │
│ • TTL: 5 minutes for LSP state         │
│ • TTL: 24 hours for module structure   │
│ • Max size: 1000 entries                │
│ • LRU eviction                          │
└─────────────────────────────────────────┘
```

---

## Summary

This architecture provides:

1. **Modular Design**: Each MCP server has a dedicated wrapper
2. **Fault Tolerance**: Fallback strategies for each tool
3. **Performance**: Caching layer for expensive operations
4. **Flexibility**: Easy to add new MCP servers
5. **Observability**: Logging and metrics at each layer
6. **Type Safety**: TypeScript types throughout
7. **Error Handling**: Comprehensive error recovery
8. **Scalability**: Connection pooling and request queuing

**Key Benefits**:
- Real-time proof verification via LSP
- Multi-source theorem search
- Type-guided proof development
- Incremental validation
- Comprehensive error diagnosis
- Faster development cycles

---

**Last Updated**: 2025-12-15  
**Version**: 1.0  
**Status**: Architecture Design Complete
