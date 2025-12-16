# MCP Tools for Lean 4

TypeScript wrappers for interacting with Lean 4 MCP (Model Context Protocol) servers.

## Overview

This module provides a unified interface for working with multiple MCP servers that enhance Lean 4 proof development:

- **lean-lsp-mcp**: Real-time proof verification via Language Server Protocol
- **LeanExplore**: Project structure and dependency exploration (planned)
- **Loogle**: Type-based theorem search (planned)
- **LeanSearch**: Semantic theorem search (planned)

## Implementation Status

| Server | Status | Description |
|--------|--------|-------------|
| lean-lsp-mcp | 🟡 Partial | Basic wrapper implemented, needs MCP integration |
| LeanExplore | 🔴 Planned | Not yet implemented |
| Loogle | 🔴 Planned | Not yet implemented |
| LeanSearch | 🔴 Planned | Not yet implemented |

## Installation

The MCP tools are part of the ProofChecker `.opencode` system. No separate installation is required.

### Prerequisites

To use the MCP tools, you need to install the corresponding MCP servers:

```bash
# lean-lsp-mcp (already configured in .mcp.json)
uvx lean-lsp-mcp

# LeanExplore (installation method TBD)
# TODO: Add installation instructions

# Loogle (installation method TBD)
# TODO: Add installation instructions

# LeanSearch (installation method TBD)
# TODO: Add installation instructions
```

## Usage

### LSP Client

```typescript
import { createLSPClient } from './.opencode/tool/mcp/index.js';

// Create client
const lsp = createLSPClient({
  timeout: 5000,
  useCache: true,
  cacheTTL: 60000,
});

// Get proof state at a position
const result = await lsp.getProofState('Logos/Core/Syntax/Formula.lean', {
  line: 45,
  column: 10,
});

if (result.success) {
  console.log('Goals:', result.data.goals);
  console.log('Hypotheses:', result.data.hypotheses);
} else {
  console.error('Error:', result.error);
}

// Check proof validity
const validation = await lsp.checkProof(
  'test.lean',
  'theorem test : 1 + 1 = 2 := by rfl'
);

if (validation.success && validation.data.isValid) {
  console.log('Proof is valid!');
} else {
  console.log('Diagnostics:', validation.data.diagnostics);
}

// Get diagnostics
const diagnostics = await lsp.getDiagnostics('Logos/Core/Syntax/Formula.lean');

if (diagnostics.success) {
  const errors = diagnostics.data.filter(d => d.severity === 'error');
  console.log(`Found ${errors.length} errors`);
}
```

### Error Handling

All MCP operations return a `Result<T>` type for functional error handling:

```typescript
import { createLSPClient, isMCPError, getFallbackStrategy } from './.opencode/tool/mcp/index.js';

const lsp = createLSPClient();
const result = await lsp.getProofState('file.lean', { line: 1, column: 1 });

if (!result.success) {
  console.error('Operation failed:', result.error);
  
  // Check if it's an MCP error with details
  if (result.details && isMCPError(result.details)) {
    const strategy = getFallbackStrategy(result.details);
    console.log('Recommended fallback:', strategy);
  }
}
```

### Caching

The LSP client includes built-in caching to reduce redundant requests:

```typescript
const lsp = createLSPClient({
  useCache: true,
  cacheTTL: 60000, // Cache for 1 minute
});

// First call - hits the server
await lsp.getProofState('file.lean', { line: 10, column: 5 });

// Second call - returns cached result
await lsp.getProofState('file.lean', { line: 10, column: 5 });

// Clear cache manually if needed
lsp.clearCache();
```

## Architecture

### Modular Design

Each MCP server has its own client module:

```
.opencode/tool/mcp/
├── index.ts           # Main exports and coordination
├── types.ts           # TypeScript type definitions
├── errors.ts          # Error handling and fallback strategies
├── lsp-client.ts      # lean-lsp-mcp wrapper
├── explore-client.ts  # LeanExplore wrapper (planned)
├── loogle-client.ts   # Loogle wrapper (planned)
├── search-client.ts   # LeanSearch wrapper (planned)
└── README.md          # This file
```

### Functional Error Handling

All operations return `Result<T>` types instead of throwing exceptions:

```typescript
type Result<T> = 
  | { success: true; data: T }
  | { success: false; error: string; details?: unknown };
```

This enables:
- Explicit error handling
- Type-safe error checking
- Composable error handling patterns

### Fallback Strategies

When MCP servers are unavailable, the system uses fallback strategies:

| Error | Strategy | Action |
|-------|----------|--------|
| CONNECTION_FAILED | USE_ALTERNATIVE | Fall back to grep/compilation |
| TIMEOUT | RETRY_ONCE | Retry once, then use cache |
| SERVER_ERROR | REPORT_ERROR | Report to user |
| NOT_AVAILABLE | USE_ALTERNATIVE | Use alternative method |

## Development

### Adding a New MCP Client

1. Create client file (e.g., `explore-client.ts`)
2. Define client class with methods
3. Implement error handling with `Result<T>` types
4. Add caching if appropriate
5. Export from `index.ts`
6. Update this README

### Testing

```bash
# Run type checking
tsc --noEmit

# Run tests (when implemented)
npm test
```

## Future Work

### Phase 2: LeanExplore Client

- [ ] Research LeanExplore MCP server
- [ ] Implement `ExploreClient` class
- [ ] Add methods: `exploreModule`, `exploreDependencies`, `exploreUsages`
- [ ] Add tests

### Phase 3: Loogle Client

- [ ] Research Loogle MCP server
- [ ] Implement `LoogleClient` class
- [ ] Add methods: `searchByType`, `searchByPattern`, `searchUnify`
- [ ] Add tests

### Phase 4: LeanSearch Client

- [ ] Research LeanSearch MCP server
- [ ] Implement `SearchClient` class
- [ ] Add methods: `searchSemantic`, `searchSimilar`, `searchConcept`
- [ ] Add tests

### Phase 5: Integration

- [ ] Connect LSP client to actual lean-lsp-mcp server
- [ ] Implement MCP protocol communication
- [ ] Add comprehensive error handling
- [ ] Add performance monitoring

## References

- [MCP Integration Plan](../../specs/mcp-integration-plan.md)
- [MCP Integration Checklist](../../specs/mcp-integration-checklist.md)
- [MCP Tools Guide](../../context/lean4/tools/mcp-tools-guide.md) (to be created)

## License

Part of the ProofChecker project. See main LICENSE file.
