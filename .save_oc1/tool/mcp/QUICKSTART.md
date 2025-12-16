# MCP Tools Quick Start

Quick reference for using MCP tools in ProofChecker.

## Installation Status

| Server | Status | Ready to Use? |
|--------|--------|---------------|
| lean-lsp-mcp | 🟡 Partial | No (needs integration) |
| LeanExplore | 🔴 Planned | No |
| Loogle | 🔴 Planned | No |
| LeanSearch | 🔴 Planned | No |

## Basic Usage

### Import

```typescript
import { 
  createLSPClient,
  type ProofState,
  type Diagnostic,
  type Result,
} from './.opencode/tool/mcp/index.js';
```

### Create Client

```typescript
const lsp = createLSPClient({
  timeout: 5000,      // 5 seconds
  useCache: true,     // Enable caching
  cacheTTL: 60000,    // Cache for 1 minute
  retryAttempts: 1,   // Retry once on failure
});
```

### Get Proof State

```typescript
const result = await lsp.getProofState('file.lean', {
  line: 45,
  column: 10,
});

if (result.success) {
  console.log('Goals:', result.data.goals);
  console.log('Hypotheses:', result.data.hypotheses);
} else {
  console.error('Error:', result.error);
}
```

### Check Proof

```typescript
const validation = await lsp.checkProof(
  'test.lean',
  'theorem test : 1 + 1 = 2 := by rfl'
);

if (validation.success && validation.data.isValid) {
  console.log('✓ Proof is valid');
} else {
  console.log('✗ Proof has errors');
  console.log('Diagnostics:', validation.data.diagnostics);
}
```

### Get Diagnostics

```typescript
const diagnostics = await lsp.getDiagnostics('file.lean');

if (diagnostics.success) {
  const errors = diagnostics.data.filter(d => d.severity === 'error');
  const warnings = diagnostics.data.filter(d => d.severity === 'warning');
  
  console.log(`Errors: ${errors.length}`);
  console.log(`Warnings: ${warnings.length}`);
}
```

## Error Handling

All methods return `Result<T>` for functional error handling:

```typescript
type Result<T> = 
  | { success: true; data: T }
  | { success: false; error: string; details?: unknown };
```

### Pattern Matching

```typescript
const result = await lsp.getProofState('file.lean', { line: 1, column: 1 });

if (result.success) {
  // Use result.data
  const { goals, hypotheses } = result.data;
} else {
  // Handle error
  console.error(result.error);
}
```

### Error Details

```typescript
import { isMCPError, getFallbackStrategy } from './.opencode/tool/mcp/index.js';

if (!result.success && result.details) {
  if (isMCPError(result.details)) {
    const strategy = getFallbackStrategy(result.details);
    console.log('Fallback strategy:', strategy);
  }
}
```

## Caching

### Default Behavior

```typescript
// First call - hits the server
await lsp.getProofState('file.lean', { line: 10, column: 5 });

// Second call - returns cached result (within TTL)
await lsp.getProofState('file.lean', { line: 10, column: 5 });
```

### Clear Cache

```typescript
// Clear all cached results
lsp.clearCache();
```

### Disable Cache

```typescript
const lsp = createLSPClient({
  useCache: false,  // Disable caching
});
```

## Configuration Options

```typescript
interface MCPClientOptions {
  /** Request timeout in milliseconds (default: 5000) */
  timeout?: number;
  
  /** Enable caching (default: true) */
  useCache?: boolean;
  
  /** Cache TTL in milliseconds (default: 60000) */
  cacheTTL?: number;
  
  /** Number of retry attempts (default: 1) */
  retryAttempts?: number;
}
```

## Common Patterns

### Incremental Proof Validation

```typescript
async function validateProofStep(
  file: string,
  position: { line: number; column: number }
): Promise<boolean> {
  // Get current proof state
  const state = await lsp.getProofState(file, position);
  if (!state.success) return false;
  
  // Check diagnostics
  const diagnostics = await lsp.getDiagnostics(file);
  if (!diagnostics.success) return false;
  
  // No errors = valid
  const errors = diagnostics.data.filter(d => d.severity === 'error');
  return errors.length === 0;
}
```

### Error Recovery

```typescript
async function getProofStateWithFallback(
  file: string,
  position: { line: number; column: number }
): Promise<ProofState | null> {
  const result = await lsp.getProofState(file, position);
  
  if (result.success) {
    return result.data;
  }
  
  // Log error and return null
  console.warn('Failed to get proof state:', result.error);
  return null;
}
```

## Current Limitations

⚠️ **Important**: The LSP client is currently a placeholder implementation.

- Methods return placeholder errors
- MCP protocol integration not yet complete
- Actual lean-lsp-mcp connection not implemented

**To use**: Wait for integration phase or implement MCP protocol communication.

## Next Steps

1. Complete MCP server research
2. Implement MCP protocol communication
3. Test with actual lean-lsp-mcp server
4. Add LeanExplore, Loogle, LeanSearch clients

## Documentation

- **Full Guide**: [mcp-tools-guide.md](../../context/lean4/tools/mcp-tools-guide.md)
- **README**: [README.md](./README.md)
- **Integration Plan**: [mcp-integration-plan.md](../../specs/mcp-integration-plan.md)
- **Type Definitions**: [types.ts](./types.ts)

## Support

For issues or questions:
1. Check the [MCP Tools Guide](../../context/lean4/tools/mcp-tools-guide.md)
2. Review [mcp-server-research.md](../../specs/mcp-server-research.md)
3. See [Integration Plan](../../specs/mcp-integration-plan.md)

---

**Version**: 0.1.0  
**Status**: Phase 1 - Foundation Complete  
**Last Updated**: 2025-12-15
