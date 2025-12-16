/**
 * MCP (Model Context Protocol) Tools for Lean 4
 * 
 * This module provides TypeScript wrappers for interacting with Lean 4 MCP servers:
 * - lean-lsp-mcp: Real-time proof verification via Language Server Protocol
 * - LeanExplore: Project structure and dependency exploration (planned)
 * - Loogle: Type-based theorem search (planned)
 * - LeanSearch: Semantic theorem search (planned)
 * 
 * @module mcp-tools
 */

// ============================================================================
// Type Exports
// ============================================================================

export type {
  // LSP Types
  Goal,
  Hypothesis,
  ProofState,
  Diagnostic,
  DiagnosticSeverity,
  ValidationResult,
  HoverInfo,
  
  // Search Types
  Theorem,
  SearchResult,
  
  // Exploration Types
  Definition,
  Instance,
  ModuleContents,
  Dependency,
  Usage,
  ExplorationResult,
  
  // Configuration Types
  MCPServerConfig,
  MCPClientOptions,
  
  // Result Types
  Result,
  Success,
  Failure,
} from './types.js';

// ============================================================================
// Error Exports
// ============================================================================

export {
  // Error Classes
  MCPError,
  
  // Error Codes
  MCPErrorCode,
  
  // Fallback Strategies
  FallbackStrategy,
  getFallbackStrategy,
  
  // Error Factory Functions
  createConnectionError,
  createTimeoutError,
  createInvalidResponseError,
  createServerError,
  createNotAvailableError,
  createInvalidRequestError,
  createNotSupportedError,
  
  // Error Utilities
  isMCPError,
  getErrorMessage,
  logError,
} from './errors.js';

// ============================================================================
// Client Exports
// ============================================================================

export {
  // LSP Client
  LSPClient,
  createLSPClient,
  type Position,
} from './lsp-client.js';

// ============================================================================
// Future Exports (Planned)
// ============================================================================

// TODO: Export LeanExplore client when implemented
// export { ExploreClient, createExploreClient } from './explore-client.js';

// TODO: Export Loogle client when implemented
// export { LoogleClient, createLoogleClient } from './loogle-client.js';

// TODO: Export LeanSearch client when implemented
// export { SearchClient, createSearchClient } from './search-client.js';

// ============================================================================
// Version Information
// ============================================================================

/**
 * MCP Tools version
 */
export const VERSION = '0.1.0';

/**
 * Implementation status of MCP servers
 */
export const MCP_SERVER_STATUS = {
  'lean-lsp': 'partial', // Basic wrapper implemented, needs MCP integration
  'lean-explore': 'planned',
  'loogle': 'planned',
  'lean-search': 'planned',
} as const;

// ============================================================================
// Health Check
// ============================================================================

/**
 * Check which MCP servers are available
 * 
 * @returns Object indicating availability of each server
 */
export async function checkMCPServers(): Promise<Record<string, boolean>> {
  // TODO: Implement actual health checks
  return {
    'lean-lsp': false, // Not yet connected to actual MCP server
    'lean-explore': false,
    'loogle': false,
    'lean-search': false,
  };
}

/**
 * Get information about MCP tools implementation status
 */
export function getImplementationStatus(): typeof MCP_SERVER_STATUS {
  return MCP_SERVER_STATUS;
}
