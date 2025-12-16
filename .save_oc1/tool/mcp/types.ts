/**
 * Type definitions for MCP (Model Context Protocol) tools
 * 
 * This module defines TypeScript interfaces for interacting with Lean 4 MCP servers:
 * - lean-lsp-mcp: Language Server Protocol integration
 * - LeanExplore: Project structure exploration
 * - Loogle: Type-based theorem search
 * - LeanSearch: Semantic theorem search
 */

// ============================================================================
// LSP (Language Server Protocol) Types
// ============================================================================

/**
 * Represents a single goal in a Lean proof state
 */
export interface Goal {
  /** Unique identifier for the goal */
  id: string;
  /** Type signature of the goal */
  type: string;
  /** Human-readable description */
  description: string;
}

/**
 * Represents a hypothesis in the proof context
 */
export interface Hypothesis {
  /** Name of the hypothesis */
  name: string;
  /** Type of the hypothesis */
  type: string;
}

/**
 * Complete proof state at a given position
 */
export interface ProofState {
  /** Active goals to be proven */
  goals: Goal[];
  /** Available hypotheses in context */
  hypotheses: Hypothesis[];
  /** Contextual information (theorem name, etc.) */
  context: string;
}

/**
 * Diagnostic severity levels
 */
export type DiagnosticSeverity = 'error' | 'warning' | 'info';

/**
 * A diagnostic message from the Lean compiler
 */
export interface Diagnostic {
  /** Severity level */
  severity: DiagnosticSeverity;
  /** Error/warning message */
  message: string;
  /** Line number (1-indexed) */
  line: number;
  /** Column number (1-indexed) */
  column: number;
  /** Optional suggestions for fixing the issue */
  suggestions?: string[];
}

/**
 * Result of validating a proof via LSP
 */
export interface ValidationResult {
  /** Whether the proof is valid */
  isValid: boolean;
  /** Current proof state (if available) */
  proofState?: ProofState;
  /** Diagnostics (errors, warnings, info) */
  diagnostics: Diagnostic[];
  /** Suggestions for improvement */
  suggestions: string[];
}

/**
 * Hover information for a symbol
 */
export interface HoverInfo {
  /** Type signature */
  type: string;
  /** Documentation string */
  documentation?: string;
  /** Source location */
  location?: string;
}

// ============================================================================
// Search Types (Loogle, LeanSearch)
// ============================================================================

/**
 * A theorem found by search
 */
export interface Theorem {
  /** Short name (e.g., "add_comm") */
  name: string;
  /** Fully qualified name (e.g., "Nat.add_comm") */
  fullName: string;
  /** Type signature */
  type: string;
  /** Namespace/module location */
  namespace: string;
  /** File location */
  location: string;
  /** Relevance score (0-1, higher is more relevant) */
  relevance?: number;
}

/**
 * Result of a theorem search
 */
export interface SearchResult {
  /** Original search query */
  query: string;
  /** Total number of results found */
  totalFound: number;
  /** List of matching theorems */
  theorems: Theorem[];
}

// ============================================================================
// Exploration Types (LeanExplore)
// ============================================================================

/**
 * A definition in a Lean module
 */
export interface Definition {
  /** Name of the definition */
  name: string;
  /** Type of the definition */
  type: string;
  /** Description/docstring */
  description: string;
}

/**
 * A type class instance
 */
export interface Instance {
  /** Instance name */
  name: string;
  /** Instance type */
  type: string;
}

/**
 * Contents of a Lean module
 */
export interface ModuleContents {
  /** Module name */
  name: string;
  /** Definitions in the module */
  definitions: Definition[];
  /** Theorems in the module */
  theorems: Theorem[];
  /** Type class instances */
  instances: Instance[];
}

/**
 * Dependency information for a theorem
 */
export interface Dependency {
  /** Name of the dependency */
  name: string;
  /** Type of dependency */
  type: string;
  /** Whether it's a direct dependency */
  isDirect: boolean;
}

/**
 * Usage information for a theorem
 */
export interface Usage {
  /** Name of the theorem using this one */
  name: string;
  /** Location where it's used */
  location: string;
  /** Context of usage */
  context: string;
}

/**
 * Complete exploration result
 */
export interface ExplorationResult {
  /** Target that was explored */
  target: string;
  /** Module contents */
  contents?: ModuleContents;
  /** Dependencies (if requested) */
  dependencies?: Dependency[];
  /** Usages (if requested) */
  usages?: Usage[];
}

// ============================================================================
// MCP Client Configuration
// ============================================================================

/**
 * Configuration for an MCP server connection
 */
export interface MCPServerConfig {
  /** Server name/identifier */
  name: string;
  /** Command to run */
  command: string;
  /** Command arguments */
  args: string[];
  /** Environment variables */
  env?: Record<string, string>;
  /** Connection timeout (ms) */
  timeout?: number;
}

/**
 * Options for MCP client operations
 */
export interface MCPClientOptions {
  /** Request timeout (ms) */
  timeout?: number;
  /** Whether to use cache */
  useCache?: boolean;
  /** Cache TTL (ms) */
  cacheTTL?: number;
  /** Retry attempts on failure */
  retryAttempts?: number;
}

// ============================================================================
// Result Types (for functional error handling)
// ============================================================================

/**
 * Success result
 */
export interface Success<T> {
  success: true;
  data: T;
}

/**
 * Failure result
 */
export interface Failure {
  success: false;
  error: string;
  details?: unknown;
}

/**
 * Result type for operations that can fail
 */
export type Result<T> = Success<T> | Failure;
