/**
 * Error handling for MCP (Model Context Protocol) tools
 * 
 * Provides error types, error codes, and fallback strategies for handling
 * MCP server failures gracefully.
 */

// ============================================================================
// Error Codes
// ============================================================================

/**
 * Standard error codes for MCP operations
 */
export enum MCPErrorCode {
  /** Failed to connect to MCP server */
  CONNECTION_FAILED = 'MCP_CONNECTION_FAILED',
  
  /** Request timed out */
  TIMEOUT = 'MCP_TIMEOUT',
  
  /** Server returned invalid/malformed response */
  INVALID_RESPONSE = 'MCP_INVALID_RESPONSE',
  
  /** Server encountered an internal error */
  SERVER_ERROR = 'MCP_SERVER_ERROR',
  
  /** MCP server is not available/installed */
  NOT_AVAILABLE = 'MCP_NOT_AVAILABLE',
  
  /** Invalid request parameters */
  INVALID_REQUEST = 'MCP_INVALID_REQUEST',
  
  /** Operation not supported by this MCP server */
  NOT_SUPPORTED = 'MCP_NOT_SUPPORTED',
}

// ============================================================================
// Error Classes
// ============================================================================

/**
 * Base error class for MCP-related errors
 */
export class MCPError extends Error {
  /**
   * Create a new MCP error
   * 
   * @param code - Error code identifying the type of error
   * @param message - Human-readable error message
   * @param details - Additional error details (optional)
   */
  constructor(
    public readonly code: MCPErrorCode,
    message: string,
    public readonly details?: unknown
  ) {
    super(message);
    this.name = 'MCPError';
    
    // Maintain proper stack trace (V8 engines)
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, MCPError);
    }
  }

  /**
   * Convert error to JSON for logging
   */
  toJSON(): Record<string, unknown> {
    return {
      name: this.name,
      code: this.code,
      message: this.message,
      details: this.details,
      stack: this.stack,
    };
  }
}

// ============================================================================
// Fallback Strategies
// ============================================================================

/**
 * Strategy for handling MCP errors
 */
export enum FallbackStrategy {
  /** Use an alternative method (e.g., grep instead of Loogle) */
  USE_ALTERNATIVE = 'use_alternative',
  
  /** Retry the operation once */
  RETRY_ONCE = 'retry_once',
  
  /** Report error to user and stop */
  REPORT_ERROR = 'report_error',
  
  /** Use cached result if available */
  USE_CACHE = 'use_cache',
  
  /** Continue without this operation */
  SKIP = 'skip',
}

/**
 * Determine appropriate fallback strategy for an error
 * 
 * @param error - The MCP error that occurred
 * @returns Recommended fallback strategy
 */
export function getFallbackStrategy(error: MCPError): FallbackStrategy {
  switch (error.code) {
    case MCPErrorCode.CONNECTION_FAILED:
    case MCPErrorCode.NOT_AVAILABLE:
      // Server unavailable - use alternative method
      return FallbackStrategy.USE_ALTERNATIVE;
    
    case MCPErrorCode.TIMEOUT:
      // Timeout - try once more, then use cache or alternative
      return FallbackStrategy.RETRY_ONCE;
    
    case MCPErrorCode.INVALID_RESPONSE:
    case MCPErrorCode.SERVER_ERROR:
      // Server error - report to user
      return FallbackStrategy.REPORT_ERROR;
    
    case MCPErrorCode.INVALID_REQUEST:
      // Bad request - report to user
      return FallbackStrategy.REPORT_ERROR;
    
    case MCPErrorCode.NOT_SUPPORTED:
      // Not supported - skip this operation
      return FallbackStrategy.SKIP;
    
    default:
      // Unknown error - report to user
      return FallbackStrategy.REPORT_ERROR;
  }
}

// ============================================================================
// Error Factory Functions
// ============================================================================

/**
 * Create a connection failed error
 */
export function createConnectionError(serverName: string, details?: unknown): MCPError {
  return new MCPError(
    MCPErrorCode.CONNECTION_FAILED,
    `Failed to connect to MCP server: ${serverName}`,
    details
  );
}

/**
 * Create a timeout error
 */
export function createTimeoutError(operation: string, timeoutMs: number): MCPError {
  return new MCPError(
    MCPErrorCode.TIMEOUT,
    `Operation '${operation}' timed out after ${timeoutMs}ms`,
    { operation, timeoutMs }
  );
}

/**
 * Create an invalid response error
 */
export function createInvalidResponseError(expected: string, received: unknown): MCPError {
  return new MCPError(
    MCPErrorCode.INVALID_RESPONSE,
    `Invalid response from MCP server. Expected: ${expected}`,
    { expected, received }
  );
}

/**
 * Create a server error
 */
export function createServerError(serverName: string, message: string, details?: unknown): MCPError {
  return new MCPError(
    MCPErrorCode.SERVER_ERROR,
    `MCP server '${serverName}' error: ${message}`,
    details
  );
}

/**
 * Create a not available error
 */
export function createNotAvailableError(serverName: string): MCPError {
  return new MCPError(
    MCPErrorCode.NOT_AVAILABLE,
    `MCP server '${serverName}' is not available. Please install and configure it.`,
    { serverName }
  );
}

/**
 * Create an invalid request error
 */
export function createInvalidRequestError(reason: string, details?: unknown): MCPError {
  return new MCPError(
    MCPErrorCode.INVALID_REQUEST,
    `Invalid request: ${reason}`,
    details
  );
}

/**
 * Create a not supported error
 */
export function createNotSupportedError(operation: string, serverName: string): MCPError {
  return new MCPError(
    MCPErrorCode.NOT_SUPPORTED,
    `Operation '${operation}' is not supported by MCP server '${serverName}'`,
    { operation, serverName }
  );
}

// ============================================================================
// Error Handling Utilities
// ============================================================================

/**
 * Check if an error is an MCP error
 */
export function isMCPError(error: unknown): error is MCPError {
  return error instanceof MCPError;
}

/**
 * Safely extract error message from unknown error
 */
export function getErrorMessage(error: unknown): string {
  if (isMCPError(error)) {
    return error.message;
  }
  if (error instanceof Error) {
    return error.message;
  }
  if (typeof error === 'string') {
    return error;
  }
  return 'Unknown error occurred';
}

/**
 * Log error with appropriate level based on severity
 */
export function logError(error: MCPError, logger?: { error: (msg: string) => void; warn: (msg: string) => void }): void {
  const message = `[${error.code}] ${error.message}`;
  
  if (!logger) {
    console.error(message, error.details);
    return;
  }
  
  // Determine log level based on error code
  const shouldWarn = [
    MCPErrorCode.NOT_AVAILABLE,
    MCPErrorCode.NOT_SUPPORTED,
    MCPErrorCode.TIMEOUT,
  ].includes(error.code);
  
  if (shouldWarn) {
    logger.warn(message);
  } else {
    logger.error(message);
  }
}
