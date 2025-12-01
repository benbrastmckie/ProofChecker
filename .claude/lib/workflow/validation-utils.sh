#!/usr/bin/env bash
# Validation Utilities Library
# Provides reusable validation functions for command development
#
# Version: 1.0.0
# Last Modified: 2025-12-01
#
# This library implements common validation patterns to reduce duplication across commands:
# - Workflow prerequisites validation (required functions availability)
# - Agent artifact validation (file existence and minimum size)
# - Absolute path validation (path format and existence)
#
# Dependencies:
# - error-handling.sh: log_command_error() for error logging integration

# Source guard: Prevent multiple sourcing
if [ -n "${VALIDATION_UTILS_SOURCED:-}" ]; then
  return 0
fi
export VALIDATION_UTILS_SOURCED=1
export VALIDATION_UTILS_VERSION="1.0.0"

set -euo pipefail

# Detect project directory dynamically
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/../core/detect-project-dir.sh"

# Source error handling library for error logging integration
source "${CLAUDE_PROJECT_DIR}/lib/core/error-handling.sh" 2>/dev/null || {
  echo "ERROR: Failed to source error-handling.sh" >&2
  return 1
}

# ==============================================================================
# Workflow Prerequisites Validation
# ==============================================================================

# validate_workflow_prerequisites: Check for required workflow management functions
#
# Validates that critical workflow management functions are available in the current
# bash context. This prevents runtime failures when commands attempt to use
# workflow functions without proper library sourcing.
#
# Usage:
#   validate_workflow_prerequisites || exit 1
#
# Checks for:
#   - sm_init (state machine initialization)
#   - sm_transition (state transitions)
#   - append_workflow_state (state persistence)
#   - load_workflow_state (state loading)
#   - save_completed_states_to_state (state array persistence)
#
# Returns:
#   0 on success (all required functions available)
#   1 on failure (one or more functions missing)
#
# Logs:
#   validation_error to centralized error log on failure
validate_workflow_prerequisites() {
  local required_functions=(
    "sm_init"
    "sm_transition"
    "append_workflow_state"
    "load_workflow_state"
    "save_completed_states_to_state"
  )

  local missing_functions=()

  for func in "${required_functions[@]}"; do
    if ! declare -F "$func" >/dev/null 2>&1; then
      missing_functions+=("$func")
    fi
  done

  if [ ${#missing_functions[@]} -gt 0 ]; then
    local missing_list
    missing_list=$(printf "%s, " "${missing_functions[@]}")
    missing_list="${missing_list%, }"  # Remove trailing comma

    # Log error if error logging context is available
    if declare -F log_command_error >/dev/null 2>&1; then
      if [ -n "${COMMAND_NAME:-}" ] && [ -n "${WORKFLOW_ID:-}" ]; then
        log_command_error \
          "$COMMAND_NAME" \
          "$WORKFLOW_ID" \
          "${USER_ARGS:-}" \
          "validation_error" \
          "Missing required workflow functions: $missing_list" \
          "validate_workflow_prerequisites" \
          "$(jq -n --arg funcs "$missing_list" '{missing_functions: $funcs}')"
      fi
    fi

    echo "ERROR: Missing required workflow functions: $missing_list" >&2
    echo "Ensure workflow-state-machine.sh and state-persistence.sh are sourced" >&2
    return 1
  fi

  return 0
}

# ==============================================================================
# Agent Artifact Validation
# ==============================================================================

# validate_agent_artifact: Validate agent-produced artifact files
#
# Checks that an agent-produced artifact exists and meets minimum size requirements.
# This prevents silent failures when agents fail to produce expected output files.
#
# Usage:
#   validate_agent_artifact "$REPORT_PATH" 100 "research report" || exit 1
#   validate_agent_artifact "$PLAN_PATH" 500 "implementation plan" || exit 1
#
# Parameters:
#   $1 - artifact_path: Absolute path to artifact file
#   $2 - min_size_bytes: Minimum expected file size in bytes (default: 10)
#   $3 - artifact_type: Human-readable artifact description (default: "artifact")
#
# Returns:
#   0 on success (file exists and meets size requirement)
#   1 on failure (file missing or too small)
#
# Logs:
#   agent_error to centralized error log on failure
validate_agent_artifact() {
  local artifact_path="${1:-}"
  local min_size_bytes="${2:-10}"
  local artifact_type="${3:-artifact}"

  # Validate parameters
  if [ -z "$artifact_path" ]; then
    echo "ERROR: artifact_path parameter required" >&2
    return 1
  fi

  # Check file existence
  if [ ! -f "$artifact_path" ]; then
    # Log error if error logging context is available
    if declare -F log_command_error >/dev/null 2>&1; then
      if [ -n "${COMMAND_NAME:-}" ] && [ -n "${WORKFLOW_ID:-}" ]; then
        log_command_error \
          "$COMMAND_NAME" \
          "$WORKFLOW_ID" \
          "${USER_ARGS:-}" \
          "agent_error" \
          "Agent failed to create $artifact_type" \
          "validate_agent_artifact" \
          "$(jq -n --arg path "$artifact_path" --arg type "$artifact_type" \
            '{artifact_path: $path, artifact_type: $type, error: "file_not_found"}')"
      fi
    fi

    echo "ERROR: Agent artifact not found: $artifact_path" >&2
    echo "Expected $artifact_type at this location" >&2
    return 1
  fi

  # Check file size
  local actual_size
  actual_size=$(stat -f%z "$artifact_path" 2>/dev/null || stat -c%s "$artifact_path" 2>/dev/null || echo 0)

  if [ "$actual_size" -lt "$min_size_bytes" ]; then
    # Log error if error logging context is available
    if declare -F log_command_error >/dev/null 2>&1; then
      if [ -n "${COMMAND_NAME:-}" ] && [ -n "${WORKFLOW_ID:-}" ]; then
        log_command_error \
          "$COMMAND_NAME" \
          "$WORKFLOW_ID" \
          "${USER_ARGS:-}" \
          "agent_error" \
          "Agent produced undersized $artifact_type" \
          "validate_agent_artifact" \
          "$(jq -n --arg path "$artifact_path" --arg type "$artifact_type" \
            --argjson actual "$actual_size" --argjson min "$min_size_bytes" \
            '{artifact_path: $path, artifact_type: $type, actual_size: $actual, min_size: $min, error: "file_too_small"}')"
      fi
    fi

    echo "ERROR: Agent artifact too small: $artifact_path" >&2
    echo "Expected minimum $min_size_bytes bytes, got $actual_size bytes" >&2
    return 1
  fi

  return 0
}

# ==============================================================================
# Path Validation
# ==============================================================================

# validate_absolute_path: Validate path format and optional existence
#
# Checks that a path is absolute (starts with /) and optionally validates
# that the path exists on the filesystem.
#
# Usage:
#   validate_absolute_path "$PLAN_FILE" true || exit 1  # Check existence
#   validate_absolute_path "$OUTPUT_DIR" false || exit 1  # Format only
#
# Parameters:
#   $1 - path: Path to validate
#   $2 - check_exists: Boolean (true/false) whether to check existence (default: false)
#
# Returns:
#   0 on success (path is absolute and exists if check_exists=true)
#   1 on failure (path is relative or doesn't exist)
#
# Logs:
#   validation_error to centralized error log on failure
validate_absolute_path() {
  local path="${1:-}"
  local check_exists="${2:-false}"

  # Validate parameters
  if [ -z "$path" ]; then
    echo "ERROR: path parameter required" >&2
    return 1
  fi

  # Check absolute path format
  if [[ ! "$path" =~ ^/ ]]; then
    # Log error if error logging context is available
    if declare -F log_command_error >/dev/null 2>&1; then
      if [ -n "${COMMAND_NAME:-}" ] && [ -n "${WORKFLOW_ID:-}" ]; then
        log_command_error \
          "$COMMAND_NAME" \
          "$WORKFLOW_ID" \
          "${USER_ARGS:-}" \
          "validation_error" \
          "Path is not absolute" \
          "validate_absolute_path" \
          "$(jq -n --arg path "$path" '{path: $path, error: "not_absolute"}')"
      fi
    fi

    echo "ERROR: Path is not absolute: $path" >&2
    echo "Absolute paths must start with /" >&2
    return 1
  fi

  # Check existence if requested
  if [ "$check_exists" = "true" ]; then
    if [ ! -e "$path" ]; then
      # Log error if error logging context is available
      if declare -F log_command_error >/dev/null 2>&1; then
        if [ -n "${COMMAND_NAME:-}" ] && [ -n "${WORKFLOW_ID:-}" ]; then
          log_command_error \
            "$COMMAND_NAME" \
            "$WORKFLOW_ID" \
            "${USER_ARGS:-}" \
            "validation_error" \
            "Path does not exist" \
            "validate_absolute_path" \
            "$(jq -n --arg path "$path" '{path: $path, error: "not_found"}')"
        fi
      fi

      echo "ERROR: Path does not exist: $path" >&2
      return 1
    fi
  fi

  return 0
}

# ==============================================================================
# Initialization
# ==============================================================================

# Library loaded successfully
return 0
