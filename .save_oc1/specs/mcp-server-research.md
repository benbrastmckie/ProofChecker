# MCP Server Research and Availability

**Status**: Research Phase  
**Date**: 2025-12-15  
**Purpose**: Document research findings on Lean 4 MCP server availability and installation

---

## Executive Summary

This document tracks research on the availability, installation methods, and configuration requirements for Lean 4 MCP servers planned for integration into the ProofChecker system.

---

## 1. lean-lsp-mcp (Language Server Protocol)

### Status: ✅ Available and Configured

**Repository**: Part of MCP ecosystem  
**Installation**: `uvx lean-lsp-mcp`  
**Configuration**: Already configured in `.mcp.json`

**Current Configuration**:
```json
{
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
```

**Capabilities**:
- Proof state inspection
- Diagnostics (errors, warnings, info)
- Hover information
- Type information
- Incremental verification

**Next Steps**:
- ✅ Configuration complete
- ⏳ Implement MCP protocol communication in TypeScript wrapper
- ⏳ Test with actual Lean files
- ⏳ Add comprehensive error handling

---

## 2. LeanExplore (Project Structure Exploration)

### Status: 🔴 Research Needed

**Research Questions**:
1. Does an official LeanExplore MCP server exist?
2. If not, what alternatives are available?
3. What's the installation method?
4. What configuration is required?

**Potential Alternatives**:
- **Lean 4 LSP**: May already provide some exploration capabilities
- **Custom Implementation**: Could build on top of Lean 4 API
- **Mathlib Tools**: Check if Mathlib provides exploration utilities

**Research Tasks**:
- [ ] Search leanprover-community GitHub for exploration tools
- [ ] Check Lean 4 documentation for built-in exploration
- [ ] Ask Lean community about MCP servers for exploration
- [ ] Evaluate building custom solution if no MCP server exists

**Placeholder Configuration**:
```json
{
  "lean-explore": {
    "type": "stdio",
    "command": "lean-explore-mcp",
    "args": ["--project", "/path/to/project"],
    "env": {
      "MATHLIB_PATH": "${MATHLIB_PATH}",
      "CACHE_SIZE": "1000"
    }
  }
}
```

**Fallback Strategy**:
If no MCP server available, implement exploration using:
- Direct file system traversal
- Lean 4 API for parsing module contents
- Grep-based search for definitions and theorems

---

## 3. Loogle (Type-based Search)

### Status: 🟡 Partial Information Available

**Known Information**:
- Loogle is a type-based search tool for Mathlib
- Web interface available at: https://loogle.lean-lang.org/
- May have API or command-line interface

**Research Questions**:
1. Is there an MCP server for Loogle?
2. Is there a command-line interface?
3. Can we use the web API programmatically?
4. What are the rate limits?

**Research Tasks**:
- [ ] Check leanprover-community/loogle repository
- [ ] Look for MCP server implementation
- [ ] Check if web API is documented
- [ ] Investigate command-line usage
- [ ] Check rate limiting policies

**Potential Approaches**:
1. **MCP Server**: If available, use directly
2. **Web API**: Wrap HTTP API in MCP-compatible interface
3. **CLI Tool**: Wrap command-line tool if available
4. **Custom Implementation**: Build type-based search using Lean 4 API

**Placeholder Configuration**:
```json
{
  "loogle": {
    "type": "stdio",
    "command": "loogle-mcp-server",
    "args": [
      "--mathlib-index", "${MATHLIB_INDEX_PATH}",
      "--cache-dir", "/tmp/loogle-cache"
    ]
  }
}
```

**Fallback Strategy**:
- Use Loogle web API with HTTP requests
- Implement caching to respect rate limits
- Fall back to grep-based search if unavailable

---

## 4. LeanSearch (Semantic Search)

### Status: 🟡 Partial Information Available

**Known Information**:
- LeanSearch provides semantic search over Mathlib
- Web interface available at: https://leansearch.net/
- Uses machine learning for semantic matching

**Research Questions**:
1. Is there an MCP server for LeanSearch?
2. Is there a public API?
3. Does it require API key?
4. What are usage limits?

**Research Tasks**:
- [ ] Check for LeanSearch MCP server
- [ ] Look for API documentation
- [ ] Check if API key is required
- [ ] Investigate usage limits and pricing
- [ ] Test API if available

**Potential Approaches**:
1. **MCP Server**: If available, use directly
2. **Web API**: Wrap HTTP API in MCP-compatible interface
3. **Custom Implementation**: Build semantic search using embeddings

**Placeholder Configuration**:
```json
{
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
```

**Fallback Strategy**:
- Use LeanSearch web interface via HTTP
- Implement keyword-based search as fallback
- Cache results to minimize API calls

---

## Research Action Items

### Immediate (Week 1)

- [ ] **lean-lsp-mcp**: Test actual MCP connection
  - Verify it responds to basic queries
  - Test proof state retrieval
  - Test diagnostics
  - Document any issues

- [ ] **LeanExplore**: Research availability
  - Search GitHub for lean-explore or similar
  - Check Lean 4 documentation
  - Ask in Lean Zulip chat
  - Document findings

- [ ] **Loogle**: Research MCP availability
  - Check loogle repository for MCP server
  - Test web API if available
  - Document API endpoints
  - Check rate limits

- [ ] **LeanSearch**: Research MCP availability
  - Check for MCP server
  - Test web API if available
  - Check if API key needed
  - Document usage limits

### Short-term (Week 2)

- [ ] Create detailed installation guides for available servers
- [ ] Update `.mcp.json` with actual configurations
- [ ] Document fallback strategies for unavailable servers
- [ ] Create test suite for available MCP servers

### Medium-term (Weeks 3-4)

- [ ] Implement MCP protocol communication for available servers
- [ ] Build HTTP API wrappers for web-based services
- [ ] Implement fallback mechanisms
- [ ] Add comprehensive error handling

---

## Community Resources

### Where to Ask

1. **Lean Zulip Chat**: https://leanprover.zulipchat.com/
   - #new members (for general questions)
   - #lean4 (for Lean 4 specific)
   - #mathlib4 (for Mathlib questions)

2. **GitHub Repositories**:
   - leanprover/lean4
   - leanprover-community/mathlib4
   - leanprover-community/loogle

3. **Documentation**:
   - Lean 4 Manual: https://lean-lang.org/lean4/doc/
   - Mathlib4 Docs: https://leanprover-community.github.io/mathlib4_docs/

### Questions to Ask

1. "Are there MCP servers available for Lean 4 theorem search and exploration?"
2. "What's the recommended way to programmatically search Mathlib by type signature?"
3. "Is there an API for Loogle and LeanSearch?"
4. "What tools exist for exploring Lean 4 project structure programmatically?"

---

## Decision Matrix

For each MCP server, we'll decide on implementation approach:

| Server | MCP Available? | API Available? | CLI Available? | Decision |
|--------|----------------|----------------|----------------|----------|
| lean-lsp | ✅ Yes | N/A | N/A | Use MCP |
| LeanExplore | ❓ TBD | ❓ TBD | ❓ TBD | Research needed |
| Loogle | ❓ TBD | 🟡 Likely | ❓ TBD | Research needed |
| LeanSearch | ❓ TBD | 🟡 Likely | ❓ TBD | Research needed |

**Decision Criteria**:
1. **MCP Server Available**: Use directly (preferred)
2. **API Available**: Wrap in MCP-compatible interface
3. **CLI Available**: Wrap command-line tool
4. **None Available**: Implement custom solution or use fallback

---

## Next Steps

1. **Complete Research** (Week 1)
   - Investigate each server's availability
   - Document findings in this file
   - Update decision matrix

2. **Update Configuration** (Week 2)
   - Update `.mcp.json` with actual configurations
   - Remove placeholder configurations
   - Add installation instructions

3. **Implement Integration** (Weeks 3-4)
   - Implement MCP protocol communication
   - Build API wrappers where needed
   - Add fallback mechanisms
   - Test thoroughly

---

## Version History

- **v0.1.0** (2025-12-15): Initial research document created
  - Documented lean-lsp-mcp status (available)
  - Identified research questions for other servers
  - Created research action items

---

**Last Updated**: 2025-12-15  
**Next Review**: After Week 1 research completion
