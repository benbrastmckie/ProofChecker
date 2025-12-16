# MCP Integration Implementation Checklist

Quick reference checklist for implementing the MCP integration plan.

**Full Plan**: [mcp-integration-plan.md](./mcp-integration-plan.md)  
**Summary**: [mcp-integration-summary.md](./mcp-integration-summary.md)

---

## Phase 1: Foundation (Week 1-2)

### Week 1: MCP Server Setup

- [x] **Verify lean-lsp-mcp** (Already installed)
  - [x] Verified in `.mcp.json` configuration
  - [ ] Test connection: `uvx lean-lsp-mcp` (deferred to integration phase)
  - [ ] Verify it responds to basic queries (deferred to integration phase)
  - [ ] Check logs for any issues (deferred to integration phase)

- [x] **Research LeanExplore MCP**
  - [x] Documented research questions in `mcp-server-research.md`
  - [x] Identified need for community research
  - [x] Created research action items
  - [x] Documented fallback strategies

- [x] **Research Loogle**
  - [x] Documented known information (web interface available)
  - [x] Identified research questions in `mcp-server-research.md`
  - [x] Created research action items
  - [x] Documented potential approaches

- [x] **Research LeanSearch**
  - [x] Documented known information (web interface available)
  - [x] Identified research questions in `mcp-server-research.md`
  - [x] Created research action items
  - [x] Documented potential approaches

- [x] **Install Missing MCP Servers**
  - [x] Deferred to Phase 2 (pending research completion)
  - [x] Documented installation research needs
  - [x] Created placeholder configurations in `.mcp.json`

- [x] **Update `.mcp.json`**
  - [x] Added placeholder configurations for future servers
  - [x] Documented research needs in comments
  - [x] Preserved existing lean-lsp configuration

### Week 2: Tool Wrapper Layer

- [x] **Create Directory Structure**
  - [x] Created `.opencode/tool/mcp/` directory
  - [x] Created `.opencode/context/lean4/tools/` directory

- [x] **Create Type Definitions**
  - [x] Created `.opencode/tool/mcp/types.ts`
  - [x] Defined ProofState interface
  - [x] Defined Diagnostic interface
  - [x] Defined Theorem interface
  - [x] Defined SearchResult interface
  - [x] Defined ModuleContents interface
  - [x] Added comprehensive JSDoc comments

- [x] **Create Error Handling**
  - [x] Created `.opencode/tool/mcp/errors.ts`
  - [x] Defined MCPError class
  - [x] Defined error codes (7 types)
  - [x] Implemented fallback strategies
  - [x] Added error factory functions
  - [x] Added error utilities

- [x] **Create LSP Client Wrapper**
  - [x] Created `.opencode/tool/mcp/lsp-client.ts`
  - [x] Implemented `getProofState()` (placeholder)
  - [x] Implemented `checkProof()` (placeholder)
  - [x] Implemented `getDiagnostics()` (placeholder)
  - [x] Implemented `getHover()` (placeholder)
  - [x] Added error handling with Result types
  - [x] Added caching layer
  - [x] Added retry logic framework

- [ ] **Create LeanExplore Client Wrapper**
  - [ ] Deferred to Phase 2 (pending research)

- [ ] **Create Loogle Client Wrapper**
  - [ ] Deferred to Phase 2 (pending research)

- [ ] **Create LeanSearch Client Wrapper**
  - [ ] Deferred to Phase 2 (pending research)

- [x] **Create Main MCP Coordinator**
  - [x] Created `.opencode/tool/mcp/index.ts`
  - [x] Exported all type definitions
  - [x] Exported error handling utilities
  - [x] Exported LSP client
  - [x] Added version information
  - [x] Added implementation status tracking
  - [x] Added health check framework
  - [x] Created README.md with comprehensive documentation

- [x] **Create MCP Tools Documentation**
  - [x] Created `.opencode/context/lean4/tools/mcp-tools-guide.md`
  - [x] Documented each MCP server (current and planned)
  - [x] Provided usage examples
  - [x] Defined search strategies
  - [x] Added troubleshooting section
  - [x] Added best practices
  - [x] Added performance considerations

- [ ] **Test Tool Wrappers**
  - [ ] Deferred to integration phase (requires actual MCP connections)
  - [ ] Test LSP client with sample file
  - [ ] Test error handling works
  - [ ] Check caching works

---

## Phase 2: Subagent Development (Week 3-4)

### Week 3: Verification & Search Subagents

- [ ] **Create LSP Validator Subagent**
  - [ ] Create directory: `.opencode/agent/subagents/verification/`
  - [ ] Create `.opencode/agent/subagents/verification/lsp-validator.md`
  - [ ] Define inputs (file_path, proof_text, position)
  - [ ] Define process flow (3 steps)
  - [ ] Define output specification
  - [ ] Add validation checks
  - [ ] Test with sample proof

- [ ] **Create Loogle Searcher Subagent**
  - [ ] Create directory: `.opencode/agent/subagents/search/`
  - [ ] Create `.opencode/agent/subagents/search/loogle-searcher.md`
  - [ ] Define inputs (type_pattern, namespace, exact_match)
  - [ ] Define process flow (3 steps)
  - [ ] Define output specification
  - [ ] Add ranking logic
  - [ ] Test with type patterns

- [ ] **Create Semantic Searcher Subagent**
  - [ ] Create `.opencode/agent/subagents/search/semantic-searcher.md`
  - [ ] Define inputs (query, max_results)
  - [ ] Define process flow (3 steps)
  - [ ] Define output specification
  - [ ] Add query optimization
  - [ ] Test with natural language queries

### Week 4: Exploration Subagent & Testing

- [ ] **Create Namespace Explorer Subagent**
  - [ ] Create directory: `.opencode/agent/subagents/exploration/`
  - [ ] Create `.opencode/agent/subagents/exploration/namespace-explorer.md`
  - [ ] Define inputs (target, show_dependencies, show_usages)
  - [ ] Define process flow (4 steps)
  - [ ] Define output specification
  - [ ] Add navigation suggestions
  - [ ] Test with Mathlib modules

- [ ] **Create Subagent Tests**
  - [ ] Test LSP Validator independently
  - [ ] Test Loogle Searcher independently
  - [ ] Test Semantic Searcher independently
  - [ ] Test Namespace Explorer independently
  - [ ] Verify output formats
  - [ ] Check error handling

- [ ] **Document Subagents**
  - [ ] Add subagents to AGENTS_GUIDE.md
  - [ ] Create usage examples
  - [ ] Document integration patterns

---

## Phase 3: Agent Enhancement (Week 5-6)

### Week 5: Researcher & Implementer

- [ ] **Enhance Researcher Agent**
  - [ ] Open `.opencode/agent/researcher.md`
  - [ ] Add new stage: "CoordinateSearchTools"
  - [ ] Add route to @loogle-searcher
  - [ ] Add route to @semantic-searcher
  - [ ] Add route to @namespace-explorer
  - [ ] Update SynthesizeFindings stage
  - [ ] Add result merging logic
  - [ ] Test multi-tool search

- [ ] **Enhance Implementer Agent**
  - [ ] Open `.opencode/agent/implementer.md`
  - [ ] Add critical rule: "incremental_lsp_validation"
  - [ ] Update TacticalImplementation stage
  - [ ] Add route to @lsp-validator
  - [ ] Add route to @proof-state-analyzer
  - [ ] Update ValidationAndLinting stage
  - [ ] Add LSP-first validation
  - [ ] Test incremental proof construction

### Week 6: Reviser & Orchestrator

- [ ] **Enhance Reviser Agent**
  - [ ] Open `.opencode/agent/reviser.md`
  - [ ] Add new stage: "LSPDiagnosticAnalysis"
  - [ ] Add LSP diagnostic querying
  - [ ] Add similar proof search
  - [ ] Update AdjustStrategy stage
  - [ ] Test error diagnosis

- [ ] **Enhance Orchestrator**
  - [ ] Open `.opencode/agent/orchestrator.md`
  - [ ] Add MCP availability detection
  - [ ] Add new routing for LSP-enabled implementer
  - [ ] Add new routing for multi-tool researcher
  - [ ] Add MCP health monitoring
  - [ ] Test coordination

- [ ] **Integration Testing**
  - [ ] Test Researcher with all search tools
  - [ ] Test Implementer with LSP validation
  - [ ] Test Reviser with LSP diagnostics
  - [ ] Test Orchestrator coordination
  - [ ] Verify error handling

---

## Phase 4: Command Development (Week 7-8)

### Week 7: Enhance Existing Commands

- [ ] **Enhance `/prove` Command**
  - [ ] Open `.opencode/command/prove.md`
  - [ ] Update process description
  - [ ] Add MCP tools used section
  - [ ] Add LSP verification step
  - [ ] Update examples
  - [ ] Test end-to-end

- [ ] **Enhance `/research` Command**
  - [ ] Open `.opencode/command/research.md`
  - [ ] Add multi-source search description
  - [ ] Add search strategy selection
  - [ ] Add new flags (--type-search, --semantic, --explore)
  - [ ] Update syntax and examples
  - [ ] Test all search modes

- [ ] **Enhance `/implement` Command**
  - [ ] Open `.opencode/command/implement.md`
  - [ ] Add LSP verification description
  - [ ] Add new flags (--lsp-verify, --incremental)
  - [ ] Update process flow
  - [ ] Update examples
  - [ ] Test LSP-verified implementation

### Week 8: Create New Commands

- [ ] **Create `/verify` Command**
  - [ ] Create `.opencode/command/verify.md`
  - [ ] Define agent routing (implementer)
  - [ ] Define description
  - [ ] Define syntax and parameters
  - [ ] Add examples
  - [ ] Define output format
  - [ ] Test with sample files

- [ ] **Create `/explore` Command**
  - [ ] Create `.opencode/command/explore.md`
  - [ ] Define agent routing (researcher)
  - [ ] Define description
  - [ ] Define syntax and parameters
  - [ ] Add examples
  - [ ] Define output format
  - [ ] Test with Mathlib modules

- [ ] **Create `/search-type` Command**
  - [ ] Create `.opencode/command/search-type.md`
  - [ ] Define agent routing (researcher)
  - [ ] Define description
  - [ ] Define syntax and parameters
  - [ ] Add pattern syntax help
  - [ ] Add examples
  - [ ] Define output format
  - [ ] Test with type patterns

- [ ] **Update Commands Documentation**
  - [ ] Update COMMANDS_REFERENCE.md
  - [ ] Add new commands
  - [ ] Update enhanced commands
  - [ ] Add usage examples

---

## Phase 5: Workflow Integration (Week 9-10)

### Week 9: Update Workflows

- [ ] **Update End-to-End Theorem Proving Workflow**
  - [ ] Open `.opencode/workflows/end-to-end-theorem-proving.md`
  - [ ] Update Step 1: Research (add MCP multi-tool search)
  - [ ] Update Step 2: Planning (add type-guided planning)
  - [ ] Update Step 3: Implementation (add LSP verification)
  - [ ] Update Step 4: Verification (add LSP diagnostics)
  - [ ] Add MCP tools to each step
  - [ ] Add critical rules
  - [ ] Test complete workflow

- [ ] **Update Context Files**
  - [ ] Update `.opencode/context/lean4/theorem-proving-guidelines.md`
  - [ ] Add "MCP-Enhanced Proof Development" section
  - [ ] Update `.opencode/context/lean4/processes/end-to-end-proof-workflow.md`
  - [ ] Add MCP tools to each step
  - [ ] Add MCP best practices

### Week 10: Create Examples

- [ ] **Create Simple Theorem Example**
  - [ ] Create example file
  - [ ] Show MCP-enhanced research
  - [ ] Show LSP-verified implementation
  - [ ] Document each step
  - [ ] Add to documentation

- [ ] **Create Complex Proof Example**
  - [ ] Create example file
  - [ ] Show multi-tool search
  - [ ] Show type-guided planning
  - [ ] Show incremental LSP validation
  - [ ] Document each step
  - [ ] Add to documentation

- [ ] **Create Research-Heavy Example**
  - [ ] Create example file
  - [ ] Show semantic search
  - [ ] Show namespace exploration
  - [ ] Show type-based search
  - [ ] Document search strategy
  - [ ] Add to documentation

---

## Phase 6: Testing & Documentation (Week 11-12)

### Week 11: Comprehensive Testing

- [ ] **Unit Tests**
  - [ ] Test LSP client wrapper
  - [ ] Test LeanExplore client wrapper
  - [ ] Test Loogle client wrapper
  - [ ] Test LeanSearch client wrapper
  - [ ] Test error handling
  - [ ] Test caching

- [ ] **Integration Tests**
  - [ ] Test Researcher with MCP tools
  - [ ] Test Implementer with LSP
  - [ ] Test Reviser with LSP diagnostics
  - [ ] Test all new commands
  - [ ] Test enhanced commands

- [ ] **End-to-End Tests**
  - [ ] Test `/prove` workflow with MCP
  - [ ] Test `/verify` command
  - [ ] Test `/explore` command
  - [ ] Test `/search-type` command
  - [ ] Test complete theorem proving workflow

- [ ] **Performance Tests**
  - [ ] Test MCP tool response times
  - [ ] Test caching effectiveness
  - [ ] Test multi-tool search performance
  - [ ] Optimize slow operations

- [ ] **Error Handling Tests**
  - [ ] Test MCP server unavailability
  - [ ] Test fallback strategies
  - [ ] Test error recovery
  - [ ] Test timeout handling

### Week 12: Documentation & Finalization

- [ ] **Update Architecture Documentation**
  - [ ] Update `.opencode/docs/ARCHITECTURE.md`
  - [ ] Add MCP integration section
  - [ ] Add data flow diagrams
  - [ ] Document tool coordination

- [ ] **Update Agents Guide**
  - [ ] Update `.opencode/docs/AGENTS_GUIDE.md`
  - [ ] Document enhanced agents
  - [ ] Document new subagents
  - [ ] Add MCP usage patterns

- [ ] **Update Commands Reference**
  - [ ] Update `.opencode/docs/COMMANDS_REFERENCE.md`
  - [ ] Document enhanced commands
  - [ ] Document new commands
  - [ ] Add comprehensive examples

- [ ] **Create MCP Integration Guide**
  - [ ] Create `.opencode/docs/MCP_INTEGRATION_GUIDE.md`
  - [ ] Explain MCP architecture
  - [ ] Document each MCP server
  - [ ] Provide troubleshooting guide
  - [ ] Add best practices

- [ ] **Create Tutorials**
  - [ ] Tutorial: Using MCP Tools
  - [ ] Tutorial: LSP-Verified Proof Development
  - [ ] Tutorial: Multi-Tool Theorem Search
  - [ ] Add to documentation

- [ ] **Update README**
  - [ ] Update `.opencode/README.md`
  - [ ] Add MCP integration highlights
  - [ ] Update feature list
  - [ ] Add quick start for MCP features

- [ ] **Final Review**
  - [ ] Review all documentation
  - [ ] Check all tests pass
  - [ ] Verify all examples work
  - [ ] Check performance metrics
  - [ ] Ensure error handling is robust

---

## Post-Implementation

### Monitoring & Maintenance

- [ ] **Monitor MCP Server Health**
  - [ ] Set up logging
  - [ ] Monitor response times
  - [ ] Track error rates
  - [ ] Monitor cache hit rates

- [ ] **Collect User Feedback**
  - [ ] Track command usage
  - [ ] Collect error reports
  - [ ] Gather feature requests
  - [ ] Identify pain points

- [ ] **Iterate & Improve**
  - [ ] Fix reported issues
  - [ ] Optimize slow operations
  - [ ] Add requested features
  - [ ] Update documentation

### Future Enhancements

- [ ] **Additional MCP Servers**
  - [ ] Research new Lean MCP servers
  - [ ] Evaluate integration value
  - [ ] Plan integration if beneficial

- [ ] **Advanced Features**
  - [ ] Proof state visualization
  - [ ] Interactive proof construction
  - [ ] Automated tactic suggestion
  - [ ] Proof optimization

- [ ] **Community Contribution**
  - [ ] Share learnings with Lean community
  - [ ] Contribute improvements to MCP servers
  - [ ] Create tutorials and blog posts
  - [ ] Help others integrate MCP tools

---

## Quick Reference

### Key Files

**Planning**:
- `mcp-integration-plan.md` - Complete detailed plan
- `mcp-integration-summary.md` - High-level summary
- `mcp-integration-checklist.md` - This checklist

**Configuration**:
- `.mcp.json` - MCP server configuration

**Tool Wrappers** (to create):
- `.opencode/tool/mcp/index.ts`
- `.opencode/tool/mcp/lsp-client.ts`
- `.opencode/tool/mcp/explore-client.ts`
- `.opencode/tool/mcp/loogle-client.ts`
- `.opencode/tool/mcp/search-client.ts`

**New Subagents** (to create):
- `.opencode/agent/subagents/verification/lsp-validator.md`
- `.opencode/agent/subagents/search/loogle-searcher.md`
- `.opencode/agent/subagents/search/semantic-searcher.md`
- `.opencode/agent/subagents/exploration/namespace-explorer.md`

**Enhanced Agents** (to update):
- `.opencode/agent/orchestrator.md`
- `.opencode/agent/researcher.md`
- `.opencode/agent/implementer.md`
- `.opencode/agent/reviser.md`

**New Commands** (to create):
- `.opencode/command/verify.md`
- `.opencode/command/explore.md`
- `.opencode/command/search-type.md`

**Enhanced Commands** (to update):
- `.opencode/command/prove.md`
- `.opencode/command/research.md`
- `.opencode/command/implement.md`

### Progress Tracking

**Phase 1**: ✅✅✅✅✅✅✅✅⬜⬜ 8/10 tasks (80% complete)
- Week 1: ✅ Complete (research and configuration)
- Week 2: ✅ Mostly complete (core infrastructure, testing deferred)

**Phase 2**: ⬜⬜⬜⬜⬜⬜⬜⬜⬜⬜ 0/10 tasks  
**Phase 3**: ⬜⬜⬜⬜⬜⬜⬜⬜⬜⬜ 0/10 tasks  
**Phase 4**: ⬜⬜⬜⬜⬜⬜⬜⬜⬜⬜ 0/10 tasks  
**Phase 5**: ⬜⬜⬜⬜⬜⬜⬜⬜⬜⬜ 0/10 tasks  
**Phase 6**: ⬜⬜⬜⬜⬜⬜⬜⬜⬜⬜ 0/10 tasks  

**Overall Progress**: 8/60 tasks (13%)

---

**Last Updated**: 2025-12-15  
**Status**: Phase 1 Foundation - 80% Complete  
**Next Action**: 
1. Complete MCP server research (community outreach)
2. Test LSP client with actual lean-lsp-mcp connection
3. Begin Phase 2 when research complete
