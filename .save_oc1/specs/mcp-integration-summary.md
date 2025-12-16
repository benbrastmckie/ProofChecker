# MCP Integration Summary

## Quick Overview

This document provides a high-level summary of the MCP integration plan for the ProofChecker .opencode system.

**Full Plan**: See [mcp-integration-plan.md](./mcp-integration-plan.md) for complete details.

---

## What We're Adding

### Four MCP Servers

1. **lean-lsp-mcp** (Already configured ✓)
   - Real-time proof verification
   - Incremental validation
   - Error diagnostics
   - Proof state inspection

2. **LeanExplore** (To be added)
   - Module/namespace exploration
   - Dependency analysis
   - Usage tracking
   - Structure navigation

3. **Loogle** (To be added)
   - Type-based theorem search
   - Pattern matching
   - Formal search by signature
   - Goal-directed discovery

4. **LeanSearch** (To be added)
   - Natural language semantic search
   - Concept-based discovery
   - Ranked results
   - Exploratory search

---

## Key Improvements

### For Proof Development

**Before MCP Integration**:
- Write entire proof → compile → see errors → fix → repeat
- Search Mathlib with grep (text-based only)
- No real-time feedback during proof construction
- High error rate on first attempt

**After MCP Integration**:
- Write each tactic → validate via LSP → see proof state → continue
- Multi-tool search (type-based + semantic + structural)
- Real-time feedback at every step
- Errors caught immediately, not after compilation

**Impact**: 
- 60%+ reduction in debugging time
- 80%+ success rate on first attempt
- 50%+ increase in relevant theorem discovery

### For Theorem Search

**Before**:
- Grep-based text search only
- Manual exploration of Mathlib files
- Keyword-dependent (must know exact terms)

**After**:
- **Loogle**: Search by type signature (`?a * ?b = ?b * ?a`)
- **LeanSearch**: Natural language (`"continuity of square root"`)
- **LeanExplore**: Structured namespace exploration
- **Grep**: Fallback for text search
- **Merged Results**: Best from all sources, ranked by relevance

**Impact**:
- 90%+ relevant theorem found in top 10 results
- < 5 seconds for comprehensive multi-tool search
- Discover theorems you didn't know existed

---

## New Capabilities

### 1. Real-time LSP Verification

```lean
-- As you type each tactic, LSP validates it immediately
theorem add_comm (a b : ℕ) : a + b = b + a := by
  induction a with
  | zero => 
    -- LSP shows: Goal: 0 + b = b + 0
    rw [Nat.zero_add]  -- ✓ LSP validates instantly
    -- LSP shows: Goal: b = b + 0
    rw [Nat.add_zero]  -- ✓ LSP validates instantly
    -- LSP shows: No goals remaining ✓
```

### 2. Type-Guided Search

```bash
# Search by exact type pattern
/search-type "∀ (a b : ℕ), a * b = b * a"

# Results:
# 1. Nat.mul_comm: ∀ (a b : ℕ), a * b = b * a
# 2. CommSemiring.mul_comm: ∀ {α : Type} [CommSemiring α] (a b : α), a * b = b * a
```

### 3. Semantic Concept Search

```bash
# Search using natural language
/research "theorems about continuity of square root function"

# Results from LeanSearch:
# 1. continuous_sqrt: Continuous (fun x => sqrt x)
# 2. sqrt_continuous_on: ContinuousOn sqrt {x : ℝ | 0 ≤ x}
# 3. Real.continuous_sqrt: Continuous Real.sqrt
```

### 4. Namespace Exploration

```bash
# Explore a Mathlib module
/explore Mathlib.Topology.MetricSpace.Basic

# Results:
# Definitions (15): MetricSpace, dist, ball, ...
# Theorems (47): dist_comm, dist_triangle, ...
# Dependencies (8): Mathlib.Topology.Basic, ...
# Used by (23): Mathlib.Analysis.Normed.Group.Basic, ...
```

---

## Enhanced Agents

### Researcher (Multi-Tool Search)

**New Workflow**:
1. LeanSearch for semantic exploration
2. LeanExplore for namespace structure
3. Loogle for type-based precision
4. Merge and rank all results

**Result**: Comprehensive theorem discovery from multiple sources

### Implementer (LSP-Verified)

**New Workflow**:
1. Initialize LSP connection
2. For each proof step:
   - Get current proof state via LSP
   - Generate tactic
   - Validate via LSP
   - Append only if valid
3. Final LSP verification

**Result**: Zero compilation errors, incremental validation

### Reviser (LSP-Guided)

**New Workflow**:
1. Query LSP for diagnostics
2. Get proof state at error location
3. Use LeanSearch to find similar successful proofs
4. Generate specific revision recommendations

**Result**: Precise error diagnosis and targeted fixes

---

## New Commands

### `/verify` - LSP Verification

```bash
/verify Logos/Theorems/Perpetuity.lean --show-states

# Output:
# ✓ No errors found
# ⚠ 2 warnings: ...
# ℹ Proof states shown at key positions
# Suggestions: ...
```

### `/explore` - Namespace Exploration

```bash
/explore Mathlib.Topology.MetricSpace.Basic --deps --usages

# Output:
# Definitions (15): ...
# Theorems (47): ...
# Dependencies (8): ...
# Used by (23): ...
```

### `/search-type` - Type-Based Search

```bash
/search-type "?a * ?b = ?b * ?a"

# Output:
# Found 15 matching theorems:
# 1. mul_comm (Nat): ∀ (a b : ℕ), a * b = b * a
# 2. mul_comm (Int): ∀ (a b : ℤ), a * b = b * a
# ...
```

---

## Implementation Phases

### Phase 1: Foundation (Week 1-2)
- Install MCP servers
- Create tool wrappers
- Write documentation

### Phase 2: Subagents (Week 3-4)
- LSP Validator
- Loogle Searcher
- Semantic Searcher
- Namespace Explorer

### Phase 3: Agent Enhancement (Week 5-6)
- Enhance Researcher
- Enhance Implementer
- Enhance Reviser
- Enhance Orchestrator

### Phase 4: Commands (Week 7-8)
- Enhance `/prove`, `/research`, `/implement`
- Create `/verify`, `/explore`, `/search-type`

### Phase 5: Workflows (Week 9-10)
- Update end-to-end theorem proving
- Update context files
- Create examples

### Phase 6: Testing (Week 11-12)
- Unit tests
- Integration tests
- End-to-end tests
- Documentation

**Total Timeline**: 12 weeks

---

## Success Metrics

### Quantitative
- Relevant theorem found in top 10: > 90%
- LSP catches errors before compilation: > 95%
- Proof success rate (first attempt): > 80%
- Search time (all tools): < 5 seconds
- Debugging time reduction: > 60%

### Qualitative
- More interactive proof development
- Better search results
- Faster implementation
- Fewer revision cycles
- Higher confidence

---

## Next Steps

### Immediate (This Week)
1. ✅ Review this plan
2. ⬜ Verify MCP server availability
3. ⬜ Install missing MCP servers
4. ⬜ Test MCP connections
5. ⬜ Begin Phase 1 implementation

### Short-term (Next 2 Weeks)
1. ⬜ Complete Phase 1 (Foundation)
2. ⬜ Begin Phase 2 (Subagents)
3. ⬜ Create initial tests

### Medium-term (Next 3 Months)
1. ⬜ Complete all 6 phases
2. ⬜ Comprehensive testing
3. ⬜ Full documentation
4. ⬜ Production deployment

---

## Key Files Created

### Planning Documents
- `mcp-integration-plan.md` - Complete detailed plan (this file's companion)
- `mcp-integration-summary.md` - This summary document

### To Be Created (Phase 1)
- `.opencode/tool/mcp/index.ts` - MCP tool coordinator
- `.opencode/tool/mcp/lsp-client.ts` - LSP wrapper
- `.opencode/tool/mcp/explore-client.ts` - LeanExplore wrapper
- `.opencode/tool/mcp/loogle-client.ts` - Loogle wrapper
- `.opencode/tool/mcp/search-client.ts` - LeanSearch wrapper
- `.opencode/context/lean4/tools/mcp-tools-guide.md` - MCP documentation

### To Be Created (Phase 2)
- `.opencode/agent/subagents/verification/lsp-validator.md`
- `.opencode/agent/subagents/search/loogle-searcher.md`
- `.opencode/agent/subagents/search/semantic-searcher.md`
- `.opencode/agent/subagents/exploration/namespace-explorer.md`

### To Be Enhanced (Phase 3-4)
- `.opencode/agent/orchestrator.md`
- `.opencode/agent/researcher.md`
- `.opencode/agent/implementer.md`
- `.opencode/agent/reviser.md`
- `.opencode/command/prove.md`
- `.opencode/command/research.md`
- `.opencode/command/implement.md`

### To Be Created (Phase 4)
- `.opencode/command/verify.md`
- `.opencode/command/explore.md`
- `.opencode/command/search-type.md`

---

## Questions to Resolve

### MCP Server Availability
- ✓ lean-lsp-mcp: Confirmed available via uvx
- ⬜ LeanExplore: Need to verify installation method
- ⬜ Loogle: Need to verify installation method
- ⬜ LeanSearch: Need to verify installation method

### Technical Details
- ⬜ What are the exact tool names/signatures for each MCP server?
- ⬜ What are the actual installation commands?
- ⬜ Are there API keys or authentication required?
- ⬜ What are the rate limits or usage constraints?

### Integration Details
- ⬜ How do we handle MCP server failures gracefully?
- ⬜ What caching strategy should we use?
- ⬜ How do we merge results from multiple search tools?
- ⬜ What timeout values are appropriate?

---

## Resources

### Documentation
- Full Plan: [mcp-integration-plan.md](./mcp-integration-plan.md)
- Current System: [../.opencode/README.md](../.opencode/README.md)
- Architecture: [../.opencode/docs/ARCHITECTURE.md](../.opencode/docs/ARCHITECTURE.md)

### MCP Servers
- lean-lsp-mcp: Already configured in `.mcp.json`
- LeanExplore: Research needed
- Loogle: Research needed
- LeanSearch: Research needed

### Related Projects
- Lean 4: https://leanprover.github.io/
- Mathlib: https://github.com/leanprover-community/mathlib4
- Model Context Protocol: https://modelcontextprotocol.io/

---

## Contact & Feedback

For questions, suggestions, or issues with this plan:
1. Review the full plan in `mcp-integration-plan.md`
2. Check the current system documentation
3. Test MCP server availability
4. Begin with Phase 1 implementation

**Plan Status**: Ready for Review and Implementation  
**Last Updated**: 2025-12-15  
**Version**: 1.0
