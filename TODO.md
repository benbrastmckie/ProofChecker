# TODO.md - ProofChecker Task Tracking

## Overview

This file serves as the central task tracking system for ProofChecker development. It organizes all pending work by priority (High/Medium/Low), tracks `sorry` placeholders requiring resolution, documents missing files, and provides actionable next steps for systematic project development.

**Purpose**: Maintain a comprehensive view of remaining implementation work for Layer 0 (Core TM) completion and beyond.

**Organization**: Tasks are prioritized based on blocking status, dependency relationships, and estimated effort. High priority tasks should be completed within 1 month, medium priority within 3 months, and low priority represents future work.

**Related Documentation**:
- [IMPLEMENTATION_STATUS.md](docs/IMPLEMENTATION_STATUS.md) - Detailed module-by-module completion tracking
- [KNOWN_LIMITATIONS.md](docs/KNOWN_LIMITATIONS.md) - Comprehensive gap documentation with workarounds
- [ARCHITECTURE.md](docs/ARCHITECTURE.md) - System design and TM logic specification

**How to Use This File**:
1. Review High Priority tasks first - these are blocking or urgent
2. Check dependencies before starting a task (see Dependency Graph section)
3. Mark completed tasks with completion date in Progress Tracking section
4. Update `sorry` registry as placeholders are resolved
5. Cross-reference with IMPLEMENTATION_STATUS.md for detailed module status

---

## High Priority Tasks

### 1. Fix CI Continue-on-Error Flags
**Effort**: 1-2 hours
**Status**: Not Started
**Priority**: High (CI quality, affects all development)

**Description**: Remove `continue-on-error: true` flags from CI configuration that are masking test/lint/docs failures.

**Files**:
- `.github/workflows/ci.yml` (lines 45, 49, 77, 86)

**Action Items**:
1. Audit `lake test` command - if tests pass, remove flag at line 45
2. Verify `lake lint` is configured - if working, remove flag at line 49
3. Check `lake build :docs` target exists in lakefile.toml - if working, remove flag at line 77
4. Test GitHub Pages deployment - if successful, remove flag at line 86
5. Add build status badge to README.md

**Blocking**: None (independent task)

**Dependencies**: None

---

### 2. Add Propositional Axioms
**Effort**: 10-15 hours
**Status**: Not Started
**Priority**: High (unblocks P1-P2 in Perpetuity.lean)

**Description**: Add propositional reasoning infrastructure (K and S axioms) to enable basic propositional theorem proving without meta-reasoning.

**Files**:
- `ProofChecker/ProofSystem/Axioms.lean` (add axioms)
- `ProofChecker/Theorems/Perpetuity.lean` (lines 88, 139 - remove `sorry` from helpers)

**Action Items**:
1. Add K axiom: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
2. Add S axiom: `φ → (ψ → φ)`
3. Prove `imp_trans` helper from K and S axioms (remove `sorry` at line 88)
4. Prove `contraposition` helper from K and S axioms (remove `sorry` at line 139)
5. Update ProofSystem/Derivation.lean to include new axioms
6. Write tests in ProofCheckerTest/ProofSystem/AxiomsTest.lean
7. Update IMPLEMENTATION_STATUS.md axiom count (8 → 10 axioms)

**Blocking**: P1-P2 perpetuity proofs (lines 88, 139), P4-P6 perpetuity proofs

**Dependencies**: None

**Next After This**: Complete Perpetuity P1-P2 (remove `sorry` after helpers proven)

---

### 3. Complete Archive Examples
**Effort**: 5-10 hours
**Status**: Not Started
**Priority**: High (documentation accuracy, pedagogical value)

**Description**: Create missing Archive example files (ModalProofs.lean, TemporalProofs.lean) to match documentation claims and provide pedagogical value.

**Files**:
- `Archive/ModalProofs.lean` (missing, referenced in CLAUDE.md line 494, README.md line 214)
- `Archive/TemporalProofs.lean` (missing, referenced in CLAUDE.md line 499, README.md line 215)
- `docs/IMPLEMENTATION_STATUS.md` (line 506 - update Archive status from "Complete" to accurate)

**Action Items**:
1. Create `Archive/ModalProofs.lean` with S5 modal logic examples:
   - Modal T axiom application (necessity implies truth)
   - Modal 4 axiom application (necessity of necessity)
   - Modal B axiom application (truth implies possible necessity)
   - Derived modal theorems
2. Create `Archive/TemporalProofs.lean` with temporal reasoning examples:
   - Temporal axiom applications (TA, TL, TF)
   - Temporal duality examples (past/future)
   - Interaction with modal operators
3. Update `Archive/Archive.lean` to re-export new modules
4. Write tests in `ProofCheckerTest/Archive/` (if needed)
5. Update IMPLEMENTATION_STATUS.md Archive status to reflect 3/3 files complete

**Blocking**: None (independent task)

**Dependencies**: None

---

### 4. Create TODO.md 
**Effort**: 2-3 hours
**Status**: COMPLETE (2025-12-01)
**Priority**: High (task tracking infrastructure)

**Description**: Create comprehensive TODO.md file at project root for systematic task tracking and priority management.

**Files**:
- `/home/benjamin/Documents/Philosophy/Projects/ProofChecker/TODO.md` (this file)

**Action Items**:  All completed

**Blocking**: None (this is the tracking file itself)

**Dependencies**: None

---

## Medium Priority Tasks

### 5. Complete Soundness Proofs
**Effort**: 15-20 hours
**Status**: Not Started
**Priority**: Medium (metalogic completeness, Layer 0 finalization)

**Description**: Complete missing soundness proofs for TL, MF, TF axioms and modal_k, temporal_k, temporal_duality rules. This requires analyzing frame constraints and either adding them to TaskFrame or documenting axioms as conditional.

**Files**:
- `ProofChecker/Metalogic/Soundness.lean`
  - Line 252: TL axiom validity (backward temporal persistence constraint needed)
  - Line 295: MF axiom validity (temporal persistence of necessity constraint needed)
  - Line 324: TF axiom validity (necessity persistence across times constraint needed)
  - Line 398: modal_k rule soundness (modal uniformity of contexts)
  - Line 416: temporal_k rule soundness (temporal uniformity of contexts)
  - Line 431: temporal_duality soundness (semantic duality lemma)

**Action Items**:
1. Analyze frame constraints required for TL, MF, TF axioms
2. Design frame constraint architecture:
   - Option A: Add constraints to `ProofChecker/Semantics/TaskFrame.lean`
   - Option B: Document axioms as conditional on frame properties
3. Implement chosen approach
4. Prove TL, MF, TF axiom validity with frame constraints
5. Prove modal_k and temporal_k rule soundness
6. Prove temporal_duality soundness with semantic duality lemma
7. Remove all 15 `sorry` placeholders from Soundness.lean
8. Write tests for new soundness proofs
9. Update IMPLEMENTATION_STATUS.md Soundness status (60% → 100%)

**Blocking**: None (soundness is metalogic property, doesn't block derivations)

**Dependencies**: None (but benefits from propositional axioms for proof techniques)

**Next After This**: Update documentation to reflect full soundness

---

### 6. Complete Perpetuity Proofs
**Effort**: 20-30 hours
**Status**: Not Started
**Priority**: Medium (theorem completeness)

**Description**: Complete proofs for perpetuity principles P4-P6, which require complex modal-temporal interactions.

**Files**:
- `ProofChecker/Theorems/Perpetuity.lean`
  - Line 225: P4 (`◇▽φ → ◇φ`) - contraposition of P3 with nested formulas
  - Line 252: P5 (`◇▽φ → △◇φ`) - persistent possibility
  - Line 280: P6 (`▽□φ → □△φ`) - occurrent necessity is perpetual

**Action Items**:
1. After propositional axioms added, prove P4 using corrected contraposition
2. Develop lemmas for modal-temporal operator interactions:
   - Lemma: `□△` and `◇▽` interaction
   - Lemma: `△◇` and `▽□` interaction
   - Lemma: Nesting properties for box-future and diamond-past
3. Prove P5 from interaction lemmas
4. Prove P6 from interaction lemmas
5. Remove all 3 `sorry` placeholders (lines 225, 252, 280)
6. Write comprehensive tests for P4-P6
7. Update IMPLEMENTATION_STATUS.md Perpetuity status (50% → 100%)

**Blocking**: None (perpetuity principles are theorems, don't block other work)

**Dependencies**:
- **REQUIRES**: Task 2 (Add Propositional Axioms) - P4-P6 need propositional helpers
- **BENEFITS FROM**: Task 5 (Complete Soundness) - for proof techniques

---

### 7. Implement Core Automation
**Effort**: 40-60 hours
**Status**: Not Started
**Priority**: Medium (developer productivity, proof automation)

**Description**: Implement 3-4 most useful tactics to replace axiom stubs with real implementations using LEAN 4's `Lean.Elab.Tactic` API.

**Files**:
- `ProofChecker/Automation/Tactics.lean` (8 axiom stubs, lines 102-141)
- `ProofChecker/Automation/ProofSearch.lean` (8 axiom stubs, lines 133-176)

**Action Items**:
1. Implement `apply_axiom` tactic (generic axiom application)
2. Implement `modal_t` tactic (modal T axiom: `□φ → φ`)
3. Implement `tm_auto` tactic (simple automation combining common patterns)
4. Implement `assumption_search` helper (search premises for goal)
5. Replace axiom declarations with real implementations
6. Write comprehensive tests in `ProofCheckerTest/Automation/TacticsTest.lean`
7. Update `docs/development/TACTIC_DEVELOPMENT.md` with implementation examples
8. Update IMPLEMENTATION_STATUS.md Automation status (0% → 40-50%)

**Blocking**: None (automation is productivity tool, doesn't block correctness)

**Dependencies**: None (can start anytime, benefits from all proven theorems)

**Phased Approach**:
- Phase 1 (15-20 hours): Implement `apply_axiom` and `modal_t` (most useful)
- Phase 2 (15-20 hours): Implement `tm_auto` (combines Phase 1 tactics)
- Phase 3 (10-20 hours): Implement `assumption_search` and additional helpers

---

### 8. Fix WorldHistory Universal Helper
**Effort**: 1-2 hours
**Status**: Not Started
**Priority**: Medium (completeness, minor gap)

**Description**: Prove `respects_task` property for universal history helper function.

**Files**:
- `ProofChecker/Semantics/WorldHistory.lean` (line 75 - `sorry` in universal helper)

**Action Items**:
1. Analyze universal history helper requirements
2. Prove `respects_task` property for specific frames
3. Remove `sorry` at line 75
4. Add test case for universal history in `ProofCheckerTest/Semantics/WorldHistoryTest.lean`
5. Update IMPLEMENTATION_STATUS.md Semantics status (note: 1 `sorry` → 0 `sorry`)

**Blocking**: None (helper function, doesn't block main semantics)

**Dependencies**: None

---

### 12. Create Comprehensive Tactic Test Suite
**Effort**: 10-15 hours
**Status**: Not Started
**Priority**: Medium (concurrent with Task 7, follows TDD approach)

**Description**: Develop comprehensive test suite for automation package following test
patterns from LEAN 4 best practices. Includes unit tests for individual tactics,
integration tests for tactic combinations, and property-based tests for correctness.

**Files**:
- `ProofCheckerTest/Automation/TacticsTest.lean` (to be created)
- `ProofCheckerTest/Automation/ProofSearchTest.lean` (to be created)

**Action Items**:
1. Create `TacticsTest.lean` with test structure following LEAN 4 test patterns
2. Write unit tests for each tactic (apply_axiom, modal_t, tm_auto, assumption_search)
3. Write integration tests for tactic combinations and common proof patterns
4. Write property-based tests verifying tactic correctness properties
5. Test error handling (invalid goals, failed applications, edge cases)
6. Test performance on realistic proof scenarios (benchmarking)
7. Document test patterns in test file comments
8. Update IMPLEMENTATION_STATUS.md Automation test coverage

**Blocking**: None (tests can be written before implementation using `sorry` placeholders)

**Dependencies**:
- **CONCURRENT WITH**: Task 7 (Implement Core Automation) - follows TDD approach
- **BENEFITS FROM**: Documentation/Development/TACTIC_DEVELOPMENT.md for test patterns

**Test Patterns Reference**: Best practices report (.claude/specs/
021_lean4_bimodal_logic_best_practices/reports/001-lean-4-modal-logic-
implementation-best.md) lines 619-648

**Notes**: Following TDD, tests should be written before or alongside implementation,
not after. Test file can use `sorry` for unimplemented tactics initially.

---

## Low Priority Tasks

### 9. Begin Completeness Proofs
**Effort**: 70-90 hours
**Status**: Not Started
**Priority**: Low (long-term metalogic goal)

**Description**: Implement canonical model construction and prove completeness theorems (weak and strong). This is a major undertaking requiring significant effort.

**Files**:
- `ProofChecker/Metalogic/Completeness.lean`
  - Line 116: lindenbaum (maximal consistent extension)
  - Line 140: maximal_consistent_closed (closure under MP)
  - Line 154: maximal_negation_complete (negation completeness)
  - Line 199: canonical_task_rel (task relation from derivability)
  - Line 210: canonical_frame (frame from maximal consistent sets)
  - Line 235: canonical_valuation (valuation from maximal sets)
  - Line 242: canonical_model (model construction)
  - Line 263: canonical_history (history from maximal sets)
  - Line 297: truth_lemma (truth preservation in canonical model)
  - Line 326: weak_completeness (`⊨ φ → ⊢ φ`)
  - Line 346: strong_completeness (`Γ ⊨ φ → Γ ⊢ φ`)

**Action Items**:
1. **Phase 1** (20-30 hours): Prove Lindenbaum lemma and maximal set properties
   - Prove lindenbaum (maximal consistent extension exists)
   - Prove maximal_consistent_closed (closure under modus ponens)
   - Prove maximal_negation_complete (for every φ, either φ or ¬φ in set)
2. **Phase 2** (20-30 hours): Construct canonical model components
   - Define canonical_task_rel from derivability relation
   - Prove canonical_frame satisfies nullity and compositionality
   - Define canonical_valuation from maximal sets
   - Combine into canonical_model
3. **Phase 3** (20-30 hours): Prove truth lemma and completeness
   - Define canonical_history for temporal operators
   - Prove truth_lemma by induction on formula structure
   - Prove weak_completeness from truth lemma
   - Prove strong_completeness from weak completeness
4. Replace all 11 axiom declarations with actual proofs
5. Write comprehensive tests in `ProofCheckerTest/Metalogic/CompletenessTest.lean`
6. Update IMPLEMENTATION_STATUS.md Completeness status (0% → 100%)

**Blocking**: None (metalogic property, doesn't block derivations or applications)

**Dependencies**:
- **BENEFITS FROM**: Task 5 (Complete Soundness) - for metalogic proof techniques
- **BENEFITS FROM**: Task 2 (Add Propositional Axioms) - for completeness proof techniques

**Notes**: This is the largest remaining task for Layer 0 completion. Can be deferred to Layer 1 planning phase.

---

### 10. Create Decidability Module
**Effort**: 40-60 hours
**Status**: Not Started
**Priority**: Low (future enhancement, not in MVP)

**Description**: Create ProofChecker/Metalogic/Decidability.lean module with tableau method for validity checking and satisfiability decision procedures.

**Files**:
- `ProofChecker/Metalogic/Decidability.lean` (does not exist, planned in CLAUDE.md line 318)

**Action Items**:
1. **Phase 1** (15-20 hours): Design decidability architecture
   - Analyze complexity (EXPTIME for S5 modal, PSPACE for LTL)
   - Design tableau method for TM logic
   - Plan satisfiability decision procedure
2. **Phase 2** (15-20 hours): Implement tableau method
   - Implement systematic tableau construction
   - Implement closure rules for TM operators
   - Implement satisfiability checking
3. **Phase 3** (10-20 hours): Prove correctness and complexity
   - Prove tableau method sound and complete
   - Analyze time/space complexity
   - Document complexity bounds
4. Write comprehensive tests in `ProofCheckerTest/Metalogic/DecidabilityTest.lean`
5. Update documentation with decidability results
6. Update IMPLEMENTATION_STATUS.md to add Decidability module

**Blocking**: None (enhancement, doesn't affect existing functionality)

**Dependencies**:
- **REQUIRES**: Task 9 (Begin Completeness Proofs) - correctness proofs depend on completeness
- **BENEFITS FROM**: Task 7 (Implement Core Automation) - for automated search

**Notes**: Planned but not essential for Layer 0. Can be deferred to Layer 1 or beyond.

---

### 11. Plan Layer 1/2/3 Extensions
**Effort**: Research phase (20-40 hours initial planning)
**Status**: Not Started
**Priority**: Low (future work, after Layer 0 complete)

**Description**: Design and plan extensions beyond Core TM (Layer 0): counterfactual operators (Layer 1), epistemic operators (Layer 2), normative operators (Layer 3).

**Action Items**:
1. **Layer 1 (Counterfactuals)**: Design counterfactual operators and semantics
   - Research counterfactual logic approaches
   - Design `□c` (would-counterfactual) and `◇m` (might-counterfactual) operators
   - Specify task semantics for counterfactuals
   - Document architectural changes needed
2. **Layer 2 (Epistemic)**: Design epistemic operators (knowledge, belief)
   - Design `K` (knowledge) and `B` (belief) operators
   - Specify multi-agent epistemic semantics
   - Plan integration with TM and counterfactuals
3. **Layer 3 (Normative)**: Design deontic/normative operators
   - Design `O` (obligation) and `P` (permission) operators
   - Specify normative task semantics
   - Plan interaction with epistemic and modal operators
4. Create implementation plans for each layer
5. Update ARCHITECTURE.md with layer design

**Blocking**: None (future work)

**Dependencies**:
- **REQUIRES**: Layer 0 completion and stability
- **REQUIRES**: Tasks 1-8 complete (high and medium priority)

**Notes**: This is strategic planning for post-MVP development. Should not begin until Layer 0 is complete and tested.

---

### 13. Create Proof Strategy Documentation
**Effort**: 5-10 hours
**Status**: Not Started
**Priority**: Low (pedagogical, not blocking)

**Description**: Create Archive/ examples demonstrating common proof strategies and
patterns for TM derivations. Provides pedagogical value for new users, students, and
researchers learning TM logic and ProofChecker usage.

**Files**:
- `Archive/ModalProofStrategies.lean` (to be created)
- `Archive/TemporalProofStrategies.lean` (to be created)
- `Archive/BimodalProofStrategies.lean` (to be created)

**Action Items**:
1. Create `ModalProofStrategies.lean` with S5 modal proof patterns (necessity chains,
   possibility proofs, modal modus ponens)
2. Create `TemporalProofStrategies.lean` with temporal reasoning patterns (always/
   eventually proofs, induction over time, temporal duality)
3. Create `BimodalProofStrategies.lean` with modal-temporal interaction patterns
   (perpetuity principles, frame reasoning, task relation proofs)
4. Document common proof techniques in extensive comments
5. Update `Archive/Archive.lean` to re-export new modules

**Blocking**: None (independent documentation task)

**Dependencies**: None (can be created anytime, benefits from completed proofs)

**Audience**: New users, students, researchers learning TM logic

**Reference**: Best practices report (.claude/specs/
021_lean4_bimodal_logic_best_practices/reports/001-lean-4-modal-logic-
implementation-best.md) lines 649-675

**Notes**: These are pedagogical examples, not required for project functionality.
Can be deferred until after core implementation is stable.

---

## Sorry Placeholder Registry

This section lists all 41 `sorry` placeholders in the codebase that require resolution. Each entry includes the file, line number, context, and recommended resolution approach.

### ProofChecker/Semantics/WorldHistory.lean (1 sorry)

- **WorldHistory.lean:75** - `universal` helper function
  - **Context**: Universal history that maps all times to the same world state
  - **Resolution**: Prove `respects_task` property for universal history
  - **Effort**: 1-2 hours
  - **See**: Task 8 (Fix WorldHistory Universal Helper)

### ProofChecker/Theorems/Perpetuity.lean (14 sorry)

**Propositional Helpers** (2 sorry):
- **Perpetuity.lean:88** - `imp_trans` propositional helper
  - **Context**: `(φ → ψ) → (ψ → χ) → (φ → χ)` transitive implication
  - **Resolution**: Prove from K and S propositional axioms
  - **Effort**: 2-3 hours (after axioms added)
  - **See**: Task 2 (Add Propositional Axioms)

- **Perpetuity.lean:139** - `contraposition` propositional helper
  - **Context**: `(φ → ψ) → (¬ψ → ¬φ)` contrapositive reasoning
  - **Resolution**: Prove from K and S propositional axioms
  - **Effort**: 2-3 hours (after axioms added)
  - **See**: Task 2 (Add Propositional Axioms)

**Perpetuity Principles** (3 sorry):
- **Perpetuity.lean:225** - P4 (`◇▽φ → ◇φ`)
  - **Context**: Possibility of occurrence implies possibility
  - **Resolution**: Use corrected contraposition after propositional axioms added
  - **Effort**: 8-10 hours (complex nested formulas)
  - **See**: Task 6 (Complete Perpetuity Proofs)

- **Perpetuity.lean:252** - P5 (`◇▽φ → △◇φ`)
  - **Context**: Persistent possibility (possible occurrence implies always possible)
  - **Resolution**: Develop modal-temporal interaction lemmas
  - **Effort**: 10-12 hours (complex modal-temporal interaction)
  - **See**: Task 6 (Complete Perpetuity Proofs)

- **Perpetuity.lean:280** - P6 (`▽□φ → □△φ`)
  - **Context**: Occurrent necessity is perpetual
  - **Resolution**: Develop modal-temporal interaction lemmas
  - **Effort**: 10-12 hours (complex modal-temporal interaction)
  - **See**: Task 6 (Complete Perpetuity Proofs)

### ProofChecker/Automation/ProofSearch.lean (3 sorry)

- **ProofSearch.lean:186** - Example usage documentation
  - **Context**: Example proof search usage (documentation `sorry`)
  - **Resolution**: Implement proof search functions, then replace with real examples
  - **Effort**: 1 hour (after search implemented)
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:191** - Example usage documentation
  - **Context**: Example heuristic search usage (documentation `sorry`)
  - **Resolution**: Implement heuristic search, then replace with real examples
  - **Effort**: 1 hour (after search implemented)
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:196** - Example cached search usage
  - **Context**: Example cached search usage (documentation `sorry`)
  - **Resolution**: Implement cached search, then replace with real examples
  - **Effort**: 1 hour (after search implemented)
  - **See**: Task 7 (Implement Core Automation)

### ProofChecker/Metalogic/Soundness.lean (15 sorry)

**Axiom Soundness** (3 sorry):
- **Soundness.lean:252** - TL axiom validity
  - **Context**: `△φ → ○φ` (always implies next) requires backward temporal persistence
  - **Resolution**: Add frame constraint or document as conditional
  - **Effort**: 5-7 hours (frame constraint architecture)
  - **See**: Task 5 (Complete Soundness Proofs)

- **Soundness.lean:295** - MF axiom validity
  - **Context**: `□○φ → ○□φ` (modal-future interaction) requires temporal persistence of necessity
  - **Resolution**: Add frame constraint or document as conditional
  - **Effort**: 5-7 hours (frame constraint architecture)
  - **See**: Task 5 (Complete Soundness Proofs)

- **Soundness.lean:324** - TF axiom validity
  - **Context**: `○□φ → □○φ` (temporal-future-modal interaction) requires necessity persistence
  - **Resolution**: Add frame constraint or document as conditional
  - **Effort**: 5-7 hours (frame constraint architecture)
  - **See**: Task 5 (Complete Soundness Proofs)

**Rule Soundness** (3 sorry):
- **Soundness.lean:398** - modal_k rule soundness
  - **Context**: Modal K rule requires modal uniformity of contexts
  - **Resolution**: Prove context preservation for modal operators
  - **Effort**: 3-5 hours
  - **See**: Task 5 (Complete Soundness Proofs)

- **Soundness.lean:416** - temporal_k rule soundness
  - **Context**: Temporal K rule requires temporal uniformity of contexts
  - **Resolution**: Prove context preservation for temporal operators
  - **Effort**: 3-5 hours
  - **See**: Task 5 (Complete Soundness Proofs)

- **Soundness.lean:431** - temporal_duality soundness
  - **Context**: Temporal duality rule requires semantic duality lemma
  - **Resolution**: Prove duality between past and future operators
  - **Effort**: 3-5 hours
  - **See**: Task 5 (Complete Soundness Proofs)

### ProofChecker/Metalogic/Completeness.lean (11 axiom declarations)

**Note**: These are axiom declarations (unproven theorems), not `sorry` placeholders, but require the same resolution attention.

- **Completeness.lean:116** - lindenbaum
  - **Context**: Every consistent set extends to maximal consistent set
  - **Resolution**: Prove using Zorn's lemma or transfinite induction
  - **Effort**: 10-15 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 1

- **Completeness.lean:140** - maximal_consistent_closed
  - **Context**: Maximal consistent sets closed under modus ponens
  - **Resolution**: Prove from maximality and consistency
  - **Effort**: 5-7 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 1

- **Completeness.lean:154** - maximal_negation_complete
  - **Context**: For every φ, either φ or ¬φ in maximal set
  - **Resolution**: Prove from maximality
  - **Effort**: 5-7 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 1

- **Completeness.lean:199** - canonical_task_rel
  - **Context**: Task relation from derivability
  - **Resolution**: Define relation, prove respects derivability
  - **Effort**: 8-10 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 2

- **Completeness.lean:210** - canonical_frame
  - **Context**: Frame from maximal consistent sets
  - **Resolution**: Prove frame axioms (nullity, compositionality)
  - **Effort**: 10-12 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 2

- **Completeness.lean:235** - canonical_valuation
  - **Context**: Valuation from maximal sets (atom membership)
  - **Resolution**: Define valuation function
  - **Effort**: 3-5 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 2

- **Completeness.lean:242** - canonical_model
  - **Context**: Combine canonical frame and valuation
  - **Resolution**: Construct model from components
  - **Effort**: 2-3 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 2

- **Completeness.lean:263** - canonical_history
  - **Context**: History from maximal sets for temporal operators
  - **Resolution**: Define history function, prove respects task
  - **Effort**: 8-10 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 3

- **Completeness.lean:297** - truth_lemma
  - **Context**: `φ ∈ Γ ↔ truth_at canonical_model canonical_history Γ t φ`
  - **Resolution**: Prove by induction on formula structure
  - **Effort**: 15-20 hours (most complex proof)
  - **See**: Task 9 (Begin Completeness Proofs), Phase 3

- **Completeness.lean:326** - weak_completeness
  - **Context**: `⊨ φ → ⊢ φ` (valid implies derivable)
  - **Resolution**: Prove from truth lemma using canonical model
  - **Effort**: 5-7 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 3

- **Completeness.lean:346** - strong_completeness
  - **Context**: `Γ ⊨ φ → Γ ⊢ φ` (semantic consequence implies derivability)
  - **Resolution**: Prove from weak completeness
  - **Effort**: 5-7 hours
  - **See**: Task 9 (Begin Completeness Proofs), Phase 3

### ProofChecker/Automation/Tactics.lean (8 axiom declarations)

**Note**: These are axiom stubs for tactic helper functions, should be replaced with real implementations.

- **Tactics.lean:102** - modal_k_tactic_stub
  - **Resolution**: Implement using LEAN 4 tactic API
  - **Effort**: 5-8 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:109** - temporal_k_tactic_stub
  - **Resolution**: Implement using LEAN 4 tactic API
  - **Effort**: 5-8 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:116** - mp_chain_stub
  - **Resolution**: Implement modus ponens chaining
  - **Effort**: 3-5 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:123** - assumption_search_stub
  - **Resolution**: Implement premise search
  - **Effort**: 3-5 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:132** - is_box_formula
  - **Resolution**: Implement formula pattern matching
  - **Effort**: 1-2 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:135** - is_future_formula
  - **Resolution**: Implement formula pattern matching
  - **Effort**: 1-2 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:138** - extract_from_box
  - **Resolution**: Implement modal operator extraction
  - **Effort**: 2-3 hours
  - **See**: Task 7 (Implement Core Automation)

- **Tactics.lean:141** - extract_from_future
  - **Resolution**: Implement temporal operator extraction
  - **Effort**: 2-3 hours
  - **See**: Task 7 (Implement Core Automation)

### ProofChecker/Automation/ProofSearch.lean (8 axiom declarations)

- **ProofSearch.lean:133** - bounded_search
  - **Resolution**: Implement depth-bounded search
  - **Effort**: 8-10 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:146** - search_with_heuristics
  - **Resolution**: Implement heuristic-guided search
  - **Effort**: 10-12 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:156** - search_with_cache
  - **Resolution**: Implement cached search
  - **Effort**: 10-12 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:164** - matches_axiom
  - **Resolution**: Implement axiom pattern matching
  - **Effort**: 3-5 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:167** - find_implications_to
  - **Resolution**: Implement implication chain search
  - **Effort**: 5-7 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:170** - heuristic_score
  - **Resolution**: Implement formula heuristic scoring
  - **Effort**: 3-5 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:173** - box_context
  - **Resolution**: Implement modal context extraction
  - **Effort**: 2-3 hours
  - **See**: Task 7 (Implement Core Automation)

- **ProofSearch.lean:176** - future_context
  - **Resolution**: Implement temporal context extraction
  - **Effort**: 2-3 hours
  - **See**: Task 7 (Implement Core Automation)

---

## Missing Files

This section lists files that are referenced in documentation but do not exist in the repository.

### 1. Archive/ModalProofs.lean
**Priority**: High
**Effort**: 3-5 hours
**Referenced In**: CLAUDE.md (line 494), README.md (line 214)

**Description**: Pedagogical examples for S5 modal logic proofs using ProofChecker.

**Creation Plan**:
1. Create file with module header and imports
2. Add modal T axiom examples (necessity implies truth)
3. Add modal 4 axiom examples (necessity of necessity)
4. Add modal B axiom examples (truth implies possible necessity)
5. Add derived modal theorem examples
6. Document with explanatory comments
7. Update Archive/Archive.lean to re-export module

**See**: Task 3 (Complete Archive Examples)

### 2. Archive/TemporalProofs.lean
**Priority**: High
**Effort**: 3-5 hours
**Referenced In**: CLAUDE.md (line 499), README.md (line 215)

**Description**: Pedagogical examples for temporal logic proofs using ProofChecker.

**Creation Plan**:
1. Create file with module header and imports
2. Add temporal axiom examples (TA, TL, TF)
3. Add temporal duality examples (past/future)
4. Add modal-temporal interaction examples
5. Document with explanatory comments
6. Update Archive/Archive.lean to re-export module

**See**: Task 3 (Complete Archive Examples)

### 3. ProofChecker/Metalogic/Decidability.lean
**Priority**: Low
**Effort**: 40-60 hours
**Referenced In**: CLAUDE.md (line 318), IMPLEMENTATION_STATUS.md (line 319)

**Description**: Decidability module with tableau method and satisfiability decision procedures.

**Creation Plan**:
1. Design tableau method for TM logic
2. Implement systematic tableau construction
3. Implement satisfiability checking
4. Prove soundness and completeness of tableau method
5. Analyze and document complexity bounds
6. Write comprehensive tests
7. Update documentation

**See**: Task 10 (Create Decidability Module)

---

## Dependency Graph

This section shows task prerequisite relationships and identifies parallel execution opportunities.

### High Priority Dependencies

```
Task 1 (Fix CI Flags)
  → Independent, can run anytime
  → Enables: Reliable CI feedback for all tasks

Task 2 (Add Propositional Axioms)
  → Independent, no prerequisites
  → Unblocks: Task 6 (Complete Perpetuity P1-P2, P4-P6)
  → Unblocks: Perpetuity.lean:88, 139 (propositional helpers)

Task 3 (Complete Archive Examples)
  → Independent, can run anytime
  → No blockers

Task 4 (Create TODO.md) 
  → COMPLETE
```

**Parallel Opportunities**: Tasks 1, 2, 3 can run in parallel (all independent).

### Medium Priority Dependencies

```
Task 5 (Complete Soundness Proofs)
  → Independent, no strict prerequisites
  → Benefits from: Task 2 (for proof techniques)
  → Unblocks: Documentation updates only (doesn't block functionality)

Task 6 (Complete Perpetuity Proofs)
  → REQUIRES: Task 2 (Add Propositional Axioms) - BLOCKING
  → Benefits from: Task 5 (for proof techniques)
  → After Task 2 complete, can proceed

Task 7 (Implement Core Automation)
  → Independent, can start anytime
  → Benefits from: All proven theorems (more automation targets)
  → Phased approach allows incremental progress

Task 8 (Fix WorldHistory Universal Helper)
  → Independent, can run anytime
  → No blockers

Task 12 (Create Tactic Test Suite)
  → CONCURRENT WITH: Task 7 (Implement Core Automation)
  → Independent, can start anytime
  → Follows TDD approach (tests written before/alongside implementation)
  → Benefits from: Documentation/Development/TACTIC_DEVELOPMENT.md
```

**Parallel Opportunities**: Tasks 5, 7, 8, 12 can run in parallel. Task 6 must wait
for Task 2. Task 12 should be concurrent with Task 7 per TDD methodology.

### Low Priority Dependencies

```
Task 9 (Begin Completeness Proofs)
  → Independent, can start anytime
  → Benefits from: Task 2 (for proof techniques)
  → Benefits from: Task 5 (for metalogic patterns)
  → Large task, phased approach recommended

Task 10 (Create Decidability Module)
  → REQUIRES: Task 9 (completeness proofs for correctness)
  → Benefits from: Task 7 (automation for search)

Task 11 (Plan Layer 1/2/3 Extensions)
  → REQUIRES: Layer 0 completion (Tasks 1-8 complete)
  → Strategic planning, not implementation

Task 13 (Create Proof Strategy Documentation)
  → Independent, can run anytime
  → No blockers
  → Benefits from: Completed proofs (more examples to document)
  → Pedagogical value for new users, students, researchers
```

**Parallel Opportunities**: Tasks 9 and 13 can run in parallel. Task 10 requires
Task 9 complete. Task 11 requires Layer 0 completion.

### Execution Waves (Optimal Ordering)

**Wave 1** (High Priority, Parallel):
- Task 1: Fix CI Flags (1-2 hours)
- Task 2: Add Propositional Axioms (10-15 hours)
- Task 3: Complete Archive Examples (5-10 hours)

**Wave 2** (Medium Priority, After Wave 1):
- Task 5: Complete Soundness Proofs (15-20 hours) - Can run parallel with 6, 7, 8, 12
- Task 6: Complete Perpetuity Proofs (20-30 hours) - AFTER Task 2, parallel with 5, 7, 8, 12
- Task 7: Implement Core Automation (40-60 hours, phased) - Can run parallel with 5, 6, 8, 12
- Task 8: Fix WorldHistory (1-2 hours) - Can run parallel with 5, 6, 7, 12
- Task 12: Create Tactic Test Suite (10-15 hours) - CONCURRENT with Task 7, parallel with 5, 6, 8

**Wave 3** (Low Priority, After Wave 2):
- Task 9: Begin Completeness Proofs (70-90 hours, phased) - Can start anytime, parallel with 13
- Task 10: Create Decidability Module (40-60 hours) - AFTER Task 9
- Task 13: Create Proof Strategy Documentation (5-10 hours) - Can run anytime, parallel with 9

**Wave 4** (Future Planning, After Layer 0 Complete):
- Task 11: Plan Layer 1/2/3 Extensions (20-40 hours research)

### Critical Path Analysis

**Shortest path to Layer 0 completion**:
1. Task 2 (Add Propositional Axioms) - 10-15 hours
2. Task 6 (Complete Perpetuity Proofs) - 20-30 hours (depends on Task 2)
3. Task 5 (Complete Soundness Proofs) - 15-20 hours (parallel with Task 6 after Task 2)
4. Task 7 (Implement Core Automation) - 40-60 hours (parallel with Tasks 5-6)
5. Task 8 (Fix WorldHistory) - 1-2 hours (parallel with any)
6. Task 1 (Fix CI Flags) - 1-2 hours (parallel with any)
7. Task 3 (Complete Archive Examples) - 5-10 hours (parallel with any)

**Total Sequential Time**: ~93-140 hours
**Estimated Parallel Time**: ~70-95 hours (with 2-3 parallel tasks)
**Time Savings**: ~25-32% with parallelization

---

## CI Technical Debt

This section documents `continue-on-error` flags in CI configuration that should be audited and removed as features complete.

### .github/workflows/ci.yml - Continue-on-Error Locations

**1. Line 45: Lake Test Continue-on-Error**
```yaml
- name: Run tests
  run: lake test
  continue-on-error: true
```
**Issue**: Tests are implemented and passing for completed modules, but CI ignores failures.
**Action**: Remove flag after verifying `lake test` passes on current codebase.
**Audit Command**: `cd /home/benjamin/Documents/Philosophy/Projects/ProofChecker && lake test`
**Priority**: High (masks test failures)

**2. Line 49: Lake Lint Continue-on-Error**
```yaml
- name: Run lint
  run: lake lint
  continue-on-error: true
```
**Issue**: Unclear if lint is configured correctly.
**Action**: Verify lint configuration, ensure zero warnings, then remove flag.
**Audit Command**: `cd /home/benjamin/Documents/Philosophy/Projects/ProofChecker && lake lint`
**Priority**: High (masks lint warnings)

**3. Line 77: Lake Build Docs Continue-on-Error**
```yaml
- name: Build documentation
  run: lake build :docs
  continue-on-error: true
```
**Issue**: Unclear if docs target is configured in lakefile.toml.
**Action**: Verify lakefile.toml has `:docs` target, test build, then remove flag.
**Audit Command**: `cd /home/benjamin/Documents/Philosophy/Projects/ProofChecker && lake build :docs`
**Priority**: Medium (docs generation, not critical for development)

**4. Line 86: GitHub Pages Deploy Continue-on-Error**
```yaml
- name: Deploy to GitHub Pages
  uses: peaceiris/actions-gh-pages@v3
  continue-on-error: true
```
**Issue**: Prevents deployment errors from failing CI job.
**Action**: Remove flag once docs are successfully generated and deployed to GitHub Pages.
**Audit**: Check if GitHub Pages is configured for repository, verify deployment works.
**Priority**: Medium (docs publishing, not critical for development)

### Audit Checklist

- [ ] Audit `lake test` (line 45) - Remove flag if tests pass
- [ ] Audit `lake lint` (line 49) - Remove flag if lint is configured and passes
- [ ] Audit `lake build :docs` (line 77) - Remove flag if docs target exists and builds
- [ ] Audit GitHub Pages deployment (line 86) - Remove flag if deployment works
- [ ] Add build status badge to README.md after flags removed
- [ ] Document CI configuration decisions in CONTRIBUTING.md

**See**: Task 1 (Fix CI Continue-on-Error Flags)

---

## Progress Tracking

This section tracks task completion with date stamps. Mark tasks complete here when finished.

### Completed Tasks

**High Priority**:
- [x] **Task 4**: Create TODO.md - COMPLETE (2025-12-01)

**Medium Priority**:
- [ ] None yet

**Low Priority**:
- [ ] None yet

### In Progress

- [ ] None currently

### Completion Log

| Date | Task | Notes |
|------|------|-------|
| 2025-12-01 | Task 4: Create TODO.md | Initial TODO.md creation complete with all sections |

### Status Summary

**Layer 0 Completion Progress**:
- High Priority: 1/4 tasks complete (25%)
- Medium Priority: 0/5 tasks complete (0%)
- Low Priority: 0/4 tasks complete (0%)
- **Overall**: 1/13 tasks complete (8%)

**Sorry Placeholder Resolution**:
- Total: 41 placeholders identified
- Resolved: 0
- Remaining: 41 (100%)

**Missing Files**:
- Total: 3 files identified
- Created: 0
- Remaining: 3 (100%)

**Estimated Effort to Layer 0 Completion**:
- High Priority Tasks: 16-30 hours remaining (Task 4 complete)
- Medium Priority Tasks: 87-128 hours (includes new Task 12: 10-15 hours)
- **Total**: 103-158 hours

**Estimated Effort to Full Completion (including Low Priority)**:
- Low Priority Tasks: 135-200 hours (includes new Task 13: 5-10 hours)
- **Grand Total**: 238-358 hours

---

## How to Update This File

When completing a task:
1. Mark the task checkbox in the appropriate section (High/Medium/Low Priority)
2. Add completion date and notes to the Completion Log table
3. Update Status Summary percentages
4. Remove corresponding `sorry` entries from Sorry Placeholder Registry (if applicable)
5. Update Missing Files section (if files were created)
6. Update IMPLEMENTATION_STATUS.md with detailed module changes
7. Cross-reference with KNOWN_LIMITATIONS.md (remove workarounds if gaps fixed)

When adding new tasks:
1. Add to appropriate priority section with effort estimate
2. Document dependencies in Dependency Graph section
3. Update Status Summary with new task count
4. If task resolves `sorry` placeholders, link to Sorry Placeholder Registry

---

## Notes

- This TODO.md is the **central task tracking system** for ProofChecker development
- For detailed module status and completion tracking, see [IMPLEMENTATION_STATUS.md](docs/IMPLEMENTATION_STATUS.md)
- For comprehensive gap documentation and workarounds, see [KNOWN_LIMITATIONS.md](docs/KNOWN_LIMITATIONS.md)
- For system design and TM logic specification, see [ARCHITECTURE.md](docs/ARCHITECTURE.md)
- Priority levels reflect blocking status and estimated timeline, not importance (all tasks are important for completeness)
- Effort estimates are conservative and may vary based on complexity during implementation
- Dependencies are explicitly tracked; always check Dependency Graph before starting a task
- CI technical debt should be resolved early to ensure reliable test feedback

**Last Updated**: 2025-12-01
