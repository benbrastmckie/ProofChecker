# Task 42b Research Report - Temporal K Infrastructure

**Date**: 2025-12-15  
**Status**: Research Complete - Ready for Implementation  
**Estimated Effort**: 11-16 hours  
**Priority**: Medium (blocked on architectural refactoring)

---

## Overview

This directory contains comprehensive research for completing **Task 42b: Proof Automation Phase 3 - Temporal K Infrastructure**. The task involves building infrastructure to derive `always_dni` and `always_dne` as theorems, reducing the axiom count by 2.

### Task Objectives

1. **PREREQUISITE**: Extract `lce_imp`, `rce_imp` to new `Propositional/Basics.lean` module
2. ✅ **COMPLETE**: Decomposition lemmas (`always_to_past`, `always_to_present`, `always_to_future`)
3. ✅ **COMPLETE**: Composition lemma (`past_present_future_to_always`)
4. Derive `always_dni`: `⊢ △φ → △(¬¬φ)` using K distributions
5. Derive `always_dne`: `⊢ △(¬¬φ) → △φ` using K distributions
6. Fix compilation errors and remove axiom declarations

### Current Blockers

1. **Derivable.height Axiomatization** (PRIMARY BLOCKER)
   - File: `Logos/Core/ProofSystem/Derivation.lean` (lines 168-222)
   - Issue: Height function and 7 properties are axiomatized
   - Impact: Blocks deduction theorem completion (3 sorry markers)
   - Resolution: Move definition to structural recursion pattern

2. **Circular Dependency** (ARCHITECTURAL BLOCKER)
   - Cycle: `Bridge.lean` → `DeductionTheorem.lean` → `Propositional.lean` → `Bridge.lean`
   - Issue: `lce_imp`, `rce_imp` needed by both DeductionTheorem and Bridge
   - Resolution: Extract to new `Propositional/Basics.lean` module

3. **Bridge.lean Compilation Errors** (5 errors)
   - Lines 415, 422, 476, 534: K axiom instantiation issues in `local_efq`
   - Line 543: Unknown identifier `neg_a_to_b_from_bot`
   - Resolution: Fix K axiom applications, implement missing helper

---

## Documents in This Directory

### 1. `task_42b_temporal_k_research_report.md` (75KB)

**Comprehensive research report covering:**

- **Topic 1: LEAN 4 Well-Founded Recursion Patterns**
  - Current state analysis (axiomatized height function)
  - Structural recursion patterns from Mathlib
  - `termination_by` and `decreasing_by` syntax
  - Code examples for `Derivable.height` definition
  - Height property proofs using `omega` tactic

- **Topic 2: Temporal K Distribution Derivation**
  - Derivation strategy for `future_k_dist`: `⊢ G(A → B) → (GA → GB)`
  - Deduction theorem application pattern
  - Temporal duality for `past_k_dist`
  - Connection to modal K distribution

- **Topic 3: Circular Dependency Resolution**
  - Module organization best practices
  - Extracting shared lemmas to break import cycles
  - `Propositional/Basics.lean` structure
  - Import graph analysis

- **Topic 4: Double Negation in Temporal Logic**
  - Decomposition/composition patterns for `always φ = Hφ ∧ φ ∧ Gφ`
  - Deriving `always_dni` using temporal K distribution
  - Deriving `always_dne` using temporal K distribution
  - Conjunction elimination helpers

**Key Resources:**
- LEAN 4 documentation links (well-founded recursion, termination)
- Mathlib code examples (List, Nat, Perm)
- Academic papers (Goldblatt, van Benthem, Blackburn)
- Zulip discussion threads
- Project-specific documentation references

### 2. `task_42b_implementation_guide.md` (15KB)

**Quick reference guide with step-by-step instructions:**

- **Step 1: Fix `Derivable.height`** (4-6 hours) ⚠️ **BLOCKER**
  - Move definition to `Derivation.lean`
  - Use structural recursion pattern
  - Prove 7 height properties as theorems
  - Update deduction theorem with `termination_by`
  - Delete axiom declarations

- **Step 2: Derive `future_k_dist`** (2-3 hours)
  - Apply deduction theorem twice
  - Use temporal_k inference rule
  - Derive `past_k_dist` via temporal duality
  - Remove axiom declarations

- **Step 3: Break Circular Dependency** (3-4 hours)
  - Create `Propositional/Basics.lean`
  - Extract `lce_imp`, `rce_imp`
  - Update imports in DeductionTheorem and Bridge
  - Test compilation

- **Step 4: Derive `always_dni` and `always_dne`** (2-3 hours)
  - Use decomposition lemmas (already implemented)
  - Apply temporal K distributions
  - Use composition lemma
  - Remove axiom declarations

**Includes:**
- Ready-to-use code snippets
- Testing commands for each step
- Troubleshooting tips
- Success criteria checklist

---

## Critical Path

```
Step 1: Fix Derivable.height (4-6 hours) ⚠️ PRIMARY BLOCKER
   ↓
Step 2: Derive future_k_dist (2-3 hours)
   ↓
Step 3: Break circular dependency (3-4 hours)
   ↓
Step 4: Derive always_dni/always_dne (2-3 hours)
```

**Total Estimated Time**: 11-16 hours

---

## Key Findings Summary

### 1. Well-Founded Recursion

**Current State:**
- `Derivable.height` is axiomatized (lines 168-222 in `Derivation.lean`)
- 7 height properties are axioms (unsound, no proofs)
- Deduction theorem has 3 sorry markers requiring termination proofs

**Solution:**
- Move `Derivable.height` to structural recursion pattern
- Prove height properties as theorems using `omega` tactic
- Update deduction theorem with `termination_by h.height`

**Code Pattern:**
```lean
def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, .axiom _ _ _ => 0
  | _, _, .assumption _ _ _ => 0
  | _, _, .modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, .necessitation _ d => d.height + 1
  | _, _, .temporal_necessitation _ d => d.height + 1
  | _, _, .temporal_duality _ d => d.height + 1
  | _, _, .weakening _ _ _ d _ => d.height + 1
```

### 2. Temporal K Distribution

**Derivation Strategy:**
1. Start with `[A → B, A] ⊢ B` (modus ponens)
2. Apply `temporal_k` to get `[G(A → B), GA] ⊢ GB`
3. Apply deduction theorem: `[G(A → B)] ⊢ GA → GB`
4. Apply deduction theorem again: `⊢ G(A → B) → (GA → GB)`

**Dependencies:**
- Requires complete deduction theorem (Step 1)
- Uses `temporal_k` inference rule (already implemented)
- Mirrors modal K distribution pattern

### 3. Circular Dependency

**Problem:**
```
Bridge.lean → DeductionTheorem.lean → Propositional.lean → Bridge.lean
```

**Solution:**
Create new module `Logos/Core/Theorems/Propositional/Basics.lean`:
```lean
-- Extract these from Propositional.lean
theorem lce_imp (A B : Formula) : ⊢ (A.and B).imp A := ...
theorem rce_imp (A B : Formula) : ⊢ (A.and B).imp B := ...
```

Update imports:
- `DeductionTheorem.lean`: `import Logos.Core.Theorems.Propositional.Basics`
- `Bridge.lean`: `import Logos.Core.Theorems.Propositional.Basics`
- `Propositional.lean`: Can import Bridge without cycle

### 4. Double Negation in Temporal Logic

**Decomposition Pattern:**
```lean
always φ = Hφ ∧ φ ∧ Gφ

-- Already implemented:
theorem always_to_past : ⊢ △φ → Hφ
theorem always_to_present : ⊢ △φ → φ
theorem always_to_future : ⊢ △φ → Gφ
theorem past_present_future_to_always : ⊢ (Hφ ∧ (φ ∧ Gφ)) → △φ
```

**Derivation of `always_dni`:**
1. Decompose `△φ` into `Hφ ∧ φ ∧ Gφ`
2. Apply `dni` to `φ`: `φ → ¬¬φ`
3. Apply `past_k_dist`: `Hφ → H(¬¬φ)`
4. Apply `future_k_dist`: `Gφ → G(¬¬φ)`
5. Recombine: `H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ) = △(¬¬φ)`

---

## Implementation Recommendations

### Phase 1: Fix Derivable.height (CRITICAL)

**Priority**: HIGH - Blocks all other work  
**Effort**: 4-6 hours  
**Risk**: Medium (well-founded recursion can be tricky)

**Steps:**
1. Move `Derivable.height` definition to `Derivation.lean` (after `Derivable` inductive)
2. Prove 7 height properties as theorems (use `rfl`, `omega`)
3. Update `DeductionTheorem.lean` with `termination_by h.height`
4. Add `decreasing_by` clauses for 3 sorry cases
5. Delete axiom declarations (lines 168-222)
6. Test: `lake build Logos.Core.Metalogic.DeductionTheorem`

**Fallback**: If blocked, consult Lean Zulip or keep axioms with documentation

### Phase 2: Derive future_k_dist

**Priority**: MEDIUM - Depends on Phase 1  
**Effort**: 2-3 hours  
**Risk**: Low (straightforward deduction theorem application)

**Steps:**
1. Implement `future_k_dist` theorem in `Bridge.lean`
2. Use deduction theorem twice (pattern from modal K)
3. Derive `past_k_dist` via temporal duality
4. Remove axiom declarations
5. Test: `lake build Logos.Core.Theorems.Perpetuity.Bridge`

### Phase 3: Break Circular Dependency

**Priority**: MEDIUM - Needed for Phase 4  
**Effort**: 3-4 hours  
**Risk**: Low (architectural refactoring)

**Steps:**
1. Create `Logos/Core/Theorems/Propositional/Basics.lean`
2. Extract `lce_imp`, `rce_imp` from `Propositional.lean`
3. Update imports in `DeductionTheorem.lean` and `Bridge.lean`
4. Update `Propositional.lean` to import Basics
5. Test: `lake build`

### Phase 4: Derive always_dni and always_dne

**Priority**: MEDIUM - Depends on Phases 2 & 3  
**Effort**: 2-3 hours  
**Risk**: Low (decomposition lemmas already implemented)

**Steps:**
1. Implement `always_dni` using decomposition + K distributions
2. Implement `always_dne` using decomposition + K distributions
3. Remove axiom declarations
4. Test: `lake build Logos.Core.Theorems.Perpetuity.Bridge`
5. Update IMPLEMENTATION_STATUS.md (axiom count reduced by 2)

---

## Testing Strategy

### After Each Phase

```bash
# Build specific module
lake build Logos.Core.Metalogic.DeductionTheorem  # Phase 1
lake build Logos.Core.Theorems.Perpetuity.Bridge  # Phases 2, 4

# Full build
lake build

# Run tests
lake test

# Check for sorry markers
grep -c "sorry" Logos/Core/Metalogic/DeductionTheorem.lean  # Expected: 0 after Phase 1
grep -c "axiom" Logos/Core/Theorems/Perpetuity/Bridge.lean  # Expected: 2 fewer after Phase 2, 2 more fewer after Phase 4
```

### Success Criteria

- [ ] Zero `sorry` markers in `DeductionTheorem.lean`
- [ ] Zero axiom declarations for `Derivable.height` properties
- [ ] `future_k_dist` and `past_k_dist` derived as theorems
- [ ] `always_dni` and `always_dne` derived as theorems
- [ ] No circular dependencies in import graph
- [ ] All tests pass (`lake test`)
- [ ] Zero build errors (`lake build`)
- [ ] Documentation updated (IMPLEMENTATION_STATUS.md, SORRY_REGISTRY.md)

---

## Risk Assessment

### High Risk

- **Phase 1 (Derivable.height)**: Well-founded recursion is complex
  - **Mitigation**: Study Mathlib patterns, consult Lean Zulip
  - **Fallback**: Keep axioms with documented blockers in SORRY_REGISTRY.md

### Medium Risk

- **Phase 2 (Temporal Axioms)**: Depends on Phase 1 completion
  - **Mitigation**: Complete Phase 1 first, use modal K pattern
  - **Fallback**: Keep `future_k_dist` as axiom

- **Phase 3 (Circular Dependency)**: Requires architectural refactoring
  - **Mitigation**: Test compilation after each import change
  - **Fallback**: Keep current structure, document limitation

### Low Risk

- **Phase 4 (Double Negation)**: Decomposition lemmas already implemented
  - **Mitigation**: Use existing patterns from perpetuity proofs
  - **Fallback**: Keep `always_dni`/`always_dne` as axioms

---

## Resources

### LEAN 4 Documentation

- [Well-Founded Recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction)
- [Termination](https://lean-lang.org/functional_programming_in_lean/programs-proofs/tail-recursion.html)
- [Structural Recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html)

### Mathlib Examples

- `Mathlib/Data/List/Basic.lean` - List.length, structural recursion
- `Mathlib/Data/Nat/Basic.lean` - Nat operations, well-founded recursion
- `Mathlib/Data/List/Perm.lean` - Permutation lemmas

### Academic References

- Goldblatt, R. (1992). *Logics of Time and Computation*
- van Benthem, J. (1983). *The Logic of Time*
- Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*

### Project Documentation

- [TODO.md](../../../TODO.md) - Task 42b description
- [Plan 065](../../065_proof_automation_temporal_deduction/plans/001-proof-automation-completion-plan.md) - Original plan
- [IMPLEMENTATION_STATUS.md](../../../Documentation/ProjectInfo/IMPLEMENTATION_STATUS.md) - Module status
- [SORRY_REGISTRY.md](../../../Documentation/ProjectInfo/SORRY_REGISTRY.md) - Technical debt tracking

---

## Next Steps

1. **Review Research**: Read both documents in this directory
2. **Assess Blockers**: Determine if well-founded recursion expertise is available
3. **Plan Execution**: Decide whether to tackle Phase 1 or defer to expert
4. **Create Feature Branch**: `git checkout -b task-42b-temporal-k-infrastructure`
5. **Begin Implementation**: Start with Phase 1 (Derivable.height fix)

---

**Last Updated**: 2025-12-15  
**Research Status**: Complete  
**Implementation Status**: Not Started  
**Next Action**: Review research documents and assess Phase 1 feasibility
