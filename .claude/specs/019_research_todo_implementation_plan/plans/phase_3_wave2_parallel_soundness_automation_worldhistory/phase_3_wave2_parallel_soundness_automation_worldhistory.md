# Phase 3: Wave 2 Parallel - Soundness, Automation, WorldHistory [IN PROGRESS]

## Metadata
- **Date**: 2025-12-02 (Revised: 2025-12-02 after axiom alignment fix)
- **Parent Plan**: TODO Implementation Systematic Plan
- **Phase Number**: 3
- **Dependencies**: Phase 1 (Wave 1 - High Priority Foundations)
- **Estimated Hours**: 35-52 hours sequential, ~25-38 hours parallel (reduced after axiom fix)
- **Complexity**: Medium (reduced from High after axiom alignment)
- **Status**: [IN PROGRESS]
- **Sub-Phases**: 3 (parallel execution)

## Axiom Alignment Fix (COMPLETED)

### Issue Identified
The JPL paper and ProofChecker originally used DIFFERENT definitions:

| Term | Paper Definition | OLD ProofChecker |
|------|------------------|------------------|
| `always φ` | `Past φ ∧ φ ∧ Future φ` | `Future φ` |
| TL Axiom | `△φ → F(Pφ)` | `Fφ → F(Pφ)` |

### Fix Applied (2025-12-02)
Updated ProofChecker to match paper:

| Component | File | Change |
|-----------|------|--------|
| `always` definition | Formula.lean | `φ.future` → `φ.past.and (φ.and φ.future)` |
| `sometimes` docs | Formula.lean | Updated to explain dual |
| TL axiom | Axioms.lean | `(Future φ).imp ...` → `φ.always.imp ...` |
| TL validity docs | Soundness.lean | Updated with paper proof reference |

### Current State
- ✅ All axioms now match paper definitions
- ✅ TL axiom is now trivially valid (paper proof applies directly)
- ✅ MF and TF can be proven via time-shift invariance (paper method)
- ✅ Build succeeds

---

## Overview

Phase 3 executes Tasks 5, 7, and 8 from the TODO Implementation Plan in parallel.

**Objective**: Complete soundness proofs for all axioms (now possible after alignment), implement automation tactics (Task 7), and fix WorldHistory (Task 8).

**Parallel Execution Strategy**:
- Sub-Phase 3A (Task 5): Soundness proofs - 6-10 hours (reduced after axiom fix)
- Sub-Phase 3B (Task 7): Automation tactics - 29-42 hours (phased)
- Sub-Phase 3C (Task 8): WorldHistory universal helper - 1-2 hours

---

## Sub-Phase 3A: Complete Soundness Proofs (Task 5) [IN PROGRESS]

### Objective
Complete validity proofs for TL, MF, TF axioms using paper's methods.

### Complexity
Medium (reduced from High - paper proofs now apply directly)

### Estimated Hours
6-10 hours (reduced from 10-14 after axiom alignment fix)

### Status After Axiom Fix

| Axiom | Status | Approach |
|-------|--------|----------|
| TL | Conceptually proven | Needs conjunction truth lemma |
| MF | Needs time-shift | Paper proof via time-shift invariance |
| TF | Needs time-shift | Paper proof via time-shift invariance |

### Tasks

#### Task 3A.1: Complete TL Axiom Proof
**File**: `ProofChecker/Metalogic/Soundness.lean`
**Status**: IN PROGRESS

**Paper Proof (line 2334)**:
> Suppose M,τ,x ⊨ always φ. Then M,τ,y ⊨ φ for all y ∈ T.
> To show M,τ,x ⊨ Future Past φ, consider any z > x.
> We must show M,τ,z ⊨ Past φ, i.e., M,τ,w ⊨ φ for all w < z.
> But this holds by our assumption that φ holds at all times in τ.

**Implementation Challenge**:
The proof is conceptually trivial, but technically requires:
1. A lemma for truth of conjunction: `truth_at M τ t ht (φ.and ψ) ↔ truth_at ... φ ∧ truth_at ... ψ`
2. This is complicated by `and` being encoded as `¬(φ → ¬ψ)`

**Time Estimate**: 2-3 hours

---

#### Task 3A.2: Implement Time-Shift Infrastructure
**File**: `ProofChecker/Semantics/WorldHistory.lean`

**Objective**: Add time-shift history construction (required for MF/TF proofs)

```lean
/-- Time-shifted history construction.
Given history τ and times x, y, construct σ where σ(z) = τ(z - x + y).
This corresponds to "viewing τ from time y instead of time x".
-/
def time_shift (τ : WorldHistory F) (x y : Int) : WorldHistory F where
  domain := fun z => τ.domain (z - x + y)
  states := fun z hz => τ.states (z - x + y) hz
  convex := sorry -- Convexity preserved under linear shift
  respects_task := sorry -- Task relation preserved under shift
```

**Time Estimate**: 1-2 hours

---

#### Task 3A.3: Implement Time-Shift Preservation Lemma
**File**: `ProofChecker/Semantics/Truth.lean`

**Objective**: Prove truth preserved under time-shift (paper's lem:history-time-shift-preservation)

```lean
theorem time_shift_preservation (M : TaskModel F) (τ : WorldHistory F) (x y : Int)
    (hy : τ.domain y) (φ : Formula) :
    truth_at M τ y hy φ ↔ truth_at M (time_shift τ x y) x _ φ := by
  induction φ <;> sorry -- Induction on formula structure
```

**Time Estimate**: 2-3 hours

---

#### Task 3A.4: Complete MF and TF Axiom Proofs
**File**: `ProofChecker/Metalogic/Soundness.lean`

**Objective**: Prove MF and TF using time-shift invariance

**MF Proof Strategy (paper line 2352)**:
- Premise: □φ at time x (φ at all histories at x)
- For any σ and y > x, need φ at (σ, y)
- Use time-shift preservation

**TF Proof Strategy (paper lines 2354-2356)**:
- Premise: □φ at time x
- For any y > x, need □φ at y
- Use time-shift: for any σ at y, ∃ρ at x with preservation

**Time Estimate**: 2-3 hours

---

### Sub-Phase 3A Summary

**Total Tasks**: 4
**Estimated Time**: 6-10 hours
**Approach**:
- TL: Complete proof using conjunction handling (conceptually trivial after axiom fix)
- MF and TF: Implement time-shift infrastructure and proofs
- All proofs follow paper's methods directly

---

## Sub-Phase 3B: Implement Core Automation (Task 7) [NOT STARTED]

### Objective
Implement core automation tactics in phased approach.

### Estimated Hours
29-42 hours (3 phases)

### Phases
- Phase 1: apply_axiom, modal_t (10-13 hours)
- Phase 2: tm_auto with Aesop (12-15 hours)
- Phase 3: assumption_search and helpers (7-14 hours)

See stage files for detailed implementation plans:
- stage_1_apply_axiom_modal_t.md
- stage_2_tm_auto_aesop.md
- stage_3_assumption_search_helpers.md

---

## Sub-Phase 3C: WorldHistory Fix (Task 8) [NOT STARTED]

### Objective
Fix WorldHistory universal helper (1 sorry)

### Estimated Hours
1-2 hours

### Task
The universal helper requires reflexive frame property. Document as conditional
or implement if simple.

---

## Success Criteria

- [x] Axiom definitions aligned with paper (Formula.lean, Axioms.lean)
- [x] TL axiom documentation updated (Soundness.lean)
- [x] MF/TF axiom documentation updated with paper proof references
- [x] lake build succeeds
- [ ] TL axiom proof completed (conjunction handling)
- [ ] Time-shift infrastructure implemented in WorldHistory.lean
- [ ] Time-shift preservation lemma proven in Truth.lean
- [ ] MF axiom soundness proven using time-shift
- [ ] TF axiom soundness proven using time-shift
- [ ] Sub-Phase 3B automation phases executed (or deferred)
- [ ] Sub-Phase 3C WorldHistory fixed or documented
