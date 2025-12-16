# Task 48 Implementation Guide - Quick Reference

**Goal**: Fix `Derivable.height` compilation blocker by moving it to `Derivation.lean`

**Time Estimate**: 2-2.5 hours

---

## Quick Start

```bash
# 1. Backup current state
git checkout -b fix/task-48-derivable-height

# 2. Edit Derivation.lean (add height function)
# 3. Edit DeductionTheorem.lean (remove axioms)
# 4. Build and test
lake clean && lake build

# 5. Commit if successful
git add -A
git commit -m "Fix Task 48: Move Derivable.height to Derivation.lean

- Move height function from DeductionTheorem.lean to Derivation.lean
- Move height property theorems to Derivation.lean
- Remove axiomatized height from DeductionTheorem.lean
- Fixes compilation blocker (GitHub Issue #1)
- Unblocks Task 42a (Phase 2 - Temporal Axiom Derivation)"
```

---

## Step-by-Step Instructions

### Step 1: Edit Derivation.lean (45 minutes)

**File**: `Logos/Core/ProofSystem/Derivation.lean`

**Location**: After line 138 (after `Derivable` definition, before examples section)

**Action**: Insert the following code:

<details>
<summary>Click to expand code to insert</summary>

```lean
/-! ## Derivation Height Measure -/

/--
Height of a derivation tree.

The height is defined as the maximum depth of the derivation tree:
- Base cases (axiom, assumption): height 0
- Unary rules (necessitation, temporal_necessitation, temporal_duality, weakening):
  height of subderivation + 1
- Binary rules (modus_ponens): max of both subderivations + 1

This measure is used for well-founded recursion in the deduction theorem proof.
-/
def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, axiom _ _ _ => 0
  | _, _, assumption _ _ _ => 0
  | _, _, modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, necessitation _ d => d.height + 1
  | _, _, temporal_necessitation _ d => d.height + 1
  | _, _, temporal_duality _ d => d.height + 1
  | _, _, weakening _ _ _ d _ => d.height + 1

/-! ## Height Properties -/

/--
Weakening increases height by exactly 1.
-/
theorem Derivable.weakening_height_succ {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    (Derivable.weakening Γ' Δ φ d h).height = d.height + 1 := by
  rfl

/--
Subderivations in weakening have strictly smaller height.
-/
theorem Derivable.subderiv_height_lt {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    d.height < (Derivable.weakening Γ' Δ φ d h).height := by
  rw [weakening_height_succ]
  omega

/--
Modus ponens height is strictly greater than the left subderivation.
-/
theorem Derivable.mp_height_gt_left {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d1.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

/--
Modus ponens height is strictly greater than the right subderivation.
-/
theorem Derivable.mp_height_gt_right {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d2.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

/--
Necessitation increases height by exactly 1.
-/
theorem Derivable.necessitation_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.necessitation φ d).height = d.height + 1 := by
  rfl

/--
Temporal necessitation increases height by exactly 1.
-/
theorem Derivable.temporal_necessitation_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.temporal_necessitation φ d).height = d.height + 1 := by
  rfl

/--
Temporal duality increases height by exactly 1.
-/
theorem Derivable.temporal_duality_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.temporal_duality φ d).height = d.height + 1 := by
  rfl

```

</details>

**Test**:
```bash
lake build Logos.Core.ProofSystem.Derivation
# Should succeed
```

---

### Step 2: Edit DeductionTheorem.lean (15 minutes)

**File**: `Logos/Core/Metalogic/DeductionTheorem.lean`

**Action**: Delete lines 33-88 (entire axiomatized section)

**What to delete**:
- Line 33: `/-! ## Derivation Height Measure (Axiomatized) -/`
- Lines 35-37: `open` statements
- Line 55: `axiom Derivable.height ...`
- Line 57: `/-! ## Height Properties (Axiomatized) -/`
- Lines 64-88: All axiomatized height property theorems

**What to keep**:
- Line 90: `namespace Logos.Core.Metalogic` (keep this!)
- Everything after line 90 (all the helper lemmas and deduction theorem)

**Result**: File should be ~307 lines instead of 395 lines.

**Test**:
```bash
lake build Logos.Core.Metalogic.DeductionTheorem
# Should succeed for the first time!
```

---

### Step 3: Full Build and Test (15 minutes)

```bash
# Clean build
lake clean

# Full build
lake build

# Run tests
lake test

# Verify no sorry
rg "sorry" Logos/Core/Metalogic/DeductionTheorem.lean
# Expected: 0 matches

# Check dependent files
lake build Logos.Core.Theorems.Perpetuity.Bridge
# Should succeed
```

---

### Step 4: Update Documentation (15 minutes)

**File 1: TODO.md**

Find Task 48 section and update:

```markdown
### 48. Fix Derivable.height Compilation Blocker
**Effort**: 2-4 hours
**Status**: ✅ COMPLETE (2025-12-15)
**Priority**: High (blocks Task 42a)
**Blocking**: Task 42a (Phase 2), Task 42b (Phase 3)
**Dependencies**: None
**GitHub Issue**: https://github.com/benbrastmckie/ProofChecker/issues/1

**Solution**: Moved `Derivable.height` function and properties from 
`DeductionTheorem.lean` to `Derivation.lean` where `Derivable` is defined.
This resolves Lean 4's cross-module extension restriction.

**Files Modified**:
- `Logos/Core/ProofSystem/Derivation.lean` - Added height function and properties
- `Logos/Core/Metalogic/DeductionTheorem.lean` - Removed axiomatized height

**Outcome**: DeductionTheorem.lean now compiles successfully. Task 42a unblocked.
```

Update Task 42a status:
```markdown
### 42a. Proof Automation Phase 2 - Temporal Axiom Derivation (Plan 065)
**Effort**: 4-6 hours
**Status**: READY (unblocked by Task 48 completion)
**Priority**: High (critical path for axiom reduction)
```

Update "Last Updated" at bottom:
```markdown
**Last Updated**: 2025-12-15 (Task 48 complete - Derivable.height fixed, Task 42a unblocked)
```

**File 2: IMPLEMENTATION_STATUS.md**

Update DeductionTheorem status (find the relevant section):
```markdown
- `DeductionTheorem.lean`: ✅ Complete (zero sorry, height function moved to Derivation.lean)
```

Update Derivation status:
```markdown
- `Derivation.lean`: ✅ Complete (includes height measure for well-founded recursion)
```

**File 3: GitHub Issue #1**

Add comment:
```markdown
## Solution Implemented

**Root Cause**: Lean 4 does not allow adding methods to an inductive type from a different module than where it was defined.

**Solution**: Moved `Derivable.height` function and all height property theorems from `DeductionTheorem.lean` to `Derivation.lean` (where `Derivable` is defined).

**Changes**:
- Added ~80 lines to `Derivation.lean` (height function + 7 property theorems)
- Removed ~55 lines from `DeductionTheorem.lean` (axiomatized height section)

**Result**: 
- ✅ DeductionTheorem.lean compiles successfully (first time ever)
- ✅ All height properties proven (no axioms)
- ✅ Task 42a unblocked
- ✅ Zero sorry in both files

**Commit**: [link to commit hash]

Closing as resolved.
```

Then close the issue.

---

## Verification Checklist

After implementation, verify:

- [ ] `lake build` succeeds with no errors
- [ ] `lake test` passes all tests
- [ ] `rg "sorry" Logos/Core/Metalogic/DeductionTheorem.lean` returns 0 matches
- [ ] `rg "axiom.*height" Logos/Core/Metalogic/DeductionTheorem.lean` returns 0 matches
- [ ] `lake build Logos.Core.Theorems.Perpetuity.Bridge` succeeds
- [ ] TODO.md updated (Task 48 complete, Task 42a unblocked)
- [ ] IMPLEMENTATION_STATUS.md updated
- [ ] GitHub Issue #1 closed with solution summary
- [ ] Git commit created with descriptive message

---

## Troubleshooting

### Error: "omega tactic failed"

**Cause**: `omega` tactic not available (needs Mathlib)

**Fix**: Change `omega` to `simp_arith` or explicit proof:
```lean
theorem Derivable.subderiv_height_lt ... := by
  rw [weakening_height_succ]
  simp_arith  -- or: exact Nat.lt_succ_self _
```

### Error: "unknown identifier 'max'"

**Cause**: `max` not in scope

**Fix**: Add `open Nat` at top of section or use `Nat.max`:
```lean
def Derivable.height : ... → Nat
  | _, _, modus_ponens _ _ _ d1 d2 => Nat.max d1.height d2.height + 1
```

### Error: "termination_by failed"

**Cause**: Height properties not accessible

**Fix**: Verify height properties are defined **before** the examples section in Derivation.lean.

---

## Rollback Plan

If something goes wrong:

```bash
# Discard all changes
git checkout Logos/Core/ProofSystem/Derivation.lean
git checkout Logos/Core/Metalogic/DeductionTheorem.lean

# Or reset branch
git reset --hard origin/main
```

---

## Success Criteria

✅ **Compilation**: `lake build` succeeds  
✅ **No Axioms**: Zero `axiom` declarations for height  
✅ **No Sorry**: Zero `sorry` in DeductionTheorem.lean  
✅ **Tests Pass**: `lake test` succeeds  
✅ **Task 42a Unblocked**: Can proceed with Phase 2  

---

## Next Steps After Completion

1. **Proceed to Task 42a**: Derive `future_k_dist` and `always_mono` theorems
2. **Update Project Board**: Mark Task 48 complete
3. **Announce**: Let team know blocker is resolved
4. **Continue**: Resume work on proof automation completion

---

**Quick Reference Created**: 2025-12-15  
**Estimated Time**: 2-2.5 hours  
**Difficulty**: Low (straightforward refactoring)  
**Risk**: Very Low (compiler will catch any errors)
