# Task 48 Problem Diagram

## Current Broken State

```
┌─────────────────────────────────────────────────────────────┐
│ Logos/Core/ProofSystem/Derivation.lean                      │
│                                                              │
│  inductive Derivable : Context → Formula → Prop where       │
│    | axiom ...                                              │
│    | assumption ...                                         │
│    | modus_ponens ...                                       │
│    | necessitation ...                                      │
│    | temporal_necessitation ...                             │
│    | temporal_duality ...                                   │
│    | weakening ...                                          │
│                                                              │
│  [NO height function here - this is the problem!]           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
                            ↓ imports
┌─────────────────────────────────────────────────────────────┐
│ Logos/Core/Metalogic/DeductionTheorem.lean                  │
│                                                              │
│  ❌ axiom Derivable.height : Derivable Γ φ → Nat            │
│  ❌ axiom Derivable.weakening_height_succ ...                │
│  ❌ axiom Derivable.subderiv_height_lt ...                   │
│  ❌ axiom Derivable.mp_height_gt_left ...                    │
│  ❌ axiom Derivable.mp_height_gt_right ...                   │
│                                                              │
│  ERROR: Cannot add 'height' to Derivable from different     │
│         module! Lean 4 module system forbids this.          │
│                                                              │
│  theorem deduction_theorem ... := by                        │
│    ...                                                       │
│    termination_by h.height  ← FAILS: height doesn't exist   │
│                                                              │
└─────────────────────────────────────────────────────────────┘
                            ↓ blocks
┌─────────────────────────────────────────────────────────────┐
│ Task 42a: Derive future_k_dist                              │
│ Task 42b: Derive always_mono, always_dni, always_dne        │
│                                                              │
│ ⏸️  BLOCKED - Cannot proceed without deduction theorem       │
└─────────────────────────────────────────────────────────────┘
```

---

## Fixed State (After Implementation)

```
┌─────────────────────────────────────────────────────────────┐
│ Logos/Core/ProofSystem/Derivation.lean                      │
│                                                              │
│  inductive Derivable : Context → Formula → Prop where       │
│    | axiom ...                                              │
│    | assumption ...                                         │
│    | modus_ponens ...                                       │
│    | necessitation ...                                      │
│    | temporal_necessitation ...                             │
│    | temporal_duality ...                                   │
│    | weakening ...                                          │
│                                                              │
│  ✅ def Derivable.height : Derivable Γ φ → Nat              │
│    | _, _, axiom _ _ _ => 0                                 │
│    | _, _, assumption _ _ _ => 0                            │
│    | _, _, modus_ponens _ _ _ d1 d2 => max d1.height        │
│                                        d2.height + 1         │
│    | _, _, necessitation _ d => d.height + 1                │
│    | _, _, temporal_necessitation _ d => d.height + 1       │
│    | _, _, temporal_duality _ d => d.height + 1             │
│    | _, _, weakening _ _ _ d _ => d.height + 1              │
│                                                              │
│  ✅ theorem Derivable.weakening_height_succ ... := rfl       │
│  ✅ theorem Derivable.subderiv_height_lt ... := by omega     │
│  ✅ theorem Derivable.mp_height_gt_left ... := by omega      │
│  ✅ theorem Derivable.mp_height_gt_right ... := by omega     │
│                                                              │
│  SUCCESS: height is in same module as Derivable!            │
│                                                              │
└─────────────────────────────────────────────────────────────┘
                            ↓ imports
┌─────────────────────────────────────────────────────────────┐
│ Logos/Core/Metalogic/DeductionTheorem.lean                  │
│                                                              │
│  [Axiomatized height section REMOVED]                       │
│                                                              │
│  ✅ theorem deduction_theorem ... := by                      │
│    ...                                                       │
│    termination_by h.height  ← WORKS: height imported!       │
│    decreasing_by                                            │
│      all_goals simp_wf                                      │
│      · exact Derivable.mp_height_gt_left h1 h2              │
│      · exact Derivable.mp_height_gt_right h1 h2             │
│      · exact Derivable.subderiv_height_lt h1 h2             │
│      · exact Derivable.subderiv_height_lt h1 h2             │
│                                                              │
│  SUCCESS: File compiles for the first time!                 │
│                                                              │
└─────────────────────────────────────────────────────────────┘
                            ↓ unblocks
┌─────────────────────────────────────────────────────────────┐
│ Task 42a: Derive future_k_dist                              │
│ Task 42b: Derive always_mono, always_dni, always_dne        │
│                                                              │
│ ✅ READY - Can now proceed with deduction theorem!           │
└─────────────────────────────────────────────────────────────┘
```

---

## Why This Works: Lean 4 Module System

```
┌─────────────────────────────────────────────────────────────┐
│ Lean 4 Module System Rules                                  │
│                                                              │
│ Rule 1: Inductive types must be defined in ONE module       │
│ Rule 2: Methods can ONLY be added in the SAME module        │
│ Rule 3: Cross-module extension is FORBIDDEN                 │
│                                                              │
│ Why? Performance + Modularity + Type Safety                 │
│                                                              │
│ ✅ ALLOWED:                                                  │
│   Module A:                                                 │
│     inductive Foo where ...                                 │
│     def Foo.bar : Foo → Nat := ...  ← Same module!          │
│                                                              │
│ ❌ FORBIDDEN:                                                │
│   Module A:                                                 │
│     inductive Foo where ...                                 │
│   Module B:                                                 │
│     def Foo.bar : Foo → Nat := ...  ← Different module!     │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Dependency Graph

### Before Fix (Broken)

```
Derivation.lean (defines Derivable)
    ↓
DeductionTheorem.lean (tries to add height) ❌ FAILS
    ↓
Bridge.lean (needs deduction theorem) ⏸️ BLOCKED
    ↓
Task 42a (needs Bridge.lean) ⏸️ BLOCKED
    ↓
Task 42b (needs Task 42a) ⏸️ BLOCKED
```

### After Fix (Working)

```
Derivation.lean (defines Derivable + height) ✅
    ↓
DeductionTheorem.lean (uses height) ✅
    ↓
Bridge.lean (uses deduction theorem) ✅
    ↓
Task 42a (uses Bridge.lean) ✅ READY
    ↓
Task 42b (uses Task 42a) ⏸️ BLOCKED (by 42a, not by 48)
```

---

## Code Movement Visualization

### What Moves FROM DeductionTheorem.lean

```lean
❌ DELETE THIS SECTION (lines 33-88):

/-! ## Derivation Height Measure (Axiomatized) -/

open Logos.Core.Syntax
open Logos.Core.ProofSystem

axiom Derivable.height {Γ : Context} {φ : Formula} (d : Derivable Γ φ) : Nat

/-! ## Height Properties (Axiomatized) -/

axiom Derivable.weakening_height_succ {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    (Derivable.weakening Γ' Δ φ d h).height = d.height + 1

axiom Derivable.subderiv_height_lt {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    d.height < (Derivable.weakening Γ' Δ φ d h).height

axiom Derivable.mp_height_gt_left {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d1.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height

axiom Derivable.mp_height_gt_right {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d2.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height
```

### What Moves TO Derivation.lean

```lean
✅ ADD THIS SECTION (after line 138):

/-! ## Derivation Height Measure -/

def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, axiom _ _ _ => 0
  | _, _, assumption _ _ _ => 0
  | _, _, modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, necessitation _ d => d.height + 1
  | _, _, temporal_necessitation _ d => d.height + 1
  | _, _, temporal_duality _ d => d.height + 1
  | _, _, weakening _ _ _ d _ => d.height + 1

/-! ## Height Properties -/

theorem Derivable.weakening_height_succ {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    (Derivable.weakening Γ' Δ φ d h).height = d.height + 1 := by
  rfl

theorem Derivable.subderiv_height_lt {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    d.height < (Derivable.weakening Γ' Δ φ d h).height := by
  rw [weakening_height_succ]
  omega

theorem Derivable.mp_height_gt_left {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d1.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

theorem Derivable.mp_height_gt_right {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d2.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

[+ 3 more height theorems for necessitation rules]
```

---

## Impact Analysis

### Files Changed: 2

1. **Derivation.lean**: +80 lines (200 → 280 lines)
2. **DeductionTheorem.lean**: -55 lines (395 → 340 lines)

### Net Change: +25 lines total

### Compilation Status

| File | Before | After |
|------|--------|-------|
| Derivation.lean | ✅ Compiles | ✅ Compiles |
| DeductionTheorem.lean | ❌ FAILS | ✅ Compiles |
| Bridge.lean | ⏸️ Blocked | ✅ Ready |

### Task Status

| Task | Before | After |
|------|--------|-------|
| Task 48 | ⏸️ BLOCKED | ✅ COMPLETE |
| Task 42a | ⏸️ BLOCKED | ✅ READY |
| Task 42b | ⏸️ BLOCKED | ⏸️ BLOCKED (by 42a) |

---

## Key Takeaways

1. **Root Cause**: Lean 4 module system restriction (cross-module extension forbidden)
2. **Solution**: Move function to same module as type definition
3. **Complexity**: Low (just moving code, not rewriting)
4. **Risk**: Very Low (compiler catches all errors)
5. **Time**: 2-2.5 hours
6. **Impact**: Unblocks critical path for Layer 0 completion

---

**Diagram Created**: 2025-12-15  
**Purpose**: Visual understanding of problem and solution
