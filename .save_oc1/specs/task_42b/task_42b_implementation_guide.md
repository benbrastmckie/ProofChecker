# Implementation Guide: Task 42b - Temporal K Infrastructure

**Quick Reference for Implementing Proof Automation Phase 3**

---

## Critical Path

```
1. Fix Derivable.height (4-6 hours)
   ↓
2. Derive future_k_dist (2-3 hours)
   ↓
3. Break circular dependency (3-4 hours)
   ↓
4. Derive always_dni/always_dne (2-3 hours)
```

**Total Estimated Time**: 11-16 hours

---

## Step 1: Fix `Derivable.height` (BLOCKER)

### Current Problem
- `Derivable.height` is **axiomatized** (lines 168-222 in `Derivation.lean`)
- Deduction theorem has **3 sorry markers** that need termination proofs
- File: `Logos/Core/Metalogic/DeductionTheorem.lean`

### Solution
Move `Derivable.height` definition to `Derivation.lean`:

```lean
-- In Logos/Core/ProofSystem/Derivation.lean (after Derivable definition)

def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, .axiom _ _ _ => 0
  | _, _, .assumption _ _ _ => 0
  | _, _, .modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, .necessitation _ d => d.height + 1
  | _, _, .temporal_necessitation _ d => d.height + 1
  | _, _, .temporal_duality _ d => d.height + 1
  | _, _, .weakening _ _ _ d _ => d.height + 1
```

### Prove Height Properties

```lean
theorem Derivable.weakening_height_succ {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    (Derivable.weakening Γ' Δ φ d h).height = d.height + 1 := by
  rfl

theorem Derivable.subderiv_height_lt {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    d.height < (Derivable.weakening Γ' Δ φ d h).height := by
  simp [height]; omega

theorem Derivable.mp_height_gt_left {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d1.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]; omega

theorem Derivable.mp_height_gt_right {Γ : Context} {φ ψ : Formula}
    (d1 : Derivable Γ (φ.imp ψ)) (d2 : Derivable Γ φ) :
    d2.height < (Derivable.modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]; omega
```

### Update Deduction Theorem

```lean
-- In Logos/Core/Metalogic/DeductionTheorem.lean

theorem deduction_theorem (Γ : Context) (A B : Formula)
    (h : (A :: Γ) ⊢ B) : Γ ⊢ A.imp B := by
  match h with
  | Derivable.axiom _ φ h_ax => exact deduction_axiom Γ A φ h_ax
  | Derivable.assumption _ φ h_mem => -- ... (existing code)
  | Derivable.modus_ponens _ φ ψ h1 h2 =>
      have ih1 : Γ ⊢ A.imp (φ.imp ψ) := deduction_theorem Γ A (φ.imp ψ) h1
      have ih2 : Γ ⊢ A.imp φ := deduction_theorem Γ A φ h2
      exact deduction_mp Γ A φ ψ ih1 ih2
  | Derivable.weakening Γ' _ φ h1 h2 => -- ... (existing code)
termination_by h.height
decreasing_by
  all_goals simp_wf
  · exact Derivable.mp_height_gt_left h1 h2
  · exact Derivable.mp_height_gt_right h1 h2
  · exact Derivable.subderiv_height_lt h1 h2
```

### Delete Axioms

Remove lines 168-222 from `Derivation.lean` (all `axiom Derivable.*` declarations).

### Test

```bash
lake build Logos.Core.Metalogic.DeductionTheorem
grep -c "sorry" Logos/Core/Metalogic/DeductionTheorem.lean  # Expected: 0
lake test
```

---

## Step 2: Derive `future_k_dist`

### Goal
Derive `⊢ G(φ → ψ) → (Gφ → Gψ)` from deduction theorem

### Implementation

```lean
-- In Logos/Core/Theorems/Perpetuity/Bridge.lean

theorem future_k_dist (φ ψ : Formula) : 
    ⊢ (φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future) := by
  -- Step 1: [φ → ψ, φ] ⊢ ψ
  have h1 : [φ.imp ψ, φ] ⊢ ψ := by
    apply Derivable.modus_ponens [φ.imp ψ, φ] φ ψ
    · apply Derivable.assumption; simp
    · apply Derivable.assumption; simp
  
  -- Step 2: [G(φ → ψ), Gφ] ⊢ Gψ (by temporal_k rule)
  have h2 : [(φ.imp ψ).all_future, φ.all_future] ⊢ ψ.all_future := by
    apply Derivable.temporal_k [φ.imp ψ, φ] ψ h1
  
  -- Step 3: [G(φ → ψ)] ⊢ Gφ → Gψ
  have h3 : [(φ.imp ψ).all_future] ⊢ φ.all_future.imp ψ.all_future := by
    exact deduction_theorem [(φ.imp ψ).all_future] φ.all_future ψ.all_future h2
  
  -- Step 4: ⊢ G(φ → ψ) → (Gφ → Gψ)
  exact deduction_theorem [] (φ.imp ψ).all_future (φ.all_future.imp ψ.all_future) h3
```

### Derive `past_k_dist`

```lean
theorem past_k_dist (φ ψ : Formula) : 
    ⊢ (φ.imp ψ).all_past.imp (φ.all_past.imp ψ.all_past) := by
  have h_future : ⊢ (φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future) :=
    future_k_dist φ ψ
  have h_swap : ⊢ ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)).swap_past_future := by
    apply Derivable.temporal_duality
    exact h_future
  simp only [Formula.swap_past_future] at h_swap
  exact h_swap
```

### Remove Axioms

Delete `axiom future_k_dist` and `axiom past_k_dist` from `Bridge.lean`.

### Test

```bash
lake build Logos.Core.Theorems.Perpetuity.Bridge
grep -c "axiom.*k_dist" Logos/Core/Theorems/Perpetuity/Bridge.lean  # Expected: 0
```

---

## Step 3: Break Circular Dependency

### Current Cycle

```
Bridge.lean → DeductionTheorem.lean → Propositional.lean → Bridge.lean
```

### Solution: Extract Basics

Create `Logos/Core/Theorems/Propositional/Basics.lean`:

```lean
import Logos.Core.ProofSystem.Derivation
import Logos.Core.Syntax.Formula
import Logos.Core.Theorems.Combinators

namespace Logos.Core.Theorems.Propositional.Basics

open Logos.Core.Syntax
open Logos.Core.ProofSystem
open Logos.Core.Theorems.Combinators

-- TODO: Prove lce_imp and rce_imp using pure combinators (no deduction theorem)
theorem lce_imp (A B : Formula) : ⊢ (A.and B).imp A := by
  sorry  -- Complex combinator proof

theorem rce_imp (A B : Formula) : ⊢ (A.and B).imp B := by
  sorry  -- Complex combinator proof

end Logos.Core.Theorems.Propositional.Basics
```

### Update Imports

**In `Bridge.lean`**:
```lean
import Logos.Core.Theorems.Propositional.Basics  -- NEW
-- Remove: import Logos.Core.Metalogic.DeductionTheorem (if not needed)
```

**In `Propositional.lean`**:
```lean
import Logos.Core.Theorems.Propositional.Basics
import Logos.Core.Metalogic.DeductionTheorem

-- Remove lce_imp and rce_imp definitions
-- Add re-exports:
export Logos.Core.Theorems.Propositional.Basics (lce_imp rce_imp)
```

### Test

```bash
lake build --verbose 2>&1 | grep "circular"  # Expected: no output
lake build
```

---

## Step 4: Derive `always_dni` and `always_dne`

### Prerequisites

Add necessitation rules (if not already present):

```lean
-- In Derivation.lean or as axioms in Bridge.lean
axiom past_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_past
axiom future_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_future
```

### Decomposition Lemmas

```lean
-- In Bridge.lean

theorem always_to_past (φ : Formula) : ⊢ φ.always → φ.all_past := by
  exact lce_imp φ.all_past (φ.and φ.all_future)

theorem always_to_present (φ : Formula) : ⊢ φ.always → φ := by
  have h1 : ⊢ φ.always → (φ.and φ.all_future) := 
    rce_imp φ.all_past (φ.and φ.all_future)
  have h2 : ⊢ (φ.and φ.all_future) → φ := 
    lce_imp φ φ.all_future
  exact imp_trans h1 h2

theorem always_to_future (φ : Formula) : ⊢ φ.always → φ.all_future := by
  have h1 : ⊢ φ.always → (φ.and φ.all_future) := 
    rce_imp φ.all_past (φ.and φ.all_future)
  have h2 : ⊢ (φ.and φ.all_future) → φ.all_future := 
    rce_imp φ φ.all_future
  exact imp_trans h1 h2
```

### Derive `always_dni`

```lean
theorem always_dni (φ : Formula) : ⊢ φ.always.imp φ.neg.neg.always := by
  -- Step 1: ⊢ Hφ → H(¬¬φ)
  have h_past : ⊢ φ.all_past.imp φ.neg.neg.all_past := by
    have dni_phi : ⊢ φ.imp φ.neg.neg := dni φ
    have past_k : ⊢ (φ.imp φ.neg.neg).all_past.imp (φ.all_past.imp φ.neg.neg.all_past) :=
      past_k_dist φ φ.neg.neg
    have h_past_dni : ⊢ (φ.imp φ.neg.neg).all_past := 
      past_necessitation (φ.imp φ.neg.neg) dni_phi
    exact Derivable.modus_ponens [] _ _ past_k h_past_dni
  
  -- Step 2: ⊢ φ → ¬¬φ
  have h_present : ⊢ φ.imp φ.neg.neg := dni φ
  
  -- Step 3: ⊢ Gφ → G(¬¬φ)
  have h_future : ⊢ φ.all_future.imp φ.neg.neg.all_future := by
    have dni_phi : ⊢ φ.imp φ.neg.neg := dni φ
    have future_k : ⊢ (φ.imp φ.neg.neg).all_future.imp (φ.all_future.imp φ.neg.neg.all_future) :=
      future_k_dist φ φ.neg.neg
    have h_future_dni : ⊢ (φ.imp φ.neg.neg).all_future := 
      future_necessitation (φ.imp φ.neg.neg) dni_phi
    exact Derivable.modus_ponens [] _ _ future_k h_future_dni
  
  -- Step 4: Combine
  have h1 : ⊢ φ.always.imp φ.neg.neg.all_past := 
    imp_trans (always_to_past φ) h_past
  have h2 : ⊢ φ.always.imp φ.neg.neg := 
    imp_trans (always_to_present φ) h_present
  have h3 : ⊢ φ.always.imp φ.neg.neg.all_future := 
    imp_trans (always_to_future φ) h_future
  
  have h_conj : ⊢ φ.always.imp (φ.neg.neg.all_past.and (φ.neg.neg.and φ.neg.neg.all_future)) := 
    combine_imp_conj_3 h1 h2 h3
  
  simp only [Formula.always] at h_conj
  exact h_conj
```

### Derive `always_dne`

```lean
theorem always_dne (φ : Formula) : ⊢ φ.neg.neg.always.imp φ.always := by
  -- Similar to always_dni, but use double_negation instead of dni
  -- ... (mirror the structure above)
```

### Remove Axioms

Delete `axiom always_dni` and `axiom always_dne` from `Bridge.lean`.

### Test

```bash
lake build Logos.Core.Theorems.Perpetuity.Bridge
grep -c "axiom always_dn" Logos/Core/Theorems/Perpetuity/Bridge.lean  # Expected: 0
lake test
```

---

## Final Verification

```bash
# Build entire project
lake build

# Count remaining axioms in Bridge.lean
grep -c "axiom" Logos/Core/Theorems/Perpetuity/Bridge.lean

# Count sorry markers in DeductionTheorem.lean
grep -c "sorry" Logos/Core/Metalogic/DeductionTheorem.lean  # Expected: 0

# Run all tests
lake test

# Update documentation
# - IMPLEMENTATION_STATUS.md: Reduce axiom count by 4
# - SORRY_REGISTRY.md: Remove 3 DeductionTheorem entries
```

---

## Troubleshooting

### Issue: `termination_by` not recognized
**Solution**: Ensure `Derivable.height` is defined in `Derivation.lean` (same module as `Derivable`)

### Issue: Circular dependency persists
**Solution**: Verify `Basics.lean` doesn't import `DeductionTheorem.lean` (directly or indirectly)

### Issue: `lce_imp` proof too complex
**Solution**: Keep as axiom temporarily, document in SORRY_REGISTRY.md, revisit later

### Issue: Necessitation rules missing
**Solution**: Add as axioms in `Bridge.lean` or as inference rules in `Derivation.lean`

---

## Resources

- **Full Research Report**: `task_42b_temporal_k_research_report.md`
- **LEAN 4 Docs**: https://lean-lang.org/theorem_proving_in_lean4/
- **Mathlib Examples**: https://github.com/leanprover-community/mathlib4
- **Zulip**: https://leanprover.zulipchat.com/

---

## Success Criteria

- [ ] `lake build` succeeds
- [ ] Zero `sorry` in `DeductionTheorem.lean`
- [ ] Zero circular dependencies
- [ ] 4 fewer axioms in `Bridge.lean`
- [ ] All tests pass (`lake test`)
- [ ] Documentation updated
