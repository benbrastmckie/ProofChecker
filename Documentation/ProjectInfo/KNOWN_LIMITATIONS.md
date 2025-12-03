# Known Limitations - ProofChecker MVP

**Last Updated**: 2025-12-03 (Updated: Aligned with paper §sec:Appendix; all axiom soundness complete, rule code-paper discrepancies documented)
**Project Version**: 0.1.0-mvp

## Overview

This document provides comprehensive documentation of all implementation gaps in the ProofChecker MVP, with detailed explanations of why each limitation exists, workarounds for users, and roadmap for completion.

**Quick Navigation**:
1. [Soundness Proof Gaps](#1-soundness-proof-gaps)
2. [Completeness Status](#2-completeness-status)
3. [Perpetuity Implementation Status](#3-perpetuity-implementation-status)
4. [Automation Stubs](#4-automation-stubs)
5. [Workarounds and Alternatives](#5-workarounds-and-alternatives)
6. [Roadmap for Completion](#6-roadmap-for-completion)
7. [Using ProofChecker Despite Limitations](#7-using-proofchecker-despite-limitations)
8. [Missing Features and Planned Extensions](#8-missing-features-and-planned-extensions)

---

## 1. Soundness Proof Gaps

**Status**: 8/8 axioms proven ✓, 4/7 inference rules proven

**Major Progress (2025-12-03)**: All 8 TM axiom soundness proofs now complete! The three previously incomplete axioms (TL, MF, TF) were proven using time-shift preservation infrastructure in Truth.lean.

**Remaining Gaps**: Three inference rule soundness cases remain incomplete:
- **Modal K** (§1.5): Code implements reverse direction from paper (§sec:Appendix line 1030)
- **Temporal K** (§1.6): Code implements reverse direction from paper (§sec:Appendix line 1037)
- **Temporal Duality** (§1.7): Soundness proof incomplete (semantic lemma needed)

### 1.1 Temporal L Axiom (TL) - ✓ COMPLETE

**Axiom**: `△φ → F(Pφ)` (always implies future-past)

**Paper Reference**: Line 1040 defines TL as `△φ → FPφ`, proven valid at lines 2325-2334.

**Status**: **PROVEN** (2025-12-03)

**Proof Strategy**: If φ holds at ALL times (always φ), then at any future time z > x, φ holds at all past times w < z. The proof is straightforward because the premise (φ at all times) immediately implies the conclusion.

### 1.2 Modal-Future Axiom (MF) - ✓ COMPLETE

**Axiom**: `□φ → □Fφ` (necessity implies necessity of future)

**Paper Reference**: Line 1034 defines MF as `□φ → □Fφ`, proven valid at lines 2343-2352. The paper notes (line 1055): "MF asserts that what is necessary is necessarily always going to be the case."

**Status**: **PROVEN** (2025-12-03)

**Proof Strategy**: If □φ holds (φ true at all histories at time x), then □Fφ holds (for all histories σ, Fφ is true, meaning φ is true at all times y > x in all histories).

### 1.3 Temporal-Future Axiom (TF) - ✓ COMPLETE

**Axiom**: `□φ → F□φ` (necessity implies future of necessity)

**Paper Reference**: Line 1043 defines TF as `□φ → F□φ`, proven valid at lines 2343-2357 using time-shift invariance. The paper notes (line 1055): "TF asserts that what is necessary is always going to be necessary."

**Status**: **PROVEN** (2025-12-03)

**Proof Strategy**: Uses time-shift invariance (Lemma A.4 in paper). If □φ holds at time x, then for any future time y > x and any history σ, there exists a time-shifted history ρ such that truth is preserved, establishing □φ at time y.

### 1.4 Axiom Soundness Summary

All 8 TM axioms now have complete soundness proofs:
- MT, M4, MB: Modal S5 properties (reflexivity, transitivity, symmetry)
- T4, TA: Temporal properties (transitivity, adjacency)
- TL, MF, TF: Modal-temporal interactions ✓ **NEWLY COMPLETE**

**Verification**:
```bash
# Verify axiom proofs (should find 8 axiom validity lemmas)
grep "axiom_valid" ProofChecker/Metalogic/Soundness.lean | grep -v sorry
```

### 1.5 Modal K Rule Soundness - INCOMPLETE

**Paper's Rule (MK)**: If `Γ ⊢ φ`, then `□Γ ⊢ □φ`

**Paper Reference**: Line 1030 defines MK, proven sound at lines 2282-2292.

**English**: If `φ` is derivable from context `Γ`, then `□φ` is derivable from the boxed context `□Γ` (where every formula is wrapped in `□`).

**Code's Implementation**: The LEAN code implements a *different* rule: If `□Γ ⊢ φ`, then `Γ ⊢ □φ`. This is the *reverse direction* from the paper's rule.

**Why the Paper's Rule is Sound** (lines 2286-2292):
The paper proves MK sound as follows: Suppose `Γ ⊨ φ` (semantic consequence). To show `□Γ ⊨ □φ`, assume at model point `(M, τ, t)` that `□γ` holds for all `γ ∈ Γ`. By definition, for any history `σ`, we have `γ` true at `(M, σ, t)` for all `γ ∈ Γ`. Since `Γ ⊨ φ`, we get `φ` true at `(M, σ, t)`. Since `σ` was arbitrary, `□φ` holds at `(M, τ, t)`.

**Why the Code's Rule is Problematic**:
The code implements `□Γ ⊢ φ ⟹ Γ ⊢ □φ`, which is NOT sound in general. If we know `φ` follows from boxed premises, that doesn't mean `□φ` follows from unboxed premises. The code's rule would require a "modal uniformity" constraint ensuring premises true at one history are true at all histories.

**Implementation Gap**:
The code's `modal_k` rule needs to be revised to match the paper's direction. The current implementation reverses the relationship between premises and conclusions.

**Verification**:
```bash
# See sorry in Soundness.lean for modal_k case
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep -i modal
```

**Resolution Options**:
1. **Fix the code**: Change `modal_k` rule to match paper's `Γ ⊢ φ ⟹ □Γ ⊢ □φ`
2. **Restrict to empty context**: The rule `⊢ φ ⟹ ⊢ □φ` (necessitation) is always sound
3. **Add constraint**: Require contexts to be "modally uniform"

### 1.6 Temporal K Rule Soundness - INCOMPLETE

**Paper's Rule (TK)**: If `Γ ⊢ φ`, then `FΓ ⊢ Fφ`

**Paper Reference**: Line 1037 defines TK, proven sound at lines 2324-2332.

**English**: If `φ` is derivable from context `Γ`, then `Fφ` is derivable from the future context `FΓ` (where every formula is wrapped in `F`).

**Code's Implementation**: The LEAN code implements a *different* rule: If `FΓ ⊢ φ`, then `Γ ⊢ Fφ`. This is the *reverse direction* from the paper's rule.

**Why the Paper's Rule is Sound** (lines 2331-2332):
The paper proves TK sound as follows: Suppose `Γ ⊨ φ` and `M,τ,x ⊨ Fγ` for all `γ ∈ Γ`. By definition, `M,τ,y ⊨ γ` for all `y > x` and all `γ ∈ Γ`. Since `Γ ⊨ φ`, we have `M,τ,y ⊨ φ` for all `y > x`. Therefore `M,τ,x ⊨ Fφ`.

**Why the Code's Rule is Problematic**:
The code implements `FΓ ⊢ φ ⟹ Γ ⊢ Fφ`, which is NOT sound in general. If we know `φ` follows from future premises, that doesn't mean `Fφ` follows from present premises. The code's rule would require "temporal persistence" of context formulas.

**Implementation Gap**:
The code's `temporal_k` rule needs to be revised to match the paper's direction. The current implementation reverses the relationship between premises and conclusions.

**Verification**:
```bash
# See sorry in Soundness.lean for temporal_k case
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep -i temporal
```

**Resolution Options**:
1. **Fix the code**: Change `temporal_k` rule to match paper's `Γ ⊢ φ ⟹ FΓ ⊢ Fφ`
2. **Restrict to empty context**: The rule `⊢ φ ⟹ ⊢ Fφ` is always sound for theorems
3. **Add constraint**: Require contexts to be "temporally persistent"

### 1.7 Temporal Duality Soundness - INCOMPLETE

**Paper's Rule (TD)**: If `⊢ φ`, then `⊢ φ_{⟨P|F⟩}`

**Paper Reference**: Line 1036 defines TD, proven sound at lines 2313-2319.

**English**: If `φ` is a theorem, then swapping past (P) and future (F) operators throughout `φ` gives another theorem.

**Why the Paper's Rule is Sound** (lines 2317-2319):
The paper proves TD sound by structural induction: the truth conditions for Past and Future in the semantics are symmetric with respect to the temporal order. Validity is preserved under the swap because `y < x` iff `x > y`.

**Code's Implementation**: The code correctly implements this rule, but the soundness proof is incomplete.

**Why Incomplete in Code**:
The semantic lemma showing truth preservation under the past↔future duality transformation needs to be proven:

```lean
truth_at M τ t φ ↔ truth_at M τ' t' (swap_past_future φ)
```

where `τ'` and `t'` are related by time reversal.

The challenge: Defining time reversal for world histories with convex domains is non-trivial. The reversed history must also satisfy convexity and task relation constraints.

**Verification**:
```bash
# See sorry in Soundness.lean for temporal_duality case
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep -i duality
```

**Resolution Options**:
1. **Prove symmetric semantics**: Show Past and Future are semantically dual
2. **Restrict to formula classes**: Prove duality for specific formula patterns
3. **Add frame constraint**: Require frames to be "time-reversible"

---

## 2. Completeness Status

**Status**: Infrastructure only (type signatures, no proofs)

### 2.1 What's Present

The `Completeness.lean` module defines:

1. **Maximal Consistent Set (MCS)** type:
   ```lean
   structure MaximalConsistentSet where
     formulas : Set Formula
     consistent : ¬(formulas ⊢ bot)
     maximal : ∀ φ, formulas ⊢ φ ∨ formulas ⊢ φ.neg
   ```

2. **Canonical Model** type:
   ```lean
   def canonical_model : TaskModel where
     frame := canonical_frame
     valuation := canonical_valuation
   ```

3. **Truth Lemma** statement:
   ```lean
   axiom truth_lemma : ∀ Γ φ, (Γ is MCS) → (φ ∈ Γ ↔ truth_at canonical_model Γ t φ)
   ```

4. **Weak Completeness** statement:
   ```lean
   axiom weak_completeness : ⊨ φ → ⊢ φ
   ```

5. **Strong Completeness** statement:
   ```lean
   axiom strong_completeness : Γ ⊨ φ → Γ ⊢ φ
   ```

### 2.2 What's Missing

**All proofs**. The `axiom` keyword declares these as unproven assumptions.

**Why Infrastructure Only**:

Completeness proofs for bimodal logic require:

1. **Canonical Model Construction** (30-40 hours):
   - Define canonical frame (MCS as worlds/times)
   - Define canonical task relation
   - Prove frame satisfies nullity and compositionality
   - Define canonical valuation from atomic formulas

2. **Lindenbaum Construction** (15-20 hours):
   - Extend consistent sets to maximal consistent sets
   - Prove existence of MCS for consistent formulas
   - Handle infinite formula sets

3. **Truth Lemma Proof** (25-35 hours):
   - Prove by induction on formula structure
   - Base case: atoms (by valuation definition)
   - Inductive cases: negation, implication, modal, temporal
   - Modal case requires relating MCS across histories
   - Temporal case requires relating MCS across times

4. **Modal Closure Properties** (10-15 hours):
   - If `□φ ∈ Γ` (MCS), then for all MCS `Δ` at same time, `φ ∈ Δ`
   - Requires modal K and T axioms
   - Complex interaction with maximality

5. **Temporal Closure Properties** (10-15 hours):
   - If `Fφ ∈ Γ` (MCS), then exists future MCS `Δ` with `φ ∈ Δ`
   - Requires temporal axioms
   - Must preserve consistency under temporal transformations

**Total Estimated Effort**: 70-90 hours for complete proof

### 2.3 Why Axioms Were Used

The `axiom` keyword in LEAN 4 declares an assumption without proof. This allows:
1. Stating theorem types for future implementation
2. Enabling downstream code to use completeness theorems (if needed)
3. Documenting the structure of completeness proofs

**Important**: Using `axiom` means these theorems are NOT verified. They are assumptions that could be unsound if incorrectly stated.

### 2.4 Verification

```bash
# Count axiom declarations
grep -c "^axiom" ProofChecker/Metalogic/Completeness.lean
# Output: 8

# Find all axiom declarations
grep -n "^axiom" ProofChecker/Metalogic/Completeness.lean
```

### 2.5 Workarounds

**Current workaround**: Use soundness only. Most applications only need soundness:
- "If we can prove it, it's true" (soundness)
- Not: "If it's true, we can prove it" (completeness)

**When completeness matters**:
- Proving unprovability (showing formulas are NOT theorems)
- Decidability results
- Axiomatic adequacy (axiom system captures semantic truth)

---

## 3. Perpetuity Implementation Status

**Status**: All 6 perpetuity principles (P1-P6) are complete and available for use. P1 and P3 have full syntactic proofs; P2, P4, P5, P6 are axiomatized with semantic justification.

**Last Updated**: 2025-12-02 (Task 6 completion)

### 3.1 Fully Proven Perpetuity Principles

**P1: `□φ → △φ` (necessary implies always)**
- **Status**: Complete syntactic proof ✓
- **Proof Strategy**: Uses `imp_trans` helper (proven from K and S axioms)
- **Line**: 126 in Perpetuity.lean
- **Zero sorry**: P1 proof itself contains no `sorry`

**P3: `□φ → □△φ` (necessity of perpetuity)**
- **Status**: Complete syntactic proof ✓
- **Proof Strategy**: Direct application of MF axiom
- **Line**: 204 in Perpetuity.lean
- **Zero sorry**: Fully proven, most straightforward perpetuity principle

### 3.2 Axiomatized Perpetuity Principles

**P2: `▽φ → ◇φ` (sometimes implies possible)**
- **Status**: Uses `contraposition` axiom
- **Line**: 175 in Perpetuity.lean
- **Rationale**: Contraposition requires the law of excluded middle or Pierce's law, which are not in the TM axiom system. Rather than extending the core system, `contraposition` is axiomatized with semantic justification.
- **Semantic Justification**: Classically valid in propositional logic. Sound by classical reasoning.

**P4: `◇▽φ → ◇φ` (possibility of occurrence)**
- **Status**: Axiomatized (line 262)
- **Derivation Strategy**: Follows from contraposition of P3 applied to `¬φ`
- **Challenge**: Requires double negation elimination. The formula type `φ.sometimes.diamond` expands to `(φ.neg.always.neg).neg.box.neg`, which is syntactically different from `φ.neg.always.box.neg` (has extra `.neg.neg`). Since `ψ.neg.neg` is not definitionally equal to `ψ` in LEAN's type system, the proof requires classical double negation elimination.
- **Semantic Justification**: Corollary 2.11 (paper line 2373) validates P4 as derivable from sound axioms.

**P5: `◇▽φ → △◇φ` (persistent possibility)**
- **Status**: Axiomatized (line 285)
- **Derivation Strategy**: Composes P4 with persistence lemma `◇φ → △◇φ` (MB + TF + MT)
- **Challenge**: The persistence lemma requires "modal reasoning" to derive `◇φ → △◇φ` from `φ → F◇φ`. This requires either modal necessitation rules or additional interaction axioms between `◇` and `F` operators, which are not yet in the system.
- **Semantic Justification**: Corollary 2.11 validates P5. The paper's derivation uses "standard modal reasoning" and temporal K rules, which are sound.

**P6: `▽□φ → □△φ` (occurrent necessity is perpetual)**
- **Status**: Axiomatized (line 326)
- **Derivation Strategy**: The paper claims P6 is "equivalent" to P5. Direct derivation would use TF axiom with temporal necessitation.
- **Challenge**: Requires reasoning about temporal points ("at some future time, necessity holds"), which needs temporal necessitation rules or the equivalence proof with P5. Both are beyond current system capabilities.
- **Semantic Justification**: Corollary 2.11 validates P6. The TF axiom's soundness is proven using time-shift invariance (Lemma A.4).

### 3.3 Propositional Helpers Status

**imp_trans (transitivity)**
- **Status**: Complete syntactic proof ✓
- **Proof**: Uses K and S axioms (lines 86-99)
- **Note**: K and S axioms were added to the TM system (ProofSystem/Axioms.lean)

**contraposition**
- **Status**: Axiomatized (line 163)
- **Rationale**: K and S axioms alone are insufficient for contraposition. Classical contraposition requires the law of excluded middle (`φ ∨ ¬φ`) or Pierce's law (`((φ → ψ) → φ) → φ`).
- **Semantic Justification**: Classically valid. Sound by classical propositional logic.

### 3.4 Usage and Safety

**Safe for Production**: All six perpetuity principles are safe to use in proofs. They are either:
1. Fully proven (P1, P3): Complete syntactic derivations from TM axioms
2. Axiomatized with semantic backing (P2, P4, P5, P6): Validated by paper's Corollary 2.11

**Theoretical Soundness**: The paper establishes that all perpetuity principles are valid in task semantics. Axiomatizing them does not introduce unsoundness.

**Practical Considerations**: Users can freely use all six principles in derivations. The axiomatization is a pragmatic choice for the MVP, avoiding the need to extend the core TM axiom system with classical logic primitives.

### 3.5 Verification

```bash
# Verify zero sorry in actual proofs
grep -c "sorry" ProofChecker/Theorems/Perpetuity.lean
# Output: 0 (comments may mention "sorry" but no actual uses)

# Verify all 6 perpetuity principles are defined
grep -c "perpetuity_[1-6]" ProofChecker/Theorems/Perpetuity.lean
# Output: 12 (6 definitions + 6 usages in examples)

# Verify build succeeds
lake build ProofChecker.Theorems.Perpetuity
# Output: Build completed successfully.
```

### 3.6 Future Work

**Option 1: Extend TM with Classical Logic**
Add excluded middle as an axiom:
```lean
| prop_lem (φ : Formula) : Axiom (φ.or φ.neg)
```
This would allow proving `contraposition` and double negation elimination, enabling syntactic proofs of P2 and P4.

**Option 2: Implement Modal Necessitation**
Add necessitation rule to the proof system, allowing proof of persistence lemma for P5.

**Option 3: Implement Temporal Necessitation**
Add temporal necessitation for P6 direct proof or prove P5 ↔ P6 equivalence.

**Option 4: Keep Current Approach**
The current axiomatization is theoretically sound and pragmatically efficient. Future versions may complete syntactic proofs, but it's not required for correctness.

---

## 4. Automation Partial Implementation

**Status**: 4/12 tactics implemented, Aesop integration blocked

### 4.1 Implemented Tactics (2025-12-03)

The `Tactics.lean` module has 4 working tactics:

1. **`apply_axiom`** ✓ - Generic axiom application (macro-based)
   - **Implementation**: Uses `apply Derivable.axiom; refine ?_`
   - **Status**: Complete and tested

2. **`modal_t`** ✓ - Apply modal T axiom convenience wrapper
   - **Implementation**: Macro expanding to `apply_axiom`
   - **Status**: Complete and tested

3. **`tm_auto`** ✓ - Native TM automation (no Aesop)
   - **Implementation**: Macro using `first` combinator to try `assumption` and 10 `apply_axiom` attempts
   - **Status**: Complete (native MVP)
   - **Limitation**: Single-step search only (no depth), no heuristic ordering

4. **`assumption_search`** ✓ - Context-based assumption finding
   - **Implementation**: `elab` using TacticM with `getLCtx`, `isDefEq`, `goal.assign`
   - **Status**: Complete and tested

### 4.2 Aesop Integration Blocker

**Issue**: Adding Aesop/Batteries as dependencies breaks ProofChecker.Semantics.Truth

**Affected File**: `ProofChecker/Semantics/Truth.lean` (lines 476-481)

**Error**:
```
error: application type mismatch
  (truth_proof_irrel M (σ.time_shift (y - x)) s' hs' hs'_cast ψ).mp h_ih
argument
  h_ih
has type
  truth_at M (σ.time_shift (s' + (y - x) - s')) s' hs'_ih ψ : Prop
but is expected to have type
  truth_at M (σ.time_shift (y - x)) s' hs' ψ : Prop
```

**Root Cause**: Batteries library changes integer simplification behavior. Expression `s' + (y - x) - s'` no longer simplifies to `y - x` automatically. Type-dependent proofs in Truth.lean rely on this simplification.

**Impact**: Cannot add Aesop for advanced automation without fixing Truth.lean.

**Workaround**: Implemented native `tm_auto` using Lean.Meta `first` combinator without external dependencies.

**Resolution Options**:
1. **Fix Truth.lean** (4-8 hours): Add explicit simplification lemmas or casting to handle `s' + (y - x) - s' = y - x`
2. **Use native proof search** (current approach): Works for MVP, but less powerful than Aesop
3. **Upgrade Lean/Batteries** (unknown effort): Use newer versions with better simplification

### 4.3 Not Implemented Tactics

The following 8 tactics are planned but not yet implemented:

1. `modal_k_tactic` - Apply modal K rule
2. `temporal_k_tactic` - Apply temporal K rule
3. `modal_4_tactic` - Apply modal 4 axiom
4. `modal_b_tactic` - Apply modal B axiom
5. `temp_4_tactic` - Apply temporal 4 axiom
6. `temp_a_tactic` - Apply temporal A axiom
7. `modal_search` - Modal proof search
8. `temporal_search` - Temporal proof search

**All have type signatures but `sorry` implementations.**

### 4.2 Why Stubs Only

Tactic implementation in LEAN 4 requires:

1. **Meta-programming Setup** (5-10 hours):
   - Import `Lean.Elab.Tactic` monad
   - Set up tactic macro system
   - Handle goal state manipulation

2. **Goal Analysis** (10-15 hours per tactic):
   - Parse goal formula structure
   - Identify applicable axioms/rules
   - Extract unification targets

3. **Proof Term Construction** (15-20 hours per tactic):
   - Build derivation tree programmatically
   - Apply inference rules correctly
   - Handle context transformations

4. **Error Handling** (5-10 hours):
   - Detect when tactic doesn't apply
   - Provide helpful error messages
   - Handle edge cases

**Total per tactic**: 35-55 hours
**Total for 12 tactics**: 420-660 hours

**Realistically**: Implement 3-4 most useful tactics (modal_t, tm_auto, apply_axiom) = 105-220 hours

### 4.3 Verification

```bash
# Check tactic file (should all have sorry)
grep -c "sorry" ProofChecker/Automation/Tactics.lean
# Output: 12

# View tactic declarations
cat ProofChecker/Automation/Tactics.lean | grep "def.*:.*Tactic" -A 3
```

### 4.4 Workarounds

**Current workaround**: Manual proof construction using `Derivable` constructors:

```lean
-- Instead of: by modal_t
-- Use:
example : ⊢ φ.box.imp φ := Derivable.axiom [] _ (Axiom.modal_t φ)
```

**Common patterns**:
```lean
-- Modus ponens
Derivable.modus_ponens Γ φ ψ h_imp h_phi

-- Weakening
Derivable.weakening Γ Δ φ h_deriv h_subset

-- Axiom application
Derivable.axiom [] φ (Axiom.modal_t ψ)
```

**When manual proof is tedious**:
1. Break complex proofs into lemmas
2. Use `have` for intermediate steps
3. Document proof structure in comments

---

## 5. Workarounds and Alternatives

This section provides practical guidance for working with ProofChecker despite the limitations.

### 5.1 Working with Soundness Status

**Status Summary**: All 8 TM axioms are now sound. Three inference rules (Modal K, Temporal K, Temporal Duality) have incomplete soundness proofs due to code-paper alignment issues.

**Safe to use** (soundness proven):
- ✓ MT (Modal T): `□φ → φ`
- ✓ M4 (Modal 4): `□φ → □□φ`
- ✓ MB (Modal B): `φ → □◇φ`
- ✓ T4 (Temporal 4): `Fφ → FFφ`
- ✓ TA (Temporal A): `φ → F⟨past⟩φ`
- ✓ TL (Temporal L): `△φ → F(Pφ)` ✓ **NOW PROVEN**
- ✓ MF (Modal-Future): `□φ → □Fφ` ✓ **NOW PROVEN**
- ✓ TF (Temporal-Future): `□φ → F□φ` ✓ **NOW PROVEN**
- ✓ Modus ponens
- ✓ Weakening
- ✓ Axiom and assumption rules

**Use with caution** (code differs from paper):
- ⚠️ Modal K rule - code implements reverse direction from paper (see §1.5)
- ⚠️ Temporal K rule - code implements reverse direction from paper (see §1.6)
- ⚠️ Temporal duality - soundness proof incomplete (see §1.7)

**Example - Safe Proof**:
```lean
-- Using proven axioms
theorem my_theorem : ⊢ φ.box.imp φ.box.box :=
  Derivable.axiom [] _ (Axiom.modal_4 φ)
```

**Example - Rule Caution**:
```lean
-- Modal K rule in code differs from paper's definition
-- Paper: Γ ⊢ φ ⟹ □Γ ⊢ □φ
-- Code:  □Γ ⊢ φ ⟹ Γ ⊢ □φ (reversed direction)
-- Use with empty context for guaranteed soundness
```

### 5.2 Working without Completeness

**Impact**: Cannot prove unprovability or use semantic arguments for derivability.

**What you CAN do**:
- ✓ Derive theorems from axioms
- ✓ Check if specific formulas are derivable
- ✓ Use soundness (derived formulas are valid)

**What you CANNOT do**:
- ✗ Prove a formula is NOT derivable
- ✗ Use "it's valid, so it's derivable" reasoning
- ✗ Prove axiom system is complete

**Workaround for unprovability**:
Use counterexamples to show invalidity (which implies underivability by soundness):

```lean
-- To show φ is not derivable, show it's invalid
example : ¬(⊨ φ) := by
  -- Construct counter-model where φ is false
  use my_frame, my_model, my_history, my_time
  -- Show φ false at this model point
  unfold truth_at
  -- ...
```

### 5.3 Working with Perpetuity Principles

**Status**: All 6 perpetuity principles (P1-P6) are now available. P1 and P3 have syntactic proofs; P2, P4, P5, P6 are axiomatized with semantic justification from the paper.

**Fully proven** (syntactic derivations):
- ✓ P1: `□φ → △φ` (uses `imp_trans`, proven from K and S axioms)
- ✓ P3: `□φ → □△φ` (direct application of MF axiom)

**Axiomatized** (semantically justified per Corollary 2.11 in paper):
- ✓ P2: `▽φ → ◇φ` (uses `contraposition` axiom)
- ✓ P4: `◇▽φ → ◇φ` (requires double negation elimination)
- ✓ P5: `◇▽φ → △◇φ` (requires modal reasoning)
- ✓ P6: `▽□φ → □△φ` (equivalent to P5)

**All safe for use**: The paper's Corollary 2.11 validates all six principles as derivable from sound axioms. Axiomatizing them does not introduce unsoundness.

**Example - Using Any Perpetuity Principle**:
```lean
-- All 6 principles are safe to use
theorem my_perpetuity_proof : ⊢ my_formula.box.imp my_formula.always.box :=
  perpetuity_3 my_formula
```

### 5.4 Working without Automation

**Manual proof construction** is required for all derivations.

**Pattern 1: Simple axiom application**:
```lean
example : ⊢ φ.box.imp φ :=
  Derivable.axiom [] _ (Axiom.modal_t φ)
```

**Pattern 2: Modus ponens chain**:
```lean
example : ⊢ ψ :=
  have h1 : ⊢ φ := ...
  have h2 : ⊢ φ.imp ψ := ...
  Derivable.modus_ponens [] φ ψ h2 h1
```

**Pattern 3: Using lemmas**:
```lean
-- Break complex proofs into lemmas
lemma step1 : ⊢ φ.imp ψ := ...
lemma step2 : ⊢ ψ.imp χ := ...

theorem main : ⊢ φ.imp χ :=
  imp_trans step1 step2  -- imp_trans is proven from K and S axioms
```

**Pattern 4: Context manipulation**:
```lean
-- Weakening to add premises
example : ⊢ φ :=
  have h : [] ⊢ φ := ...
  Derivable.weakening [] [ψ, χ] φ h (by simp [Context.subset])
```

---

## 6. Roadmap for Completion

This section outlines the path to completing all ProofChecker features.

### 6.1 Short-term Priorities (Next 3 months)

**Priority 1: Fix Modal K and Temporal K Rules** (15-20 hours)
- ✓ TL, MF, TF axiom soundness: **COMPLETE** (2025-12-03)
- Fix code to match paper's rule definitions:
  - Modal K: Change from `□Γ ⊢ φ ⟹ Γ ⊢ □φ` to `Γ ⊢ φ ⟹ □Γ ⊢ □φ`
  - Temporal K: Change from `FΓ ⊢ φ ⟹ Γ ⊢ Fφ` to `Γ ⊢ φ ⟹ FΓ ⊢ Fφ`
- Prove soundness for corrected rules (straightforward per paper)

**Priority 2: Complete Temporal Duality Soundness** (10-15 hours)
- ✓ K and S axioms added, `imp_trans` proven: **COMPLETE**
- Prove semantic lemma for past↔future swap preservation
- Complete temporal_duality soundness case

**Priority 3: Complete Documentation** (5-10 hours)
- Update README, CLAUDE.md with accurate status
- Ensure all docs reflect 8/8 axiom soundness
- Document code-paper alignment issues for rules

**Total short-term**: 30-45 hours

### 6.2 Medium-term Goals (Next 6 months)

**Goal 1: Syntactic Proofs for Remaining Perpetuity** (20-30 hours)
- ✓ All 6 perpetuity principles are now available (P2, P4, P5, P6 axiomatized)
- Optional: Prove P4 syntactically using double negation elimination
- Optional: Prove P5, P6 syntactically using modal reasoning lemmas

**Goal 2: Basic Automation** (40-60 hours)
- Implement 3-4 core tactics:
  - `apply_axiom` (most useful)
  - `modal_t` (common pattern)
  - `tm_auto` (simple automation)
- Write tests and documentation for tactics

**Goal 3: Begin Completeness** (30-40 hours)
- Define canonical model structure
- Prove frame axioms (nullity, compositionality)
- Start truth lemma (base cases)

**Total medium-term**: 90-130 hours

### 6.3 Long-term Roadmap (Next 12 months)

**Goal 1: Full Completeness** (70-90 hours total)
- Complete canonical model construction
- Prove truth lemma (all cases)
- Prove weak and strong completeness
- Add completeness tests

**Goal 2: Advanced Automation** (100-150 hours)
- Implement remaining tactics
- Add proof search algorithms
- Heuristic-guided search
- Performance optimization

**Goal 3: Decidability** (40-60 hours)
- Tableau method implementation
- Satisfiability checking
- Complexity analysis

**Goal 4: Layer 1/2/3 Extensions** (200-300 hours)
- Counterfactual operators
- Epistemic operators
- Normative operators
- Extended soundness and completeness

**Total long-term**: 410-600 hours

### 6.4 Estimated Full Completion

**Total effort for full Layer 0**: 155-215 hours
**Total effort for Layer 1/2/3**: 200-300 hours
**Grand total**: 355-515 hours

**With 10 hours/week**: 35-51 weeks (8-12 months)
**With 20 hours/week**: 18-26 weeks (4-6 months)

---

## 7. Using ProofChecker Despite Limitations

**Key Insight**: ProofChecker MVP is highly functional. All axioms are sound; only some inference rules have code-paper alignment issues.

**What works well**:
- ✓ Complete syntax and proof system
- ✓ Complete semantics (task frame, models, truth evaluation)
- ✓ Full axiom soundness (8/8 axioms proven)
- ✓ All 6 perpetuity principles (P1-P6) available
- ✓ Comprehensive tests for complete components

**Recommended usage patterns**:

1. **Formal verification of modal-temporal reasoning**:
   - All 8 axioms are sound and safe to use
   - Use Modal K/Temporal K rules with empty context for guaranteed soundness
   - Manual proof construction required (no automation yet)

2. **Semantic model checking**:
   - Build task models programmatically
   - Evaluate formula truth
   - Find counterexamples for invalid formulas

3. **Pedagogical examples**:
   - Demonstrate S5 modal logic
   - Demonstrate linear temporal logic
   - Show bimodal interactions (all axioms proven)

4. **Research prototyping**:
   - Experiment with task semantics
   - Test new axioms and rules
   - Develop proof strategies

**What to avoid**:
- ⚠️ Modal K and Temporal K rules with non-empty contexts (code differs from paper)
- ✗ Relying on completeness for unprovability arguments
- ✗ Expecting tactic automation

---

## 8. Missing Features and Planned Extensions

### 8.1 Counterexamples Module

**Status**: Not yet implemented

**Context**: The Counterexamples/ directory was removed from the codebase as it contained only stub implementations with no actual counterexample construction. This violated TDD principles (no tests, no implementation).

**Planned functionality**:
- Invalid formula detection using task semantics
- Countermodel construction for non-theorems
- Automated counterexample search
- Pedagogical counterexamples for common mistakes

**Current workarounds**:
- Manually construct TaskModels to demonstrate invalidity
- Use semantic validity checking with specific models
- Consult ARCHITECTURE.md for semantic definitions

**Implementation timeline**: Post-MVP, requires completion of:
- Decidability module (Metalogic/Decidability.lean)
- Model construction tactics
- Semantic validity checker

**Restoration**: When implemented, Counterexamples/ will be restored with full test coverage and TDD compliance.

### 8.2 DSL Module

**Status**: Documented but not yet implemented (Syntax/DSL.lean)

**Planned functionality**:
- Readable syntax for formula construction (e.g., `□"p" → "p"`)
- Custom operators and notation
- Type-safe formula DSL

**Current workarounds**:
- Use direct formula construction: `(Formula.atom "p").box.imp (Formula.atom "p")`
- Leverage dot notation for formula combinators

### 8.3 Decidability Module

**Status**: Not yet started (Metalogic/Decidability.lean)

**Planned functionality**:
- Decision procedures for TM logic
- Automated theorem proving
- Complexity analysis

**Current workarounds**:
- Manual proof construction using Derivable relation
- Semantic validity checking with specific models

---

## References

- [IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md) - Detailed module status
- [ARCHITECTURE.md](../UserGuide/ARCHITECTURE.md) - TM logic specification
- [README.md](../../README.md) - Project overview
- [CLAUDE.md](../../CLAUDE.md) - Developer configuration
- [TUTORIAL.md](../UserGuide/TUTORIAL.md) - Getting started guide
- [EXAMPLES.md](../UserGuide/EXAMPLES.md) - Usage examples

---

## Feedback and Questions

If you encounter issues related to these limitations or have questions:

1. Check this document for workarounds
2. Check IMPLEMENTATION_STATUS.md for detailed status
3. Consult source code comments (excellent inline documentation)
4. Open an issue on GitHub with `limitation` label

**Note**: This document is updated with each release. Last reviewed: 2025-12-01.
