# Known Limitations - ProofChecker MVP

**Last Updated**: 2025-12-01
**Project Version**: 0.1.0-mvp

## Overview

This document provides comprehensive documentation of all implementation gaps in the ProofChecker MVP, with detailed explanations of why each limitation exists, workarounds for users, and roadmap for completion.

**Quick Navigation**:
1. [Soundness Proof Gaps](#1-soundness-proof-gaps)
2. [Completeness Status](#2-completeness-status)
3. [Perpetuity Partial Implementation](#3-perpetuity-partial-implementation)
4. [Automation Stubs](#4-automation-stubs)
5. [Workarounds and Alternatives](#5-workarounds-and-alternatives)
6. [Roadmap for Completion](#6-roadmap-for-completion)

---

## 1. Soundness Proof Gaps

**Status**: 5/8 axioms proven, 4/7 inference rules proven

### 1.1 Temporal L Axiom (TL)

**Axiom**: `Gφ → G(Hφ)` where G = future (always), H = past

**English**: If `φ` holds at all future times, then at each future time, `φ` holds at all past times relative to that future time.

**Why Incomplete**:
From `Gφ` (future `φ`) we know `φ` holds at all times `s > t`. To prove `G(Hφ)`, we need to show: for all `s > t`, for all `r < s`, `φ` holds at `r`.

The problem: when `r < s` but `r ≤ t`, we have NO information about `φ` at `r` from our premise. The premise `Gφ` only constrains future times relative to the current time `t`, not past times.

**Frame Constraint Needed**:
```lean
-- Backward Temporal Persistence
∀ t s, t < s → (∀ r, r < s → φ at r) → (∀ r, r < t → φ at r)
```

This would require the TaskFrame to enforce that truth values "propagate backward" through time, which is not derivable from nullity and compositionality alone.

**Verification**:
```bash
# See sorry at line 252
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "252"
```

**Alternative Approaches**:
1. Add TL as a frame axiom (semantic restriction)
2. Weaken TL to only apply to times within the original domain
3. Remove TL from the axiom system (proof-theoretic approach)

### 1.2 Modal-Future Axiom (MF)

**Axiom**: `□φ → □(Fφ)`

**English**: If `φ` is necessarily true (at all possible worlds at time `t`), then necessarily, `φ` is true at all future times.

**Why Incomplete**:
`□φ` means `φ` is true at ALL histories at time `t`. The consequent `□(Fφ)` means: for all histories `σ` at time `t`, for all future times `s > t` in `σ`, `φ` is true at `(σ, s)`.

The problem: `□φ` only tells us about `φ` at the CURRENT time `t` across histories, not at other times. To prove MF, we need to show that if `φ` is true at all histories at time `t`, then `φ` remains true at all histories at all future times.

**Frame Constraint Needed**:
```lean
-- Temporal Persistence of Necessity
∀ t s, t < s → (∀ σ, φ at (σ, t)) → (∀ σ, φ at (σ, s))
```

This requires relating truth across different times, which is not provided by the TaskFrame structure.

**Verification**:
```bash
# See sorry at line 294
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "294"
```

**Alternative Approaches**:
1. Add temporal persistence as a frame axiom
2. Restrict MF to formulas satisfying persistence properties
3. Replace MF with weaker axiom relating modal and temporal operators

### 1.3 Temporal-Future Axiom (TF)

**Axiom**: `□φ → F(□φ)`

**English**: If `φ` is necessarily true now, then at all future times, `φ` remains necessarily true.

**Why Incomplete**:
Similar to MF, this relates necessity across different times. From `□φ` at time `t` (all histories satisfy `φ` at `t`), we need to show that at all future times `s > t`, all histories satisfy `φ` at `s`.

The problem: The TaskFrame allows different histories to exist at different times. There's no constraint ensuring that necessary truths (true at all histories at one time) remain necessary at other times.

**Frame Constraint Needed**:
```lean
-- Necessary Truths Persist
∀ t s, t < s → (∀ σ, φ at (σ, t)) → (∀ ρ, φ at (ρ, s))
```

This is a strong constraint saying necessity is time-invariant, not derivable from TaskFrame axioms.

**Verification**:
```bash
# See sorry at line 324
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "324"
```

**Alternative Approaches**:
1. Add axiom schema restricting models (semantic approach)
2. Prove for specific formula classes (e.g., atomic formulas only)
3. Accept partial soundness for provable axioms only

### 1.4 Modal K Rule Soundness

**Rule**: From `Γ.map box ⊢ φ`, derive `Γ ⊢ □φ`

**English**: If `φ` is derivable from the boxed context (every formula in context is boxed), then `□φ` is derivable from the original context.

**Why Incomplete**:
To prove soundness, at a model point `(M, τ, t)` where `Γ` is true, we need `□φ` true. This means: for all histories `σ` at time `t`, `φ` is true at `(M, σ, t)`.

To use the induction hypothesis for `(M, σ, t)`, we need `Γ.map box` true at `(M, σ, t)`. For `ψ ∈ Γ`, we need `ψ.box` true at `(M, σ, t)`, meaning: for all histories `ρ` at time `t`, `ψ` is true at `(M, ρ, t)`.

The problem: From `Γ` true at `(M, τ, t)`, we only know `ψ` true at the SPECIFIC history `τ`, not at ALL histories `ρ`. This requires a frame constraint ensuring contexts are "modally uniform" (if true at one history, true at all histories).

**Frame Constraint Needed**:
```lean
-- Modal Uniformity of Contexts
∀ Γ τ σ t, (∀ ψ ∈ Γ, ψ at (M, τ, t)) → (∀ ψ ∈ Γ, ψ at (M, σ, t))
```

**Verification**:
```bash
# See sorry at line 398
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "398"
```

**Alternative Approaches**:
1. Restrict modal_k rule to empty context `[]` (always sound)
2. Add typing discipline ensuring contexts are modal
3. Add frame constraint for modal closure

### 1.5 Temporal K Rule Soundness

**Rule**: From `Γ.map future ⊢ φ`, derive `Γ ⊢ Fφ`

**English**: If `φ` is derivable from the future context, then `Fφ` is derivable from the original context.

**Why Incomplete**:
Similar to modal_k, at a model point `(M, τ, t)` where `Γ` is true, we need `Fφ` true (for all `s > t`, `φ` at `(M, τ, s)`).

To use the IH at `(M, τ, s)`, we need `Γ.map future` true at `(M, τ, s)`. For `ψ ∈ Γ`, we need `ψ.future` true at `(M, τ, s)`, meaning: for all `r > s`, `ψ` at `(M, τ, r)`.

The problem: From `Γ` true at `(M, τ, t)`, we know `ψ` at time `t`, but `ψ.future` at later time `s` requires `ψ` true at ALL times `> s`. This requires temporal persistence of context formulas.

**Frame Constraint Needed**:
```lean
-- Temporal Uniformity of Contexts
∀ Γ τ t s, t < s → (∀ ψ ∈ Γ, ψ at (M, τ, t)) → (∀ ψ ∈ Γ, ψ at (M, τ, s))
```

**Verification**:
```bash
# See sorry at line 416
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "416"
```

**Alternative Approaches**:
1. Restrict temporal_k rule to empty context `[]`
2. Add typing discipline for temporal contexts
3. Prove for specific formula classes

### 1.6 Temporal Duality Soundness

**Rule**: From `[] ⊢ φ`, derive `[] ⊢ swap_past_future φ`

**English**: If `φ` is a theorem (valid formula), then swapping past and future operators gives another theorem.

**Why Incomplete**:
This requires a deep semantic lemma showing that truth is preserved under the past↔future duality transformation. The proof would need to show:

```lean
truth_at M τ t φ ↔ truth_at M τ' t' (swap_past_future φ)
```

where `τ'` and `t'` are related by time reversal.

The problem: Defining time reversal for world histories with convex domains is non-trivial. The reversed history must also satisfy convexity and task relation constraints. This requires careful semantic analysis and may not hold for all task frames.

**Semantic Lemma Needed**:
```lean
-- Temporal Duality Lemma
∀ M τ t φ, truth_at M τ t φ ↔ truth_at M (reverse τ) (reverse_time t) (swap_past_future φ)
```

Plus definitions of `reverse` and `reverse_time` preserving TaskFrame properties.

**Verification**:
```bash
# See sorry at line 431
grep -n "sorry" ProofChecker/Metalogic/Soundness.lean | grep "431"
```

**Alternative Approaches**:
1. Prove duality for restricted formula classes
2. Add duality as a frame axiom (require reversible frames)
3. Remove temporal_duality rule from system

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

## 3. Perpetuity Partial Implementation

**Status**: P1-P3 proven (with propositional helpers), P4-P6 use `sorry`

### 3.1 Propositional Reasoning Gaps

The TM proof system has:
- ✓ Modal axioms (MT, M4, MB)
- ✓ Temporal axioms (T4, TA, TL, MF, TF)
- ✓ Modus ponens
- ✓ Modal K and Temporal K rules

The TM proof system does NOT have:
- ✗ K axiom: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`
- ✗ S axiom: `φ → (ψ → φ)`
- ✗ Transitivity: `(φ → ψ) → ((ψ → χ) → (φ → χ))`
- ✗ Contraposition: `(φ → ψ) → (¬ψ → ¬φ)`

**Why This Matters**:
Perpetuity principles require propositional reasoning. For example, P1 (`□φ → △φ`) is proven using:
1. MF axiom: `□φ → □(Fφ)`
2. MT axiom: `□(Fφ) → Fφ`
3. **Transitivity**: Combine (1) and (2) to get `□φ → Fφ`

The helper `imp_trans` (line 83-88 in Perpetuity.lean) implements transitivity but uses `sorry` because transitivity is not derivable without propositional axioms K and S.

### 3.2 P1-P3 Status

**P1: `□φ → △φ`** (Perpetuity 1, line 115)
- **Status**: Proof complete, but uses `imp_trans` with `sorry`
- **Sorry location**: Line 88 (in helper)

**P2: `▽φ → ◇φ`** (Perpetuity 2, line 150)
- **Status**: Proof complete, but uses `contraposition` with `sorry`
- **Sorry location**: Line 139 (in helper)

**P3: `□φ → □△φ`** (Perpetuity 3, line 179)
- **Status**: Fully proven, ZERO sorry ✓
- **Proof**: Direct application of MF axiom

### 3.3 P4-P6 Status

**P4: `◇▽φ → ◇φ`** (Perpetuity 4, line 217)
- **Why incomplete**: Contraposition of P3 with complex nested formulas
- **Issue**: Requires reasoning about `(¬φ).future.box.neg` types
- **Sorry location**: Line 225

**P5: `◇▽φ → △◇φ`** (Perpetuity 5, line 248)
- **Why incomplete**: Requires complex modal-temporal interaction
- **Issue**: Combining TF and P3 with possibility persistence reasoning
- **Sorry location**: Line 252

**P6: `▽□φ → □△φ`** (Perpetuity 6, line 271)
- **Why incomplete**: Occurrent necessity requires modal-temporal interaction
- **Issue**: Relating TF axiom to sometimes operator
- **Sorry location**: Line 280

### 3.4 Verification

```bash
# Count all sorry in Perpetuity.lean
grep -c "sorry" ProofChecker/Theorems/Perpetuity.lean
# Output: 14

# Propositional helper sorry
grep -n "sorry" ProofChecker/Theorems/Perpetuity.lean | head -2
# Lines 88, 139

# Complex perpetuity sorry
grep -n "sorry" ProofChecker/Theorems/Perpetuity.lean | grep -E "(225|252|280)"
```

### 3.5 Workarounds

**Option 1: Use only P3**
P3 is fully proven with zero `sorry`. It's the only perpetuity principle safe for production use without caveats.

**Option 2: Add propositional axioms**
Add K and S axioms to proof system:
```lean
| prop_k : ∀ φ ψ χ, Axiom (φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))
| prop_s : ∀ φ ψ, Axiom (φ.imp (ψ.imp φ))
```

Then prove `imp_trans` and `contraposition` using K and S, removing `sorry`.

**Option 3: Implement propositional tactic**
Create `prop_auto` tactic handling common propositional reasoning patterns. Replace `sorry` with `by prop_auto`.

**Option 4: Prove in Lean directly**
Prove perpetuity principles directly in LEAN's type theory without using TM derivability. This establishes semantic validity without relying on the proof system.

---

## 4. Automation Stubs

**Status**: All tactics are function declarations with `sorry` bodies

### 4.1 Declared Tactics

The `Tactics.lean` module declares 12 tactics (lines vary):

1. `modal_k` - Apply modal K rule
2. `temporal_k` - Apply temporal K rule
3. `modal_t` - Apply modal T axiom
4. `modal_4` - Apply modal 4 axiom
5. `modal_b` - Apply modal B axiom
6. `temp_4` - Apply temporal 4 axiom
7. `temp_a` - Apply temporal A axiom
8. `modal_search` - Modal proof search
9. `temporal_search` - Temporal proof search
10. `tm_auto` - Full TM automation
11. `simplify_context` - Context simplification
12. `apply_axiom` - Generic axiom application

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

### 5.1 Working with Partial Soundness

**Recommendation**: Only use axioms and rules with proven soundness.

**Safe to use** (soundness proven):
- ✓ MT (Modal T)
- ✓ M4 (Modal 4)
- ✓ MB (Modal B)
- ✓ T4 (Temporal 4)
- ✓ TA (Temporal A)
- ✓ Modus ponens
- ✓ Weakening
- ✓ Axiom and assumption rules

**Use with caution** (soundness incomplete):
- ⚠️ TL (Temporal L) - may require frame constraints
- ⚠️ MF (Modal-Future) - may require frame constraints
- ⚠️ TF (Temporal-Future) - may require frame constraints
- ⚠️ Modal K rule - only safe with empty or modal contexts
- ⚠️ Temporal K rule - only safe with empty or temporal contexts
- ⚠️ Temporal duality - may not preserve validity for all formulas

**Example - Safe Proof**:
```lean
-- Using only proven components
theorem my_theorem : ⊢ φ.box.imp φ.box.box :=
  Derivable.axiom [] _ (Axiom.modal_4 φ)
```

**Example - Unsafe Proof**:
```lean
-- Uses TL which has incomplete soundness
theorem my_theorem : ⊢ (φ.future).imp (φ.past.future) :=
  Derivable.axiom [] _ (Axiom.temp_l φ)  -- ⚠️ Soundness not proven
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

### 5.3 Working with Partial Perpetuity

**Recommendation**: Only use P3 in production code.

**Fully proven** (safe to use):
- ✓ P3: `□φ → □△φ` (necessity of perpetuity)

**Partial** (use with acknowledgment of propositional gaps):
- ~ P1: `□φ → △φ` (uses `imp_trans` with `sorry`)
- ~ P2: `▽φ → ◇φ` (uses `contraposition` with `sorry`)

**Incomplete** (avoid in production):
- ✗ P4: `◇▽φ → ◇φ`
- ✗ P5: `◇▽φ → △◇φ`
- ✗ P6: `▽□φ → □△φ`

**Example - Safe Usage**:
```lean
-- Use only P3
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
  imp_trans step1 step2  -- Note: uses sorry in imp_trans
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

**Priority 1: Complete Soundness** (15-20 hours)
- Analyze frame constraints for TL, MF, TF
- Determine if constraints are reasonable for task semantics
- Either:
  - Add frame constraints and prove axioms valid, OR
  - Document axioms as conditional (valid under constraints), OR
  - Remove problematic axioms from system

**Priority 2: Fix Propositional Reasoning** (10-15 hours)
- Add propositional axioms K and S to proof system
- Prove `imp_trans` and `contraposition` from K and S
- Remove `sorry` from P1 and P2 proofs

**Priority 3: Complete Documentation** (5-10 hours)
- Update README, CLAUDE.md with accurate status
- Add warnings to Tutorial and Examples
- Link all documentation to this limitations doc

**Total short-term**: 30-45 hours

### 6.2 Medium-term Goals (Next 6 months)

**Goal 1: Complete Perpetuity** (20-30 hours)
- Prove P4 using corrected contraposition
- Develop lemmas for modal-temporal interactions
- Prove P5 and P6 from lemmas

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

**Key Insight**: ProofChecker MVP is highly functional despite partial implementation.

**What works well**:
- ✓ Complete syntax and proof system
- ✓ Complete semantics (task frame, models, truth evaluation)
- ✓ Core soundness (5/8 axioms, 4/7 rules)
- ✓ Perpetuity P3 (fully proven)
- ✓ Comprehensive tests for complete components

**Recommended usage patterns**:

1. **Formal verification of modal-temporal reasoning**:
   - Use proven axioms and rules only
   - Manual proof construction
   - Verify derivations with soundness

2. **Semantic model checking**:
   - Build task models programmatically
   - Evaluate formula truth
   - Find counterexamples for invalid formulas

3. **Pedagogical examples**:
   - Demonstrate S5 modal logic
   - Demonstrate linear temporal logic
   - Show bimodal interactions (using proven components)

4. **Research prototyping**:
   - Experiment with task semantics
   - Test new axioms and rules
   - Develop proof strategies

**What to avoid**:
- ✗ Production use of incomplete axioms (TL, MF, TF)
- ✗ Relying on completeness for unprovability arguments
- ✗ Using unproven perpetuity principles (P4-P6) without caveats
- ✗ Expecting tactic automation

---

## References

- [IMPLEMENTATION_STATUS.md](IMPLEMENTATION_STATUS.md) - Detailed module status
- [ARCHITECTURE.md](ARCHITECTURE.md) - TM logic specification
- [README.md](../README.md) - Project overview
- [CLAUDE.md](../CLAUDE.md) - Developer configuration
- [TUTORIAL.md](TUTORIAL.md) - Getting started guide
- [EXAMPLES.md](EXAMPLES.md) - Usage examples

---

## Feedback and Questions

If you encounter issues related to these limitations or have questions:

1. Check this document for workarounds
2. Check IMPLEMENTATION_STATUS.md for detailed status
3. Consult source code comments (excellent inline documentation)
4. Open an issue on GitHub with `limitation` label

**Note**: This document is updated with each release. Last reviewed: 2025-12-01.
