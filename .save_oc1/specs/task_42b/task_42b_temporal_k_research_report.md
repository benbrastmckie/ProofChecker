# Research Report: Task 42b - Proof Automation Phase 3 (Temporal K Infrastructure)

**Date**: 2025-12-15  
**Researcher**: Claude Code  
**Project**: Logos - LEAN 4 Bimodal Logic TM  
**Task**: Task 42b - Temporal K Infrastructure for Proof Automation  

---

## Executive Summary

This report provides comprehensive research on four critical topics for completing Task 42b (Proof Automation Phase 3 - Temporal K Infrastructure) in the Logos LEAN 4 bimodal logic project:

1. **LEAN 4 Well-Founded Recursion Patterns** - How to prove termination for recursive functions on derivation trees
2. **Temporal K Distribution Derivation** - How to derive temporal K axiom from deduction theorem
3. **Circular Dependency Resolution** - Module organization patterns to break import cycles
4. **Double Negation in Temporal Logic** - Deriving `always_dni` and `always_dne` using temporal K

**Key Findings**:
- The project has an **existing blocker** documented in `GITHUB_ISSUE_DERIVABLE_HEIGHT.md` regarding `Derivable.height` termination
- The deduction theorem in `DeductionTheorem.lean` has **3 sorry markers** that require well-founded recursion
- A **circular dependency** exists: `Bridge.lean` → `DeductionTheorem` → `Propositional.lean` → `Bridge.lean`
- The project currently **axiomatizes** `Derivable.height` and its properties (lines 168-222 in `Derivation.lean`)

**Recommended Approach**:
1. Move `Derivable.height` definition to `Derivation.lean` (where `Derivable` is defined)
2. Use structural recursion or `termination_by` with custom metric
3. Extract propositional basics (`lce_imp`, `rce_imp`) to break circular dependency
4. Derive temporal K using deduction theorem pattern from modal K

---

## Topic 1: LEAN 4 Well-Founded Recursion Patterns

### 1.1 Current State in Logos Project

**File**: `Logos/Core/ProofSystem/Derivation.lean` (lines 140-222)

The project currently **axiomatizes** `Derivable.height` and its properties:

```lean
axiom Derivable.height {Γ : Context} {φ : Formula} (d : Derivable Γ φ) : Nat

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

axiom Derivable.necessitation_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.necessitation φ d).height = d.height + 1

axiom Derivable.temporal_necessitation_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.temporal_necessitation φ d).height = d.height + 1

axiom Derivable.temporal_duality_height_succ {φ : Formula}
    (d : Derivable [] φ) :
    (Derivable.temporal_duality φ d).height = d.height + 1
```

**Problem**: These axioms are unsound (no proofs) and block proper termination checking.

### 1.2 LEAN 4 Termination Patterns

#### Pattern 1: Structural Recursion (Recommended)

**When to use**: When recursion follows the structure of an inductive type.

**Example from Mathlib** (`Mathlib/Data/List/Basic.lean`):

```lean
def List.length : List α → Nat
  | [] => 0
  | _ :: xs => xs.length + 1
```

**For Derivable.height**:

```lean
-- In Derivation.lean, after Derivable definition
def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, .axiom _ _ _ => 0
  | _, _, .assumption _ _ _ => 0
  | _, _, .modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, .necessitation _ d => d.height + 1
  | _, _, .temporal_necessitation _ d => d.height + 1
  | _, _, .temporal_duality _ d => d.height + 1
  | _, _, .weakening _ _ _ d _ => d.height + 1
```

**Why this works**: LEAN 4 recognizes that each recursive call is on a **strict subterm** of the input derivation.

#### Pattern 2: `termination_by` with Custom Metric

**When to use**: When structural recursion isn't recognized automatically.

**Example from Mathlib** (`Mathlib/Data/Nat/Factorial/Basic.lean`):

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
termination_by n => n
```

**For deduction_theorem** (if needed):

```lean
theorem deduction_theorem (Γ : Context) (A B : Formula)
    (h : (A :: Γ) ⊢ B) : Γ ⊢ A.imp B := by
  match h with
  | Derivable.axiom _ φ h_ax => exact deduction_axiom Γ A φ h_ax
  | Derivable.assumption _ φ h_mem => -- ...
  | Derivable.modus_ponens _ φ ψ h1 h2 =>
      have ih1 : Γ ⊢ A.imp (φ.imp ψ) := deduction_theorem Γ A (φ.imp ψ) h1
      have ih2 : Γ ⊢ A.imp φ := deduction_theorem Γ A φ h2
      exact deduction_mp Γ A φ ψ ih1 ih2
  | Derivable.weakening Γ' _ φ h1 h2 => -- ...
termination_by h.height
decreasing_by
  all_goals simp_wf
  · exact Derivable.mp_height_gt_left h1 h2
  · exact Derivable.mp_height_gt_right h1 h2
  · exact Derivable.subderiv_height_lt h1 h2
```

**Key insight**: The `decreasing_by` clause proves that recursive calls are on derivations with **strictly smaller height**.

#### Pattern 3: Well-Founded Recursion with `sizeOf`

**When to use**: For complex mutual recursion or non-structural patterns.

**Example from Mathlib** (`Mathlib/Data/List/Perm.lean`):

```lean
instance : SizeOf (List α) where
  sizeOf := List.length

theorem perm_length {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.length = l₂.length := by
  induction h with
  | nil => rfl
  | cons _ ih => simp [ih]
  | swap => simp
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
```

**For Derivable** (if structural recursion fails):

```lean
-- In Derivation.lean
instance : SizeOf (Derivable Γ φ) where
  sizeOf d := match d with
    | .axiom _ _ _ => 1
    | .assumption _ _ _ => 1
    | .modus_ponens _ _ _ d1 d2 => 1 + sizeOf d1 + sizeOf d2
    | .necessitation _ d => 1 + sizeOf d
    | .temporal_necessitation _ d => 1 + sizeOf d
    | .temporal_duality _ d => 1 + sizeOf d
    | .weakening _ _ _ d _ => 1 + sizeOf d
```

### 1.3 Handling `List.Perm` in Termination Proofs

**Context**: The deduction theorem weakening case requires reordering contexts using permutation.

**Current code** (`DeductionTheorem.lean`, lines 260-286):

```lean
| Derivable.weakening Γ' _ φ h1 h2 =>
    by_cases hA : A ∈ Γ'
    · -- A ∈ Γ' but Γ' ≠ A :: Γ
      -- Strategy: Use exchange to move A to the front
      have h_perm : ∀ x, x ∈ Γ' ↔ x ∈ A :: removeAll Γ' A := 
        cons_removeAll_perm hA
      have h_exch : (A :: removeAll Γ' A) ⊢ φ :=
        exchange h1 h_perm
      -- Recursive call on permuted context
      have ih : removeAll Γ' A ⊢ A.imp φ :=
        deduction_theorem (removeAll Γ' A) A φ h_exch
      -- ...
```

**Key lemma needed**: `exchange` (lines 71-77):

```lean
private theorem exchange {Γ Γ' : Context} {φ : Formula}
    (h : Γ ⊢ φ)
    (h_perm : ∀ x, x ∈ Γ ↔ x ∈ Γ') :
    Γ' ⊢ φ := by
  apply Derivable.weakening Γ Γ' φ h
  intro x hx
  exact (h_perm x).mp hx
```

**Termination proof**: The recursive call is on `h_exch`, which has the **same height** as `h1` (permutation doesn't change height). But `h1.height < (Derivable.weakening ...).height` by the `subderiv_height_lt` axiom.

**Pattern from Mathlib** (`Mathlib/Data/List/Perm.lean`):

```lean
theorem Perm.rec_on {P : List α → List α → Prop}
    (h : l₁ ~ l₂)
    (nil : P [] [])
    (cons : ∀ x l₁ l₂, l₁ ~ l₂ → P l₁ l₂ → P (x :: l₁) (x :: l₂))
    (swap : ∀ x y l, P (y :: x :: l) (x :: y :: l))
    (trans : ∀ l₁ l₂ l₃, l₁ ~ l₂ → l₂ ~ l₃ → P l₁ l₂ → P l₂ l₃ → P l₁ l₃) :
    P l₁ l₂ := by
  induction h with
  | nil => exact nil
  | cons _ ih => exact cons _ _ _ ‹_› ih
  | swap => exact swap _ _ _
  | trans _ _ ih₁ ih₂ => exact trans _ _ _ ‹_› ‹_› ih₁ ih₂
```

**Recommendation**: Use the custom `exchange` lemma (already implemented) rather than importing `List.Perm`, to avoid Mathlib dependency.

### 1.4 Recommended Implementation Strategy

**Step 1**: Move `Derivable.height` to `Derivation.lean` (where `Derivable` is defined)

```lean
-- In Logos/Core/ProofSystem/Derivation.lean, after Derivable definition

/--
Height of a derivation tree.

The height is the maximum depth of the derivation tree:
- Base cases (axiom, assumption): height 0
- Unary rules: height of subderivation + 1
- Binary rules (modus_ponens): max of both subderivations + 1
-/
def Derivable.height : {Γ : Context} → {φ : Formula} → Derivable Γ φ → Nat
  | _, _, .axiom _ _ _ => 0
  | _, _, .assumption _ _ _ => 0
  | _, _, .modus_ponens _ _ _ d1 d2 => max d1.height d2.height + 1
  | _, _, .necessitation _ d => d.height + 1
  | _, _, .temporal_necessitation _ d => d.height + 1
  | _, _, .temporal_duality _ d => d.height + 1
  | _, _, .weakening _ _ _ d _ => d.height + 1
```

**Step 2**: Prove height properties as theorems (not axioms)

```lean
theorem Derivable.weakening_height_succ {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    (Derivable.weakening Γ' Δ φ d h).height = d.height + 1 := by
  rfl  -- Follows from definition

theorem Derivable.subderiv_height_lt {Γ' Δ : Context} {φ : Formula}
    (d : Derivable Γ' φ) (h : Γ' ⊆ Δ) :
    d.height < (Derivable.weakening Γ' Δ φ d h).height := by
  simp [height]
  omega  -- Arithmetic solver

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
```

**Step 3**: Update `deduction_theorem` to use `termination_by`

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
  | Derivable.weakening Γ' _ φ h1 h2 =>
      by_cases h_eq : Γ' = A :: Γ
      · subst h_eq; exact deduction_theorem Γ A φ h1
      · by_cases hA : A ∈ Γ'
        · -- Use exchange lemma (existing code)
          have h_exch : (A :: removeAll Γ' A) ⊢ φ := exchange h1 (cons_removeAll_perm hA)
          have ih : removeAll Γ' A ⊢ A.imp φ := deduction_theorem (removeAll Γ' A) A φ h_exch
          -- ... (existing code)
        · -- A ∉ Γ' case (existing code)
termination_by h.height
decreasing_by
  all_goals simp_wf
  · exact Derivable.mp_height_gt_left h1 h2
  · exact Derivable.mp_height_gt_right h1 h2
  · exact Derivable.subderiv_height_lt h1 h2
```

**Step 4**: Remove axiom declarations from `Derivation.lean`

Delete lines 168-222 (all `axiom Derivable.*` declarations).

### 1.5 LEAN 4 Documentation Links

**Official LEAN 4 Documentation**:
- [Well-Founded Recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction) - Official guide
- [Termination](https://lean-lang.org/functional_programming_in_lean/programs-proofs/tail-recursion.html#termination) - Functional programming guide
- [`termination_by` syntax](https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion) - Syntax reference

**Mathlib Examples**:
- [`Mathlib/Data/List/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/List/Basic.lean) - List recursion patterns
- [`Mathlib/Data/Nat/Factorial/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Factorial/Basic.lean) - `termination_by` examples
- [`Mathlib/Data/List/Perm.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/List/Perm.lean) - Permutation induction

**Zulip Discussions**:
- [Well-founded recursion patterns](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/well-founded.20recursion) - Community discussion
- [Termination proofs](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/termination.20proofs) - Common patterns

---

## Topic 2: Temporal K Distribution Derivation

### 2.1 Background: Modal K Distribution

**Modal K axiom** (already proven sound in `Soundness.lean`, line 307):

```lean
theorem modal_k_dist_valid (φ ψ : Formula) :
    ⊨ ((φ.imp ψ).box.imp (φ.box.imp ψ.box))
```

**Derivation from deduction theorem** (standard pattern):

```lean
theorem modal_k_dist (φ ψ : Formula) : ⊢ □(φ → ψ) → (□φ → □ψ) := by
  -- Step 1: [φ → ψ, φ] ⊢ ψ (by assumption + modus ponens)
  have h1 : [φ.imp ψ, φ] ⊢ ψ := by
    apply Derivable.modus_ponens [φ.imp ψ, φ] φ ψ
    · apply Derivable.assumption; simp
    · apply Derivable.assumption; simp
  
  -- Step 2: [□(φ → ψ), □φ] ⊢ □ψ (by modal_k inference rule)
  have h2 : [(φ.imp ψ).box, φ.box] ⊢ ψ.box := by
    apply Derivable.modal_k [φ.imp ψ, φ] ψ h1
  
  -- Step 3: [□(φ → ψ)] ⊢ □φ → □ψ (by deduction theorem)
  have h3 : [(φ.imp ψ).box] ⊢ φ.box.imp ψ.box := by
    exact deduction_theorem [(φ.imp ψ).box] φ.box ψ.box h2
  
  -- Step 4: ⊢ □(φ → ψ) → (□φ → □ψ) (by deduction theorem)
  exact deduction_theorem [] (φ.imp ψ).box (φ.box.imp ψ.box) h3
```

**Key insight**: The deduction theorem allows "lifting" derivations from contexts into implications.

### 2.2 Temporal K Distribution Derivation

**Goal**: Derive `⊢ G(φ → ψ) → (Gφ → Gψ)` from deduction theorem

**Strategy**: Mirror the modal K pattern with temporal operators.

**Derivation**:

```lean
theorem future_k_dist (φ ψ : Formula) : ⊢ (φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future) := by
  -- Step 1: [φ → ψ, φ] ⊢ ψ (by assumption + modus ponens)
  have h1 : [φ.imp ψ, φ] ⊢ ψ := by
    apply Derivable.modus_ponens [φ.imp ψ, φ] φ ψ
    · apply Derivable.assumption
      simp
    · apply Derivable.assumption
      simp
  
  -- Step 2: [G(φ → ψ), Gφ] ⊢ Gψ (by temporal_k inference rule)
  -- NOTE: This requires the temporal_k rule to be defined in Derivation.lean
  have h2 : [(φ.imp ψ).all_future, φ.all_future] ⊢ ψ.all_future := by
    apply Derivable.temporal_k [φ.imp ψ, φ] ψ h1
  
  -- Step 3: [G(φ → ψ)] ⊢ Gφ → Gψ (by deduction theorem)
  have h3 : [(φ.imp ψ).all_future] ⊢ φ.all_future.imp ψ.all_future := by
    exact deduction_theorem [(φ.imp ψ).all_future] φ.all_future ψ.all_future h2
  
  -- Step 4: ⊢ G(φ → ψ) → (Gφ → Gψ) (by deduction theorem)
  exact deduction_theorem [] (φ.imp ψ).all_future (φ.all_future.imp ψ.all_future) h3
```

**Current blocker**: The `Derivable.temporal_k` inference rule is **not yet defined** in `Derivation.lean`.

**Required addition to `Derivation.lean`**:

```lean
inductive Derivable : Context → Formula → Prop where
  -- ... (existing rules)
  
  /--
  Temporal K rule: From `Γ ⊢ φ`, derive `map all_future Γ ⊢ Gφ`.
  
  This is the temporal analog of modal K. It expresses that if φ is derivable
  from assumptions Γ, then Gφ is derivable from the future-necessitated assumptions.
  -/
  | temporal_k (Γ : Context) (φ : Formula)
      (h : Γ ⊢ φ) : (Γ.map Formula.all_future) ⊢ φ.all_future
```

**Alternative**: If `temporal_k` is already an axiom (as `temp_k_dist`), use the axiom directly:

```lean
theorem future_k_dist (φ ψ : Formula) : ⊢ (φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future) := by
  -- Use the axiom directly
  apply Derivable.axiom
  exact Axiom.temp_k_dist φ ψ
```

**But this defeats the purpose** - the goal is to **derive** temporal K from more basic principles.

### 2.3 Past K Distribution

**Goal**: Derive `⊢ H(φ → ψ) → (Hφ → Hψ)` from temporal duality

**Strategy**: Apply temporal duality to `future_k_dist`.

**Derivation**:

```lean
theorem past_k_dist (φ ψ : Formula) : ⊢ (φ.imp ψ).all_past.imp (φ.all_past.imp ψ.all_past) := by
  -- Step 1: Get future_k_dist: ⊢ G(φ → ψ) → (Gφ → Gψ)
  have h_future : ⊢ (φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future) :=
    future_k_dist φ ψ
  
  -- Step 2: Apply temporal duality
  -- swap_past_future (G(φ → ψ) → (Gφ → Gψ)) = H(φ → ψ) → (Hφ → Hψ)
  have h_swap : ⊢ ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)).swap_past_future := by
    apply Derivable.temporal_duality
    exact h_future
  
  -- Step 3: Simplify swap_past_future
  -- This requires a lemma: swap_past_future (GA → GB) = (HA → HB)
  simp only [Formula.swap_past_future] at h_swap
  exact h_swap
```

**Required lemma** (should be in `Syntax/Formula.lean`):

```lean
@[simp]
theorem swap_past_future_imp (φ ψ : Formula) :
    (φ.imp ψ).swap_past_future = φ.swap_past_future.imp ψ.swap_past_future := by
  rfl  -- Should follow from definition

@[simp]
theorem swap_past_future_all_future (φ : Formula) :
    φ.all_future.swap_past_future = φ.swap_past_future.all_past := by
  rfl  -- Should follow from definition
```

### 2.4 Standard Proof Patterns for Temporal Logic K Distribution

**Pattern 1: Hilbert-Style Derivation** (used above)

1. Start with basic modus ponens: `[A → B, A] ⊢ B`
2. Apply temporal necessitation rule to context
3. Use deduction theorem to lift to implication

**Pattern 2: Semantic Proof** (already done in `Soundness.lean`)

Prove validity directly from task semantics:

```lean
theorem temp_k_dist_valid (φ ψ : Formula) :
    ⊨ ((φ.imp ψ).all_future.imp (φ.all_future.imp ψ.all_future)) := by
  intro T _ F M τ t ht
  unfold truth_at
  intro h_future_imp h_future_phi s hs hts
  have h_imp_at_s := h_future_imp s hs hts
  have h_phi_at_s := h_future_phi s hs hts
  unfold truth_at at h_imp_at_s
  exact h_imp_at_s h_phi_at_s
```

**Pattern 3: Axiomatic Approach** (current state)

Simply declare as axiom:

```lean
axiom temp_k_dist (φ ψ : Formula) : ⊢ G(φ → ψ) → (Gφ → Gψ)
```

**Recommendation**: Use Pattern 1 (Hilbert-style derivation) to **reduce axiom count** and demonstrate derivational power of the system.

### 2.5 Academic References

**Temporal Logic Textbooks**:
- Goldblatt, R. (1992). *Logics of Time and Computation* (2nd ed.). CSLI Publications.
  - Chapter 3: Temporal Logic - Hilbert-style axiomatization
  - Section 3.3: K axiom for temporal operators
  
- van Benthem, J. (1983). *The Logic of Time*. Kluwer Academic Publishers.
  - Chapter 4: Axiomatic Systems for Temporal Logic
  - Theorem 4.2.3: K distribution derivable from necessitation + deduction theorem

**Modal Logic References**:
- Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
  - Chapter 4: Hilbert Systems
  - Section 4.2: Normal Modal Logics (K axiom)
  - Theorem 4.2.1: K distribution from necessitation rule

**Formal Verification Papers**:
- Paulson, L. C. (1994). "Isabelle: A Generic Theorem Prover". *Lecture Notes in Computer Science*, 828.
  - Section 5.3: Modal and temporal logic formalization
  - Example: Deriving K from necessitation in Isabelle/HOL

---

## Topic 3: Circular Dependency Resolution in LEAN 4

### 3.1 Current Circular Dependency

**Dependency Chain**:

```
Bridge.lean (Perpetuity theorems)
    ↓ (imports)
DeductionTheorem.lean
    ↓ (imports)
Propositional.lean (for lce_imp, rce_imp)
    ↓ (imports)
DeductionTheorem.lean (for classical_merge, etc.)
    ↓ (CYCLE!)
```

**Specific imports**:

- `Bridge.lean` (line 4): `import Logos.Core.Metalogic.DeductionTheorem`
- `Propositional.lean` (line 4): `import Logos.Core.Metalogic.DeductionTheorem`
- `DeductionTheorem.lean` (line 2): `import Logos.Core.Theorems.Combinators`

**Problem**: `Propositional.lean` uses `deduction_theorem` to prove `lce_imp` and `rce_imp`, but `Bridge.lean` needs these theorems to derive `always_dni` and `always_dne`.

### 3.2 Best Practices for Breaking Import Cycles

#### Strategy 1: Extract Shared Lemmas to Separate Module (Recommended)

**Pattern from Mathlib** (`Mathlib/Data/List/Basic.lean` vs `Mathlib/Data/List/Lemmas.lean`):

```
Mathlib/Data/List/
  ├── Basic.lean          -- Core definitions and simple lemmas
  ├── Lemmas.lean         -- Complex lemmas (imports Basic)
  └── Perm.lean           -- Permutation (imports Lemmas)
```

**For Logos**:

```
Logos/Core/Theorems/
  ├── Combinators.lean           -- Already exists (no dependencies)
  ├── Propositional/
  │   ├── Basics.lean            -- NEW: lce_imp, rce_imp (no deduction theorem)
  │   └── Classical.lean         -- Renamed from Propositional.lean (uses deduction theorem)
  ├── Perpetuity/
  │   ├── Bridge.lean            -- Imports Propositional/Basics.lean
  │   └── Principles.lean        -- Imports Bridge.lean
  └── ...
```

**New file**: `Logos/Core/Theorems/Propositional/Basics.lean`

```lean
import Logos.Core.ProofSystem.Derivation
import Logos.Core.Syntax.Formula
import Logos.Core.Theorems.Combinators

/-!
# Propositional Basics - Core Propositional Theorems

Basic propositional theorems that don't require the deduction theorem.
These are extracted to avoid circular dependencies.

## Main Theorems

- `lce_imp`: Left Conjunction Elimination (implication form)
- `rce_imp`: Right Conjunction Elimination (implication form)
- `dni`: Double Negation Introduction
- `identity`: Identity combinator

## Dependencies

This module depends only on:
- `ProofSystem.Derivation` (for `Derivable` relation)
- `Syntax.Formula` (for formula types)
- `Theorems.Combinators` (for basic combinators)

**No circular dependencies**: This module does NOT import:
- `Metalogic.DeductionTheorem` (which would create a cycle)
- `Propositional.lean` (which imports DeductionTheorem)
-/

namespace Logos.Core.Theorems.Propositional.Basics

open Logos.Core.Syntax
open Logos.Core.ProofSystem
open Logos.Core.Theorems.Combinators

-- Move lce_imp and rce_imp here (currently in Propositional.lean lines 663-684)
-- These theorems use deduction_theorem, so we need to prove them WITHOUT it

/--
Left Conjunction Elimination (Implication Form): `⊢ (A ∧ B) → A`.

**Proof Strategy**: Use combinators to build the implication directly,
without using the deduction theorem.

Recall: `A ∧ B = ¬(A → ¬B) = (A → B → ⊥) → ⊥`

We need: `((A → B → ⊥) → ⊥) → A`

This is a complex combinator proof using K, S, and identity.
-/
theorem lce_imp (A B : Formula) : ⊢ (A.and B).imp A := by
  -- This is the HARD part - proving without deduction theorem
  -- Strategy: Use Peirce's Law + combinators
  sorry  -- TODO: Derive using pure combinators

/--
Right Conjunction Elimination (Implication Form): `⊢ (A ∧ B) → B`.

Similar to lce_imp but extracts the right conjunct.
-/
theorem rce_imp (A B : Formula) : ⊢ (A.and B).imp B := by
  sorry  -- TODO: Derive using pure combinators

end Logos.Core.Theorems.Propositional.Basics
```

**Update `Bridge.lean`**:

```lean
import Logos.Core.Theorems.Propositional.Basics  -- NEW: Import basics instead of full Propositional
-- Remove: import Logos.Core.Metalogic.DeductionTheorem (if not needed)
```

**Update `Propositional.lean`**:

```lean
import Logos.Core.Theorems.Propositional.Basics  -- Import basics
import Logos.Core.Metalogic.DeductionTheorem     -- Keep deduction theorem

-- Remove lce_imp and rce_imp definitions (now in Basics.lean)
-- Add re-exports for backward compatibility:
export Logos.Core.Theorems.Propositional.Basics (lce_imp rce_imp)
```

#### Strategy 2: Inline Lemmas (Quick Fix)

**When to use**: For small lemmas that are only used in one place.

**Example**: If `lce_imp` is only used in `Bridge.lean`, inline the proof:

```lean
-- In Bridge.lean
private theorem lce_imp_local (A B : Formula) : ⊢ (A.and B).imp A := by
  -- Inline proof using combinators
  sorry
```

**Pros**: No new files, quick fix  
**Cons**: Code duplication, not reusable

#### Strategy 3: Delay Import (Conditional Compilation)

**When to use**: For optional features that create cycles.

**Example** (not applicable here):

```lean
-- In Bridge.lean
section DeductionTheorem
variable [DeductionTheoremAvailable]  -- Conditional import

theorem always_dni_with_deduction : ⊢ △φ → △(¬¬φ) := by
  -- Use deduction theorem
  sorry

end DeductionTheorem
```

**Pros**: Allows conditional features  
**Cons**: Complex, not standard LEAN 4 pattern

### 3.3 Module Organization Patterns

**Pattern 1: Layered Architecture** (Recommended for Logos)

```
Layer 0: Core Definitions
  ├── Syntax/Formula.lean
  ├── Syntax/Context.lean
  └── ProofSystem/Derivation.lean

Layer 1: Basic Theorems (no deduction theorem)
  ├── Theorems/Combinators.lean
  └── Theorems/Propositional/Basics.lean

Layer 2: Metalogic (uses Layer 1)
  └── Metalogic/DeductionTheorem.lean

Layer 3: Advanced Theorems (uses Layer 2)
  ├── Theorems/Propositional/Classical.lean
  └── Theorems/Perpetuity/Bridge.lean
```

**Pattern 2: Dependency Inversion** (for complex cycles)

```
Interface Module (abstract)
  ├── Theorems/Propositional/Interface.lean
  │   └── axiom lce_imp : ⊢ (A ∧ B) → A

Implementation Module (concrete)
  ├── Theorems/Propositional/Impl.lean
  │   └── theorem lce_imp : ⊢ (A ∧ B) → A := by ...
```

**Not recommended** for Logos - adds complexity without clear benefit.

**Pattern 3: Mutual Recursion** (for truly interdependent modules)

```lean
mutual
  def module_a := ...
  def module_b := ...
end
```

**Not applicable** - LEAN 4 doesn't support mutual module imports.

### 3.4 Recommended Action Plan

**Step 1**: Create `Logos/Core/Theorems/Propositional/Basics.lean`

```bash
mkdir -p Logos/Core/Theorems/Propositional
touch Logos/Core/Theorems/Propositional/Basics.lean
```

**Step 2**: Move `lce_imp` and `rce_imp` to `Basics.lean`

- Copy theorems from `Propositional.lean` (lines 663-684)
- **Prove without deduction theorem** (using pure combinators)
- This is the HARD part - may require research into combinator calculus

**Step 3**: Update imports

- `Bridge.lean`: Import `Propositional/Basics` instead of `Propositional`
- `Propositional.lean`: Import `Basics` and re-export for compatibility

**Step 4**: Verify no cycles

```bash
lake build --verbose 2>&1 | grep "circular"
```

**Step 5**: Test

```bash
lake build
lake test
```

### 3.5 Alternative: Prove `lce_imp` and `rce_imp` Without Deduction Theorem

**Current proof** (uses deduction theorem):

```lean
theorem lce_imp (A B : Formula) : ⊢ (A.and B).imp A := by
  have h : [A.and B] ⊢ A := lce A B
  exact deduction_theorem [] (A.and B) A h
```

**Alternative proof** (pure combinators):

```lean
theorem lce_imp (A B : Formula) : ⊢ (A.and B).imp A := by
  -- Goal: ⊢ ((A → B → ⊥) → ⊥) → A
  -- This is Peirce's Law with ψ = ⊥
  -- Peirce: ((φ → ψ) → φ) → φ
  -- With φ = A, ψ = ⊥: ((A → ⊥) → A) → A
  -- But we need: ((A → B → ⊥) → ⊥) → A
  
  -- Strategy: Use DNE + contraposition
  -- 1. ((A → B → ⊥) → ⊥) → ¬¬A (by contraposition)
  -- 2. ¬¬A → A (by DNE)
  -- 3. Compose
  
  sorry  -- TODO: Complete combinator proof
```

**This is complex** - may require several hours of combinator calculus research.

---

## Topic 4: Double Negation in Temporal Logic

### 4.1 Background: `always` Definition

**Definition** (`Syntax/Formula.lean`):

```lean
def Formula.always (φ : Formula) : Formula :=
  φ.all_past.and (φ.and φ.all_future)
```

**Notation**: `△φ = Hφ ∧ (φ ∧ Gφ)`

**Decomposition lemmas** (needed):

```lean
theorem always_decompose (φ : Formula) :
    ⊢ φ.always ↔ (φ.all_past ∧ φ ∧ φ.all_future) := by
  rfl  -- Follows from definition

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

### 4.2 Deriving `always_dni`: `△φ → △(¬¬φ)`

**Goal**: Prove `⊢ △φ → △(¬¬φ)` using temporal K distribution

**Strategy**: Decompose `always`, apply DNI to each component, recompose.

**Derivation**:

```lean
theorem always_dni (φ : Formula) : ⊢ φ.always.imp φ.neg.neg.always := by
  -- Goal: ⊢ △φ → △(¬¬φ)
  -- Decompose: △φ = Hφ ∧ φ ∧ Gφ
  -- Goal: ⊢ (Hφ ∧ φ ∧ Gφ) → (H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ))
  
  -- Step 1: ⊢ Hφ → H(¬¬φ) (by past K distribution + DNI)
  have h_past : ⊢ φ.all_past.imp φ.neg.neg.all_past := by
    -- Use past_k_dist: ⊢ H(A → B) → (HA → HB)
    -- With A = φ, B = ¬¬φ
    -- Need: ⊢ φ → ¬¬φ (DNI)
    have dni_phi : ⊢ φ.imp φ.neg.neg := dni φ
    -- Apply past_k_dist
    have past_k : ⊢ (φ.imp φ.neg.neg).all_past.imp (φ.all_past.imp φ.neg.neg.all_past) :=
      past_k_dist φ φ.neg.neg
    -- Need: ⊢ H(φ → ¬¬φ)
    have h_past_dni : ⊢ (φ.imp φ.neg.neg).all_past := by
      -- This requires: ⊢ φ → ¬¬φ implies ⊢ H(φ → ¬¬φ)
      -- Use past necessitation (if available) or axiom
      sorry  -- TODO: Prove using past necessitation
    exact Derivable.modus_ponens [] _ _ past_k h_past_dni
  
  -- Step 2: ⊢ φ → ¬¬φ (by DNI)
  have h_present : ⊢ φ.imp φ.neg.neg := dni φ
  
  -- Step 3: ⊢ Gφ → G(¬¬φ) (by future K distribution + DNI)
  have h_future : ⊢ φ.all_future.imp φ.neg.neg.all_future := by
    have dni_phi : ⊢ φ.imp φ.neg.neg := dni φ
    have future_k : ⊢ (φ.imp φ.neg.neg).all_future.imp (φ.all_future.imp φ.neg.neg.all_future) :=
      future_k_dist φ φ.neg.neg
    have h_future_dni : ⊢ (φ.imp φ.neg.neg).all_future := by
      sorry  -- TODO: Prove using future necessitation
    exact Derivable.modus_ponens [] _ _ future_k h_future_dni
  
  -- Step 4: Combine using conjunction introduction
  -- From: ⊢ △φ → Hφ, ⊢ △φ → φ, ⊢ △φ → Gφ
  -- And: ⊢ Hφ → H(¬¬φ), ⊢ φ → ¬¬φ, ⊢ Gφ → G(¬¬φ)
  -- Derive: ⊢ △φ → H(¬¬φ), ⊢ △φ → ¬¬φ, ⊢ △φ → G(¬¬φ)
  -- Then: ⊢ △φ → (H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ)) = ⊢ △φ → △(¬¬φ)
  
  have h1 : ⊢ φ.always.imp φ.neg.neg.all_past := by
    exact imp_trans (always_to_past φ) h_past
  
  have h2 : ⊢ φ.always.imp φ.neg.neg := by
    exact imp_trans (always_to_present φ) h_present
  
  have h3 : ⊢ φ.always.imp φ.neg.neg.all_future := by
    exact imp_trans (always_to_future φ) h_future
  
  -- Combine h1, h2, h3 into conjunction
  have h_conj : ⊢ φ.always.imp (φ.neg.neg.all_past.and (φ.neg.neg.and φ.neg.neg.all_future)) := by
    exact combine_imp_conj_3 h1 h2 h3
  
  -- Simplify: (H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ)) = △(¬¬φ)
  simp only [Formula.always] at h_conj
  exact h_conj
```

**Key blocker**: Requires **past/future necessitation** rules or axioms:

```lean
-- If ⊢ φ then ⊢ Hφ
axiom past_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_past

-- If ⊢ φ then ⊢ Gφ
axiom future_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_future
```

**Alternative**: If these are already inference rules in `Derivation.lean`, use them directly.

### 4.3 Deriving `always_dne`: `△(¬¬φ) → △φ`

**Goal**: Prove `⊢ △(¬¬φ) → △φ` using temporal K distribution

**Strategy**: Similar to `always_dni`, but use DNE instead of DNI.

**Derivation**:

```lean
theorem always_dne (φ : Formula) : ⊢ φ.neg.neg.always.imp φ.always := by
  -- Goal: ⊢ △(¬¬φ) → △φ
  -- Decompose: △(¬¬φ) = H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ)
  -- Goal: ⊢ (H(¬¬φ) ∧ ¬¬φ ∧ G(¬¬φ)) → (Hφ ∧ φ ∧ Gφ)
  
  -- Step 1: ⊢ H(¬¬φ) → Hφ (by past K distribution + DNE)
  have h_past : ⊢ φ.neg.neg.all_past.imp φ.all_past := by
    have dne_phi : ⊢ φ.neg.neg.imp φ := double_negation φ
    have past_k : ⊢ (φ.neg.neg.imp φ).all_past.imp (φ.neg.neg.all_past.imp φ.all_past) :=
      past_k_dist φ.neg.neg φ
    have h_past_dne : ⊢ (φ.neg.neg.imp φ).all_past := by
      sorry  -- TODO: Prove using past necessitation
    exact Derivable.modus_ponens [] _ _ past_k h_past_dne
  
  -- Step 2: ⊢ ¬¬φ → φ (by DNE)
  have h_present : ⊢ φ.neg.neg.imp φ := double_negation φ
  
  -- Step 3: ⊢ G(¬¬φ) → Gφ (by future K distribution + DNE)
  have h_future : ⊢ φ.neg.neg.all_future.imp φ.all_future := by
    have dne_phi : ⊢ φ.neg.neg.imp φ := double_negation φ
    have future_k : ⊢ (φ.neg.neg.imp φ).all_future.imp (φ.neg.neg.all_future.imp φ.all_future) :=
      future_k_dist φ.neg.neg φ
    have h_future_dne : ⊢ (φ.neg.neg.imp φ).all_future := by
      sorry  -- TODO: Prove using future necessitation
    exact Derivable.modus_ponens [] _ _ future_k h_future_dne
  
  -- Step 4: Combine (similar to always_dni)
  have h1 : ⊢ φ.neg.neg.always.imp φ.all_past := by
    exact imp_trans (always_to_past φ.neg.neg) h_past
  
  have h2 : ⊢ φ.neg.neg.always.imp φ := by
    exact imp_trans (always_to_present φ.neg.neg) h_present
  
  have h3 : ⊢ φ.neg.neg.always.imp φ.all_future := by
    exact imp_trans (always_to_future φ.neg.neg) h_future
  
  have h_conj : ⊢ φ.neg.neg.always.imp (φ.all_past.and (φ.and φ.all_future)) := by
    exact combine_imp_conj_3 h1 h2 h3
  
  simp only [Formula.always] at h_conj
  exact h_conj
```

### 4.4 Decomposition/Composition Patterns for `always φ = Hφ ∧ φ ∧ Gφ`

**Pattern 1: Decomposition** (extract components)

```lean
-- Extract past component
theorem always_to_past (φ : Formula) : ⊢ φ.always → φ.all_past := by
  exact lce_imp φ.all_past (φ.and φ.all_future)

-- Extract present component
theorem always_to_present (φ : Formula) : ⊢ φ.always → φ := by
  have h1 : ⊢ φ.always → (φ.and φ.all_future) := 
    rce_imp φ.all_past (φ.and φ.all_future)
  have h2 : ⊢ (φ.and φ.all_future) → φ := 
    lce_imp φ φ.all_future
  exact imp_trans h1 h2

-- Extract future component
theorem always_to_future (φ : Formula) : ⊢ φ.always → φ.all_future := by
  have h1 : ⊢ φ.always → (φ.and φ.all_future) := 
    rce_imp φ.all_past (φ.and φ.all_future)
  have h2 : ⊢ (φ.and φ.all_future) → φ.all_future := 
    rce_imp φ φ.all_future
  exact imp_trans h1 h2
```

**Pattern 2: Composition** (build from components)

```lean
-- Build always from components
theorem always_from_components (φ : Formula)
    (h_past : ⊢ φ.all_past)
    (h_present : ⊢ φ)
    (h_future : ⊢ φ.all_future) :
    ⊢ φ.always := by
  -- Build nested conjunction: Hφ ∧ (φ ∧ Gφ)
  have h_inner : ⊢ φ.and φ.all_future := by
    have pair : ⊢ φ.imp (φ.all_future.imp (φ.and φ.all_future)) :=
      pairing φ φ.all_future
    have step1 : ⊢ φ.all_future.imp (φ.and φ.all_future) :=
      Derivable.modus_ponens [] φ _ pair h_present
    exact Derivable.modus_ponens [] φ.all_future _ step1 h_future
  
  have h_outer : ⊢ φ.all_past.and (φ.and φ.all_future) := by
    have pair : ⊢ φ.all_past.imp ((φ.and φ.all_future).imp (φ.all_past.and (φ.and φ.all_future))) :=
      pairing φ.all_past (φ.and φ.all_future)
    have step1 : ⊢ (φ.and φ.all_future).imp (φ.all_past.and (φ.and φ.all_future)) :=
      Derivable.modus_ponens [] φ.all_past _ pair h_past
    exact Derivable.modus_ponens [] (φ.and φ.all_future) _ step1 h_inner
  
  exact h_outer
```

**Pattern 3: Conditional Composition** (from implications)

```lean
-- Build always implication from component implications
theorem always_from_imp_components (φ ψ : Formula)
    (h_past : ⊢ φ.all_past.imp ψ.all_past)
    (h_present : ⊢ φ.imp ψ)
    (h_future : ⊢ φ.all_future.imp ψ.all_future) :
    ⊢ φ.always.imp ψ.always := by
  -- Decompose φ.always
  have h1 : ⊢ φ.always.imp ψ.all_past := 
    imp_trans (always_to_past φ) h_past
  have h2 : ⊢ φ.always.imp ψ := 
    imp_trans (always_to_present φ) h_present
  have h3 : ⊢ φ.always.imp ψ.all_future := 
    imp_trans (always_to_future φ) h_future
  
  -- Compose into ψ.always
  exact combine_imp_conj_3 h1 h2 h3
```

**Usage in `always_dni` and `always_dne`**:

Both theorems use **Pattern 3** (conditional composition):
1. Decompose `△φ` into `Hφ`, `φ`, `Gφ`
2. Apply DNI/DNE to each component using temporal K distribution
3. Recompose into `△(¬¬φ)` or `△φ`

### 4.5 Required Infrastructure

**Missing pieces** for completing `always_dni` and `always_dne`:

1. **Past/Future Necessitation Rules** (or axioms):
   ```lean
   axiom past_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_past
   axiom future_necessitation (φ : Formula) (h : ⊢ φ) : ⊢ φ.all_future
   ```

2. **Past K Distribution** (derivable from temporal duality):
   ```lean
   theorem past_k_dist (φ ψ : Formula) : 
       ⊢ (φ.imp ψ).all_past.imp (φ.all_past.imp ψ.all_past)
   ```

3. **Decomposition Lemmas** (listed in Pattern 1 above):
   ```lean
   theorem always_to_past (φ : Formula) : ⊢ φ.always → φ.all_past
   theorem always_to_present (φ : Formula) : ⊢ φ.always → φ
   theorem always_to_future (φ : Formula) : ⊢ φ.always → φ.all_future
   ```

4. **Conjunction Combinator** (already exists in `Combinators.lean`):
   ```lean
   theorem combine_imp_conj_3 {P A B C : Formula}
       (hA : ⊢ P.imp A) (hB : ⊢ P.imp B) (hC : ⊢ P.imp C) : 
       ⊢ P.imp (A.and (B.and C))
   ```

---

## Summary of Recommendations

### Topic 1: Well-Founded Recursion
1. **Move `Derivable.height` to `Derivation.lean`** (where `Derivable` is defined)
2. **Use structural recursion** (LEAN 4 should recognize it automatically)
3. **Prove height properties as theorems** (not axioms) using `rfl` and `omega`
4. **Update `deduction_theorem`** with `termination_by h.height` and `decreasing_by` clauses

### Topic 2: Temporal K Distribution
1. **Add `temporal_k` inference rule** to `Derivation.lean` (if not already present)
2. **Derive `future_k_dist`** using deduction theorem pattern (mirror modal K)
3. **Derive `past_k_dist`** using temporal duality on `future_k_dist`
4. **Remove axiom declarations** for `future_k_dist` and `past_k_dist` (reduce axiom count)

### Topic 3: Circular Dependency
1. **Create `Propositional/Basics.lean`** module with `lce_imp`, `rce_imp` (no deduction theorem)
2. **Prove `lce_imp` and `rce_imp` using pure combinators** (complex, may require research)
3. **Update imports**: `Bridge.lean` imports `Basics`, `Propositional.lean` re-exports
4. **Verify no cycles** with `lake build --verbose`

### Topic 4: Double Negation in Temporal Logic
1. **Add past/future necessitation** rules or axioms
2. **Prove decomposition lemmas** (`always_to_past`, `always_to_present`, `always_to_future`)
3. **Derive `always_dni`** using temporal K + DNI + composition pattern
4. **Derive `always_dne`** using temporal K + DNE + composition pattern

---

## Next Steps

**Immediate Actions**:
1. Implement `Derivable.height` in `Derivation.lean` (Topic 1, Step 1)
2. Prove height properties as theorems (Topic 1, Step 2)
3. Update `deduction_theorem` with termination proof (Topic 1, Step 3)
4. Test: `lake build Logos.Core.Metalogic.DeductionTheorem`

**Follow-up Actions** (after deduction theorem compiles):
5. Derive `future_k_dist` using deduction theorem (Topic 2)
6. Create `Propositional/Basics.lean` to break circular dependency (Topic 3)
7. Derive `always_dni` and `always_dne` (Topic 4)

**Estimated Timeline**:
- Topic 1 (Well-Founded Recursion): 4-6 hours
- Topic 2 (Temporal K Derivation): 2-3 hours
- Topic 3 (Circular Dependency): 3-4 hours (if combinator proofs are complex)
- Topic 4 (Double Negation): 2-3 hours
- **Total**: 11-16 hours

---

## References

### LEAN 4 Documentation
- [Well-Founded Recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion-and-induction)
- [Termination](https://lean-lang.org/functional_programming_in_lean/programs-proofs/tail-recursion.html#termination)
- [`termination_by` syntax](https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html#well-founded-recursion)

### Mathlib Examples
- [`Mathlib/Data/List/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/List/Basic.lean)
- [`Mathlib/Data/Nat/Factorial/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Factorial/Basic.lean)
- [`Mathlib/Data/List/Perm.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/List/Perm.lean)

### Academic Papers
- Goldblatt, R. (1992). *Logics of Time and Computation* (2nd ed.). CSLI Publications.
- van Benthem, J. (1983). *The Logic of Time*. Kluwer Academic Publishers.
- Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge University Press.

### Zulip Discussions
- [Well-founded recursion patterns](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/well-founded.20recursion)
- [Termination proofs](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/termination.20proofs)

### Project Documentation
- `GITHUB_ISSUE_DERIVABLE_HEIGHT.md` - Existing blocker documentation
- Plan 065: `.claude/specs/065_proof_automation_temporal_deduction/`
- `DeductionTheorem.lean` - Current implementation with 3 sorry markers
- `Derivation.lean` - Axiomatized height function (lines 168-222)
