# Tactic Development Guide for ProofChecker

This document provides guidelines for developing custom tactics for the ProofChecker proof automation system.

## 1. Custom Tactics Roadmap

### Priority Tactics (Layer 0 - Core TM)

| Tactic | Purpose | Status |
|--------|---------|--------|
| `modal_k` | Apply modal K rule (MK) | Planned |
| `temporal_k` | Apply temporal K rule (TK) | Planned |
| `modal_t` | Apply axiom MT (□φ → φ) | Planned |
| `modal_4` | Apply axiom M4 (□φ → □□φ) | Planned |
| `modal_b` | Apply axiom MB (φ → □◇φ) | Planned |
| `s5_simp` | Simplify S5 modal formulas | Planned |
| `temporal_simp` | Simplify temporal formulas | Planned |
| `bimodal_simp` | Simplify using MF/TF axioms | Planned |
| `perpetuity` | Apply perpetuity principles P1-P6 | Planned |
| `tm_auto` | Comprehensive TM automation | Planned |

### Advanced Tactics (Future)

| Tactic | Purpose | Layer |
|--------|---------|-------|
| `modal_search` | Bounded modal proof search | Layer 0 |
| `temporal_search` | Bounded temporal proof search | Layer 0 |
| `counterfactual` | Counterfactual reasoning | Layer 1 |
| `grounding` | Grounding relation reasoning | Layer 1 |

## 2. LEAN 4 Metaprogramming Overview

### Tactic Architecture

LEAN 4 tactics are defined using the `Lean.Elab.Tactic` module:

```lean
import Lean.Elab.Tactic

open Lean Elab Tactic Meta

/-- A simple custom tactic that applies a specific lemma -/
elab "my_tactic" : tactic => do
  -- Get the current goal
  let goal ← getMainGoal
  -- Get the goal's type
  let goalType ← goal.getType

  -- Perform some action
  -- ...

  -- Close the goal or create subgoals
  goal.assign proof
```

### Key Modules

```lean
import Lean.Elab.Tactic      -- Tactic elaboration
import Lean.Meta.Basic       -- Meta-level operations
import Lean.Meta.Tactic.Simp -- Simplification
import Lean.Meta.Tactic.Rewrite -- Rewriting
```

### Metaprogramming Concepts

| Concept | Description |
|---------|-------------|
| `MVarId` | Goal identifier (metavariable) |
| `Expr` | Expression/term representation |
| `TacticM` | Monad for tactic execution |
| `MetaM` | Monad for meta-level operations |
| `getMainGoal` | Get current goal |
| `MVarId.assign` | Assign proof term to goal |
| `mkAppM` | Create function application |
| `mkConst` | Create constant reference |

## 3. Tactic Implementation Patterns

### Pattern 1: Apply Axiom

Apply a specific axiom to the current goal:

```lean
/-- Apply modal axiom MT: □φ → φ -/
elab "modal_t" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Check if goal matches pattern: □_ → _
  match goalType with
  | .app (.app (.const ``Formula.imp _) (.app (.const ``Formula.box _) φ)) ψ =>
    if φ == ψ then
      -- Goal is □φ → φ, apply axiom
      let proof ← mkAppM ``Derivable.axiom #[← mkAppM ``Axiom.modal_t #[φ]]
      goal.assign proof
    else
      throwError "modal_t: goal is not □φ → φ"
  | _ =>
    throwError "modal_t: goal must be an implication □φ → φ"
```

### Pattern 2: Apply Inference Rule

Apply an inference rule that creates subgoals:

```lean
/-- Apply modus ponens, creating subgoals for φ → ψ and φ -/
elab "mp" h1:ident h2:ident : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Get hypothesis expressions
  let h1Expr ← elabTerm h1 none
  let h2Expr ← elabTerm h2 none

  -- Apply modus ponens
  let proof ← mkAppM ``Derivable.modus_ponens #[h1Expr, h2Expr]
  goal.assign proof
```

### Pattern 3: Simplification Tactic

Simplify formulas using simp lemmas:

```lean
/-- Simplify modal formulas -/
elab "modal_simp" : tactic => do
  let goal ← getMainGoal

  -- Add modal simplification lemmas
  let simpLemmas := #[
    ``diamond_neg_box_neg,      -- ◇φ ≡ ¬□¬φ
    ``box_box_eq_box,           -- □□φ ≡ □φ (in S5)
    ``diamond_diamond_eq_diamond -- ◇◇φ ≡ ◇φ (in S5)
  ]

  -- Apply simplification
  let (_, newGoal) ← simpGoal goal (simpLemmas := simpLemmas)

  match newGoal with
  | some g => replaceMainGoal [g]
  | none => pure ()  -- Goal solved
```

### Pattern 4: Proof Search

Bounded proof search:

```lean
/-- Bounded proof search for modal formulas -/
partial def modalSearch (goal : MVarId) (depth : Nat) : TacticM Unit := do
  if depth == 0 then
    throwError "modal_search: depth limit reached"

  let goalType ← goal.getType

  -- Try each strategy in order
  try
    -- Try assumption
    goal.assumption
  catch _ =>
    try
      -- Try applying axiom MT
      let proof ← mkAppM ``Derivable.axiom #[← mkAppM ``Axiom.modal_t #[← inferType goalType]]
      goal.assign proof
    catch _ =>
      try
        -- Try applying axiom M4
        let proof ← mkAppM ``Derivable.axiom #[← mkAppM ``Axiom.modal_4 #[← inferType goalType]]
        goal.assign proof
      catch _ =>
        -- Try modus ponens (creates subgoals)
        let (subgoal1, subgoal2) ← applyMP goal
        modalSearch subgoal1 (depth - 1)
        modalSearch subgoal2 (depth - 1)

elab "modal_search" depth:num : tactic => do
  let goal ← getMainGoal
  modalSearch goal depth.getNat
```

## 4. Syntax Macros

### Defining Custom Syntax

```lean
/-- DSL syntax for modal necessity -/
syntax "□" term : term
macro_rules
  | `(□ $φ) => `(Formula.box $φ)

/-- DSL syntax for possibility -/
syntax "◇" term : term
macro_rules
  | `(◇ $φ) => `(diamond $φ)

/-- DSL syntax for derivability -/
syntax term " ⊢ " term : term
macro_rules
  | `($Γ ⊢ $φ) => `(Derivable $Γ $φ)
```

### Tactic Syntax Macros

```lean
/-- Shorthand for applying axiom and specific axiom constructor -/
macro "apply_axiom" ax:ident : tactic =>
  `(tactic| apply Derivable.axiom; apply $ax)

/-- Combined modal tactic -/
macro "modal_reasoning" : tactic =>
  `(tactic|
    repeat (first
      | apply_axiom Axiom.modal_t
      | apply_axiom Axiom.modal_4
      | apply_axiom Axiom.modal_b
      | apply Derivable.modus_ponens <;> assumption))
```

## 5. Aesop Integration

### Using @[aesop] Attributes

```lean
/-- Mark lemma for automatic use by Aesop -/
@[aesop safe [constructors, cases]]
theorem modal_t_valid (φ : Formula) : valid (φ.box.imp φ) := by
  sorry

/-- Mark as normalization rule -/
@[aesop norm simp]
theorem diamond_def (φ : Formula) : diamond φ = neg (Formula.box (neg φ)) := rfl

/-- Mark as safe forward reasoning -/
@[aesop safe forward]
theorem modal_4_chain (φ : Formula) (h : ⊢ φ.box) : ⊢ φ.box.box := by
  sorry
```

### Custom Aesop Rule Sets

```lean
/-- Create TM-specific rule set -/
declare_aesop_rule_sets [TMLogic]

@[aesop safe [TMLogic]]
theorem perpetuity_1_forward (φ : Formula) (h : ⊢ φ.box) : ⊢ (always φ) := by
  sorry

/-- Use TM rule set in proofs -/
example (P : Formula) : [P.box] ⊢ (always P) := by
  aesop (rule_sets [TMLogic])
```

## 6. Testing Tactics

### Unit Tests for Tactics

```lean
-- Tests/Unit/Automation/TacticsTests.lean

/-- Test modal_t applies correctly -/
example (P : Formula) : ⊢ (P.box.imp P) := by
  modal_t

/-- Test modal_t fails on wrong formula -/
example (P Q : Formula) : ⊢ (P.imp Q) := by
  fail_if_success modal_t  -- Should fail
  sorry

/-- Test modal_reasoning solves simple goal -/
example (P : Formula) : [P.box] ⊢ P := by
  modal_reasoning

/-- Test proof search with depth limit -/
example (P : Formula) : ⊢ (P.box.imp P) := by
  modal_search 3
```

### Performance Tests

```lean
/-- Test tactic performance on complex formula -/
example (P Q R : Formula) :
  ⊢ ((P.box.and Q.box).and R.box).imp (P.and (Q.and R)).box := by
  -- Should complete in reasonable time
  tm_auto

/-- Benchmark: deeply nested modal formula -/
def deeply_nested (n : Nat) : Formula :=
  match n with
  | 0 => Formula.atom "p"
  | n + 1 => Formula.box (deeply_nested n)

-- Test on nested formula (should complete quickly)
#guard (deeply_nested 10).complexity = 11
```

## 7. Documentation Requirements

### Tactic Documentation Format

```lean
/-!
# Modal Reasoning Tactics

This module provides tactics for automated modal reasoning in TM logic.

## Main Tactics

* `modal_t` - Apply axiom MT (□φ → φ)
* `modal_k` - Apply modal K rule
* `modal_simp` - Simplify modal formulas
* `modal_auto` - Comprehensive modal automation

## Usage

```lean
example (P : Formula) : ⊢ (P.box.imp P) := by
  modal_t

example (P Q : Formula) : [P.box, P.imp Q] ⊢ Q.box := by
  modal_auto
```

## Implementation Notes

Tactics use LEAN 4 metaprogramming to analyze goal structure and apply
appropriate axioms and inference rules.
-/

/-- Apply modal axiom MT: □φ → φ

This tactic succeeds when the goal has the form `⊢ □φ → φ` for some formula φ.
It applies the reflexivity axiom of S5 modal logic.

## Example

```lean
example (P : Formula) : ⊢ (P.box.imp P) := by
  modal_t
```

## Errors

* "goal must be an implication □φ → φ" - Goal doesn't match required pattern
-/
elab "modal_t" : tactic => do
  -- implementation
  sorry
```

### Limitations Documentation

Document what the tactic cannot handle:

```lean
/-- Modal proof search with bounded depth.

**Limitations:**
- Does not handle temporal operators (use `temporal_search`)
- May not find proof within depth limit
- Does not backtrack on suboptimal choices

**Completeness:**
Complete for propositional S5 within the depth limit.
-/
elab "modal_search" depth:num : tactic => ...
```

## 8. Best Practices

### Do

- Write tests before implementing tactics
- Document expected goal patterns
- Provide clear error messages
- Use type-safe pattern matching
- Integrate with existing LEAN tactics when possible
- Profile performance on representative examples

### Don't

- Leave tactics partially implemented without `sorry`
- Create tactics that loop infinitely
- Ignore edge cases (empty contexts, atomic formulas)
- Hardcode proof terms (use `mkAppM`)
- Skip documentation

### Error Messages

Provide helpful error messages:

```lean
-- Good
throwError "modal_t: expected goal of form □φ → φ, got {goalType}"

-- Bad
throwError "tactic failed"
```

### Performance Considerations

- Avoid unnecessary recursion
- Use memoization for repeated computations
- Set reasonable depth limits for search
- Profile tactics on large formulas

## References

- [LEAN 4 Metaprogramming Book](https://leanprover-community.github.io/lean4-metaprogramming-book/)
- [Aesop Documentation](https://github.com/leanprover-community/aesop)
- [Mathlib4 Tactics](https://leanprover-community.github.io/mathlib4_docs/)
- [ProofChecker Architecture](../UserGuide/ARCHITECTURE.md)
- [Testing Standards](TESTING_STANDARDS.md)
