import ProofChecker.Theorems.Perpetuity

/-!
# Perpetuity Principles Tests

Tests for the P1-P6 perpetuity principles that connect modal necessity (□)
with temporal operators (always/sometimes).

## Test Coverage

- P1: `□φ → always φ` (necessary implies always)
- P2: `sometimes φ → ◇φ` (sometimes implies possible)
- P3: `□φ → □always φ` (necessity of perpetuity)
- P4: `◇sometimes φ → ◇φ` (possibility of occurrence)
- P5: `◇sometimes φ → always ◇φ` (persistent possibility)
- P6: `sometimes □φ → □always φ` (occurrent necessity perpetual)
-/

namespace ProofCheckerTest.Theorems.PerpetuityTest

open ProofChecker.Syntax
open ProofChecker.ProofSystem
open ProofChecker.Theorems.Perpetuity

/-!
## P1 Tests: □φ → always φ (necessary implies always)
-/

/-- Test P1 type signature: □φ → △φ (always = future) -/
example (φ : Formula) : ⊢ φ.box.imp φ.always := perpetuity_1 φ

/-- Test P1 with atomic formula -/
example : ⊢ (Formula.atom "p").box.imp (Formula.atom "p").always := perpetuity_1 _

/-- Test P1 using triangle notation -/
example (φ : Formula) : ⊢ φ.box.imp (△φ) := perpetuity_1 φ

/-!
## P2 Tests: sometimes φ → ◇φ (sometimes implies possible)
-/

/-- Test P2 type signature: ▽φ → ◇φ -/
example (φ : Formula) : ⊢ φ.sometimes.imp φ.diamond := perpetuity_2 φ

/-- Test P2 with atomic formula -/
example : ⊢ (Formula.atom "p").sometimes.imp (Formula.atom "p").diamond := perpetuity_2 _

/-- Test P2 using triangle notation -/
example (φ : Formula) : ⊢ (▽φ).imp φ.diamond := perpetuity_2 φ

/-!
## P3 Tests: □φ → □always φ (necessity of perpetuity)
-/

/-- Test P3 type signature: □φ → □△φ -/
example (φ : Formula) : ⊢ φ.box.imp (φ.always.box) := perpetuity_3 φ

/-- Test P3 with atomic formula -/
example : ⊢ (Formula.atom "p").box.imp (Formula.atom "p").always.box := perpetuity_3 _

/-!
## P4 Tests: ◇sometimes φ → ◇φ (possibility of occurrence)
-/

/-- Test P4 type signature: ◇▽φ → ◇φ -/
example (φ : Formula) : ⊢ φ.sometimes.diamond.imp φ.diamond := perpetuity_4 φ

/-- Test P4 with atomic formula -/
example : ⊢ (Formula.atom "p").sometimes.diamond.imp (Formula.atom "p").diamond := perpetuity_4 _

/-!
## P5 Tests: ◇sometimes φ → always ◇φ (persistent possibility)
-/

/-- Test P5 type signature: ◇▽φ → △◇φ -/
example (φ : Formula) : ⊢ φ.sometimes.diamond.imp φ.diamond.always := perpetuity_5 φ

/-- Test P5 with atomic formula -/
example : ⊢ (Formula.atom "p").sometimes.diamond.imp (Formula.atom "p").diamond.always := perpetuity_5 _

/-!
## P6 Tests: sometimes □φ → □always φ (occurrent necessity perpetual)
-/

/-- Test P6 type signature: ▽□φ → □△φ -/
example (φ : Formula) : ⊢ φ.box.sometimes.imp φ.always.box := perpetuity_6 φ

/-- Test P6 with atomic formula -/
example : ⊢ (Formula.atom "p").box.sometimes.imp (Formula.atom "p").always.box := perpetuity_6 _

/-!
## Triangle Notation Tests
-/

/-- Test: P3 with triangle notation - □φ → □△φ -/
example (φ : Formula) : ⊢ φ.box.imp (△φ).box := perpetuity_3 φ

/-- Test: P4 with triangle notation - ◇▽φ → ◇φ -/
example (φ : Formula) : ⊢ (▽φ).diamond.imp φ.diamond := perpetuity_4 φ

/-- Test: P5 with triangle notation - ◇▽φ → △◇φ -/
example (φ : Formula) : ⊢ (▽φ).diamond.imp (△(φ.diamond)) := perpetuity_5 φ

/-- Test: P6 with triangle notation - ▽□φ → □△φ -/
example (φ : Formula) : ⊢ (▽(φ.box)).imp (△φ).box := perpetuity_6 φ

/-- Test: Mixed notation - box with triangle -/
example (p : Formula) : ⊢ p.box.imp (△p).box := perpetuity_3 p

/-- Test: Mixed notation - diamond with triangle -/
example (p : Formula) : ⊢ (▽p).diamond.imp (△(p.diamond)) := perpetuity_5 p

/-!
## Integration Tests
-/

/-- Test: P1 combined with modal T gives reflexivity path -/
example (φ : Formula) : ⊢ φ.box.imp φ := by
  -- □φ → φ is Modal T axiom, but we can also derive via P1 + other axioms
  apply Derivable.axiom
  exact Axiom.modal_t φ

/-- Test: P3 is derivable from MF axiom (□φ → □Fφ, and always = future) -/
example (φ : Formula) : ⊢ φ.box.imp φ.always.box := perpetuity_3 φ

/-- Test: Triangle notation equivalence - △ = always -/
example (p : Formula) : △p = p.always := rfl

/-- Test: Triangle notation equivalence - ▽ = sometimes -/
example (p : Formula) : ▽p = p.sometimes := rfl

end ProofCheckerTest.Theorems.PerpetuityTest
