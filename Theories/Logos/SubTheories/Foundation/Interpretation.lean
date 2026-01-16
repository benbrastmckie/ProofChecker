import Logos.SubTheories.Foundation.Frame
import Logos.SubTheories.Foundation.Proposition
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Interpretation Functions for Constitutive Models

This module defines interpretation functions that assign meanings to
non-logical vocabulary in constitutive models.

## Paper Specification Reference

**Interpretation (recursive-semantics.md)**:
The interpretation function I assigns:
- n-place function symbols f → I(f) : Sⁿ → S (0-place = individual constants)
- n-place predicates F → ordered pairs ⟨v_F, f_F⟩ where:
  - v_F : verifier function type Sⁿ → S
  - f_F : falsifier function type Sⁿ → S
- Sentence letters (0-place predicates) p → ⟨verifier type, falsifier type⟩

## Main Definitions

- `Interpretation`: Structure assigning meanings to non-logical vocabulary
- `VarAssignment`: Variable assignment mapping variables to states

## Implementation Notes

We use `Fin n → S` for n-ary functions over states, which is equivalent
to `Sⁿ → S` in the paper notation.
-/

namespace Logos.SubTheories.Foundation

variable {F : ConstitutiveFrame}

/--
Variable assignment: a function mapping variable names to states.

**Paper notation**: σ : Var → S
-/
def VarAssignment (F : ConstitutiveFrame) := String → F.State

namespace VarAssignment

/--
Update a variable assignment at a single variable.

**Paper notation**: σ[v/x] maps x to v and agrees with σ elsewhere.
-/
def update (σ : VarAssignment F) (x : String) (v : F.State) : VarAssignment F :=
  fun y => if y = x then v else σ y

/--
Updating at x and then looking up x gives the new value.
-/
@[simp]
theorem update_same (σ : VarAssignment F) (x : String) (v : F.State) :
    (σ.update x v) x = v := by
  simp [update]

/--
Updating at x doesn't affect other variables.
-/
@[simp]
theorem update_other (σ : VarAssignment F) (x y : String) (v : F.State) (h : y ≠ x) :
    (σ.update x v) y = σ y := by
  simp [update, h]

end VarAssignment

/--
Predicate interpretation: zero or more verifier and falsifier functions.

For n-ary predicates, we have:
- verifierType: (Fin n → F.State) → F.State
- verifierCount: Nat (number of verifier functions)  
- verifierFns: Fin verifierCount → verifierType (indexed access)

This represents "zero or more functions" in pure type theory without using Set.
For sentence letters (0-ary), these reduce to state-based propositions.
-/
structure PredicateInterp (F : ConstitutiveFrame) (n : Nat) where
  /-- Number of verifier functions -/
  verifierCount : Nat
  /-- Verifier functions indexed by their count -/
  verifierFns : Fin verifierCount → ((Fin n → F.State) → F.State)
  /-- Number of falsifier functions -/
  falsifierCount : Nat
  /-- Falsifier functions indexed by their count -/
  falsifierFns : Fin falsifierCount → ((Fin n → F.State) → F.State)

namespace PredicateInterp

/--
Sentence letter interpretation (0-ary predicate).
Verifier and falsifier function types reduce to constant function types,
which we can identify with states.
-/
def sentenceLetter (F : ConstitutiveFrame) (verifiers falsifiers : List F.State) :
    PredicateInterp F 0 where
  verifierCount := verifiers.length
  verifierFns := fun i => fun _ => verifiers.get i
  falsifierCount := falsifiers.length
  falsifierFns := fun i => fun _ => falsifiers.get i

/--
Convert to bilateral proposition for sentence letters.
-/
def toBilateralProp (p : PredicateInterp F 0) : BilateralProp F.State where
  verifiers := { s | ∃ i : Fin p.verifierCount, (p.verifierFns i) Fin.elim0 = s }
  falsifiers := { s | ∃ i : Fin p.falsifierCount, (p.falsifierFns i) Fin.elim0 = s }

end PredicateInterp

/--
Function symbol interpretation: maps n states to a state.

For individual constants (0-ary function symbols), this is just a state.
-/
def FunctionInterp (F : ConstitutiveFrame) (n : Nat) := (Fin n → F.State) → F.State

namespace FunctionInterp

/--
Individual constant interpretation (0-ary function symbol).
-/
def constant (s : F.State) : FunctionInterp F 0 :=
  fun _ => s

end FunctionInterp

/--
Full interpretation for a constitutive model.

Assigns meanings to function symbols and predicates of each arity.
-/
structure Interpretation (F : ConstitutiveFrame) where
  /-- Interpretation of function symbols by arity -/
  functionSymbol : String → (n : Nat) → FunctionInterp F n
  /-- Interpretation of predicates by arity -/
  predicate : String → (n : Nat) → PredicateInterp F n

namespace Interpretation

/--
Get the interpretation of an individual constant (0-ary function symbol).
-/
def getConstant (I : Interpretation F) (c : String) : F.State :=
  I.functionSymbol c 0 Fin.elim0

/--
Get the interpretation of a sentence letter (0-ary predicate).
-/
def getSentenceLetter (I : Interpretation F) (p : String) : BilateralProp F.State :=
  (I.predicate p 0).toBilateralProp

end Interpretation

/--
Constitutive Model: a frame with an interpretation.

**Paper definition**: M = ⟨S, ⊑, I⟩ where ⟨S, ⊑⟩ is a constitutive frame
and I is an interpretation function.
-/
structure ConstitutiveModel where
  /-- The underlying constitutive frame -/
  frame : ConstitutiveFrame
  /-- Interpretation of non-logical vocabulary -/
  interp : Interpretation frame

namespace ConstitutiveModel

/--
Get the state type from a model.
-/
def State (M : ConstitutiveModel) : Type := M.frame.State

/--
Get the null state of a model.
-/
def null (M : ConstitutiveModel) : M.frame.State := M.frame.null

/--
Get the full state of a model.
-/
def full (M : ConstitutiveModel) : M.frame.State := M.frame.full

/--
Get fusion operation from a model.
-/
def fusion (M : ConstitutiveModel) (s t : M.frame.State) : M.frame.State :=
  M.frame.fusion s t

end ConstitutiveModel

end Logos.SubTheories.Foundation
