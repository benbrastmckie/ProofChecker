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
Predicate interpretation: a bilateral proposition for each arity.

For n-ary predicates, verifier and falsifier "functions" are actually
sets of functions Sⁿ → S. For sentence letters (0-ary), these reduce to
sets of states.

The verifier and falsifier function sets must satisfy two mereological constraints:

1. **Fusion of inputs ⊑ output**: For any function f in the set and arguments args,
   the fusion of all argument states must be a part of the output state:
   Fusion(args) ⊑ f(args)

2. **Closure under function fusion**: If f, g are in the set, then their pointwise
   fusion ⨆{f}{g} is also in the set.

These constraints ensure that the semantics respects the mereological structure of states.
-/
structure PredicateInterp (F : ConstitutiveFrame) (n : Nat) where
  /-- Verifier functions: each f ∈ verifierFns satisfies f(a₁,...,aₙ) verifies F(a₁,...,aₙ) -/
  verifierFns : Set ((Fin n → F.State) → F.State)
  /-- Falsifier functions: each f ∈ falsifierFns satisfies f(a₁,...,aₙ) falsifies F(a₁,...,aₙ) -/
  falsifierFns : Set ((Fin n → F.State) → F.State)
  /-- Verifier functions respect mereological constraint: Fusion(args) ⊑ f(args) -/
  verifierFns_input_fusion : ∀ (f : (Fin n → F.State) → F.State), f ∈ verifierFns →
    ∀ (args : Fin n → F.State), F.parthood (F.argsFusion n args) (f args)
  /-- Falsifier functions respect mereological constraint: Fusion(args) ⊑ f(args) -/
  falsifierFns_input_fusion : ∀ (f : (Fin n → F.State) → F.State), f ∈ falsifierFns →
    ∀ (args : Fin n → F.State), F.parthood (F.argsFusion n args) (f args)
  /-- Verifier functions closed under function fusion -/
  verifierFns_fusion_closed : ∀ (f g : (Fin n → F.State) → F.State), f ∈ verifierFns → g ∈ verifierFns → F.functionFusion f g ∈ verifierFns
  /-- Falsifier functions closed under function fusion -/
  falsifierFns_fusion_closed : ∀ (f g : (Fin n → F.State) → F.State), f ∈ falsifierFns → g ∈ falsifierFns → F.functionFusion f g ∈ falsifierFns

namespace PredicateInterp

/--
Sentence letter interpretation (0-ary predicate) with closure requirements.

For sentence letters, we require that the verifier and falsifier state sets
are closed under fusion, which ensures closure under function fusion for
the corresponding constant functions.
-/
def sentenceLetter (F : ConstitutiveFrame)
    (verifiers falsifiers : Set F.State)
    (verifiers_fusion_closed : ∀ (v w : F.State), v ∈ verifiers → w ∈ verifiers → F.fusion v w ∈ verifiers)
    (falsifiers_fusion_closed : ∀ (v w : F.State), v ∈ falsifiers → w ∈ falsifiers → F.fusion v w ∈ falsifiers) :
    PredicateInterp F 0 where
  verifierFns := { f | f (Fin.elim0) ∈ verifiers }
  falsifierFns := { f | f (Fin.elim0) ∈ falsifiers }
  verifierFns_input_fusion := by
    intro f hf args
    -- For n=0, Fin 0 is empty, so ⨆ i : Fin 0, args i = ⊥
    -- We need to prove: ⊥ ⊑ f args, which is always true
    show F.parthood (F.argsFusion 0 args) (f args)
    unfold ConstitutiveFrame.argsFusion ConstitutiveFrame.parthood
    simp
  falsifierFns_input_fusion := by
    intro f hf args
    -- Same reasoning as for verifiers
    show F.parthood (F.argsFusion 0 args) (f args)
    unfold ConstitutiveFrame.argsFusion ConstitutiveFrame.parthood
    simp
  verifierFns_fusion_closed := by
    intro f g hf hg
    -- If f and g are constant functions in verifierFns, their fusion is also constant
    -- with value equal to the fusion of their values
    have h_val : (F.functionFusion f g) Fin.elim0 = F.fusion (f Fin.elim0) (g Fin.elim0) := by
      simp only [ConstitutiveFrame.functionFusion]
    -- Since f, g ∈ verifierFns, their values are in verifiers
    have h_f_val : (f Fin.elim0) ∈ verifiers := hf
    have h_g_val : (g Fin.elim0) ∈ verifiers := hg
    -- By closure of verifiers under fusion, the fused value is in verifiers
    exact verifiers_fusion_closed (f Fin.elim0) (g Fin.elim0) h_f_val h_g_val
  falsifierFns_fusion_closed := by
    intro f g hf hg
    have h_val : (F.functionFusion f g) Fin.elim0 = F.fusion (f Fin.elim0) (g Fin.elim0) := by
      simp only [ConstitutiveFrame.functionFusion]
    have h_f_val : (f Fin.elim0) ∈ falsifiers := hf
    have h_g_val : (g Fin.elim0) ∈ falsifiers := hg
    exact falsifiers_fusion_closed (f Fin.elim0) (g Fin.elim0) h_f_val h_g_val

/--
Convert to bilateral proposition for sentence letters.
-/
def toBilateralProp (p : PredicateInterp F 0) : BilateralProp F.State where
  verifiers := { s | ∃ (f : (Fin 0 → F.State) → F.State), f ∈ p.verifierFns ∧ f Fin.elim0 = s }
  falsifiers := { s | ∃ (f : (Fin 0 → F.State) → F.State), f ∈ p.falsifierFns ∧ f Fin.elim0 = s }

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
