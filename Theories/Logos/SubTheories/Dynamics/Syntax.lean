import Logos.SubTheories.Foundation.Syntax

/-!
# Core Formula Syntax

This module defines the formula syntax for the Dynamics Foundation layer.
These formulas are evaluated relative to world-histories and times.

## Paper Specification Reference

**Dynamics Foundation Syntax (recursive-semantics.md)**:
The Dynamics Foundation interprets these additional syntactic primitives:
- Modal operators: □ (necessity), ◇ (possibility)
- Temporal operators: H (always past), G (always future), P (some past), F (some future)
- Extended temporal operators: ◁ (since), ▷ (until)
- Counterfactual conditional: □→ (would-counterfactual)
- Causal operator: ○→ (causation)
- Store/recall operators: ↑ⁱ (store), ↓ⁱ (recall)
- Universal quantification: ∀x.A

## Main Definitions

- `Formula`: Full formula type with all Dynamics Foundation operators
- Derived operators: ◇, P, F, ◇→, ○→, always (△), sometimes (▽)

## Implementation Notes

Formulas embed ConstitutiveFormula from the Foundation layer and add
the modal, temporal, counterfactual, and indexed reference operators.
-/

namespace Logos.SubTheories.Dynamics

open Logos.SubTheories.Foundation

/--
Core formula syntax.

Formulas in the Explanatory Extension layer. These extend Constitutive Foundation
formulas with modal, temporal, counterfactual, and indexed operators.
-/
inductive Formula where
  /-- Embed a constitutive formula -/
  | cfml : ConstitutiveFormula → Formula
  /-- Top (⊤, verum) -/
  | top : Formula
  /-- Bottom (⊥, falsum) -/
  | bot : Formula
  /-- Negation: ¬A -/
  | neg : Formula → Formula
  /-- Conjunction: A ∧ B -/
  | conj : Formula → Formula → Formula
  /-- Disjunction: A ∨ B -/
  | disj : Formula → Formula → Formula
  /-- Necessity: □A (all world-histories at current time satisfy A) -/
  | box : Formula → Formula
  /-- Possibility: ◇A (some world-history at current time satisfies A) -/
  | diamond : Formula → Formula
  /-- Always past: HA (A holds at all past times) -/
  | all_past : Formula → Formula
  /-- Always future: GA (A holds at all future times) -/
  | all_future : Formula → Formula
  /-- Some past: PA (A holds at some past time) -/
  | some_past : Formula → Formula
  /-- Some future: FA (A holds at some future time) -/
  | some_future : Formula → Formula
  /-- Since: A ◁ B (A has held since B last held) -/
  | since : Formula → Formula → Formula
  /-- Until: A ▷ B (A will hold until B holds) -/
  | untl : Formula → Formula → Formula
  /-- Counterfactual: A □→ B (if A were the case, B would be the case) -/
  | counterfactual : Formula → Formula → Formula
  /-- Causation: A ○→ B (A causes B)

      This operator is PRIMITIVE (like the counterfactual conditional □→).

      AWAITING IMPLEMENTATION: The correct semantics from "Counterfactual Worlds"
      (Brast-McKie 2025) line 626 requires context parameters and expected evolutions.
      See Task 394 for research on porting the paper semantics. -/
  | causal : Formula → Formula → Formula
  /-- Store: ↑ⁱA (store current time at index i, then evaluate A) -/
  | store : Nat → Formula → Formula
  /-- Recall: ↓ⁱA (recall time from index i, evaluate A at that time) -/
  | rcall : Nat → Formula → Formula
  /-- Universal quantification: ∀x.A -/
  | all : String → Formula → Formula
  /-- Lambda application: (λx.A)(t) -/
  | lambdaApp : String → Formula → Term → Formula
  deriving Repr

namespace Formula

/-! ### Derived Operators -/

/--
Material implication: A → B := ¬A ∨ B
-/
def imp (φ ψ : Formula) : Formula := disj (neg φ) ψ

/--
Biconditional: A ↔ B := (A → B) ∧ (B → A)
-/
def iff (φ ψ : Formula) : Formula := conj (imp φ ψ) (imp ψ φ)

/--
Might-counterfactual: A ◇→ B := ¬(A □→ ¬B)
"If A were the case, B might be the case"
-/
def might_counterfactual (φ ψ : Formula) : Formula :=
  neg (counterfactual φ (neg ψ))

/--
Always: △A := HA ∧ A ∧ GA
"A has always been and will always be the case"
-/
def always (φ : Formula) : Formula :=
  conj (conj (all_past φ) φ) (all_future φ)

/--
Sometimes: ▽A := PA ∨ A ∨ FA
"A was, is, or will be the case"
-/
def sometimes (φ : Formula) : Formula :=
  disj (disj (some_past φ) φ) (some_future φ)

/--
Existential quantification: ∃x.A := ¬∀x.¬A
-/
def exist (x : String) (φ : Formula) : Formula :=
  neg (all x (neg φ))

/-! ### Embedding Constitutive Formulas -/

/--
Embed a sentence letter from the constitutive foundation.
-/
def atom (p : String) : Formula := cfml (ConstitutiveFormula.atom p)

/--
Embed a predicate application from the constitutive foundation.
-/
def pred (P : String) (ts : List Term) : Formula := cfml (ConstitutiveFormula.pred P ts)

/--
Embed propositional identity from the constitutive foundation.
-/
def ident (φ ψ : ConstitutiveFormula) : Formula := cfml (ConstitutiveFormula.ident φ ψ)

/-! ### Formula Complexity -/

/--
Structural complexity of a formula.
-/
def complexity : Formula → Nat
  | cfml c => c.complexity
  | top => 1
  | bot => 1
  | neg φ => 1 + φ.complexity
  | conj φ ψ => 1 + φ.complexity + ψ.complexity
  | disj φ ψ => 1 + φ.complexity + ψ.complexity
  | box φ => 1 + φ.complexity
  | diamond φ => 1 + φ.complexity
  | all_past φ => 1 + φ.complexity
  | all_future φ => 1 + φ.complexity
  | some_past φ => 1 + φ.complexity
  | some_future φ => 1 + φ.complexity
  | since φ ψ => 1 + φ.complexity + ψ.complexity
  | untl φ ψ => 1 + φ.complexity + ψ.complexity
  | counterfactual φ ψ => 1 + φ.complexity + ψ.complexity
  | causal φ ψ => 1 + φ.complexity + ψ.complexity
  | store _ φ => 1 + φ.complexity
  | rcall _ φ => 1 + φ.complexity
  | all _ φ => 1 + φ.complexity
  | lambdaApp _ φ _ => 1 + φ.complexity

/-! ### Notation -/

section Notation

/-- Notation for negation -/
prefix:80 "~ᶜ" => Formula.neg

/-- Notation for conjunction -/
infixl:65 " ⋀ᶜ " => Formula.conj

/-- Notation for disjunction -/
infixl:60 " ⋁ᶜ " => Formula.disj

/-- Notation for implication -/
infixr:55 " →ᶜ " => Formula.imp

/-- Notation for necessity -/
prefix:80 "□" => Formula.box

/-- Notation for possibility -/
prefix:80 "◇" => Formula.diamond

/-- Notation for counterfactual -/
infixr:50 " □→ " => Formula.counterfactual

/-- Notation for might-counterfactual -/
infixr:50 " ◇→ " => Formula.might_counterfactual

/-- Notation for causation -/
infixr:50 " ○→ " => Formula.causal

/-- Notation for always past -/
prefix:80 "𝐇" => Formula.all_past

/-- Notation for always future -/
prefix:80 "𝐆" => Formula.all_future

/-- Notation for some past -/
prefix:80 "𝐏" => Formula.some_past

/-- Notation for some future -/
prefix:80 "𝐅" => Formula.some_future

/-- Notation for since -/
infixl:55 " ◁ " => Formula.since

/-- Notation for until -/
infixl:55 " ▷ " => Formula.untl

/-- Notation for always -/
prefix:80 "△" => Formula.always

/-- Notation for sometimes -/
prefix:80 "▽" => Formula.sometimes

end Notation

end Formula

end Logos.SubTheories.Dynamics
