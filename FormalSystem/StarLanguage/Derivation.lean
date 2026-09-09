/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Axioms

/-!
# `StarDerivationTree` — TM⋆'s proof system

A constructor-for-constructor mirror of `FormalSystem.PlusLanguage.PlusDerivationTree` over
`StarFormula`, with `StarAxiom` (`StarLanguage/Axioms.lean`) in the `axiom` rule. The mirror is
deliberate, and it is what the whole component is for: it makes TM⋆ and TM⁺ *structurally
comparable*, so that the embedding `StarDerivationTree.ofPlusTree`
(`StarLanguage/Embedding.lean`) is a seven-case structural recursion with one case per rule, and
so that the soundness companion recursion
(`Metalogic/Conservativity/Star/StarSoundness.lean`) transcribes TM⁺'s arm for arm.

## Inference rules (7, matching TM⁺ and TM exactly)

1. `axiom` — a `StarAxiom` instance, gated by `h.minFrameClass ≤ fc`
2. `assumption`
3. `modus_ponens`
4. `necessitation` — `⊢ φ ⟹ ⊢ □φ`, empty context only
5. `temporal_necessitation` — `⊢ φ ⟹ ⊢ Gφ`, empty context only
6. `temporal_duality` — `⊢ φ ⟹ ⊢ swapTemporal φ`, empty context only
7. `weakening`

**There is no register-necessitation rule and no `⊡`-necessitation rule.** Register
necessitation (`⊢ φ ⟹ ⊢ ↑ⁱφ`, `⊢ ↓ⁱφ`) is *sound* — validity quantifies the stored-time vector
universally and both register clauses map a point to a point — but it is not needed by anything
built on this system, and adding it would break the exact seven-rule mirror that `ofPlusTree`
and the soundness recursion rely on. The same applies to the classical hybrid `↓`-binder
hazard, which does not arise here: the hazard is *uniform substitution*, and TM⁺ is already not
substitution-closed (`PlusAxiom.atom_stab`), so no argument anywhere in this component uses it.

## `⊡`-necessitation, and exactly how far it reaches

In TM⁺, `⊢ φ ⟹ ⊢ ⊡φ` is derivable at every formula — `necessitation` to `⊢ □φ`, then MS
(`□φ → ⊡φ`) and modus ponens — which is why `PlusDerivationTree` carries no `⊡` rule of its own.
In TM⋆ the derivation goes through **only at embedded formulas**, and `stabNecessitationOfPlus`
below is stated at exactly that strength. The reason is the `ofBase` design (see
`StarLanguage/Axioms.lean`): MS reaches TM⋆ only as `StarAxiom.ofBase _ (PlusAxiom.box_stab _)`,
whose instances are `□(ofPlus ψ) → ⊡(ofPlus ψ)`. At a register-containing `φ`, `⊢⋆ φ ⟹ ⊢⋆ ⊡φ`
remains **sound** (the `stab` clause restricts the `box` clause's quantifier, so validity
transfers) but is not derivable from this axiom set.

That is not a defect to be repaired by weakening a statement: it is one more instance of the
recorded cost of the `ofBase` embedding, and it is recorded here rather than papered over. A
native `box_stab` schema over `StarFormula` would remove the restriction and would be sound; it
is deliberately not declared, because `StarAxiom`'s constructor list is fixed at one embedding
arm plus the register block.

## Notation

`Γ ⊢⋆[fc] φ` and `⊢⋆[fc] φ`, a fourth token alongside TM's `⊢[fc]`, TM⁻'s `⊢⁻[fc]` and TM⁺'s
`⊢⁺[fc]`, at the same precedence.

## References

* `FormalSystem/PlusLanguage/Derivation.lean` — the TM⁺ counterpart being mirrored
* `FormalSystem/StarLanguage/Axioms.lean` — `StarAxiom`, `StarAxiom.minFrameClass`

## Tags

proof-system · star-language · derivation-tree · store-recall
-/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.ProofSystem (FrameClass)
open FormalSystem.PlusLanguage

/--
Derivation tree for TM⋆, parameterized by frame class. `Type`-valued, like its TM⁺ and TM
counterparts, so that the soundness recursion can match on it and `height` is computable.

Paper: — (formalization-native; the manuscript supplies no proof system for `\BL^\star`)
-/
inductive StarDerivationTree (fc : FrameClass) : StarContext → StarFormula → Type where
  /-- Axiom rule, gated by `h.minFrameClass ≤ fc`. -/
  | axiom (Γ : StarContext) (φ : StarFormula) (h : StarAxiom φ) (h_fc : h.minFrameClass ≤ fc)
      : StarDerivationTree fc Γ φ
  /-- Assumption rule: formulas in the context are derivable. -/
  | assumption (Γ : StarContext) (φ : StarFormula) (h : φ ∈ Γ) : StarDerivationTree fc Γ φ
  /-- Modus ponens. -/
  | modus_ponens (Γ : StarContext) (φ ψ : StarFormula)
      (d1 : StarDerivationTree fc Γ (φ.imp ψ))
      (d2 : StarDerivationTree fc Γ φ) : StarDerivationTree fc Γ ψ
  /-- Necessitation: from `⊢ φ`, conclude `⊢ □φ`. Theorems only. -/
  | necessitation (φ : StarFormula)
      (d : StarDerivationTree fc [] φ) : StarDerivationTree fc [] (StarFormula.box φ)
  /-- Temporal necessitation: from `⊢ φ`, conclude `⊢ Gφ`. Theorems only. -/
  | temporal_necessitation (φ : StarFormula)
      (d : StarDerivationTree fc [] φ) : StarDerivationTree fc [] (StarFormula.allFuture φ)
  /-- Temporal duality: from `⊢ φ`, conclude `⊢ swapTemporal φ`. Theorems only. -/
  | temporal_duality (φ : StarFormula)
      (d : StarDerivationTree fc [] φ) : StarDerivationTree fc [] φ.swapTemporal
  /-- Weakening: from `Γ ⊢ φ` and `Γ ⊆ Δ`, conclude `Δ ⊢ φ`. -/
  | weakening (Γ Δ : StarContext) (φ : StarFormula)
      (d : StarDerivationTree fc Γ φ)
      (h : Γ ⊆ Δ) : StarDerivationTree fc Δ φ

namespace StarDerivationTree

/-- Lift a derivation from `fc₁` to `fc₂` when `fc₁ ≤ fc₂`. Mirrors
`PlusDerivationTree.lift`. -/
def lift {fc₁ fc₂ : FrameClass} (h_le : fc₁ ≤ fc₂)
    {Γ : StarContext} {φ : StarFormula} : StarDerivationTree fc₁ Γ φ → StarDerivationTree fc₂ Γ φ
  | .axiom Γ φ h h_fc => .axiom Γ φ h (le_trans h_fc h_le)
  | .assumption Γ φ h => .assumption Γ φ h
  | .modus_ponens Γ φ ψ d1 d2 => .modus_ponens Γ φ ψ (d1.lift h_le) (d2.lift h_le)
  | .necessitation φ d => .necessitation φ (d.lift h_le)
  | .temporal_necessitation φ d => .temporal_necessitation φ (d.lift h_le)
  | .temporal_duality φ d => .temporal_duality φ (d.lift h_le)
  | .weakening Γ Δ φ d h => .weakening Γ Δ φ (d.lift h_le) h

/-- Height of a derivation, mirroring `PlusDerivationTree.height`. -/
def height {fc : FrameClass} {Γ : StarContext} {φ : StarFormula} :
    StarDerivationTree fc Γ φ → Nat
  | .axiom _ _ _ _ => 0
  | .assumption _ _ _ => 0
  | .modus_ponens _ _ _ d1 d2 => 1 + max d1.height d2.height
  | .necessitation _ d => 1 + d.height
  | .temporal_necessitation _ d => 1 + d.height
  | .temporal_duality _ d => 1 + d.height
  | .weakening _ _ _ d _ => 1 + d.height

/-- Re-target a derivation whose context is a subset of the empty context. Mirror of
`PlusDerivationTree.ofWeakeningNil`. -/
def ofWeakeningNil {fc : FrameClass} {Γ' : StarContext} {φ : StarFormula}
    (d : StarDerivationTree fc Γ' φ) (h_sub : Γ' ⊆ ([] : StarContext)) :
    StarDerivationTree fc [] φ :=
  (List.eq_nil_of_subset_nil h_sub) ▸ d

/-- `ofWeakeningNil` preserves height exactly. -/
@[simp] theorem height_ofWeakeningNil {fc : FrameClass} {Γ' : StarContext} {φ : StarFormula}
    (d : StarDerivationTree fc Γ' φ) (h_sub : Γ' ⊆ ([] : StarContext)) :
    (d.ofWeakeningNil h_sub).height = d.height := by
  have h_eq : Γ' = [] := List.eq_nil_of_subset_nil h_sub
  subst h_eq
  rfl

/-- Transporting to the empty context is strictly cheaper than the `weakening` node. -/
theorem height_ofWeakeningNil_lt {fc : FrameClass} {Γ' : StarContext} {φ : StarFormula}
    (d : StarDerivationTree fc Γ' φ) (h_sub : Γ' ⊆ ([] : StarContext)) :
    (d.ofWeakeningNil h_sub).height <
      (StarDerivationTree.weakening Γ' ([] : StarContext) φ d h_sub).height := by
  simp only [StarDerivationTree.height_ofWeakeningNil, StarDerivationTree.height]
  omega

/-- Modus ponens height is strictly greater than the left subderivation. -/
theorem mp_height_gt_left {fc : FrameClass} {Γ : StarContext} {φ ψ : StarFormula}
    (d1 : StarDerivationTree fc Γ (φ.imp ψ)) (d2 : StarDerivationTree fc Γ φ) :
    d1.height < (modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

/-- Modus ponens height is strictly greater than the right subderivation. -/
theorem mp_height_gt_right {fc : FrameClass} {Γ : StarContext} {φ ψ : StarFormula}
    (d1 : StarDerivationTree fc Γ (φ.imp ψ)) (d2 : StarDerivationTree fc Γ φ) :
    d2.height < (modus_ponens Γ φ ψ d1 d2).height := by
  simp [height]
  omega

end StarDerivationTree

/-- Prop-valued derivability in TM⋆, mirroring `PlusDerivable`. -/
def StarDerivable (fc : FrameClass) (Γ : StarContext) (φ : StarFormula) : Prop :=
  Nonempty (StarDerivationTree fc Γ φ)

/-- Derivability in TM⋆ from context `Γ` at frame class `fc`. -/
notation:50 Γ " ⊢⋆[" fc "] " φ => StarDerivationTree fc Γ φ

/-- Theoremhood in TM⋆ at frame class `fc`. -/
notation:50 "⊢⋆[" fc "] " φ => StarDerivationTree fc [] φ

/-- `StarDerivable` is monotone in the frame class. -/
theorem StarDerivable.mono {fc₁ fc₂ : FrameClass} (h : fc₁ ≤ fc₂) {Γ : StarContext}
    {φ : StarFormula} (hd : StarDerivable fc₁ Γ φ) : StarDerivable fc₂ Γ φ :=
  hd.elim fun d => ⟨d.lift h⟩

/-! ## The derived `⊡`-necessitation rule, at embedded formulas -/

/-- **`⊡`-necessitation, at `ofPlus` instances**: `⊢⋆ ofPlus ψ ⟹ ⊢⋆ ⊡(ofPlus ψ)`, by
`necessitation` to `⊢⋆ □(ofPlus ψ)` and then MS through `StarAxiom.ofBase`.

The restriction to embedded formulas is exactly the reach of `ofBase`, which supplies
`PlusAxiom.box_stab` only at `ofPlus` instances; see this module's docstring for why the general
rule is sound but not derivable here, and why it is recorded rather than assumed. -/
def stabNecessitationOfPlus {fc : FrameClass} {ψ : PlusFormula}
    (d : ⊢⋆[fc] (ofPlus ψ)) : ⊢⋆[fc] StarFormula.stab (ofPlus ψ) :=
  .modus_ponens [] _ _
    (.axiom [] _ (StarAxiom.ofBase _ (PlusAxiom.box_stab ψ)) (FrameClass.base_le fc))
    (.necessitation _ d)

/-! ### Smoke tests -/

/-- A register schema is a theorem at every class: `↑ⁱ□φ ↔ □↑ⁱφ`. -/
example (fc : FrameClass) (i : ℕ) (φ : StarFormula) :
    ⊢⋆[fc] (StarFormula.timeStore i (.box φ)).iff (StarFormula.box (.timeStore i φ)) :=
  .axiom [] _ (StarAxiom.store_box i φ) (FrameClass.base_le fc)

/-- MF reaches TM⋆ through `ofBase`, at an embedded formula — and only there. -/
example (fc : FrameClass) (ψ : PlusFormula) :
    ⊢⋆[fc] ofPlus ((PlusFormula.box ψ).imp (PlusFormula.box (PlusFormula.allFuture ψ))) :=
  .axiom [] _ (StarAxiom.ofBase _ (PlusAxiom.modal_future ψ)) (FrameClass.base_le fc)

/-- Temporal duality applies to a register formula: the dual of forward rigidity is backward
rigidity, and it is reached by the rule rather than by a second axiom. -/
example (fc : FrameClass) (i : ℕ) (φ : StarFormula) :
    ⊢⋆[fc] ((StarFormula.timeRecall i φ).imp
      (StarFormula.allFuture (.timeRecall i φ))).swapTemporal :=
  .temporal_duality _ (.axiom [] _ (StarAxiom.recall_rigid_future i φ) (FrameClass.base_le fc))

end FormalSystem.StarLanguage
