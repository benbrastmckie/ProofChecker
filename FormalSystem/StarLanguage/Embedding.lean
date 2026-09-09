/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Derivation
import FormalSystem.PlusLanguage.Derivation

/-!
# Every TM⁺ theorem is a TM⋆ theorem at its embedded formula

The backward half of the L⁺ ⊂ L⋆ conservativity pair:

```
TM⁺ ⊢⁺[fc] φ  ⟹  TM⋆ ⊢⋆[fc] ofPlus φ,   at every frame class and every context.
```

Unlike the base-language bridge (`Metalogic/Conservativity/Backward.lean`) no axiom-discharge
table is needed, and unlike `PlusAxiom.ofTM` no 45-arm schema translation is needed either:
`StarAxiom.ofBase` *is* the axiom case, in one line. That is the whole return on the `ofBase`
design — the price paid there (TM⋆'s inherited schemata reach only `ofPlus` instances) is exactly
the price that makes this direction free, because the embedding never needs a TM⁺ schema anywhere
but at an `ofPlus` instance.

Six of the seven cases are structural. The seventh, `temporal_duality`, transports along
`ofPlus_swapTemporal` (`StarLanguage/Formula.lean`) — the one commutation in the family that is
an induction rather than a `rfl`.

## Main Results

- `StarAxiom.minFrameClass_ofBase` — the embedding preserves the minimum frame class
- `StarDerivationTree.ofPlusTree` — the seven-case structural recursion on derivations
- `starDerivable_of_plusDerivable` — its `Prop`-level form
- `starDerivable_of_derivable` — composed with `plusDerivable_of_derivable`, the L ⊂ L⋆
  backward direction, and the backward half of `starDerivable_ofFormula_iff`
  (`Metalogic/Conservativity/Star/Forward.lean`)

## The forward direction is elsewhere, and is not symmetric

`TM⋆ ⊢⋆ ofPlus φ ⟹ TM⁺ ⊢⁺ φ` is **not** proved here and is not proved by any syntactic route:
register erasure is refuted as a translation (`Semantics/StarNonValidities.lean`,
`storeG_recall_valid` with `refute_erasure`). It is treated semantically, and only conditionally,
in `Metalogic/Conservativity/Star/Forward.lean`. The forward direction over the *base* language
`TM⋆ ⊢⋆ ofPlus (ofFormula φ) ⟹ TM ⊢ φ` is unconditional, because TM has completeness engines and
TM⁺ does not.

## References

* `FormalSystem/PlusLanguage/Derivation.lean` — `PlusDerivationTree.ofTM`, the shape mirrored here
* `FormalSystem/StarLanguage/Axioms.lean` — `StarAxiom.ofBase`

## Tags

conservativity · star-language · embedding · proof-system
-/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.ProofSystem (FrameClass)
open FormalSystem.PlusLanguage

/-- The embedding of axioms preserves the minimum frame class: `ofBase` reads it straight off the
TM⁺ instance. Mirror of `PlusAxiom.minFrameClass_ofTM`. -/
theorem StarAxiom.minFrameClass_ofBase {φ : PlusFormula} (ax : PlusAxiom φ) :
    (StarAxiom.ofBase φ ax).minFrameClass = ax.minFrameClass := rfl

/--
**The backward conservativity bridge for L⁺ ⊂ L⋆.** Every TM⁺ derivation becomes a TM⋆
derivation of its embedding, at the same frame class and over the embedded context. Seven cases,
one per rule; the `axiom` case is `StarAxiom.ofBase`, the `temporal_duality` case transports
along `ofPlus_swapTemporal`, and the rest are structural.
-/
def StarDerivationTree.ofPlusTree {fc : FrameClass} {Γ : PlusContext} {φ : PlusFormula} :
    PlusDerivationTree fc Γ φ → StarDerivationTree fc (ofStarCtx Γ) (ofPlus φ)
  | .axiom _ _ h h_fc =>
      .axiom _ _ (StarAxiom.ofBase _ h) (by rw [StarAxiom.minFrameClass_ofBase]; exact h_fc)
  | .assumption _ _ h => .assumption _ _ (mem_ofStarCtx h)
  | .modus_ponens _ φ ψ d1 d2 =>
      .modus_ponens _ (ofPlus φ) (ofPlus ψ) (ofPlusTree d1) (ofPlusTree d2)
  | .necessitation φ d => .necessitation (ofPlus φ) (ofPlusTree d)
  | .temporal_necessitation φ d => .temporal_necessitation (ofPlus φ) (ofPlusTree d)
  | .temporal_duality φ d =>
      (ofPlus_swapTemporal φ).symm ▸
        StarDerivationTree.temporal_duality (ofPlus φ) (ofPlusTree d)
  | .weakening _ _ _ d h =>
      .weakening _ _ _ (ofPlusTree d)
        (by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact List.mem_map_of_mem (h hy))

/-- **Backward conservativity, `Prop`-level**: `TM⁺ ⊢⁺[fc] φ ⟹ TM⋆ ⊢⋆[fc] ofPlus φ`, at every
frame class and context. -/
theorem starDerivable_of_plusDerivable {fc : FrameClass} {Γ : PlusContext} {φ : PlusFormula}
    (h : PlusDerivable fc Γ φ) : StarDerivable fc (ofStarCtx Γ) (ofPlus φ) :=
  h.elim fun d => ⟨StarDerivationTree.ofPlusTree d⟩

/-- **L ⊂ L⋆, backward**: a TM theorem is a TM⋆ theorem at its doubly-embedded formula, by
composing with `plusDerivable_of_derivable`. This is the backward half of the unconditional
conservativity biconditional `starDerivable_ofFormula_iff`. -/
theorem starDerivable_of_derivable {fc : FrameClass} {φ : Formula}
    (h : ProofSystem.Derivable fc [] φ) : StarDerivable fc [] (ofPlus (ofFormula φ)) :=
  starDerivable_of_plusDerivable (plusDerivable_of_derivable h)

/-! ### Acceptance checks -/

/-- MF at a `⊡`-formula — an instance `PlusAxiom` supplies and no native TM⋆ schema could —
crosses the embedding. -/
example (p : Atom) :
    ⊢⋆[FrameClass.Base] ofPlus ((PlusFormula.box (PlusFormula.stab (PlusFormula.atom p))).imp
      (PlusFormula.box (PlusFormula.allFuture (PlusFormula.stab (PlusFormula.atom p))))) :=
  StarDerivationTree.ofPlusTree
    (.axiom [] _ (PlusAxiom.modal_future _) (FrameClass.base_le _))

/-- A TM⁺ theorem obtained by the `temporal_duality` rule crosses too — the case that consumes
`ofPlus_swapTemporal`. -/
example (fc : FrameClass) (φ : PlusFormula) :
    StarDerivable fc [] (ofPlus ((PlusFormula.stab φ).imp φ).swapTemporal) :=
  starDerivable_of_plusDerivable
    ⟨.temporal_duality _ (.axiom [] _ (PlusAxiom.stab_t φ) (FrameClass.base_le fc))⟩

end FormalSystem.StarLanguage
