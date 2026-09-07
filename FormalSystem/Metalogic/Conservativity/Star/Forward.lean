/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.Star.StarSoundness
import FormalSystem.Metalogic.Conservativity.Fragment

/-!
# Proof-theoretic conservativity of TM⋆ over TM⁺, both directions

The **forward** direction — `TM⋆ ⊢[fc] ofFormula φ ⟹ TM⁺ ⊢[fc] φ` — via semantics:

```
TM⋆ ⊢ ofFormula φ  ⟹[star_soundness_validIn]  StarValidIn fc (ofFormula φ)
                   ⟹[starValidIn_ofFormula_iff]  ValidIn fc φ
                   ⟹[WeakCompleteness fc engine]  TM⁺ ⊢ φ
```

It needs TM⋆ **soundness** and TM⁺ **completeness** — never TM⋆ completeness, which remains
open. Together with the backward direction `starDerivable_of_derivable`
(`StarLanguage/Derivation.lean`, by the constructor-to-constructor embedding of derivations),
this gives `starDerivable_ofFormula_iff`: **TM⋆ is a conservative extension of TM⁺**, at every
frame class carrying a completeness engine — that is, at all four.

## Contrast with the base-language pair

The same composition for L ⊂ L⁺ (`TM⁺ ⊢ tr φ ⟹ TM ⊢ φ`) would need TM-completeness, which is
refuted (`tmCompleteZTime_refuted`; `Metalogic/Conservativity.lean`). So `Forward⋆`
(TM⋆ over TM⁺) holds at all four classes, unlike `Forward` (TM⁺ over TM). The composed L ⊂ L⋆
rows below inherit exactly that status: the backward direction composes, the forward direction
is the L ⊂ L⁺ forward direction and is **not asserted**.

## Main Results

- `forward_star` — the forward direction at any class with an engine; four instantiated rows
- `starDerivable_ofFormula_iff` — conservativity in both directions; four rows
- `star_of_tm` — the composed L ⊂ L⋆ backward rows
- `tmFrag_iff_star` — the H/G-fragment of TM⁺ is also the H/G-fragment of TM⋆

## References

* `FormalSystem/Metalogic/StrongCompleteness.lean` — the four `WeakCompleteness` engines
* `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — why the L ⊂ L⁺ forward
  direction is a different matter
-/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.StarLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic

/-- **Forward conservativity of TM⋆ over TM⁺**, at any class with a weak-completeness engine:
TM⋆ soundness, then the truth-transfer bridge, then the engine. -/
theorem forward_star {fc : FrameClass} (engine : WeakCompleteness fc) (φ : Formula)
    (h : StarDerivable fc [] (ofFormula φ)) : ProofSystem.Derivable fc [] φ :=
  engine φ ((starValidIn_ofFormula_iff fc φ).mp (star_soundness_validIn h))

/-- Forward conservativity at `.Base`, via `completeness_base`. -/
theorem forward_star_base (φ : Formula) (h : StarDerivable FrameClass.Base [] (ofFormula φ)) :
    ProofSystem.Derivable FrameClass.Base [] φ :=
  forward_star completeness_base φ h

/-- Forward conservativity at `.Dense`, via `completeness_dense`. -/
theorem forward_star_dense (φ : Formula) (h : StarDerivable FrameClass.Dense [] (ofFormula φ)) :
    ProofSystem.Derivable FrameClass.Dense [] φ :=
  forward_star completeness_dense φ h

/-- Forward conservativity at `.Discrete`, via `completeness_ztime`. -/
theorem forward_star_ztime (φ : Formula)
    (h : StarDerivable FrameClass.Discrete [] (ofFormula φ)) :
    ProofSystem.Derivable FrameClass.Discrete [] φ :=
  forward_star completeness_ztime φ h

/-- Forward conservativity at `.Dedekind`, via `completeness_rtime`. -/
theorem forward_star_rtime (φ : Formula)
    (h : StarDerivable FrameClass.Dedekind [] (ofFormula φ)) :
    ProofSystem.Derivable FrameClass.Dedekind [] φ :=
  forward_star completeness_rtime φ h

/-- **TM⋆ is a conservative extension of TM⁺**: at any class with an engine, an L⁺ formula is a
TM⋆ theorem iff it is a TM⁺ theorem. Backward by the embedding of derivations, forward by
soundness plus completeness. -/
theorem starDerivable_ofFormula_iff {fc : FrameClass} (engine : WeakCompleteness fc)
    (φ : Formula) : StarDerivable fc [] (ofFormula φ) ↔ ProofSystem.Derivable fc [] φ :=
  ⟨forward_star engine φ, fun h => starDerivable_of_derivable h⟩

/-- Conservativity at `.Base`. -/
theorem starDerivable_ofFormula_iff_base (φ : Formula) :
    StarDerivable FrameClass.Base [] (ofFormula φ) ↔ ProofSystem.Derivable FrameClass.Base [] φ :=
  starDerivable_ofFormula_iff completeness_base φ

/-- Conservativity at `.Dense`. -/
theorem starDerivable_ofFormula_iff_dense (φ : Formula) :
    StarDerivable FrameClass.Dense [] (ofFormula φ) ↔
      ProofSystem.Derivable FrameClass.Dense [] φ :=
  starDerivable_ofFormula_iff completeness_dense φ

/-- Conservativity at `.Discrete`. -/
theorem starDerivable_ofFormula_iff_ztime (φ : Formula) :
    StarDerivable FrameClass.Discrete [] (ofFormula φ) ↔
      ProofSystem.Derivable FrameClass.Discrete [] φ :=
  starDerivable_ofFormula_iff completeness_ztime φ

/-- Conservativity at `.Dedekind`. -/
theorem starDerivable_ofFormula_iff_rtime (φ : Formula) :
    StarDerivable FrameClass.Dedekind [] (ofFormula φ) ↔
      ProofSystem.Derivable FrameClass.Dedekind [] φ :=
  starDerivable_ofFormula_iff completeness_rtime φ

/-! ## The composed pair L ⊂ L⋆

Backward: `derivable_translate` (`Conservativity/Backward.lean`) composed with
`starDerivable_of_derivable`. The **forward** direction for this pair,
`TM⋆ ⊢ ofFormula (tr φ) ⟹ TM ⊢ φ`, is by `starDerivable_ofFormula_iff` exactly the L ⊂ L⁺
forward direction `TM⁺ ⊢ tr φ ⟹ TM ⊢ φ`, which is refuted at `.Base` and `.Discrete` and open
at `.Dense` and `.Dedekind` (`Metalogic/Conservativity.lean`); it is **not asserted**. -/

/-- **L ⊂ L⋆, backward**: a TM theorem embeds, through `tr` and `ofFormula`, into a TM⋆ theorem
at the same class. -/
theorem star_of_tm {fc : FrameClass} (φ : BLFormula)
    (h : BaseLanguage.Derivable fc [] φ) : StarDerivable fc [] (ofFormula (tr φ)) :=
  starDerivable_of_derivable (derivable_translate h)

/-- L ⊂ L⋆ backward at `.Base`. -/
theorem star_of_tm_base (φ : BLFormula) (h : BaseLanguage.Derivable FrameClass.Base [] φ) :
    StarDerivable FrameClass.Base [] (ofFormula (tr φ)) :=
  star_of_tm φ h

/-- L ⊂ L⋆ backward at `.Dense`. -/
theorem star_of_tm_dense (φ : BLFormula) (h : BaseLanguage.Derivable FrameClass.Dense [] φ) :
    StarDerivable FrameClass.Dense [] (ofFormula (tr φ)) :=
  star_of_tm φ h

/-- L ⊂ L⋆ backward at `.Discrete`. -/
theorem star_of_tm_ztime (φ : BLFormula)
    (h : BaseLanguage.Derivable FrameClass.Discrete [] φ) :
    StarDerivable FrameClass.Discrete [] (ofFormula (tr φ)) :=
  star_of_tm φ h

/-- L ⊂ L⋆ backward at `.Dedekind`. -/
theorem star_of_tm_rtime (φ : BLFormula)
    (h : BaseLanguage.Derivable FrameClass.Dedekind [] φ) :
    StarDerivable FrameClass.Dedekind [] (ofFormula (tr φ)) :=
  star_of_tm φ h

/-- **The H/G-fragment is the same seen from TM⋆**: `TMFrag fc φ` (`Conservativity/Fragment.lean`)
iff the embedding of `tr φ` is a TM⋆ theorem, at any class with an engine. -/
theorem tmFrag_iff_star {fc : FrameClass} (engine : WeakCompleteness fc) (φ : BLFormula) :
    TMFrag fc φ ↔ StarDerivable fc [] (ofFormula (tr φ)) :=
  (starDerivable_ofFormula_iff engine (tr φ)).symm

/-! ### Acceptance check -/

example (φ : Formula) :
    StarDerivable FrameClass.Base [] (ofFormula φ) ↔ ProofSystem.Derivable FrameClass.Base [] φ :=
  starDerivable_ofFormula_iff completeness_base φ

end FormalSystem.Metalogic.Conservativity
