/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.Z1Countermodel

/-!
# `TMFrag` — the H/G-fragment of TM⁺, and its metatheory

**Read `Metalogic/Conservativity.lean`'s module docstring first.** Forward proof-theoretic
conservativity of TM⁺ over TM — `Derivable fc [] (tr φ) → BaseLanguage.Derivable fc [] φ` —
is refuted at `.ZTime` (`tmCompleteZTime_refuted`), refuted in the source at `.Base`, and
by `tmComplete_iff_forward` it is *the same proposition* as "TM is complete over the frames of
`fc`". Nothing in this file states, approaches, or `sorry`s it.

What this file delivers instead is the logic that **is** complete for the base-language
validity `BLValidIn fc`: the **H/G-fragment of TM⁺**,

```
TMFrag fc φ  :=  TM⁺ ⊢[fc] tr φ
```

the set of base-language formulas whose translation is a TM⁺ theorem. Its metatheory transfers
mechanically through the landed truth-transfer bridge `blValidIn_iff_validIn_tr`
(`Conservativity/BaseLanguageSoundness.lean`):

- **soundness** (`tmFrag_sound`) from `soundness_validIn`;
- **completeness** (`tmFrag_complete`) from any `WeakCompleteness fc` engine — instantiated at
  all four classes by `tmFrag_complete_base/dense/discrete/dedekind`;
- **`TM ⊆ TMFrag`** at every class (`tm_le_tmFrag`, the `Γ = []` instance of
  `derivable_translate`);
- **`TM ⊊ TMFrag` at `.ZTime`** (`tm_lt_tmFrag_ztime`): the Z1 schema is in the fragment
  (`z1_translate`) but not a TM_f theorem (`not_bl_derivable_z1`);
- the reduction restated in fragment terms (`tmComplete_iff_tmFrag_le_tm`): TM is complete at
  `fc` iff the fragment collapses onto TM at `fc` — with `Forward` unfolded, never asserted.

Compactness of the fragment at `.Base` and `.Dense` is the sibling module
`Conservativity/FragmentCompactness.lean`.

## Why the fragment, and not a finite axiomatization

`TMFrag` is defined *through* TM⁺; a native finite Hilbert axiomatization of the H/G-fragment of
TM⁺ over `BLFormula` is open research and is not attempted here. What the fragment gives is an
honest, complete logic of `BLValidIn` at every frame class, which TM itself is not
(`tmCompleteZTime_refuted`).

## References

* `FormalSystem/Metalogic/Conservativity.lean` — the forward-conservativity prohibition
* `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — `TMComplete`,
  `Forward`, `tmComplete_iff_forward`
* `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean` — `not_bl_derivable_z1`
* `FormalSystem/Metalogic/StrongCompleteness.lean` — the four `WeakCompleteness` engines

## Tags

conservativity · fragment · base-language · completeness · compactness
-/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic

/--
**The H/G-fragment of TM⁺.** A base-language formula `φ` is a theorem of the fragment at `fc`
iff its translation `tr φ` is a TM⁺ theorem at `fc`.

This — not TM — is the complete logic of `BLValidIn fc`: by `tmComplete_iff_forward`
(`Conservativity/TMCompletenessReduction.lean`), TM-completeness at `fc` is equivalent to forward
conservativity at `fc`, which is refuted at `.ZTime` (`tmCompleteZTime_refuted`). The
fragment sidesteps that gap by definition: `tmFrag_iff_blValidIn` below shows it is exactly
`BLValidIn fc` at every class carrying a `WeakCompleteness fc` engine.
-/
def TMFrag (fc : FrameClass) (φ : BLFormula) : Prop :=
  ProofSystem.Derivable fc [] (tr φ)

/-- **Soundness of the fragment.** A fragment theorem at `fc` is `BLValidIn fc`: TM⁺ soundness
(`soundness_validIn`) on the translation, crossed back through `blValidIn_iff_validIn_tr`.

Paper: — (formalization-native; the H/G-fragment is this tree's construction)
-/
theorem tmFrag_sound {fc : FrameClass} (φ : BLFormula) (h : TMFrag fc φ) : BLValidIn fc φ :=
  (blValidIn_iff_validIn_tr fc φ).mpr (h.elim soundness_validIn)

/-- **Completeness of the fragment**, given a weak-completeness engine at `fc`: a `BLValidIn fc`
formula's translation is `ValidIn fc` (`blValidIn_iff_validIn_tr`), hence TM⁺-derivable.

Paper: — (formalization-native; the H/G-fragment is this tree's construction)
-/
theorem tmFrag_complete {fc : FrameClass} (engine : WeakCompleteness fc) (φ : BLFormula)
    (h : BLValidIn fc φ) : TMFrag fc φ :=
  engine (tr φ) ((blValidIn_iff_validIn_tr fc φ).mp h)

/-- **The fragment is exactly base-language validity**, at every class with an engine. -/
theorem tmFrag_iff_blValidIn {fc : FrameClass} (engine : WeakCompleteness fc) (φ : BLFormula) :
    TMFrag fc φ ↔ BLValidIn fc φ :=
  ⟨tmFrag_sound φ, tmFrag_complete engine φ⟩

/-! ### The four completeness rows

`tmFrag_complete` at the four engines of `Metalogic/StrongCompleteness.lean`. -/

/-- Fragment completeness at `.Base`, via `completeness_base`. -/
theorem tmFrag_complete_base (φ : BLFormula) (h : BLValidIn FrameClass.Base φ) :
    TMFrag FrameClass.Base φ :=
  tmFrag_complete completeness_base φ h

/-- Fragment completeness at `.Dense`, via `completeness_dense`. -/
theorem tmFrag_complete_dense (φ : BLFormula) (h : BLValidIn FrameClass.Dense φ) :
    TMFrag FrameClass.Dense φ :=
  tmFrag_complete completeness_dense φ h

/-- Fragment completeness at `.ZTime`, via `completeness_ztime`. -/
theorem tmFrag_complete_ztime (φ : BLFormula) (h : BLValidIn FrameClass.ZTime φ) :
    TMFrag FrameClass.ZTime φ :=
  tmFrag_complete completeness_ztime φ h

/-- Fragment completeness at `.RTime`, via `completeness_rtime`. -/
theorem tmFrag_complete_rtime (φ : BLFormula) (h : BLValidIn FrameClass.RTime φ) :
    TMFrag FrameClass.RTime φ :=
  tmFrag_complete completeness_rtime φ h

/-! ### `TM ⊆ TMFrag`, and the strict inclusion at `.ZTime` -/

/-- **`TM ⊆ TMFrag` at every class.** The `Γ = []` instance of `derivable_translate`
(`Conservativity/Backward.lean`); `trCtx [] = []` definitionally, so no context bookkeeping.

Paper: — (formalization-native; the H/G-fragment is this tree's construction)
-/
theorem tm_le_tmFrag {fc : FrameClass} (φ : BLFormula)
    (h : BaseLanguage.Derivable fc [] φ) : TMFrag fc φ :=
  derivable_translate h

/-- The Z1 schema is in the fragment at `.ZTime`: this is `z1_translate`. -/
theorem tmFrag_z1_ztime (p : Atom) : TMFrag FrameClass.ZTime (Z1 (.atom p)) :=
  z1_translate _

/--
**`TM ⊊ TMFrag` at `.ZTime`.** Every TM_f theorem is in the fragment, and the fragment
contains a formula — `Z1 p` — that TM_f does not derive (`not_bl_derivable_z1`,
`Conservativity/Z1Countermodel.lean`, by soundness over the non-Archimedean carrier
`ℚ ×ₗ ℤ`).

This is the fragment-logic reading of the CEF refutation: the H/G-fragment of TM⁺_f is
strictly larger than TM_f.

Paper: — (formalization-native; the H/G-fragment is this tree's construction)
-/
theorem tm_lt_tmFrag_ztime :
    (∀ φ : BLFormula, BaseLanguage.Derivable FrameClass.ZTime [] φ →
        TMFrag FrameClass.ZTime φ) ∧
      ∃ φ : BLFormula, TMFrag FrameClass.ZTime φ ∧
        ¬ BaseLanguage.Derivable FrameClass.ZTime [] φ :=
  ⟨fun φ h => tm_le_tmFrag φ h,
   ⟨Z1 (.atom (Atom.mkBase "p")), tmFrag_z1_ztime _, not_bl_derivable_z1 _⟩⟩

/--
**The reduction, in fragment terms.** TM is complete over the frames of `fc` iff the fragment
collapses onto TM at `fc`. This is `tmComplete_iff_forward` with `Forward fc` unfolded to its
definition — `∀ φ, TMFrag fc φ → BaseLanguage.Derivable fc [] φ` — and, exactly as there,
**neither side is asserted**: at `.ZTime` both are false (`tmCompleteZTime_refuted`,
`tm_lt_tmFrag_ztime`).
-/
theorem tmComplete_iff_tmFrag_le_tm {fc : FrameClass} (engine : WeakCompleteness fc) :
    TMComplete fc ↔ ∀ φ : BLFormula, TMFrag fc φ → BaseLanguage.Derivable fc [] φ :=
  tmComplete_iff_forward engine

/-! ### Acceptance checks -/

/-- The flagship equivalence typechecks at `.Base` on the nose. -/
example (φ : BLFormula) : TMFrag FrameClass.Base φ ↔ BLValidIn FrameClass.Base φ :=
  tmFrag_iff_blValidIn completeness_base φ

/-- At `.ZTime`, TM-completeness is refuted and the fragment is strictly larger — the two
facts are the two halves of one story. -/
example : ¬ TMComplete FrameClass.ZTime := tmCompleteZTime_refuted (Atom.mkBase "p")

end FormalSystem.Metalogic.Conservativity
