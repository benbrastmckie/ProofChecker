/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.Fragment
import FormalSystem.Metalogic.Compactness

/-!
# Compactness of the base-language consequence relation at `.Base` and `.Dense`

The base-language mirror of `Metalogic/SetConsequence.lean`'s consequence-form compactness
`Compact fc`, transferred from the landed `compactBase` / `compactDense`
(`Metalogic/Compactness.lean`) along the translation `tr`.

## Main Definitions

- `BLSetConsequenceOnFrames`, `BLSetSemanticConsequenceOn` — set-premise consequence for
  `BLFormula`, binder for binder against `SetConsequenceOnFrames` / `SetSemanticConsequenceOn`
- `BLCompact fc` — the consequence form of compactness: a set-consequence yields a finite premise
  list whose `foldr`-implication into the conclusion is `BLValidIn fc`

## Main Results

- `blSetConsequence_iff_image` — BL set-consequence is BL⁺ set-consequence of the `tr`-image
- `tr_foldr_imp` — `tr` commutes with the `foldr`-implication
- `blCompact_of_compact` — `Compact fc → BLCompact fc`, by pulling the BL⁺ witness list back
  along `tr`
- `blCompactBase`, `blCompactDense` — the two positive rows

## Which form landed

The **consequence form** (the mirror of `Compact`, `SetConsequence.lean`), not the
model-existence form: the witness list pulls back along `tr` by a straightforward induction
(`exists_preimage_list`), because every member of the BL⁺ witness lies in `tr '' Γ` and `tr`
commutes with `imp` definitionally.

## The `.ZTime` and `.RTime` rows do NOT transfer

BL⁺'s non-compactness at `.ZTime` (`notCompactZTime`, witness `{F p} ∪ {¬Xⁿ p}`) and at
`.RTime` (`notCompactRTime`, witness built from `K⁺`-shaped `untl` guards) uses formulas
**outside the range of `tr`**: `Formula.next` is `untl bot _` and `K⁺` is a top-level `untl`,
while by `BaseLanguage.tr_ne_untl` nothing in the range of `tr` is a top-level `untl`. So neither
refutation transfers to the base language, and no BL non-compactness claim is made at those two
classes here. Only the two positive rows are delivered; whether `BLCompact .ZTime` or
`BLCompact .RTime` holds is left open.

## References

* `FormalSystem/Metalogic/SetConsequence.lean` — `SetConsequenceOnFrames`, `Compact`
* `FormalSystem/Metalogic/Compactness.lean` — `compactBase`, `compactDense`
* `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` — `truthAt_tr`,
  `blValidIn_iff_validIn_tr`
-/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic

/-- Set-premise consequence for the base language over the frames satisfying `P`. Binder-for-binder
mirror of `SetConsequenceOnFrames`, against `BLTruthAt`. -/
def BLSetConsequenceOnFrames (P : TaskFrame → Prop) (Γ : Set BLFormula) (φ : BLFormula) : Prop :=
  ∀ (F : TaskFrame), P F → ∀ (M : TaskModel F)
    (τ : WorldHistory F) (_ : τ.IsTotal) (t : F.Duration),
    (∀ ψ ∈ Γ, BLTruthAt M τ t ψ) → BLTruthAt M τ t φ

/-- Set-premise consequence for the base language at a `FrameClass` tag. Mirror of
`SetSemanticConsequenceOn`. -/
def BLSetSemanticConsequenceOn (fc : FrameClass) (Γ : Set BLFormula) (φ : BLFormula) : Prop :=
  BLSetConsequenceOnFrames fc.Sat Γ φ

/-- **Compactness of the base-language consequence relation at `fc`**, in the consequence form:
a set-consequence yields a finite premise list whose `foldr`-implication into the conclusion is
`BLValidIn fc`. Mirror of `Compact`. -/
def BLCompact (fc : FrameClass) : Prop :=
  ∀ (Γ : Set BLFormula) (φ : BLFormula), BLSetSemanticConsequenceOn fc Γ φ →
    ∃ L : List BLFormula, (∀ ψ ∈ L, ψ ∈ Γ) ∧ BLValidIn fc (L.foldr BLFormula.imp φ)

/-- BL set-consequence over the frames satisfying `P` is BL⁺ set-consequence of the `tr`-image
over the same frames, by the truth-transfer bridge `truthAt_tr` on every premise and on the
conclusion. -/
theorem blSetConsequenceOnFrames_iff_image (P : TaskFrame → Prop) (Γ : Set BLFormula)
    (φ : BLFormula) :
    BLSetConsequenceOnFrames P Γ φ ↔ SetConsequenceOnFrames P (tr '' Γ) (tr φ) := by
  constructor
  · intro h F hF M τ hτ t hΓ
    refine (truthAt_tr M φ τ t).mpr (h F hF M τ hτ t ?_)
    intro ψ hψ
    exact (truthAt_tr M ψ τ t).mp (hΓ (tr ψ) ⟨ψ, hψ, rfl⟩)
  · intro h F hF M τ hτ t hΓ
    refine (truthAt_tr M φ τ t).mp (h F hF M τ hτ t ?_)
    intro ψ' hψ'
    obtain ⟨ψ, hψ, rfl⟩ := hψ'
    exact (truthAt_tr M ψ τ t).mpr (hΓ ψ hψ)

/-- `blSetConsequenceOnFrames_iff_image` at a `FrameClass` tag. -/
theorem blSetConsequence_iff_image (fc : FrameClass) (Γ : Set BLFormula) (φ : BLFormula) :
    BLSetSemanticConsequenceOn fc Γ φ ↔ SetSemanticConsequenceOn fc (tr '' Γ) (tr φ) :=
  blSetConsequenceOnFrames_iff_image fc.Sat Γ φ

/-- `tr` commutes with the `foldr`-implication of a premise list, because `tr` is definitional on
`imp`. -/
theorem tr_foldr_imp (L : List BLFormula) (φ : BLFormula) :
    tr (L.foldr BLFormula.imp φ) = (L.map tr).foldr Formula.imp (tr φ) := by
  induction L with
  | nil => rfl
  | cons ψ L ih => simp only [List.foldr_cons, List.map_cons, tr_imp, ih]

/-- Every list of BL⁺ formulas drawn from `tr '' Γ` is the `tr`-image of a list drawn from `Γ`. -/
theorem exists_preimage_list (Γ : Set BLFormula) :
    ∀ L' : List Formula, (∀ ψ ∈ L', ψ ∈ tr '' Γ) →
      ∃ L : List BLFormula, (∀ ψ ∈ L, ψ ∈ Γ) ∧ L.map tr = L'
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | ψ :: L', h => by
      obtain ⟨χ, hχ, rfl⟩ := h ψ List.mem_cons_self
      obtain ⟨L, hL, hmap⟩ :=
        exists_preimage_list Γ L' (fun ψ' h' => h ψ' (List.mem_cons_of_mem _ h'))
      refine ⟨χ :: L, ?_, by simp [hmap]⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hχ
      · exact hL x hx

/--
**Transfer of compactness along `tr`.** From `Compact fc`, obtain the BL⁺ witness list for the
image consequence `tr '' Γ ⊨ tr φ`, pull it back along `tr` (`exists_preimage_list`), and read
the `BLValidIn` conclusion off `blValidIn_iff_validIn_tr` after rewriting with `tr_foldr_imp`.
-/
theorem blCompact_of_compact {fc : FrameClass} (h : Compact fc) : BLCompact fc := by
  intro Γ φ hcons
  obtain ⟨L', hL', hval⟩ := h (tr '' Γ) (tr φ) ((blSetConsequence_iff_image fc Γ φ).mp hcons)
  obtain ⟨L, hL, rfl⟩ := exists_preimage_list Γ L' hL'
  refine ⟨L, hL, (blValidIn_iff_validIn_tr fc _).mpr ?_⟩
  rw [tr_foldr_imp]
  exact hval

/-- **Compactness of the base-language consequence relation at `.Base`.** -/
theorem blCompactBase : BLCompact FrameClass.Base :=
  blCompact_of_compact compactBase

/-- **Compactness of the base-language consequence relation at `.Dense`.** -/
theorem blCompactDense : BLCompact FrameClass.Dense :=
  blCompact_of_compact compactDense

end FormalSystem.Metalogic.Conservativity
