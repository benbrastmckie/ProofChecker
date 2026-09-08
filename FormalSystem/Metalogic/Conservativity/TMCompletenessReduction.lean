/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.BaseLanguageSoundness
import FormalSystem.Metalogic.BXCanonical
import FormalSystem.Metalogic.StrongCompleteness

/-!
# The TM-completeness / forward-conservativity reduction

**Read `Metalogic/Conservativity.lean`'s module docstring first.** That module states, and
proves the tree must never state or `sorry`, the **forward-conservativity prohibition**:

```
theorem forward {fc} {φ} : ProofSystem.Derivable fc [] (tr φ) → BaseLanguage.Derivable fc [] φ
```

is refuted at `fc := .Base` and `fc := .ZTime`, and a `sorry`-ed proof of it would be an
unsound placeholder, not deferred debt.

**This module strengthens that prohibition by exposing a second phrasing of the forbidden
claim.** Given the tree's own `BXCanonical.completeness` (BL⁺ completeness at `.Base`) and
`blValid_iff_valid_tr` (the BL/BL⁺ validity bridge), "TM is complete over task frames" and
"forward conservativity holds at `FrameClass.Base`" turn out to be *the same proposition* — a
two-line composition of results already in this tree, with **neither side asserted**. Nothing
here proves TM-completeness, and nothing here proves forward conservativity; the point is that a
future dispatch attempting either one, in good faith, is thereby attempting the other, and is
covered by the same prohibition. No `sorry` occurs anywhere in this file, and neither
`TMCompleteBase` nor `ForwardBase` (nor their `.ZTime` siblings) appears as the conclusion of
any `theorem` below — both are `def`s, referenced only as the *statement* being related, never
discharged.

## Where the backward direction does the work

`tmCompleteBase_iff_forwardBase`'s **backward** direction (`ForwardBase → TMCompleteBase`) is
where `BXCanonical.completeness` — TM⁺'s completeness over *all* task frames, `cor:tm-completeness`
row 1, machine-checked in this tree — actually does the work: it is the step that turns a
BL-valid formula into a `⊢[Base] tr φ` derivation, which `ForwardBase` then pulls back across the
translation. The **forward** direction (`TMCompleteBase → ForwardBase`) is the easier composition,
routing `⊢[Base] tr φ` through TM⁺'s own soundness to `Valid (tr φ)`, then across
`blValid_iff_valid_tr` to `BLValid φ`.

## Main Definitions

- `TMComplete fc` — "TM is complete over the frames of `fc`": every `fc`-BL-valid formula is
  TM-derivable at `fc`. Unasserted, at every tag.
- `Forward fc` — the forward-conservativity statement at `fc`, literally `Conservativity.lean`'s
  forbidden `forward` theorem restricted to one frame class. Unasserted, at every tag.
- `TMCompleteBase`, `TMCompleteZTime`, `ForwardBase`, `ForwardZTime` — the two tags this
  module named before the generalization, retained as instantiations with their statements
  unchanged.

## Main Results

- `tmComplete_iff_forward` — the two propositions are equivalent at any `fc` supplying a
  `WeakCompleteness fc` engine
- `tmCompleteBase_iff_forwardBase`, `tmCompleteZTime_iff_forwardZTime` — its two
  pre-existing instantiations
- `tmCompleteDense_iff_forwardDense`, `tmCompleteRTime_iff_forwardRTime` — two further
  rows the generalization yields for free

## References

* `FormalSystem/Metalogic/Conservativity.lean` — the forward-conservativity prohibition this
  module strengthens
* `FormalSystem/Metalogic/BXCanonical/Completeness.lean` — `completeness`, `completeness_ztime`
* `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` — `blValid_iff_valid_tr`,
  `blValidZTime_iff_validZTime_tr`
-/

namespace FormalSystem.Metalogic

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic.Conservativity

/-! ## The reduction, at any frame class

Both propositions and the equivalence between them, stated once and indexed by the `FrameClass`
tag. The four per-tag rows below are instantiations; before this collapse the `.Base` and
`.ZTime` rows were two hand-written copies of the same two-line composition, and the `.Dense`
and `.RTime` rows did not exist. -/

/--
**"TM is complete over the frames of `fc`."** Every `fc`-BL-valid formula is derivable in TM at
`fc`. **Unasserted** — this `def` states the proposition so it can be named and related to
`Forward` below; it is never the conclusion of a `theorem` in this tree, at any tag.
-/
def TMComplete (fc : FrameClass) : Prop :=
  ∀ φ : BLFormula, BLValidIn fc φ → BaseLanguage.Derivable fc [] φ

/--
**"Forward conservativity holds at `fc`."** Literally the `forward` theorem
`Conservativity.lean`'s module docstring shows must never be stated or `sorry`-ed, restricted to
one tag. **Unasserted**, for the same reason.
-/
def Forward (fc : FrameClass) : Prop :=
  ∀ φ : BLFormula, ProofSystem.Derivable fc [] (tr φ) → BaseLanguage.Derivable fc [] φ

/--
**The reduction, generically.** `TMComplete fc` and `Forward fc` are the same proposition, given
a weak-completeness engine at `fc`.

Forward (`TMComplete fc → Forward fc`): given `⊢[fc] tr φ`, `soundness_validIn`
(`Metalogic/Soundness.lean`) gives `ValidIn fc (tr φ)`, and `blValidIn_iff_validIn_tr`
(`Metalogic/Conservativity/BaseLanguageSoundness.lean`) crosses to `BLValidIn fc φ`; apply the hypothesis. This
direction does not use the engine.

Backward (`Forward fc → TMComplete fc`): given `BLValidIn fc φ`, `blValidIn_iff_validIn_tr` gives
`ValidIn fc (tr φ)`, and the **engine** turns that into `⊢[fc] tr φ`; apply the hypothesis. This
is where TM⁺'s completeness does the actual work, and it is the whole of the class-dependence —
the reason `WeakCompleteness fc` is the hypothesis rather than anything stronger.

**The module's prohibition discipline is preserved, not weakened.** The conclusion here is an
`Iff`, not either side of it: nothing below asserts `TMComplete fc` and nothing asserts
`Forward fc`. What the generalization adds is that the equivalence now holds at all four tags
rather than two, so a future dispatch attempting either side at *any* class is thereby
attempting the other, and is covered by the same prohibition.
-/
theorem tmComplete_iff_forward {fc : FrameClass} (engine : WeakCompleteness fc) :
    TMComplete fc ↔ Forward fc := by
  constructor
  · intro hcomplete φ h
    exact hcomplete φ ((blValidIn_iff_validIn_tr fc φ).mpr (h.elim soundness_validIn))
  · intro hforward φ hvalid
    exact hforward φ (engine (tr φ) ((blValidIn_iff_validIn_tr fc φ).mp hvalid))

/-! ## `FrameClass.Base` -/

/--
**"TM is complete over task frames."** `TMComplete` at `.Base`. `BLValid` is `BLValidIn .Base`
definitionally (`Semantics/BLValidity.lean`), so the statement is unchanged by the
generalization. **Unasserted.**
-/
def TMCompleteBase : Prop := TMComplete FrameClass.Base

/--
**"Forward conservativity holds at `FrameClass.Base`."** `Forward` at `.Base`. **Unasserted**,
for the same reason.
-/
def ForwardBase : Prop := Forward FrameClass.Base

/-- **The reduction at `.Base`.** `tmComplete_iff_forward` with `completeness_base`
(`Metalogic/StrongCompleteness.lean`) as the engine — that theorem is stated as a
`WeakCompleteness FrameClass.Base` witness, so it inhabits the hypothesis on the nose. -/
theorem tmCompleteBase_iff_forwardBase : TMCompleteBase ↔ ForwardBase :=
  tmComplete_iff_forward completeness_base

/-! ## `FrameClass.ZTime` -/

/--
**"TM_z is complete over `FrameClass.ZTime` task frames."** `TMComplete` at `.ZTime`;
`BLValidZTime` is `BLValidIn .ZTime` definitionally. **Unasserted**, exactly as
`TMCompleteBase`.
-/
def TMCompleteZTime : Prop := TMComplete FrameClass.ZTime

/--
**"Forward conservativity holds at `FrameClass.ZTime`."** `Forward` at `.ZTime`.
**Unasserted**, exactly as `ForwardBase`.
-/
def ForwardZTime : Prop := Forward FrameClass.ZTime

/-- **The `.ZTime` mirror**, with `completeness_ztime` as the engine. -/
theorem tmCompleteZTime_iff_forwardZTime : TMCompleteZTime ↔ ForwardZTime :=
  tmComplete_iff_forward completeness_ztime

/-! ## The two rows the generalization yields

`FrameClass.Dense` and `FrameClass.RTime` carry weak-completeness engines of their own
(`completeness_dense` and `completeness_rtime`, the latter being Reynolds 1992 §9 Theorem 7 as
formalized in this tree), so the same equivalence holds at those tags. Neither row existed before
the collapse, and neither costs anything beyond naming it. Both sides remain **unasserted** at
both tags, exactly as at `.Base` and `.ZTime`. -/

/-- **The `.Dense` row.** `tmComplete_iff_forward completeness_dense`. -/
theorem tmCompleteDense_iff_forwardDense :
    TMComplete FrameClass.Dense ↔ Forward FrameClass.Dense :=
  tmComplete_iff_forward completeness_dense

/-- **The `.RTime` row.** `tmComplete_iff_forward completeness_rtime`. -/
theorem tmCompleteRTime_iff_forwardRTime :
    TMComplete FrameClass.RTime ↔ Forward FrameClass.RTime :=
  tmComplete_iff_forward completeness_rtime


end FormalSystem.Metalogic
