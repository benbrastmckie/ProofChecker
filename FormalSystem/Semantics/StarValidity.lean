/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Semantics.StarTruth
import FormalSystem.Semantics.Validity

/-!
# L⋆ validity — the `StarFormula` mirrors of `Semantics/Validity.lean`

Validity for the language L⋆ (`FormalSystem/StarLanguage/Formula.lean`), stated against the
native `StarTruthAt` of `Semantics/StarTruth.lean`, plus the **truth-transfer bridge** along the
embedding `ofFormula : Formula → StarFormula` and the **semantic conservativity** of L⋆ over
L⁺ that follows from it at every frame class.

Each predicate here is a binder-for-binder mirror of its counterpart in `Semantics/Validity.lean`
(and of the base-language mirror in `Semantics/BLValidity.lean`): `TaskFrame.StarValidOn` of
`TaskFrame.ValidOn`, `StarValidOnFrames` of `ValidOnFrames`, `StarValidIn` of `ValidIn`,
`StarValid` of `Valid`. The frame-predicate form `StarValidOnFrames` is the **primitive**, and
`StarValidIn fc := StarValidOnFrames fc.Sat` its instance at a tag — exactly the shape that lets
one monotonicity lemma serve every bridge, and that lets a validity notion over a frame class no
`FrameClass` tag denotes (for instance the deterministic frames) be stated without touching the
semantics.

## Main Definitions

- `TaskFrame.StarValidOn`, `StarValidOnFrames`, `StarValidIn`, `StarValid`
- `StarValidDense`, `StarValidDiscrete`, `StarValidDedekind` — the per-class abbreviations

## Main Results

- `StarValidOnFrames.mono`, `StarValidIn.mono` — monotonicity
- `StarValidIn.of_forall_total` / `.apply_total` and the `StarValidOnFrames` forms — the
  binder-shape adapters
- `starTruthAt_ofFormula` — **the truth-transfer bridge**: an L⁺ formula is true in L⋆ exactly
  when it is true in L⁺, at the same model, history and time
- `starValidIn_ofFormula_iff` — **semantic conservativity of L⋆ over L⁺, at every frame
  class**; `starValid_ofFormula_iff` is its `.Base` instance

## References

* JPL paper `def:frame-validity`, `def:logical-consequence`, `cor:tm-completeness`
* `FormalSystem/Semantics/Validity.lean` — the L⁺ predicates these mirror
* `FormalSystem/Semantics/BLValidity.lean` — the base-language mirror, the same shape
-/

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.StarLanguage

/-! ## `FrameClass`-indexed validity for L⋆ -/

/-- `def:frame-validity` for L⋆: `φ` is valid over the frame `F` iff it is true at every model
over `F`, every possible world `τ ∈ H_F`, and every time. The L⋆ mirror of
`TaskFrame.ValidOn`. -/
def TaskFrame.StarValidOn (F : TaskFrame) (φ : StarFormula) : Prop :=
  ∀ (M : TaskModel F) (τ : TaskFrame.HF F) (x : F.Duration), StarTruthAt M τ.val x φ

/-- `φ` is valid on every frame satisfying `P`. **The primitive**: the L⋆ mirror of
`ValidOnFrames`, indexed by a bare frame predicate rather than a `FrameClass` tag so that one
monotonicity lemma serves every bridge and so that validity over a class no tag denotes can be
stated directly. -/
def StarValidOnFrames (P : TaskFrame → Prop) (φ : StarFormula) : Prop :=
  ∀ F : TaskFrame, P F → F.StarValidOn φ

/-- Class-restricted validity `⊨_C` for L⋆, at a `FrameClass` tag. The L⋆ mirror of `ValidIn`,
over the same `FrameClass.Sat`. -/
def StarValidIn (fc : ProofSystem.FrameClass) (φ : StarFormula) : Prop :=
  StarValidOnFrames fc.Sat φ

/-- An L⋆ formula is **valid** if it is true in all models, at all times, at every **total**
history, over every task frame. `StarValidIn` at the unconstrained class, exactly as `Valid` is
`ValidIn .Base`. -/
def StarValid (φ : StarFormula) : Prop :=
  StarValidIn ProofSystem.FrameClass.Base φ

/-- Validity over dense frames. Mirror of `ValidDense`. -/
def StarValidDense (φ : StarFormula) : Prop := StarValidIn ProofSystem.FrameClass.Dense φ

/-- Validity over discrete (succ-Archimedean) frames. Mirror of `ValidDiscrete`. -/
def StarValidDiscrete (φ : StarFormula) : Prop := StarValidIn ProofSystem.FrameClass.Discrete φ

/-- Validity over dense Dedekind-complete frames. Mirror of `ValidDedekind`. -/
def StarValidDedekind (φ : StarFormula) : Prop := StarValidIn ProofSystem.FrameClass.Dedekind φ

/-! ### Monotonicity -/

/-- `StarValidOnFrames` is antitone in its frame predicate. Mirror of `ValidOnFrames.mono`. -/
theorem StarValidOnFrames.mono {P Q : TaskFrame → Prop} {φ : StarFormula}
    (h : ∀ F, Q F → P F) (hP : StarValidOnFrames P φ) : StarValidOnFrames Q φ :=
  fun F hF => hP F (h F hF)

/-- L⋆ validity is monotone in the `FrameClass` order. Mirror of `ValidIn.mono`. -/
theorem StarValidIn.mono {fc₁ fc₂ : ProofSystem.FrameClass} {φ : StarFormula} (h : fc₁ ≤ fc₂)
    (hv : StarValidIn fc₁ φ) : StarValidIn fc₂ φ :=
  StarValidOnFrames.mono (fun _ => ProofSystem.FrameClass.Sat.anti h) hv

/-! ### Binder-shape adapters

`StarValidOnFrames` is stated over the bundled `(τ : TaskFrame.HF F)`; every proof that consumes
or produces it works with the unbundled pair `(τ : WorldHistory F) (hτ : τ.IsTotal)`. These four
are the adapters, exactly as on the L⁺ and BL sides. -/

/-- Introduce `StarValidOnFrames` from the unbundled shape. -/
theorem StarValidOnFrames.of_forall_total {P : TaskFrame → Prop} {φ : StarFormula}
    (h : ∀ (F : TaskFrame), P F → ∀ (M : TaskModel F) (τ : WorldHistory F),
           τ.IsTotal → ∀ t : F.Duration, StarTruthAt M τ t φ) :
    StarValidOnFrames P φ :=
  fun F hF M τ t => h F hF M τ.val τ.property t

/-- Eliminate `StarValidOnFrames` into the unbundled shape. -/
theorem StarValidOnFrames.apply_total {P : TaskFrame → Prop} {φ : StarFormula}
    (h : StarValidOnFrames P φ) (F : TaskFrame) (hF : P F) (M : TaskModel F)
    (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration) : StarTruthAt M τ t φ :=
  h F hF M ⟨τ, hτ⟩ t

/-- `StarValidOnFrames.of_forall_total` at a `FrameClass` tag. -/
theorem StarValidIn.of_forall_total {fc : ProofSystem.FrameClass} {φ : StarFormula}
    (h : ∀ (F : TaskFrame), fc.Sat F → ∀ (M : TaskModel F) (τ : WorldHistory F),
           τ.IsTotal → ∀ t : F.Duration, StarTruthAt M τ t φ) :
    StarValidIn fc φ :=
  StarValidOnFrames.of_forall_total h

/-- `StarValidOnFrames.apply_total` at a `FrameClass` tag. -/
theorem StarValidIn.apply_total {fc : ProofSystem.FrameClass} {φ : StarFormula}
    (h : StarValidIn fc φ) (F : TaskFrame) (hF : fc.Sat F) (M : TaskModel F)
    (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration) : StarTruthAt M τ t φ :=
  StarValidOnFrames.apply_total h F hF M τ hτ t

/-- Introduce `StarValid` from the unbundled shape; the `Sat .Base` argument (`True`) is
discharged here. Mirror of `Valid.of_forall_total`. -/
theorem StarValid.of_forall_total {φ : StarFormula}
    (h : ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F),
           τ.IsTotal → ∀ t : F.Duration, StarTruthAt M τ t φ) :
    StarValid φ :=
  fun F _ M τ t => h F M τ.val τ.property t

/-- Eliminate `StarValid` into the unbundled shape. Mirror of `Valid.apply`. -/
theorem StarValid.apply {φ : StarFormula} (h : StarValid φ) (F : TaskFrame) (M : TaskModel F)
    (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration) : StarTruthAt M τ t φ :=
  h F trivial M ⟨τ, hτ⟩ t

/-! ## The truth-transfer bridge along `ofFormula` -/

variable {F : TaskFrame}

/--
**The truth-transfer bridge.** An L⁺ formula embedded into L⋆ is true exactly when it is true in
L⁺, at the same model, history and time.

By induction on `φ`, `generalizing τ t`: the `box` case needs the hypothesis at a different
history and the two temporal cases at a different time. Every case is congruence, because the
six L⁺ clauses of `StarTruthAt` are `TruthAt`'s verbatim and `ofFormula` is
constructor-to-constructor.
-/
theorem starTruthAt_ofFormula (M : TaskModel F) (φ : Formula) :
    ∀ (τ : WorldHistory F) (t : F.Duration),
      StarTruthAt M τ t (ofFormula φ) ↔ TruthAt M τ t φ := by
  induction φ with
  | atom p => intro τ t; exact Iff.rfl
  | bot => intro τ t; exact Iff.rfl
  | imp φ ψ ihφ ihψ => intro τ t; exact Iff.imp (ihφ τ t) (ihψ τ t)
  | box φ ih => intro τ t; exact forall_congr' fun σ => imp_congr_right fun _ => ih σ t
  | untl ψ φ ihψ ihφ =>
    intro τ t
    exact exists_congr fun s => and_congr_right fun _ =>
      and_congr (ihφ τ s)
        (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ r)
  | snce ψ φ ihψ ihφ =>
    intro τ t
    exact exists_congr fun s => and_congr_right fun _ =>
      and_congr (ihφ τ s)
        (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ r)

/-- The context-level form of the bridge. -/
theorem starTruthAt_ofCtx (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration)
    {Γ : Context} (h : ∀ ψ ∈ Γ, TruthAt M τ t ψ) :
    ∀ ψ ∈ ofCtx Γ, StarTruthAt M τ t ψ := by
  intro ψ hψ
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp hψ
  exact (starTruthAt_ofFormula M χ τ t).mpr (h χ hχ)

/-- **Transfer at a bare frame predicate.** L⋆ validity of an embedded L⁺ formula over the frames
satisfying `P` is L⁺ validity over the same frames. -/
theorem starValidOnFrames_ofFormula_iff (P : TaskFrame → Prop) (φ : Formula) :
    StarValidOnFrames P (ofFormula φ) ↔ ValidOnFrames P φ := by
  constructor
  · intro h
    refine ValidOnFrames.of_forall_total ?_
    intro F hF M τ hτ t
    exact (starTruthAt_ofFormula M φ τ t).mp (StarValidOnFrames.apply_total h F hF M τ hτ t)
  · intro h
    refine StarValidOnFrames.of_forall_total ?_
    intro F hF M τ hτ t
    exact (starTruthAt_ofFormula M φ τ t).mpr (ValidOnFrames.apply_total h F hF M τ hτ t)

/--
**Semantic conservativity of L⋆ over L⁺, at every frame class.** An L⁺ formula is L⋆-valid over
the frames of `fc` iff it is L⁺-valid over them. `starValidOnFrames_ofFormula_iff` at `fc.Sat`.
-/
theorem starValidIn_ofFormula_iff (fc : ProofSystem.FrameClass) (φ : Formula) :
    StarValidIn fc (ofFormula φ) ↔ ValidIn fc φ :=
  starValidOnFrames_ofFormula_iff fc.Sat φ

/-- Semantic conservativity at the unconstrained class: `starValidIn_ofFormula_iff` at `.Base`. -/
theorem starValid_ofFormula_iff (φ : Formula) : StarValid (ofFormula φ) ↔ Valid φ :=
  starValidIn_ofFormula_iff ProofSystem.FrameClass.Base φ

end FormalSystem.Semantics
