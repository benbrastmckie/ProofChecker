/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Axioms
import FormalSystem.Semantics.StarValidity
import FormalSystem.Metalogic.Conservativity.Plus.AxiomValidity

/-!
# Validity and swap-validity of every TM⋆ axiom schema

The two dispatch lemmas of TM⋆ soundness, one arm per `StarAxiom` constructor and **no wildcard
arm** — so that a constructor added to `StarAxiom` fails the build here until its arm is
supplied:

- `starAxiom_validIn_min` — every schema is valid at its own `minFrameClass`;
- `starAxiom_swap_validIn_min` — every schema's temporal dual is valid at its own
  `minFrameClass`.

The second is what makes the `temporal_duality` rule sound **semantically**
(`Conservativity/Star/StarSoundness.lean`, the companion recursion). No proof-theoretic mirror
argument is used, and — as everywhere in this tree — no argument by uniform substitution: TM⁺ is
already not substitution-closed via `PlusAxiom.atom_stab`, and nothing here needs it.

## How the arms close

- **The `ofBase` arm is two lines, in each lemma.** `starValidOnFrames_ofPlus`
  (`Semantics/StarValidity.lean`) says L⋆ validity of an embedded formula *is* L⁺ validity, so
  the whole TM⁺ schema block transports from `plusAxiom_validIn_min` /
  `plusAxiom_swap_validIn_min` without re-proving a single schema. This is the return on the
  `ofBase` design.

  **No L⋆ atomization is used, and none can exist.** The TM⁺ arms of `plusAxiom_validIn_min` go
  through `Conservativity/Plus/Atomization.lean`, which rests on `stab_state_only` — the
  invariant `StarFormula` is built to break. The transport above consumes `plusAxiom_validIn_min`
  as a black box at `PlusFormula`, and never lifts the atomization itself to `StarFormula`.

- **The sixteen register arms** are the named `starValid_*` lemmas below, one per constructor,
  proved directly from the two clauses of `def:BLstar-semantics`. Ten of them are definitional
  (`Iff.rfl`, or one `Function.update` identity); the four rigidity arms use forward and backward
  seriality; the two export arms are a six-line `constructor`.

- **The swap arms reuse the validity arms.** Every register schema's temporal dual is an
  instance of a constructor of the same inductive — the ten `.iff` schemata are self-dual, the
  four rigidity arms pair G↔H, and the two export arms pair U↔S — so each swap arm normalises
  `swapTemporal` through the `StarFormula.swap_temporal_*` family and then applies the matching
  validity lemma at swapped arguments. That is the swap-closure invariant of
  `StarLanguage/Axioms.lean`, discharged.

## References

* `FormalSystem/Metalogic/Conservativity/Plus/AxiomValidity.lean` — the TM⁺ dispatch pair being
  transported, and the dispatch shape being mirrored
* `FormalSystem/StarLanguage/Axioms.lean` — `StarAxiom` and its swap-closure invariant
* JPL paper `possible_worlds.tex` — `def:BLstar-semantics`

## Tags

soundness · star-language · axiom-validity · store-recall
-/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.PlusLanguage
open FormalSystem.StarLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic

/-! ## Two shape adapters

The `.iff` clause lemma for `StarTruthAt`, and the `StarValid`-at-an-`.iff` introduction rule
every register arm below is stated through. They live here rather than in
`Semantics/StarTruth.lean` because every consumer is in this directory. -/

/-- The `.iff` clause lemma, in the shape of the `StarTruth.*_iff` family. -/
theorem starTruth_iff_iff {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (t : F.Duration) (v : ℕ → F.Duration) (φ ψ : StarFormula) :
    StarTruthAt M τ t v (φ.iff ψ) ↔ (StarTruthAt M τ t v φ ↔ StarTruthAt M τ t v ψ) := by
  simp only [StarFormula.iff, StarTruth.and_iff, StarTruth.imp_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Introduce `StarValid (φ.iff ψ)` from a pointwise biconditional. -/
theorem starValid_iff_of_forall {φ ψ : StarFormula}
    (h : ∀ (F : TaskFrame) (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal →
           ∀ (x : F.Duration) (v : ℕ → F.Duration),
             (StarTruthAt M τ x v φ ↔ StarTruthAt M τ x v ψ)) :
    StarValid (φ.iff ψ) :=
  StarValid.of_forall_total fun F M τ hτ x v =>
    (starTruth_iff_iff M τ x v φ ψ).mpr (h F M τ hτ x v)

/-! ## The sixteen register schemata

Each is valid over **every** task frame, hence stated as `StarValid`. -/

/-- S1: `↑ⁱ↓ⁱφ ↔ ↑ⁱφ` — register `i` of `v⃗[i ↦ x]` is `x`. -/
theorem starValid_store_recall_same (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeStore i (.timeRecall i φ)).iff (.timeStore i φ)) := by
  refine starValid_iff_of_forall fun F M τ _ x v => ?_
  rw [StarTruth.timeStore_iff, StarTruth.timeRecall_iff, Function.update_self,
    StarTruth.timeStore_iff]

/-- S2: `↓ⁱ↑ⁱφ ↔ ↓ⁱφ` — writing `v⃗ᵢ` into register `i` writes back what was there. -/
theorem starValid_recall_store_same (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeRecall i (.timeStore i φ)).iff (.timeRecall i φ)) := by
  refine starValid_iff_of_forall fun F M τ _ x v => ?_
  rw [StarTruth.timeRecall_iff, StarTruth.timeStore_iff, Function.update_eq_self,
    StarTruth.timeRecall_iff]

/-- S3: `↓ⁱ↓ʲφ ↔ ↓ʲφ` — the inner recall overrides the outer one. -/
theorem starValid_recall_recall (i j : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeRecall i (.timeRecall j φ)).iff (.timeRecall j φ)) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S4: `↑ⁱ↑ʲφ ↔ ↑ʲ↑ⁱφ` — both stores write the same time, so the updates commute. -/
theorem starValid_store_store_comm (i j : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeStore i (.timeStore j φ)).iff
      (StarFormula.timeStore j (.timeStore i φ))) := by
  refine starValid_iff_of_forall fun F M τ _ x v => ?_
  simp only [StarTruth.timeStore_iff]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [Function.update_comm hij x x v]

/-- S5: `↑ⁱ(φ → ψ) ↔ (↑ⁱφ → ↑ⁱψ)` — `↑ⁱ` is functional. -/
theorem starValid_store_k (i : ℕ) (φ ψ : StarFormula) :
    StarValid ((StarFormula.timeStore i (φ.imp ψ)).iff
      ((StarFormula.timeStore i φ).imp (.timeStore i ψ))) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S5, recall half: `↓ⁱ(φ → ψ) ↔ (↓ⁱφ → ↓ⁱψ)`. -/
theorem starValid_recall_k (i : ℕ) (φ ψ : StarFormula) :
    StarValid ((StarFormula.timeRecall i (φ.imp ψ)).iff
      ((StarFormula.timeRecall i φ).imp (.timeRecall i ψ))) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S6: `↑ⁱ□φ ↔ □↑ⁱφ` — `□` moves the history, never the time or the vector. -/
theorem starValid_store_box (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeStore i (.box φ)).iff (StarFormula.box (.timeStore i φ))) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S6, recall half: `↓ⁱ□φ ↔ □↓ⁱφ`. -/
theorem starValid_recall_box (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeRecall i (.box φ)).iff (StarFormula.box (.timeRecall i φ))) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S7: `↑ⁱ⊡φ ↔ ⊡↑ⁱφ` — `⊡`'s same-state condition is taken at the time `↑ⁱ` writes. The recall
analogue `↓ⁱ⊡φ ↔ ⊡↓ⁱφ` is **refuted** and is deliberately not among the schemata. -/
theorem starValid_store_stab (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeStore i (.stab φ)).iff (StarFormula.stab (.timeStore i φ))) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S9: `↑ⁱp ↔ p` for atoms — the atom clause does not read the register vector. -/
theorem starValid_store_atom (i : ℕ) (p : Atom) :
    StarValid ((StarFormula.timeStore i (.atom p)).iff (StarFormula.atom p)) :=
  starValid_iff_of_forall fun _ _ _ _ _ _ => Iff.rfl

/-- S8: `↓ⁱφ → G↓ⁱφ` — a recall's truth does not read the time of evaluation. -/
theorem starValid_recall_rigid_future (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeRecall i φ).imp
      (StarFormula.allFuture (.timeRecall i φ))) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  rw [StarTruth.allFuture_iff]
  intro s _
  exact h

/-- S8, converse: `G↓ⁱφ → ↓ⁱφ`, by forward seriality (`exists_gt`). -/
theorem starValid_future_rigid_recall (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.allFuture (.timeRecall i φ)).imp
      (StarFormula.timeRecall i φ)) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  rw [StarTruth.allFuture_iff] at h
  obtain ⟨y, hy⟩ := exists_gt x
  exact h y hy

/-- S8, past half: `↓ⁱφ → H↓ⁱφ`. -/
theorem starValid_recall_rigid_past (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.timeRecall i φ).imp
      (StarFormula.allPast (.timeRecall i φ))) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  rw [StarTruth.allPast_iff]
  intro s _
  exact h

/-- S8, past converse: `H↓ⁱφ → ↓ⁱφ`, by backward seriality (`exists_lt`). -/
theorem starValid_past_rigid_recall (i : ℕ) (φ : StarFormula) :
    StarValid ((StarFormula.allPast (.timeRecall i φ)).imp
      (StarFormula.timeRecall i φ)) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  rw [StarTruth.allPast_iff] at h
  obtain ⟨y, hy⟩ := exists_lt x
  exact h y hy

/-- S10: `ψ U ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ U ⊤))` — a rigid event contributes nothing to the `until` beyond
the existence of the interval. -/
theorem starValid_recall_export_until (i : ℕ) (φ ψ : StarFormula) :
    StarValid ((StarFormula.untl ψ (.timeRecall i φ)).iff
      ((StarFormula.timeRecall i φ).and (StarFormula.untl ψ StarFormula.top))) := by
  refine starValid_iff_of_forall fun F M τ _ x v => ?_
  rw [StarTruth.and_iff]
  simp only [StarTruth.untl_iff, StarTruth.timeRecall_iff]
  constructor
  · rintro ⟨s, hs, hev, hg⟩
    exact ⟨hev, s, hs, StarTruth.top_true M τ s v, hg⟩
  · rintro ⟨hrec, s, hs, _, hg⟩
    exact ⟨s, hs, hrec, hg⟩

/-- S10, past mirror: `ψ S ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ S ⊤))`. -/
theorem starValid_recall_export_since (i : ℕ) (φ ψ : StarFormula) :
    StarValid ((StarFormula.snce ψ (.timeRecall i φ)).iff
      ((StarFormula.timeRecall i φ).and (StarFormula.snce ψ StarFormula.top))) := by
  refine starValid_iff_of_forall fun F M τ _ x v => ?_
  rw [StarTruth.and_iff]
  simp only [StarTruth.snce_iff, StarTruth.timeRecall_iff]
  constructor
  · rintro ⟨s, hs, hev, hg⟩
    exact ⟨hev, s, hs, StarTruth.top_true M τ s v, hg⟩
  · rintro ⟨hrec, s, hs, _, hg⟩
    exact ⟨s, hs, hrec, hg⟩

/-! ## Validity -/

/-- **Every TM⋆ schema is valid at its own minimum frame class.** One arm per constructor, no
wildcard. -/
theorem starAxiom_validIn_min {φ : StarFormula} (ax : StarAxiom φ) :
    StarValidIn ax.minFrameClass φ := by
  cases ax with
  | ofBase ψ ax => exact (starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min ax)
  | store_recall_same i φ => exact starValid_store_recall_same i φ
  | recall_store_same i φ => exact starValid_recall_store_same i φ
  | recall_recall i j φ => exact starValid_recall_recall i j φ
  | store_store_comm i j φ => exact starValid_store_store_comm i j φ
  | store_k i φ ψ => exact starValid_store_k i φ ψ
  | recall_k i φ ψ => exact starValid_recall_k i φ ψ
  | store_box i φ => exact starValid_store_box i φ
  | recall_box i φ => exact starValid_recall_box i φ
  | store_stab i φ => exact starValid_store_stab i φ
  | store_atom i p => exact starValid_store_atom i p
  | recall_rigid_future i φ => exact starValid_recall_rigid_future i φ
  | future_rigid_recall i φ => exact starValid_future_rigid_recall i φ
  | recall_rigid_past i φ => exact starValid_recall_rigid_past i φ
  | past_rigid_recall i φ => exact starValid_past_rigid_recall i φ
  | recall_export_until i φ ψ => exact starValid_recall_export_until i φ ψ
  | recall_export_since i φ ψ => exact starValid_recall_export_since i φ ψ

/-- Validity of a TM⋆ schema at any class admitting it. -/
theorem starAxiom_validIn {φ : StarFormula} {fc : FrameClass} (ax : StarAxiom φ)
    (h : ax.minFrameClass ≤ fc) : StarValidIn fc φ :=
  StarValidIn.mono h (starAxiom_validIn_min ax)

/-! ## Swap-validity -/

/-- **Every TM⋆ schema's temporal dual is valid at its own minimum frame class.** One arm per
constructor; the semantic input to the `temporal_duality` case of soundness. Each register arm
normalises `swapTemporal` and lands on the matching validity lemma — the swap-closure invariant
of `StarLanguage/Axioms.lean`, discharged constructor by constructor. -/
theorem starAxiom_swap_validIn_min {φ : StarFormula} (ax : StarAxiom φ) :
    StarValidIn ax.minFrameClass φ.swapTemporal := by
  cases ax with
  | ofBase ψ ax =>
    rw [← ofPlus_swapTemporal]
    exact (starValidOnFrames_ofPlus _ _).mpr (plusAxiom_swap_validIn_min ax)
  | store_recall_same i φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_recall_same i φ.swapTemporal
  | recall_store_same i φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_recall_store_same i φ.swapTemporal
  | recall_recall i j φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_recall_recall i j φ.swapTemporal
  | store_store_comm i j φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_store_comm i j φ.swapTemporal
  | store_k i φ ψ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_k i φ.swapTemporal ψ.swapTemporal
  | recall_k i φ ψ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_recall_k i φ.swapTemporal ψ.swapTemporal
  | store_box i φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_box i φ.swapTemporal
  | recall_box i φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_recall_box i φ.swapTemporal
  | store_stab i φ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_stab i φ.swapTemporal
  | store_atom i p =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swapTemporal]
    exact starValid_store_atom i p
  | recall_rigid_future i φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_future]
    exact starValid_recall_rigid_past i φ.swapTemporal
  | future_rigid_recall i φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_future]
    exact starValid_past_rigid_recall i φ.swapTemporal
  | recall_rigid_past i φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_past]
    exact starValid_recall_rigid_future i φ.swapTemporal
  | past_rigid_recall i φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_past]
    exact starValid_future_rigid_recall i φ.swapTemporal
  | recall_export_until i φ ψ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swap_temporal_and,
      StarFormula.swap_temporal_top, StarFormula.swapTemporal]
    exact starValid_recall_export_since i φ.swapTemporal ψ.swapTemporal
  | recall_export_since i φ ψ =>
    simp only [StarFormula.swap_temporal_iff, StarFormula.swap_temporal_and,
      StarFormula.swap_temporal_top, StarFormula.swapTemporal]
    exact starValid_recall_export_until i φ.swapTemporal ψ.swapTemporal

/-- Swap-validity of a TM⋆ schema at any class admitting it. -/
theorem starAxiom_swap_validIn {φ : StarFormula} {fc : FrameClass} (ax : StarAxiom φ)
    (h : ax.minFrameClass ≤ fc) : StarValidIn fc φ.swapTemporal :=
  StarValidIn.mono h (starAxiom_swap_validIn_min ax)

end FormalSystem.Metalogic.Conservativity
