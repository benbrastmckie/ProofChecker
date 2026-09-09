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

/-! ## The TM⁺ mirror block — Layer 1 (propositional), Layer 2 (S5 modal), and the `⊡` S5 block

Each of these is the schema of the correspondingly named `StarAxiom` constructor, proved
**directly against `StarTruthAt`** at arbitrary `StarFormula` metavariables — not transported
from `PlusAxiom`, which reaches only `ofPlus` instances.

**No L⋆ atomization, and no uniform substitution.** Both routes are prohibited here and
throughout this file: the first does not exist (`stab_state_only` has no L⋆ analogue, see the
module docstring), and the second is unsound over TM⁺, which `atom_stab` already makes
non-substitution-closed. Every arm below is a fresh direct proof. -/

/-- Propositional K over L⋆. Mirror of `PlusAxiom.prop_k`'s validity. -/
theorem starValid_prop_k (φ ψ χ : StarFormula) :
    StarValid ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h1 h2 h3 => h1 h3 (h2 h3)

/-- Propositional S (weakening) over L⋆. -/
theorem starValid_prop_s (φ ψ : StarFormula) : StarValid (φ.imp (ψ.imp φ)) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h _ => h

/-- Ex Falso Quodlibet over L⋆. -/
theorem starValid_ex_falso (φ : StarFormula) : StarValid (StarFormula.bot.imp φ) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h => h.elim

/-- Peirce's Law over L⋆, by classical case analysis on `φ`. -/
theorem starValid_peirce (φ ψ : StarFormula) : StarValid (((φ.imp ψ).imp φ).imp φ) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  by_cases hφ : StarTruthAt M τ x v φ
  · exact hφ
  · exact h fun hp => absurd hp hφ

/-- Modal T over L⋆: the evaluation history is itself total, so `□` reflects. -/
theorem starValid_modal_t (φ : StarFormula) : StarValid ((StarFormula.box φ).imp φ) :=
  StarValid.of_forall_total fun _ _ τ hτ _ _ h => h τ hτ

/-- Modal 4 over L⋆: the `box` clause quantifies over all total histories, so it is idempotent. -/
theorem starValid_modal_4 (φ : StarFormula) :
    StarValid ((StarFormula.box φ).imp (StarFormula.box (StarFormula.box φ))) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h _ _ => h

/-- Modal B over L⋆. -/
theorem starValid_modal_b (φ : StarFormula) :
    StarValid (φ.imp (StarFormula.box φ.diamond)) := by
  refine StarValid.of_forall_total fun F M τ hτ x v h => ?_
  intro σ _
  rw [StarTruth.diamond_iff]
  exact ⟨τ, hτ, h⟩

/-- Modal 5 Collapse over L⋆. -/
theorem starValid_modal_5_collapse (φ : StarFormula) :
    StarValid (φ.box.diamond.imp φ.box) := by
  refine StarValid.of_forall_total fun F M τ _ x v h => ?_
  rw [StarTruth.diamond_iff] at h
  obtain ⟨σ, hσ, hb⟩ := h
  exact hb

/-- Modal K distribution over L⋆. -/
theorem starValid_modal_k_dist (φ ψ : StarFormula) :
    StarValid ((φ.imp ψ).box.imp (φ.box.imp ψ.box)) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h1 h2 σ hσ => h1 σ hσ (h2 σ hσ)

/-- SK over L⋆: K for `⊡`, from the universal-quantifier shape of the `stab` clause. -/
theorem starValid_stab_k (φ ψ : StarFormula) :
    StarValid ((StarFormula.stab (φ.imp ψ)).imp
      ((StarFormula.stab φ).imp (StarFormula.stab ψ))) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h1 h2 σ hσ hs => h1 σ hσ hs (h2 σ hσ hs)

/-- ST over L⋆: `SameStateAt` is reflexive. -/
theorem starValid_stab_t (φ : StarFormula) : StarValid ((StarFormula.stab φ).imp φ) :=
  StarValid.of_forall_total fun _ _ τ hτ _ _ h => h τ hτ (SameStateAt.refl τ _)

/-- S4 for `⊡` over L⋆: `SameStateAt` at a fixed time is transitive. -/
theorem starValid_stab_4 (φ : StarFormula) :
    StarValid ((StarFormula.stab φ).imp (StarFormula.stab (StarFormula.stab φ))) := by
  refine StarValid.of_forall_total fun F M τ hτ x v h => ?_
  intro σ hσ hσsame ρ hρ hρsame
  exact h ρ hρ (fun hτ' hρ' => by rw [hσsame hτ' (hσ x), hρsame (hσ x) hρ'])

/-- S5 for `⊡` over L⋆: `SameStateAt` at a fixed time is symmetric. -/
theorem starValid_stab_5 (φ : StarFormula) :
    StarValid ((StarFormula.dstab φ).imp (StarFormula.stab (StarFormula.dstab φ))) := by
  refine StarValid.of_forall_total fun F M τ hτ x v h => ?_
  intro σ hσ hσsame
  rw [StarTruth.dstab_iff] at h ⊢
  obtain ⟨ρ, hρ, hρsame, hφ⟩ := h
  exact ⟨ρ, hρ, fun hσ' hρ' => by rw [← hσsame (hτ x) hσ', ← hρsame (hτ x) hρ'], hφ⟩

/-- MS over L⋆: `⟨τ⟩_x ⊆ H_F`, so `□` is stronger than `⊡` — **at every `φ : StarFormula`**,
registers included. This is the schematic fact that makes `stabNecessitation`
(`StarLanguage/Derivation.lean`) unrestricted. -/
theorem starValid_box_stab (φ : StarFormula) :
    StarValid ((StarFormula.box φ).imp (StarFormula.stab φ)) :=
  StarValid.of_forall_total fun _ _ _ _ _ _ h σ hσ _ => h σ hσ

/-- AS over L⋆: the atom clause reads the world state alone, which `SameStateAt` fixes. -/
theorem starValid_atom_stab (p : Atom) :
    StarValid ((StarFormula.atom p).imp (StarFormula.stab (StarFormula.atom p))) := by
  refine StarValid.of_forall_total fun F M τ hτ x v h => ?_
  intro σ hσ hsame
  rw [StarTruth.atom_iff] at h ⊢
  obtain ⟨ht, hval⟩ := h
  exact ⟨hσ x, by rw [← hsame ht (hσ x)]; exact hval⟩

/-! ## The TM⁺ mirror block — seriality, monotonicity, connection

Transcriptions of the corresponding L-level proofs (`Metalogic/Soundness.lean`) under the
substitution `TruthAt M τ t ↦ StarTruthAt M τ t v`, `Truth.*_iff ↦ StarTruth.*_iff`. The two
seriality schemata are closed formulas, hence literally `ofPlus` images, and transport. -/

/-- Serial future over L⋆. The formula is closed, so it *is* an `ofPlus` image and the L⁺
validity transports along `starValidOnFrames_ofPlus`. -/
theorem starValid_serial_future :
    StarValid ((StarFormula.bot.imp StarFormula.bot).imp
      (StarFormula.someFuture (StarFormula.bot.imp StarFormula.bot))) :=
  (starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min PlusAxiom.serial_future)

/-- Serial past over L⋆, likewise by transport. -/
theorem starValid_serial_past :
    StarValid ((StarFormula.bot.imp StarFormula.bot).imp
      (StarFormula.somePast (StarFormula.bot.imp StarFormula.bot))) :=
  (starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min PlusAxiom.serial_past)

/-- BX2G over L⋆: the guard of an `until` may be weakened under `G`. -/
theorem starValid_left_mono_until_G (φ χ ψ : StarFormula) :
    StarValid ((φ.imp χ).allFuture.imp
      ((StarFormula.untl φ ψ).imp (StarFormula.untl χ ψ))) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allFuture_iff, StarTruth.untl_iff]
  rintro h_G ⟨s, hts, h_event, h_guard⟩
  exact ⟨s, hts, h_event, fun r htr hrs => h_G r htr (h_guard r htr hrs)⟩

/-- BX2H over L⋆, the past mirror of `starValid_left_mono_until_G`. -/
theorem starValid_left_mono_since_H (φ χ ψ : StarFormula) :
    StarValid ((φ.imp χ).allPast.imp
      ((StarFormula.snce φ ψ).imp (StarFormula.snce χ ψ))) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allPast_iff, StarTruth.snce_iff]
  rintro h_H ⟨s, hst, h_event, h_guard⟩
  exact ⟨s, hst, h_event, fun r hsr hrt => h_H r hrt (h_guard r hsr hrt)⟩

/-- BX3 over L⋆: the event of an `until` may be weakened under `G`. -/
theorem starValid_right_mono_until (φ ψ χ : StarFormula) :
    StarValid ((φ.imp ψ).allFuture.imp
      ((StarFormula.untl χ φ).imp (StarFormula.untl χ ψ))) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allFuture_iff, StarTruth.untl_iff]
  rintro h_G ⟨s, hts, h_event, h_guard⟩
  exact ⟨s, hts, h_G s hts h_event, h_guard⟩

/-- BX3' over L⋆, the past mirror of `starValid_right_mono_until`. -/
theorem starValid_right_mono_since (φ ψ χ : StarFormula) :
    StarValid ((φ.imp ψ).allPast.imp
      ((StarFormula.snce χ φ).imp (StarFormula.snce χ ψ))) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allPast_iff, StarTruth.snce_iff]
  rintro h_H ⟨s, hst, h_event, h_guard⟩
  exact ⟨s, hst, h_H s hst h_event, h_guard⟩

/-- BX4 over L⋆: what is true now is always going to have been true. -/
theorem starValid_connect_future (φ : StarFormula) :
    StarValid (φ.imp (φ.somePast.allFuture)) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allFuture_iff, StarTruth.somePast_iff]
  intro h s hts
  exact ⟨t, hts, h⟩

/-- BX4' over L⋆, the past mirror of `starValid_connect_future`. -/
theorem starValid_connect_past (φ : StarFormula) :
    StarValid (φ.imp (φ.someFuture.allPast)) := by
  refine StarValid.of_forall_total fun F M τ _ t v => ?_
  simp only [StarTruth.imp_iff, StarTruth.allPast_iff, StarTruth.someFuture_iff]
  intro h s hst
  exact ⟨t, hst, h⟩

/-! ## Validity -/

/-- **Every TM⋆ schema is valid at its own minimum frame class.** One arm per constructor, no
wildcard. -/
theorem starAxiom_validIn_min {φ : StarFormula} (ax : StarAxiom φ) :
    StarValidIn ax.minFrameClass φ := by
  cases ax with
  | ofBase ψ ax => exact (starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min ax)
  | prop_k φ ψ χ => exact starValid_prop_k φ ψ χ
  | prop_s φ ψ => exact starValid_prop_s φ ψ
  | ex_falso φ => exact starValid_ex_falso φ
  | peirce φ ψ => exact starValid_peirce φ ψ
  | modal_t φ => exact starValid_modal_t φ
  | modal_4 φ => exact starValid_modal_4 φ
  | modal_b φ => exact starValid_modal_b φ
  | modal_5_collapse φ => exact starValid_modal_5_collapse φ
  | modal_k_dist φ ψ => exact starValid_modal_k_dist φ ψ
  | stab_k φ ψ => exact starValid_stab_k φ ψ
  | stab_t φ => exact starValid_stab_t φ
  | stab_4 φ => exact starValid_stab_4 φ
  | stab_5 φ => exact starValid_stab_5 φ
  | box_stab φ => exact starValid_box_stab φ
  | atom_stab p => exact starValid_atom_stab p
  | serial_future => exact starValid_serial_future
  | serial_past => exact starValid_serial_past
  | left_mono_until_G φ χ ψ => exact starValid_left_mono_until_G φ χ ψ
  | left_mono_since_H φ χ ψ => exact starValid_left_mono_since_H φ χ ψ
  | right_mono_until φ ψ χ => exact starValid_right_mono_until φ ψ χ
  | right_mono_since φ ψ χ => exact starValid_right_mono_since φ ψ χ
  | connect_future φ => exact starValid_connect_future φ
  | connect_past φ => exact starValid_connect_past φ
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
  | prop_k φ ψ χ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_prop_k φ.swapTemporal ψ.swapTemporal χ.swapTemporal
  | prop_s φ ψ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_prop_s φ.swapTemporal ψ.swapTemporal
  | ex_falso φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_ex_falso φ.swapTemporal
  | peirce φ ψ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_peirce φ.swapTemporal ψ.swapTemporal
  | modal_t φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_modal_t φ.swapTemporal
  | modal_4 φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_modal_4 φ.swapTemporal
  | modal_b φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_diamond]
    exact starValid_modal_b φ.swapTemporal
  | modal_5_collapse φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_diamond]
    exact starValid_modal_5_collapse φ.swapTemporal
  | modal_k_dist φ ψ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_modal_k_dist φ.swapTemporal ψ.swapTemporal
  | stab_k φ ψ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_stab_k φ.swapTemporal ψ.swapTemporal
  | stab_t φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_stab_t φ.swapTemporal
  | stab_4 φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_stab_4 φ.swapTemporal
  | stab_5 φ =>
    simp only [StarFormula.swap_temporal_dstab, StarFormula.swapTemporal]
    exact starValid_stab_5 φ.swapTemporal
  | box_stab φ =>
    simp only [StarFormula.swapTemporal]
    exact starValid_box_stab φ.swapTemporal
  | atom_stab p =>
    simp only [StarFormula.swapTemporal]
    exact starValid_atom_stab p
  | serial_future =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_some_future]
    exact starValid_serial_past
  | serial_past =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_some_past]
    exact starValid_serial_future
  | left_mono_until_G φ χ ψ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_future]
    exact starValid_left_mono_since_H φ.swapTemporal χ.swapTemporal ψ.swapTemporal
  | left_mono_since_H φ χ ψ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_past]
    exact starValid_left_mono_until_G φ.swapTemporal χ.swapTemporal ψ.swapTemporal
  | right_mono_until φ ψ χ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_future]
    exact starValid_right_mono_since φ.swapTemporal ψ.swapTemporal χ.swapTemporal
  | right_mono_since φ ψ χ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_past]
    exact starValid_right_mono_until φ.swapTemporal ψ.swapTemporal χ.swapTemporal
  | connect_future φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_future,
      StarFormula.swap_temporal_some_past]
    exact starValid_connect_past φ.swapTemporal
  | connect_past φ =>
    simp only [StarFormula.swapTemporal, StarFormula.swap_temporal_all_past,
      StarFormula.swap_temporal_some_future]
    exact starValid_connect_future φ.swapTemporal
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
