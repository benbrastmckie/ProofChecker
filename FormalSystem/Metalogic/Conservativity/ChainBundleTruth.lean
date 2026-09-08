/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.BaseLanguageSoundness
import FormalSystem.Metalogic.Algebraic.FlowFrame

/-!
# The valuation-only chain-bundle truth lemma

A base-language formula evaluated on the flow frames of `Metalogic/Algebraic/FlowFrame.lean` can
see only a very simple Kripke structure: an indexed family of copies of the duration order, with
`H`/`G` quantifying *within* a copy and `□` quantifying over *everything*. This module states that
structure as a bare satisfaction predicate `chainSat` over `FamIdx × ↑D` — no maximal-consistent
sets, no proof-theoretic data, just a valuation — and proves that `BLTruthAt` along a translate
history agrees with it pointwise.

## Why `□` is universal and carries no time argument

`chainSat`'s `box` clause is `∀ q', chainSat v q' φ`, quantifying **both** coordinates and taking
no time argument at all. That is not a simplification: it is what
`Conservativity/BaseLanguageSoundness.lean`'s `bl_box_universal` establishes. `BLTruthAt`'s box
clause is history-blind by definition (it does not mention `τ`) and time-blind by
`Semantics.Truth.box_const`, so `□φ` holds at one total history-and-time exactly when `φ` holds at
every total history and every time. On a flow frame the total histories are *exactly* the
translates (`multiFamGen_total_eq_range`), so "every total history, every time" is "every point of
`FamIdx × ↑D`".

A `box` clause carrying a time argument would therefore be a mis-transcription, and would make BL
over task frames look like a product logic with same-time alignment validities, which it is not.

## What this module is, and what it is not

It is **the transfer half** of the standard route to a completeness theorem over the dense or
Dedekind classes: given a chain-model refutation of `φ`, produce a task-frame refutation. That
half is closed here, generically in `D` and `FamIdx`, and `not_blValidIn_of_not_chainSat` is the
single interface any future canonical-model work consumes. The frame construction the route also
needs was already in-tree and generic (`multiFamTaskFrameGen` discharges all four frame axioms for
an arbitrary temporal order), so no frame-building appears here either.

It is **not** a completeness proof and does not approach one. The missing content is entirely on
the other side: a canonical model built from base-language maximal-consistent sets, canonicity for
the eleven Base axioms plus `DN`, bulldozing, and a countable-ℚ realization. None of that is here,
no theorem in this module concludes in `TMComplete _` or `Forward _`, and the standing prohibition
in `Metalogic/Conservativity.lean` — never state a completeness or forward-conservativity theorem
and discharge it with `sorry` — applies in full. The current four-row status is recorded in
`Conservativity/TMCompletenessReduction.lean`'s module docstring.

In particular, the converse of `not_blValidIn_of_not_chainSat` is **not** proved and is not
available: nothing here says that a formula underivable in the system has a chain-model
refutation. That implication is the completeness direction itself.

## Main Results

- `chainSat` — Kripke satisfaction on a disjoint union of `D`-chains, with `□` universal over all
  points and `H`/`G` quantifying the second coordinate within a fixed first coordinate
- `chainBundle_truth_lemma` — `BLTruthAt` along `multiFamHistoryGen f w₀` at time `t` matches
  `chainSat` at the point `(f, w₀ + t)`
- `not_blValidIn_of_not_chainSat` — the transfer corollary: a chain-model refutation refutes
  `BLValidIn fc` at every `fc` the flow frame satisfies
- `not_blValidDense_of_not_chainSat`, `not_blValidRTime_of_not_chainSat` — its instantiations at
  ℚ and at ℝ, so the transfer step is closed for both of the two open rows

## References

* `FormalSystem/Metalogic/Algebraic/FlowFrame.lean` — `multiFamTaskFrameGen`,
  `multiFamHistoryGen`, `multiFamHistoryGen_total`, `multiFamGen_total_eq_range`
* `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` — `bl_box_universal`
* `FormalSystem/Semantics/BLTruth.lean` — the six `BLTruthAt` clauses `chainSat` mirrors
* `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — the four-row status table

## Tags

chain-bundle · truth-lemma · flow-frame · universal-modality · base-language
-/

namespace FormalSystem.Metalogic

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.BaseLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic.Algebraic

variable {D : TemporalOrder} {FamIdx : Type} [Nonempty FamIdx]

/--
**Kripke satisfaction on a disjoint union of `D`-chains.**

Points are pairs `(f, x)`: `f` names the chain, `x` the position along it. Six clauses, one per
`BLFormula` constructor, mirroring `Semantics.BLTruthAt`:

* `atom` — read off the bare valuation `v`. Unlike `BLTruthAt`'s atom clause there is no domain
  side condition, because a chain point is always in the "domain" of its own chain.
* `bot`, `imp` — as usual.
* `box` — `∀ q', chainSat v q' φ`, over **all** points of **all** chains, with no time argument.
  See the module docstring: this is `bl_box_universal`, not a simplification.
* `allPast`, `allFuture` — quantify the second coordinate strictly below/above `q.2`, holding the
  first coordinate `q.1` fixed. This is the sense in which the chains are disjoint for `H`/`G`
  while being merged for `□`.
-/
def chainSat (v : FamIdx × (D : Type) → Atom → Prop) :
    FamIdx × (D : Type) → BLFormula → Prop
  | q, .atom p => v q p
  | _, .bot => False
  | q, .imp φ ψ => chainSat v q φ → chainSat v q ψ
  | _, .box φ => ∀ q' : FamIdx × (D : Type), chainSat v q' φ
  | q, .allPast φ => ∀ s : (D : Type), s < q.2 → chainSat v (q.1, s) φ
  | q, .allFuture φ => ∀ s : (D : Type), q.2 < s → chainSat v (q.1, s) φ

/--
**The truth lemma.** BL truth along the translate history `multiFamHistoryGen f w₀`, at time `t`,
is `chainSat` at the point `(f, w₀ + t)`.

Induction on `φ`, `generalizing f w₀ t` — mandatory, since three of the six cases need the
hypothesis at a different point: `box` at a different chain *and* a different base point,
`allPast`/`allFuture` at a different time.

Case by case:

* `atom` — the model's valuation at `multiFamHistoryGen f w₀`'s state at `t`, which is
  definitionally `(f, w₀ + t)`. The domain conjunct is `trivial` (`multiFamHistoryGen` carries
  `domain := fun _ => True`).
* `bot`, `imp` — `Iff.rfl` and congruence.
* `box` — the two interesting halves. Forwards, `bl_box_universal` turns `□φ` at `(τ, t)` into
  truth at *every* total history and *every* time, so it can be instantiated at
  `multiFamHistoryGen q'.1 q'.2` and time `0`, landing on `chainSat v (q'.1, q'.2 + 0)`.
  Backwards, an arbitrary total `σ` is a translate by `multiFamGen_total_eq_range`, and the
  hypothesis covers every point.
* `allPast`, `allFuture` — the quantified variable is reindexed along the order-isomorphism
  `s ↦ w₀ + s` of `↑D`, whose two directions are `lt_of_add_lt_add_left` and
  `add_lt_add_iff_left`. This is where the chains stay separate: the translation moves the
  position within the chain `f` and never leaves it.
-/
theorem chainBundle_truth_lemma (M : TaskModel (multiFamTaskFrameGen D FamIdx))
    (f : FamIdx) (w₀ t : (D : Type)) (φ : BLFormula) :
    BLTruthAt M (multiFamHistoryGen (D := D) f w₀) t φ ↔ chainSat M.valuation (f, w₀ + t) φ := by
  induction φ generalizing f w₀ t with
  | atom p =>
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨trivial, h⟩
  | bot => exact Iff.rfl
  | imp φ ψ ih1 ih2 => exact imp_congr (ih1 f w₀ t) (ih2 f w₀ t)
  | box φ ih =>
      constructor
      · intro h q'
        have huniv := (bl_box_universal M _ t (multiFamHistoryGen_total f w₀) φ).mp h
        have hq := (ih q'.1 q'.2 0).mp
          (huniv (multiFamHistoryGen q'.1 q'.2) (multiFamHistoryGen_total _ _) 0)
        simpa using hq
      · intro h σ hσ
        have hmem :
            σ ∈ Set.range (fun (p : FamIdx × (D : Type)) => multiFamHistoryGen p.1 p.2) := by
          rw [← multiFamGen_total_eq_range (D := D) FamIdx]; exact hσ
        obtain ⟨⟨f', w₀'⟩, rfl⟩ := hmem
        exact (ih f' w₀' t).mpr (h (f', w₀' + t))
  | allPast φ ih =>
      constructor
      · intro h u hu
        have hlt : w₀ + (u - w₀) < w₀ + t := by simpa using hu
        have hu' := (ih f w₀ (u - w₀)).mp (h (u - w₀) (lt_of_add_lt_add_left hlt))
        simpa using hu'
      · intro h s hs
        exact (ih f w₀ s).mpr (h (w₀ + s) (show w₀ + s < w₀ + t from
          (add_lt_add_iff_left w₀).mpr hs))
  | allFuture φ ih =>
      constructor
      · intro h u hu
        have hlt : w₀ + t < w₀ + (u - w₀) := by simpa using hu
        have hu' := (ih f w₀ (u - w₀)).mp (h (u - w₀) (lt_of_add_lt_add_left hlt))
        simpa using hu'
      · intro h s hs
        exact (ih f w₀ s).mpr (h (w₀ + s) (show w₀ + t < w₀ + s from
          (add_lt_add_iff_left w₀).mpr hs))

end FormalSystem.Metalogic
