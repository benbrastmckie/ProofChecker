/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Bundle.LimitMCS

/-!
# LimitMCSCoherence: temporal coherence across the rational/limit case matrix

The real extension of a rational family of maximal consistent sets does not take the limit set
everywhere. At a point whose shifted coordinate is (the cast of) a rational it *selects* the
rational family's own set; only elsewhere does it take the left limit. See
`Bundle/LimitMCS.lean`'s module docstring for why: agreement between `limitSetBelow m (q : ℝ)`
and `m q` fails in both directions, so "extends rather than replaces" has to be arranged by
construction rather than obtained as a lemma.

Consequently the two temporal coherence conditions of `FMCS` (`Bundle/FMCSDef.lean`) each face
a 2x2 matrix of cases, according to whether the *source* point and the *target* point are
selected (rational) or unselected (limit):

| | target selected | target unselected |
|---|---|---|
| **source selected** | G3 / H3 — no lemma needed | G1 / H1 |
| **source unselected** | G2 / H2 | G4 / H4 |

This module proves the surviving cases of that matrix. Each is stated about `limitSetBelow` and
takes the rational family's coherence field as an **explicit hypothesis**, so nothing here
presupposes maximality of the limit set and nothing here depends on how maximality is obtained.
The four unselected-source cases (G2, G4, H2, H4) are retired -- see
`Boneyard/LimitMCSCoherenceDeadCases/README.md` -- along with the `t = (q : ℝ)` corollary of H1;
`Bundle/RealExtension.lean` consumes only the source-rational cases (G1, H1) and the
`limitMCSBelow`-source variants below.

## The two cases with no lemma

Cases **G3** and **H3** (selected source, selected target) need **no lemma in this module, by
design**. Both points are then of the form `(q : ℝ)` for a rational `q`, the extension's value
at each is the rational family's own `m q`, and the required implication is the family's
`forward_G` (resp. `backward_H`) field verbatim, modulo `Rat.cast_lt` to move the order
hypothesis between `ℝ` and `Rat`. Do not go looking for `..._forward_G_rat_rat`; it deliberately
does not exist.

## Main results

- `limitSetBelow_forward_G_rat_source` (G1), `limitSetBelow_backward_H_rat_source` (H1).
- The four unselected-source cases with an ultrafilter-limit hypothesis:
  `limitMCSBelow_forward_G_rat_target` (G2), `limitMCSBelow_forward_G_limit` (G4),
  `limitMCSBelow_backward_H_rat_target` (H2), `limitMCSBelow_backward_H_limit` (H4). These are
  the forms the real extension of `Bundle/RealExtension.lean` actually consumes, since it takes
  the ultrafilter limit at unselected points; see the section comment introducing them.

## Notes on the statements

**No offset.** The families of the real bundle carry a real offset `δ`, and the coherence
obligations are stated at shifted coordinates `x + δ < y + δ`. That offset is absorbed by
`add_lt_add_right` at the point of use, so every lemma here is stated without it, at bare real
arguments.

**H1 subsumes `limitSetBelow_of_rat`.** `limitSetBelow_backward_H_rat_source` is stated with
`t ≤ (q : ℝ)` rather than `t < (q : ℝ)`: the strict case is the coherence matrix's case H1, and
the case `t = (q : ℝ)` is exactly `limitSetBelow_of_rat` (`Bundle/LimitMCS.lean`), which remains
standing (its own explicit corollary here was retired -- both are one-liners from the `≤` form).
Its `forward_G` mirror image admits no such widening: at `t = (q : ℝ)` the left limit at `t`
sees only rationals strictly *below* `q`, about which `allFuture φ ∈ m q` says nothing.

**The past-side limit set plays no role here.** `limitSetAbove` and its `Bundle/LimitMCS.lean`
duals are standing assets but are not used on this route: the real extension takes the *left*
limit at unselected points, so both `forward_G` and `backward_H` go through `limitSetBelow`.
-/

namespace FormalSystem.Metalogic.Bundle

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.Metalogic.Core

/-! ## Forward G coherence -/

/--
**Case G1 (selected source, unselected target).** If the rational family asserts `allFuture φ`
at `q`, then `φ` belongs to the left limit at every real point strictly above `q`.

The threshold witnessing membership is `(q : ℝ)` itself: every rational `p` in the interval
`(q, t)` lies strictly above `q`, so the family's own `forward_G` already places `φ` in `m p`.

The hypothesis `hG` is the `forward_G` field of `FMCS` (`Bundle/FMCSDef.lean`) specialised to
`D := Rat`, taken as an argument so this lemma is available before the real-carrier family is
assembled.
-/
theorem limitSetBelow_forward_G_rat_source (m : Rat → Set Formula)
    (hG : ∀ (s t : Rat) (φ : Formula), s < t → Formula.allFuture φ ∈ m s → φ ∈ m t)
    (q : Rat) (t : ℝ) (φ : Formula) (hqt : (q : ℝ) < t)
    (hφ : Formula.allFuture φ ∈ m q) :
    φ ∈ limitSetBelow m t := by
  rw [mem_limitSetBelow]
  refine ⟨(q : ℝ), hqt, ?_⟩
  intro p hp1 _
  have hqp : q < p := by exact_mod_cast hp1
  exact hG q p φ hqp hφ

/-! ## Backward H coherence

Cases G2 and G4 (unselected source) are retired -- see
`Boneyard/LimitMCSCoherenceDeadCases/README.md`. Only the source-rational case (G1, above) and
the `limitMCSBelow`-source variants further below survive live.
-/

/--
**Case H1 (selected source, unselected target).** If the rational family asserts `allPast φ` at
`q`, then `φ` belongs to the left limit at every real point `t ≤ (q : ℝ)`.

The threshold is `t - 1`: every rational `p` in `(t - 1, t)` satisfies `p < t ≤ q`, hence lies
in `q`'s strict past, so `backward_H` places `φ` in `m p`.

The strict case `t < (q : ℝ)` is the coherence matrix's case H1; the case `t = (q : ℝ)` is
`limitSetBelow_of_rat` (`Bundle/LimitMCS.lean`) -- the `≤` form below is a generalisation of it
(retired as an explicit corollary; see `Boneyard/LimitMCSCoherenceDeadCases/README.md`).
-/
theorem limitSetBelow_backward_H_rat_source (m : Rat → Set Formula)
    (hH : ∀ (s t : Rat) (φ : Formula), t < s → Formula.allPast φ ∈ m s → φ ∈ m t)
    (q : Rat) (t : ℝ) (φ : Formula) (htq : t ≤ (q : ℝ))
    (hφ : Formula.allPast φ ∈ m q) :
    φ ∈ limitSetBelow m t := by
  rw [mem_limitSetBelow]
  refine ⟨t - 1, by linarith, ?_⟩
  intro p _ hp2
  have hpq : p < q := by
    have : (p : ℝ) < (q : ℝ) := lt_of_lt_of_le hp2 htq
    exact_mod_cast this
  exact hH q p φ hpq hφ

/-! ## The `limitMCSBelow`-source variants

Cases H2 and H4 (unselected source), and the `t = (q : ℝ)` corollary of H1, are retired -- see
`Boneyard/LimitMCSCoherenceDeadCases/README.md`. Only the source-rational case (H1, above) and
the four variants below survive live.
-/

/-
The real extension takes the **ultrafilter** limit `limitMCSBelow` at unselected points, not the
plain limit set, because that is what carries maximality (`limitMCSBelow_is_mcs`,
`Bundle/LimitMCS.lean`). The four cases with an *unselected source* — G2, G4, H2, H4 — therefore
arrive with a `limitMCSBelow` hypothesis rather than a `limitSetBelow` one, and the six lemmas
above do not apply on the nose.

Each transposes in one step. Where the `limitSetBelow` proof destructures the membership into a
threshold `z` and a "carried at every rational in `(z, r)`" clause, the `limitMCSBelow` proof
calls `limitMCSBelow_cofinal_below` at a threshold of its own choosing — the threshold is a
*parameter* of that lemma, not an output — and gets back a single rational carrying the formula.
Because the caller picks the threshold, the `max`-based bounds of the H-side proofs above
disappear: the bound that the `max` was there to clear is simply passed as the threshold.

The *conclusion* side needs no variants: `limitSetBelow_subset_limitMCSBelow`
(`Bundle/LimitMCS.lean`) upgrades a `limitSetBelow` conclusion to a `limitMCSBelow` one in one
step, and that is how G4 and H4 below produce their conclusions (and how a caller lifts G1 and
H1 at an unselected target).
-/

/--
**Case G2 with an ultrafilter-limit source.** The `limitMCSBelow` form of the retired case G2
(`Boneyard/LimitMCSCoherenceDeadCases/README.md`).

Cofinality is called at the threshold `s - 1`, which is admissible for any `s` and delivers a
rational `q < s`; then `q < s < p` puts `p` in `q`'s strict future.
-/
theorem limitMCSBelow_forward_G_rat_target (m : Rat → Set Formula)
    (hG : ∀ (s t : Rat) (φ : Formula), s < t → Formula.allFuture φ ∈ m s → φ ∈ m t)
    (s : ℝ) (p : Rat) (φ : Formula) (hsp : s < (p : ℝ))
    (hφ : Formula.allFuture φ ∈ limitMCSBelow m s) :
    φ ∈ m p := by
  obtain ⟨q, _, hq2, hqmem⟩ := limitMCSBelow_cofinal_below m s hφ (s - 1) (by linarith)
  have hqp : q < p := by
    have : (q : ℝ) < (p : ℝ) := lt_trans hq2 hsp
    exact_mod_cast this
  exact hG q p φ hqp hqmem

/--
**Case G4 with an ultrafilter-limit source.** The `limitMCSBelow` form of the retired case G4
(`Boneyard/LimitMCSCoherenceDeadCases/README.md`), on both sides.

Cofinality at `s - 1` yields a rational `q₀ < s` carrying `allFuture φ`; `q₀` is then a valid
`limitSetBelow` threshold at `t`, and the conclusion is upgraded by
`limitSetBelow_subset_limitMCSBelow`.
-/
theorem limitMCSBelow_forward_G_limit (m : Rat → Set Formula)
    (hG : ∀ (s t : Rat) (φ : Formula), s < t → Formula.allFuture φ ∈ m s → φ ∈ m t)
    (s t : ℝ) (φ : Formula) (hst : s < t)
    (hφ : Formula.allFuture φ ∈ limitMCSBelow m s) :
    φ ∈ limitMCSBelow m t := by
  obtain ⟨q₀, _, hq₀2, hq₀mem⟩ := limitMCSBelow_cofinal_below m s hφ (s - 1) (by linarith)
  have hq₀t : (q₀ : ℝ) < t := lt_trans hq₀2 hst
  refine limitSetBelow_subset_limitMCSBelow m t (mem_limitSetBelow.mpr ⟨(q₀ : ℝ), hq₀t, ?_⟩)
  intro p hp1 _
  have hq₀p : q₀ < p := by exact_mod_cast hp1
  exact hG q₀ p φ hq₀p hq₀mem

/--
**Case H2 with an ultrafilter-limit source.** The `limitMCSBelow` form of the retired case H2
(`Boneyard/LimitMCSCoherenceDeadCases/README.md`).

Cofinality is called at the threshold `(p : ℝ)` itself — admissible precisely because
`(p : ℝ) < s` — so the returned rational `q` satisfies `p < q` outright. The `max` of the
`limitSetBelow` proof is not needed: the bound it was clearing is now the threshold.
-/
theorem limitMCSBelow_backward_H_rat_target (m : Rat → Set Formula)
    (hH : ∀ (s t : Rat) (φ : Formula), t < s → Formula.allPast φ ∈ m s → φ ∈ m t)
    (s : ℝ) (p : Rat) (φ : Formula) (hps : (p : ℝ) < s)
    (hφ : Formula.allPast φ ∈ limitMCSBelow m s) :
    φ ∈ m p := by
  obtain ⟨q, hq1, _, hqmem⟩ := limitMCSBelow_cofinal_below m s hφ (p : ℝ) hps
  have hpq : p < q := by exact_mod_cast hq1
  exact hH q p φ hpq hqmem

/--
**Case H4 with an ultrafilter-limit source.** The `limitMCSBelow` form of the retired case H4
(`Boneyard/LimitMCSCoherenceDeadCases/README.md`), on both sides.

Cofinality is called at the threshold `t` — admissible because `t < s` — so the returned
rational `q₀` satisfies `t < q₀` outright, again without a `max`. Then `t - 1` is a valid
`limitSetBelow` threshold at `t`, since every rational `p < t` lies below `q₀`.
-/
theorem limitMCSBelow_backward_H_limit (m : Rat → Set Formula)
    (hH : ∀ (s t : Rat) (φ : Formula), t < s → Formula.allPast φ ∈ m s → φ ∈ m t)
    (s t : ℝ) (φ : Formula) (hts : t < s)
    (hφ : Formula.allPast φ ∈ limitMCSBelow m s) :
    φ ∈ limitMCSBelow m t := by
  obtain ⟨q₀, hq₀1, _, hq₀mem⟩ := limitMCSBelow_cofinal_below m s hφ t hts
  refine limitSetBelow_subset_limitMCSBelow m t (mem_limitSetBelow.mpr ⟨t - 1, by linarith, ?_⟩)
  intro p _ hp2
  have hpq₀ : p < q₀ := by
    have : (p : ℝ) < (q₀ : ℝ) := lt_trans hp2 hq₀1
    exact_mod_cast this
  exact hH q₀ p φ hpq₀ hq₀mem

end FormalSystem.Metalogic.Bundle
