import Bimodal.Metalogic.Core.MaximalConsistent
import Bimodal.Metalogic.Core.MCSProperties
import Bimodal.Syntax.Formula

/-!
# FMCS: Family of Maximal Consistent Sets

This module defines the `FMCS` (Family of Maximal Consistent Sets) structure,
which models a single **world history** in the canonical model construction.

## Semantic Role

A world history is a function from durations (times) to world states. In the
canonical model, world states are maximal consistent sets (MCS). An FMCS
assigns an MCS to each element of `D` — one world state per duration — with
coherence conditions ensuring that temporal formulas propagate correctly
along the ordering.

Each FMCS is one world history. A BFMCS (bundle of FMCSs) models the full
space of world histories (Ω), with modal coherence ensuring the box operator
quantifies correctly over alternative histories.

## Terminology (Task 928)

- **MCS**: A single maximal consistent set (a world state in the canonical model)
- **FMCS**: A SINGLE family of MCS indexed by `D` — one world history
- **BFMCS**: A BUNDLE (set) of FMCS families with modal coherence — the space Ω

## Duration Type `D`

The type parameter `D` is a totally ordered abelian group of durations. It is
**parametric**: the same definitions and proofs apply regardless of whether
durations are integers, rationals, reals, or any other ordered abelian group.
The Lean definition only requires `[Preorder D]` for technical flexibility
(some intermediate constructions use weaker structure), but the intended
instantiation is always a totally ordered abelian group.

The coherence conditions (`forward_G`, `backward_H`) use the strict ordering
on `D`: if `t < t'` then `G φ ∈ mcs t` implies `φ ∈ mcs t'` (and dually for H).

## Main Definitions

- `FMCS D`: Structure assigning an MCS (world state) to each duration `t : D`
- `forward_G`: G formulas propagate strictly forward: `t < t'` implies `φ ∈ mcs t'`
- `backward_H`: H formulas propagate strictly backward: `t' < t` implies `φ ∈ mcs t'`

## Design Note (Task 843)

The structure previously included `forward_H` and `backward_G` fields. These were
removed because:
1. The TruthLemma does NOT use them (verified by grep)
2. They existed only because constant-family constructions provided them trivially
3. Removing them simplifies all downstream family constructions
4. The temporal backward properties (G backward, H backward) are proven via
   contraposition using `forward_F`/`backward_P` from `TemporalCoherentFamily`

## References

- Research report: specs/812_canonical_model_completeness/reports/research-007.md
- Original: Bimodal.Boneyard.Metalogic_v5.Representation.FMCS
-/

namespace Bimodal.Metalogic.Bundle

open Bimodal.Syntax
open Bimodal.Metalogic.Core

/-!
## FMCS Structure
-/

variable (D : Type*) [Preorder D]

/--
A family of maximal consistent sets indexed by a duration type `D`,
modeling a single **world history** in the canonical model.

Each duration `t : D` is assigned an MCS (world state), with coherence
conditions ensuring that temporal formulas propagate correctly along
the strict ordering on `D`.

**Type Parameter `D`**: A totally ordered abelian group of durations,
parametric across extensions (discrete, dense, continuous, etc.). The Lean
definition requires only `[Preorder D]` for technical flexibility, but the
intended instantiation is always an ordered abelian group. The task relation
and `D` together determine which world histories are possible.

**Fields**:
- `mcs`: Function assigning an MCS (world state) to each duration `t : D`
- `is_mcs`: Proof that each assigned set is maximal consistent
- `forward_G`: G formulas propagate strictly forward (`t < t'` implies `φ ∈ mcs t'`)
- `backward_H`: H formulas propagate strictly backward (`t' < t` implies `φ ∈ mcs t'`)

**Terminology (Task 928)**:
- FMCS = Family of MCS — one world history
- BFMCS = Bundle of FMCSs — the space of world histories (Ω)
-/
structure FMCS where
  /-- The MCS assignment: each duration `t : D` gets an MCS (world state). -/
  mcs : D -> Set Formula
  /-- Each assigned set is maximal consistent. -/
  is_mcs : forall t, SetMaximalConsistent (mcs t)
  /--
  Forward G coherence: `G φ ∈ mcs t` and `t < t'` implies `φ ∈ mcs t'`.

  With strict semantics, `G φ` means "φ at all strictly later durations".
  If `G φ` is in the MCS (world state) at `t`, then `φ` must be in the MCS at
  any `t'` with `t < t'`. This does NOT imply `φ ∈ mcs t` (no T-axiom).
  -/
  forward_G : forall t t' phi, t < t' -> Formula.all_future phi ∈ mcs t -> phi ∈ mcs t'
  /--
  Backward H coherence: `H φ ∈ mcs t` and `t' < t` implies `φ ∈ mcs t'`.

  With strict semantics, `H φ` means "φ at all strictly earlier durations".
  If `H φ` is in the MCS (world state) at `t`, then `φ` must be in the MCS at
  any `t'` with `t' < t`. This does NOT imply `φ ∈ mcs t` (no T-axiom).
  -/
  backward_H : forall t t' phi, t' < t -> Formula.all_past phi ∈ mcs t -> phi ∈ mcs t'

variable {D : Type*} [Preorder D]

-- Unused convenience definitions removed in Task 970:
-- FMCS.at, FMCS.consistent, FMCS.maximal, FMCS.forward_G_chain, FMCS.backward_H_chain,
-- FMCS.GG_to_G, FMCS.HH_to_H, FMCS.theorem_mem, FMCS.G_implies_future_phi,
-- FMCS.H_implies_past_phi, IsConstantFamily
-- These were thin wrappers around structure fields that were never used.

end Bimodal.Metalogic.Bundle
