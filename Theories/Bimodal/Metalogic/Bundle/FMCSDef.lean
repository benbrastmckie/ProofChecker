import Bimodal.Metalogic.Core.MaximalConsistent
import Bimodal.Metalogic.Core.MCSProperties
import Bimodal.Syntax.Formula

/-!
# FMCS: Family of Maximal Consistent Sets

This module defines the `FMCS` (Family of Maximal Consistent Sets) structure
that assigns a maximal consistent set (MCS) to each element of a preordered
index type `D`, with coherence conditions ensuring proper formula propagation
along the ordering.

## Terminology (Task 928)

- **MCS**: A single maximal consistent set (a world state in the canonical model)
- **FMCS**: A SINGLE indexed family of MCS — one MCS per element of `D`
- **BFMCS**: A BUNDLE (set) of FMCS families with modal coherence

## Overview

An FMCS assigns an MCS to each element of a preordered index type `D`, with
coherence conditions that ensure formulas propagate correctly along the ordering.

The type parameter `D` is **not necessarily a time type**. It is any preordered
type used to index the family:

- **`D = Int`**: Elements of D are integer times. Each time gets an MCS (world state).
  This is used in `CanonicalConstruction.lean` for the truth lemma, where histories
  map times to world states.
- **`D = CanonicalMCS`**: Elements of D are world states themselves, ordered by
  `CanonicalR` (the reflexive closure of forward accessibility). Each world state
  maps to its own MCS. This is used in `CanonicalFMCS.lean` to establish temporal
  coherence over the space of all MCS, before transferring to an integer timeline.
- **`D = Rat`**: Rational times for dense temporal extensions.

The coherence conditions (`forward_G`, `backward_H`) use the strict ordering on `D`:
if `t < t'` in `D`, then `G φ ∈ mcs t` implies `φ ∈ mcs t'` (and dually for H).

## Main Definitions

- `FMCS D`: Structure pairing each `t : D` with an MCS, plus coherence conditions
- `forward_G`: G formulas at t propagate strictly forward: t < t' implies φ ∈ mcs t'
- `backward_H`: H formulas at t propagate strictly backward: t' < t implies φ ∈ mcs t'

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
A family of maximal consistent sets indexed by a preordered type `D`.

Each element `t : D` is assigned an MCS, with coherence conditions ensuring
that temporal formulas propagate correctly along the strict ordering on `D`.

**Type Parameter `D`**: A preordered index type. This is intentionally general:
- When `D = Int` or `D = Rat`, elements are times and the family is time-indexed.
- When `D = CanonicalMCS`, elements are world states (MCS ordered by `CanonicalR`),
  and the family maps each world state to its own MCS.

The parametricity over `D` allows the same structure to serve both as a
time-indexed family (for the truth lemma) and as a world-state-indexed family
(for establishing temporal coherence over all MCS).

**Fields**:
- `mcs`: Function assigning an MCS (a set of formulas) to each `t : D`
- `is_mcs`: Proof that each assigned set is maximal consistent
- `forward_G`: G formulas propagate strictly forward (t < t' implies φ ∈ mcs t')
- `backward_H`: H formulas propagate strictly backward (t' < t implies φ ∈ mcs t')

**Terminology (Task 928)**:
- FMCS = Family of MCS (single indexed family)
- BFMCS = Bundle of FMCSs (collection of families with modal coherence)
-/
structure FMCS where
  /-- The MCS assignment: each element `t : D` gets an MCS (a set of formulas). -/
  mcs : D -> Set Formula
  /-- Each assigned set is maximal consistent. -/
  is_mcs : forall t, SetMaximalConsistent (mcs t)
  /--
  Forward G coherence: `G φ ∈ mcs t` and `t < t'` implies `φ ∈ mcs t'`.

  With irreflexive (strict) semantics, `G φ` means "φ at all strictly later indices".
  If `G φ` is in the MCS at `t`, then `φ` must be in the MCS at any `t'` with `t < t'`.
  This does NOT imply `φ ∈ mcs t` (no reflexivity / T-axiom).
  -/
  forward_G : forall t t' phi, t < t' -> Formula.all_future phi ∈ mcs t -> phi ∈ mcs t'
  /--
  Backward H coherence: `H φ ∈ mcs t` and `t' < t` implies `φ ∈ mcs t'`.

  With irreflexive (strict) semantics, `H φ` means "φ at all strictly earlier indices".
  If `H φ` is in the MCS at `t`, then `φ` must be in the MCS at any `t'` with `t' < t`.
  This does NOT imply `φ ∈ mcs t` (no reflexivity / T-axiom).
  -/
  backward_H : forall t t' phi, t' < t -> Formula.all_past phi ∈ mcs t -> phi ∈ mcs t'

variable {D : Type*} [Preorder D]

-- Unused convenience definitions removed in Task 970:
-- FMCS.at, FMCS.consistent, FMCS.maximal, FMCS.forward_G_chain, FMCS.backward_H_chain,
-- FMCS.GG_to_G, FMCS.HH_to_H, FMCS.theorem_mem, FMCS.G_implies_future_phi,
-- FMCS.H_implies_past_phi, IsConstantFamily
-- These were thin wrappers around structure fields that were never used.

end Bimodal.Metalogic.Bundle
