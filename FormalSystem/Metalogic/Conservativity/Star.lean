/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.Star.Atomization
import FormalSystem.Metalogic.Conservativity.Star.AxiomValidity
import FormalSystem.Metalogic.Conservativity.Star.StarSoundness
import FormalSystem.Metalogic.Conservativity.Star.Forward

/-!
# The stability extension L⋆ / TM⋆ — soundness and conservativity over TM⁺

**TM⋆** is the logic of the language L⋆ = L⁺ + `⊡` (`FormalSystem/StarLanguage/`): the 45 TM⁺
schemata re-declared over `StarFormula`, the S5 schemata for `⊡`, the bridges `□φ → ⊡φ` and
`p → ⊡p` (atoms), and the two pasting schemata PS/US with pure-future/pure-past side conditions,
under the seven rules of TM⁺. Its semantics is the paper's `($\Stability$)` clause
(`possible_worlds.tex` line 1114) over the task-frame semantics of L⁺
(`FormalSystem/Semantics/StarTruth.lean`).

**This file is the aggregator, and it holds no declarations.** It re-exports the four modules of
the L⋆ metatheory:

| Module | Contents |
|--------|----------|
| `Conservativity/Star/Atomization.lean` | `Encoding`, `atomize`, `TaskModel.atomModel`, the transfer lemma `starTruthAt_iff_atomize`, and `starValidIn_of_plus` / `starValidIn_swap_of_plus` — TM⁺ schema soundness over L⋆ in one lemma |
| `Conservativity/Star/AxiomValidity.lean` | `starAxiom_validIn_min`, `starAxiom_swap_validIn_min` — validity and swap-validity of every `StarAxiom` constructor, one arm each |
| `Conservativity/Star/StarSoundness.lean` | `star_derivable_valid_and_swap_validIn`, `star_soundness_validIn`, `star_soundness_in`, the four rows — soundness of TM⋆ at every class, TD discharged semantically |
| `Conservativity/Star/Forward.lean` | `forward_star`, `starDerivable_ofFormula_iff`, `star_of_tm`, `tmFrag_iff_star` — conservativity over TM⁺ in both directions |

## The result, stated precisely

**`Forward⋆` (TM⋆ over TM⁺) holds at all four classes, unlike `Forward` (TM⁺ over TM).** For
every L⁺ formula `φ` and every `fc ∈ {Base, Dense, Discrete, Dedekind}`:

```
TM⋆ ⊢[fc] ofFormula φ   ↔   TM⁺ ⊢[fc] φ          (starDerivable_ofFormula_iff)
```

Backward is the embedding of derivations (`StarLanguage/Derivation.lean`); forward is TM⋆
soundness composed with the truth-transfer bridge `starValidIn_ofFormula_iff` and the TM⁺
completeness engine at `fc`. No TM⋆ completeness is used. Semantic conservativity,
`StarValidIn fc (ofFormula φ) ↔ ValidIn fc φ`, is `Semantics/StarValidity.lean`'s
`starValidIn_ofFormula_iff`. The composed pair L ⊂ L⋆ inherits the L ⊂ L⁺ status exactly:
backward at every class (`star_of_tm`), forward not asserted (refuted at `.Base` and `.Discrete`,
open at `.Dense` and `.Dedekind` — `Metalogic/Conservativity.lean`).

## What is open, and is not promised here

- **Completeness of TM⋆** over the all-histories semantics, at any class. The four TM⁺
  completeness engines build deterministic countermodels, on which `⊡` is the identity, so none
  of them can refute a `¬⊡`-formula and none transfers; a canonical model on `⊡`-classes of
  maximal consistent sets faces a lifting obstruction the pasting schemata do not resolve for
  mixed past/future demands. Nothing in this tree asserts or approaches TM⋆ completeness.
- **Decidability of TM⋆.** By the conservativity above, a decision procedure for TM⋆ would
  decide TM⁺, whose decidability is itself open at every class; no result in either direction is
  claimed.

## Import discipline

The four children import each other in the chain
`Atomization ← AxiomValidity ← StarSoundness ← Forward`; none imports this aggregator, and the
aggregator is imported by `Metalogic/Conservativity.lean`.
-/
