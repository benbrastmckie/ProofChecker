/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Formula
import FormalSystem.StarLanguage.Axioms
import FormalSystem.StarLanguage.Derivation

/-!
# `FormalSystem.StarLanguage` — the language L⋆ and its logic TM⋆

This component is a self-contained mirror of `Syntax` + `ProofSystem` for the language **L⋆**:
L⁺ (`FormalSystem.Syntax.Formula`) extended by the paper's **stability modal** `⊡`
(`possible_worlds.tex` line 1114), read "settled at the present world state". It follows the
pattern of `FormalSystem.MinusLanguage`: a separate inductive with an embedding, and a
proof system mirroring `ProofSystem.DerivationTree` constructor for constructor.

## Modules

- `StarLanguage.Formula` — `StarFormula`, the derived operators (with `Formula`'s right-hand
  sides), `swapTemporal`, the purity predicates `IsPureFuture`/`IsPurePast`, and the embedding
  `ofFormula`
- `StarLanguage.Axioms` — `StarAxiom`, the closed inductive of TM⋆ schemata: the 45 TM⁺
  schemata re-declared over `StarFormula`, plus the eight `⊡` schemata (S5 for `⊡`, `□φ → ⊡φ`,
  `p → ⊡p` for atoms, and the two pasting schemata with purity side conditions); `minFrameClass`
- `StarLanguage.Derivation` — `StarDerivationTree`, `StarDerivable`, `⊢⋆[fc]` notation, the
  derived `⊡`-necessitation rule, and the **backward conservativity** bridge
  `StarDerivationTree.ofPlus` / `starDerivable_of_derivable`:
  `TM⁺ ⊢[fc] φ ⟹ TM⋆ ⊢[fc] ofFormula φ` at every frame class

## Where the L⋆ semantics and metatheory live

- `FormalSystem/Semantics/StarTruth.lean` — `SameStateAt`, `StarTruthAt`
- `FormalSystem/Semantics/StarValidity.lean` — `StarValidIn`, semantic conservativity
- `FormalSystem/Semantics/StarPasting.lean`, `StarNonValidities.lean` — the pasting validities
  and the refutations that bound the axiom set
- `FormalSystem/Metalogic/Conservativity/Star.lean` — soundness of TM⋆ at all four frame
  classes and proof-theoretic conservativity over TM⁺ in both directions

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
Checkable by `grep -rn 'FormalSystem.Semantics' FormalSystem/StarLanguage/`, whose only matches
are prose mentions in docstrings — no `import` line matches. The invariant is directional,
exactly as for `MinusLanguage/`: the converse edge is permitted and is how L⋆ acquires its
semantics.
-/
