/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Formula

/-!
# `FormalSystem.StarLanguage` — the language L⋆ = L⁺ + time store/recall

This component is the **syntactic** half of the manuscript's `\BL^\star` in the presentation
`def:BLstar-semantics` gives it: L⁺ (`FormalSystem.PlusLanguage`) extended by the two hybrid
time registers `↑ⁱ` (store) and `↓ⁱ` (recall), with the world registers `↑_M`/`↓_M` suppressed.
It follows the pattern of `FormalSystem.MinusLanguage` and `FormalSystem.PlusLanguage`: a
separate inductive with a constructor-to-constructor embedding.

## Modules

- `StarLanguage.Formula` — `StarFormula`, the derived operators (with `PlusFormula`'s right-hand
  sides), and the embedding `ofPlus`

## Where the L⋆ semantics lives

- `FormalSystem/Semantics/StarTruth.lean` — `StarTruthAt` over points `(τ, x, v⃗)`, the transport
  layer, and the truth transfer `starTruthAt_ofPlus`
- `FormalSystem/Semantics/StarValidity.lean` — `TaskFrame.StarValidOn`, `sentDet`
- `FormalSystem/Semantics/StarDeterminism.lean` — `app:deterministic-future`'s positive half,
  `detPM`, and Theorem C's `Det-pm` half
- `FormalSystem/Semantics/StarNonValidities.lean` — `app:deterministic-future`'s negative half
- `FormalSystem/Metalogic/Independence/StarDiscrimination.lean` — the discrimination footnote

## Reserved and unbuilt

`StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are **reserved names, not declared**. This
component is semantic-only; see `FormalSystem/StarLanguage/README.md` for the reason and for the
paper-label correspondence table.

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
Checkable by `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/`.
-/
