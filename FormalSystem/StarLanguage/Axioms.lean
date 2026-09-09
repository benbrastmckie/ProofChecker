/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Formula
import FormalSystem.PlusLanguage.Axioms

/-!
# `StarAxiom` — the axiom schemata of TM⋆ over `StarFormula`

The axiom system **TM⋆** for the language L⋆ (`StarLanguage/Formula.lean`): one constructor
`ofBase` carrying every TM⁺ schema (`PlusLanguage/Axioms.lean`) at its `ofPlus` instances, plus
sixteen schemata governing the two time registers `↑ⁱ` and `↓ⁱ` of `def:BLstar-semantics`.

## Why the TM⁺ schemata are embedded rather than re-declared

This is the **opposite** decision to `PlusAxiom`'s, and for a reason that is not a matter of
convenience. `PlusAxiom` re-declares the 45 TM schemata over `PlusFormula` because TM⁺ needs
them at `⊡`-formulas, and every one of them remains valid there. Over `StarFormula` that is
false: `modal_future` (`□φ → □Gφ`) is **refuted** — see `refute_modal_future`
(`Semantics/StarNonValidities.lean`), which fails it already at `φ := ↓¹p → p` over a
two-state frame. MF is the sole schema in the TM block whose soundness proof consumes time-shift
homogeneity, and the L⋆ time-shift lemma shifts the stored-time vector along with the history,
so the argument no longer reaches the conclusion — and the gap is real, not an artefact.

A re-declared TM block over `StarFormula` would therefore contain an unsound schema, and no
weakened restatement of MF appears here in its place. `ofBase` supplies every TM⁺ schema
exactly at the register-free instances where it is sound, which is everything the embedding
(`StarLanguage/Embedding.lean`) and the conservativity results
(`Metalogic/Conservativity/Star/`) consume. **The recorded cost**: TM⋆'s inherited temporal
schemata are available only at `ofPlus` instances, never at a formula containing a register.

## The register schemata

Every entry is a validity of `StarTruthAt` over *every* task frame; most are definitional. The
justifications are the two clauses of `def:BLstar-semantics`: `↑ⁱφ` at `(τ, x, v⃗)` is `φ` at
`(τ, x, v⃗[i ↦ x])`, and `↓ⁱφ` at `(τ, x, v⃗)` is `φ` at `(τ, v⃗ᵢ, v⃗)`.

| Constructor | Schema | Why |
|---|---|---|
| `store_recall_same` | `↑ⁱ↓ⁱφ ↔ ↑ⁱφ` | register `i` of `v⃗[i ↦ x]` is `x`, the time already being evaluated at |
| `recall_store_same` | `↓ⁱ↑ⁱφ ↔ ↓ⁱφ` | writing `v⃗ᵢ` into register `i` leaves `v⃗` alone |
| `recall_recall` | `↓ⁱ↓ʲφ ↔ ↓ʲφ` | `↓ⁱ` sets the time, `↓ʲ` immediately overrides it |
| `store_store_comm` | `↑ⁱ↑ʲφ ↔ ↑ʲ↑ⁱφ` | both write the *same* time, so the updates commute |
| `store_k` / `recall_k` | `↑ⁱ(φ→ψ) ↔ (↑ⁱφ → ↑ⁱψ)`, likewise `↓ⁱ` | both registers are *functional*: one point in, one point out |
| `store_box` / `recall_box` | `↑ⁱ□φ ↔ □↑ⁱφ`, `↓ⁱ□φ ↔ □↓ⁱφ` | `□` moves the history, never the time or the vector |
| `store_stab` | `↑ⁱ⊡φ ↔ ⊡↑ⁱφ` | `⊡`'s same-state condition is taken at the current time, which is exactly what `↑ⁱ` writes |
| `store_atom` | `↑ⁱp ↔ p` for atoms | the atom clause does not read the vector |
| `recall_rigid_future` / `future_rigid_recall` | `↓ⁱφ ↔ G↓ⁱφ`, as two implications | `↓ⁱφ`'s truth does not read the time of evaluation (⟶), and the frame is serial forward (⟵) |
| `recall_rigid_past` / `past_rigid_recall` | `↓ⁱφ ↔ H↓ⁱφ`, as two implications | the same, backwards |
| `recall_export_until` | `ψ U ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ U ⊤))` | rigidity plus the `untl` clause |
| `recall_export_since` | `ψ S ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ S ⊤))` | the past mirror |

**Deliberately absent, because refuted.** `↑ⁱ↓ⁱφ ↔ φ` (the correct law is `store_recall_same`);
`↓ⁱ⊡φ ↔ ⊡↓ⁱφ` — this is `stab_state_only`'s documented failure inside a recall scope, which is
why there is a `store_stab` but no `recall_stab`; `↑ⁱ(ψ U φ) ↔ (↑ⁱψ U ↑ⁱφ)` and its `S`/`G`/`H`
analogues, since the left stores the evaluation time once and the right re-stores each
quantified time; `↑ⁱ↓ʲφ ↔ ↓ʲ↑ⁱφ` for `i ≠ j`; and MF, as above.

**Deliberately absent, because unconsumed.** The register-closure schema `↑ⁱφ ↔ φ` for `i` not
free in `φ` (`store_atom` is its atomic case) needs a free-register predicate and a coincidence
lemma; register renaming needs a register substitution. Nothing in the metatheory built on this
inductive consumes either.

## Swap-closure — a stated invariant, checked constructor by constructor

`StarDerivationTree`'s `temporal_duality` rule is discharged **semantically**
(`Metalogic/Conservativity/Star/StarSoundness.lean`, the companion recursion), so the standing
obligation on this inductive is that every constructor's `swapTemporal` is again valid. It is,
and by the strongest available route — every arm's dual is an *instance of a constructor of this
same inductive*:

* `ofBase` — `swapTemporal` commutes with `ofPlus` (`ofPlus_swapTemporal`), so the dual of an
  `ofBase φ ax` instance is the TM⁺ schema's own dual, supplied by `plusAxiom_swap_validIn_min`.
* `store_recall_same`, `recall_store_same`, `recall_recall`, `store_store_comm`, `store_k`,
  `recall_k`, `store_box`, `recall_box`, `store_stab`, `store_atom` — **self-dual**: each is an
  `.iff` of formulas built from `imp`, `box`, `stab` and the two registers, none of which
  `swapTemporal` exchanges, so the dual is the same constructor at `φ.swapTemporal`.
* `recall_rigid_future` ↔ `recall_rigid_past` and `future_rigid_recall` ↔ `past_rigid_recall` —
  **dual pairs**, since `swapTemporal` exchanges `allFuture` and `allPast`.
* `recall_export_until` ↔ `recall_export_since` — a **dual pair**, since `swapTemporal`
  exchanges `untl` and `snce` and fixes `top`.

Every arm is therefore accounted for; a constructor added later must extend this list or the
swap dispatch lemma will not close.

## Frame classes

`StarAxiom.minFrameClass` sends `ofBase _ ax` to `ax.minFrameClass`, inheriting TM⁺'s routing of
the Dense, Discrete and Dedekind schemata, and every register schema to `.Base` — the register
clauses appeal to no order property beyond forward and backward seriality, which every task
frame has.

## Extension recipe

`StarAxiom` is a **closed** inductive. Exactly three declarations pattern-match on its
constructors: `StarAxiom.minFrameClass` below, and the two dispatch lemmas
`starAxiom_validIn_min` / `starAxiom_swap_validIn_min`
(`Metalogic/Conservativity/Star/StarAxiomValidity.lean`), neither of which carries a wildcard
arm. Adding a constructor means one constructor line, one `minFrameClass` arm, one arm in each
dispatch lemma, and one row in the swap-closure list above.

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
The semantic modules cited in this docstring are cited in prose only.

## References

* `FormalSystem/PlusLanguage/Axioms.lean` — `PlusAxiom`, the schema block `ofBase` carries
* `FormalSystem/Semantics/StarNonValidities.lean` — `refute_modal_future`, the reason no TM
  schema is re-declared here
* JPL paper `possible_worlds.tex` — `def:BLstar-semantics` (the store/recall clauses)

## Tags

star-language · axioms · store-recall · time-register
-/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.ProofSystem (FrameClass)
open FormalSystem.PlusLanguage

/--
Axiom schemata of TM⋆ over `StarFormula`: one `ofBase` arm carrying every TM⁺ schema at its
`ofPlus` instances, then the sixteen register schemata. See the module docstring for the design,
the schema inventory, and the swap-closure invariant.
-/
inductive StarAxiom : StarFormula → Type where
  /-- Every TM⁺ schema, at its embedded instance. MF (`□φ → □Gφ`) reaches TM⋆ through this arm
  and only through it; it is refuted at register-containing formulas. -/
  | ofBase (φ : PlusFormula) (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)
  /-- `↑ⁱ↓ⁱφ ↔ ↑ⁱφ`: recalling the register just written returns the present time. -/
  | store_recall_same (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.timeRecall i φ)).iff (.timeStore i φ))
  /-- `↓ⁱ↑ⁱφ ↔ ↓ⁱφ`: storing at the recalled time writes back what was already there. -/
  | recall_store_same (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.timeStore i φ)).iff (.timeRecall i φ))
  /-- `↓ⁱ↓ʲφ ↔ ↓ʲφ`: the inner recall overrides the outer one. -/
  | recall_recall (i j : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.timeRecall j φ)).iff (.timeRecall j φ))
  /-- `↑ⁱ↑ʲφ ↔ ↑ʲ↑ⁱφ`: both stores write the same time, so they commute. -/
  | store_store_comm (i j : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.timeStore j φ)).iff
        (StarFormula.timeStore j (.timeStore i φ)))
  /-- `↑ⁱ(φ → ψ) ↔ (↑ⁱφ → ↑ⁱψ)`: `↑ⁱ` is functional, hence a self-dual normal modality. -/
  | store_k (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (φ.imp ψ)).iff
        ((StarFormula.timeStore i φ).imp (.timeStore i ψ)))
  /-- `↓ⁱ(φ → ψ) ↔ (↓ⁱφ → ↓ⁱψ)`: likewise for recall. -/
  | recall_k (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (φ.imp ψ)).iff
        ((StarFormula.timeRecall i φ).imp (.timeRecall i ψ)))
  /-- `↑ⁱ□φ ↔ □↑ⁱφ`: `□` moves the history, never the time or the register vector. -/
  | store_box (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.box φ)).iff (StarFormula.box (.timeStore i φ)))
  /-- `↓ⁱ□φ ↔ □↓ⁱφ`: likewise for recall. -/
  | recall_box (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.box φ)).iff (StarFormula.box (.timeRecall i φ)))
  /-- `↑ⁱ⊡φ ↔ ⊡↑ⁱφ`: `⊡`'s same-state condition is taken at the very time `↑ⁱ` writes. There is
  deliberately **no** `recall_stab`: `↓ⁱ⊡φ ↔ ⊡↓ⁱφ` is refuted. -/
  | store_stab (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.stab φ)).iff (StarFormula.stab (.timeStore i φ)))
  /-- `↑ⁱp ↔ p` for atoms: the atom clause does not read the register vector. -/
  | store_atom (i : ℕ) (p : Atom) :
      StarAxiom ((StarFormula.timeStore i (.atom p)).iff (StarFormula.atom p))
  /-- `↓ⁱφ → G↓ⁱφ` (**rigidity**): a recall's truth does not depend on the time of evaluation. -/
  | recall_rigid_future (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i φ).imp (StarFormula.allFuture (.timeRecall i φ)))
  /-- `G↓ⁱφ → ↓ⁱφ`: the converse of `recall_rigid_future`, by forward seriality. -/
  | future_rigid_recall (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.allFuture (.timeRecall i φ)).imp (StarFormula.timeRecall i φ))
  /-- `↓ⁱφ → H↓ⁱφ`: rigidity, backwards. -/
  | recall_rigid_past (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i φ).imp (StarFormula.allPast (.timeRecall i φ)))
  /-- `H↓ⁱφ → ↓ⁱφ`: the converse, by backward seriality. -/
  | past_rigid_recall (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.allPast (.timeRecall i φ)).imp (StarFormula.timeRecall i φ))
  /-- `ψ U ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ U ⊤))` (**recall export**): a rigid event contributes nothing to the
  `until` beyond the existence of the interval. -/
  | recall_export_until (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl ψ (.timeRecall i φ)).iff
        ((StarFormula.timeRecall i φ).and (StarFormula.untl ψ StarFormula.top)))
  /-- `ψ S ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ S ⊤))`: the past mirror of `recall_export_until`. -/
  | recall_export_since (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce ψ (.timeRecall i φ)).iff
        ((StarFormula.timeRecall i φ).and (StarFormula.snce ψ StarFormula.top)))

/--
Minimum frame class of each TM⋆ schema. The `ofBase` arm inherits `PlusAxiom.minFrameClass`;
every register schema is valid over every task frame and is routed to `.Base`.
-/
def StarAxiom.minFrameClass {φ : StarFormula} : StarAxiom φ → FrameClass
  | .ofBase _ ax => ax.minFrameClass
  | _ => .Base

/-! ### Pins -/

example (φ : PlusFormula) : (StarAxiom.ofBase _ (PlusAxiom.density φ)).minFrameClass = .Dense :=
  rfl

example (φ : PlusFormula) : (StarAxiom.ofBase _ (PlusAxiom.stab_t φ)).minFrameClass = .Base := rfl

example (i : ℕ) (φ : StarFormula) : (StarAxiom.store_box i φ).minFrameClass = .Base := rfl

example (i : ℕ) (φ ψ : StarFormula) :
    (StarAxiom.recall_export_until i φ ψ).minFrameClass = .Base := rfl

end FormalSystem.StarLanguage
