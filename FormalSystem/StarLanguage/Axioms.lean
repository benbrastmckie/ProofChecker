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
* The **TM⁺ mirror block**, group by group as it lands:
  * `prop_k`, `prop_s`, `ex_falso`, `peirce`, `modal_t`, `modal_4`, `modal_b`,
    `modal_5_collapse`, `modal_k_dist`, `stab_k`, `stab_t`, `stab_4`, `stab_5`, `box_stab`,
    `atom_stab` — **self-dual**: each is built from `imp`, `box`, `stab`, `bot` and `atom`, none
    of which `swapTemporal` exchanges.
  * `serial_future` ↔ `serial_past`, `left_mono_until_G` ↔ `left_mono_since_H`,
    `right_mono_until` ↔ `right_mono_since`, `connect_future` ↔ `connect_past` — four **dual
    pairs**, since `swapTemporal` exchanges `untl`/`snce` and `allFuture`/`allPast`.
  * `enrichment_until` ↔ `enrichment_since`, `self_accum_until` ↔ `self_accum_since`,
    `absorb_until` ↔ `absorb_since`, `linear_until` ↔ `linear_since` — four **dual pairs**.
  * `until_F` ↔ `since_P`, `temp_linearity` ↔ `temp_linearity_past`,
    `F_until_equiv` ↔ `P_since_equiv` — three **dual pairs**.

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

Paper: — (formalization-native; the manuscript supplies no proof system for `\BL^\star`)
-/
inductive StarAxiom : StarFormula → Type where
  /-- Every TM⁺ schema, at its embedded instance. MF (`□φ → □Gφ`) reaches TM⋆ through this arm
  and only through it; it is refuted at register-containing formulas. -/
  | ofBase (φ : PlusFormula) (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)
  -- ## The TM⁺ mirror block
  -- Every TM⁺ schema (`PlusLanguage/Axioms.lean`), re-declared directly over `StarFormula`,
  -- constructor for constructor and argument for argument. `modal_future` alone carries a side
  -- condition its `PlusAxiom` mirror does not; `paste`/`untl_paste` carry the L⋆ counterparts of
  -- the purity conditions their mirrors already carry.
  -- Layer 1: Propositional (4)
  /-- Propositional K: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. Mirrors `PlusAxiom.prop_k`. -/
  | prop_k (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Propositional S (weakening): `φ → (ψ → φ)`. Mirrors `PlusAxiom.prop_s`. -/
  | prop_s (φ ψ : StarFormula) : StarAxiom (φ.imp (ψ.imp φ))
  /-- Ex Falso Quodlibet: `⊥ → φ`. Mirrors `PlusAxiom.ex_falso`. -/
  | ex_falso (φ : StarFormula) : StarAxiom (StarFormula.bot.imp φ)
  /-- Peirce's Law: `((φ → ψ) → φ) → φ`. Mirrors `PlusAxiom.peirce`. -/
  | peirce (φ ψ : StarFormula) : StarAxiom (((φ.imp ψ).imp φ).imp φ)
  -- Layer 2: S5 Modal (5)
  /-- Modal T: `□φ → φ`. Mirrors `PlusAxiom.modal_t`. -/
  | modal_t (φ : StarFormula) : StarAxiom (StarFormula.box φ |>.imp φ)
  /-- Modal 4: `□φ → □□φ`. Mirrors `PlusAxiom.modal_4`. -/
  | modal_4 (φ : StarFormula) :
      StarAxiom ((StarFormula.box φ).imp (StarFormula.box (StarFormula.box φ)))
  /-- Modal B: `φ → □◇φ`. Mirrors `PlusAxiom.modal_b`. -/
  | modal_b (φ : StarFormula) : StarAxiom (φ.imp (StarFormula.box φ.diamond))
  /-- Modal 5 Collapse: `◇□φ → □φ`. Mirrors `PlusAxiom.modal_5_collapse`. -/
  | modal_5_collapse (φ : StarFormula) : StarAxiom (φ.box.diamond.imp φ.box)
  /-- Modal K Distribution: `□(φ → ψ) → (□φ → □ψ)`. Mirrors `PlusAxiom.modal_k_dist`. -/
  | modal_k_dist (φ ψ : StarFormula) :
      StarAxiom ((φ.imp ψ).box.imp (φ.box.imp ψ.box))
  -- The stability modal, S5 block and the two bridge principles (6 of 8)
  /-- SK: `⊡(φ → ψ) → (⊡φ → ⊡ψ)`. Mirrors `PlusAxiom.stab_k`. -/
  | stab_k (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.stab (φ.imp ψ)).imp ((StarFormula.stab φ).imp (StarFormula.stab ψ)))
  /-- ST: `⊡φ → φ`. Mirrors `PlusAxiom.stab_t`. -/
  | stab_t (φ : StarFormula) : StarAxiom ((StarFormula.stab φ).imp φ)
  /-- S4 for `⊡`: `⊡φ → ⊡⊡φ`. Mirrors `PlusAxiom.stab_4`. -/
  | stab_4 (φ : StarFormula) :
      StarAxiom ((StarFormula.stab φ).imp (StarFormula.stab (StarFormula.stab φ)))
  /-- S5 for `⊡`: `⟐φ → ⊡⟐φ`, stated through `dstab`. Mirrors `PlusAxiom.stab_5`. -/
  | stab_5 (φ : StarFormula) :
      StarAxiom ((StarFormula.dstab φ).imp (StarFormula.stab (StarFormula.dstab φ)))
  /-- MS: `□φ → ⊡φ`. Mirrors `PlusAxiom.box_stab`. This is the schema the unrestricted
  `stabNecessitation` rule (`StarLanguage/Derivation.lean`) is built from, and its availability at
  **arbitrary** `φ : StarFormula` is what removes that rule's former `ofPlus` restriction. -/
  | box_stab (φ : StarFormula) : StarAxiom ((StarFormula.box φ).imp (StarFormula.stab φ))
  /-- AS: `p → ⊡p` for atoms. Mirrors `PlusAxiom.atom_stab`; the atom restriction is the schema's
  own content, not an artefact of L⋆. -/
  | atom_stab (p : Atom) :
      StarAxiom ((StarFormula.atom p).imp (StarFormula.stab (StarFormula.atom p)))
  -- Layer 3: BX Temporal — seriality, monotonicity, connection (8)
  /-- Serial future: `⊤ → F(⊤)`. Mirrors `PlusAxiom.serial_future`. -/
  | serial_future :
      StarAxiom ((StarFormula.bot.imp StarFormula.bot).imp
        (StarFormula.someFuture (StarFormula.bot.imp StarFormula.bot)))
  /-- Serial past: `⊤ → P(⊤)`. Mirrors `PlusAxiom.serial_past`. -/
  | serial_past :
      StarAxiom ((StarFormula.bot.imp StarFormula.bot).imp
        (StarFormula.somePast (StarFormula.bot.imp StarFormula.bot)))
  /-- BX2G: `G(φ→χ) → ((φ U ψ) → (χ U ψ))`. Mirrors `PlusAxiom.left_mono_until_G`. -/
  | left_mono_until_G (φ χ ψ : StarFormula) :
      StarAxiom ((φ.imp χ).allFuture.imp ((StarFormula.untl φ ψ).imp (StarFormula.untl χ ψ)))
  /-- BX2H: `H(φ→χ) → ((φ S ψ) → (χ S ψ))`. Mirrors `PlusAxiom.left_mono_since_H`. -/
  | left_mono_since_H (φ χ ψ : StarFormula) :
      StarAxiom ((φ.imp χ).allPast.imp ((StarFormula.snce φ ψ).imp (StarFormula.snce χ ψ)))
  /-- BX3: `G(φ → ψ) → ((χ U φ) → (χ U ψ))`. Mirrors `PlusAxiom.right_mono_until`. -/
  | right_mono_until (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp ψ).allFuture.imp ((StarFormula.untl χ φ).imp (StarFormula.untl χ ψ)))
  /-- BX3': `H(φ → ψ) → ((χ S φ) → (χ S ψ))`. Mirrors `PlusAxiom.right_mono_since`. -/
  | right_mono_since (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp ψ).allPast.imp ((StarFormula.snce χ φ).imp (StarFormula.snce χ ψ)))
  /-- BX4: `φ → G(P(φ))`. Mirrors `PlusAxiom.connect_future`. -/
  | connect_future (φ : StarFormula) :
      StarAxiom (φ.imp (φ.somePast.allFuture))
  /-- BX4': `φ → H(F(φ))`. Mirrors `PlusAxiom.connect_past`. -/
  | connect_past (φ : StarFormula) :
      StarAxiom (φ.imp (φ.someFuture.allPast))
  -- Layer 3: BX Temporal — enrichment, self-accumulation, absorption, linearity (8)
  /-- BX13: `p ∧ untl(φ, ψ) → untl(φ, ψ ∧ snce(φ, p))`. Mirrors `PlusAxiom.enrichment_until`. -/
  | enrichment_until (φ ψ p : StarFormula) :
      StarAxiom (StarFormula.and p (StarFormula.untl φ ψ) |>.imp
        (StarFormula.untl φ (StarFormula.and ψ (StarFormula.snce φ p))))
  /-- BX13': `p ∧ snce(φ, ψ) → snce(φ, ψ ∧ untl(φ, p))`. Mirrors `PlusAxiom.enrichment_since`. -/
  | enrichment_since (φ ψ p : StarFormula) :
      StarAxiom (StarFormula.and p (StarFormula.snce φ ψ) |>.imp
        (StarFormula.snce φ (StarFormula.and ψ (StarFormula.untl φ p))))
  /-- BX5: `U(ψ, φ) → U(ψ, φ ∧ U(ψ, φ))`. Mirrors `PlusAxiom.self_accum_until`. -/
  | self_accum_until (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ ψ).imp
        (StarFormula.untl (StarFormula.and φ (StarFormula.untl φ ψ)) ψ))
  /-- BX5': `S(ψ, φ) → S(ψ, φ ∧ S(ψ, φ))`. Mirrors `PlusAxiom.self_accum_since`. -/
  | self_accum_since (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ ψ).imp
        (StarFormula.snce (StarFormula.and φ (StarFormula.snce φ ψ)) ψ))
  /-- BX6: `U(φ ∧ U(ψ, φ), φ) → U(ψ, φ)`. Mirrors `PlusAxiom.absorb_until`. -/
  | absorb_until (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ (StarFormula.and φ (StarFormula.untl φ ψ))).imp
        (StarFormula.untl φ ψ))
  /-- BX6': `S(φ ∧ S(ψ, φ), φ) → S(ψ, φ)`. Mirrors `PlusAxiom.absorb_since`. -/
  | absorb_since (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ (StarFormula.and φ (StarFormula.snce φ ψ))).imp
        (StarFormula.snce φ ψ))
  /-- BX7: linearity of Until. Mirrors `PlusAxiom.linear_until`. -/
  | linear_until (φ ψ χ θ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.untl φ ψ) (StarFormula.untl χ θ)
        |>.imp (StarFormula.or
          (StarFormula.or
            (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and ψ θ))
            (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and ψ χ)))
          (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and φ θ))))
  /-- BX7': linearity of Since. Mirrors `PlusAxiom.linear_since`. -/
  | linear_since (φ ψ χ θ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.snce φ ψ) (StarFormula.snce χ θ)
        |>.imp (StarFormula.or
          (StarFormula.or
            (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and ψ θ))
            (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and ψ χ)))
          (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and φ θ))))
  -- Layer 3: BX Temporal — `until_F`/`since_P`, temporal linearity, the two equivalences (6)
  /-- BX10: `U(ψ, φ) → F(ψ)`. Mirrors `PlusAxiom.until_F`. -/
  | until_F (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ ψ).imp (StarFormula.someFuture ψ))
  /-- BX10': `S(ψ, φ) → P(ψ)`. Mirrors `PlusAxiom.since_P`. -/
  | since_P (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ ψ).imp (StarFormula.somePast ψ))
  /-- BX11: `F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ)`. Mirrors
  `PlusAxiom.temp_linearity`. -/
  | temp_linearity (φ ψ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.someFuture φ) (StarFormula.someFuture ψ) |>.imp
        (StarFormula.or (StarFormula.someFuture (StarFormula.and φ ψ))
          (StarFormula.or (StarFormula.someFuture (StarFormula.and φ (StarFormula.someFuture ψ)))
            (StarFormula.someFuture (StarFormula.and (StarFormula.someFuture φ) ψ)))))
  /-- BX11': `P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ)`. Mirrors
  `PlusAxiom.temp_linearity_past`. -/
  | temp_linearity_past (φ ψ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.somePast φ) (StarFormula.somePast ψ) |>.imp
        (StarFormula.or (StarFormula.somePast (StarFormula.and φ ψ))
          (StarFormula.or (StarFormula.somePast (StarFormula.and φ (StarFormula.somePast ψ)))
            (StarFormula.somePast (StarFormula.and (StarFormula.somePast φ) ψ)))))
  /-- BX12: `F(φ) → U(φ, ⊤)`. Mirrors `PlusAxiom.F_until_equiv`. -/
  | F_until_equiv (φ : StarFormula) :
      StarAxiom ((StarFormula.someFuture φ).imp
        (StarFormula.untl (StarFormula.bot.imp StarFormula.bot) φ))
  /-- BX12': `P(φ) → S(φ, ⊤)`. Mirrors `PlusAxiom.P_since_equiv`. -/
  | P_since_equiv (φ : StarFormula) :
      StarAxiom ((StarFormula.somePast φ).imp
        (StarFormula.snce (StarFormula.bot.imp StarFormula.bot) φ))
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

example (φ ψ χ : StarFormula) : (StarAxiom.prop_k φ ψ χ).minFrameClass = .Base := rfl

example (φ : StarFormula) : (StarAxiom.box_stab φ).minFrameClass = .Base := rfl

example (i : ℕ) (φ ψ : StarFormula) :
    (StarAxiom.recall_export_until i φ ψ).minFrameClass = .Base := rfl

end FormalSystem.StarLanguage
