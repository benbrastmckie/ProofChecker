/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.StarLanguage.Formula
import FormalSystem.ProofSystem.Axioms

/-!
# `StarAxiom` — the axiom schemata of TM⋆ over `StarFormula`

The axiom system **TM⋆** for the language L⋆ (`StarLanguage/Formula.lean`): the 45 schemata of
TM⁺ (`ProofSystem/Axioms.lean`) **re-declared with `StarFormula` parameters**, plus eight
schemata for the stability modal `⊡`.

## Why the TM⁺ schemata are re-declared rather than embedded

An embedding constructor `ofPlus : Axiom φ → StarAxiom (ofFormula φ)` would yield only the
`⊡`-free instances of each schema. TM⋆ needs, for instance, `□⊡p → □G⊡p` — MF at `⊡p` — so every
schema must range over all of `StarFormula`. The re-declaration is mechanical: constructor for
constructor, the same name, the same parameter list, the same statement through the derived
operators of `StarLanguage/Formula.lean`, whose right-hand sides are `Formula`'s verbatim. The
function `StarAxiom.ofPlus` (`StarLanguage/Derivation.lean`) sends each `Axiom` instance to the
re-declared twin at the embedded parameters; every one of its 45 arms is `rfl`-shaped, so any
drift between the two inductives fails to typecheck there.

## The `⊡` schemata

| Name | Schema | Validity |
|------|--------|----------|
| `stab_k` | `⊡(φ → ψ) → (⊡φ → ⊡ψ)` | universal-quantifier shape of the `stab` clause |
| `stab_t` | `⊡φ → φ` | `Semantics/StarTruth.lean`, `of_stab` |
| `stab_4` | `⊡φ → ⊡⊡φ` | `stab_four` |
| `stab_5` | `⟐φ → ⊡⟐φ` (as `¬⊡¬φ → ⊡¬⊡¬φ`) | `stab_five` |
| `box_stab` | `□φ → ⊡φ` | `stab_of_box` (`⟨τ⟩_x ⊆ H_F`, paper line 1108) |
| `atom_stab` | `p → ⊡p` for atoms | `stab_atom_of_atom` (paper footnote, line 1119) |
| `paste` | `⟐φ⁺ → (⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻))`, `φ⁺` pure-future, `ψ⁻` pure-past | `Semantics/StarPasting.lean`, `paste_valid` |
| `untl_paste` | `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)`, `α⁻` pure-past, `φ⁺` pure-future | `untl_dstab_valid` |

The first four say that the monomodal logic of `⊡` is S5 (paper footnote, line 1118: `⟨τ⟩_x`
is an equivalence class of `σ ∼_x τ := σ(x) = τ(x)`), and the next two are the bridge principles
relating `⊡` to `□` and to atoms. **That set alone is provably incomplete**: it knows that `∼_x`
is an equivalence contained in the universal relation and respected by atoms, and nothing
else. The two pasting schemata `paste` and `untl_paste` add the one structural fact about
`⟨τ⟩_x` that the S5 axioms miss — the total histories through a world state are the product of
its possible pasts and its possible futures — and they are exactly what makes, for instance,
`⊡Gφ⁺ → G⊡φ⁺` derivable. Their purity side conditions are necessary
(`Semantics/StarNonValidities.lean`).

**Derived, not constructors.** FS (`F⟐φ⁺ → ⟐Fφ⁺`) is `untl_paste` at `α⁻ := ⊤`; GS
(`⊡Gφ⁺ → G⊡φ⁺`) is its contrapositive; the past mirrors (PS with the conjuncts exchanged, and
SS `(α⁺ S ⟐φ⁻) → ⟐(α⁺ S φ⁻)`) are obtained by the temporal-duality rule, since `swapTemporal`
exchanges `IsPureFuture` and `IsPurePast`. `⊡`-necessitation is likewise a derived rule
(necessitation for `□` followed by `box_stab`; `StarLanguage/Derivation.lean`,
`stabNecessitation`).

**Refuted, hence absent.** `⊡φ → □⊡φ`, `G⊡p → ⊡Gp`, `⊡GPp → G⊡Pp`, *Determined* `φ → ⊡φ` (over
non-deterministic frames), and `P⊡p → ⊡Pp` are all refuted in
`Semantics/StarNonValidities.lean`. In particular *Determined* must never be added here: it is
refuted at `.Base`, so adding it would falsify TM⋆ soundness. A validity notion over the
deterministic frames can be stated through `StarValidOnFrames` without touching this inductive.

**Open.** Completeness of TM⋆ over the all-histories semantics, and decidability of TM⋆, are
both open and outside this module's scope; nothing here promises either.

## Frame classes

`StarAxiom.minFrameClass` routes the TM⁺ schemata exactly as `Axiom.minFrameClass` does (Dense,
Discrete and Dedekind axioms to their classes, everything else to `.Base`); every `⊡` schema is
valid over every task frame and is routed to `.Base`.

## Extension recipe

`StarAxiom` is a **closed** inductive. Exactly three declarations pattern-match on its
constructors: `StarAxiom.minFrameClass` below, and the two dispatch lemmas
`starAxiom_validIn_min` / `starAxiom_swap_validIn_min`
(`Metalogic/Conservativity/Star/AxiomValidity.lean`). Adding a constructor means one constructor
line, one `minFrameClass` arm and one arm in each dispatch lemma; every other file recompiles
unchanged.

## References

* `FormalSystem/ProofSystem/Axioms.lean` — the 45 TM⁺ schemata, with their [burgess1982] / [xu1988] /
  [reynolds1992] provenance; the docstrings there are authoritative for each schema's reading
* JPL paper `possible_worlds.tex` lines 1108, 1114, 1118-1119, 1121
-/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.ProofSystem (FrameClass)
open StarFormula

/--
Axiom schemata of TM⋆ over `StarFormula`: the 45 TM⁺ schemata re-declared with `StarFormula`
parameters, then the eight `⊡` schemata. See the module docstring for the design and the axiom
inventory.
-/
inductive StarAxiom : StarFormula → Type where
  -- Layer 1: Propositional (4)
  /-- Propositional K: `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` -/
  | prop_k (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  /-- Propositional S (weakening): `φ → (ψ → φ)` -/
  | prop_s (φ ψ : StarFormula) : StarAxiom (φ.imp (ψ.imp φ))
  /-- Ex Falso Quodlibet: `⊥ → φ` -/
  | ex_falso (φ : StarFormula) : StarAxiom (StarFormula.bot.imp φ)
  /-- Peirce's Law: `((φ → ψ) → φ) → φ` -/
  | peirce (φ ψ : StarFormula) : StarAxiom (((φ.imp ψ).imp φ).imp φ)
  -- Layer 2: S5 Modal (5)
  /-- Modal T: `□φ → φ` -/
  | modal_t (φ : StarFormula) : StarAxiom (StarFormula.box φ |>.imp φ)
  /-- Modal 4: `□φ → □□φ` -/
  | modal_4 (φ : StarFormula) : StarAxiom ((StarFormula.box φ).imp (StarFormula.box (StarFormula.box φ)))
  /-- Modal B: `φ → □◇φ` -/
  | modal_b (φ : StarFormula) : StarAxiom (φ.imp (StarFormula.box φ.diamond))
  /-- Modal 5 Collapse: `◇□φ → □φ` -/
  | modal_5_collapse (φ : StarFormula) : StarAxiom (φ.box.diamond.imp φ.box)
  /-- Modal K Distribution: `□(φ → ψ) → (□φ → □ψ)` -/
  | modal_k_dist (φ ψ : StarFormula) :
      StarAxiom ((φ.imp ψ).box.imp (φ.box.imp ψ.box))
  -- Layer 3: BX Temporal (22)
  /-- Serial future: `⊤ → F(⊤)` -/
  | serial_future :
    StarAxiom ((StarFormula.bot.imp StarFormula.bot).imp
      (StarFormula.someFuture (StarFormula.bot.imp StarFormula.bot)))
  /-- Serial past: `⊤ → P(⊤)` -/
  | serial_past :
    StarAxiom ((StarFormula.bot.imp StarFormula.bot).imp
      (StarFormula.somePast (StarFormula.bot.imp StarFormula.bot)))
  /-- BX2G: `G(φ→χ) → ((φ U ψ) → (χ U ψ))` -/
  | left_mono_until_G (φ χ ψ : StarFormula) :
      StarAxiom ((φ.imp χ).allFuture.imp ((StarFormula.untl φ ψ).imp (StarFormula.untl χ ψ)))
  /-- BX2H: `H(φ→χ) → ((φ S ψ) → (χ S ψ))` -/
  | left_mono_since_H (φ χ ψ : StarFormula) :
      StarAxiom ((φ.imp χ).allPast.imp ((StarFormula.snce φ ψ).imp (StarFormula.snce χ ψ)))
  /-- BX3: `G(φ → ψ) → ((χ U φ) → (χ U ψ))` -/
  | right_mono_until (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp ψ).allFuture.imp ((StarFormula.untl χ φ).imp (StarFormula.untl χ ψ)))
  /-- BX3': `H(φ → ψ) → ((χ S φ) → (χ S ψ))` -/
  | right_mono_since (φ ψ χ : StarFormula) :
      StarAxiom ((φ.imp ψ).allPast.imp ((StarFormula.snce χ φ).imp (StarFormula.snce χ ψ)))
  /-- BX4: `φ → G(P(φ))` -/
  | connect_future (φ : StarFormula) :
      StarAxiom (φ.imp (φ.somePast.allFuture))
  /-- BX4': `φ → H(F(φ))` -/
  | connect_past (φ : StarFormula) :
      StarAxiom (φ.imp (φ.someFuture.allPast))
  /-- BX13: `p ∧ untl(φ, ψ) → untl(φ, ψ ∧ snce(φ, p))` (Burgess A3a) -/
  | enrichment_until (φ ψ p : StarFormula) :
      StarAxiom (StarFormula.and p (StarFormula.untl φ ψ) |>.imp
        (StarFormula.untl φ (StarFormula.and ψ (StarFormula.snce φ p))))
  /-- BX13': `p ∧ snce(φ, ψ) → snce(φ, ψ ∧ untl(φ, p))` (Burgess A3b) -/
  | enrichment_since (φ ψ p : StarFormula) :
      StarAxiom (StarFormula.and p (StarFormula.snce φ ψ) |>.imp
        (StarFormula.snce φ (StarFormula.and ψ (StarFormula.untl φ p))))
  /-- BX5: `U(ψ, φ) → U(ψ, φ ∧ U(ψ, φ))` -/
  | self_accum_until (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ ψ).imp
        (StarFormula.untl (StarFormula.and φ (StarFormula.untl φ ψ)) ψ))
  /-- BX5': `S(ψ, φ) → S(ψ, φ ∧ S(ψ, φ))` -/
  | self_accum_since (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ ψ).imp
        (StarFormula.snce (StarFormula.and φ (StarFormula.snce φ ψ)) ψ))
  /-- BX6: `U(φ ∧ U(ψ, φ), φ) → U(ψ, φ)` -/
  | absorb_until (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ (StarFormula.and φ (StarFormula.untl φ ψ))).imp
        (StarFormula.untl φ ψ))
  /-- BX6': `S(φ ∧ S(ψ, φ), φ) → S(ψ, φ)` -/
  | absorb_since (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ (StarFormula.and φ (StarFormula.snce φ ψ))).imp
        (StarFormula.snce φ ψ))
  /-- BX7: linearity of Until -/
  | linear_until (φ ψ χ θ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.untl φ ψ) (StarFormula.untl χ θ)
        |>.imp (StarFormula.or
          (StarFormula.or
            (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and ψ θ))
            (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and ψ χ)))
          (StarFormula.untl (StarFormula.and φ χ) (StarFormula.and φ θ))))
  /-- BX7': linearity of Since -/
  | linear_since (φ ψ χ θ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.snce φ ψ) (StarFormula.snce χ θ)
        |>.imp (StarFormula.or
          (StarFormula.or
            (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and ψ θ))
            (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and ψ χ)))
          (StarFormula.snce (StarFormula.and φ χ) (StarFormula.and φ θ))))
  /-- BX10: `U(ψ, φ) → F(ψ)` -/
  | until_F (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl φ ψ).imp (StarFormula.someFuture ψ))
  /-- BX10': `S(ψ, φ) → P(ψ)` -/
  | since_P (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce φ ψ).imp (StarFormula.somePast ψ))
  /-- BX11: `F(φ) ∧ F(ψ) → F(φ ∧ ψ) ∨ F(φ ∧ F(ψ)) ∨ F(F(φ) ∧ ψ)` -/
  | temp_linearity (φ ψ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.someFuture φ) (StarFormula.someFuture ψ) |>.imp
        (StarFormula.or (StarFormula.someFuture (StarFormula.and φ ψ))
          (StarFormula.or (StarFormula.someFuture (StarFormula.and φ (StarFormula.someFuture ψ)))
            (StarFormula.someFuture (StarFormula.and (StarFormula.someFuture φ) ψ)))))
  /-- BX11': `P(φ) ∧ P(ψ) → P(φ ∧ ψ) ∨ P(φ ∧ P(ψ)) ∨ P(P(φ) ∧ ψ)` -/
  | temp_linearity_past (φ ψ : StarFormula) :
      StarAxiom (StarFormula.and (StarFormula.somePast φ) (StarFormula.somePast ψ) |>.imp
        (StarFormula.or (StarFormula.somePast (StarFormula.and φ ψ))
          (StarFormula.or (StarFormula.somePast (StarFormula.and φ (StarFormula.somePast ψ)))
            (StarFormula.somePast (StarFormula.and (StarFormula.somePast φ) ψ)))))
  /-- BX12: `F(φ) → U(φ, ⊤)` -/
  | F_until_equiv (φ : StarFormula) :
      StarAxiom ((StarFormula.someFuture φ).imp
        (StarFormula.untl (StarFormula.bot.imp StarFormula.bot) φ))
  /-- BX12': `P(φ) → S(φ, ⊤)` -/
  | P_since_equiv (φ : StarFormula) :
      StarAxiom ((StarFormula.somePast φ).imp
        (StarFormula.snce (StarFormula.bot.imp StarFormula.bot) φ))
  -- Layer 4: Modal-Temporal Interaction (1)
  /-- Modal-Future: `□φ → □(Gφ)` -/
  | modal_future (φ : StarFormula) :
      StarAxiom ((StarFormula.box φ).imp (StarFormula.box (StarFormula.allFuture φ)))
  -- Layer 5: Uniformity (5)
  /-- `U(⊤,⊥) → S(⊤,⊥)` -/
  | discrete_symm_fwd :
      StarAxiom ((StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).imp
        (StarFormula.snce StarFormula.bot (StarFormula.bot.imp StarFormula.bot)))
  /-- `S(⊤,⊥) → U(⊤,⊥)` -/
  | discrete_symm_bwd :
      StarAxiom ((StarFormula.snce StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).imp
        (StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)))
  /-- `U(⊤,⊥) → G(U(⊤,⊥))` -/
  | discrete_propagate_fwd :
      StarAxiom ((StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).imp
        (StarFormula.allFuture
          (StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot))))
  /-- `U(⊤,⊥) → H(U(⊤,⊥))` -/
  | discrete_propagate_bwd :
      StarAxiom ((StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).imp
        (StarFormula.allPast
          (StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot))))
  /-- `U(⊤,⊥) → □(U(⊤,⊥))` -/
  | discrete_box_necessity :
      StarAxiom ((StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).imp
        (StarFormula.box (StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot))))
  -- Layer 6: Prior (2)
  /-- Prior-UZ: `F(φ) → U(φ, ¬φ)` -/
  | prior_UZ (φ : StarFormula) :
      StarAxiom (φ.someFuture.imp (StarFormula.untl φ.neg φ))
  /-- Prior-SZ: `P(φ) → S(φ, ¬φ)` -/
  | prior_SZ (φ : StarFormula) :
      StarAxiom (φ.somePast.imp (StarFormula.snce φ.neg φ))
  -- Layer 7: Z1 (1)
  /-- Z1: `G(Gφ→φ) → (FGφ→Gφ)` -/
  | z1 (φ : StarFormula) :
      StarAxiom ((φ.allFuture.imp φ).allFuture.imp (φ.allFuture.someFuture.imp φ.allFuture))
  -- Layer 8: Density (2)
  /-- Density: `GGφ → Gφ` -/
  | density (φ : StarFormula) :
      StarAxiom (φ.allFuture.allFuture.imp φ.allFuture)
  /-- Dense indicator: `¬U(⊤,⊥)` -/
  | dense_indicator :
      StarAxiom (StarFormula.untl StarFormula.bot (StarFormula.bot.imp StarFormula.bot)).neg
  -- Layer 9: Reynolds Dedekind (3)
  /-- Prior-U (gap form): `U(⊤,φ) ∧ F(¬φ) → U(¬φ ∨ K⁺(¬φ), φ)` -/
  | prior_U_gap (φ : StarFormula) :
      StarAxiom ((StarFormula.and (StarFormula.untl φ StarFormula.top) φ.neg.someFuture).imp
        (StarFormula.untl φ (StarFormula.or φ.neg (StarFormula.kPlus φ.neg))))
  /-- Prior-S (gap form): `S(⊤,φ) ∧ P(¬φ) → S(¬φ ∨ K⁻(¬φ), φ)` -/
  | prior_S_gap (φ : StarFormula) :
      StarAxiom ((StarFormula.and (StarFormula.snce φ StarFormula.top) φ.neg.somePast).imp
        (StarFormula.snce φ (StarFormula.or φ.neg (StarFormula.kMinus φ.neg))))
  /-- Sep: `K⁺φ ∧ ¬K⁺(φ ∧ U(φ,¬φ)) → K⁺(K⁺φ ∧ K⁻φ)` -/
  | sep (φ : StarFormula) :
      StarAxiom ((StarFormula.and (StarFormula.kPlus φ)
        (StarFormula.kPlus (StarFormula.and φ (StarFormula.untl φ.neg φ))).neg).imp
        (StarFormula.kPlus (StarFormula.and (StarFormula.kPlus φ) (StarFormula.kMinus φ))))
  -- The stability modal (8)
  /-- SK: `⊡(φ → ψ) → (⊡φ → ⊡ψ)` — K for `⊡`, from the universal-quantifier shape of the
  `stab` clause (paper line 1114). -/
  | stab_k (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.stab (φ.imp ψ)).imp ((StarFormula.stab φ).imp (StarFormula.stab ψ)))
  /-- ST: `⊡φ → φ` — T for `⊡` (paper footnote, line 1118); `Semantics.of_stab`. -/
  | stab_t (φ : StarFormula) : StarAxiom ((StarFormula.stab φ).imp φ)
  /-- S4: `⊡φ → ⊡⊡φ` (paper footnote, line 1118); `Semantics.stab_four`. -/
  | stab_4 (φ : StarFormula) :
      StarAxiom ((StarFormula.stab φ).imp (StarFormula.stab (StarFormula.stab φ)))
  /-- S5: `⟐φ → ⊡⟐φ`, stated as `¬⊡¬φ → ⊡¬⊡¬φ` through `dstab` (paper footnote, line 1118);
  `Semantics.stab_five` at `¬φ`. -/
  | stab_5 (φ : StarFormula) :
      StarAxiom ((dstab φ).imp (StarFormula.stab (dstab φ)))
  /-- MS: `□φ → ⊡φ` — `⟨τ⟩_x ⊆ H_F` (paper line 1108); `Semantics.stab_of_box`. -/
  | box_stab (φ : StarFormula) : StarAxiom ((StarFormula.box φ).imp (StarFormula.stab φ))
  /-- AS: `p → ⊡p` for atoms (paper footnote, line 1119); `Semantics.stab_atom_of_atom`. -/
  | atom_stab (p : Atom) :
      StarAxiom ((StarFormula.atom p).imp (StarFormula.stab (StarFormula.atom p)))
  /-- PS (same-time pasting): `⟐φ⁺ → (⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻))` for pure-future `φ⁺` and pure-past
  `ψ⁻`; `Semantics.paste_valid`. -/
  | paste (φ ψ : StarFormula) (hφ : IsPureFuture φ) (hψ : IsPurePast ψ) :
      StarAxiom ((dstab φ).imp ((dstab ψ).imp (dstab (φ.and ψ))))
  /-- US (future pasting): `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)` for pure-past `α⁻` and pure-future `φ⁺`;
  `Semantics.untl_dstab_valid`. -/
  | untl_paste (α φ : StarFormula) (hα : IsPurePast α) (hφ : IsPureFuture φ) :
      StarAxiom ((StarFormula.untl α (dstab φ)).imp (dstab (StarFormula.untl α φ)))

/--
Minimum frame class of each TM⋆ schema. The TM⁺ arms are `Axiom.minFrameClass`'s
(`ProofSystem/Axioms.lean`); every `⊡` schema is valid over every task frame and is routed to
`.Base`.
-/
def StarAxiom.minFrameClass {φ : StarFormula} : StarAxiom φ → FrameClass
  | .density _ => .Dense
  | .dense_indicator => .Dense
  | .prior_UZ _ => .ZTime
  | .prior_SZ _ => .ZTime
  | .z1 _ => .ZTime
  | .prior_U_gap _ => .RTime
  | .prior_S_gap _ => .RTime
  | .sep _ => .RTime
  | _ => .Base

/-! ### Pins -/

example (φ : StarFormula) : (StarAxiom.stab_t φ).minFrameClass = .Base := rfl
example (φ : StarFormula) : (StarAxiom.density φ).minFrameClass = .Dense := rfl
example (φ ψ : StarFormula) (hφ : IsPureFuture φ) (hψ : IsPurePast ψ) :
    (StarAxiom.paste φ ψ hφ hψ).minFrameClass = .Base := rfl

end FormalSystem.StarLanguage
