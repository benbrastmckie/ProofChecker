/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.PlusLanguage.Formula

/-!
# `StarFormula` — the language L⋆: L⁺ plus the time store/recall operators

This module defines the language **L⋆**, obtained from L⁺
(`FormalSystem/PlusLanguage/Formula.lean`) by adding the manuscript's two **hybrid time
registers**:

```
φ, ψ ::= pᵢ | ⊥ | φ → ψ | □φ | φ U ψ | φ S ψ | ⊡φ | ↑ⁱφ | ↓ⁱφ
```

`↑ⁱ` (`timeStore i`) stores the current time in register `i`; `↓ⁱ` (`timeRecall i`) moves
evaluation to the time held in register `i`. The manuscript's `def:BLstar-semantics` interprets
exactly these two together with `⊡` over points `(τ, x, v⃗)`, `v⃗` a vector of stored **times**,
suppressing the world registers `↑_M`/`↓_M`; this component follows that presentation.

## Why a separate inductive rather than two more `PlusFormula` constructors

`PlusFormula` must not grow store/recall constructors. The atomization route to TM⁺ soundness
(`Metalogic/Conservativity/Plus/Atomization.lean`) rests on `stab_state_only`
(`Semantics/PlusTruth.lean`): `⊡φ`'s truth depends on the world state alone, at any time. That
invariant is **false inside a recall scope** — `⊡↓ⁱφ` reaches back to a time the register names,
which the present world state does not determine — so adding the operators to `PlusFormula`
would silently invalidate a landed conservativity result. `StarFormula` is therefore a separate
inductive with a constructor-to-constructor embedding `ofPlus`, exactly the landed
`MinusFormula`/`PlusFormula` pattern.

## Design

Every derived operator below has the **same right-hand side** as its `PlusFormula` namesake, so
`ofPlus` commutes with each of them by `rfl`; the `rfl` pins at the end of the file are that
contract. The `⊡`-specific operators (`dstab`, `Will`, `will`, `Could`, `could`) are mirrored
too, so no consumer has to reach back into `PlusFormula` for them.

## Main Definitions

- `StarFormula`: nine-constructor inductive type for L⋆; `StarContext := List StarFormula`
- Derived operators with `PlusFormula`'s right-hand sides: `top`, `neg`, `and`, `or`, `iff`,
  `diamond`, `someFuture`, `somePast`, `allFuture`, `allPast`, `kPlus`, `kMinus`, `always`,
  `sometimes`, `next`, `prev`, `dstab`, `Will`, `will`, `Could`, `could`
- `ofPlus`, `ofStarCtx`: the embedding of L⁺ into L⋆ and its context lift

## Main Results

- `DecidableEq`, `Countable`, `Infinite`, `Denumerable` for `StarFormula`
- `ofPlus_injective`, and the `rfl`-shaped commutation lemmas `ofPlus_neg`, `ofPlus_allFuture`,
  `ofPlus_always`, `ofPlus_someFuture`, `ofPlus_or`, `ofPlus_top`
- `ofPlus_ne_timeStore`, `ofPlus_ne_timeRecall`: nothing in the image of the embedding is a
  top-level register operator

## Module Invariant

**Nothing under `FormalSystem/StarLanguage/` imports anything from `FormalSystem/Semantics/`.**
Checkable by `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/`. The invariant
is directional, exactly as for `MinusLanguage/` and `PlusLanguage/`: the converse edge is
permitted and is how L⋆ acquires its semantics
(`FormalSystem/Semantics/StarTruth.lean`).

## Reserved and unbuilt

`StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` are **reserved names, deliberately not
declared here**. This component is semantic-only: the manuscript supplies no proof system for
`\BL^\star`, and every result this component was built for
(`app:deterministic-future`, the discrimination footnote, Theorem C's `Det-pm` half) is a
semantic one. See `FormalSystem/StarLanguage/README.md`.

## References

* JPL paper `possible_worlds.tex` — `def:BLstar-semantics` (the store/recall clauses and the
  point `(τ, x, v⃗)`), `sub:Extension`, `sent:det`, `app:deterministic-future`
* `FormalSystem/PlusLanguage/Formula.lean` — the L⁺ side whose operators are mirrored here
* `FormalSystem/Semantics/StarTruth.lean` — `StarTruthAt`, the truth recursion over
  `(τ, x, v⃗)`

## Tags

star-language · store-recall · time-register · hybrid-logic
-/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.PlusLanguage

/--
Formula type for the language L⋆: the seven constructors of `PlusFormula` plus the two time
registers of `def:BLstar-semantics`.

Constructor order and argument order (guard first, event second for `untl`/`snce`) are those of
`FormalSystem.PlusLanguage.PlusFormula`, so that `ofPlus` is constructor-to-constructor.
-/
inductive StarFormula : Type where
  /-- Propositional atom (variable). -/
  | atom : Atom → StarFormula
  /-- Bottom (`⊥`, falsum). -/
  | bot : StarFormula
  /-- Implication (`φ → ψ`). -/
  | imp : StarFormula → StarFormula → StarFormula
  /-- Modal necessity (`□φ`). -/
  | box : StarFormula → StarFormula
  /-- Until, `φ U ψ`, guard first and event second, exactly as `PlusFormula.untl`. -/
  | untl : StarFormula → StarFormula → StarFormula
  /-- Since, `φ S ψ`, guard first and event second, exactly as `PlusFormula.snce`. -/
  | snce : StarFormula → StarFormula → StarFormula
  /-- The stability modal `⊡φ` (`def:BLstar-semantics`). -/
  | stab : StarFormula → StarFormula
  /-- Time store `↑ⁱφ` (`def:BLstar-semantics`): evaluate `φ` with the current time written into
      register `i`. -/
  | timeStore : ℕ → StarFormula → StarFormula
  /-- Time recall `↓ⁱφ` (`def:BLstar-semantics`): evaluate `φ` at the time held in register
      `i`. -/
  | timeRecall : ℕ → StarFormula → StarFormula
  deriving Repr, DecidableEq, Countable

/-- `StarFormula.atom` is injective. -/
theorem StarFormula.atom_injective : Function.Injective StarFormula.atom := by
  intro a b h
  injection h

/-- `StarFormula` is infinite, via the injection of atoms. -/
instance : Infinite StarFormula :=
  Infinite.of_injective StarFormula.atom StarFormula.atom_injective

/-- `StarFormula` is denumerable (countable + infinite), exactly as `PlusFormula` obtains it. -/
noncomputable instance : Denumerable StarFormula :=
  Classical.choice (nonempty_denumerable StarFormula)

/-- Contexts of L⋆ formulas. -/
abbrev StarContext := List StarFormula

namespace StarFormula

/-! ### Derived operators

Each right-hand side is copied verbatim from `PlusLanguage/Formula.lean`, so that `ofPlus`
commutes with it by `rfl` (see the pins at the end of the file). -/

/-- Top (`⊤`): `⊥ → ⊥`. Mirrors `PlusFormula.top`. -/
def top : StarFormula := StarFormula.bot.imp StarFormula.bot

/-- Negation (`¬φ`): `φ → ⊥`. Mirrors `PlusFormula.neg`. -/
def neg (φ : StarFormula) : StarFormula := φ.imp bot

/-- Existential future (`Fφ`): `⊤ U φ`. Mirrors `PlusFormula.someFuture`. -/
def someFuture (φ : StarFormula) : StarFormula := StarFormula.untl StarFormula.top φ

/-- Existential past (`Pφ`): `⊤ S φ`. Mirrors `PlusFormula.somePast`. -/
def somePast (φ : StarFormula) : StarFormula := StarFormula.snce StarFormula.top φ

/-- Universal future (`Gφ`): `¬F¬φ`. Mirrors `PlusFormula.allFuture`. -/
def allFuture (φ : StarFormula) : StarFormula := (someFuture φ.neg).neg

/-- Universal past (`Hφ`): `¬P¬φ`. Mirrors `PlusFormula.allPast`. -/
def allPast (φ : StarFormula) : StarFormula := (somePast φ.neg).neg

/-- Reynolds' `K⁺`: `¬U(¬φ, ⊤)` in guard-first order. Mirrors `PlusFormula.kPlus`. -/
def kPlus (φ : StarFormula) : StarFormula := (StarFormula.untl φ.neg StarFormula.top).neg

/-- Reynolds' `K⁻`: `¬S(¬φ, ⊤)` in guard-first order. Mirrors `PlusFormula.kMinus`. -/
def kMinus (φ : StarFormula) : StarFormula := (StarFormula.snce φ.neg StarFormula.top).neg

/-- Conjunction (`φ ∧ ψ`): `¬(φ → ¬ψ)`. Mirrors `PlusFormula.and`. -/
def and (φ ψ : StarFormula) : StarFormula := (φ.imp ψ.neg).neg

/-- Disjunction (`φ ∨ ψ`): `¬φ → ψ`. Mirrors `PlusFormula.or`. -/
def or (φ ψ : StarFormula) : StarFormula := φ.neg.imp ψ

/-- Biconditional (`φ ↔ ψ`): `(φ → ψ) ∧ (ψ → φ)`. Mirrors `PlusFormula.iff`. -/
def iff (φ ψ : StarFormula) : StarFormula := (φ.imp ψ).and (ψ.imp φ)

/-- Modal possibility (`◇φ`): `¬□¬φ`. Mirrors `PlusFormula.diamond`. -/
def diamond (φ : StarFormula) : StarFormula := φ.neg.box.neg

/-- Temporal `always` (`△φ`): `Hφ ∧ (φ ∧ Gφ)`. Mirrors `PlusFormula.always`. -/
def always (φ : StarFormula) : StarFormula := φ.allPast.and (φ.and φ.allFuture)

/-- Temporal `sometimes` (`▽φ`): `¬△¬φ`. Mirrors `PlusFormula.sometimes`. -/
def sometimes (φ : StarFormula) : StarFormula := φ.neg.always.neg

/-- Next-step (`Xφ`): `⊥ U φ`. Mirrors `PlusFormula.next`. -/
def next (φ : StarFormula) : StarFormula := StarFormula.untl StarFormula.bot φ

/-- Previous-step (`Yφ`): `⊥ S φ`. Mirrors `PlusFormula.prev`. -/
def prev (φ : StarFormula) : StarFormula := StarFormula.snce StarFormula.bot φ

/-! ### The `⊡`-specific operators, mirrored from L⁺ -/

/-- The dual stability modal `⟐φ := ¬⊡¬φ`. Mirrors `PlusFormula.dstab`. -/
def dstab (φ : StarFormula) : StarFormula := neg (.stab (neg φ))

/-- `Will φ := ⊡Gφ`. Mirrors `PlusFormula.Will`. -/
def Will (φ : StarFormula) : StarFormula := .stab (allFuture φ)

/-- `will φ := ⊡Fφ`. Mirrors `PlusFormula.will`. -/
def will (φ : StarFormula) : StarFormula := .stab (someFuture φ)

/-- `Could φ := ⟐Gφ`. Mirrors `PlusFormula.Could`. -/
def Could (φ : StarFormula) : StarFormula := dstab (allFuture φ)

/-- `could φ := ⟐Fφ`. Mirrors `PlusFormula.could`. -/
def could (φ : StarFormula) : StarFormula := dstab (someFuture φ)

end StarFormula

/-! ## The embedding of L⁺ into L⋆ -/

/-- The embedding of L⁺ into L⋆, constructor to constructor. Nothing in its image mentions a
time register, which is why `StarTruthAt` evaluates it independently of the stored-time vector
(`starTruthAt_ofPlus`, `Semantics/StarTruth.lean`). -/
def ofPlus : PlusFormula → StarFormula
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (ofPlus φ) (ofPlus ψ)
  | .box φ => .box (ofPlus φ)
  | .untl φ ψ => .untl (ofPlus φ) (ofPlus ψ)
  | .snce φ ψ => .snce (ofPlus φ) (ofPlus ψ)
  | .stab φ => .stab (ofPlus φ)

/-- `ofPlus` is injective. Per-constructor `cases` on the target with the induction hypotheses
applied by `rw`, exactly as `ofFormula_injective` does. -/
theorem ofPlus_injective : Function.Injective ofPlus := by
  intro φ ψ h
  induction φ generalizing ψ with
  | atom a => cases ψ <;> simp_all [ofPlus]
  | bot => cases ψ <;> simp_all [ofPlus]
  | imp φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [ofPlus] at h
    rw [ih₁ h.1, ih₂ h.2]
  | box φ ih =>
    cases ψ <;> simp [ofPlus] at h
    rw [ih h]
  | untl φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [ofPlus] at h
    rw [ih₁ h.1, ih₂ h.2]
  | snce φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [ofPlus] at h
    rw [ih₁ h.1, ih₂ h.2]
  | stab φ ih =>
    cases ψ <;> simp [ofPlus] at h
    rw [ih h]

/-- Nothing in the range of `ofPlus` is a top-level `timeStore`. -/
@[simp] theorem ofPlus_ne_timeStore (φ : PlusFormula) (i : ℕ) (ψ : StarFormula) :
    ofPlus φ ≠ StarFormula.timeStore i ψ := by
  cases φ <;> simp [ofPlus]

/-- Nothing in the range of `ofPlus` is a top-level `timeRecall`. -/
@[simp] theorem ofPlus_ne_timeRecall (φ : PlusFormula) (i : ℕ) (ψ : StarFormula) :
    ofPlus φ ≠ StarFormula.timeRecall i ψ := by
  cases φ <;> simp [ofPlus]

/-- The embedding lifted to contexts. Definitionally `List.map ofPlus`. -/
abbrev ofStarCtx (Γ : PlusContext) : StarContext := List.map ofPlus Γ

@[simp] theorem ofStarCtx_nil : ofStarCtx [] = [] := rfl

@[simp] theorem ofStarCtx_cons (φ : PlusFormula) (Γ : PlusContext) :
    ofStarCtx (φ :: Γ) = ofPlus φ :: ofStarCtx Γ := rfl

/-- Membership transports through `ofPlus`. -/
theorem mem_ofStarCtx {φ : PlusFormula} {Γ : PlusContext} (h : φ ∈ Γ) : ofPlus φ ∈ ofStarCtx Γ :=
  List.mem_map_of_mem h

/-! ### `rfl` pins

`ofPlus` commutes with every derived operator **definitionally**, because each L⋆ operator was
given `PlusFormula`'s right-hand side verbatim. If one of these stops being `rfl`, the fix is in
the operator's right-hand side above, never at the use site. -/

theorem ofPlus_top : ofPlus PlusFormula.top = StarFormula.top := rfl

theorem ofPlus_neg (φ : PlusFormula) : ofPlus φ.neg = (ofPlus φ).neg := rfl

theorem ofPlus_and (φ ψ : PlusFormula) :
    ofPlus (φ.and ψ) = (ofPlus φ).and (ofPlus ψ) := rfl

theorem ofPlus_or (φ ψ : PlusFormula) :
    ofPlus (φ.or ψ) = (ofPlus φ).or (ofPlus ψ) := rfl

theorem ofPlus_someFuture (φ : PlusFormula) :
    ofPlus (PlusFormula.someFuture φ) = StarFormula.someFuture (ofPlus φ) := rfl

theorem ofPlus_somePast (φ : PlusFormula) :
    ofPlus (PlusFormula.somePast φ) = StarFormula.somePast (ofPlus φ) := rfl

theorem ofPlus_allFuture (φ : PlusFormula) :
    ofPlus (PlusFormula.allFuture φ) = StarFormula.allFuture (ofPlus φ) := rfl

theorem ofPlus_allPast (φ : PlusFormula) :
    ofPlus (PlusFormula.allPast φ) = StarFormula.allPast (ofPlus φ) := rfl

theorem ofPlus_always (φ : PlusFormula) :
    ofPlus (PlusFormula.always φ) = StarFormula.always (ofPlus φ) := rfl

theorem ofPlus_sometimes (φ : PlusFormula) :
    ofPlus (PlusFormula.sometimes φ) = StarFormula.sometimes (ofPlus φ) := rfl

theorem ofPlus_diamond (φ : PlusFormula) :
    ofPlus φ.diamond = (ofPlus φ).diamond := rfl

theorem ofPlus_dstab (φ : PlusFormula) :
    ofPlus (PlusFormula.dstab φ) = StarFormula.dstab (ofPlus φ) := rfl

example (φ ψ : PlusFormula) : ofPlus (φ.iff ψ) = (ofPlus φ).iff (ofPlus ψ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.kPlus φ) = StarFormula.kPlus (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.kMinus φ) = StarFormula.kMinus (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.next φ) = StarFormula.next (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.prev φ) = StarFormula.prev (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.Will φ) = StarFormula.Will (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.will φ) = StarFormula.will (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.Could φ) = StarFormula.Could (ofPlus φ) := rfl
example (φ : PlusFormula) : ofPlus (PlusFormula.could φ) = StarFormula.could (ofPlus φ) := rfl

end FormalSystem.StarLanguage
