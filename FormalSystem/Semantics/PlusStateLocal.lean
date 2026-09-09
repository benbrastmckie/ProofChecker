/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Semantics.PlusNonValidities

/-!
# State-locality: the L⁺ fragment whose truth is fixed by the present world state

`PlusFormula.StateLocal` is a syntactic fragment of L⁺
(`FormalSystem/PlusLanguage/Formula.lean`), and `IsPlusStateLocal` is the semantic property it
approximates: at a fixed time `t`, two possible worlds carrying the *same world state at `t`*
agree about `φ`. That is exactly the class `⊡` quantifies over, so a state-local `φ` is already
`⊡`-stable — the headline `φ ↔ ⊡φ` below.

## Main Definitions

- `PlusFormula.StateLocal` — the syntactic fragment, by structural recursion
- `IsPlusStateLocal` — the semantic property: `SameStateAt τ σ t` transfers truth at `t`

## Main Results

- `isPlusStateLocal_box`, `isPlusStateLocal_stab`
- `isPlusStateLocal_of_stateLocal`
- `not_isPlusStateLocal_someFuture`, `not_isPlusStateLocal_somePast`
- `plusStateLocal_stab_iff`, `plusStateLocal_plusValid_iff_stab`
- `stab_of_stateLocal`

## Tags

plus-language · state-locality · stability-modal · fragment
-/

namespace FormalSystem.PlusLanguage

open FormalSystem.Syntax

/--
**The state-locality fragment of L⁺**, by structural recursion.

`atom`, `bot` and `imp` are the propositional core; `box` and `stab` are admitted for an
arbitrary argument (see `Semantics/PlusStateLocal.lean`'s `isPlusStateLocal_box` and
`isPlusStateLocal_stab`); and `untl`, `snce` are excluded, each with a countermodel in that
module.

Sufficient, not necessary — see the module docstring's "Sound, not complete".
-/
def PlusFormula.StateLocal : PlusFormula → Prop
  | .atom _ => True
  | .bot => True
  | .imp φ ψ => PlusFormula.StateLocal φ ∧ PlusFormula.StateLocal ψ
  | .box _ => True
  | .untl _ _ => False
  | .snce _ _ => False
  | .stab _ => True

/-- Atoms are state-local: an atom reads the world state at the evaluation time and nothing
else. -/
@[simp] theorem stateLocal_atom (p : Atom) : (PlusFormula.atom p).StateLocal := trivial

/-- `⊥` is state-local: it is constant. -/
@[simp] theorem stateLocal_bot : PlusFormula.bot.StateLocal := trivial

/-- `φ → ψ` is state-local exactly when both sides are: the clause is pointwise. -/
@[simp] theorem stateLocal_imp_iff (φ ψ : PlusFormula) :
    (PlusFormula.imp φ ψ).StateLocal ↔ φ.StateLocal ∧ ψ.StateLocal := Iff.rfl

/-- `□φ` is state-local for an **arbitrary** `φ`: the `box` clause never mentions the history. -/
@[simp] theorem stateLocal_box (φ : PlusFormula) : (PlusFormula.box φ).StateLocal := trivial

/-- `φ U ψ` is outside the fragment: it quantifies over later times, where two worlds agreeing
at `t` may diverge. -/
@[simp] theorem not_stateLocal_untl (ψ φ : PlusFormula) : ¬ (PlusFormula.untl ψ φ).StateLocal :=
  id

/-- `φ S ψ` is outside the fragment: it quantifies over earlier times, likewise. -/
@[simp] theorem not_stateLocal_snce (ψ φ : PlusFormula) : ¬ (PlusFormula.snce ψ φ).StateLocal :=
  id

/-- `⊡φ` is state-local for an **arbitrary** `φ`: the class `⟨τ⟩ₜ` is fixed by the state at
`t`. -/
@[simp] theorem stateLocal_stab (φ : PlusFormula) : (PlusFormula.stab φ).StateLocal := trivial

/-- `F φ` is outside the fragment: it is an `untl`. -/
@[simp] theorem not_stateLocal_someFuture (φ : PlusFormula) :
    ¬ (PlusFormula.someFuture φ).StateLocal := id

/-- `P φ` is outside the fragment: it is a `snce`. -/
@[simp] theorem not_stateLocal_somePast (φ : PlusFormula) :
    ¬ (PlusFormula.somePast φ).StateLocal := id

/-- The negation of a state-local formula is state-local: `¬φ` is `φ → ⊥`. -/
theorem StateLocal.neg {φ : PlusFormula} (hφ : φ.StateLocal) : φ.neg.StateLocal :=
  ⟨hφ, trivial⟩

/-- Conjunction stays inside the fragment. -/
theorem StateLocal.and {φ ψ : PlusFormula} (hφ : φ.StateLocal) (hψ : ψ.StateLocal) :
    (PlusFormula.and φ ψ).StateLocal :=
  ⟨⟨hφ, hψ, trivial⟩, trivial⟩

/-- Disjunction stays inside the fragment. -/
theorem StateLocal.or {φ ψ : PlusFormula} (hφ : φ.StateLocal) (hψ : ψ.StateLocal) :
    (PlusFormula.or φ ψ).StateLocal :=
  ⟨⟨hφ, trivial⟩, hψ⟩

end FormalSystem.PlusLanguage
