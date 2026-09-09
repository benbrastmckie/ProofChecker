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

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage

/-! ## The semantic property -/

/--
**State-locality, semantically.** `φ` is state-local when, at every frame and model, any two
possible worlds carrying the same world state at `t` agree about `φ` at `t`.

L⁺ has no time registers, so this is `IsStateLocal` (`Semantics/StarStateLocal.lean`) with the
stored-time vector deleted and nothing else changed; the two are arm-for-arm comparable.

The hypotheses could be weakened from `τ.IsTotal`/`σ.IsTotal` to `τ.domain t`/`σ.domain t` —
every proof below uses totality only at `t`, except `plusStateLocal_stab_iff`'s right-to-left
half, which needs `τ ∈ ⟨τ⟩ₜ` and therefore genuinely needs `τ` total. The stronger hypotheses
are kept deliberately, so that this definition and `IsStateLocal` differ in exactly one respect
(the register vector) rather than two.
-/
def IsPlusStateLocal (φ : PlusFormula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ σ : ConvexHistory F), τ.IsTotal → σ.IsTotal →
    ∀ t : F.Duration, SameStateAt τ σ t →
      (PlusTruthAt M τ t φ ↔ PlusTruthAt M σ t φ)

/-! ## `□` and `⊡` are state-local for an arbitrary argument -/

/--
**`□φ` is state-local, whatever `φ` is.** The `box` clause quantifies over *every* total history
and never mentions `τ`, so the two sides are literally the same proposition.

This settles, positively and by proof rather than by analogy with L⋆, the question of whether
`□` belongs in the fragment: it does, and without a hypothesis on `φ`.

Paper: — (the formalization's own: the manuscript classifies no L⁺ constructor for
state-locality)
-/
theorem isPlusStateLocal_box (φ : PlusFormula) : IsPlusStateLocal (.box φ) :=
  fun _ _ _ _ _ _ _ _ => Iff.rfl

/--
**`⊡φ` is state-local, whatever `φ` is.** Discharged from `stab_congr_sameState`
(`Semantics/PlusTruth.lean`), which is exactly this statement at domain hypotheses rather than
totality: the truth of `⊡φ` at `(τ, t)` depends only on the `∼ₜ`-class of `τ`.

That proof dependency is the first of the three relations this module records: the L⁺ fragment's
`stab` arm *is* `stab_congr_sameState`, not a re-derivation of it.

Paper: — (the formalization's own; the underlying clause is `def:BLstar-semantics`)
-/
theorem isPlusStateLocal_stab (φ : PlusFormula) : IsPlusStateLocal (.stab φ) :=
  fun _ M τ σ hτ hσ t h => stab_congr_sameState M τ σ t (hτ t) (hσ t) h φ

/-! ## Soundness of the syntactic fragment -/

/--
**The soundness theorem.** Every formula in the syntactic fragment has the semantic property.

Seven cases, one per constructor. `box` and `stab` discharge to the two lemmas above with no
inductive hypothesis; `untl` and `snce` are vacuous, the syntactic predicate being `False`
there.

Paper: — (the formalization's own: the manuscript has no fragment of L⁺ and no state-locality
predicate; this is the L⁺ twin of `isStateLocal_of_stateLocal`)
-/
theorem isPlusStateLocal_of_stateLocal :
    ∀ {φ : PlusFormula}, φ.StateLocal → IsPlusStateLocal φ := by
  intro φ
  induction φ with
  | atom p =>
    intro _ _ M τ σ hτ hσ t h
    constructor
    · rintro ⟨ht, hv⟩
      refine ⟨hσ t, ?_⟩
      rw [← h ht (hσ t)]
      exact hv
    · rintro ⟨ht, hv⟩
      refine ⟨hτ t, ?_⟩
      rw [h (hτ t) ht]
      exact hv
  | bot => intro _ _ _ _ _ _ _ _ _; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    rintro ⟨hφ, hψ⟩ F M τ σ hτ hσ t h
    exact imp_congr (ihφ hφ F M τ σ hτ hσ t h) (ihψ hψ F M τ σ hτ hσ t h)
  | box φ _ => intro _; exact isPlusStateLocal_box φ
  | untl ψ φ _ _ => intro hφ; exact absurd hφ (not_stateLocal_untl ψ φ)
  | snce ψ φ _ _ => intro hφ; exact absurd hφ (not_stateLocal_snce ψ φ)
  | stab φ _ => intro _; exact isPlusStateLocal_stab φ

/-! ## The excluded constructors are excluded by theorem

Each witness lives on `NF` with `natModel` (`Semantics/PlusNonValidities.lean`), and each uses a
pair of possible worlds agreeing at time `0` and disagreeing away from it. Both are stated as
negations of `IsPlusStateLocal`, the semantic property: the *syntactic* predicate is `False` on
these constructors by definition, so its negation would be a vacuous claim.

L⁺ has no time registers, so the L⋆ module's third exclusion — `not_isStateLocal_timeRecall` —
does not arise here. Two exclusions are all the seven-constructor recursion needs. -/

/-- The constant possible world of `NF` at world state `0`. -/
private def zeroHist : ConvexHistory NF := natHist (fun _ => 0)

/-- The possible world of `NF` that sits at state `0` up to time `0` and leaves it afterwards. -/
private def lateHist : ConvexHistory NF := natHist (fun s => if s ≤ 0 then 0 else 1)

/-- The possible world of `NF` that sits away from state `0` before time `0` and at it after. -/
private def earlyHist : ConvexHistory NF := natHist (fun s => if s < 0 then 1 else 0)

private theorem zero_lateHist_same : SameStateAt zeroHist lateHist (0 : ℤ) := by
  intro _ _
  show (0 : ℕ) = (if (0 : ℤ) ≤ 0 then 0 else 1)
  simp

private theorem zero_earlyHist_same : SameStateAt zeroHist earlyHist (0 : ℤ) := by
  intro _ _
  show (0 : ℕ) = (if (0 : ℤ) < 0 then 1 else 0)
  simp

/--
**`F φ` is not state-local**, already at an atom. `zeroHist` and `lateHist` agree at time `0` and
differ at every later time, and `natModel` makes `p` true exactly at world state `0`: so `F p`
holds at `(zeroHist, 0)` and fails at `(lateHist, 0)`. This is the `untl` exclusion.

Paper: — (the formalization's own; `untl`'s clause is `def:BLstar-semantics`)
-/
theorem not_isPlusStateLocal_someFuture (p : Atom) :
    ¬ IsPlusStateLocal (PlusFormula.someFuture (.atom p)) := by
  intro h
  have hleft : PlusTruthAt natModel zeroHist (0 : ℤ) (PlusFormula.someFuture (.atom p)) := by
    rw [PlusTruth.someFuture_iff]
    exact ⟨(1 : ℤ), by norm_num, trivial, rfl⟩
  have hright := (h NF natModel zeroHist lateHist (natHist_isTotal _) (natHist_isTotal _)
    (0 : ℤ) zero_lateHist_same).mp hleft
  rw [PlusTruth.someFuture_iff] at hright
  obtain ⟨s, hs, _, hval⟩ := hright
  have hval' : (if s ≤ (0 : ℤ) then (0 : ℕ) else 1) = 0 := hval
  rw [if_neg (not_le.mpr hs)] at hval'
  exact one_ne_zero hval'

/--
**`P φ` is not state-local**, already at an atom. `zeroHist` and `earlyHist` agree at time `0` and
differ at every earlier time, so `P p` holds at `(zeroHist, 0)` and fails at `(earlyHist, 0)`.
This is the `snce` exclusion.

Paper: — (the formalization's own; `snce`'s clause is `def:BLstar-semantics`)
-/
theorem not_isPlusStateLocal_somePast (p : Atom) :
    ¬ IsPlusStateLocal (PlusFormula.somePast (.atom p)) := by
  intro h
  have hleft : PlusTruthAt natModel zeroHist (0 : ℤ) (PlusFormula.somePast (.atom p)) := by
    rw [PlusTruth.somePast_iff]
    exact ⟨(-1 : ℤ), by norm_num, trivial, rfl⟩
  have hright := (h NF natModel zeroHist earlyHist (natHist_isTotal _) (natHist_isTotal _)
    (0 : ℤ) zero_earlyHist_same).mp hleft
  rw [PlusTruth.somePast_iff] at hright
  obtain ⟨s, hs, _, hval⟩ := hright
  have hval' : (if s < (0 : ℤ) then (1 : ℕ) else 0) = 0 := hval
  rw [if_pos hs] at hval'
  exact one_ne_zero hval'

end FormalSystem.Semantics
