/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Semantics.PlusNonValidities
import FormalSystem.Semantics.StarValidity

/-!
# `app:deterministic-future`, negative half — `sent:det` refuted over `NF`

`sent:det` is invalid over some non-deterministic task frame. The manuscript's own proof says
"by the same non-deterministic task frame `F'` and countermodel presented in
`app:deterministic`"; in this tree that countermodel is `NF = FrameOver.natFrame (D := ℤ)` with
`natHist`, `natModel`, and the history pair `τ = const 0` / `σ = fun s => if s ≤ 0 then 0 else 1`
that `refute_determined` (`Semantics/PlusNonValidities.lean`) already uses.

Reusing it is the fidelity-preserving choice, not a shortcut: the manuscript explicitly reuses
its own earlier countermodel, and this module reuses the tree's transcription of that
countermodel. Building a second two-state frame from scratch would duplicate it.

## The witnesses line up with the manuscript's `w₀`/`w₁`

`natModel`'s valuation is `n = 0`, so `|p| = {0}`. At `x = 0` and `y = 1`:

* `τ(0) = 0 = σ(0)`, so `σ ∈ ⟨τ⟩₀` — the manuscript's `σ(0) = w₀ = τ(0)`;
* `τ(1) = 0 ∈ |p|`, so `τ` itself refutes the `⊡↓²¬p` disjunct;
* `σ(1) = 1 ∉ |p|`, so `σ` refutes the `⊡↓²p` disjunct.

Both disjuncts of `settledDisj` therefore fail at `(τ, 0, v[0/v₁][1/v₂])`, and `sentDet_unfold`
carries the failure back to `sent:det` itself — exactly the manuscript's pair of witnesses.

## Main Results

- `refute_sentDet` — `app:deterministic-future`, negative half

## References

* JPL paper `app:deterministic-future` (negative half), `app:deterministic`, `sent:det`
* `FormalSystem/Semantics/PlusNonValidities.lean` — `NF`, `natHist`, `natModel`,
  `refute_determined`
* `FormalSystem/Semantics/StarDeterminism.lean` — the positive half

## Tags

star-language · non-validity · determinism · app:deterministic-future
-/

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage
open FormalSystem.StarLanguage

/--
**`app:deterministic-future`, negative half.** `sent:det` is refuted over the non-deterministic
frame `NF` — the same frame and countermodel `app:deterministic`'s negative half
(`refute_determined`) uses.

The refuting instance is a bare atom, which is *not* a weakening: unlike *Determined*, whose
atomic instances are frame-valid everywhere (`stab_atom_of_atom`), `sent:det` has genuine
content at an atom because `↓²` moves evaluation to a *different time*, where the present world
state no longer determines the atom's value. That is precisely the discrimination the time
registers buy, and it is why no uniform-substitution argument is needed — or available — here.
-/
theorem refute_sentDet (p : Atom) :
    ¬ NF.StarValidOn (sentDet (ofPlus (PlusFormula.atom p))) := by
  refine not_starValidOn_sentDet natModel (natHist fun _ => 0) (natHist_isTotal _)
    (0 : ℤ) (1 : ℤ) (one_pos : (0 : ℤ) < 1)
    (natHist fun _ => 0) (natHist fun s => if s ≤ 0 then 0 else 1)
    (natHist_isTotal _) (natHist_isTotal _) (SameStateAt.refl _ _)
    (fun _ _ => by show (0 : ℕ) = (if (0 : ℤ) ≤ 0 then 0 else 1); simp) ?_ ?_
  · -- `τ` itself satisfies `p` at time `1`: `τ(1) = 0` and `|p| = {0}`.
    exact fun _ => ⟨trivial, (rfl : (0 : ℕ) = 0)⟩
  · -- `σ` fails `p` at time `1`: `σ(1) = 1 ∉ |p|`.
    rintro _ ⟨_, hval⟩
    have hval' : (if (1 : ℤ) ≤ 0 then (0 : ℕ) else 1) = 0 := hval
    simp at hval'

/-- The same refutation at the level of unrestricted L⋆ validity: `sent:det` is not valid. -/
theorem not_starValid_sentDet (p : Atom) :
    ¬ StarValid (sentDet (ofPlus (PlusFormula.atom p))) :=
  fun h => refute_sentDet p (h NF trivial)

end FormalSystem.Semantics
