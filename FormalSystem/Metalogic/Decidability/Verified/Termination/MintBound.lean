/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.Invariants
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.OrderingTimes
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.MintPotential
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.Measure
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.Terminus
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.ClosureResidual
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.TimeCensus
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.Register

/-!
# The mint bound — an independent ceiling on fresh-time minting

`Fuel.lean` (T3) turns the formula stock (T1) and the time-type bound (T2) into a fuel figure at
which `expandBranchWithFuel` cannot exhaust, but its totality theorem
`expandBranchWithFuel_isSome_of_noSplit` is scoped to runs that never branch. Lifting that scope
needs a bound on the number of **fresh-time mints** along a run that is independent of branch
growth, because at an ordered split's third arm (`Branch.identifyTime`) the branch shrinks as a
set and the branch-cardinality measure the extending case relies on is not available.

This module supplies that bound in four blocks.

## A. The irreflexivity invariant (`IrreflOrd`)

Witness preservation across the identification arm is **conditional** on the ordering carrying no
self-loop. That is not a convenience hypothesis: `TimeOrdering.identifyTime` drops every
constraint whose two components rename to the same index, including a pre-existing `(a, a)`, and
a witness reachable only around such a self-loop is destroyed. The counterexample
`witnessPresent_identifyTime_unconditional_false` below refutes the unconditional form outright.
`IrreflOrd` is therefore established as an engine-level run invariant before anything is built on
top of it.

## B. Reachability transport and witness preservation

`futureOf`/`pastOf` reachability transports along the identification renaming `rho`, length
preserving, so a witness found at one fuel figure is re-found at the same one. That lifts to
`witnessPresent` for all eight fresh-label rules, with every other rule covered by a *proved*
vacuity rather than an assumed one.

## C. The mint potential

The count of `(rule, signed formula)` pairs still eligible to mint. Witness preservation makes it
non-increasing along a run and a mint makes it strictly decrease, which is what converts "each
pair mints at most once" into a per-state measure an induction can carry.

## D. The amortized counting chain

`#mints`, `#identifications`, total shrinkage, and `#extensions`, each bounded absolutely, feeding
the branch-budget-carrying restatement of the totality theorem and its terminus at
`buildTableauAt`.

## Placement

Everything here is downstream of `Fuel.lean` and purely additive: no declaration in
`Fuel.lean`, `Saturation.lean`, or `Tableau.lean` is edited, and in particular `buildTableau`,
its default fuel, and `expandBranchWithFuel`'s default branch cap are untouched.
-/

namespace FormalSystem.Metalogic.Decidability

open FormalSystem.Syntax

/-! ## D2. `MintPaysForTime`: the verdict

**Verdict: refutable as literally stated.** `mintPaysForTime_untlNeg_false` is the witness, and it
is universally quantified in the frame class and in `Tmax`. This is the third residual on this
terminus to come out refutable rather than merely unproved, after `DifficultyBounded`
(`difficultyBounded_multiplicity_false`) and `UniverseClosed`
(`universeClosed_identify_retime_false`).

**The cause, in one line.** `untlNeg` is in `freshTimeRules` and **not** in `freshLabelRules`
(`freshTimeRules_incomparable_freshLabelRules`), so a step that fires it mints a time while moving
no pair of `mintPotential`'s index set `freshLabelRules ×ˢ U`. Disjunct 1's first conjunct then
fails because a known time was added, and disjunct 2's second conjunct fails because the potential
is unchanged — `mintTimeBudget = knownTimes.card + mintPotential` even *rises*, so disjunct 2's
first conjunct fails too. All three failures are decided at the concrete configuration below.

**Re-indexing the potential on `freshTimeRules` does not repair it**, and that is worth stating
before anyone tries. `mintPotential` filters on `witnessPresent r (σ sf) b ord = false`, and
`witnessPresent`'s match has exactly eight arms — one per `freshLabelRules` member — with
everything else falling to the catch-all `false`. `witnessPresent_eq_false_of_not_freshLabel`
decides that. So widening the index set to `freshTimeRules` adds `densityRule`, `untlNeg` and
`snceNeg` columns that are *permanently* false at every state, contributing a constant to the count
and never decreasing. The wider potential is the narrower one plus `3 * |U|`, and it moves exactly
when the narrower one does. The rule coordinate is not where the repair lives.

**Where the repair does live**, and what Phase 7 builds: disjunct 1's first conjunct is the wrong
inequality. `applyRule_emitted_time_dichotomy` says an unordered successor's times are the branch's
plus at most `Branch.nextTime` — one new time per step, never more. The satisfiable statement is
therefore `nb.knownTimes.card ≤ b.knownTimes.card + 1`, which is a *theorem*
(`knownTimes_card_le_succ_of_unorderedSuccessor`) rather than a hypothesis, leaving the ordering
rank as disjunct 1's only real content.

**The satisfiability boundary.** `mintPaysForTime_empty` holds at `U = ∅`: confinement forces
`b = []`, on which the engine reports `.saturated` and there are no unordered successors at all.
As with `UniverseClosed`, the predicate is satisfiable exactly where the terminus it guards is
vacuous — `signedUniverse C L` is empty only when `C` or `L` is.

`MintPaysForTime` itself is retained **verbatim**. Nothing in this file is withdrawn. -/

/-- **`witnessPresent` is identically `false` outside `freshLabelRules`.** Its match has eight
arms, one per witness-guarded rule, and every other `(rule, sign, formula)` triple reaches the
catch-all.

This is the fact that rules out repairing `MintPaysForTime` by widening `mintPotential`'s index
set from `freshLabelRules` to `freshTimeRules`: the three added columns — `densityRule`, `untlNeg`,
`snceNeg` — would be false at every state of every run, so they contribute `3 * |U|` to the count
and never move. See the register entry. -/
theorem witnessPresent_eq_false_of_not_freshLabel {r : TableauRule}
    (h : ruleMintsFreshLabel r = false) (sf : SignedFormula) (b : Branch) (ord : TimeOrdering) :
    witnessPresent r sf b ord = false := by
  cases sf with
  | mk sign formula label =>
    cases r <;> first
      | exact Bool.noConfusion h
      | (cases sign <;> simp only [witnessPresent])

/-! ### The refuting configuration

`untlNeg`'s ACTIVE arm fires when `timeOrd.futureOf l.time` is empty while `timeOrd.timeCount` is
in `(0, 4)`. The configuration below meets that with the least machinery possible: the trigger
`F(U(e,g))` sits at time `0`, and the ordering's single constraint `1 < 2` involves neither `0` nor
anything reachable from it. Two atoms at times `1` and `2` carry those times on the branch, which
is what `OrdTimesKnown` needs; atoms fire no rule, so nothing pre-empts the trigger.

`untlNeg` is a `carrierBase` rule, so this configuration is available at **every** frame class —
the witness quantifies over `fc` and the four cases are decided separately. It also quantifies over
`Tmax`: disjunct 1 fails at its *first* conjunct, which does not mention `Tmax` at all. -/

def mwE : Formula := .atom (Atom.mkBase "e")
def mwG : Formula := .atom (Atom.mkBase "g")
def mwP : Formula := .atom (Atom.mkBase "p")
def mwQ : Formula := .atom (Atom.mkBase "q")

/-- The trigger: `F(U(e,g))` at the initial label. -/
def mintWitnessTrigger : SignedFormula := SignedFormula.neg (Formula.untl mwG mwE) ⟨0, 0⟩

/-- The witness branch. The two atoms exist to carry times `1` and `2`, which the ordering's one
constraint mentions and `OrdTimesKnown` therefore requires. -/
def mintWitnessBranch : Branch :=
  [mintWitnessTrigger, SignedFormula.pos mwP ⟨0, 1⟩, SignedFormula.pos mwQ ⟨0, 2⟩]

/-- The witness ordering: `1 < 2`, leaving `futureOf 0` empty with `timeCount = 2`. Exactly the
ACTIVE arm's trigger condition. -/
def mintWitnessOrd : TimeOrdering := { constraints := [(1, 2)] }

/-- The witness universe: the branch itself, so confinement is immediate. -/
def mintWitnessUniverse : Finset SignedFormula :=
  {mintWitnessTrigger, SignedFormula.pos mwP ⟨0, 1⟩, SignedFormula.pos mwQ ⟨0, 2⟩}

/-- The first arm of the split: `F(e)` at the freshly minted time `3`, the re-included trigger, and
the original branch. -/
def mintWitnessSucc : Branch :=
  [SignedFormula.neg mwE ⟨0, 3⟩, mintWitnessTrigger, mintWitnessTrigger,
   SignedFormula.pos mwP ⟨0, 1⟩, SignedFormula.pos mwQ ⟨0, 2⟩]

/-- The witness state satisfies the run invariant, so the refutation is not reached by feeding
`MintPaysForTime` a state the run cannot occupy. -/
theorem mintWitness_runInvariant : RunInvariant mintWitnessBranch mintWitnessOrd := by
  constructor
  · unfold IrreflOrd mintWitnessOrd; decide
  · unfold OrdTimesKnown; decide

/-- …and it is confined to the witness universe. -/
theorem mintWitness_confined : ∀ x ∈ mintWitnessBranch, x ∈ mintWitnessUniverse := by decide

/-- **`MintPaysForTime` is false, at every frame class and every `Tmax`.**

At the configuration above the engine fires `untlNeg`'s ACTIVE arm and reports a two-arm `.split`.
On the first arm: `knownTimes` goes from `{0,1,2}` to `{0,1,2,3}`, so disjunct 1's first conjunct
`4 ≤ 3` is false; `mintPotential` is `24` before and `24` after, so disjunct 2's second conjunct
`24 < 24` is false. Both disjuncts fail and the four frame classes are decided separately.

The step is a genuine mint — it issues `Branch.nextTime` — but it is invisible to `mintPotential`
because `untlNeg` is not in `freshLabelRules`, and `witnessPresent_eq_false_of_not_freshLabel`
records that no re-indexing recovers it. -/
theorem mintPaysForTime_untlNeg_false (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    ¬ MintPaysForTime fc mintWitnessUniverse Tmax := by
  intro h
  have key := h id mintWitnessBranch mintWitnessOrd EventualityTracker.empty
    mintWitness_runInvariant mintWitness_confined
  cases fc <;>
    [ (rcases key mintWitnessSucc (by decide) with ⟨h1, -⟩ | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with ⟨h1, -⟩ | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with ⟨h1, -⟩ | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with ⟨h1, -⟩ | ⟨-, h3⟩)] <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h3 (by decide)

/-- **The satisfiability boundary: `U = ∅`.** Confinement forces the branch empty, the engine has
nothing to pick in any of its three stages and reports `.saturated`, and `unorderedSuccessorBranches`
of a `.saturated` result is `[]`. So the whole statement is vacuous there.

The same shape as `universeClosed_identify_empty`: the residual is satisfiable exactly where the
terminus it guards has nothing to say, since `signedUniverse C L` is empty only when `C` or `L` is. -/
theorem mintPaysForTime_empty (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    MintPaysForTime fc ∅ Tmax := by
  intro _ b ord tr _ hconf nb hnb
  have hb : b = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by simpa using hconf x hx
  subst hb
  simp [expandOnceUnblocked, findUnexpandedUnblockedWith, unorderedSuccessorBranches] at hnb

/-! ### The repair, attempted and BLOCKED

The repair this section was to land is **not available**, and this subsection records why with
machine-checked evidence rather than leaving the attempt undocumented. Nothing vacuous is
substituted for it.

*The rule-coordinate repair is out.* Widening `mintPotential`'s index set from `freshLabelRules` to
`freshTimeRules` adds three columns that `witnessPresent_eq_false_of_not_freshLabel` proves are
`false` at every state of every run. The wider potential is the narrower one plus `3 · |U|` and
moves exactly when it does.

*The disjunct-1 repair is out too, and this is the one that had to be tested.* The obvious
remaining narrowing is to drop disjunct 1's first conjunct — `nb.knownTimes.card ≤ b.knownTimes.card`
is exactly what a minting step falsifies, and `knownTimes_card_le_succ_of_unorderedSuccessor` shows
the true bound is one larger — leaving the ordering-rank conjunct as disjunct 1's whole content.
That does not work: `splitOrderedRank Tmax b ord` is
`b.knownTimes.card * (Tmax² + 1) + (incompPairs b ord).card`, the second summand is bounded by
`Tmax²` (`incompPairs_card_le` plus the carried time bound), and the base `Tmax² + 1` is *one more*
than that bound by construction. So one extra known time raises the rank by at least `1` no matter
what the incomparable-pair count does — `splitOrderedRank_lt_of_knownTimes_lt`. The rank conjunct
therefore fails at **every** time-minting step, not just at the refuting one, and
`mintPaysForTime_rank_repair_false` decides the weakened predicate false at the same configuration
that refuted the original.

*What is actually missing.* A fourth measure component that pays for the three self-guarded minting
rules. Each has its own termination argument, and none of them is `mintPotential`:

* `untlNeg` / `snceNeg` fire only when `ord.futureOf l.time` (resp. `pastOf`) is empty **and**
  `ord.timeCount < 4`, and their own `newOrd` makes that first test fail at the next call — the
  `ruleSelfGuarded` mechanism. The natural potential, "branch times with empty forward reach", does
  **not** decrease: the arm removes the trigger's empty future and mints a fresh time whose future
  is empty, for a net change of zero.
* `densityRule` splits each maximal unfilled gap at most once, an argument about the *gap set*,
  which mentions neither `knownTimes` nor `incompPairs` nor any `witnessPresent` count.

Composing those into one measure that also survives the identification arm is open. The
identification arm is the specific obstruction: `ord.timeCount` is the quantity `untlNeg`'s cap is
stated against, and `TimeOrdering.identifyTime` can lower it — the same `maxTime`-lowering
mechanism the time-reuse verdict above turns on.

**Status: this phase is BLOCKED, and so is the concrete-instantiation discharge that depends on
it.** What is delivered instead is the accounting the residual was blocked on
(`applyRule_emitted_time_mem`, `applyRule_emitted_time_dichotomy`,
`unorderedSuccessor_time_dichotomy`, `knownTimes_card_le_succ_of_unorderedSuccessor`), the
satisfiability verdict on the residual as stated, the time-reuse verdict, and the two refutations
below that close off the repair routes a reader would try first. `MintPaysForTime` remains a named,
open hypothesis, retained verbatim; nothing in this file assumes it.

**Since this note was written, the fourth component has been attempted and decided.** The subsection
"The fourth measure component: the self-guard discharge potential" below builds the natural
candidate — a second defect ledger over `selfGuardRules ×ˢ U`, measured against each rule's own
discharge rather than against `ord.timeCount`, and therefore immune to the two routes the register
already refutes — and `mintPaysForTimeAt_reuse_false` decides it **false**, at every frame class and
every `Tmax`. So the paragraph above is now sharper than "open": the identification arm is not only
the obstruction to composing a measure in general, it defeats this composition specifically, through
the σ-hit route of the time-reuse verdict in a weakened *time-hit* form that escapes nothing.
Register entry 17 is the standing record, and the subsection "The density residual" below records
the one coordinate the verdict leaves untouched. `MintPaysForTime` is still a named, open
hypothesis, and is still assumed by nothing.

**And since *that* note was written, the verdict has been scoped and then overturned.** The
reorientation of the ordered split's identification arm (register entry 18) removed the σ-hit
configuration from the engine path, and the subsection "The self-guard component re-gated at the
oriented arm" below re-runs the gate at the renaming the oriented arm actually produces: the
component's potential falls where it previously did not, and the repaired predicate
`MintPaysForTimeStable` — the self-guard disjunct paired with a combined-budget conjunct, under a
σ-time-stability hypothesis the engine discharges — carries the four-component measure
`budgetPotentialAt` through both step lemmas and up to the two seed-level termini. So the paragraph
above is now sharper again, in the other direction: the identification arm is no longer the
obstruction, the σ-hit obligation is discharged rather than carried, and what remains open is the
**density** coordinate alone. `mintPaysForTimeAt_reuse_false` is untouched and stays true; it is a
statement about `MintPaysForTimeAt`, whose σ is tied to nothing. Register entry 19 is the standing
record, and `MintPaysForTime` — as literally stated — is still refuted, still named, and still
assumed by nothing. -/

/-- **One extra known time strictly raises the ordered rank**, whenever the smaller time count is
within the carried bound.

The base `Tmax * Tmax + 1` in `splitOrderedRank` is one more than `incompPairs`' range, and this is
that design fact used in the direction it was built for: a *rise* in the first component cannot be
absorbed by any fall in the second, exactly as a *fall* in the first cannot be absorbed by a rise.
`splitOrderedRank_le` is the range statement it rests on. -/
theorem splitOrderedRank_lt_of_knownTimes_lt {Tmax : Nat} {b nb : Branch}
    {ord ord' : TimeOrdering}
    (hT : b.knownTimes.toFinset.card ≤ Tmax)
    (hlt : b.knownTimes.toFinset.card < nb.knownTimes.toFinset.card) :
    splitOrderedRank Tmax b ord < splitOrderedRank Tmax nb ord' := by
  have hip : (incompPairs b ord).card ≤ Tmax * Tmax :=
    le_trans (incompPairs_card_le b ord) (Nat.mul_le_mul hT hT)
  simp only [splitOrderedRank]
  have h1 : b.knownTimes.toFinset.card + 1 ≤ nb.knownTimes.toFinset.card := hlt
  have h2 : (b.knownTimes.toFinset.card + 1) * (Tmax * Tmax + 1)
      ≤ nb.knownTimes.toFinset.card * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, one_mul] at h2
  omega

/-- **Dropping disjunct 1's cardinality conjunct does not repair `MintPaysForTime`.**

The weakened predicate is spelled out inline rather than given a name, because a repaired predicate
that is itself false must not be landed as a definition for a later reader to pick up. It is
`MintPaysForTime` with disjunct 1's first conjunct removed — the narrowing the satisfiability
verdict pointed at — and it is false at the *same* configuration, at every frame class, for every
`Tmax ≥ 3`.

The `3` is not arbitrary: it is the witness branch's time count, and the hypothesis is exactly what
`splitOrderedRank_lt_of_knownTimes_lt` needs. Any `Tmax` too small to bound the witness's own times
is one the terminus could not have been instantiated at. -/
theorem mintPaysForTime_rank_repair_false (fc : FormalSystem.ProofSystem.FrameClass)
    {Tmax : Nat} (hT : 3 ≤ Tmax) :
    ¬ (∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
         (tr : EventualityTracker), RunInvariant b ord →
         (∀ x ∈ b, x ∈ mintWitnessUniverse) →
         ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
           splitOrderedRank Tmax nb (expandOnceUnblocked b ord fc tr).2
               ≤ splitOrderedRank Tmax b ord
           ∨ (mintTimeBudget mintWitnessUniverse σ nb (expandOnceUnblocked b ord fc tr).2
                 ≤ mintTimeBudget mintWitnessUniverse σ b ord ∧
              mintPotential mintWitnessUniverse σ nb (expandOnceUnblocked b ord fc tr).2
                 < mintPotential mintWitnessUniverse σ b ord)) := by
  intro h
  have hcard : mintWitnessBranch.knownTimes.toFinset.card ≤ Tmax := by
    have h3 : mintWitnessBranch.knownTimes.toFinset.card = 3 := by decide
    omega
  have hgrow : mintWitnessBranch.knownTimes.toFinset.card
      < mintWitnessSucc.knownTimes.toFinset.card := by decide
  have key := h id mintWitnessBranch mintWitnessOrd EventualityTracker.empty
    mintWitness_runInvariant mintWitness_confined
  cases fc <;>
    [ (rcases key mintWitnessSucc (by decide) with h1 | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with h1 | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with h1 | ⟨-, h3⟩);
      (rcases key mintWitnessSucc (by decide) with h1 | ⟨-, h3⟩)] <;>
    first
      | exact absurd h1 (Nat.not_le.mpr (splitOrderedRank_lt_of_knownTimes_lt hcard hgrow))
      | exact absurd h3 (by decide)

/-! ### Verdict on the time-reuse sub-question

**Verdict: reuse is possible.** Decided, at a configuration the engine itself drives.

*The obligation, restated precisely.* `mintPotential_lt_of_mint` asks that the minting pair be
**σ-hit**: the formula the rule fires on must be `σ sf` for some `sf ∈ U`, where `σ` is the
composition of the `rhoSF`s of the ordered splits taken so far. `rhoSF src tgt` never lands on
`src` (`rhoSF_time_ne_src`), so σ's image omits exactly the times earlier identifications merged
away. The obligation is therefore: *a minting formula does not sit at a merged-away time.*

*The affirmative direction fails.* The available facts about identification are
`src_not_mem_knownTimes_identifyTime` (the retired time leaves `knownTimes`) and
`knownTimes_card_lt_identifyTime` (the count strictly drops). Neither says anything about
`Branch.maxTime`, and `Branch.nextTime` is `maxTime + 1`. When the retired time is the branch's
largest, `maxTime` drops with it and the next fresh time lands *back on the retired value*.
`nextTime_reissues_retired_time` decides exactly that: `firstIncomparablePair` selects `(0, 2)` on
a three-time branch, `2` leaves `knownTimes`, and the post-identification `nextTime` is `2` again.

*And the engine drives it.* `reuse_driven_through_engine` decides that two `expandOnceUnblocked`
steps after the identification, the branch carries time `2` once more. So this is not a
configuration reachable only by hand-assembling a `Branch`; it is on a run.

*The consequence for the measure.* `mint_not_in_rhoSF_image` is the σ-hit failure stated directly:
a formula minted at `b.nextTime`, when that value is the retired `src`, is in the image of no
`rhoSF src tgt`. The hypothesis of `mintPotential_lt_of_mint` is therefore not discharged — it is
**false** at this step — and Phase 7's repair must carry it structurally rather than discharge it.

*The live-times reformulation carries the identical obligation, verified rather than asserted.*
That reformulation filters additionally on the formula's time being a fixed point of `σ`. But
`rho_src_ne_src` says `src` is not a fixed point of `rho src tgt`, and the re-issued time **is**
`src`. So the extra filter excludes the re-minted formula for precisely the reason the image
condition does, and defeating one defeats the other. The obstruction is intrinsic to
identification-plus-`maxTime`, not to this measure's shape. -/

/-- The renaming never fixes the time it retires. One line, and the whole σ-hit story rests on it. -/
theorem rho_src_ne_src {src tgt : TimeIndex} (h : tgt ≠ src) : rho src tgt src ≠ src := by
  simp [rho, h]

/-- **`rhoSF src tgt`'s image omits the time `src` entirely.** Everything at `src` is moved to
`tgt`, and everything else keeps a time that was not `src` to begin with. This is why σ's image
omits exactly the merged-away times. -/
theorem rhoSF_time_ne_src {src tgt : TimeIndex} (h : tgt ≠ src) (sf : SignedFormula) :
    (rhoSF src tgt sf).label.time ≠ src := by
  simp only [rhoSF, rho]
  by_cases hc : sf.label.time = src <;> simp [hc, h]

/-- **The σ-hit failure, stated directly.** If the branch's next fresh time *is* the time an
earlier identification retired, then nothing the rule mints there lies in the renaming's image —
so `mintPotential_lt_of_mint`'s hypothesis is false, not merely unproved, at that step. -/
theorem mint_not_in_rhoSF_image {src tgt : TimeIndex} (h : tgt ≠ src) {b : Branch}
    (hnext : b.nextTime = src) {g : SignedFormula} (hg : g.label.time = b.nextTime)
    (sf : SignedFormula) : rhoSF src tgt sf ≠ g := by
  intro heq
  exact rhoSF_time_ne_src h sf (by rw [heq, hg, hnext])

/-- **The retired time comes back.** `firstIncomparablePair` selects `(0, 2)` here, so the
identification arm merges the branch's *largest* time away; `Branch.maxTime` drops from `2` to `1`
and `Branch.nextTime` becomes `2` — the value just retired.

All six conjuncts are decided. The first three establish that this is a genuine ordered-split
trigger meeting both standing hypotheses, so the coincidence in the last three is attributable to
the arm rather than to a violated precondition — the same discipline
`ordTimes_identifyTime_arm3_false` uses. -/
theorem nextTime_reissues_retired_time :
    letI p : Formula := .atom ⟨"p", none⟩
    letI q : Formula := .atom ⟨"q", none⟩
    letI r : Formula := .atom ⟨"r", none⟩
    letI b : Branch := [⟨.pos, p, ⟨0, 0⟩⟩, ⟨.pos, q, ⟨0, 1⟩⟩, ⟨.pos, r, ⟨0, 2⟩⟩]
    letI ord : TimeOrdering := ⟨[(0, 1)]⟩
    IrreflOrd ord ∧ OrdTimesKnown b ord ∧
      firstIncomparablePair b ord = some (0, 2) ∧
      2 ∈ b.knownTimes ∧
      2 ∉ (b.identifyTime 2 0).knownTimes ∧
      (b.identifyTime 2 0).nextTime = 2 := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide⟩
  · unfold IrreflOrd; decide
  · unfold OrdTimesKnown; decide

/-- One engine step along the first reported unordered successor. A witness helper, not part of
the development's interface — it exists so the continuation below is a closed term `decide` can
evaluate. -/
def reuseStep (s : Branch × TimeOrdering) : Option (Branch × TimeOrdering) :=
  let r := expandOnceUnblocked s.1 s.2 FormalSystem.ProofSystem.FrameClass.Base
    EventualityTracker.empty
  match unorderedSuccessorBranches r.1 with
  | [] => none
  | nb :: _ => some (nb, r.2)

/-- The branch of `nextTime_reissues_retired_time`. -/
def reuseWitnessBranch : Branch :=
  [⟨.pos, .atom ⟨"p", none⟩, ⟨0, 0⟩⟩, ⟨.pos, .atom ⟨"q", none⟩, ⟨0, 1⟩⟩,
   ⟨.pos, .atom ⟨"r", none⟩, ⟨0, 2⟩⟩]

/-- The ordering of `nextTime_reissues_retired_time`. -/
def reuseWitnessOrd : TimeOrdering := ⟨[(0, 1)]⟩

/-- The state of `nextTime_reissues_retired_time`, after the identification arm. -/
def reuseWitnessState : Branch × TimeOrdering :=
  (Branch.identifyTime reuseWitnessBranch 2 0, TimeOrdering.identifyTime reuseWitnessOrd 2 0)

/-- **The engine really does re-issue it.** Two `expandOnceUnblocked` steps after the
identification, time `2` is back on the branch. Decided.

This is what turns the coincidence above into a statement about *runs* rather than about
hand-assembled branches, and it is why the verdict is "reuse possible" rather than "open".

**This statement is UNCHANGED by the arm's reorientation, and that is not an oversight.** The plan
that reoriented arm 3 anticipated this `decide` flipping value and required an honest restatement
if it did. It did not flip, for a reason worth stating precisely rather than absorbing: `reuseStep`
is driven from `reuseWitnessState`, which is *hand-assembled* by a direct
`Branch.identifyTime reuseWitnessBranch 2 0` call and not by the engine's arm. What this theorem
decides is therefore conditional — *if* a run ever reaches a branch whose `maxTime` has fallen
below an index it once carried, the engine re-mints that index — and that conditional is as true
now as it was before. What the repair changes is whether the engine can *reach* such a branch:
`oriented_engine_does_not_produce_reuse` below decides that it no longer produces this one, and
`maxTime_monotone_along_run` proves it produces no other. Keeping this theorem at its original
value and adding the reachability statement beside it is the accurate record; re-tuning the witness
until the number moved would have destroyed exactly the conditional worth keeping. -/
theorem reuse_driven_through_engine :
    ((reuseStep reuseWitnessState).bind reuseStep).map
      (fun s => s.1.knownTimes.contains 2) = some true := by decide

/-- **…and the engine no longer produces the state it is conditional on.** The measurement
`reuse_driven_through_engine` cannot make, decided at the same witness.

`reuseWitnessState` is what arm 3 *used to* hand back here. Conjuncts 4 and 5 record that state's
numbers — `maxTime` fallen to `1`, `nextTime` back down to `2`, the retired index — and conjuncts 2
and 3 record what the arm now hands back instead: `maxTime` still `2`, `nextTime` `3`. Conjunct 1
pins the trigger, so the comparison is at the pair the engine itself selects rather than at a pair
chosen to make it come out right; the arm's `min 0 2` / `max 0 2` are written unevaluated for the
same reason, so the statement is read at the arm's own form. Conjunct 6 drives one further engine
step and finds `nextTime` still at `3`: nothing along the continuation recovers the retired value.

Together with `reuse_driven_through_engine` this is the whole of the repair at this witness: the
implication is untouched, and its antecedent is now unreachable. -/
theorem oriented_engine_does_not_produce_reuse :
    firstIncomparablePair reuseWitnessBranch reuseWitnessOrd = some (0, 2) ∧
      (Branch.identifyTime reuseWitnessBranch (min 0 2) (max 0 2)).maxTime = 2 ∧
      (Branch.identifyTime reuseWitnessBranch (min 0 2) (max 0 2)).nextTime = 3 ∧
      reuseWitnessState.1.maxTime = 1 ∧
      reuseWitnessState.1.nextTime = 2 ∧
      (reuseStep (Branch.identifyTime reuseWitnessBranch (min 0 2) (max 0 2),
          TimeOrdering.identifyTime reuseWitnessOrd (min 0 2) (max 0 2))).map
        (fun s => s.1.nextTime) = some 3 := by decide

/-! ### The fourth measure component: the self-guard discharge potential

The component the blocked-repair note above says is missing: a potential paying for the
**self-guarded** minting rules, measured against each rule's own discharge rather than against its
cap. `untlNeg` and `snceNeg` fire only when the trigger's forward (resp. backward) reach is empty,
and each arm's own `newOrd` makes that test fail at the next call. That is a defect ledger with its
own defect notion — deliberately *not* a widening of `mintPotential`'s, which is what closes it off
from the two routes the register already refutes. It is stated against `ord.futureOf` / `ord.pastOf`
emptiness and never against `ord.timeCount`, the quantity `TimeOrdering.identifyTime` lowers.

The subsection opens with a refute-first gate on the one exposure the design inherits and cannot
argue away in advance: the σ-hit obligation. -/

/-- **The two self-guarded time-minting rules**, as a `Finset`, so the potential's index set is a
product in the shape `mintPotential` already uses.

This is deliberately **not** `freshTimeRules` and **not** a widening of `freshLabelRules`. Widening
`mintPotential`'s index set to `freshTimeRules` is the route the do-not-re-attempt register closes
with `witnessPresent_eq_false_of_not_freshLabel`: the added columns are permanently `false`, so the
wider potential is the narrower one plus a constant. This index set carries a **different** cured/
uncured predicate (`selfGuardDischarged`, below), so it is a second ledger rather than a wider
first one.

`densityRule` is excluded on purpose. Its termination argument is about the *gap set*, is quadratic
in `|U|`, and is gated on `denseRules`; it is the right second component and is a named residual,
not a member of this list. -/
def selfGuardRules : Finset TableauRule :=
  {TableauRule.untlNeg, TableauRule.snceNeg}

/-- There are exactly two, decided rather than counted by hand. -/
theorem selfGuardRules_card : selfGuardRules.card = 2 := by decide

/-- **The self-guard's own discharge test**, transcribed from each rule's own firing guard in
inverted polarity.

`untlNeg`'s ACTIVE arm fires only when `timeOrd.futureOf l.time` is empty, and `snceNeg`'s only when
`timeOrd.pastOf l.time` is. So "the defect is already cured at this column" is exactly
*non*-emptiness of that reach — the rule cannot fire there again.

**The catch-all is `true`, the mirror image of `witnessPresent`'s polarity, and this is the design
decision that separates this component from the refuted re-indexing route.** A rule outside the
index set reports `true` here, so its column is permanently *cured* and contributes `0` to the
count; under `witnessPresent`'s polarity the out-of-range arms report `false` and contribute a
permanent positive constant, which is precisely why
`witnessPresent_eq_false_of_not_freshLabel` kills that route. The catch-all is unreachable from
`selfGuardPotential` anyway, since the index set's left factor is exactly the two named rules
(`mem_selfGuardRules`); the polarity choice is what makes any future widening harmless rather than
inert.

`ord.timeCount` is deliberately absent. It is the second conjunct of both arms' guards, and it is
the quantity `TimeOrdering.identifyTime` can lower; measuring the discharge rather than the cap is
what this component is for. -/
def selfGuardDischarged (r : TableauRule) (sf : SignedFormula) (ord : TimeOrdering) : Bool :=
  match r with
  | .untlNeg => !(ord.futureOf sf.label.time).isEmpty
  | .snceNeg => !(ord.pastOf sf.label.time).isEmpty
  | _ => true

/-- **The self-guard potential**: the number of `(rule, formula)` pairs drawn from the fixed index
set `selfGuardRules ×ˢ U` whose self-guard is **not** yet discharged, with the formula carried
through the accumulated renaming `σ`.

It deliberately does **not** take a `Branch`. The self-guard is a property of the ordering alone,
so the branch-growth half of `mintPotential`'s monotonicity has no analogue here and no branch-side
hypothesis is needed at any call site.

`σ` is the composition of the `rhoSF`s of the ordered splits taken so far, exactly as in
`mintPotential`; carrying it keeps the index set fixed across the whole run. -/
def selfGuardPotential (U : Finset SignedFormula) (σ : SignedFormula → SignedFormula)
    (ord : TimeOrdering) : Nat :=
  ((selfGuardRules ×ˢ U).filter (fun p => selfGuardDischarged p.1 (σ p.2) ord = false)).card

/-- **The repaired time-minting residual**: `MintPaysForTime`'s body verbatim, with a **third**
disjunct added and nothing removed.

Nothing is dropped, so the implication runs `MintPaysForTime → MintPaysForTimeAt` and never the
other way; the converse is refuted by `mintPaysForTime_untlNeg_false` at a `U` where the weaker
form was intended to hold. This is the `universeClosedAt_of_universeClosed` idiom.

The third disjunct is the self-guard coordinate: a self-guarded minting step is paid for by
discharging its own guard, which is invisible to both existing disjuncts — the mint raises
`knownTimes` (killing disjunct 1's first conjunct) and `untlNeg` / `snceNeg` are not in
`freshLabelRules` (so `mintPotential` does not move at all).

**Verdict on this predicate at the σ-hit hazard: see `mintPaysForTimeAt_reuse_false` below. It is
false there, for the same reason `MintPaysForTime`'s second disjunct is.** The definition is landed
anyway, and named, because the refutation has to be *stated about something*; it is not offered as
a working repair.

**Obligation map — the density coordinate is a second, independent gap.** Even setting the σ-hit
verdict aside, this predicate carrying only the `selfGuardPotential` disjunct is separately
refutable at `.Dense` / `.RTime` by a `densityRule` vehicle: `densityRule` returns `.persistent`
(`Tableau.lean:1385`), which `expandOnceUnblocked` maps to `.extended`, so
it is inside this predicate's scope, and it mints a fresh time while lying outside **both**
`freshLabelRules` and `selfGuardRules` — no disjunct moves at all. The intended component is
`gapPotential`, indexed by `U ×ˢ U` and gated on `denseRules`; it is a **named residual**,
implemented nowhere and assumed by nothing. See the subsection "The density residual" following
`mintPaysForTimeAt_reuse_false`, and register entry 17. -/
def MintPaysForTimeAt (fc : FormalSystem.ProofSystem.FrameClass) (U : Finset SignedFormula)
    (Tmax : Nat) : Prop :=
  ∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
    (tr : EventualityTracker), RunInvariant b ord → (∀ x ∈ b, x ∈ U) →
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      (nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb (expandOnceUnblocked b ord fc tr).2
          ≤ splitOrderedRank Tmax b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord ∧
          mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
            < mintPotential U σ b ord)
      ∨ selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
          < selfGuardPotential U σ ord

/-! #### The gate: the σ-hit obligation, inherited in weakened form and still false

The time-reuse verdict decides that σ's image omits the times earlier identifications merged away,
and that the engine re-issues exactly those times. `mintPotential_lt_of_mint` needs the minting
formula to be **σ-hit** — literally `σ sf` for some `sf ∈ U` — and `mint_not_in_rhoSF_image`
refutes that at the re-issue configuration.

`selfGuardPotential` inherits the obligation in a *weaker* form. Its columns are indexed by the
σ-image's **time**, not by the σ-image formula, so it needs only a *time* hit: some `sf ∈ U` with
`(σ sf).label.time` equal to the trigger's time. The question this gate decides is whether that
weakening escapes the refutation.

**It does not, and the reason is one line.** `rhoSF_time_ne_src` is already a statement about
*times*: `(rhoSF src tgt sf).label.time ≠ src`, for every `sf` whatsoever. The formula-hit
refutation was derived from it (`mint_not_in_rhoSF_image` is three lines on top of it), so the
time-hit weakening cannot escape what the formula-hit failure was a corollary of. -/

/-- **No column of `selfGuardPotential`'s index set is indexed at a retired time.**

The general half of the gate, and the reason the concrete configuration below is not a lucky
choice. The ACTIVE arm of `untlNeg` cures its trigger's column by adding `(l.time, freshTime)` to
the ordering, so the only column that arm can flip is the one at `l.time`. When `l.time` is a time
an earlier identification retired — which the time-reuse verdict decides the engine re-issues —
`rhoSF_time_ne_src` says no column lives there at all. Nothing flips, so nothing drops.

This is `mint_not_in_rhoSF_image`'s obligation stated one level weaker and still unmet: weakening
a formula hit to a time hit gains nothing, because the refutation was a time-level fact to begin
with. -/
theorem selfGuard_no_column_at_retired_time {src tgt : TimeIndex} (h : tgt ≠ src)
    (U : Finset SignedFormula) :
    ∀ p ∈ selfGuardRules ×ˢ U, ((rhoSF src tgt) p.2).label.time ≠ src :=
  fun p _ => rhoSF_time_ne_src h p.2

/-- The gate's trigger: `F(U(e,g))` at the **re-issued** time `2`. Same formula shape as
`mintWitnessTrigger`; the label's time is what differs, and it is the whole point. -/
def gateTrigger : SignedFormula := SignedFormula.neg (Formula.untl mwG mwE) ⟨0, 2⟩

/-- The gate branch. The trigger sits at the re-issued time `2`; the two atoms carry times `0` and
`1`, which the ordering's one constraint mentions and `OrdTimesKnown` therefore requires. Atoms fire
no rule, so nothing pre-empts the trigger. -/
def gateBranch : Branch :=
  [gateTrigger, SignedFormula.pos mwP ⟨0, 0⟩, SignedFormula.pos mwQ ⟨0, 1⟩]

/-- The gate ordering. It is `TimeOrdering.identifyTime reuseWitnessOrd 2 0` on the nose — the
ordering the identification arm of `nextTime_reissues_retired_time` leaves behind (the retired time
`2` appears in no constraint, so the substitution is a no-op there). `futureOf 2` is empty and
`timeCount` is `2`, which is exactly `untlNeg`'s ACTIVE guard. -/
def gateOrd : TimeOrdering := ⟨[(0, 1)]⟩

/-- The gate universe: the branch itself, so confinement is immediate. -/
def gateUniverse : Finset SignedFormula :=
  {gateTrigger, SignedFormula.pos mwP ⟨0, 0⟩, SignedFormula.pos mwQ ⟨0, 1⟩}

/-- The first arm of the split the ACTIVE `untlNeg` reports: `F(e)` at the freshly minted time `3`,
the re-included trigger, and the original branch. -/
def gateSucc : Branch :=
  [SignedFormula.neg mwE ⟨0, 3⟩, gateTrigger, gateTrigger,
   SignedFormula.pos mwP ⟨0, 0⟩, SignedFormula.pos mwQ ⟨0, 1⟩]

/-- The ordering after the ACTIVE arm: `addFuture 2 3` prepended. This is the edge that is supposed
to cure the trigger's column. -/
def gateNewOrd : TimeOrdering := ⟨[(2, 3), (0, 1)]⟩

/-- **The run-realizable renaming.** `rhoSF 2 0` is the σ the identification `2 → 0` itself
produces, not a σ chosen to make the refutation work. Refuting a σ-mediated potential with a σ
unconstrained by the run is worthless — a hostile σ defeats every such potential and teaches
nothing — so the gate uses the *most favorable available* σ, the discipline
`mintPaysForTime_untlNeg_false` sets by using `id`. -/
def gateSigma : SignedFormula → SignedFormula := rhoSF 2 0

/-- The gate state satisfies the run invariant. -/
theorem gate_runInvariant : RunInvariant gateBranch gateOrd := by
  constructor
  · unfold IrreflOrd gateOrd; decide
  · unfold OrdTimesKnown; decide

/-- …and it is confined to the gate universe. -/
theorem gate_confined : ∀ x ∈ gateBranch, x ∈ gateUniverse := by decide

/-- **The gate configuration really is the re-issue hazard.** Seven conjuncts, all decided, in the
discipline `nextTime_reissues_retired_time` uses: without them a negative verdict below would be
attributable to a violated precondition rather than to the arm.

1-2. the standing hypotheses hold at the gate state;
3. `firstIncomparablePair` selects `(0, 2)` on the predecessor state, so the identification that
   produces `gateSigma = rhoSF 2 0` is the one the engine itself takes;
4. time `2` really is retired by it;
5. …and really is re-issued: the post-identification `nextTime` is `2` again;
6. the gate ordering is exactly what that identification leaves behind;
7. the trigger sits at the re-issued time and `untlNeg`'s ACTIVE guard is met there — empty forward
   reach, with `timeCount` inside the `(0, 4)` window. -/
theorem gate_is_reissue_hazard :
    IrreflOrd gateOrd ∧ OrdTimesKnown gateBranch gateOrd ∧
      firstIncomparablePair reuseWitnessBranch reuseWitnessOrd = some (0, 2) ∧
      2 ∉ (Branch.identifyTime reuseWitnessBranch 2 0).knownTimes ∧
      (Branch.identifyTime reuseWitnessBranch 2 0).nextTime = 2 ∧
      gateOrd.constraints = (TimeOrdering.identifyTime reuseWitnessOrd 2 0).constraints ∧
      (gateTrigger.label.time = 2 ∧ (gateOrd.futureOf 2).isEmpty = true ∧
        0 < gateOrd.timeCount ∧ gateOrd.timeCount < 4) := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩
  · unfold IrreflOrd gateOrd; decide
  · unfold OrdTimesKnown; decide

/-- **The engine fires the ACTIVE arm here**, at every frame class: the reported ordering is
`gateNewOrd` and `gateSucc` is one of the two unordered successors. `untlNeg` is a `carrierBase`
rule, so this is not a frame-class accident.

**Unchanged by the arm's reorientation**, for the reason `oriented_gate_invariants` conjunct 7
already decides: the gate's trigger is `some (2, 0)`, so `min 2 0 = 0` and `max 2 0 = 2`, and the
oriented arm and the unoriented one are *literally the same list* at this configuration. Nothing at
the gate is evidence for the mechanism, and nothing at the gate regresses under it — which is why
the reuse witness, where the two orientations genuinely differ, is the configuration that carries
the verdict. -/
theorem gate_step_fires (fc : FormalSystem.ProofSystem.FrameClass) :
    (expandOnceUnblocked gateBranch gateOrd fc EventualityTracker.empty).2.constraints
        = gateNewOrd.constraints ∧
      gateSucc ∈ unorderedSuccessorBranches
        (expandOnceUnblocked gateBranch gateOrd fc EventualityTracker.empty).1 := by
  cases fc <;> exact ⟨by decide, by decide⟩

/-- **The component is not inert: with `σ = id` the self-guard potential does drop**, `4` to `3`, at
exactly this step. The trigger's own column at time `2` flips uncured → cured, which is the whole
mechanism `selfGuardPotential` was designed around.

This is the discriminating measurement. It is what makes the refutation below a statement about the
**σ-hit obligation** rather than about the component failing to move at all — the distinction that
separates a located obstruction from an unexamined one. -/
theorem selfGuardPotential_lt_at_gate_with_id :
    selfGuardPotential gateUniverse id gateNewOrd
      < selfGuardPotential gateUniverse id gateOrd := by decide

/-- **…and with the run-realizable `σ` it does not.** `4 → 3` becomes `3 → 3`. The column that
flipped under `id` was the trigger's own, indexed at time `2`; under `gateSigma = rhoSF 2 0` no
column is indexed there at all (`selfGuard_no_column_at_retired_time`), so the curing edge
`(2, 3)` that the ACTIVE arm adds lands outside the index set. -/
theorem selfGuardPotential_eq_at_gate_with_sigma :
    selfGuardPotential gateUniverse gateSigma gateNewOrd
      = selfGuardPotential gateUniverse gateSigma gateOrd := by decide

/-- **VERDICT: `MintPaysForTimeAt` is FALSE.** At every frame class and every `Tmax`, at the
configuration the time-reuse verdict identifies as the σ-hit hazard, with the most favorable
run-realizable renaming.

*The verdict in words.* The self-guard discharge potential does **not** repair the time-minting
residual. The σ-hit obligation that the time-reuse verdict decides false for `mintPotential` is
inherited by `selfGuardPotential` in a weakened *time-hit* form, and **the weakening does not
escape it.** `mint_not_in_rhoSF_image` is a corollary of `rhoSF_time_ne_src`, which is already a
statement about times, so relaxing "the minting formula is `σ sf`" to "the minting formula's *time*
is `(σ sf)`'s time" relaxes nothing that the refutation depended on.

*How all three disjuncts fail here.* The step mints time `3`, so `knownTimes` goes from `3` to `4`
and disjunct 1's first conjunct `4 ≤ 3` is false. `mintTimeBudget` goes from `27` to `28` and
`mintPotential` is `24` both before and after — `untlNeg` is not in `freshLabelRules` — so both of
disjunct 2's conjuncts are false. And `selfGuardPotential` is `3` both before and after, so
disjunct 3's `3 < 3` is false.

*Why this is a real refutation and not a measurement artifact.* Three things are established
separately rather than assumed. `gate_is_reissue_hazard` decides all seven preconditions, so the
failure is attributable to the arm and not to a violated hypothesis.
`selfGuardPotential_lt_at_gate_with_id` decides that the component **does** drop at this very step
under `σ = id`, so the component is not inert and the failure is located precisely at σ.
And `selfGuard_no_column_at_retired_time` gives the general reason — no configuration escapes it,
because the obstruction is the renaming's image omitting the retired time, which holds for every
`U`, every trigger and every retired time.

*Consequence.* The self-guard coordinate is not the missing fourth measure component, and the
obstruction is not this component's shape: it is intrinsic to identification-plus-`maxTime`, the
same conclusion the live-times reformulation reaches. See register entry 17. -/
theorem mintPaysForTimeAt_reuse_false (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    ¬ MintPaysForTimeAt fc gateUniverse Tmax := by
  intro h
  have key := h gateSigma gateBranch gateOrd EventualityTracker.empty
    gate_runInvariant gate_confined
  cases fc <;>
    [ (rcases key gateSucc (by decide) with ⟨h1, -⟩ | ⟨h2, -⟩ | h3);
      (rcases key gateSucc (by decide) with ⟨h1, -⟩ | ⟨h2, -⟩ | h3);
      (rcases key gateSucc (by decide) with ⟨h1, -⟩ | ⟨h2, -⟩ | h3);
      (rcases key gateSucc (by decide) with ⟨h1, -⟩ | ⟨h2, -⟩ | h3)] <;>
    first
      | exact absurd h1 (by decide)
      | exact absurd h2 (by decide)
      | exact absurd h3 (by decide)

/-! #### The density residual: `gapPotential`, unattempted rather than refuted

Recorded immediately after the verdict because the verdict closes the **self-guard** coordinate and
would otherwise leave a reader believing the whole fourth-component question closed with it. It is
not. This subsection states precisely which coordinate remains, why it is a separate clause rather
than another disjunct fitted to the same ledger, and that nothing here is implemented or assumed.

*The exposure the verdict does not cover.* `MintPaysForTimeAt` carrying only the
`selfGuardPotential` disjunct is separately refutable at `.Dense` / `.RTime` by a `densityRule`
vehicle, on grounds that have nothing to do with the σ-hit hazard. `densityRule` is inside the
predicate's scope — it returns `.persistent` (`Tableau.lean:1385`), which `expandOnceUnblocked` maps
to `.extended` — and it mints a fresh time while sitting outside **both**
`freshLabelRules` and `selfGuardRules`. So a `densityRule` step moves no disjunct of the predicate
at all, at any `U`, independently of everything above. `freshTimeRules_incomparable_freshLabelRules`
is the census fact that puts it outside the first list; `selfGuardRules` excludes it by construction.

*The intended component, named so that its absence is legible.* `gapPotential`, indexed by `U ×ˢ U`
rather than by `selfGuardRules ×ˢ U`. The index shape is forced by the rule's own argument:
`densityRule` splits each *maximal unfilled gap* at most once, and a gap is a **pair**, so the
ledger transcribes the rule's own `gapTargets` filter (`Tableau.lean:1364-1366`) —
`(timeOrd.futureOf t').isEmpty`, together with `t'` lying below no other future time of the trigger
— rather than any per-rule discharge test. It is therefore quadratic in `|U|` where
`selfGuardPotential` is linear, and it is gated on `denseRules` (`Tableau.lean:1593`), so it
contributes nothing at `.Base` / `.ZTime`.

*That it has to be a separate clause is not this development's invention.* In the mosaic
decidability argument whose residual structure this file follows, density is `(SVDns)`, listed among
the *additional vertical saturation conditions* and kept apart from the eventuality conditions the
other clauses discharge (Caleiro–Viganò–Volpe 2013, §3.1). The separation is the source's. The
pair-indexing conclusion is independently forced by `densityRule`'s own docstring in any case, so
nothing here rests on the citation alone.

**Nothing of `gapPotential` is implemented in this file, and no theorem in this file assumes it.**
It is named so that a reader arriving at the verdict above can tell which coordinate is *refuted*
and which is merely *untried*; see register entry 17. Refuting the self-guard coordinate says
nothing about this one in either direction. -/

/-! ### Monotone time issuance: the identification-side gate

**VERDICT: TRUE.** The mechanism prevents the reuse, at the witness and along the engine-driven
run, and all three settled invariants survive it. Phases 2-9 of the repair are unlocked by this
subsection; nothing below it is assumed anywhere above.

*What the gate is deciding.* Entry 15 records that the ordered split's identification arm can
retire the branch's **largest** time, dropping `Branch.maxTime` and making `Branch.nextTime`
re-issue the value just retired. The arm calls `branch.identifyTime t₂ t₁`, retiring `t₂` whatever
its magnitude, and `firstIncomparablePair_spec` guarantees only `t₂ ≠ t₁` — never `t₁ < t₂`. The
mechanism prototyped here **orients the merge by numeric order** instead: retire `min t₁ t₂`, keep
`max t₁ t₂`. Which numeral survives is semantically arbitrary — identification asserts the two
instants are the *same*, and nothing in the semantics reads the numeral's magnitude — so the
orientation is free, and it is exactly what makes `maxTime` non-decreasing at the arm.

*Why this is a gate and not the repair.* Everything here is **additive** and calls the existing,
byte-unchanged `Branch.identifyTime` / `TimeOrdering.identifyTime`. No engine file is touched by
this subsection. That constraint is not stylistic: `Verified/Decidable.lean` carries 102
`Branch.nextTime` references — `lt_nextTime_of_mem_knownTimes`, `OrdWithin.bound` and
`OrdWithin.nextTime_not_mem` among them — which consume `nextTime = maxTime + 1` *definitionally*.
Redefining the bookkeeping would break all of them; reorienting the call site breaks none.

*The measured contrast, which is what makes the verdict attributable to the mechanism.* Along the
same two engine steps from the same witness:

| | `maxTime` trajectory | retired index | re-issued? |
|---|---|---|---|
| current arm (`identifyTime t₂ t₁`) | `2 → 1 → 1 → 2` | `2` | **yes** (`reuse_driven_through_engine`) |
| oriented arm (`identifyTime (min) (max)`) | `2 → 2 → 2 → 3` | `0` | **no** |

`oriented_arm_is_not_inert` decides both rows side by side. Without that pairing the gate could not
distinguish "the mechanism prevents the reuse" from "the configuration stopped applying" — the same
discriminating discipline `selfGuardPotential_lt_at_gate_with_id` sets for the refuted
fourth-component route.

*Ladder rung used.* Candidate A (merge orientation) only. The two fallback rungs — a `horizon`
field on `TimeOrdering`, and a run-level mint counter threaded through `applyRule` — were not
prototyped, because the first rung decided the gate. Their measured costs (29 files and 82 literal
sites; two engine signatures plus `Saturation.lean`) are recorded here so a reader who needs them
does not have to re-measure. -/

/-- **The orientation, as a pure function on the trigger's pair.** `(retired, surviving)`: the
numeral that disappears is the smaller, the numeral that survives is the larger.

That single choice is the whole mechanism. `Branch.identifyTime src tgt` relabels everything at
`src` to sit at `tgt` and leaves every other time alone, so the post-arm branch's times are the
pre-arm branch's times minus `src`. If `src` is the smaller of a pair both of whose members are
known times, it cannot have been the branch's maximum — the larger member is a known time too, and
they are distinct — so nothing the branch loses can lower `Branch.maxTime`, and `Branch.nextTime`,
being `maxTime + 1` by definition, cannot fall either. -/
def identifyOrient (t₁ t₂ : TimeIndex) : TimeIndex × TimeIndex := (min t₁ t₂, max t₁ t₂)

/-- **The prototype arm-3 successor.** The ordered split's identification arm as it would read
under the orientation, assembled here without touching `Tableau.lean`.

It calls the **existing, unmodified** `Branch.identifyTime` and `TimeOrdering.identifyTime` — no
new field, no new signature, no threaded counter. Demonstrating that the mechanism needs nothing
but a swap of two arguments at one call site is the point of stating it this way, and it is the
constraint the whole repair rests on. -/
def identifyOriented (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    Branch × TimeOrdering :=
  (b.identifyTime (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2,
   ord.identifyTime (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2)

/-- **Question (a) at the witness: the oriented arm does not re-issue.** Decided at
`reuseWitnessBranch` / `reuseWitnessOrd` with the pair `(0, 2)` that `firstIncomparablePair`
actually selects there (`gate_is_reissue_hazard` conjunct 3), so the measurement is at the
configuration entry 15 is about and not at a configuration chosen to make it come out right.

Three conjuncts. Time `2` is a known time; the post-arm `nextTime` is strictly above it, so `2`
cannot be minted next; and `Branch.maxTime` did not fall across the arm — which is the property
that generalises, and the one Phase 2 lifts off this configuration. -/
theorem oriented_arm_does_not_reissue :
    2 ∈ reuseWitnessBranch.knownTimes ∧
      (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.nextTime > 2 ∧
      reuseWitnessBranch.maxTime
        ≤ (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.maxTime := by
  decide

/-- The state `reuseWitnessState` would have been under the oriented arm. The counterpart of
`reuseWitnessState`, and the seed of the engine-driven measurement below. -/
def orientedReuseWitnessState : Branch × TimeOrdering :=
  identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2

/-- **Question (a) driven through the engine: the retired index does not come back.** The direct
counterpart of `reuse_driven_through_engine`, and the conjunct that makes the verdict a statement
about *runs* rather than about a hand-assembled `Branch`.

Under the orientation the index the arm retires is `0`, not `2`. Two `expandOnceUnblocked` steps
later it is still absent from `knownTimes`, and `Branch.maxTime` has gone `2 → 2 → 3` rather than
`2 → 1 → 2`. Reuse is not merely unobserved here: `Branch.nextTime` is `maxTime + 1` and `maxTime`
never fell, so every mint along this run is at a value strictly above every index the run has ever
retired.

A gate that checked only `oriented_arm_does_not_reissue` would be checking the arm in isolation.
This is the conjunct that checks the mechanism where entry 15 does its damage. -/
theorem oriented_reuse_not_driven_through_engine :
    ((reuseStep orientedReuseWitnessState).bind reuseStep).map
        (fun s => s.1.knownTimes.contains 0) = some false ∧
      (reuseStep orientedReuseWitnessState).map (fun s => s.1.maxTime) = some 2 ∧
      ((reuseStep orientedReuseWitnessState).bind reuseStep).map
        (fun s => s.1.maxTime) = some 3 := by
  decide

/-- **The discriminating measurement.** At the *same* witness, the *current* orientation re-issues
and the oriented one does not — decided side by side, in one statement, so the verdict cannot be an
artifact of the configuration having stopped applying.

Conjuncts 1 and 3 restate what `nextTime_reissues_retired_time` and `reuse_driven_through_engine`
already decide, at the same numbers; conjuncts 2 and 4 are their oriented counterparts. Conjuncts 5
and 6 exhibit the `maxTime` drop that causes the re-issue and its absence under the orientation, so
the mechanism is visible and not merely its consequence.

This is the pairing `selfGuardPotential_lt_at_gate_with_id` sets the precedent for: a gate that
reports only the favourable half of a comparison has measured nothing. -/
theorem oriented_arm_is_not_inert :
    (Branch.identifyTime reuseWitnessBranch 2 0).nextTime = 2 ∧
      (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.nextTime = 3 ∧
      ((reuseStep reuseWitnessState).bind reuseStep).map
        (fun s => s.1.knownTimes.contains 2) = some true ∧
      ((reuseStep orientedReuseWitnessState).bind reuseStep).map
        (fun s => s.1.knownTimes.contains 0) = some false ∧
      (Branch.identifyTime reuseWitnessBranch 2 0).maxTime < reuseWitnessBranch.maxTime ∧
      reuseWitnessBranch.maxTime
        ≤ (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.maxTime := by
  decide

/-- The reuse witness's universe, **closed under retiming within its own known times**: its three
atoms against world `0` and times `0`-`2`.

Stated in the `signedUniverse` shape rather than as the three-formula literal, because the bare
literal is not retiming-closed and confinement across *any* identification arm would fail against
it — under the current orientation exactly as much as under this one. That is register entry 10's
finding, not a cost of the mechanism, and `UniverseClosedAt` is the settled repair for it. -/
def orientedReuseUniverse : Finset SignedFormula :=
  signedUniverse
    ({.atom ⟨"p", none⟩, .atom ⟨"q", none⟩, .atom ⟨"r", none⟩} : Finset Formula)
    ((({0} : Finset WorldIndex) ×ˢ ({0, 1, 2} : Finset TimeIndex)).image
      (fun p => (⟨p.1, p.2⟩ : Label)))

/-- **Question (b): the settled invariants survive the oriented arm.** Seven conjuncts, decided at
**both** landed witness configurations, in the discipline `gate_is_reissue_hazard` uses — without
the trigger conjuncts a negative verdict would be attributable to a violated precondition rather
than to the mechanism.

1-2. the pair each configuration's trigger actually reports, so the oriented arm below is applied
   at the pair the engine itself would hand it;
3. `RunInvariant` — hence `IrreflOrd` **and** `OrdTimesKnown`, register entries 7 and 16's settled
   repair — holds after the oriented arm at the reuse witness;
4. …and at the gate configuration;
5. the oriented merge **target** is a known time at both configurations. This is precisely
   `UniverseClosedAt` clause 2's restriction (entries 10-12), so the confinement bridge
   `universeClosedAt_identify_at_trigger` applies at the oriented arm with nothing extra assumed —
   note clause 2 already quantifies its *source* time freely, which is why the swap costs nothing
   there;
6. confinement itself, decided: the post-arm branch stays inside the retiming-closed universe;
7. **at the gate configuration the oriented arm and the current arm are the same list.** The gate's
   trigger reports `(2, 0)`, so `min = 0 = t₂` and `max = 2 = t₁`, and the orientation is already
   what the current arm does there. Nothing at the gate regresses, and nothing at the gate is
   evidence *for* the mechanism either — which is why the reuse witness, where the two orientations
   genuinely differ, carries the verdict. -/
theorem oriented_gate_invariants :
    firstIncomparablePair reuseWitnessBranch reuseWitnessOrd = some (0, 2) ∧
    firstIncomparablePair gateBranch gateOrd = some (2, 0) ∧
    RunInvariant (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1
      (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).2 ∧
    RunInvariant (identifyOriented gateBranch gateOrd 2 0).1
      (identifyOriented gateBranch gateOrd 2 0).2 ∧
    ((identifyOrient 0 2).2 ∈ reuseWitnessBranch.knownTimes ∧
      (identifyOrient 2 0).2 ∈ gateBranch.knownTimes) ∧
    ((∀ x ∈ reuseWitnessBranch, x ∈ orientedReuseUniverse) ∧
      ∀ x ∈ (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1,
        x ∈ orientedReuseUniverse) ∧
    (identifyOriented gateBranch gateOrd 2 0).1 = Branch.identifyTime gateBranch 0 2 := by
  refine ⟨by decide, by decide, ⟨?_, ?_⟩, ⟨?_, ?_⟩, by decide, by decide, by decide⟩
  · unfold IrreflOrd; decide
  · unfold OrdTimesKnown; decide
  · unfold IrreflOrd; decide
  · unfold OrdTimesKnown; decide

/-- **The one exposure the orientation inherits, measured at the gate before it is proved in
general.** `identifyTime_no_collapse` is stated from an `incomparableB ord (t₁, t₂)` hypothesis
whose three conjuncts are written asymmetrically in `t₁` / `t₂`, so applying it at the flipped
orientation needs `incomparableB` to be symmetric in its pair.

Decided here at both witness orderings, in both directions. That is evidence, not proof: the
general `incomparableB_symm` is a named obligation of the next phase, and if it turns out to be
false in general the mechanism dies there rather than here. Recording the decided instances now
means a reader can see the obligation was identified before it was needed. -/
theorem oriented_arm_symmetric_trigger :
    incomparableB reuseWitnessOrd (0, 2) = true ∧
      incomparableB reuseWitnessOrd (2, 0) = true ∧
      incomparableB gateOrd (2, 0) = true ∧
      incomparableB gateOrd (0, 2) = true := by decide


/-! #### Run-level monotonicity, off the gate configuration

Phase 1 decided the mechanism at two witnesses. This subsection lifts it: the same statements
quantified over every branch, every ordering and both times, plus the one citation the design rests
on turned into a checked statement.

*The one finding worth recording up front.* The general form needs **no membership hypotheses at
all**. `maxTime_le_identifyTime_of_le` asks only `src ≤ tgt`, and `min t₁ t₂ ≤ max t₁ t₂` is
unconditional, so `maxTime_le_identifyTime_oriented` holds for arbitrary times on an arbitrary
branch. The plan-time shape carried `t₁ ∈ b.knownTimes` and `t₂ ∈ b.knownTimes`; both turned out to
be unnecessary, which is a strengthening rather than a shortcut — the hypotheses reappear only in
`retired_lt_nextTime_oriented`, where the *retired* index has to be located below `b.maxTime` and
membership is genuinely what does it. -/

/-- **The mechanism in one lemma, with the orientation abstracted away.** Identifying a time into a
time at least as large never lowers `Branch.maxTime`.

Every branch formula survives the relabelling (`mem_identifyTime`), so it is enough to place each
pre-arm time under the post-arm maximum. A formula not sitting at `src` keeps its time outright; a
formula sitting at `src` moves to `tgt`, and `src ≤ tgt` is exactly what carries the bound across
that move. No membership hypothesis is used, and none is available to be used — the statement is
true on an arbitrary branch at arbitrary times.

This is the whole of Candidate A's content. Everything below is instantiation. -/
theorem maxTime_le_identifyTime_of_le {b : Branch} {src tgt : TimeIndex} (h : src ≤ tgt) :
    b.maxTime ≤ (b.identifyTime src tgt).maxTime := by
  refine maxTime_le_of_forall ?_
  intro sf hsf
  have hle : (rhoSF src tgt sf).label.time ≤ (b.identifyTime src tgt).maxTime :=
    le_maxTime (mem_identifyTime b src tgt sf hsf)
  by_cases hc : sf.label.time = src
  · have hr : (rhoSF src tgt sf).label.time = tgt := by simp [rhoSF, rho, hc]
    rw [hr] at hle
    exact le_trans (hc ▸ h) hle
  · have hr : (rhoSF src tgt sf).label.time = sf.label.time := by simp [rhoSF, rho, hc]
    rw [hr] at hle
    exact hle

/-- **`Branch.maxTime` is non-decreasing across the oriented arm**, on every branch and at every
pair. The general form of `oriented_arm_does_not_reissue`'s third conjunct, and the reason the
orientation is the mechanism rather than a coincidence of the witness.

Contrast `ordTimes_identifyTime_arm3_false` and `oriented_arm_is_not_inert` conjunct 5: at the
*current* orientation `Branch.maxTime` demonstrably falls. There is no hypothesis that could be
added to rescue the current arm, because the drop is what the arm does. -/
theorem maxTime_le_identifyTime_oriented (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    b.maxTime ≤ (identifyOriented b ord t₁ t₂).1.maxTime :=
  maxTime_le_identifyTime_of_le min_le_max

/-- **…and so is `Branch.nextTime`.** The immediate corollary, stated separately because this is
the form the nine mint sites in `Tableau.lean` consume: each of them reads `branch.nextTime`, and
none of them needs an edit once this holds, since `Branch.nextTime = Branch.maxTime + 1` is
unchanged and `Nat.succ` is monotone.

That is the payoff of the byte-unchanged-definitions constraint, stated as a theorem rather than
argued: the repair reaches all nine mint sites without touching any of them. -/
theorem nextTime_le_identifyTime_oriented (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    b.nextTime ≤ (identifyOriented b ord t₁ t₂).1.nextTime :=
  Nat.succ_le_succ (maxTime_le_identifyTime_oriented b ord t₁ t₂)

/-- **The statement that replaces the obstruction.** The index the oriented arm retires is strictly
below the branch's next fresh time *after* the arm — so it cannot be the value the next mint
issues, and register entry 15's configuration cannot arise.

Membership of both times is used here and is genuinely needed: the retired index has to be placed
under `b.maxTime` before monotonicity can carry it under the post-arm `nextTime`, and only
membership does that. `firstIncomparablePair_spec` supplies both at the engine's own trigger, so
the hypotheses cost nothing at the one call site there is.

This is the theorem C9 entry 18 cites. If a later phase fails, it fails downstream of this. -/
theorem retired_lt_nextTime_oriented {b : Branch} (ord : TimeOrdering) {t₁ t₂ : TimeIndex}
    (h₁ : t₁ ∈ b.knownTimes) (h₂ : t₂ ∈ b.knownTimes) :
    (identifyOrient t₁ t₂).1 < (identifyOriented b ord t₁ t₂).1.nextTime := by
  have hmax : max t₁ t₂ ≤ b.maxTime := by
    rcases Nat.le_total t₁ t₂ with hle | hle
    · rw [Nat.max_eq_right hle]; exact le_maxTime_of_mem_knownTimes h₂
    · rw [Nat.max_eq_left hle]; exact le_maxTime_of_mem_knownTimes h₁
  calc (identifyOrient t₁ t₂).1 ≤ b.maxTime := le_trans min_le_max hmax
    _ < b.nextTime := Nat.lt_succ_self _
    _ ≤ _ := nextTime_le_identifyTime_oriented b ord t₁ t₂

/-- The ordered split's three arms as they read under the orientation. Arms 1 and 2 are byte-for-byte
what `applyRule .timeLinearity` already produces; only the third differs.

Stated here so run-level monotonicity is provable **before** `Tableau.lean` is edited, and so the
edit that lands in the engine has a named referent to be checked against rather than being its own
specification. -/
def orientedSplitArms (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    List (Branch × TimeOrdering) :=
  [ (b, ord.addFuture t₁ t₂), (b, ord.addFuture t₂ t₁), identifyOriented b ord t₁ t₂ ]

/-- **The "single non-additive step" claim, checked rather than cited.**
`Verified/Decidable.lean:274` asserts in prose that the ordered split's identification arm is the
engine's only non-additive branch step. This is that assertion as a theorem, and the enumeration
behind it is complete: `ExpansionResult` has exactly **four** constructors, and every one is
accounted for.

* `.saturated` — no successor branch at all, so `unorderedSuccessorBranches` is `[]`.
* `.extended` — one successor, of shape `fs ++ b` (`expandOnceUnblocked_extended_shape`).
* `.split` — its arms, each containing `b` (`expandOnceUnblocked_split_subset`).
* `.splitOrdered` — contributes nothing to `unorderedSuccessorBranches` by construction, and is
  covered by the second conjunct, which returns the exact three-arm list.

Conjunct 1 is `expandOnceUnblocked_branch_mono`, which was already landed and is stated at exactly
the generality the check needs; conjunct 2 is `expandOnceUnblocked_splitOrdered_shape`. Composing
them is the check: **every** successor of **every** shape either contains `b` verbatim or is one of
the three ordered-split arms, of which only the third moves a time. No second branch-shrinking arm
exists, so Phase 1's verdict about arm 3 does establish run-level monotonicity rather than a
statement about one arm.

Conjunct 2 now reads `bs = orientedSplitArms b ord t₁ t₂` on the nose. That is not a restatement
for tidiness: since the engine's arm is itself oriented, `orientedSplitArms` has stopped being a
prototype standing in for the arm and *is* the arm, so everything proved about it below is a
statement about runs the engine actually takes. -/
theorem expandOnce_branch_shape_census {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker} :
    (∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1, ∀ x ∈ b, x ∈ nb) ∧
    (∀ bs, (expandOnceUnblocked b ord fc tr).1 = ExpansionResult.splitOrdered bs →
      ∃ t₁ t₂, firstIncomparablePair b ord = some (t₁, t₂) ∧
        bs = orientedSplitArms b ord t₁ t₂) :=
  ⟨expandOnceUnblocked_branch_mono, fun _ h => expandOnceUnblocked_splitOrdered_shape h⟩

/-- `Branch.maxTime` does not fall at any of the three oriented arms. Arms 1 and 2 leave the branch
literally unchanged — they move only the ordering — so they are `Nat.le_refl`; arm 3 is
`maxTime_le_identifyTime_oriented`. -/
theorem maxTime_le_orientedSplitArms (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    ∀ p ∈ orientedSplitArms b ord t₁ t₂, b.maxTime ≤ p.1.maxTime := by
  intro p hp
  simp only [orientedSplitArms, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact maxTime_le_identifyTime_oriented b ord t₁ t₂

/-- **Run-level monotonicity of `Branch.maxTime`**, composing the shape census with the arm result:
across every successor of every shape the engine can report, the branch maximum is non-decreasing.

Conjunct 1 covers `.extended` and `.split` — the additive shapes — through
`expandOnceUnblocked_branch_mono` and `maxTime_mono`. Conjunct 2 covers the ordered split, stated
at the engine's **own** `.splitOrdered` result rather than at a hypothetical arm list: since the
live arm is the oriented one, the shape census turns any reported `bs` into `orientedSplitArms` and
`maxTime_le_orientedSplitArms` finishes. `.saturated` reports no successor and is covered by
conjunct 1 vacuously, which is absence of a successor rather than a weakening of the claim.

Together the two conjuncts exhaust the engine's step: **no successor of any shape has a smaller
`Branch.maxTime` than the branch it came from.** This is the run-level statement Phase 1's gate
decided at one configuration. -/
theorem maxTime_monotone_along_run {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker} :
    (∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
        b.maxTime ≤ nb.maxTime) ∧
      (∀ bs, (expandOnceUnblocked b ord fc tr).1 = ExpansionResult.splitOrdered bs →
        ∀ p ∈ bs, b.maxTime ≤ p.1.maxTime) :=
  ⟨fun nb hnb => maxTime_mono (expandOnceUnblocked_branch_mono nb hnb),
   fun _ h => by
     obtain ⟨t₁, t₂, -, rfl⟩ := (expandOnce_branch_shape_census (fc := fc) (tr := tr)).2 _ h
     exact maxTime_le_orientedSplitArms b ord t₁ t₂⟩

/-- **…and hence of fresh-time issuance itself.** `Branch.nextTime` is `Branch.maxTime + 1` by a
definition this task leaves byte-unchanged, so monotonicity of the one is monotonicity of the
other. This is the run-level form of the property register entry 15 says is unavailable — and it
*was* unavailable at the unoriented arm, which is why the repair went to the arm and not to the
measure.

**Read as a statement about reuse**: every fresh time the engine mints is `nb.maxTime + 1` for the
branch it mints on, and no branch along a run has a smaller `maxTime` than its predecessor, so
every mint is strictly above every time index the run has ever carried — including every index an
earlier identification retired. `nextTime_reissues_retired_time`'s configuration cannot recur on
the engine path; see `reuse_driven_through_engine` for the same fact decided at that witness. -/
theorem nextTime_monotone_along_run {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker} :
    (∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
        b.nextTime ≤ nb.nextTime) ∧
      (∀ bs, (expandOnceUnblocked b ord fc tr).1 = ExpansionResult.splitOrdered bs →
        ∀ p ∈ bs, b.nextTime ≤ p.1.nextTime) :=
  ⟨fun nb hnb => Nat.succ_le_succ
      (maxTime_monotone_along_run (fc := fc) (tr := tr) |>.1 nb hnb),
   fun bs h p hp => Nat.succ_le_succ
     (maxTime_monotone_along_run (fc := fc) (tr := tr) |>.2 bs h p hp)⟩


/-! #### Invariant survival at the oriented arm, generally

The three settled repairs the register protects — `OrdTimesKnown` (entries 7 and 16), the
`UniverseClosedAt` confinement (entries 10-12), and the `.splitOrdered` measure's first component —
re-proved at the oriented arm for arbitrary branches and times, not only at the gate.

*R1 is closed, and the answer is the favourable one.* `incomparableB_symm` was the plan's single
most likely point of failure: `identifyTime_no_collapse` is stated from an `incomparableB
ord (t₁, t₂)` hypothesis written asymmetrically in `t₁` / `t₂`, and the oriented arm applies it at
the flipped pair whenever `t₁ < t₂`. The symmetry **holds**, and it reduces to the reachability
duality this development already owns — with one gap, recorded below.

*The one thing that was genuinely missing.* `orderDual_holds` (`Fuel.lean`) states the duality in
the forward direction only: `t₂ ∈ futureOf t₁ → t₁ ∈ pastOf t₂`. `incomparableB_symm` needs the
mirror as well, and the mirror was not landed anywhere. `orderDual_backward` supplies it, by the
same three-step argument at the converse step relation. That is the only declaration in this
subsection that is not an instantiation of something already proved, and recording it is the point
of the plan's "a lemma that needed an independent proof is a signal" instruction: the signal here
is small and localised — a missing mirror in a reachability calculus, not a defect in the
orientation.

*Where those two live.* `orderDual_backward` and `incomparableB_symm` are landed in section A,
alongside `incomparableB_of_firstIncomparablePair`, rather than here: the engine-facing arm-3
lemmas consume them far above this subsection, and Lean's dependency order decides the position.
Their content is this subsection's; only their location is not. -/

/-- **Collapse-freedom at the oriented arm.** `identifyTime_no_collapse` restated at
`(min t₁ t₂, max t₁ t₂)`, by a case split on which of the two times is the smaller.

When `t₂ ≤ t₁` the oriented arm *is* the current arm and the lemma applies verbatim. When
`t₁ ≤ t₂` the arguments are flipped and `incomparableB_symm` supplies the hypothesis at the flipped
pair. Both branches are direct instantiations; the case split is the whole of the new content. -/
theorem identifyTime_no_collapse_oriented (ord : TimeOrdering) (t₁ t₂ : TimeIndex)
    (hinc : incomparableB ord (t₁, t₂) = true) (hnsl : IrreflOrd ord)
    (a b : TimeIndex) (h : (a, b) ∈ ord.constraints) :
    rho (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 a
      ≠ rho (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 b := by
  simp only [identifyOrient]
  rcases Nat.le_total t₁ t₂ with hle | hle
  · rw [Nat.min_eq_left hle, Nat.max_eq_right hle]
    exact identifyTime_no_collapse ord t₂ t₁ (incomparableB_symm hinc) hnsl a b h
  · rw [Nat.min_eq_right hle, Nat.max_eq_left hle]
    exact identifyTime_no_collapse ord t₁ t₂ hinc hnsl a b h

/-- Irreflexivity at the oriented arm. A direct instantiation:
`irreflOrd_identifyTime` is already quantified over both of its times and takes no hypotheses at
all, so the orientation is invisible to it. -/
theorem irreflOrd_identifyTime_oriented (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex) :
    IrreflOrd (identifyOriented b ord t₁ t₂).2 :=
  irreflOrd_identifyTime ord _ _

/-- **Register entries 7 and 16's settled repair, at the oriented arm.** A direct instantiation, as
the plan predicted: `ordTimesKnown_identifyTime`'s docstring records that it needs *no trigger
hypotheses at all* — not `firstIncomparablePair`, not `IrreflOrd` — because it is a structural fact
about branch and ordering being relabelled by the same `rho`. A fact of that shape cannot notice
which way round its two times are.

This is the lemma whose failure would have been the quiet regression the plan warns about, so it is
stated separately rather than only inside the bundle below. -/
theorem ordTimesKnown_identifyTime_oriented {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (h : OrdTimesKnown b ord) :
    OrdTimesKnown (identifyOriented b ord t₁ t₂).1 (identifyOriented b ord t₁ t₂).2 :=
  ordTimesKnown_identifyTime h

/-- The run invariant survives the oriented arm, bundled. Both components are unconditional in the
orientation, so the bundle is too. -/
theorem runInvariant_identifyTime_oriented {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (h : RunInvariant b ord) :
    RunInvariant (identifyOriented b ord t₁ t₂).1 (identifyOriented b ord t₁ t₂).2 :=
  ⟨irreflOrd_identifyTime_oriented b ord t₁ t₂, ordTimesKnown_identifyTime_oriented h.2⟩

/-- **R2, discharged: the termination measure's first component still strictly drops.**
`knownTimes_card_lt_identifyTime` at the oriented arguments.

Its hypotheses are membership of both times plus distinctness, and `firstIncomparablePair_spec`
supplies all three in either orientation — which is exactly why the risk register rated this low
and why it is proved **here**, in `MintBound.lean`, before `Tableau.lean` is touched. The
`.splitOrdered` lexicographic measure's arm-3 discharge is therefore never in doubt at any point in
the remaining phases. -/
theorem knownTimes_card_lt_identifyTime_oriented {b : Branch} {ord : TimeOrdering}
    {t₁ t₂ : TimeIndex} (h1 : t₁ ∈ b.knownTimes) (h2 : t₂ ∈ b.knownTimes) (hne : t₂ ≠ t₁) :
    ((identifyOriented b ord t₁ t₂).1.knownTimes).toFinset.card
      < (b.knownTimes).toFinset.card := by
  simp only [identifyOriented, identifyOrient]
  rcases Nat.le_total t₁ t₂ with hle | hle
  · rw [Nat.min_eq_left hle, Nat.max_eq_right hle]
    exact knownTimes_card_lt_identifyTime h2 h1 (Ne.symm hne)
  · rw [Nat.min_eq_right hle, Nat.max_eq_left hle]
    exact knownTimes_card_lt_identifyTime h1 h2 hne

/-! Register entries 10-12's confinement bridge at the oriented arm is
`universeClosedAt_identify_at_trigger_oriented`, landed beside its unoriented original where the
engine-level consumers reach it. It discharges the *existing* clause 2: the predicate already
quantifies its source time freely and restricts only its target, so swapping which member of the
pair is which costs exactly the one fact `firstIncomparablePair_spec_oriented` supplies, and adds
no hypothesis. Nothing here constrains `t₂` as well as `t₁` — entry 12 decides that both-times
form is the weaker one, not the repair. -/

/-- **…and clause 2 discharged at the concrete universe, at the oriented arm.**
`timeMergeClosed_identifyTime_signedUniverse` at the oriented merge, so the whole confinement chain
— predicate, bridge, and concrete discharge — is available in the oriented form rather than only
the first two links of it. Same one fact, same source: the surviving numeral is a known time. -/
theorem timeMergeClosed_identifyTime_oriented {C : Finset Formula} {L : Finset Label}
    (hL : TimeMergeClosed L) {b : Branch} {ord : TimeOrdering}
    (hb : ∀ x ∈ b, x ∈ signedUniverse C L) {t₁ t₂ : TimeIndex}
    (h1 : t₁ ∈ b.knownTimes) (h2 : t₂ ∈ b.knownTimes) :
    ∀ x ∈ (identifyOriented b ord t₁ t₂).1, x ∈ signedUniverse C L := by
  refine timeMergeClosed_identifyTime_signedUniverse hL hb (t₁ := (identifyOrient t₁ t₂).2)
    (t₂ := (identifyOrient t₁ t₂).1) ?_
  simp only [identifyOrient]
  rcases Nat.le_total t₁ t₂ with hle | hle
  · rw [Nat.max_eq_right hle]; exact h2
  · rw [Nat.max_eq_left hle]; exact h1


/-! ### The self-guard component re-gated at the oriented arm

Phase 1's gate above is a statement about the renaming the identification arm produced **at the
time that gate was built**. Arm 3 merged `t₂` into `t₁` whatever their magnitudes, so at the reuse
witness's own trigger `(0, 2)` it produced `rhoSF 2 0` — retiring the *larger* numeral — and
`gateSigma` is exactly that renaming. `identifyOrient` retires the smaller numeral instead, so at
the same trigger the arm now produces `rhoSF 0 2`, and no run produces `rhoSF 2 0` there any more.

That distinction is the whole of the σ-hit obligation, and it cuts the other way from Phase 1.
`rhoSF src tgt`'s image omits exactly `src` (`rhoSF_time_ne_src`) and fixes every other time on the
nose (`rhoSF_time_eq_of_ne_src` below), while `src_not_mem_knownTimes_identifyTime` says the
post-arm branch carries no formula at `src` at all. Under the oriented arm the renaming therefore
fixes the time of **every formula the branch still carries**, so the *time* hit `selfGuardPotential`
needs is available at every trigger the engine can select: the trigger is a branch formula, and the
branch's times are precisely the ones the renaming fixes.

**`mintPaysForTimeAt_reuse_false` is untouched by this and stays true exactly as stated.**
`MintPaysForTimeAt` quantifies `σ` with no tie to the state it is read at, so a renaming no run
produces still refutes it, and register entry 17 stands as a statement about that predicate. What
changes is that the refuting renaming is now identifiable *by a property of the state it is applied
at* rather than only by provenance: `gateSigma` moves the gate's own trigger off its own time, and
no renaming the oriented arm produces does that to a formula the branch still carries.
`SigmaTimeStable` names that property; `MintPaysForTimeStable` is `MintPaysForTimeAt` carrying it.
-/

/-- **The converse of `rhoSF_time_ne_src`: every time but the retired one is fixed on the nose.**

One line, and it is the positive half of the σ-hit story that Phase 1 had no use for. `rho src tgt`
is an `if` on `t = src`, so away from `src` it is the identity — which is why the *only* time a
single identification's renaming can fail to hit is the one it retires. -/
theorem rhoSF_time_eq_of_ne_src {src tgt : TimeIndex} {sf : SignedFormula}
    (h : sf.label.time ≠ src) : (rhoSF src tgt sf).label.time = sf.label.time := by
  simp [rhoSF, rho, h]

/-- **The converse of `selfGuard_no_column_at_retired_time`: at a live time a column *is* indexed.**

`selfGuard_no_column_at_retired_time` says no column of `selfGuardRules ×ˢ U` sits at the retired
index. This says the retired index is the *only* one missing: for any `sf ∈ U` whose time is not
`src`, the pair `(untlNeg, sf)` is a column of the index set and its σ-image sits at exactly
`sf.label.time`.

Together the two lemmas locate the obstruction precisely. It was never that the ledger is indexed
too narrowly; it was that the one time the renaming omits happened, under the unoriented arm, to be
a time the engine could re-issue and put a trigger at. -/
theorem selfGuard_column_at_live_time {src tgt : TimeIndex} {U : Finset SignedFormula}
    {sf : SignedFormula} (hsf : sf ∈ U) (hlive : sf.label.time ≠ src) :
    ((TableauRule.untlNeg, sf) : TableauRule × SignedFormula) ∈ selfGuardRules ×ˢ U ∧
      (rhoSF src tgt sf).label.time = sf.label.time := by
  have hr : TableauRule.untlNeg ∈ selfGuardRules := by decide
  exact ⟨Finset.mem_product.mpr ⟨hr, hsf⟩, rhoSF_time_eq_of_ne_src hlive⟩

/-- The orientation's two numerals are distinct exactly when the trigger's are. -/
theorem identifyOrient_ne {t₁ t₂ : TimeIndex} (hne : t₁ ≠ t₂) :
    (identifyOrient t₁ t₂).1 ≠ (identifyOrient t₁ t₂).2 := by
  simp only [identifyOrient]
  rcases Nat.le_total t₁ t₂ with hle | hle
  · rw [Nat.min_eq_left hle, Nat.max_eq_right hle]; exact hne
  · rw [Nat.min_eq_right hle, Nat.max_eq_left hle]; exact hne.symm

/-- **σ-time-stability**: the accumulated renaming moves no formula the branch still carries off
its own time.

This is the property that separates the renamings a run can produce from the ones it cannot, and it
is stated *at the state* rather than by provenance so that it can be assumed, discharged and
decided. It is deliberately weaker than "σ fixes the branch pointwise" — only times are constrained,
because only times are what `selfGuardDischarged` reads.

Note what it does **not** say. It puts no condition on `σ` away from `b`, so it does not exclude a
renaming that moves times the branch has already lost; that is exactly right, since a column at a
lost time can no longer be flipped by any rule the engine fires. -/
def SigmaTimeStable (σ : SignedFormula → SignedFormula) (b : Branch) : Prop :=
  ∀ x ∈ b, (σ x).label.time = x.label.time

/-- **The oriented arm's own renaming is σ-time-stable at the state the arm produces.**

The general reason the re-gate below comes out the other way, and it needs nothing but the two
facts either side of it: the post-arm branch carries no formula at the retired index
(`src_not_mem_knownTimes_identifyTime`), and away from that index the renaming is the identity on
times (`rhoSF_time_eq_of_ne_src`).

No membership hypothesis on `t₁` or `t₂` is used, and none is available to be used — the statement
holds on an arbitrary branch at any two distinct times. Under the unoriented arm the same proof
gives the same conclusion about `rhoSF t₂ t₁`; what the orientation buys is not this lemma but
`retired_lt_nextTime_oriented`, which is what stops the engine from ever putting a trigger back at
the retired index. -/
theorem sigmaTimeStable_identifyOriented {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (hne : t₁ ≠ t₂) :
    SigmaTimeStable (rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2)
      (identifyOriented b ord t₁ t₂).1 := by
  intro x hx
  simp only [identifyOriented] at hx
  refine rhoSF_time_eq_of_ne_src ?_
  intro hEq
  have hmem : x.label.time
      ∈ (b.identifyTime (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2).knownTimes :=
    mem_knownTimes_of_mem hx
  rw [hEq] at hmem
  exact src_not_mem_knownTimes_identifyTime b _ _ (identifyOrient_ne hne) hmem

/-- **`SigmaTimeStable` is exactly what excludes Phase 1's gate, and it excludes nothing else
there.** Decided at both configurations, side by side, so the exclusion is measured rather than
asserted.

Conjunct 1 is the whole content: `gateSigma = rhoSF 2 0` moves the gate's own trigger off time `2`,
which is why no column of the ledger sat at the trigger's time and why disjunct 3 could not fall.
Conjunct 2 records that the oriented renaming is no better *at that branch* — `gateBranch` carries
a formula at time `0`, the index the oriented arm retires — which is the honest statement: the
Phase-1 gate is not a state the oriented arm produces at all, under either renaming. Conjunct 3 is
the oriented gate below, where the arm's own renaming is stable. -/
theorem gateSigma_not_sigmaTimeStable :
    (¬ SigmaTimeStable gateSigma gateBranch) ∧ ¬ SigmaTimeStable (rhoSF 0 2) gateBranch := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact absurd (h gateTrigger (by decide)) (by decide)
  · exact absurd (h (SignedFormula.pos mwP ⟨0, 0⟩) (by decide)) (by decide)

/-- **The repaired time-minting residual**: `MintPaysForTimeAt`'s body verbatim, with the renaming
tied to the state it is read at by one added hypothesis and nothing removed.

Two hypotheses were added to `MintPaysForTime` on the way here and both weaken the predicate, so
the implication runs `MintPaysForTime → MintPaysForTimeStable` and never the other way. This is the
`universeClosedAt_of_universeClosed` idiom. It does **not** factor through `MintPaysForTimeAt`: that
predicate's third disjunct is the bare `selfGuardPotential` drop, this one's pairs the drop with a
combined-budget conjunct, and the pairing is forced — see below.

**What the added hypothesis is for.** `MintPaysForTimeAt` is refuted as stated by
`mintPaysForTimeAt_reuse_false`, and that refutation is permanent: `σ` is quantified there with no
tie to `b`, so a renaming that moves the trigger off its own time defeats any σ-mediated ledger.
`SigmaTimeStable σ b` is the minimal statement excluding exactly that, and it is not a wish —
`sigmaTimeStable_identifyOriented` discharges it at the state the identification arm produces, with
no membership hypothesis at all.

**What it is not.** It is not a constraint on the frame class, on `U`, on `Tmax`, or on the branch;
it is a constraint on the renaming, which is the one argument of `MintPaysForTime` that no consumer
of the terminus supplies from outside. See `mintPaysForTimeStable_no_leak` below.

**Why the third disjunct is a pair.** It mirrors disjunct 2 exactly: disjunct 2 pairs a
`mintPotential` drop with a `mintTimeBudget` non-increase, and this one pairs a `selfGuardPotential`
drop with a **combined**-budget non-increase — the mint budget plus the self-guard potential. The
pairing is forced, not decorative. A self-guarded mint raises `mintTimeBudget` by one, and
`extensionAllowance` carries a factor of `|U|` per unit of mint budget, so without a cap on the
combined quantity the measure does not fall however the fourth component is weighted. The combined
form is the right one because the mint spends exactly one unit of the fourth component to buy the
one unit of mint budget it consumes: the component funds the budget rather than sitting beside it.
Measured at the oriented gate, `26 + 3 = 29` before and `27 + 1 = 28` after
(`orientedGate_disjunct3_holds`). The consequence is that `MintPaysForTimeAt`, whose third disjunct
is the bare drop, does **not** imply this predicate; see `mintPaysForTimeStable_of_mintPaysForTime`.

**The density residual is unchanged.** Everything `MintPaysForTimeAt`'s obligation map records
about `densityRule` applies here verbatim: `densityRule` mints a fresh time while lying outside
both `freshLabelRules` and `selfGuardRules`, so no disjunct moves, and the intended component
`gapPotential` remains a named residual. See the subsection "The density residual" and register
entry 17. -/
def MintPaysForTimeStable (fc : FormalSystem.ProofSystem.FrameClass) (U : Finset SignedFormula)
    (Tmax : Nat) : Prop :=
  ∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
    (tr : EventualityTracker), RunInvariant b ord → (∀ x ∈ b, x ∈ U) → SigmaTimeStable σ b →
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      (nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb (expandOnceUnblocked b ord fc tr).2
          ≤ splitOrderedRank Tmax b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord ∧
          mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
            < mintPotential U σ b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
          selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            < selfGuardPotential U σ ord)

/-- **Direction lemma, first link.** `MintPaysForTimeAt` adds a disjunct and removes nothing, so
every consumer of `MintPaysForTime` can be restated against it. -/
theorem mintPaysForTimeAt_of_mintPaysForTime {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat} (h : MintPaysForTime fc U Tmax) :
    MintPaysForTimeAt fc U Tmax := by
  intro σ b ord tr hri hconf nb hnb
  rcases h σ b ord tr hri hconf nb hnb with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

/-- **Direction lemma, second link.** The statement a reader restating an existing terminus needs:
`MintPaysForTimeStable` adds a hypothesis and a disjunct and removes nothing, so it is weaker than
`MintPaysForTime` and every theorem restated against it is a strengthening.

**It does *not* factor through `MintPaysForTimeAt`, and that is deliberate.** The two predicates'
third disjuncts differ: `MintPaysForTimeAt`'s is the bare `selfGuardPotential` drop, while this
one's pairs that drop with a **combined-budget** conjunct, exactly as disjunct 2 pairs its
`mintPotential` drop with a plain budget conjunct. The pairing is not decoration — see
`budgetStateAt_of_disjunct3` — so `MintPaysForTimeAt → MintPaysForTimeStable` is unavailable and is
not claimed. Both disjuncts 1 and 2 survive verbatim, which is all this lemma needs. -/
theorem mintPaysForTimeStable_of_mintPaysForTime {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat} (h : MintPaysForTime fc U Tmax) :
    MintPaysForTimeStable fc U Tmax := by
  intro σ b ord tr hri hconf _ nb hnb
  rcases h σ b ord tr hri hconf nb hnb with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

/-! #### The oriented gate: the same measurement at the renaming the oriented arm produces

Phase 1's gate is rebuilt here at the state the *oriented* arm hands back from the same reuse
witness at the same trigger `(0, 2)`. Everything is a faithful mirror: the ordering is
`TimeOrdering.identifyTime reuseWitnessOrd 0 2` on the nose, the branch is that arm's branch with an
`untlNeg` trigger placed at the one time whose forward reach the ordering leaves empty, and the
renaming is the `rhoSF` the arm itself produces. Only the orientation differs.

The discipline is Phase 1's, unchanged. All three disjuncts are measured, not just the favourable
one; the hazard conjuncts are decided separately so a verdict cannot be attributed to a violated
precondition; and the unfavourable renaming is measured at the same step so the verdict is located
at σ rather than at the ledger's shape. -/

/-- The oriented gate's trigger. `untl` again, so the vehicle is `mintWitnessTrigger`'s and the
comparison with Phase 1 is at one moving part. It sits at time `1`, the time whose forward reach
the post-arm ordering leaves empty — `untlNeg`'s ACTIVE guard. -/
def orientedGateTrigger : SignedFormula := SignedFormula.neg (Formula.untl mwG mwE) ⟨0, 1⟩

/-- The oriented gate branch: the trigger, then the two atoms the oriented arm leaves at times `2`
and `1`. Under the orientation the retired numeral is `0`, so — unlike `gateBranch` — no formula
here sits at a retired index, which is exactly what `orientedGate_sigmaTimeStable` decides. -/
def orientedGateBranch : Branch :=
  [orientedGateTrigger, SignedFormula.pos mwP ⟨0, 2⟩, SignedFormula.pos mwQ ⟨0, 1⟩]

/-- The oriented gate ordering. It is `TimeOrdering.identifyTime reuseWitnessOrd 0 2` on the nose:
the arm substitutes `0 ↦ 2` in the single constraint `(0, 1)`, leaving `(2, 1)`. `futureOf 1` is
empty and `timeCount` is `2`, which is `untlNeg`'s ACTIVE guard. -/
def orientedGateOrd : TimeOrdering := ⟨[(2, 1)]⟩

/-- The oriented gate universe: the branch itself, so confinement is immediate — the same choice
`gateUniverse` makes. -/
def orientedGateUniverse : Finset SignedFormula :=
  {orientedGateTrigger, SignedFormula.pos mwP ⟨0, 2⟩, SignedFormula.pos mwQ ⟨0, 1⟩}

/-- The first arm of the split the ACTIVE `untlNeg` reports: `F(e)` at the freshly minted time `3`,
the re-included trigger, and the original branch. -/
def orientedGateSucc : Branch :=
  [SignedFormula.neg mwE ⟨0, 3⟩, orientedGateTrigger, orientedGateTrigger,
   SignedFormula.pos mwP ⟨0, 2⟩, SignedFormula.pos mwQ ⟨0, 1⟩]

/-- The ordering after the ACTIVE arm: `addFuture 1 3` prepended. This is the edge that cures the
trigger's column — and, under the oriented renaming, the column is actually there to be cured. -/
def orientedGateNewOrd : TimeOrdering := ⟨[(1, 3), (2, 1)]⟩

/-- **The renaming the oriented arm produces.** `rhoSF 0 2`, not `rhoSF 2 0`: `identifyOrient 0 2`
is `(0, 2)`, so the numeral the arm retires is `0` and the numeral that survives is `2`.

`gateSigma` is the *same arm at the same trigger* under the old orientation, which is the entire
difference between this subsection's verdict and Phase 1's. -/
def orientedGateSigma : SignedFormula → SignedFormula := rhoSF 0 2

/-- The oriented gate state satisfies the run invariant. -/
theorem orientedGate_runInvariant : RunInvariant orientedGateBranch orientedGateOrd := by
  constructor
  · unfold IrreflOrd orientedGateOrd; decide
  · unfold OrdTimesKnown; decide

/-- …and it is confined to the oriented gate universe. -/
theorem orientedGate_confined : ∀ x ∈ orientedGateBranch, x ∈ orientedGateUniverse := by decide

/-- **The oriented gate really is the oriented arm's state at the reuse witness's own trigger.**
Seven conjuncts, all decided, in the discipline `gate_is_reissue_hazard` uses — and deliberately
the *same seven questions*, so the two gates can be read side by side.

1-2. the standing hypotheses hold at the oriented gate state;
3. `firstIncomparablePair` selects `(0, 2)` on the predecessor state, so the identification that
   produces `orientedGateSigma` is the one the engine itself takes;
4. the numeral the oriented arm retires is `0`, and it really is retired;
5. …and, unlike under the old orientation, it is **not** re-issued: the post-arm `nextTime` is `3`,
   strictly above the retired index. This is conjunct 5 of `gate_is_reissue_hazard` with its verdict
   reversed, and it is the whole mechanism;
6. the oriented gate ordering is exactly what that identification leaves behind;
7. the trigger sits at a live time and `untlNeg`'s ACTIVE guard is met there — empty forward reach,
   with `timeCount` inside the `(0, 4)` window. -/
theorem orientedGate_is_oriented_arm_state :
    IrreflOrd orientedGateOrd ∧ OrdTimesKnown orientedGateBranch orientedGateOrd ∧
      firstIncomparablePair reuseWitnessBranch reuseWitnessOrd = some (0, 2) ∧
      ((identifyOrient 0 2).1 = 0 ∧
        0 ∉ (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.knownTimes) ∧
      (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1.nextTime = 3 ∧
      orientedGateOrd.constraints
        = (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).2.constraints ∧
      (orientedGateTrigger.label.time = 1 ∧ (orientedGateOrd.futureOf 1).isEmpty = true ∧
        0 < orientedGateOrd.timeCount ∧ orientedGateOrd.timeCount < 4) := by
  refine ⟨?_, ?_, by decide, ⟨by decide, by decide⟩, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  · unfold IrreflOrd orientedGateOrd; decide
  · unfold OrdTimesKnown; decide

/-- **The oriented gate's renaming is σ-time-stable at it, and Phase 1's is not at Phase 1's.**

The discriminating hypothesis, decided at both configurations. This is the conjunct that makes
`mintPaysForTimeAt_reuse_false` and the verdict below consistent rather than contradictory: the two
gates are distinguished by a property of the *state*, not by an appeal to provenance.

Conjunct 2 also records `sigmaTimeStable_identifyOriented`'s content at the concrete configuration,
so the general lemma can be checked against a number. -/
theorem orientedGate_sigmaTimeStable :
    SigmaTimeStable orientedGateSigma orientedGateBranch ∧
      SigmaTimeStable (rhoSF (identifyOrient 0 2).1 (identifyOrient 0 2).2)
        (identifyOriented reuseWitnessBranch reuseWitnessOrd 0 2).1 := by
  refine ⟨?_, sigmaTimeStable_identifyOriented (by decide)⟩
  show ∀ x ∈ orientedGateBranch, (orientedGateSigma x).label.time = x.label.time
  decide

/-- **The engine fires the ACTIVE arm here**, at every frame class: the reported ordering is
`orientedGateNewOrd` and `orientedGateSucc` is one of the two unordered successors. `untlNeg` is a
`carrierBase` rule, so this is not a frame-class accident. The mirror of `gate_step_fires`. -/
theorem orientedGate_step_fires (fc : FormalSystem.ProofSystem.FrameClass) :
    (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).2.constraints
        = orientedGateNewOrd.constraints ∧
      orientedGateSucc ∈ unorderedSuccessorBranches
        (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).1 := by
  cases fc <;> exact ⟨by decide, by decide⟩

/-- **The self-guard potential falls at the oriented gate, under the arm's own renaming.** `3` to
`1`. The trigger's column at time `1` flips uncured → cured, and so does the column of the atom
sitting there — which is the mechanism `selfGuardPotential` was designed around, working.

This is the exact measurement `selfGuardPotential_eq_at_gate_with_sigma` reports as `3 → 3`. The
only difference is which numeral the identification arm retired. -/
theorem selfGuardPotential_lt_at_orientedGate :
    selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateNewOrd
      < selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd := by decide

/-- **All three disjuncts measured, not just the favourable one.** The mirror of the numbers in
`mintPaysForTimeAt_reuse_false`'s docstring, at the oriented gate.

Disjuncts 1 and 2 fail here exactly as they failed at Phase 1's gate, and for the same reasons: the
step mints time `3`, so `knownTimes` rises `2 → 3`; `mintTimeBudget` rises `26 → 27` and
`mintPotential` is `24` before and after, because `untlNeg` is not in `freshLabelRules`. Disjunct 3
is the one that moves, `3 → 1`, and it is the only one that does. The fourth component is carrying
the step on its own — which is what it was for. -/
theorem orientedGate_disjuncts_measured :
    orientedGateBranch.knownTimes.toFinset.card = 2 ∧
      orientedGateSucc.knownTimes.toFinset.card = 3 ∧
      mintTimeBudget orientedGateUniverse orientedGateSigma orientedGateBranch orientedGateOrd
        = 26 ∧
      mintTimeBudget orientedGateUniverse orientedGateSigma orientedGateSucc orientedGateNewOrd
        = 27 ∧
      mintPotential orientedGateUniverse orientedGateSigma orientedGateBranch orientedGateOrd
        = 24 ∧
      mintPotential orientedGateUniverse orientedGateSigma orientedGateSucc orientedGateNewOrd
        = 24 ∧
      selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd = 3 ∧
      selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateNewOrd = 1 := by
  decide

/-- **The verdict, side by side, in one statement.** The same component, the same rule, the same
witness, the same trigger — and opposite outcomes, separated only by which numeral the
identification arm retires.

Conjunct 1 restates `selfGuardPotential_eq_at_gate_with_sigma`: under the old orientation the
potential does not move. Conjunct 2 is the oriented measurement. Conjunct 3 records that the
unoriented renaming is not inert *here* either — it also falls, `4 → 2` — so the verdict is not an
artifact of the oriented gate being an easier configuration; every renaming pays at a state whose
trigger sits at a live time.

This is the pairing `oriented_arm_is_not_inert` sets the precedent for. -/
theorem orientedGate_verdict_side_by_side :
    selfGuardPotential gateUniverse gateSigma gateNewOrd
        = selfGuardPotential gateUniverse gateSigma gateOrd ∧
      selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateNewOrd
        < selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd ∧
      selfGuardPotential orientedGateUniverse gateSigma orientedGateNewOrd
        < selfGuardPotential orientedGateUniverse gateSigma orientedGateOrd := by
  decide

/-- **The repaired predicate's third disjunct, decided at the oriented gate.** Both conjuncts, at
both reported successors, at every frame class.

Split out from the verdict below because it is the half that `decide` can evaluate: the combined
budget mentions the successor branch, so the statement has to be read with the `∀ nb` still inside
it rather than after an `intro`. The numbers are `27 + 1 ≤ 26 + 3` and `1 < 3`. -/
theorem orientedGate_disjunct3_holds (fc : FormalSystem.ProofSystem.FrameClass) :
    ∀ nb ∈ unorderedSuccessorBranches
        (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).1,
      (mintTimeBudget orientedGateUniverse orientedGateSigma nb
          (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).2
          + selfGuardPotential orientedGateUniverse orientedGateSigma
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
          ≤ mintTimeBudget orientedGateUniverse orientedGateSigma orientedGateBranch
            orientedGateOrd
            + selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd) ∧
      selfGuardPotential orientedGateUniverse orientedGateSigma
          (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).2
        < selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd := by
  cases fc <;> decide

/-- **VERDICT: the re-gate decides TRUE.** `MintPaysForTimeStable`'s body holds at the oriented
gate, at every frame class, every `Tmax` and every reported successor.

*The verdict in words.* Phase 1's FALSE verdict does **not** survive the reorientation of the
identification arm. It was a statement about `rhoSF 2 0` — the renaming the arm produced when it
merged the larger numeral away — and the arm no longer produces it at that trigger, or at any
other. At the renaming the arm now produces, the self-guard discharge potential pays for the
self-guarded minting step on its own, which is what the component was designed to do.

*What is decided here and what is not.* This is a gate, and it decides exactly what Phase 1's gate
decided, with the sign reversed: the design is not refuted at the configuration that refuted it, so
the plumbing may be built. It is **not** a proof of `MintPaysForTimeStable` at any `U` — that is the
work the plan's later phases carry, and the density residual (`gapPotential`) is untouched by it.
A reader who takes this theorem for the discharge has taken a decided instance for a quantified
statement.

*Why this does not contradict `mintPaysForTimeAt_reuse_false`.* That theorem is about
`MintPaysForTimeAt`, which quantifies `σ` with no tie to the state it is read at, and it stays true.
`MintPaysForTimeStable` carries `SigmaTimeStable σ b`, which `gateSigma_not_sigmaTimeStable` decides
false at Phase 1's gate and `orientedGate_sigmaTimeStable` decides true here, and which
`sigmaTimeStable_identifyOriented` discharges at every state the identification arm produces. The
two verdicts are about two predicates and both stand. See register entry 19. -/
theorem mintPaysForTimeStable_body_at_orientedGate
    (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    ∀ nb ∈ unorderedSuccessorBranches
        (expandOnceUnblocked orientedGateBranch orientedGateOrd fc EventualityTracker.empty).1,
      (nb.knownTimes.toFinset.card ≤ orientedGateBranch.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
          ≤ splitOrderedRank Tmax orientedGateBranch orientedGateOrd)
      ∨ (mintTimeBudget orientedGateUniverse orientedGateSigma nb
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
            ≤ mintTimeBudget orientedGateUniverse orientedGateSigma orientedGateBranch
              orientedGateOrd ∧
          mintPotential orientedGateUniverse orientedGateSigma nb
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
            < mintPotential orientedGateUniverse orientedGateSigma orientedGateBranch
              orientedGateOrd)
      ∨ (mintTimeBudget orientedGateUniverse orientedGateSigma nb
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
            + selfGuardPotential orientedGateUniverse orientedGateSigma
              (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
                EventualityTracker.empty).2
            ≤ mintTimeBudget orientedGateUniverse orientedGateSigma orientedGateBranch
              orientedGateOrd
              + selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd ∧
          selfGuardPotential orientedGateUniverse orientedGateSigma
            (expandOnceUnblocked orientedGateBranch orientedGateOrd fc
              EventualityTracker.empty).2
            < selfGuardPotential orientedGateUniverse orientedGateSigma orientedGateOrd) := by
  intro nb hnb
  exact Or.inr (Or.inr (orientedGate_disjunct3_holds fc nb hnb))

/-! #### The component's structural facts: index-set agreement, the ceiling, growth

With the gate decided the plumbing every consumer needs can be built. All four statements below are
transcriptions of the already-landed `mintPotential` siblings, and the transcription is exact except
in one place: `selfGuardPotential` does not take a `Branch`, so the growth lemma needs only the
ordering half of `mintPotential_le_of_grow`'s hypothesis and no branch-monotonicity fact at all. -/

/-- **Index-set agreement**, the anti-drift guarantee. Mirrors `mem_freshLabelRules` and
`mem_freshTimeRules`: if the list is ever widened, every consumer that reads this lemma breaks
loudly rather than silently counting extra columns. -/
theorem mem_selfGuardRules {r : TableauRule} :
    r ∈ selfGuardRules ↔ (r = TableauRule.untlNeg ∨ r = TableauRule.snceNeg) := by
  cases r <;> simp [selfGuardRules]

/-- **`selfGuardPotential ≤ 2 · |U|`**, immediately, for every ordering and every renaming: the
filter cannot exceed its index set, and the index set is a product with a two-element left factor.

The coefficient is the index set's width and nothing else, which is the point of choosing a second
ledger over a widening: `mintPotential`'s ceiling is `8 · |U|` and stays `8 · |U|`. Transcribed from
`mintPotential_le_eight_mul`. -/
theorem selfGuardPotential_le_two_mul (U : Finset SignedFormula)
    (σ : SignedFormula → SignedFormula) (ord : TimeOrdering) :
    selfGuardPotential U σ ord ≤ 2 * U.card := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, selfGuardRules_card]

/-- A non-empty reach transports along any map that carries its members into the target reach.

The one shared shape behind both growth and both transport arguments below: `selfGuardDischarged`
reads `!(reach).isEmpty`, so every preservation statement about it is "some member survives", and
the member's identity is never used. Stating it once keeps the four rule cases below to a single
line each. -/
theorem not_isEmpty_transport (φ : TimeIndex → TimeIndex) {l l' : List TimeIndex}
    (h : ∀ x ∈ l, φ x ∈ l') (hl : (!l.isEmpty) = true) : (!l'.isEmpty) = true := by
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff] at hl ⊢
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hl
  exact List.ne_nil_of_mem (h x hx)

/-- **A discharged self-guard stays discharged as the ordering grows.** Consumes
`TimeOrdering.futureOf_mono` / `TimeOrdering.pastOf_mono`.

The hypothesis is supplied at every call site by the mint arms themselves: `addFuture` and `addPast`
only cons onto `ord.constraints`, so the pre-step constraint list is literally a sublist of the
post-step one. The catch-all rules close by `rfl`, since their column is `true` at every ordering —
the polarity choice `selfGuardDischarged`'s docstring explains. -/
theorem selfGuardDischarged_le_of_grow {ord ord' : TimeOrdering}
    (hord : ∀ q ∈ ord.constraints, q ∈ ord'.constraints) (r : TableauRule) (sf : SignedFormula)
    (h : selfGuardDischarged r sf ord = true) : selfGuardDischarged r sf ord' = true := by
  cases r <;> simp only [selfGuardDischarged] at h ⊢ <;>
    first
      | rfl
      | exact not_isEmpty_transport id (fun x hx => TimeOrdering.futureOf_mono hord _ x hx) h
      | exact not_isEmpty_transport id (fun x hx => TimeOrdering.pastOf_mono hord _ x hx) h

/-- **An ordinary step does not increase the self-guard potential.** The ordering grows, so
`selfGuardDischarged` can only turn on; contrapositively the after-`false` set is a *subset* of the
before-`false` set inside the same index set, and no injection is needed.

Transcribed from `mintPotential_le_of_grow`, minus its branch-growth hypothesis: the component does
not take a `Branch`, so the branch half has no analogue and no call site has to supply one. This
covers `.extended`, `.split`, and the ordered split's first two arms — every step that keeps `σ`. -/
theorem selfGuardPotential_le_of_grow {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {ord ord' : TimeOrdering}
    (hord : ∀ q ∈ ord.constraints, q ∈ ord'.constraints) :
    selfGuardPotential U σ ord' ≤ selfGuardPotential U σ ord := by
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rcases hd : selfGuardDischarged p.1 (σ p.2) ord with _ | _
  · rfl
  · rw [selfGuardDischarged_le_of_grow hord p.1 (σ p.2) hd] at hp
    exact absurd hp.2 (by simp)

/-! #### Preservation across the identification arm — Constraint (F), discharged

The crux. The ordered split's arm 3 is the one step at which the whole design has to be checked
rather than argued, because it is the step every `knownTimes.card`-affine candidate dies at: a
self-guarded mint raises the known-time count and the identification arm lowers it, so no sign of
coefficient satisfies both. `selfGuardPotential` is not affine in that count — it is not a function
of the branch at all — and what has to be shown instead is that the arm does not *raise* it.

It does not, and with room to spare: the arm's renaming is post-composed onto σ, no constraint is
dropped at an incomparable trigger (`identifyTime_no_collapse`), and reachability transports edge by
edge (`futureOf_transport` / `pastOf_transport`). So the discharged set only grows and the uncured
count only falls. **This is Constraint (F) discharged with equality-or-better**, and it is what
separates Candidate 2 from every candidate the constraint kills.

The `incomparableB ord (t₁, t₂)` side condition is not a new hypothesis. It is available at the
consuming site from `firstIncomparablePair_spec`, whose last two conjuncts are literally
`incomparableB`'s two clauses, and at the engine's own orientation from
`incomparableB_of_firstIncomparablePair_oriented`. `IrreflOrd` is likewise the run invariant's own
first conjunct — and it is *necessary*, not convenient: `witnessPresent_identifyTime_unconditional_false`
(register entry 5) refutes the `IrreflOrd`-free form for the sibling predicate, and the reason
carries over verbatim, since `TimeOrdering.identifyTime` drops a pre-existing self-loop whose two
endpoints rename together. -/

/-- **A discharged self-guard survives the identification arm, renamed.**

Three steps, exactly the ones the design was fixed on. (1) No constraint is dropped:
`identifyTime_no_collapse` gives `rho t₂ t₁ a ≠ rho t₂ t₁ b` for every constraint, and
`TimeOrdering.identifyTime`'s `filterMap` discards only when the two components collapse. (2)
Non-emptiness transports: `futureOf_transport` / `pastOf_transport` carry a witnessing member of the
reach to a member of the renamed reach, length-preservingly, so the `100`-step fuel bound is
re-met at the same length. (3) The column index lines up, because `rhoSF` acts on the label's time
by exactly the `rho` the reach transport is stated at. -/
theorem selfGuardDischarged_identifyTime {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (hinc : incomparableB ord (t₁, t₂) = true) (hnsl : IrreflOrd ord)
    (r : TableauRule) (sf : SignedFormula) (h : selfGuardDischarged r sf ord = true) :
    selfGuardDischarged r (rhoSF t₂ t₁ sf) (ord.identifyTime t₂ t₁) = true := by
  cases r <;> simp only [selfGuardDischarged, rhoSF] at h ⊢ <;>
    first
      | rfl
      | exact not_isEmpty_transport (rho t₂ t₁)
          (fun x hx => futureOf_transport ord t₁ t₂ hinc hnsl _ x hx) h
      | exact not_isEmpty_transport (rho t₂ t₁)
          (fun x hx => pastOf_transport ord t₁ t₂ hinc hnsl _ x hx) h

/-- **The identification arm does not increase the self-guard potential.**

`Finset.card_le_card` over the previous lemma: the filter's `true`-set only grows, so the
`false`-set only shrinks, inside an index set that does not move. No injection from the after-set
into the before-set is required, and none is available — `rhoSF t₂ t₁` is not injective on `U`.
This is the same skeleton as `mintPotential_identifyTime`, one lemma deeper.

Because the renaming is *post-composed* onto the parameter, the statement applies unchanged at a
second, third or `n`-th identification along the same run. -/
theorem selfGuardPotential_identifyTime {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (hinc : incomparableB ord (t₁, t₂) = true) (hnsl : IrreflOrd ord) :
    selfGuardPotential U (fun x => rhoSF t₂ t₁ (σ x)) (ord.identifyTime t₂ t₁)
      ≤ selfGuardPotential U σ ord := by
  refine Finset.card_le_card ?_
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rcases hd : selfGuardDischarged p.1 (σ p.2) ord with _ | _
  · rfl
  · rw [selfGuardDischarged_identifyTime hinc hnsl p.1 (σ p.2) hd] at hp
    exact absurd hp.2 (by simp)

/-- **…at the engine's own orientation.** `selfGuardPotential_identifyTime` read at
`(min t₁ t₂, max t₁ t₂)`, which is the merge arm 3 actually performs.

One fact deeper and nothing else: `incomparableB_of_firstIncomparablePair_oriented` supplies the
side condition at the flipped pair, via `incomparableB_symm`. The two statements are otherwise
definitionally the same, which is the concrete payoff of having stated the transport stack in
`src` / `tgt` rather than in the trigger's own coordinates. -/
theorem selfGuardPotential_identifyOriented {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (htrig : firstIncomparablePair b ord = some (t₁, t₂)) (hirr : IrreflOrd ord) :
    selfGuardPotential U
        (fun x => rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 (σ x))
        (identifyOriented b ord t₁ t₂).2
      ≤ selfGuardPotential U σ ord :=
  selfGuardPotential_identifyTime (incomparableB_of_firstIncomparablePair_oriented htrig) hirr

/-! #### The σ-hit obligation, discharged rather than carried

Register entry 14 instructed that the σ-hit residual be *carried structurally* rather than
discharged, and Phase 1's gate is why: at the unoriented arm it is false, so carrying it was the
only honest option. `SigmaTimeStable` changes that. The obligation asks for some `sf ∈ U` whose
σ-image sits at the trigger's time; the trigger is a branch formula; confinement puts it in `U`; and
σ-time-stability says σ does not move it off its own time. Three facts, one line, no search.

This is the single place where the reorientation pays off in the measure's own terms, and it is
worth being precise about what it costs. Nothing is assumed here that a consumer does not already
have: `∀ x ∈ b, x ∈ U` is `MintPaysForTime`'s own second hypothesis, unchanged since the predicate
was written, and `SigmaTimeStable σ b` is discharged at the identification arm by
`sigmaTimeStable_identifyOriented`. -/

/-- **The σ-hit obligation, discharged from confinement and σ-time-stability.**

The trigger witnesses its own hit. `mintPotential_lt_of_mint`'s formula-level obligation is *not*
available this way — it needs `σ sf = g` on the nose, and `rhoSF`'s image genuinely omits formulas —
but the time-level obligation `selfGuardPotential` reads is, and that difference is the whole reason
the fourth component is indexed by time rather than by formula. -/
theorem sigma_time_hit_of_sigmaTimeStable {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} (hconf : ∀ x ∈ b, x ∈ U)
    (hst : SigmaTimeStable σ b) {sf : SignedFormula} (hsf : sf ∈ b) :
    ∃ x ∈ U, (σ x).label.time = sf.label.time :=
  ⟨sf, hconf sf hsf, hst sf hsf⟩

/-- **`SigmaTimeStable` at a single renaming is exactly "the branch has lost the retired index".**

An `iff`, so it can be used in both directions: to *discharge* stability from a branch fact, and to
*read off* a branch fact from stability. `sigmaTimeStable_identifyOriented` is the forward direction
instantiated at the arm's own post-state; this is the general statement behind it. -/
theorem sigmaTimeStable_rhoSF_iff {src tgt : TimeIndex} {b : Branch} (h : tgt ≠ src) :
    SigmaTimeStable (rhoSF src tgt) b ↔ ∀ x ∈ b, x.label.time ≠ src := by
  constructor
  · intro hst x hx hc
    exact rhoSF_time_ne_src h x ((hst x hx).trans hc)
  · intro hne x hx
    exact rhoSF_time_eq_of_ne_src (hne x hx)

/-- **…and a branch every one of whose times is above the retired index is stable.**

The form the run-level argument consumes. Under the oriented arm the retired index is strictly below
the post-arm `nextTime` (`retired_lt_nextTime_oriented`) and `nextTime` is non-decreasing along the
run (`nextTime_monotone_along_run`), so every time the run mints after the arm is strictly above
every index the arm retired — which is exactly this hypothesis, and is why growth cannot break
stability. -/
theorem sigmaTimeStable_rhoSF_of_lt {src tgt : TimeIndex} {b : Branch} (h : tgt ≠ src)
    (hlt : ∀ x ∈ b, src < x.label.time) : SigmaTimeStable (rhoSF src tgt) b :=
  (sigmaTimeStable_rhoSF_iff h).mpr (fun x hx => Ne.symm (Nat.ne_of_lt (hlt x hx)))

/-! #### The discharge lemmas: `untlNeg` and `snceNeg` pay for their own mints

Each self-guarded rule fires only when its own reach is empty and returns an ordering that makes
that reach non-empty. So its trigger's column flips uncured → cured at exactly the step it mints,
and by `selfGuardPotential_le_of_grow` no other column flips the other way — the edge is *added*,
never removed. One column strictly lost from a set that only shrinks is a strict decrease.

**Research risk R2 is dissolved rather than discharged, and that is a finding worth recording.**
The plan asked for a prior lemma placing the freshly minted time outside the ordering's endpoints,
on the worry that the mint might create a new *uncured* column and cancel the flip. It cannot:
`selfGuardPotential` does not take a `Branch`, the index set `selfGuardRules ×ˢ U` is fixed, and a
mint step changes neither `U` nor `σ`. So the freshly minted formula has no column at all unless it
already had one, and the column indices do not move. The `OrdTimesKnown`-plus-`nextTime > maxTime`
argument the plan reserved for this is not needed, and reaching for it would have been reaching for
a fact about a quantity the component deliberately does not read.

**Research risk R3 is resolved by measurement, not by assumption.** The `snceNeg` mirror below is
exact: same guard shape read off the arm's own `if` rather than off its comment
(`pastTimes.isEmpty && timeCount > 0 && timeCount < 4`), same one-edge `newOrd`
(`timeOrd.addPast l.time freshTime`), and `addPast ord t tf = (tf, t) :: ord.constraints`, so the
curing edge runs *into* the trigger's time and `mem_pastOf_of_mem_constraints` closes it. The proof
is a transcription with `futureOf → pastOf` and nothing else changed. -/

/-- **Adding a forward edge out of an uncured time strictly drops the potential.**

Stated at the ordering operation rather than at the rule, because that is where the content is: the
rule's contribution is `newOrd = ord.addFuture l.time freshTime` and its guard
`(ord.futureOf l.time).isEmpty`, both of which appear here as hypotheses and are supplied at the
engine level by `applyRule_untlNeg_active_ord`.

The σ-hit hypothesis is `hhit`, and it is **not** vacuous: `sigma_time_hit_of_sigmaTimeStable`
discharges it from confinement plus σ-time-stability, and `selfGuardPotential_lt_at_orientedGate`
decides the whole conclusion at a concrete configuration. At the unoriented arm it is false, which
is what `mintPaysForTimeAt_reuse_false` records. -/
theorem selfGuardPotential_lt_of_addFuture {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {ord : TimeOrdering} {t tf : TimeIndex}
    (hempty : (ord.futureOf t).isEmpty = true)
    {sf : SignedFormula} (hsf : sf ∈ U) (hhit : (σ sf).label.time = t) :
    selfGuardPotential U σ (ord.addFuture t tf) < selfGuardPotential U σ ord := by
  have hgrow : ∀ q ∈ ord.constraints, q ∈ (ord.addFuture t tf).constraints := by
    intro q hq; simp only [TimeOrdering.addFuture, List.mem_cons]; exact Or.inr hq
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rcases hd : selfGuardDischarged p.1 (σ p.2) ord with _ | _
    · rfl
    · rw [selfGuardDischarged_le_of_grow hgrow p.1 (σ p.2) hd] at hp
      exact absurd hp.2 (by simp)
  · intro hsub
    have hmemR : TableauRule.untlNeg ∈ selfGuardRules := by decide
    have hcol : ((TableauRule.untlNeg, sf) : TableauRule × SignedFormula)
        ∈ (selfGuardRules ×ˢ U).filter
          (fun p => selfGuardDischarged p.1 (σ p.2) ord = false) := by
      simp only [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hmemR, hsf⟩, ?_⟩
      simp only [selfGuardDischarged, hhit, hempty]
      rfl
    have hnil : ((ord.addFuture t tf).futureOf t) ≠ [] :=
      List.ne_nil_of_mem
        (mem_futureOf_of_mem_constraints _ t tf (by simp [TimeOrdering.addFuture]))
    have hcured : selfGuardDischarged TableauRule.untlNeg (σ sf) (ord.addFuture t tf) = true := by
      simp only [selfGuardDischarged, hhit, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      exact hnil
    have hfalse := (Finset.mem_filter.mp (hsub hcol)).2
    rw [hcured] at hfalse
    exact absurd hfalse (by simp)

/-- **The exact past mirror.** `addPast ord t tf` is `(tf, t) :: ord.constraints`, so the new edge
runs *into* `t` and `mem_pastOf_of_mem_constraints` puts `tf` in `t`'s past. Transcription of the
lemma above with `futureOf → pastOf`, `addFuture → addPast`, `untlNeg → snceNeg`; nothing else
differs, which is the measurement research risk R3 asked for. -/
theorem selfGuardPotential_lt_of_addPast {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {ord : TimeOrdering} {t tf : TimeIndex}
    (hempty : (ord.pastOf t).isEmpty = true)
    {sf : SignedFormula} (hsf : sf ∈ U) (hhit : (σ sf).label.time = t) :
    selfGuardPotential U σ (ord.addPast t tf) < selfGuardPotential U σ ord := by
  have hgrow : ∀ q ∈ ord.constraints, q ∈ (ord.addPast t tf).constraints := by
    intro q hq; simp only [TimeOrdering.addPast, List.mem_cons]; exact Or.inr hq
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rcases hd : selfGuardDischarged p.1 (σ p.2) ord with _ | _
    · rfl
    · rw [selfGuardDischarged_le_of_grow hgrow p.1 (σ p.2) hd] at hp
      exact absurd hp.2 (by simp)
  · intro hsub
    have hmemR : TableauRule.snceNeg ∈ selfGuardRules := by decide
    have hcol : ((TableauRule.snceNeg, sf) : TableauRule × SignedFormula)
        ∈ (selfGuardRules ×ˢ U).filter
          (fun p => selfGuardDischarged p.1 (σ p.2) ord = false) := by
      simp only [Finset.mem_filter]
      refine ⟨Finset.mem_product.mpr ⟨hmemR, hsf⟩, ?_⟩
      simp only [selfGuardDischarged, hhit, hempty]
      rfl
    have hnil : ((ord.addPast t tf).pastOf t) ≠ [] :=
      List.ne_nil_of_mem
        (mem_pastOf_of_mem_constraints _ tf t (by simp [TimeOrdering.addPast]))
    have hcured : selfGuardDischarged TableauRule.snceNeg (σ sf) (ord.addPast t tf) = true := by
      simp only [selfGuardDischarged, hhit, Bool.not_eq_true', List.isEmpty_eq_false_iff]
      exact hnil
    have hfalse := (Finset.mem_filter.mp (hsub hcol)).2
    rw [hcured] at hfalse
    exact absurd hfalse (by simp)

/-- **The `untlNeg` ACTIVE arm's ordering, read off the engine.** The arm returns
`timeOrd.addFuture l.time branch.nextTime` and nothing else touches the ordering component, so the
discharge lemma's `addFuture` hypothesis is the engine's own output rather than a modelling choice.

The guard is transcribed exactly as the arm's `if` writes it — `futureTimes.isEmpty &&
timeOrd.timeCount > 0 && timeOrd.timeCount < 4` — because the arm's *comment* and the arm's `if`
disagreed historically and the `if` is what fires. -/
theorem applyRule_untlNeg_active_ord {sign : Sign} {φ : Formula} {l : Label}
    {b : Branch} {ord : TimeOrdering} {e g : Formula}
    (hsign : sign = Sign.neg) (hform : asUntil? φ = some (e, g))
    (hguard : ((ord.futureOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true) :
    (applyRule TableauRule.untlNeg ⟨sign, φ, l⟩ b ord).2 = ord.addFuture l.time b.nextTime := by
  subst hsign
  simp only [applyRule, hform, hguard, if_true]

/-- **The `snceNeg` ACTIVE arm's ordering, read off the engine.** The past mirror, same shape,
`addPast` in place of `addFuture`. -/
theorem applyRule_snceNeg_active_ord {sign : Sign} {φ : Formula} {l : Label}
    {b : Branch} {ord : TimeOrdering} {e g : Formula}
    (hsign : sign = Sign.neg) (hform : asSince? φ = some (e, g))
    (hguard : ((ord.pastOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true) :
    (applyRule TableauRule.snceNeg ⟨sign, φ, l⟩ b ord).2 = ord.addPast l.time b.nextTime := by
  subst hsign
  simp only [applyRule, hform, hguard, if_true]

/-- **The `untlNeg` discharge lemma, assembled.** At an ACTIVE `untlNeg` firing on a branch formula,
under confinement and σ-time-stability, the self-guard potential strictly drops.

Every hypothesis here is one a consumer already has. `hconf` is `MintPaysForTime`'s own second
hypothesis; `hst` is `MintPaysForTimeStable`'s added one, discharged at the identification arm by
`sigmaTimeStable_identifyOriented`; `hguard` is the arm's own firing condition, so it is available
wherever the arm fired; and `hsf` says the trigger is on the branch, which every `pick` stage
supplies. Nothing is assumed about the frame class, `Tmax`, or the shape of `U`. -/
theorem selfGuardPotential_lt_of_untlNeg {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {φ : Formula} {l : Label} {e g : Formula}
    (hconf : ∀ x ∈ b, x ∈ U) (hst : SigmaTimeStable σ b)
    (hsf : (⟨Sign.neg, φ, l⟩ : SignedFormula) ∈ b) (hform : asUntil? φ = some (e, g))
    (hguard : ((ord.futureOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true) :
    selfGuardPotential U σ (applyRule TableauRule.untlNeg ⟨Sign.neg, φ, l⟩ b ord).2
      < selfGuardPotential U σ ord := by
  obtain ⟨x, hxU, hxt⟩ := sigma_time_hit_of_sigmaTimeStable hconf hst hsf
  rw [applyRule_untlNeg_active_ord rfl hform hguard]
  refine selfGuardPotential_lt_of_addFuture ?_ hxU hxt
  simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hguard).1).1

/-- **The `snceNeg` discharge lemma, assembled.** The exact past mirror of the lemma above. -/
theorem selfGuardPotential_lt_of_snceNeg {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {φ : Formula} {l : Label} {e g : Formula}
    (hconf : ∀ x ∈ b, x ∈ U) (hst : SigmaTimeStable σ b)
    (hsf : (⟨Sign.neg, φ, l⟩ : SignedFormula) ∈ b) (hform : asSince? φ = some (e, g))
    (hguard : ((ord.pastOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true) :
    selfGuardPotential U σ (applyRule TableauRule.snceNeg ⟨Sign.neg, φ, l⟩ b ord).2
      < selfGuardPotential U σ ord := by
  obtain ⟨x, hxU, hxt⟩ := sigma_time_hit_of_sigmaTimeStable hconf hst hsf
  rw [applyRule_snceNeg_active_ord rfl hform hguard]
  refine selfGuardPotential_lt_of_addPast ?_ hxU hxt
  simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hguard).1).1

/-! #### The run-level form of the σ hypothesis, and the no-leak confirmation

`SigmaTimeStable σ b` is stated per *formula*, which is the weakest form the discharge lemmas need
and therefore the right one to put in the predicate. It is **not** the right form to carry along a
run, and the reason is worth stating rather than discovering later: the identification arm replaces
branch formulas by their renamed images, and a renamed image need not have been on the branch
before, so a per-formula hypothesis about the old branch says nothing about it.

The time-level strengthening `SigmaTimeFixed` closes that gap. It quantifies over *every* formula
sitting at a branch time rather than over branch formulas, which is exactly the extra reach the
arm's relabelling needs, and it implies the per-formula form immediately. Everything else about it
is the same: `id` satisfies it, the arm preserves it, and it is discharged rather than assumed.

**What is confirmed here, and what is left named.** The arm — the only step that changes σ — is
handled in full. Additive steps do not change σ at all, so the only way one can break the invariant
is by minting a time σ retires; `SigmaFixesFrom` plus `sigmaTimeFixed_grow_of_fixesFrom` is the
supply for that, and the fact that closes it is the reorientation's own
(`retired_lt_nextTime_oriented`: every index the arm retires is strictly below the `nextTime` at
which the run afterwards mints, and `nextTime_monotone_along_run` keeps it there). Assembling those
into a single run-level invariant is measure-level work and belongs with the step lemmas, not here;
it is named as an obligation rather than assumed. -/

/-- **The time-level form of the σ hypothesis.** Every formula sitting at a time the branch knows
keeps its time under `σ`.

Stronger than `SigmaTimeStable` in exactly one respect — it reaches formulas that are not on the
branch but sit at a time that is — and that is the respect the identification arm needs, since the
arm puts renamed formulas on the branch that were not there before. -/
def SigmaTimeFixed (σ : SignedFormula → SignedFormula) (b : Branch) : Prop :=
  ∀ x : SignedFormula, x.label.time ∈ b.knownTimes → (σ x).label.time = x.label.time

/-- The time-level form implies the per-formula form the predicate carries. One line: a branch
formula's time is a branch time. -/
theorem sigmaTimeStable_of_sigmaTimeFixed {σ : SignedFormula → SignedFormula} {b : Branch}
    (h : SigmaTimeFixed σ b) : SigmaTimeStable σ b :=
  fun x hx => h x (mem_knownTimes_of_mem hx)

/-- **The seed satisfies it for free.** `σ` is `id` before the first ordered split, so the run
starts inside the invariant and no caller supplies anything. -/
theorem sigmaTimeFixed_id (b : Branch) : SigmaTimeFixed id b := fun _ _ => rfl

/-- **The identification arm preserves it.** The one step that changes `σ`, handled in full.

Two facts and nothing else. The post-arm branch's times are a subset of the pre-arm branch's
(`knownTimes_identifyTime_subset`, which is why the surviving numeral has to be a known time — the
same side condition `universeClosedAt_identify_at_trigger_oriented` carries, and no more), so the
old invariant applies to every time the new branch knows; and the post-arm branch has lost the
retired index, so the arm's own `rhoSF` is the identity on every time still present.

Under the *unoriented* arm this lemma is equally true — it is not what the reorientation buys. What
the reorientation buys is that the retired index stays retired, which is
`retired_lt_nextTime_oriented`'s business, not this one's. -/
theorem sigmaTimeFixed_identifyOriented {σ : SignedFormula → SignedFormula} {b : Branch}
    {ord : TimeOrdering} {t₁ t₂ : TimeIndex} (hne : t₁ ≠ t₂)
    (hmax : (identifyOrient t₁ t₂).2 ∈ b.knownTimes) (h : SigmaTimeFixed σ b) :
    SigmaTimeFixed
      (fun x => rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 (σ x))
      (identifyOriented b ord t₁ t₂).1 := by
  intro x hx
  simp only [identifyOriented] at hx
  have hb : x.label.time ∈ b.knownTimes := knownTimes_identifyTime_subset hmax _ hx
  have hnesrc : x.label.time ≠ (identifyOrient t₁ t₂).1 := by
    intro hc
    exact src_not_mem_knownTimes_identifyTime b _ _ (identifyOrient_ne hne) (hc ▸ hx)
  have hfix := h x hb
  exact (rhoSF_time_eq_of_ne_src (by rw [hfix]; exact hnesrc)).trans hfix

/-- **σ retires nothing at or above `n`.** The provenance fact about the accumulated renaming that
additive steps need: a freshly minted time is safe as soon as it is at least `n`.

Stated as a property of `σ` rather than as a claim about how `σ` was built, so that it composes
(`sigmaFixesFrom_comp`) and weakens (`sigmaFixesFrom_mono`) without a provenance predicate. -/
def SigmaFixesFrom (σ : SignedFormula → SignedFormula) (n : TimeIndex) : Prop :=
  ∀ x : SignedFormula, n ≤ x.label.time → (σ x).label.time = x.label.time

/-- `id` retires nothing, at any watermark. -/
theorem sigmaFixesFrom_id (n : TimeIndex) : SigmaFixesFrom id n := fun _ _ => rfl

/-- A single renaming retires nothing above the index it retires. -/
theorem sigmaFixesFrom_rhoSF {src tgt n : TimeIndex} (h : src < n) :
    SigmaFixesFrom (rhoSF src tgt) n :=
  fun x hx => rhoSF_time_eq_of_ne_src (Nat.ne_of_gt (Nat.lt_of_lt_of_le h hx))

/-- …and post-composing another one keeps the watermark, provided the new retired index is below
it. This is the induction step of the run-level provenance argument, and it is where
`retired_lt_nextTime_oriented` is consumed. -/
theorem sigmaFixesFrom_comp {σ : SignedFormula → SignedFormula} {src tgt n : TimeIndex}
    (hσ : SigmaFixesFrom σ n) (h : src < n) :
    SigmaFixesFrom (fun x => rhoSF src tgt (σ x)) n := by
  intro x hx
  have hfix := hσ x hx
  exact (rhoSF_time_eq_of_ne_src
    (by rw [hfix]; exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h hx))).trans hfix

/-- The watermark may be raised freely. `nextTime_monotone_along_run` is what raises it. -/
theorem sigmaFixesFrom_mono {σ : SignedFormula → SignedFormula} {n m : TimeIndex}
    (h : SigmaFixesFrom σ n) (hle : n ≤ m) : SigmaFixesFrom σ m :=
  fun x hx => h x (le_trans hle hx)

/-- **Growth preserves the invariant, given the obligation on the new times.** The obligation is
stated rather than assumed away: every time the successor knows is either one the predecessor knew,
or one `σ` fixes. -/
theorem sigmaTimeFixed_grow {σ : SignedFormula → SignedFormula} {b b' : Branch}
    (h : SigmaTimeFixed σ b)
    (hnew : ∀ t ∈ b'.knownTimes, t ∈ b.knownTimes ∨ ∀ x : SignedFormula, x.label.time = t →
      (σ x).label.time = x.label.time) :
    SigmaTimeFixed σ b' := by
  intro x hx
  rcases hnew x.label.time hx with hb | hfix
  · exact h x hb
  · exact hfix x rfl

/-- **…and the form the run-level argument actually uses.** The new-time obligation is discharged by
a watermark: a successor's times are the predecessor's plus fresh ones, and the fresh ones are at
least `b.nextTime`, which is strictly above every index the run has retired. -/
theorem sigmaTimeFixed_grow_of_fixesFrom {σ : SignedFormula → SignedFormula} {b b' : Branch}
    {n : TimeIndex} (h : SigmaTimeFixed σ b) (hfix : SigmaFixesFrom σ n)
    (hnew : ∀ t ∈ b'.knownTimes, t ∈ b.knownTimes ∨ n ≤ t) : SigmaTimeFixed σ b' := by
  refine sigmaTimeFixed_grow h (fun t ht => ?_)
  rcases hnew t ht with hb | hle
  · exact Or.inl hb
  · exact Or.inr (fun x hxt => hfix x (hxt ▸ hle))

/-- **The no-leak confirmation.** Three conjuncts, and together they are the whole claim that the
repair costs no consumer a hypothesis.

*The direction.* Conjunct 1: `MintPaysForTimeStable` is **weaker** than `MintPaysForTime` — a
disjunct was added and a hypothesis was added, and nothing was removed — so every terminus currently
carrying `MintPaysForTime` as a residual hypothesis can be restated against the repaired predicate
and the restatement is a **strengthening**. This is the `universeClosedAt_of_universeClosed` idiom
(`MintBound.lean` section D1) and the `ordTimesLeMaxTime_of_ordTimesKnown` idiom (section A3), used
here for the third time in this file. Saying this in words is not a formality: register entry 7
exists because a "simplification" that was secretly a weakening was once mistaken for a repair.

*The added hypothesis is discharged, not assumed.* Conjunct 2: the run starts inside it, since `σ`
is `id` before the first ordered split. Conjunct 3: the identification arm — the only step that
changes `σ` — preserves it, needing exactly the side condition
`universeClosedAt_identify_at_trigger_oriented` already carries and nothing more.

*What is named rather than closed.* Additive steps leave `σ` alone, so the only remaining way to
leave the invariant is to mint a time `σ` retires. `sigmaTimeFixed_grow_of_fixesFrom` reduces that
to a watermark, and `retired_lt_nextTime_oriented` plus `nextTime_monotone_along_run` supply the
watermark; assembling them into a single quantified run invariant is measure-level work and is
carried as a named obligation of the step lemmas, not discharged here.

*The only other cost is a coefficient.* A fourth component forces `mintPathBound` / `mintAwareFuel`
to absorb `2·(Tmax²+1)·2·|U|`. That is an arithmetic enlargement of exactly the kind register entry
8 already records for `splitAwareFuel_le_mintAwareFuel` — not a new assumption on any caller, and
not a change to any consuming terminus's hypothesis list. -/
theorem mintPaysForTimeStable_no_leak {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat} :
    (MintPaysForTime fc U Tmax → MintPaysForTimeStable fc U Tmax) ∧
      (∀ b : Branch, SigmaTimeFixed id b) ∧
      (∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
          (t₁ t₂ : TimeIndex), t₁ ≠ t₂ → (identifyOrient t₁ t₂).2 ∈ b.knownTimes →
        SigmaTimeFixed σ b →
        SigmaTimeFixed
          (fun x => rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 (σ x))
          (identifyOriented b ord t₁ t₂).1) :=
  ⟨mintPaysForTimeStable_of_mintPaysForTime, sigmaTimeFixed_id,
   fun _ _ _ _ _ hne hmax h => sigmaTimeFixed_identifyOriented hne hmax h⟩

/-! #### The four-component measure

`budgetPotential` is byte-unchanged; this is a new declaration alongside it, additive in the literal
sense — the original plus one weighted summand.

**Two things had to change from the plan-time design, and both are findings rather than choices.**

*The state's budget clause is the mint budget **plus** the fourth component.* A self-guarded mint
necessarily raises `mintTimeBudget`: it adds a time to `knownTimes` and leaves `mintPotential` alone,
because `untlNeg` and `snceNeg` are not in `freshLabelRules`. So `BudgetState` cannot survive the very
step the fourth component exists to pay for, and no weight fixes that — the failure is in the state
predicate, not in the measure. `BudgetStateAt` carries `mintTimeBudget + selfGuardPotential ≤ Tmax`
instead, and the arithmetic works because the mint spends exactly one unit of the fourth component
to buy the one unit of mint budget it consumes. That is the component *funding* the budget rather
than sitting beside it, and it is why the repaired predicate's third disjunct has to be a **pair**.

*The third disjunct is a pair, mirroring disjunct 2.* Disjunct 2 pairs a `mintPotential` drop with a
`mintTimeBudget` non-increase; disjunct 3 pairs a `selfGuardPotential` drop with a **combined**-budget
non-increase. Without the second conjunct `extensionAllowance` is unbounded above at the step — it
carries a factor of `|U|` per unit of mint budget — and the measure does not fall. This is why
`MintPaysForTimeAt → MintPaysForTimeStable` is unavailable and is not claimed.

*The weight is `2·(Tmax² + 1) + |U|`, not `2·(Tmax² + 1)`.* The extra `|U|` is exactly what pays for
`extensionAllowance`'s rise across a step that spends combined budget. The plan-time figure was read
off `splitOrderedRank`'s rise alone and did not account for the allowance; the correction is recorded
here rather than absorbed.

Neither change touches a landed declaration, and neither is a new hypothesis on any caller:
`BudgetStateAt`'s clause is a *strengthening* of `BudgetState`'s, discharged at the seed by choosing
`Tmax` with the slack `selfGuardPotential_le_two_mul` bounds at `2·|U|` — a figure enlargement of
exactly the kind register entry 8 records. -/

/-- **The carried state, at the four-component measure.** `BudgetState`'s three clauses with the
third replaced by the *combined* budget: the mint budget plus the self-guard potential.

The combination is load-bearing, not cosmetic. A self-guarded mint raises `mintTimeBudget` by one
and lowers `selfGuardPotential` by at least one, so the sum is non-increasing at exactly the step
the plain clause fails at. Measured at the oriented gate: `26 + 3 = 29` before, `27 + 1 = 28` after
(`orientedGate_disjunct3_holds`). -/
def BudgetStateAt (U : Finset SignedFormula) (Tmax : Nat)
    (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering) : Prop :=
  RunInvariant b ord ∧ (∀ x ∈ b, x ∈ U) ∧
    mintTimeBudget U σ b ord + selfGuardPotential U σ ord ≤ Tmax ∧
    SigmaTimeFixed σ b ∧ SigmaFixesFrom σ b.nextTime
/-- **The four-component measure.** `budgetPotential` plus the self-guard coordinate at weight
`2·(Tmax² + 1) + |U|`.

The weight has to dominate everything a step that spends one unit of combined budget can add:
`(Tmax² + 1)` for the extra known time in `splitOrderedRank`, `Tmax²` for a full incomparable-pair
range (`incompPairs_card_le` at `knownTimes.card ≤ Tmax`), and `|U|` for `extensionAllowance`'s
per-budget-unit factor. `2·(Tmax² + 1) + |U|` clears all three with a unit to spare, which is why
the drop is by at least one however much the step mints. -/
def budgetPotentialAt (U : Finset SignedFormula) (Tmax : Nat)
    (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering) : Nat :=
  budgetPotential U Tmax σ b ord
    + (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord


/-- **Constraint (F), tested at the arm before the inequality is attempted.** The fourth component
does not rise at the ordered split's identification arm.

This is the plan's own gate on Phase 7 and it passes with equality-or-better:
`selfGuardPotential_identifyOriented` is exactly the statement, read at the arm's own
`(min t₁ t₂, max t₁ t₂)`. Had it failed, the phase would have been blocked rather than rescued by
re-weighting — the research shows re-weighting is unsatisfiable, since the mint-side rise scales
identically. -/
theorem selfGuardPotential_le_at_arm3 {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (htrig : firstIncomparablePair b ord = some (t₁, t₂)) (hirr : IrreflOrd ord) :
    selfGuardPotential U (fun x => rhoSF (min t₁ t₂) (max t₁ t₂) (σ x))
        (ord.identifyTime (min t₁ t₂) (max t₁ t₂))
      ≤ selfGuardPotential U σ ord :=
  selfGuardPotential_identifyOriented (b := b) htrig hirr


/-- **The measure drops at every arm of an ordered split, at the four-component measure.**

`budgetPotential_step_splitOrdered` re-proved, with exactly one additional input per arm — the
fourth component's non-increase, multiplied by the weight — and the state clause discharged from the
same inputs. Arms 1 and 2 get it from `selfGuardPotential_le_of_grow` (the arms only add an edge);
arm 3 gets it from `selfGuardPotential_le_at_arm3`. `hrk`, `hEmul` and `hEexp` are unchanged, which
is the plan's Scope Hypothesis for this phase confirmed rather than assumed.

No residual is consumed here: an ordered split does not mint, so the repaired predicate is not used
at all. -/
theorem budgetPotentialAt_step_splitOrdered {U : Finset SignedFormula} {Tmax : Nat}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {bs : List (Branch × TimeOrdering)}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hUcl : UniverseClosedAt fc U) (hst : BudgetStateAt U Tmax σ b ord)
    (hres : (expandOnceUnblocked b ord fc tr).1 = ExpansionResult.splitOrdered bs) :
    ∀ p ∈ bs, ∃ σ' : SignedFormula → SignedFormula, BudgetStateAt U Tmax σ' p.1 p.2 ∧
      budgetPotentialAt U Tmax σ' p.1 p.2 < budgetPotentialAt U Tmax σ b ord := by
  obtain ⟨hinv, hbU, hbud, hfix, hfrom⟩ := hst
  have hkT : b.knownTimes.toFinset.card ≤ Tmax := by
    simp only [mintTimeBudget] at hbud; omega
  have hcU : b.toFinset.card ≤ U.card := card_le_of_subset_universe hbU
  have hrank := expandOnceUnblocked_splitOrdered_rank_lt hkT hres
  have hinvs := (expandOnceUnblocked_runInvariant hinv).2 bs hres
  obtain ⟨t₁, t₂, htrig, rfl⟩ := expandOnceUnblocked_splitOrdered_shape hres
  intro p hp
  have hrk := hrank p hp
  have hinvp := hinvs p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · dsimp only at hrk hinvp ⊢
    have hm' : mintPotential U σ b (ord.addFuture t₁ t₂) ≤ mintPotential U σ b ord :=
      mintPotential_le_of_grow (fun _ hx => hx) (addFuture_constraints_mono ord t₁ t₂)
    have hI : mintTimeBudget U σ b (ord.addFuture t₁ t₂) ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ b (ord.addFuture t₁ t₂) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ b (ord.addFuture t₁ t₂)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hS1 : selfGuardPotential U σ (ord.addFuture t₁ t₂) ≤ selfGuardPotential U σ ord :=
      selfGuardPotential_le_of_grow (addFuture_constraints_mono ord t₁ t₂)
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ (ord.addFuture t₁ t₂)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS1
    refine ⟨σ, ⟨hinvp, hbU, by omega, hfix, hfrom⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · dsimp only at hrk hinvp ⊢
    have hm' : mintPotential U σ b (ord.addFuture t₂ t₁) ≤ mintPotential U σ b ord :=
      mintPotential_le_of_grow (fun _ hx => hx) (addFuture_constraints_mono ord t₂ t₁)
    have hI : mintTimeBudget U σ b (ord.addFuture t₂ t₁) ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ b (ord.addFuture t₂ t₁) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ b (ord.addFuture t₂ t₁)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hS2 : selfGuardPotential U σ (ord.addFuture t₂ t₁) ≤ selfGuardPotential U σ ord :=
      selfGuardPotential_le_of_grow (addFuture_constraints_mono ord t₂ t₁)
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ (ord.addFuture t₂ t₁)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS2
    refine ⟨σ, ⟨hinvp, hbU, by omega, hfix, hfrom⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · dsimp only at hrk hinvp ⊢
    have hk := knownTimes_card_lt_at_arm3_oriented (b := b) (ord := ord) htrig
    set s := min t₁ t₂ with hsdef
    set u := max t₁ t₂ with hudef
    have hm' : mintPotential U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
        (ord.identifyTime s u) ≤ mintPotential U σ b ord :=
      mintPotential_identifyTime_oriented htrig hinv.irreflOrd
    have hS3 : selfGuardPotential U (fun x => rhoSF s u (σ x)) (ord.identifyTime s u)
        ≤ selfGuardPotential U σ ord := selfGuardPotential_le_at_arm3 htrig hinv.irreflOrd
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U (fun x => rhoSF s u (σ x))
          (ord.identifyTime s u)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS3
    have hIU : ∀ x ∈ b.identifyTime s u, x ∈ U :=
      universeClosedAt_identify_at_trigger_oriented hUcl hbU htrig
    have hc'U : (b.identifyTime s u).toFinset.card ≤ U.card :=
      card_le_of_subset_universe hIU
    have hIsucc : mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
        (ord.identifyTime s u) + 1 ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : (mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) + 1) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hIsucc
    have hEexp : (mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) + 1) * U.card
        = mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) * U.card + U.card := by ring
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U (fun x => rhoSF s u (σ x))
          (b.identifyTime s u) (ord.identifyTime s u)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    obtain ⟨hmaxk, hmink, hminmax⟩ := firstIncomparablePair_spec_oriented htrig
    obtain ⟨hk1, hk2, hne21, -, -⟩ := firstIncomparablePair_spec htrig
    have hfix' : SigmaTimeFixed (fun x => rhoSF s u (σ x)) (b.identifyTime s u) :=
      sigmaTimeFixed_identifyOriented (ord := ord) (Ne.symm hne21) hmaxk hfix
    have hnextle : b.nextTime ≤ (b.identifyTime s u).nextTime :=
      nextTime_le_identifyTime_oriented b ord t₁ t₂
    have hfrom' : SigmaFixesFrom (fun x => rhoSF s u (σ x)) (b.identifyTime s u).nextTime :=
      sigmaFixesFrom_comp (sigmaFixesFrom_mono hfrom hnextle)
        (retired_lt_nextTime_oriented (b := b) ord hk1 hk2)
    refine ⟨fun x => rhoSF s u (σ x), ⟨hinvp, hIU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega


/-- **The measure drops at `.extended` and at every arm of a `.split`, at the four-component
measure.**

`budgetPotential_step_unordered` re-proved against `MintPaysForTimeStable`. Disjuncts 1 and 2 are the
landed cases with the fourth component along for the ride — it cannot rise, since an unordered step
only grows the ordering (`expandOnceUnblocked_ord_mono`). Disjunct 3 is the new case and the one the
whole task is about: the self-guarded mint pays for itself.

*The disjunct-3 arithmetic, in one line.* The combined-budget conjunct caps the rise in
`extensionAllowance` at `|U|` per unit of self-guard drop and the rise in `splitOrderedRank` at
`(Tmax² + 1)` per unit plus one incomparable-pair range; the weight `2·(Tmax² + 1) + |U|` pays for
all of it and leaves `(Tmax² + 1) − Tmax² = 1` over, and `hgrow` supplies one more. So the drop is by
at least two.

`hstab` is the repaired predicate's own added hypothesis, threaded through unchanged; it is
discharged at the seed by `sigmaTimeFixed_id` and at the identification arm by
`sigmaTimeFixed_identifyOriented`. -/
theorem budgetPotentialAt_step_unordered {U : Finset SignedFormula} {Tmax : Nat}
    {σ : SignedFormula → SignedFormula} {b nb : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hUcl : UniverseClosedAt fc U) (hmint : MintPaysForTimeStable fc U Tmax)
    (hst : BudgetStateAt U Tmax σ b ord)
    (hmem : nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1)
    (hgrow : b.toFinset.card < nb.toFinset.card) :
    BudgetStateAt U Tmax σ nb (expandOnceUnblocked b ord fc tr).2 ∧
      budgetPotentialAt U Tmax σ nb (expandOnceUnblocked b ord fc tr).2
        < budgetPotentialAt U Tmax σ b ord := by
  obtain ⟨hinv, hbU, hbud, hfix, hfrom⟩ := hst
  have hstab : SigmaTimeStable σ b := sigmaTimeStable_of_sigmaTimeFixed hfix
  have hfix' : SigmaTimeFixed σ nb :=
    sigmaTimeFixed_grow_of_fixesFrom hfix hfrom (fun t ht =>
      (unorderedSuccessor_time_dichotomy hinv.ordTimesKnown nb hmem t ht).imp id
        (fun h => le_of_eq h.symm))
  have hfrom' : SigmaFixesFrom σ nb.nextTime :=
    sigmaFixesFrom_mono hfrom (nextTime_monotone_along_run.1 nb hmem)
  have hnbU : ∀ x ∈ nb, x ∈ U := hUcl.1 b ord tr hbU nb hmem
  have hinv' : RunInvariant nb (expandOnceUnblocked b ord fc tr).2 :=
    (expandOnceUnblocked_runInvariant hinv).1 nb hmem
  have hm' : mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
      ≤ mintPotential U σ b ord := mintPotential_expandOnceUnblocked nb hmem
  have hs' : selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
      ≤ selfGuardPotential U σ ord := selfGuardPotential_le_of_grow expandOnceUnblocked_ord_mono
  have hcU : b.toFinset.card ≤ U.card := card_le_of_subset_universe hbU
  have hc'U : nb.toFinset.card ≤ U.card := card_le_of_subset_universe hnbU
  rcases hmint σ b ord tr hinv hbU hstab nb hmem with ⟨hk, hR⟩ | ⟨hI, hmlt⟩ | ⟨hbud3, hslt⟩
  · -- disjunct 1
    have hI : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
        ≤ mintTimeBudget U σ b ord := by simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hs'
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · -- disjunct 2: the landed case, with the fourth component along for the ride
    have hkT : nb.knownTimes.toFinset.card ≤ Tmax := by
      simp only [mintTimeBudget] at hI hbud; omega
    have hp' : (incompPairs nb (expandOnceUnblocked b ord fc tr).2).card ≤ Tmax * Tmax :=
      le_trans (incompPairs_card_le _ _) (Nat.mul_le_mul hkT hkT)
    have hEmul : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hs'
    have hg1 : (nb.knownTimes.toFinset.card + mintPotential U σ nb
          (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord) * (Tmax * Tmax + 1) := by
      refine Nat.mul_le_mul_right _ ?_
      simpa only [mintTimeBudget] using hI
    have hg3 : (mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        ≤ mintPotential U σ b ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hmlt
    have he1 : (nb.knownTimes.toFinset.card + mintPotential U σ nb
          (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        = nb.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have he2 : (b.knownTimes.toFinset.card + mintPotential U σ b ord) * (Tmax * Tmax + 1)
        = b.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    have he3 : (mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + (Tmax * Tmax + 1) := by ring
    have he4 : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have he5 : 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord
        = mintPotential U σ b ord * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance, splitOrderedRank]
    omega
  · -- disjunct 3: the fourth component carries the step on its own
    have hbud3' : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2)
        + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord)
          + selfGuardPotential U σ ord := by
      simpa only [mintTimeBudget] using hbud3
    have hkT : nb.knownTimes.toFinset.card ≤ Tmax := by
      simp only [mintTimeBudget] at hbud; omega
    have hp' : (incompPairs nb (expandOnceUnblocked b ord fc tr).2).card ≤ Tmax * Tmax :=
      le_trans (incompPairs_card_le _ _) (Nat.mul_le_mul hkT hkT)
    have h1 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * (Tmax * Tmax + 1) :=
      Nat.mul_le_mul_right _ hbud3'
    have h3 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * U.card
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * U.card :=
      Nat.mul_le_mul_right _ hbud3'
    have h2 : mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
        ≤ mintPotential U σ b ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hm'
    have h4 : (selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        ≤ selfGuardPotential U σ ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hslt
    have e1 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        = nb.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            * (Tmax * Tmax + 1) := by ring
    have e2 : (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * (Tmax * Tmax + 1)
        = b.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * (Tmax * Tmax + 1) := by ring
    have e3 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * U.card
        = mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * U.card := by
      simp only [mintTimeBudget]; ring
    have e4 : (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * U.card
        = mintTimeBudget U σ b ord * U.card + selfGuardPotential U σ ord * U.card := by
      simp only [mintTimeBudget]; ring
    have e5 : (selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        = selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + (Tmax * Tmax + 1) := by ring
    have e6 : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have e7 : 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord
        = mintPotential U σ b ord * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    have e8 : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        = selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * U.card := by ring
    have e9 : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord
        = selfGuardPotential U σ ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * U.card := by ring
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance, splitOrderedRank]
    omega


/-! #### The per-step bundle and the fuel figure at the four-component measure

Section C6's induction is genuinely abstract over the carried state, the measure and the invariant —
`StepDecreases` mentions no branch cardinality, no known-time count, no mint potential and no
ordering rank — so this is an **instantiation**, not a re-proof. The plan's Scope Hypothesis for
this phase asked that that be confirmed before anything was written rather than assumed; it is
confirmed: `stepDecreases_budgetPotentialAt` below is `stepDecreases_budgetPotential`'s proof with
the two step lemmas swapped and nothing else changed.

The figure enlarges by the fourth component's ceiling times its weight,
`(2·(Tmax² + 1) + |U|)·2·|U|` — `selfGuardPotential_le_two_mul` is the ceiling — in exactly the
shape `splitAwareFuel_le_mintAwareFuel` records for the previous enlargement. Nothing stated at the
landed figure is withdrawn. -/

/-- **The per-step bundle, discharged at the four-component measure.** Byte-for-byte
`stepDecreases_budgetPotential` with `budgetPotentialAt_step_unordered` and
`budgetPotentialAt_step_splitOrdered` in place of their three-component originals: `hβ`, `hD`, the
arity facts and the difficulty facts are all reached through `hst.2.1`, which is the confinement
clause both state predicates share in the same position. -/
theorem stepDecreases_budgetPotentialAt {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax D β : Nat} (hβ : 3 ≤ β)
    (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeStable fc U Tmax) :
    StepDecreases fc (BudgetStateAt U Tmax) (budgetPotentialAt U Tmax) D β := by
  intro σ b ord tr hst
  refine ⟨?_, ?_, ?_⟩
  · intro nb hres
    have hmem : nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1 := by
      rw [hres]; simp [unorderedSuccessorBranches]
    exact ⟨σ, budgetPotentialAt_step_unordered hUcl hmint hst hmem
      (expandOnceUnblocked_card_lt hres)⟩
  · intro bs hres
    have hmem : ∀ nb ∈ bs,
        nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1 := by
      intro nb hnb; rw [hres]; simpa [unorderedSuccessorBranches] using hnb
    refine ⟨le_trans (expandOnceUnblocked_split_arity_le hres) hβ, ?_, ?_⟩
    · intro nb hnb
      exact (hD b ord tr hst.2.1).1 nb (hmem nb hnb)
    · intro nb hnb
      exact ⟨σ, budgetPotentialAt_step_unordered hUcl hmint hst (hmem nb hnb)
        (expandOnceUnblocked_split_card_lt hres hnb)⟩
  · intro bs hres
    have harity : bs.length ≤ β := by
      obtain ⟨t₁, t₂, -, rfl⟩ := expandOnceUnblocked_splitOrdered_shape hres
      simpa using hβ
    exact ⟨harity, (hD b ord tr hst.2.1).2 bs hres,
      budgetPotentialAt_step_splitOrdered hUcl hst hres⟩

/-- **The derived path bound at the four-component measure.** `mintPathBound` plus the fourth
component's ceiling times its weight. `selfGuardPotential ≤ 2·|U|` is the ceiling
(`selfGuardPotential_le_two_mul`), and the weight is `2·(Tmax² + 1) + |U|`. -/
def mintPathBoundAt (Ucard Tmax mintBudget : Nat) : Nat :=
  mintPathBound Ucard Tmax mintBudget
  + (2 * (Tmax * Tmax + 1) + Ucard) * (2 * Ucard)

/-- **The derived fuel figure at the four-component measure**, the landed one evaluated at the
enlarged path bound. -/
def mintAwareFuelAt (Ucard Tmax mintBudget D β : Nat) : Nat :=
  fuelFigure D β (mintPathBoundAt Ucard Tmax mintBudget)

/-- The enlarged path bound is an **enlargement** of the landed one, never a replacement. -/
theorem mintPathBound_le_mintPathBoundAt (Ucard Tmax mintBudget : Nat) :
    mintPathBound Ucard Tmax mintBudget ≤ mintPathBoundAt Ucard Tmax mintBudget := by
  simp only [mintPathBoundAt]; omega

/-- …and so is the fuel figure, so nothing stated at `mintAwareFuel` — or, through
`splitAwareFuel_le_mintAwareFuel`, at `splitAwareFuel` — is withdrawn. This is the sense in which
the fourth component's only cost is a **coefficient**: the whole chain of figures still reads
`splitAwareFuel ≤ mintAwareFuel ≤ mintAwareFuelAt`, and no caller's hypothesis list changes. -/
theorem mintAwareFuel_le_mintAwareFuelAt (Ucard Tmax mintBudget D β : Nat) :
    mintAwareFuel Ucard Tmax mintBudget D β ≤ mintAwareFuelAt Ucard Tmax mintBudget D β :=
  fuelFigure_mono (mintPathBound_le_mintPathBoundAt _ _ _)

/-- …and the whole chain, in one statement, so a reader does not have to compose it. -/
theorem splitAwareFuel_le_mintAwareFuelAt (Ucard Tmax mintBudget D β : Nat) :
    splitAwareFuel Ucard Tmax D β ≤ mintAwareFuelAt Ucard Tmax mintBudget D β :=
  le_trans (splitAwareFuel_le_mintAwareFuel _ _ _ _ _)
    (mintAwareFuel_le_mintAwareFuelAt _ _ _ _ _)

/-- **The four-component measure sits under the enlarged path bound.** The one arithmetic fact
connecting the induction to a concrete figure, at the repaired measure.

Three of the four components are capped exactly as `budgetPotential_lt_mintPathBound` caps them;
the fourth is capped by `selfGuardPotential_le_two_mul`, whose coefficient is the index set's width
and not `|U|`-dependent in any other way. Note the state's budget clause is the *combined* one, so
`hbud` gives the mint budget a bound with room for the self-guard potential rather than on the
nose — which is why the mint-side inputs are re-derived here rather than reused. -/
theorem budgetPotentialAt_lt_mintPathBoundAt {U : Finset SignedFormula} {Tmax mintBudget : Nat}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hst : BudgetStateAt U Tmax σ b ord) (hmb : 8 * U.card ≤ mintBudget) :
    budgetPotentialAt U Tmax σ b ord < mintPathBoundAt U.card Tmax mintBudget := by
  obtain ⟨hinv, hbU, hbud, -, -⟩ := hst
  have hkT : b.knownTimes.toFinset.card ≤ Tmax := by
    simp only [mintTimeBudget] at hbud; omega
  have hm8 := mintPotential_le_eight_mul U σ b ord
  have hs2 := selfGuardPotential_le_two_mul U σ ord
  have hR := splitOrderedRank_le Tmax b ord hkT
  have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord
      ≤ 2 * (Tmax * Tmax + 1) * mintBudget := Nat.mul_le_mul_left _ (by omega)
  have hEmul : mintTimeBudget U σ b ord * U.card ≤ Tmax * U.card :=
    Nat.mul_le_mul_right _ (by simp only [mintTimeBudget] at hbud ⊢; omega)
  have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord
      ≤ (2 * (Tmax * Tmax + 1) + U.card) * (2 * U.card) := Nat.mul_le_mul_left _ hs2
  simp only [budgetPotentialAt, budgetPotential, extensionAllowance, mintPathBoundAt,
    mintPathBound]
  omega

/-! #### The terminus chain, restated at the repaired predicate

The six theorems below are the `_at` chain with `MintPaysForTime` exchanged for
`MintPaysForTimeStable`, `BudgetState` for `BudgetStateAt`, `budgetPotential` for
`budgetPotentialAt`, and `mintAwareFuel` for `mintAwareFuelAt`. **The originals are untouched** and
nothing stated at them is withdrawn — `mintAwareFuel_le_mintAwareFuelAt` is the statement that the
figures compose rather than compete.

*The classification, run before anything was restated.* `grep MintPaysForTime` reports eleven
hypothesis sites in this file. Nine are intermediate — the step lemmas, `stepDecreases`,
`expandBranchWithFuel_isSome_of_budget`, `buildTableauAt_isSome_of_budget` and their `_at` siblings
— and pass the residual on without inspecting it. Exactly **two** are seed-level, in the sense that
they quantify no `U` and read every number off a concrete `signedUniverse C L`:
`buildTableauAt_isSome_of_lengthBudget_signedUniverse` and
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse`. Both are restated below; the parent
plan's Scope Hypothesis named a different pair (`buildTableauAt_isSome_at_seed` and
`..._at_seed_lengthBudget`), and the correction is that those two still quantify `U` — they are
seed-level in the *fuel* coordinate only.

*The only new number.* The mint budget floor rises from `8·|U|` to `10·|U|`, because the carried
state's budget clause is now the combined one and `selfGuardPotential ≤ 2·|U|`. `derivedTmaxAt`
carries the same enlargement into the caller-facing form. That is a figure, not a hypothesis: no
caller's hypothesis *list* changes, and `derivedTmax_le_derivedTmaxAt` records that the time bound
grows rather than moves. -/

/-- **The derived time bound at the four-component measure.** The initial known-time count plus the
enlarged mint budget: `8·|U|` for the mint dimension and `2·|U|` for the self-guard dimension, the
two ceilings `mintPotential_le_eight_mul` and `selfGuardPotential_le_two_mul` supply. -/
def derivedTmaxAt (kt0 Ucard : Nat) : Nat := kt0 + 10 * Ucard

/-- The enlarged time hypothesis is satisfied at `derivedTmaxAt`, definitionally — the same sense in
which `derivedTmax_spec` makes the mint budget a discharged parameter rather than a caller
obligation. -/
theorem derivedTmaxAt_spec (b : Branch) (U : Finset SignedFormula) :
    b.knownTimes.toFinset.card + 10 * U.card
      ≤ derivedTmaxAt (b.knownTimes.toFinset.card) U.card := Nat.le_refl _

/-- The enlarged bound is an **enlargement**, never a replacement. -/
theorem derivedTmax_le_derivedTmaxAt (kt0 Ucard : Nat) :
    derivedTmax kt0 Ucard ≤ derivedTmaxAt kt0 Ucard := by
  simp only [derivedTmax, derivedTmaxAt]; omega

/-- `BudgetedTotalityAt` at the four-component measure: the enlarged fuel figure and the enlarged
mint-budget floor, everything else unchanged. -/
def BudgetedTotalitySelfGuarded (fc : FormalSystem.ProofSystem.FrameClass)
    (U : Finset SignedFormula) (mintBudget Tmax D β : Nat) : Prop :=
  ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker) (applied : AppliedSet)
    (maxBranches branchesUsed : Nat),
    (∀ x ∈ b, x ∈ U) →
    RunInvariant b ord →
    10 * U.card ≤ mintBudget →
    b.knownTimes.toFinset.card + mintBudget ≤ Tmax →
    branchesUsed + β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches →
    (expandBranchWithFuel b (mintAwareFuelAt U.card Tmax mintBudget D β) ord fc tr applied
      maxBranches branchesUsed).isSome = true

/-- `expandBranchWithFuel_isSome_of_budget_at` at the repaired predicate.

The seed state is built at `σ = id`, where both σ clauses are free — `sigmaTimeFixed_id` and
`sigmaFixesFrom_id` — so the repaired predicate's added hypothesis costs the caller nothing here.
The combined budget clause is where the enlarged floor is consumed. -/
theorem expandBranchWithFuel_isSome_of_budget_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat}
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeStable fc U Tmax) (harm : ArmSettlement fc) :
    BudgetedTotalitySelfGuarded fc U mintBudget Tmax D β := by
  intro b ord tr applied maxBranches branchesUsed hbU hinv hmb hT hbud
  have hst : BudgetStateAt U Tmax id b ord := by
    refine ⟨hinv, hbU, ?_, sigmaTimeFixed_id b, sigmaFixesFrom_id _⟩
    have h8 := mintPotential_le_eight_mul U id b ord
    have h2 := selfGuardPotential_le_two_mul U id ord
    simp only [mintTimeBudget]
    omega
  exact expandBranchWithFuel_isSome_of_measure (by omega)
    (stepDecreases_budgetPotentialAt hβ hUcl hD hmint)
    harm (mintPathBoundAt U.card Tmax mintBudget) id _ b ord tr applied maxBranches branchesUsed
    hst (budgetPotentialAt_lt_mintPathBoundAt hst (by omega)) (Nat.le_refl _) hbud

/-- **THE TERMINUS, at the repaired predicate.** `buildTableauAt_isSome_of_budget_at` with
`MintPaysForTime` exchanged for `MintPaysForTimeStable`.

The exchange is a **strengthening**: the hypothesis is weaker
(`mintPaysForTimeStable_of_mintPaysForTime`), for the same reason and in the same sense that
`UniverseClosedAt` strengthened its predecessor. The other three residuals are carried across
unaltered and are still named — `DifficultyBounded`, `PostBlockingSettles`, and `UniverseClosedAt`.
Nothing above is withdrawn. -/
theorem buildTableauAt_isSome_of_budget_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeStable fc U Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget D β) fc maxBranches).isSome
      = true := by
  refine buildTableauAt_isSome_of_settles hpb ?_
  exact expandBranchWithFuel_isSome_of_budget_selfGuarded hβ hUcl hD hmint
    (armSettlement_of_postBlockingSettles hpb)
    (seedBranch phi) TimeOrdering.empty EventualityTracker.empty {} maxBranches 0
    hseed (runInvariant_initial _) hmb hT (by omega)

/-- `buildTableauAt_isSome_at_seed_at` at the repaired predicate, with every number read off. -/
theorem buildTableauAt_isSome_at_seed_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {D β : Nat}
    (phi : Formula) (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U)
    (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeStable fc U
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U) :
    (buildTableauAt phi
        (mintAwareFuelAt U.card (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card)
          (10 * U.card) D β)
        fc
        (β * mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card) (10 * U.card) D β)
      ).isSome = true :=
  buildTableauAt_isSome_of_budget_selfGuarded phi _ hβ hUcl hD hmint hpb hseed (Nat.le_refl _)
    (derivedTmaxAt_spec (seedBranch phi) U) (Nat.le_refl _)

/-- `buildTableauAt_isSome_of_lengthBudget_at` at the repaired predicate — **three** refutable
residuals exchanged for satisfiable or weaker ones at once. -/
theorem buildTableauAt_isSome_of_lengthBudget_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax L β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hL : StepLengthBounded fc U L)
    (hmint : MintPaysForTimeStable fc U Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget (difficultyCeiling U L) β
      ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget (difficultyCeiling U L) β) fc
        maxBranches).isSome = true :=
  buildTableauAt_isSome_of_budget_selfGuarded phi maxBranches hβ hUcl
    (difficultyBounded_of_stepLengthBounded_at hL hUcl) hmint hpb hseed hmb hT hbud

/-- `buildTableauAt_isSome_at_seed_lengthBudget_at` at the repaired predicate. -/
theorem buildTableauAt_isSome_at_seed_lengthBudget_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {L β : Nat}
    (phi : Formula) (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U)
    (hL : StepLengthBounded fc U L)
    (hmint : MintPaysForTimeStable fc U
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U) :
    (buildTableauAt phi
        (mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card)
          (10 * U.card) (difficultyCeiling U L) β)
        fc
        (β * mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card) (10 * U.card)
          (difficultyCeiling U L) β)
      ).isSome = true :=
  buildTableauAt_isSome_at_seed_selfGuarded phi hβ hUcl
    (difficultyBounded_of_stepLengthBounded_at hL hUcl) hmint hpb hseed

/-- **Seed-level terminus 1, restated at the repaired predicate**, at the concrete universe
`signedUniverse C L`.

`grep`-and-classify identified exactly two seed-level sites; this is the first. Every hypothesis is
the one the landed `buildTableauAt_isSome_of_lengthBudget_signedUniverse` carries, with
`MintPaysForTime` exchanged for `MintPaysForTimeStable` and the mint-budget floor read at `10·|U|`.
`UniverseClosedAt` is discharged here, not assumed: `universeClosedAt_signedUniverse_of_headroom`
pays it from a `TableauClosed`, `TrichStock` formula stock and a `TimeMergeClosed` label set. -/
theorem buildTableauAt_isSome_of_lengthBudget_signedUniverse_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass}
    {C : Finset Formula} {L : Finset Label} {mintBudget Tmax L' β : Nat}
    (phi : Formula) (maxBranches : Nat) (hβ : 3 ≤ β)
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hlab : UnorderedSuccessorLabelClosed fc L)
    (hSL : StepLengthBounded fc (signedUniverse C L) L')
    (hmint : MintPaysForTimeStable fc (signedUniverse C L) Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ signedUniverse C L)
    (hmb : 10 * (signedUniverse C L).card ≤ mintBudget)
    (hT' : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt (signedUniverse C L).card Tmax mintBudget
      (difficultyCeiling (signedUniverse C L) L') β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt (signedUniverse C L).card Tmax mintBudget
        (difficultyCeiling (signedUniverse C L) L') β) fc maxBranches).isSome = true :=
  buildTableauAt_isSome_of_lengthBudget_selfGuarded phi maxBranches hβ
    (universeClosedAt_signedUniverse_of_headroom hC hT hL hlab) hSL hmint hpb hseed hmb hT' hbud

/-- **Seed-level terminus 2, restated at the repaired predicate** — the caller-facing form, every
number read off, at the concrete universe `signedUniverse C L`.

This is the deliverable's terminus. A caller supplies a `TableauClosed`, `TrichStock` formula
stock, a `TimeMergeClosed` label set (any rectangle), a length bound, and the three unchanged
residuals — `MintPaysForTimeStable`, `PostBlockingSettles`, `UnorderedSuccessorLabelClosed` — and
reads the fuel and the branch budget off the statement.

*What changed relative to `buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse`.* One
residual is weaker (`MintPaysForTimeStable` in place of `MintPaysForTime`,
`mintPaysForTimeStable_of_mintPaysForTime`), and two figures are larger (`mintAwareFuelAt`,
`derivedTmaxAt`, both recorded as enlargements). The hypothesis **list** is identical, name for
name. That is the whole cost of the fourth measure component at the caller's boundary. -/
theorem buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_selfGuarded
    {fc : FormalSystem.ProofSystem.FrameClass}
    {C : Finset Formula} {L : Finset Label} {L' β : Nat} (phi : Formula) (hβ : 3 ≤ β)
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hlab : UnorderedSuccessorLabelClosed fc L)
    (hSL : StepLengthBounded fc (signedUniverse C L) L')
    (hmint : MintPaysForTimeStable fc (signedUniverse C L)
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) (signedUniverse C L).card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ signedUniverse C L) :
    (buildTableauAt phi
        (mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
        fc
        (β * mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
      ).isSome = true :=
  buildTableauAt_isSome_at_seed_lengthBudget_selfGuarded phi hβ
    (universeClosedAt_signedUniverse_of_headroom hC hT hL hlab) hSL hmint hpb hseed

/-! #### The repaired predicate discharged, and the boundary at which it stops

`mintPaysForTime_empty` records the satisfiability boundary for the landed predicate: the residual
is satisfiable exactly where the terminus it guards has nothing to say, since `signedUniverse C L`
is empty only when `C` or `L` is. The repaired predicate inherits that boundary verbatim, and the
discharge below is stated at a **concrete** `signedUniverse C L` rather than at the bare `∅`, so it
instantiates the seed-level termini above rather than only their `U`-quantified ancestors.

**What blocks a discharge at a nonempty universe, precisely.** It is the density coordinate, and
not the σ-hit obligation any more. *(Corrected below: this account is incomplete. The subsection
"The formula-level σ obligation, and the refutation it forces" decides that
`MintPaysForTimeStable` is **false** at a concrete nonempty `signedUniverse`, with no `densityRule`
in the vehicle — the time-level σ hypothesis does not reach the formula-level obligation disjunct 2
carries. Read the paragraph below as one of two blockers, not the only one; see register entry
20.)* `densityRule` mints a fresh time and lies outside **both**
`freshLabelRules` and `selfGuardRules`, so at a `densityRule` step disjunct 1 fails (the mint raises
`knownTimes`), disjunct 2 cannot move (`mintPotential` does not read the rule) and disjunct 3 cannot
move (`selfGuardDischarged` reports the catch-all `true` for it). That is the residual
`MintPaysForTimeAt`'s obligation map already names, carried here unchanged: the intended second
component is `gapPotential`, indexed by `U ×ˢ U` and gated on `denseRules`, and it is implemented
nowhere and assumed by nothing.

`densityRule` is `denseRules`-gated, so it cannot fire at a frame class outside `.Dense` /
`.RTime`; a discharge restricted to the other classes is therefore not refuted. What it needs is
a rule-by-rule census showing that every remaining rule either mints no time (disjunct 1), is
witness-guarded (disjunct 2) or is self-guarded (disjunct 3). That census is the parent plan's
time-minting-census work read in the other direction, and it is **not attempted here** — stated as
a named next step rather than gestured at. See register entries 19 and 20. -/

/-- **The satisfiability boundary, at the repaired predicate.** The exact mirror of
`mintPaysForTime_empty`, and for the same reason: confinement forces the branch empty, the engine
reports `.saturated`, and `unorderedSuccessorBranches` of a `.saturated` result is `[]`.

The added `SigmaTimeStable` hypothesis is discarded rather than used, which is the honest reading —
this discharge is about the universe being empty, not about the renaming. -/
theorem mintPaysForTimeStable_empty (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    MintPaysForTimeStable fc ∅ Tmax := by
  intro _ b ord tr _ hconf _ nb hnb
  have hb : b = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by simpa using hconf x hx
  subst hb
  simp [expandOnceUnblocked, findUnexpandedUnblockedWith, unorderedSuccessorBranches] at hnb

/-- `signedUniverse C L` is empty when `L` is — the fact that turns the boundary above into a
statement about a concrete `signedUniverse`. -/
theorem signedUniverse_empty_labels (C : Finset Formula) :
    signedUniverse C (∅ : Finset Label) = ∅ := by
  simp [signedUniverse]

/-- **The repaired predicate, discharged at a concrete `signedUniverse C L`**, at every frame class
and every `Tmax`.

This is the instantiation the seed-level termini above consume: `hmint` is supplied rather than
assumed, so
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_selfGuarded` reads with one residual
fewer at `L = ∅`. It is also, by `mintPaysForTime_empty`'s own argument, exactly as far as the
predicate can be discharged without the density coordinate: see the subsection preamble for what a
nonempty discharge needs, and register entry 19 for the record. -/
theorem mintPaysForTimeStable_signedUniverse_empty
    (fc : FormalSystem.ProofSystem.FrameClass) (C : Finset Formula) (Tmax : Nat) :
    MintPaysForTimeStable fc (signedUniverse C (∅ : Finset Label)) Tmax := by
  rw [signedUniverse_empty_labels]
  exact mintPaysForTimeStable_empty fc Tmax

/-! #### The formula-level σ obligation, and the refutation it forces

The subsection above stops at `U = ∅` and names the **density** coordinate as what blocks a
nonempty discharge. That account is incomplete, and the missing half is decided here rather than
argued: `MintPaysForTimeStable` is **false** at a concrete nonempty `signedUniverse C L`, at every
frame class and every `Tmax`, with no `densityRule` anywhere near the vehicle.

*Why the density account missed it.* `sigma_time_hit_of_sigmaTimeStable` discharges the σ-hit
obligation `selfGuardPotential` reads, and its own docstring already records that
`mintPotential_lt_of_mint`'s obligation is **not** available the same way — it needs `σ sf = g` on
the nose. Disjunct 2 is the only disjunct that pays for the six rules in
`freshLabelRules ∩ freshTimeRules`, and those rules mint at times whose reach the self-guard
component may already count as cured, so disjunct 3 cannot stand in for it. `SigmaTimeStable`
constrains σ's *times* and nothing else, so a renaming that preserves every label and destroys every
formula satisfies it while pinning `mintPotential` at its ceiling forever.

*The vehicle.* `flatSigma` sends every signed formula to a fixed positive atom **at its own label**.
`witnessPresent`'s match is on `(rule, sign, formula)` and every arm that could fire needs a
temporal or modal shape, so an atom falls through to the catch-all at all thirty-six rules:
`mintPotential U flatSigma b ord = 8 · |U|` at *every* state (`mintPotential_flatSigma`), so
disjunct 2's strict inequality is unavailable at every step of every run. What remains is to find
one step that mints while curing no self-guard column, and `untlPos` at a time whose future is
already non-empty is such a step — it is witness-guarded, so it is exactly one of the six rules
disjunct 2 was carrying.

*What is not claimed.* This does not withdraw anything. `MintPaysForTimeStable`'s direction lemma,
its no-leak confirmation, the four-component measure and the restated termini all stand exactly as
they are; what changes is the reading of the residual they carry, from "open at nonempty `U`, at the
density coordinate" to "false at nonempty `U`, at the formula coordinate, **and** open at the
density coordinate". See register entry 20. -/

/-- **The formula-destroying, time-preserving renaming.** Every signed formula goes to a fixed
positive atom at its own label, so the label — and therefore the time — is untouched and the formula
is gone. -/
def flatSigma : SignedFormula → SignedFormula := fun x => ⟨Sign.pos, mwP, x.label⟩

/-- It is `SigmaTimeStable` on **every** branch, by `rfl`. This is the whole point: the hypothesis
`MintPaysForTimeStable` adds is satisfied by a renaming no run produces, and satisfied for free. -/
theorem flatSigma_sigmaTimeStable (b : Branch) : SigmaTimeStable flatSigma b := fun _ _ => rfl

/-- **Its image is witness-free at every rule, state and ordering.** `witnessPresent` matches on the
formula's shape at all eight fresh-label arms — `.box`, `asDiamond?`, `.allFuture`, `.allPast`,
`asSomeFuture?`, `asSomePast?`, `asUntil?`, `asSince?` — and an atom matches none of them, so every
arm falls through to the catch-all. Decided over all thirty-six constructors. -/
theorem witnessPresent_flatSigma (r : TableauRule) (x : SignedFormula) (b : Branch)
    (ord : TimeOrdering) : witnessPresent r (flatSigma x) b ord = false := by
  cases r <;> rfl

/-- **So `mintPotential` is pinned at its own ceiling, at every state.** Compare
`mintPotential_le_eight_mul`, which bounds it: under `flatSigma` the bound is met with equality
everywhere, so the potential is a constant function of the state and disjunct 2's strict inequality
is unavailable at every step of every run — before any configuration is chosen. -/
theorem mintPotential_flatSigma (U : Finset SignedFormula) (b : Branch) (ord : TimeOrdering) :
    mintPotential U flatSigma b ord = 8 * U.card := by
  simp only [mintPotential]
  rw [Finset.filter_true_of_mem
      (fun p _ => witnessPresent_flatSigma p.1 p.2 b ord),
    Finset.card_product, freshLabelRules_card]

/-- **…while the fourth component measures exactly what `id` measures.** `selfGuardDischarged` reads
only `sf.label.time`, and `flatSigma` preserves the label, so the refutation cannot be dismissed as
one that also breaks the self-guard ledger: that ledger sees the identity. -/
theorem selfGuardPotential_flatSigma (U : Finset SignedFormula) (ord : TimeOrdering) :
    selfGuardPotential U flatSigma ord = selfGuardPotential U id ord := rfl

/-- The refuting trigger: `U(g, e)` positive at time `1`, a **witness-guarded** minting rule's
vehicle (`untlPos ∈ freshLabelRules ∩ freshTimeRules`), so the step it drives is one disjunct 2 was
carrying and disjunct 3 never claimed. -/
def fhTrigger : SignedFormula := SignedFormula.pos (Formula.untl mwG mwE) ⟨0, 1⟩

/-- The refuting branch. The two atoms carry times `0` and `2`, which `OrdTimesKnown` requires of
the ordering below and which also put the trigger's time strictly inside the order. -/
def fhBranch : Branch :=
  [fhTrigger, SignedFormula.pos mwP ⟨0, 0⟩, SignedFormula.pos mwQ ⟨0, 2⟩]

/-- The refuting ordering: `0 < 1 < 2`. The trigger sits at `1`, whose future is **already**
non-empty — which is what makes the step invisible to the self-guard component, since `untlNeg`'s
column at time `1` is already cured before the step and stays cured after it. -/
def fhOrd : TimeOrdering := { constraints := [(0, 1), (1, 2)] }

/-- The label rectangle. Deliberately excludes time `3`, the index the step mints: the new edge
`(1, 3)` therefore puts nothing into the past of any time the universe indexes, so no self-guard
column flips at all. -/
def fhLabels : Finset Label := {⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 2⟩}

/-- The formula stock: the trigger's formula and the two carrier atoms. -/
def fhStock : Finset Formula := {mwP, mwQ, Formula.untl mwG mwE}

/-- The first arm of the `untlPos` split: the event at the freshly minted time `3`, then the
re-included trigger and the original branch. -/
def fhSucc : Branch :=
  [SignedFormula.pos mwE ⟨0, 3⟩, fhTrigger, SignedFormula.pos mwP ⟨0, 0⟩,
   SignedFormula.pos mwQ ⟨0, 2⟩]

/-- The refuting state satisfies the run invariant, so the refutation is not reached by feeding the
predicate a state the run cannot occupy. -/
theorem fh_runInvariant : RunInvariant fhBranch fhOrd := by
  constructor
  · unfold IrreflOrd fhOrd; decide
  · unfold OrdTimesKnown; decide

/-- …and it is confined to a **concrete, nonempty** `signedUniverse`, which is the universe shape
the seed-level termini consume. -/
theorem fh_confined : ∀ x ∈ fhBranch, x ∈ signedUniverse fhStock fhLabels := by decide

/-- The universe is nonempty, and its size is read off rather than asserted: two signs, three
formulas, three labels. -/
theorem fh_universe_card : (signedUniverse fhStock fhLabels).card = 18 := by decide

/-- **`MintPaysForTimeStable` is false at a concrete nonempty `signedUniverse`**, at every frame
class and every `Tmax`.

The step is `untlPos` firing on the trigger at time `1`; the engine reports a two-arm `.split` and
this is its first arm. On it, all three disjuncts fail on decided numbers:

* disjunct 1 — `knownTimes` goes `{0,1,2}` to `{0,1,2,3}`, so `4 ≤ 3` is false;
* disjunct 2 — `mintPotential` is `8·18 = 144` before **and** after, by `mintPotential_flatSigma`,
  which is a general fact and not a measurement at this configuration;
* disjunct 3 — `selfGuardPotential` is `12` before and `12` after: the step's only new edge is
  `(1, 3)`, time `1`'s future was already non-empty, and no formula of the universe sits at time `3`.

The four frame classes are decided separately, and `Tmax` is universally quantified because
disjunct 1 fails at its first conjunct and disjunct 2 fails by an identity, neither of which
mentions `Tmax`.

Contrast `mintPaysForTime_untlNeg_false`, which refutes the *unrepaired* predicate with a
**self-guarded** vehicle at `σ = id`. That refutation is what the fourth measure component answers.
This one is at a **witness-guarded** vehicle, and what it defeats is the hypothesis
`MintPaysForTimeStable` adds rather than the ledger it adds. -/
theorem mintPaysForTimeStable_signedUniverse_false
    (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    ¬ MintPaysForTimeStable fc (signedUniverse fhStock fhLabels) Tmax := by
  intro h
  have key := h flatSigma fhBranch fhOrd EventualityTracker.empty fh_runInvariant fh_confined
    (flatSigma_sigmaTimeStable fhBranch)
  cases fc <;>
    [ (rcases key fhSucc (by decide) with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h3⟩);
      (rcases key fhSucc (by decide) with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h3⟩);
      (rcases key fhSucc (by decide) with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h3⟩);
      (rcases key fhSucc (by decide) with ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h3⟩)] <;>
    first
      | exact absurd h1 (by decide)
      | (rw [mintPotential_flatSigma, mintPotential_flatSigma] at h2; omega)
      | exact absurd h3 (by decide)

/-! #### The formula-level repair: `SigmaFixed`, and the residual restated at it

The refutation above localises the defect precisely — the added hypothesis constrains σ's *times*
where disjunct 2 needs it to constrain σ's *formulas* — so the repair is to state the hypothesis at
the coordinate the obligation lives at, and nowhere else. Nothing else about the predicate changes:
the three disjuncts are the same three, in the same order, with the same conjuncts.

**The repair is free at the arm, which is the whole reason it is available.** `rhoSF src tgt` renames
one time and leaves every other formula strictly alone, so `rhoSF_eq_of_ne_src` is the same one-line
fact as `rhoSF_time_eq_of_ne_src` with the conclusion strengthened from "same time" to "same
formula". Every lemma of the σ layer transcribes across that strengthening with no new content:
`sigmaFixed_identifyOriented` is `sigmaTimeStable_identifyOriented`'s proof verbatim,
`sigmaFormulaFixed_identifyOriented` is `sigmaTimeFixed_identifyOriented`'s, and the watermark
lemmas are `sigmaFixesFrom_*`'s. That the strengthening costs nothing at the one step that changes σ
is a fact about `rhoSF`, not a coincidence, and it is why the repair does not have to be paid for
anywhere downstream: **no figure changes** — `mintPathBoundAt`, `mintAwareFuelAt` and `derivedTmaxAt`
are reused unaltered, unlike the fourth component, which cost a coefficient.

**What is bought.** `sigma_formula_hit_of_sigmaFixed` discharges
`mintPotential_lt_of_mint`'s obligation from confinement alone — the trigger witnesses its own hit,
exactly as `sigma_time_hit_of_sigmaTimeStable` does at the time level — and
`mintPotential_lt_of_pick_linear_sigmaFixed` / `..._branching_sigmaFixed` are that discharge
delivered at the pick, which is where disjunct 2 is actually established. So the added hypothesis is
not inert, and the sense in which it is not is a proved implication rather than a measurement.

**What is not bought.** The density coordinate, unchanged. `densityRule` mints a fresh time while
lying outside both `freshLabelRules` and `selfGuardRules`, so no disjunct moves at a `densityRule`
step whatever σ is; it is `denseRules`-gated, so a discharge restricted to the frame classes outside
`.Dense` / `.RTime` is not refuted, and what such a discharge needs is the rule-by-rule census
register entry 19 names. That census is **not** attempted here. See register entry 20. -/

/-- **`rhoSF` is the identity on a formula away from the retired index** — not merely on its time.
The strengthening of `rhoSF_time_eq_of_ne_src` that the whole formula-level layer rests on, and it
is the same one line: `rho` is a conditional on the time, so off the retired index the record is
rebuilt from its own fields. -/
theorem rhoSF_eq_of_ne_src {src tgt : TimeIndex} {sf : SignedFormula}
    (h : sf.label.time ≠ src) : rhoSF src tgt sf = sf := by
  simp [rhoSF, rho, h]

/-- **The formula-level twin of `SigmaTimeStable`**: σ fixes every branch formula outright.

Strictly stronger, and stronger in exactly the respect `mintPotential_lt_of_mint` needs — that
lemma asks for `σ sf = g` on the nose and `SigmaTimeStable` supplies only `(σ sf).label.time =
g.label.time`. `flatSigma_not_sigmaFixed` decides that the gap is real rather than notional. -/
def SigmaFixed (σ : SignedFormula → SignedFormula) (b : Branch) : Prop :=
  ∀ x ∈ b, σ x = x

/-- It implies the time-level form, so nothing stated at `SigmaTimeStable` is lost. -/
theorem sigmaTimeStable_of_sigmaFixed {σ : SignedFormula → SignedFormula} {b : Branch}
    (h : SigmaFixed σ b) : SigmaTimeStable σ b := fun x hx => by rw [h x hx]

/-- **The refuting renaming is excluded by exactly this hypothesis**, which is the statement that
the repair is aimed at the defect rather than past it. `flatSigma` satisfies `SigmaTimeStable` on
every branch and fails `SigmaFixed` on the refuting one. -/
theorem flatSigma_not_sigmaFixed : ¬ SigmaFixed flatSigma fhBranch := by
  intro h
  exact absurd (h fhTrigger (by decide)) (by decide)

/-- **The formula-level twin of `SigmaTimeFixed`.** Quantifies over every formula sitting at a
branch time rather than over branch formulas, which is the extra reach the identification arm's
relabelling needs — the arm puts formulas on the branch that were not there before. -/
def SigmaFormulaFixed (σ : SignedFormula → SignedFormula) (b : Branch) : Prop :=
  ∀ x : SignedFormula, x.label.time ∈ b.knownTimes → σ x = x

theorem sigmaFixed_of_sigmaFormulaFixed {σ : SignedFormula → SignedFormula} {b : Branch}
    (h : SigmaFormulaFixed σ b) : SigmaFixed σ b :=
  fun x hx => h x (mem_knownTimes_of_mem hx)

theorem sigmaTimeFixed_of_sigmaFormulaFixed {σ : SignedFormula → SignedFormula} {b : Branch}
    (h : SigmaFormulaFixed σ b) : SigmaTimeFixed σ b :=
  fun x hx => by rw [h x hx]

/-- **The seed satisfies it for free**, exactly as at the time level: σ is `id` before the first
ordered split. -/
theorem sigmaFormulaFixed_id (b : Branch) : SigmaFormulaFixed id b := fun _ _ => rfl

/-- **The formula-level twin of `SigmaFixesFrom`.** The provenance fact additive steps need: a
freshly minted time is safe as soon as it is at least `n`. -/
def SigmaFixesFormulasFrom (σ : SignedFormula → SignedFormula) (n : TimeIndex) : Prop :=
  ∀ x : SignedFormula, n ≤ x.label.time → σ x = x

theorem sigmaFixesFrom_of_sigmaFixesFormulasFrom {σ : SignedFormula → SignedFormula}
    {n : TimeIndex} (h : SigmaFixesFormulasFrom σ n) : SigmaFixesFrom σ n :=
  fun x hx => by rw [h x hx]

theorem sigmaFixesFormulasFrom_id (n : TimeIndex) : SigmaFixesFormulasFrom id n := fun _ _ => rfl

theorem sigmaFixesFormulasFrom_rhoSF {src tgt n : TimeIndex} (h : src < n) :
    SigmaFixesFormulasFrom (rhoSF src tgt) n :=
  fun _ hx => rhoSF_eq_of_ne_src (Nat.ne_of_gt (Nat.lt_of_lt_of_le h hx))

/-- Post-composing another renaming keeps the watermark, provided the new retired index is below it.
`retired_lt_nextTime_oriented` is what supplies that, exactly as at the time level. -/
theorem sigmaFixesFormulasFrom_comp {σ : SignedFormula → SignedFormula} {src tgt n : TimeIndex}
    (hσ : SigmaFixesFormulasFrom σ n) (h : src < n) :
    SigmaFixesFormulasFrom (fun x => rhoSF src tgt (σ x)) n := by
  intro x hx
  have hfix := hσ x hx
  show rhoSF src tgt (σ x) = x
  rw [hfix]
  exact rhoSF_eq_of_ne_src (Nat.ne_of_gt (Nat.lt_of_lt_of_le h hx))

theorem sigmaFixesFormulasFrom_mono {σ : SignedFormula → SignedFormula} {n m : TimeIndex}
    (h : SigmaFixesFormulasFrom σ n) (hle : n ≤ m) : SigmaFixesFormulasFrom σ m :=
  fun x hx => h x (le_trans hle hx)

/-- **The identification arm preserves the formula-level invariant.** The time-level proof with
`rhoSF_time_eq_of_ne_src` exchanged for `rhoSF_eq_of_ne_src`; the side condition is the same one
`universeClosedAt_identify_at_trigger_oriented` already carries, and no more. -/
theorem sigmaFormulaFixed_identifyOriented {σ : SignedFormula → SignedFormula} {b : Branch}
    {ord : TimeOrdering} {t₁ t₂ : TimeIndex} (hne : t₁ ≠ t₂)
    (hmax : (identifyOrient t₁ t₂).2 ∈ b.knownTimes) (h : SigmaFormulaFixed σ b) :
    SigmaFormulaFixed
      (fun x => rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 (σ x))
      (identifyOriented b ord t₁ t₂).1 := by
  intro x hx
  simp only [identifyOriented] at hx
  have hb : x.label.time ∈ b.knownTimes := knownTimes_identifyTime_subset hmax _ hx
  have hnesrc : x.label.time ≠ (identifyOrient t₁ t₂).1 := by
    intro hc
    exact src_not_mem_knownTimes_identifyTime b _ _ (identifyOrient_ne hne) (hc ▸ hx)
  have hfix := h x hb
  simp only [hfix]
  exact rhoSF_eq_of_ne_src hnesrc

/-- **…and the arm's own renaming is formula-fixed on the state the arm produces.**
`sigmaTimeStable_identifyOriented`'s proof verbatim with the strengthened conclusion — the post-arm
branch carries no formula at the retired index, and away from that index `rhoSF` is the identity on
the formula and not merely on its time. No membership hypothesis on `t₁` or `t₂` is used. -/
theorem sigmaFixed_identifyOriented {b : Branch} {ord : TimeOrdering} {t₁ t₂ : TimeIndex}
    (hne : t₁ ≠ t₂) :
    SigmaFixed (rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2)
      (identifyOriented b ord t₁ t₂).1 := by
  intro x hx
  simp only [identifyOriented] at hx
  refine rhoSF_eq_of_ne_src ?_
  intro hEq
  have hmem : x.label.time
      ∈ (b.identifyTime (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2).knownTimes :=
    mem_knownTimes_of_mem hx
  rw [hEq] at hmem
  exact src_not_mem_knownTimes_identifyTime b _ _ (identifyOrient_ne hne) hmem

theorem sigmaFormulaFixed_grow {σ : SignedFormula → SignedFormula} {b b' : Branch}
    (h : SigmaFormulaFixed σ b)
    (hnew : ∀ t ∈ b'.knownTimes, t ∈ b.knownTimes ∨ ∀ x : SignedFormula, x.label.time = t →
      σ x = x) :
    SigmaFormulaFixed σ b' := by
  intro x hx
  rcases hnew x.label.time hx with hb | hfix
  · exact h x hb
  · exact hfix x rfl

/-- The form the run-level argument uses: a successor's times are the predecessor's plus fresh
ones, and the fresh ones are at least `b.nextTime`, strictly above every index the run has retired
(`retired_lt_nextTime_oriented`, `nextTime_monotone_along_run`). -/
theorem sigmaFormulaFixed_grow_of_fixesFrom {σ : SignedFormula → SignedFormula} {b b' : Branch}
    {n : TimeIndex} (h : SigmaFormulaFixed σ b) (hfix : SigmaFixesFormulasFrom σ n)
    (hnew : ∀ t ∈ b'.knownTimes, t ∈ b.knownTimes ∨ n ≤ t) : SigmaFormulaFixed σ b' := by
  refine sigmaFormulaFixed_grow h (fun t ht => ?_)
  rcases hnew t ht with hb | hle
  · exact Or.inl hb
  · exact Or.inr (fun x hxt => hfix x (hxt ▸ hle))

/-- **The formula-level σ-hit obligation, discharged from confinement.** The trigger witnesses its
own hit, and this time at the coordinate `mintPotential_lt_of_mint` actually asks about. The exact
mirror of `sigma_time_hit_of_sigmaTimeStable`, and the statement whose absence
`mintPaysForTimeStable_signedUniverse_false` exploits. -/
theorem sigma_formula_hit_of_sigmaFixed {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} (hconf : ∀ x ∈ b, x ∈ U)
    (hfix : SigmaFixed σ b) {sf : SignedFormula} (hsf : sf ∈ b) :
    ∃ x ∈ U, σ x = sf :=
  ⟨sf, hconf sf hsf, hfix sf hsf⟩

/-- **The residual restated at the formula-level hypothesis.** `MintPaysForTimeStable`'s body
verbatim, with `SigmaTimeStable σ b` exchanged for `SigmaFixed σ b` and nothing else touched — the
same three disjuncts, in the same order, with the same conjuncts.

**The direction.** `SigmaFixed` is stronger than `SigmaTimeStable`, so requiring it makes the
predicate **weaker**: the implication runs `MintPaysForTimeStable → MintPaysForTimeFixed` and never
the other way, and every theorem restated against it is a **strengthening**. This is the
`universeClosedAt_of_universeClosed` idiom for the fourth time in this file, and saying it in words
is not a formality — register entry 7 exists because a weakening was once mistaken for a repair.

**What the exchange buys, and what it costs.** It buys the formula-level σ-hit
(`sigma_formula_hit_of_sigmaFixed`), which is what disjunct 2 needs at the six rules in
`freshLabelRules ∩ freshTimeRules` and which `SigmaTimeStable` provably does not supply
(`mintPaysForTimeStable_signedUniverse_false`). It costs **nothing**: the added hypothesis is
discharged at the seed by `sigmaFormulaFixed_id` and at the identification arm by
`sigmaFormulaFixed_identifyOriented`, no figure changes, and no caller's hypothesis list changes.

**What it does not touch.** The density coordinate. At a `densityRule` step disjunct 1 fails (the
mint raises `knownTimes`), disjunct 2 cannot move (`densityRule ∉ freshLabelRules`) and disjunct 3
cannot move (`densityRule ∉ selfGuardRules`), for every σ whatsoever — so this predicate is
separately refutable at `.Dense` / `.RTime` by a `densityRule` vehicle, and a discharge at the
other frame classes needs the rule-by-rule census register entries 19 and 20 name. That census is
not attempted here, and `gapPotential` remains implemented nowhere and assumed by nothing. -/
def MintPaysForTimeFixed (fc : FormalSystem.ProofSystem.FrameClass) (U : Finset SignedFormula)
    (Tmax : Nat) : Prop :=
  ∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
    (tr : EventualityTracker), RunInvariant b ord → (∀ x ∈ b, x ∈ U) → SigmaFixed σ b →
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      (nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb (expandOnceUnblocked b ord fc tr).2
          ≤ splitOrderedRank Tmax b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord ∧
          mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
            < mintPotential U σ b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
          selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            < selfGuardPotential U σ ord)

/-- **Direction lemma.** The hypothesis is strengthened and nothing is removed, so
`MintPaysForTimeFixed` is **weaker** than `MintPaysForTimeStable` and every theorem restated against
it is a strengthening. The predicate is not landed without this lemma; see register entry 7. -/
theorem mintPaysForTimeFixed_of_mintPaysForTimeStable
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {Tmax : Nat}
    (h : MintPaysForTimeStable fc U Tmax) : MintPaysForTimeFixed fc U Tmax :=
  fun σ b ord tr hri hconf hfix nb hnb =>
    h σ b ord tr hri hconf (sigmaTimeStable_of_sigmaFixed hfix) nb hnb

/-- …and the composite back to the predicate this file started from, so the whole chain of
weakenings `MintPaysForTime → MintPaysForTimeStable → MintPaysForTimeFixed` is one statement. -/
theorem mintPaysForTimeFixed_of_mintPaysForTime {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat} (h : MintPaysForTime fc U Tmax) :
    MintPaysForTimeFixed fc U Tmax :=
  mintPaysForTimeFixed_of_mintPaysForTimeStable (mintPaysForTimeStable_of_mintPaysForTime h)

/-- **The added hypothesis is not inert, at a `.linear` witness-guarded mint.** Confinement plus
`SigmaFixed` deliver `mintPotential_lt_of_pick_linear`'s σ-hit outright, so disjunct 2 holds at the
pick with no further input. This is the statement the refutation above shows is unavailable under
`SigmaTimeStable`. -/
theorem mintPotential_lt_of_pick_linear_sigmaFixed {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {r : TableauRule} {sf₀ : SignedFormula}
    {fs : List SignedFormula} {o : TimeOrdering}
    (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) (hsf₀ : sf₀ ∈ b)
    (hpick : findApplicableRule sf₀ b ord fc = some (r, RuleResult.linear fs, o))
    (hfresh : ruleMintsFreshLabel r = true) :
    mintPotential U σ (fs ++ b) o < mintPotential U σ b ord := by
  obtain ⟨x, hxU, hxσ⟩ := sigma_formula_hit_of_sigmaFixed hconf hfix hsf₀
  exact mintPotential_lt_of_pick_linear hpick hfresh hxU hxσ

/-- **The branching mirror**, on every arm. -/
theorem mintPotential_lt_of_pick_branching_sigmaFixed {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {r : TableauRule} {sf₀ : SignedFormula}
    {bss : List (List SignedFormula)} {o : TimeOrdering}
    (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) (hsf₀ : sf₀ ∈ b)
    (hpick : findApplicableRule sf₀ b ord fc = some (r, RuleResult.branching bss, o))
    (hfresh : ruleMintsFreshLabel r = true) :
    ∀ arm ∈ bss, mintPotential U σ (arm ++ b) o < mintPotential U σ b ord := by
  obtain ⟨x, hxU, hxσ⟩ := sigma_formula_hit_of_sigmaFixed hconf hfix hsf₀
  exact mintPotential_lt_of_pick_branching hpick hfresh hxU hxσ

/-- **The no-leak confirmation at the formula level.** Five conjuncts, and together they are the
claim that the repair costs no consumer a hypothesis.

*The direction*, twice: from the original predicate and from the previous repair, so the chain of
weakenings is explicit and neither link is left to inference. *Discharged, not assumed*: the seed
satisfies the invariant because σ is `id` there, and the arm's own renaming satisfies the
per-formula form on the state the arm produces with **no** membership side condition, which is
strictly better than the time-level layer needed. *Preserved*: the arm carries the invariant
forward under exactly the side condition
`universeClosedAt_identify_at_trigger_oriented` already carries.

*And the cost, stated so it can be checked.* Unlike the fourth measure component, which cost a
coefficient in `mintPathBound` and `derivedTmax`, this repair costs **no figure at all**:
`budgetPotentialAt`, `mintPathBoundAt`, `mintAwareFuelAt` and `derivedTmaxAt` are reused byte for
byte by the chain below. -/
theorem mintPaysForTimeFixed_no_leak {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat} :
    (MintPaysForTime fc U Tmax → MintPaysForTimeFixed fc U Tmax) ∧
      (MintPaysForTimeStable fc U Tmax → MintPaysForTimeFixed fc U Tmax) ∧
      (∀ b : Branch, SigmaFormulaFixed id b) ∧
      (∀ (b : Branch) (ord : TimeOrdering) (t₁ t₂ : TimeIndex), t₁ ≠ t₂ →
        SigmaFixed (rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2)
          (identifyOriented b ord t₁ t₂).1) ∧
      (∀ (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering)
          (t₁ t₂ : TimeIndex), t₁ ≠ t₂ → (identifyOrient t₁ t₂).2 ∈ b.knownTimes →
        SigmaFormulaFixed σ b →
        SigmaFormulaFixed
          (fun x => rhoSF (identifyOrient t₁ t₂).1 (identifyOrient t₁ t₂).2 (σ x))
          (identifyOriented b ord t₁ t₂).1) :=
  ⟨mintPaysForTimeFixed_of_mintPaysForTime, mintPaysForTimeFixed_of_mintPaysForTimeStable,
   sigmaFormulaFixed_id, fun _ _ _ _ hne => sigmaFixed_identifyOriented hne,
   fun _ _ _ _ _ hne hmax h => sigmaFormulaFixed_identifyOriented hne hmax h⟩

/-- **The carried state at the formula-level σ clause.** -/
def BudgetStateFixed (U : Finset SignedFormula) (Tmax : Nat)
    (σ : SignedFormula → SignedFormula) (b : Branch) (ord : TimeOrdering) : Prop :=
  RunInvariant b ord ∧ (∀ x ∈ b, x ∈ U) ∧
    mintTimeBudget U σ b ord + selfGuardPotential U σ ord ≤ Tmax ∧
    SigmaFormulaFixed σ b ∧ SigmaFixesFormulasFrom σ b.nextTime

/-- The formula-level state implies the time-level one. -/
theorem budgetStateAt_of_budgetStateFixed {U : Finset SignedFormula} {Tmax : Nat}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    (h : BudgetStateFixed U Tmax σ b ord) : BudgetStateAt U Tmax σ b ord :=
  ⟨h.1, h.2.1, h.2.2.1, sigmaTimeFixed_of_sigmaFormulaFixed h.2.2.2.1,
    sigmaFixesFrom_of_sigmaFixesFormulasFrom h.2.2.2.2⟩

/-- **The measure drops at every arm of an ordered split, at the formula-level state.**
`budgetPotentialAt_step_splitOrdered` with the two σ clauses read at the formula level. The
measure arithmetic is byte-identical — no figure and no weight changes — and the only edits are
`sigmaFormulaFixed_identifyOriented` and `sigmaFixesFormulasFrom_comp` in place of their time-level
originals at arm 3. No residual is consumed here: an ordered split does not mint. -/
theorem budgetPotentialAt_step_splitOrdered_fixed {U : Finset SignedFormula} {Tmax : Nat}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {bs : List (Branch × TimeOrdering)}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hUcl : UniverseClosedAt fc U) (hst : BudgetStateFixed U Tmax σ b ord)
    (hres : (expandOnceUnblocked b ord fc tr).1 = ExpansionResult.splitOrdered bs) :
    ∀ p ∈ bs, ∃ σ' : SignedFormula → SignedFormula, BudgetStateFixed U Tmax σ' p.1 p.2 ∧
      budgetPotentialAt U Tmax σ' p.1 p.2 < budgetPotentialAt U Tmax σ b ord := by
  obtain ⟨hinv, hbU, hbud, hfix, hfrom⟩ := hst
  have hkT : b.knownTimes.toFinset.card ≤ Tmax := by
    simp only [mintTimeBudget] at hbud; omega
  have hcU : b.toFinset.card ≤ U.card := card_le_of_subset_universe hbU
  have hrank := expandOnceUnblocked_splitOrdered_rank_lt hkT hres
  have hinvs := (expandOnceUnblocked_runInvariant hinv).2 bs hres
  obtain ⟨t₁, t₂, htrig, rfl⟩ := expandOnceUnblocked_splitOrdered_shape hres
  intro p hp
  have hrk := hrank p hp
  have hinvp := hinvs p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · dsimp only at hrk hinvp ⊢
    have hm' : mintPotential U σ b (ord.addFuture t₁ t₂) ≤ mintPotential U σ b ord :=
      mintPotential_le_of_grow (fun _ hx => hx) (addFuture_constraints_mono ord t₁ t₂)
    have hI : mintTimeBudget U σ b (ord.addFuture t₁ t₂) ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ b (ord.addFuture t₁ t₂) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ b (ord.addFuture t₁ t₂)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hS1 : selfGuardPotential U σ (ord.addFuture t₁ t₂) ≤ selfGuardPotential U σ ord :=
      selfGuardPotential_le_of_grow (addFuture_constraints_mono ord t₁ t₂)
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ (ord.addFuture t₁ t₂)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS1
    refine ⟨σ, ⟨hinvp, hbU, by omega, hfix, hfrom⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · dsimp only at hrk hinvp ⊢
    have hm' : mintPotential U σ b (ord.addFuture t₂ t₁) ≤ mintPotential U σ b ord :=
      mintPotential_le_of_grow (fun _ hx => hx) (addFuture_constraints_mono ord t₂ t₁)
    have hI : mintTimeBudget U σ b (ord.addFuture t₂ t₁) ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ b (ord.addFuture t₂ t₁) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ b (ord.addFuture t₂ t₁)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hS2 : selfGuardPotential U σ (ord.addFuture t₂ t₁) ≤ selfGuardPotential U σ ord :=
      selfGuardPotential_le_of_grow (addFuture_constraints_mono ord t₂ t₁)
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ (ord.addFuture t₂ t₁)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS2
    refine ⟨σ, ⟨hinvp, hbU, by omega, hfix, hfrom⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · dsimp only at hrk hinvp ⊢
    have hk := knownTimes_card_lt_at_arm3_oriented (b := b) (ord := ord) htrig
    set s := min t₁ t₂ with hsdef
    set u := max t₁ t₂ with hudef
    have hm' : mintPotential U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
        (ord.identifyTime s u) ≤ mintPotential U σ b ord :=
      mintPotential_identifyTime_oriented htrig hinv.irreflOrd
    have hS3 : selfGuardPotential U (fun x => rhoSF s u (σ x)) (ord.identifyTime s u)
        ≤ selfGuardPotential U σ ord := selfGuardPotential_le_at_arm3 htrig hinv.irreflOrd
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U (fun x => rhoSF s u (σ x))
          (ord.identifyTime s u)
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hS3
    have hIU : ∀ x ∈ b.identifyTime s u, x ∈ U :=
      universeClosedAt_identify_at_trigger_oriented hUcl hbU htrig
    have hc'U : (b.identifyTime s u).toFinset.card ≤ U.card :=
      card_le_of_subset_universe hIU
    have hIsucc : mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
        (ord.identifyTime s u) + 1 ≤ mintTimeBudget U σ b ord := by
      simp only [mintTimeBudget]; omega
    have hEmul : (mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) + 1) * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hIsucc
    have hEexp : (mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) + 1) * U.card
        = mintTimeBudget U (fun x => rhoSF s u (σ x)) (b.identifyTime s u)
          (ord.identifyTime s u) * U.card + U.card := by ring
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U (fun x => rhoSF s u (σ x))
          (b.identifyTime s u) (ord.identifyTime s u)
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    obtain ⟨hmaxk, hmink, hminmax⟩ := firstIncomparablePair_spec_oriented htrig
    obtain ⟨hk1, hk2, hne21, -, -⟩ := firstIncomparablePair_spec htrig
    have hfix' : SigmaFormulaFixed (fun x => rhoSF s u (σ x)) (b.identifyTime s u) :=
      sigmaFormulaFixed_identifyOriented (ord := ord) (Ne.symm hne21) hmaxk hfix
    have hnextle : b.nextTime ≤ (b.identifyTime s u).nextTime :=
      nextTime_le_identifyTime_oriented b ord t₁ t₂
    have hfrom' : SigmaFixesFormulasFrom (fun x => rhoSF s u (σ x)) (b.identifyTime s u).nextTime :=
      sigmaFixesFormulasFrom_comp (sigmaFixesFormulasFrom_mono hfrom hnextle)
        (retired_lt_nextTime_oriented (b := b) ord hk1 hk2)
    refine ⟨fun x => rhoSF s u (σ x), ⟨hinvp, hIU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega

/-- **The measure drops at `.extended` and at every arm of a `.split`, at the formula-level
state.** `budgetPotentialAt_step_unordered` re-proved against `MintPaysForTimeFixed`. The three
disjunct cases are byte-identical; the edits are confined to the σ layer — `hstab` is now
`sigmaFixed_of_sigmaFormulaFixed`, and the successor's two clauses come from
`sigmaFormulaFixed_grow_of_fixesFrom` and `sigmaFixesFormulasFrom_mono`, on the same two supplies
(`unorderedSuccessor_time_dichotomy` and `nextTime_monotone_along_run`) the time-level proof uses.

That the transcription is this mechanical is the content of the repair's cost claim: strengthening
the σ hypothesis from times to formulas is free at every step, because `rhoSF` is the identity on
formulas away from the one index it retires. -/
theorem budgetPotentialAt_step_unordered_fixed {U : Finset SignedFormula} {Tmax : Nat}
    {σ : SignedFormula → SignedFormula} {b nb : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hUcl : UniverseClosedAt fc U) (hmint : MintPaysForTimeFixed fc U Tmax)
    (hst : BudgetStateFixed U Tmax σ b ord)
    (hmem : nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1)
    (hgrow : b.toFinset.card < nb.toFinset.card) :
    BudgetStateFixed U Tmax σ nb (expandOnceUnblocked b ord fc tr).2 ∧
      budgetPotentialAt U Tmax σ nb (expandOnceUnblocked b ord fc tr).2
        < budgetPotentialAt U Tmax σ b ord := by
  obtain ⟨hinv, hbU, hbud, hfix, hfrom⟩ := hst
  have hstab : SigmaFixed σ b := sigmaFixed_of_sigmaFormulaFixed hfix
  have hfix' : SigmaFormulaFixed σ nb :=
    sigmaFormulaFixed_grow_of_fixesFrom hfix hfrom (fun t ht =>
      (unorderedSuccessor_time_dichotomy hinv.ordTimesKnown nb hmem t ht).imp id
        (fun h => le_of_eq h.symm))
  have hfrom' : SigmaFixesFormulasFrom σ nb.nextTime :=
    sigmaFixesFormulasFrom_mono hfrom (nextTime_monotone_along_run.1 nb hmem)
  have hnbU : ∀ x ∈ nb, x ∈ U := hUcl.1 b ord tr hbU nb hmem
  have hinv' : RunInvariant nb (expandOnceUnblocked b ord fc tr).2 :=
    (expandOnceUnblocked_runInvariant hinv).1 nb hmem
  have hm' : mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
      ≤ mintPotential U σ b ord := mintPotential_expandOnceUnblocked nb hmem
  have hs' : selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
      ≤ selfGuardPotential U σ ord := selfGuardPotential_le_of_grow expandOnceUnblocked_ord_mono
  have hcU : b.toFinset.card ≤ U.card := card_le_of_subset_universe hbU
  have hc'U : nb.toFinset.card ≤ U.card := card_le_of_subset_universe hnbU
  rcases hmint σ b ord tr hinv hbU hstab nb hmem with ⟨hk, hR⟩ | ⟨hI, hmlt⟩ | ⟨hbud3, hslt⟩
  · -- disjunct 1
    have hI : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
        ≤ mintTimeBudget U σ b ord := by simp only [mintTimeBudget]; omega
    have hEmul : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hAmul : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        ≤ 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord := Nat.mul_le_mul_left _ hm'
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hs'
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance]
    omega
  · -- disjunct 2: the landed case, with the fourth component along for the ride
    have hkT : nb.knownTimes.toFinset.card ≤ Tmax := by
      simp only [mintTimeBudget] at hI hbud; omega
    have hp' : (incompPairs nb (expandOnceUnblocked b ord fc tr).2).card ≤ Tmax * Tmax :=
      le_trans (incompPairs_card_le _ _) (Nat.mul_le_mul hkT hkT)
    have hEmul : mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
        ≤ mintTimeBudget U σ b ord * U.card := Nat.mul_le_mul_right _ hI
    have hSmul : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord :=
      Nat.mul_le_mul_left _ hs'
    have hg1 : (nb.knownTimes.toFinset.card + mintPotential U σ nb
          (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord) * (Tmax * Tmax + 1) := by
      refine Nat.mul_le_mul_right _ ?_
      simpa only [mintTimeBudget] using hI
    have hg3 : (mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        ≤ mintPotential U σ b ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hmlt
    have he1 : (nb.knownTimes.toFinset.card + mintPotential U σ nb
          (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        = nb.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have he2 : (b.knownTimes.toFinset.card + mintPotential U σ b ord) * (Tmax * Tmax + 1)
        = b.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    have he3 : (mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + (Tmax * Tmax + 1) := by ring
    have he4 : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have he5 : 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord
        = mintPotential U σ b ord * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance, splitOrderedRank]
    omega
  · -- disjunct 3: the fourth component carries the step on its own
    have hbud3' : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2)
        + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord)
          + selfGuardPotential U σ ord := by
      simpa only [mintTimeBudget] using hbud3
    have hkT : nb.knownTimes.toFinset.card ≤ Tmax := by
      simp only [mintTimeBudget] at hbud; omega
    have hp' : (incompPairs nb (expandOnceUnblocked b ord fc tr).2).card ≤ Tmax * Tmax :=
      le_trans (incompPairs_card_le _ _) (Nat.mul_le_mul hkT hkT)
    have h1 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * (Tmax * Tmax + 1) :=
      Nat.mul_le_mul_right _ hbud3'
    have h3 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * U.card
        ≤ (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * U.card :=
      Nat.mul_le_mul_right _ hbud3'
    have h2 : mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
        ≤ mintPotential U σ b ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hm'
    have h4 : (selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        ≤ selfGuardPotential U σ ord * (Tmax * Tmax + 1) := Nat.mul_le_mul_right _ hslt
    have e1 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * (Tmax * Tmax + 1)
        = nb.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            * (Tmax * Tmax + 1) := by ring
    have e2 : (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * (Tmax * Tmax + 1)
        = b.knownTimes.toFinset.card * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * (Tmax * Tmax + 1) := by ring
    have e3 : (nb.knownTimes.toFinset.card
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2) * U.card
        = mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2 * U.card
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * U.card := by
      simp only [mintTimeBudget]; ring
    have e4 : (b.knownTimes.toFinset.card + mintPotential U σ b ord
          + selfGuardPotential U σ ord) * U.card
        = mintTimeBudget U σ b ord * U.card + selfGuardPotential U σ ord * U.card := by
      simp only [mintTimeBudget]; ring
    have e5 : (selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 + 1)
          * (Tmax * Tmax + 1)
        = selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + (Tmax * Tmax + 1) := by ring
    have e6 : 2 * (Tmax * Tmax + 1) * mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
        = mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1) := by
      ring
    have e7 : 2 * (Tmax * Tmax + 1) * mintPotential U σ b ord
        = mintPotential U σ b ord * (Tmax * Tmax + 1)
          + mintPotential U σ b ord * (Tmax * Tmax + 1) := by ring
    have e8 : (2 * (Tmax * Tmax + 1) + U.card)
          * selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
        = selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * (Tmax * Tmax + 1)
          + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2 * U.card := by ring
    have e9 : (2 * (Tmax * Tmax + 1) + U.card) * selfGuardPotential U σ ord
        = selfGuardPotential U σ ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * (Tmax * Tmax + 1)
          + selfGuardPotential U σ ord * U.card := by ring
    refine ⟨⟨hinv', hnbU, by omega, hfix', hfrom'⟩, ?_⟩
    simp only [budgetPotentialAt, budgetPotential, extensionAllowance, splitOrderedRank]
    omega

/-- **The per-step bundle at the formula-level state.** -/
theorem stepDecreases_budgetPotentialAt_fixed {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax D β : Nat} (hβ : 3 ≤ β)
    (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U Tmax) :
    StepDecreases fc (BudgetStateFixed U Tmax) (budgetPotentialAt U Tmax) D β := by
  intro σ b ord tr hst
  refine ⟨?_, ?_, ?_⟩
  · intro nb hres
    have hmem : nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1 := by
      rw [hres]; simp [unorderedSuccessorBranches]
    exact ⟨σ, budgetPotentialAt_step_unordered_fixed hUcl hmint hst hmem
      (expandOnceUnblocked_card_lt hres)⟩
  · intro bs hres
    have hmem : ∀ nb ∈ bs,
        nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1 := by
      intro nb hnb; rw [hres]; simpa [unorderedSuccessorBranches] using hnb
    refine ⟨le_trans (expandOnceUnblocked_split_arity_le hres) hβ, ?_, ?_⟩
    · intro nb hnb
      exact (hD b ord tr hst.2.1).1 nb (hmem nb hnb)
    · intro nb hnb
      exact ⟨σ, budgetPotentialAt_step_unordered_fixed hUcl hmint hst (hmem nb hnb)
        (expandOnceUnblocked_split_card_lt hres hnb)⟩
  · intro bs hres
    have harity : bs.length ≤ β := by
      obtain ⟨t₁, t₂, -, rfl⟩ := expandOnceUnblocked_splitOrdered_shape hres
      simpa using hβ
    exact ⟨harity, (hD b ord tr hst.2.1).2 bs hres,
      budgetPotentialAt_step_splitOrdered_fixed hUcl hst hres⟩

/-- The measure sits under the same path bound: the repair changes no figure. -/
theorem budgetPotentialAt_lt_mintPathBoundAt_fixed {U : Finset SignedFormula}
    {Tmax mintBudget : Nat} {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hst : BudgetStateFixed U Tmax σ b ord) (hmb : 8 * U.card ≤ mintBudget) :
    budgetPotentialAt U Tmax σ b ord < mintPathBoundAt U.card Tmax mintBudget :=
  budgetPotentialAt_lt_mintPathBoundAt (budgetStateAt_of_budgetStateFixed hst) hmb

/-- `BudgetedTotalitySelfGuarded` at the formula-level state: identical figures throughout. -/
def BudgetedTotalityFixed (fc : FormalSystem.ProofSystem.FrameClass)
    (U : Finset SignedFormula) (mintBudget Tmax D β : Nat) : Prop :=
  ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker) (applied : AppliedSet)
    (maxBranches branchesUsed : Nat),
    (∀ x ∈ b, x ∈ U) →
    RunInvariant b ord →
    10 * U.card ≤ mintBudget →
    b.knownTimes.toFinset.card + mintBudget ≤ Tmax →
    branchesUsed + β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches →
    (expandBranchWithFuel b (mintAwareFuelAt U.card Tmax mintBudget D β) ord fc tr applied
      maxBranches branchesUsed).isSome = true

theorem expandBranchWithFuel_isSome_of_budget_fixed
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat}
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U Tmax) (harm : ArmSettlement fc) :
    BudgetedTotalityFixed fc U mintBudget Tmax D β := by
  intro b ord tr applied maxBranches branchesUsed hbU hinv hmb hT hbud
  have hst : BudgetStateFixed U Tmax id b ord := by
    refine ⟨hinv, hbU, ?_, sigmaFormulaFixed_id b, sigmaFixesFormulasFrom_id _⟩
    have h8 := mintPotential_le_eight_mul U id b ord
    have h2 := selfGuardPotential_le_two_mul U id ord
    simp only [mintTimeBudget]
    omega
  exact expandBranchWithFuel_isSome_of_measure (by omega)
    (stepDecreases_budgetPotentialAt_fixed hβ hUcl hD hmint)
    harm (mintPathBoundAt U.card Tmax mintBudget) id _ b ord tr applied maxBranches branchesUsed
    hst (budgetPotentialAt_lt_mintPathBoundAt_fixed hst (by omega)) (Nat.le_refl _) hbud

/-- **THE TERMINUS, at the formula-level repaired predicate.** -/
theorem buildTableauAt_isSome_of_budget_fixed
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget D β) fc maxBranches).isSome
      = true := by
  refine buildTableauAt_isSome_of_settles hpb ?_
  exact expandBranchWithFuel_isSome_of_budget_fixed hβ hUcl hD hmint
    (armSettlement_of_postBlockingSettles hpb)
    (seedBranch phi) TimeOrdering.empty EventualityTracker.empty {} maxBranches 0
    hseed (runInvariant_initial _) hmb hT (by omega)

theorem buildTableauAt_isSome_at_seed_fixed
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {D β : Nat}
    (phi : Formula) (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U)
    (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U) :
    (buildTableauAt phi
        (mintAwareFuelAt U.card (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card)
          (10 * U.card) D β)
        fc
        (β * mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card) (10 * U.card) D β)
      ).isSome = true :=
  buildTableauAt_isSome_of_budget_fixed phi _ hβ hUcl hD hmint hpb hseed (Nat.le_refl _)
    (derivedTmaxAt_spec (seedBranch phi) U) (Nat.le_refl _)

theorem buildTableauAt_isSome_of_lengthBudget_fixed
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax L β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hL : StepLengthBounded fc U L)
    (hmint : MintPaysForTimeFixed fc U Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget (difficultyCeiling U L) β
      ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget (difficultyCeiling U L) β) fc
        maxBranches).isSome = true :=
  buildTableauAt_isSome_of_budget_fixed phi maxBranches hβ hUcl
    (difficultyBounded_of_stepLengthBounded_at hL hUcl) hmint hpb hseed hmb hT hbud

theorem buildTableauAt_isSome_at_seed_lengthBudget_fixed
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {L β : Nat}
    (phi : Formula) (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U)
    (hL : StepLengthBounded fc U L)
    (hmint : MintPaysForTimeFixed fc U
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U) :
    (buildTableauAt phi
        (mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card)
          (10 * U.card) (difficultyCeiling U L) β)
        fc
        (β * mintAwareFuelAt U.card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) U.card) (10 * U.card)
          (difficultyCeiling U L) β)
      ).isSome = true :=
  buildTableauAt_isSome_at_seed_fixed phi hβ hUcl
    (difficultyBounded_of_stepLengthBounded_at hL hUcl) hmint hpb hseed

/-- **Seed-level terminus 1, at the formula-level repaired predicate.** -/
theorem buildTableauAt_isSome_of_lengthBudget_signedUniverse_fixed
    {fc : FormalSystem.ProofSystem.FrameClass}
    {C : Finset Formula} {L : Finset Label} {mintBudget Tmax L' β : Nat}
    (phi : Formula) (maxBranches : Nat) (hβ : 3 ≤ β)
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hlab : UnorderedSuccessorLabelClosed fc L)
    (hSL : StepLengthBounded fc (signedUniverse C L) L')
    (hmint : MintPaysForTimeFixed fc (signedUniverse C L) Tmax) (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ signedUniverse C L)
    (hmb : 10 * (signedUniverse C L).card ≤ mintBudget)
    (hT' : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt (signedUniverse C L).card Tmax mintBudget
      (difficultyCeiling (signedUniverse C L) L') β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt (signedUniverse C L).card Tmax mintBudget
        (difficultyCeiling (signedUniverse C L) L') β) fc maxBranches).isSome = true :=
  buildTableauAt_isSome_of_lengthBudget_fixed phi maxBranches hβ
    (universeClosedAt_signedUniverse_of_headroom hC hT hL hlab) hSL hmint hpb hseed hmb hT' hbud

/-- **Seed-level terminus 2, at the formula-level repaired predicate.** -/
theorem buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_fixed
    {fc : FormalSystem.ProofSystem.FrameClass}
    {C : Finset Formula} {L : Finset Label} {L' β : Nat} (phi : Formula) (hβ : 3 ≤ β)
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hlab : UnorderedSuccessorLabelClosed fc L)
    (hSL : StepLengthBounded fc (signedUniverse C L) L')
    (hmint : MintPaysForTimeFixed fc (signedUniverse C L)
      (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card) (signedUniverse C L).card))
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ signedUniverse C L) :
    (buildTableauAt phi
        (mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
        fc
        (β * mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
      ).isSome = true :=
  buildTableauAt_isSome_at_seed_lengthBudget_fixed phi hβ
    (universeClosedAt_signedUniverse_of_headroom hC hT hL hlab) hSL hmint hpb hseed

/-! #### The formula-level predicate discharged, and the boundary at which it stops

The boundary is inherited verbatim from `mintPaysForTimeStable_empty`, and for the same reason:
confinement forces the branch empty, the engine reports `.saturated`, and
`unorderedSuccessorBranches` of a `.saturated` result is `[]`. What is **not** inherited is the
refutation — `flatSigma_not_sigmaFixed` decides that the vehicle above does not reach this
predicate, so the boundary is where the discharge currently stops rather than where it is known to
fail.

**What a nonempty discharge needs, precisely, and what is already available.** For the six rules in
`freshLabelRules ∩ freshTimeRules` disjunct 2 is now supplied at the pick, by
`mintPotential_lt_of_pick_linear_sigmaFixed` and `mintPotential_lt_of_pick_branching_sigmaFixed`.
For the two rules of `selfGuardRules` disjunct 3 is supplied by `selfGuardPotential_lt_of_untlNeg`
and `selfGuardPotential_lt_of_snceNeg`, whose σ-hit comes from `SigmaFixed` a fortiori. For the
twenty-seven rules outside `freshTimeRules`, `applyRule_emitted_time_dichotomy` says the step emits
at no new time, which is disjunct 1's first conjunct, and `expandOnceUnblocked_ord_mono` gives the
second. What is missing is the **engine-level assembly**: threading the pick's rule through
`expandOnceUnblocked`'s three stages so that the case split above is available at the successor,
for every rule at once.

**And the one rule none of that reaches.** `densityRule`. It mints a fresh time and lies outside
both `freshLabelRules` and `selfGuardRules`, so no disjunct moves at a `densityRule` step for any σ
whatsoever — the assembly above therefore delivers a discharge only at frame classes where
`denseRules` cannot fire, and the intended second component `gapPotential` (indexed by `U ×ˢ U`,
`denseRules`-gated) remains implemented nowhere and assumed by nothing. Neither the assembly nor
`gapPotential` is attempted here; both are stated as named next steps. See register entry 20.

**Where that boundary has since moved.** Section D3 discharges the predicate — and its unrepaired
original — at every universe of `untl`/`snce`-free formulas, hence at a nonempty
`signedUniverse C L`, at every frame class. Neither the assembly nor `gapPotential` is needed
there, because both are obligations on a time mint and no rule of `freshTimeRules` is applicable to
such a formula: every one of the nine is gated on a shape carrying an `untl` or `snce` node, and
`densityRule` is excluded by that gate before its `Dense ≤ fc` gate is consulted. So what the two
named next steps actually gate is the discharge at a universe carrying a **temporal** operator. -/

/-- **The satisfiability boundary, at the formula-level predicate.** -/
theorem mintPaysForTimeFixed_empty (fc : FormalSystem.ProofSystem.FrameClass) (Tmax : Nat) :
    MintPaysForTimeFixed fc ∅ Tmax :=
  mintPaysForTimeFixed_of_mintPaysForTimeStable (mintPaysForTimeStable_empty fc Tmax)

/-- **The formula-level predicate, discharged at a concrete `signedUniverse C L`**, at every frame
class and every `Tmax`. The instantiation the seed-level termini above consume, at the same
boundary `mintPaysForTime_empty` and `mintPaysForTimeStable_signedUniverse_empty` record.

Superseded on the `untl`/`snce`-free fragment by
`mintPaysForTimeFixed_signedUniverse_untlSnceFree`, which drops the `L = ∅` restriction entirely;
retained because it is the boundary statement of the empty-universe series and because it holds for
every `C` whatsoever, temporal formulas included. -/
theorem mintPaysForTimeFixed_signedUniverse_empty
    (fc : FormalSystem.ProofSystem.FrameClass) (C : Finset Formula) (Tmax : Nat) :
    MintPaysForTimeFixed fc (signedUniverse C (∅ : Finset Label)) Tmax :=
  mintPaysForTimeFixed_of_mintPaysForTimeStable
    (mintPaysForTimeStable_signedUniverse_empty fc C Tmax)

/-! ## C11. Clause 1's label dimension, discharged from branch-side headroom

**What this section spends.** Section C10 left clause 1's label dimension as the named residual
`UnorderedSuccessorLabelClosed`, and its obligation map recorded one coordinate as available and one
as absent: the world coordinate had `applyRule_emitted_world_dichotomy`, and the time coordinate had
no statement at all bounding the times a rule emits at. Section D1 has since landed exactly that
statement — `applyRule_emitted_time_dichotomy`, together with the engine-level
`unorderedSuccessor_time_dichotomy`. This section spends it, and the accounting is now complete in
both coordinates.

**What completing the accounting does and does not buy.** It buys the *reduction*: the label
dimension of every unordered successor follows from a branch-side headroom condition, as a theorem
(`unorderedSuccessor_label_mem_of_headroom`), with nothing left unaccounted. It does **not** buy the
residual's discharge, and no lemma could have: clause 1 is *refuted* at a fixed finite
`signedUniverse C L` (`universeClosed_fresh_world_escapes`), and no condition on `L` repairs it
(`freshWorldHeadroom_not_universal`). So the residual survives — but it survives for a proved reason
rather than for a missing lemma, and that is the difference this section makes. The honest bracket is
stated as `freshLabelHeadroom_not_universal`.

**The rectangle, and why the world condition alone was never enough.** A label is a *pair*. The two
dichotomies are per-coordinate: a successor's worlds lie in `b.worldFinset ∪ {b.nextWorld}` and its
times lie in `b.knownTimes ∪ {b.nextTime}`, but nothing correlates the two, so four quadrants have to
be covered rather than two. `FreshWorldHeadroom` covers one of them. Confinement of `b` covers *not
even one*: `∀ x ∈ b, x.label ∈ L` says the pairs `b` actually carries are in `L`, which does not put
`⟨w, t⟩` in `L` for a `w` and a `t` that `b` carries on different formulas. `FreshLabelHeadroom` is
the rectangle the two dichotomies actually license, and `freshWorldHeadroom_of_freshLabelHeadroom`
records that it is the strictly stronger of the two. This is the same rectangle shape
`timeMergeClosed_iff_product` found on the clause-2 side, arrived at from the opposite direction. -/

/-- **The world dichotomy at engine level.** Every world an unordered successor mentions is a world
`b` mentioned, or `b.nextWorld`. One step adds at most the one fresh world, and never more.

The exact counterpart of `unorderedSuccessor_time_dichotomy`, assembled the same way and through the
same invariant-agnostic machinery — `pick_branches_eq`, `pick_stage_source`, `resultBranch_sub` — so
the three-stage pick is not destructured a second time. It carries **no** auxiliary hypothesis where
its time twin carries `OrdTimesKnown b ord`: `applyRule_emitted_world_dichotomy` needs nothing, since
no rule propagates a world through the `TimeOrdering` the way four of them propagate times through
`futureOf` / `pastOf`. See `applyRule_emitted_time_mem_ordTimesKnown_needed` for why the asymmetry is
real rather than an artifact of the proof. -/
private theorem pickBranches_world_dichotomy {b : Branch} {ord : TimeOrdering}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o)) :
    ∀ nb ∈ pickBranches b p, ∀ w ∈ nb.worldFinset, w ∈ b.worldFinset ∨ w = b.nextWorld := by
  rcases p with _ | ⟨r, res, o⟩
  · simp [pickBranches]
  · obtain ⟨sf, hsf, hA⟩ := hp r res o rfl
    intro nb hnb w hwm
    obtain ⟨-, hsub⟩ := resultBranch_sub (b := b) (nb := nb) (res := res) hnb
    obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_worldFinset hwm
    rcases hsub x hx with hxe | hxb
    · refine applyRule_emitted_world_dichotomy (rule := r) (sf := sf) (ord := ord) hsf x ?_
      rw [hA]
      exact hxe
    · exact Or.inl (Branch.mem_worldFinset hxb)

/-- **The world dichotomy, at the shape clause 1 quantifies at.** Every world an unordered successor
mentions is one `b` mentioned or `b.nextWorld`.

This is the world-coordinate half of the label accounting, at engine level. Its time twin is
`unorderedSuccessor_time_dichotomy`; together they are what
`unorderedSuccessor_label_mem_of_headroom` consumes. -/
theorem unorderedSuccessor_world_dichotomy {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker} :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ w ∈ nb.worldFinset, w ∈ b.worldFinset ∨ w = b.nextWorld := by
  have keyB : unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1
      = pickBranches b
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_branches_eq
  rw [keyB]
  exact pickBranches_world_dichotomy (pick_stage_source b ord fc tr)

/-- **The branch-side headroom condition the label dimension actually needs**: the rectangle spanned
by the branch's worlds-plus-one against its times-plus-one lies in `L`.

Stated in exactly the shape the two dichotomies deliver — a disjunction per coordinate — so that no
step of `unorderedSuccessor_label_mem_of_headroom` has to reconcile a `Finset` form with a `List`
form. Four quadrants, not two, because the dichotomies are per-coordinate and nothing correlates
them; and the quadrant `⟨w, t⟩` with `w` and `t` both already on `b` is **not** free, because
confinement of `b` constrains the pairs `b` carries and not their cross product.

`FreshWorldHeadroom` is the third quadrant alone (`freshWorldHeadroom_of_freshLabelHeadroom`). Like
it, this is a condition on the **branch**: `freshLabelHeadroom_not_universal` proves it cannot be
moved into `L`. -/
def FreshLabelHeadroom (L : Finset Label) (b : Branch) : Prop :=
  ∀ w, (w ∈ b.worldFinset ∨ w = b.nextWorld) →
    ∀ t, (t ∈ b.knownTimes ∨ t = b.nextTime) → (⟨w, t⟩ : Label) ∈ L

/-- The rectangle condition is the strictly stronger of the two headroom conditions: it is
`FreshWorldHeadroom` plus the three quadrants that one omits. -/
theorem freshWorldHeadroom_of_freshLabelHeadroom {L : Finset Label} {b : Branch}
    (h : FreshLabelHeadroom L b) : FreshWorldHeadroom L b :=
  fun t ht => h b.nextWorld (Or.inr rfl) t (Or.inl ht)

/-- **Clause 1's label dimension, discharged.** Every formula on every unordered successor of an
`L`-confined branch with headroom sits at a label of `L`.

This is the statement the Phase 7 blocker named, and it is now a theorem rather than a hypothesis.
Both coordinates are accounted for and neither is assumed: `unorderedSuccessor_world_dichotomy` for
the world, `unorderedSuccessor_time_dichotomy` for the time, `FreshLabelHeadroom` for the four
quadrants they leave. Nothing else is used — in particular, confinement of `b` is **not** among the
hypotheses, because the headroom rectangle already subsumes what confinement would have supplied.

`OrdTimesKnown b ord` is inherited from the time dichotomy and is not new currency:
`ordTimesKnown_empty` supplies it at a run's seed and `expandOnceUnblocked_ordTimesKnown` propagates
it across every step, so nothing reaches the terminus that was not already there. -/
theorem unorderedSuccessor_label_mem_of_headroom {L : Finset Label} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (haux : OrdTimesKnown b ord) (hh : FreshLabelHeadroom L b) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ x ∈ nb, x.label ∈ L := by
  intro nb hnb x hx
  exact hh x.label.world
    (unorderedSuccessor_world_dichotomy nb hnb x.label.world (Branch.mem_worldFinset hx))
    x.label.time
    (unorderedSuccessor_time_dichotomy haux nb hnb x.label.time (mem_knownTimes_of_mem hx))

/-- **Clause 1 at `signedUniverse C L`, both dimensions, with no residual left standing.**

The composite the Phase 7 blocker was blocking. `TableauClosed C` and `TrichStock C` discharge the
formula coordinate via `unorderedSuccessor_formula_mem`; `FreshLabelHeadroom L b` discharges the
label coordinate via `unorderedSuccessor_label_mem_of_headroom`. Contrast
`unorderedSuccessor_confined_signedUniverse_of_headroom`, which is the same statement carrying
`UnorderedSuccessorLabelClosed fc L` as an unanalyzed hypothesis: that one is retained verbatim and
is what the landed terminus chain consumes; this one is the analysis of it.

The two are not interchangeable, and the difference is exactly the quantifier. This form is
**per-branch**: the headroom is a hypothesis about the `b` in front of it. The residual form
quantifies over every `L`-confined branch at once, and in that position the headroom is *refutable*
(`freshLabelHeadroom_not_universal`). So this theorem does not discharge the residual — see the
section note. -/
theorem unorderedSuccessor_confined_signedUniverse_of_freshLabelHeadroom {C : Finset Formula}
    {L : Finset Label} {fc : FormalSystem.ProofSystem.FrameClass}
    (hC : TableauClosed C) (hT : TrichStock C) :
    ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker),
      OrdTimesKnown b ord → FreshLabelHeadroom L b →
      (∀ x ∈ b, x ∈ signedUniverse C L) →
      ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1, ∀ x ∈ nb,
        x ∈ signedUniverse C L := by
  intro b ord tr haux hh hb nb hnb x hx
  have hbf : ∀ y ∈ b, y.formula ∈ C :=
    fun y hy => (formula_label_of_mem_signedUniverse (hb y hy)).1
  exact mem_signedUniverse
    (unorderedSuccessor_formula_mem hC hT hbf nb hnb x hx)
    (unorderedSuccessor_label_mem_of_headroom haux hh nb hnb x hx)

/-- **The residual, restated with the ordering hypothesis the time coordinate needs.**

`UnorderedSuccessorLabelClosed` quantifies over an arbitrary `TimeOrdering` with nothing tying it to
the branch, which is one hypothesis short of what `unorderedSuccessor_time_dichotomy` asks. This is
the same predicate with `OrdTimesKnown b ord` added, and it is therefore the *weaker* of the two —
`unorderedSuccessorLabelClosedOrd_of_unorderedSuccessorLabelClosed` records the implication. The
original is retained verbatim and is what the landed chain consumes; this one exists so that the
reduction below can be stated at all.

The added hypothesis is not a new cost at any consuming site:
`applyRule_emitted_time_mem_ordTimesKnown_needed` shows it is not removable, `ordTimesKnown_empty`
supplies it at a seed, and `expandOnceUnblocked_ordTimesKnown` propagates it. -/
def UnorderedSuccessorLabelClosedOrd (fc : FormalSystem.ProofSystem.FrameClass)
    (L : Finset Label) : Prop :=
  ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker), OrdTimesKnown b ord →
    (∀ x ∈ b, x.label ∈ L) →
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1, ∀ x ∈ nb, x.label ∈ L

/-- The ordering-hypothesis form is implied by the original, as adding a hypothesis always does. -/
theorem unorderedSuccessorLabelClosedOrd_of_unorderedSuccessorLabelClosed
    {fc : FormalSystem.ProofSystem.FrameClass} {L : Finset Label}
    (h : UnorderedSuccessorLabelClosed fc L) : UnorderedSuccessorLabelClosedOrd fc L :=
  fun b ord tr _ hbl => h b ord tr hbl

/-- **The reduction, complete.** The residual follows from branch-side headroom on every `L`-confined
branch. No coordinate is left unaccounted, and no hypothesis, placeholder or unfinished step stands
the two.

This is what section D1's arrival makes provable. Read together with
`freshLabelHeadroom_not_universal` it is also the *end* of the line: the antecedent is refutable at
every nonempty `L`, so the reduction is complete without being a discharge. -/
theorem unorderedSuccessorLabelClosedOrd_of_headroom
    {fc : FormalSystem.ProofSystem.FrameClass} {L : Finset Label}
    (h : ∀ b : Branch, (∀ x ∈ b, x.label ∈ L) → FreshLabelHeadroom L b) :
    UnorderedSuccessorLabelClosedOrd fc L :=
  fun b _ _ haux hbl => unorderedSuccessor_label_mem_of_headroom haux (h b hbl)

/-- **The rectangle cannot be moved into `L` either**, at every nonempty finite `L`.

Immediate from `freshWorldHeadroom_not_universal` through
`freshWorldHeadroom_of_freshLabelHeadroom`: the rectangle is the stronger condition, so refuting the
weaker one refutes it too. Stated separately because it is the load-bearing half of this section's
verdict — `unorderedSuccessorLabelClosedOrd_of_headroom` reduces the residual to exactly this
antecedent, and this says the antecedent is unavailable wherever the terminus is not vacuous.

So `UnorderedSuccessorLabelClosed` remains a residual, and now for a *proved* reason rather than for
a missing lemma. Register entry 11 records the finding; entry 21 records this refinement of it. -/
theorem freshLabelHeadroom_not_universal (L : Finset Label) (hne : L.Nonempty) :
    ¬ (∀ b : Branch, (∀ x ∈ b, x.label ∈ L) → FreshLabelHeadroom L b) :=
  fun h => freshWorldHeadroom_not_universal L hne
    fun b hb => freshWorldHeadroom_of_freshLabelHeadroom (h b hb)

/-- **The weakened residual is still refutable**, so the reduction above is not a reduction to
something already true.

The same witness `unorderedSuccessorLabelClosed_not_universal` uses, with the added ordering
hypothesis supplied by `ordTimesKnown_empty` — the witness runs at `TimeOrdering.empty`, so nothing
had to be rebuilt. Adding `OrdTimesKnown` to the residual therefore does not weaken it into
vacuity. -/
theorem unorderedSuccessorLabelClosedOrd_not_universal
    (fc : FormalSystem.ProofSystem.FrameClass) :
    ¬ UnorderedSuccessorLabelClosedOrd fc freshWorldLabels := by
  intro h
  have hstep := expandOnceUnblocked_freshWorldBranch fc EventualityTracker.empty
  have hmem : (freshWorldEmitted ++ freshWorldBranch)
      ∈ unorderedSuccessorBranches
        (expandOnceUnblocked freshWorldBranch TimeOrdering.empty fc
          EventualityTracker.empty).1 := by
    rw [hstep]; simp [unorderedSuccessorBranches]
  have hbl : ∀ y ∈ freshWorldBranch, y.label ∈ freshWorldLabels := by
    intro y hy
    simp only [freshWorldBranch, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    simp [freshWorldLabels, freshWorldWitness, SignedFormula.neg]
  have hbad := h freshWorldBranch TimeOrdering.empty EventualityTracker.empty
    (ordTimesKnown_empty freshWorldBranch) hbl _ hmem
    (SignedFormula.neg fwp ⟨1, 0⟩) (by simp [freshWorldEmitted])
  simp [freshWorldLabels, SignedFormula.neg, Label.initial] at hbad

/-! ### The refutation generalizes: **every** nonempty `L`, not merely one witness

`unorderedSuccessorLabelClosed_not_universal` and `unorderedSuccessorLabelClosedOrd_not_universal`
refute the residual at one particular label set, `freshWorldLabels = {⟨0,0⟩}`. That is enough to
show it is not a theorem, but it leaves open the reading — which the earlier phrasing of register
entry 11 invited — that the residual might hold at *other* label sets, so that a consuming site
could be repaired by choosing `L` more carefully.

It cannot. The generalization is mechanical, and for a structural reason: the engine's shape gates
match a signed formula's **sign and formula constructor**, never its label. So `F(□p)` fires
`.boxNeg` at every label, not only at `Label.initial`, and what the rule emits always sits at the
branch's `Branch.nextWorld`, which at a one-formula branch labelled `l` is `l.world + 1` — this is
what `arAt_bn` below records, by `rfl`, with `l` a free variable. Running the witness at a label of
**maximal world** in `L` therefore puts the emission outside `L`'s world projection by maximality,
at every nonempty finite `L` and every frame class.

The other end is immediate: at `L = ∅` the confinement hypothesis `∀ x ∈ b, x.label ∈ L` forces
`b = []`, the pick finds nothing, and the conclusion holds vacuously. So the residual's
satisfiability set is **exactly `{∅}`** — and `∅` is precisely the case in which every theorem
carrying it as a hypothesis has an empty universe and says nothing.

The family below is stated **beside** the `freshWorld*` family, not in place of it: the
single-witness form is what the file's earlier sections cite, and it is not withdrawn. -/

section FreshWorldRefutationAtEveryLabel

/-- `F(□p)` at an arbitrary label — the label-generalized form of `freshWorldWitness`, which is
this at `Label.initial`. -/
def freshWorldWitnessAt (l : Label) : SignedFormula := SignedFormula.neg (Formula.box fwp) l

/-- The witness branch at `l`. One formula, so its only world is `l.world` and its next world is
`l.world + 1`. -/
def freshWorldBranchAt (l : Label) : Branch := [freshWorldWitnessAt l]

/-- What `boxNeg` emits at the witness: `F(p)` at world `l.world + 1`, the fresh world, with the
time coordinate carried across unchanged. -/
def freshWorldEmittedAt (l : Label) : List SignedFormula :=
  [SignedFormula.neg fwp ⟨l.world + 1, l.time⟩]

private theorem iaAt_ug (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .priorUGap (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_sg (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .priorSGap (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_sep (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .sepRule (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_np (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .negPos (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_nn (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .negNeg (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_in (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .impNeg (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_ap (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .andPos (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_on (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .orNeg (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_bp (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .boxPos (freshWorldWitnessAt l) fc = false := rfl
private theorem iaAt_bn (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    isApplicable .boxNeg (freshWorldWitnessAt l) fc = true := rfl
/-- **The label-independence of the emission, stated as a `rfl` fact with `l` free.** This is the
one line that carries the whole generalization: the rule's output is computed from the branch's
`Branch.nextWorld`, and at a one-formula branch that is `l.world + 1` for whatever `l` is. -/
private theorem arAt_bn (l : Label) :
    applyRule .boxNeg (freshWorldWitnessAt l) (freshWorldBranchAt l) TimeOrdering.empty
      = (RuleResult.linear (freshWorldEmittedAt l), TimeOrdering.empty) := rfl
private theorem wpAt_bn (l : Label) :
    witnessPresent .boxNeg (freshWorldWitnessAt l) (freshWorldBranchAt l) TimeOrdering.empty
      = false := rfl
private theorem twAt_bn (l : Label) :
    trivialEventWitnessed .boxNeg (freshWorldWitnessAt l) (freshWorldBranchAt l) TimeOrdering.empty
      = false := rfl

-- `rm_bn` (`ruleMintsFreshLabel .boxNeg = true`) is reused rather than restated: it mentions no
-- witness and no label, so the label-generalized family needs no variant of it.
attribute [local simp] iaAt_ug iaAt_sg iaAt_sep iaAt_np iaAt_nn iaAt_in iaAt_ap iaAt_on iaAt_bp
  iaAt_bn arAt_bn rm_bn wpAt_bn twAt_bn

/-- **`.boxNeg` is the rule the engine picks at the witness, at every frame class and every label.**
Exactly `findApplicableRule_freshWorldWitness`'s argument with `l` free: the nine rules ahead of
`.boxNeg` are inapplicable to a `.neg`-signed box regardless of where it sits, and the Dense and
Discrete blocks are *appended* after the base rules by `allRulesForFC`, so neither can pre-empt it. -/
theorem findApplicableRule_freshWorldWitnessAt
    (fc : FormalSystem.ProofSystem.FrameClass) (l : Label) :
    findApplicableRule (freshWorldWitnessAt l) (freshWorldBranchAt l) TimeOrdering.empty fc
      = some (TableauRule.boxNeg, RuleResult.linear (freshWorldEmittedAt l), TimeOrdering.empty) := by
  simp only [findApplicableRule, allRulesForFC, allRules, rTimeRules]
  by_cases hd : FormalSystem.ProofSystem.FrameClass.RTime ≤ fc
  · simp [hd, List.findSome?]
  · simp [hd, List.findSome?]

/-- **The step fires at the witness, at every frame class, tracker and label.** Blocking is empty
(`blockedTimes_empty`), the pick short-circuits on the single formula, and the result carries a
formula at world `l.world + 1`. -/
theorem expandOnceUnblocked_freshWorldBranchAt
    (fc : FormalSystem.ProofSystem.FrameClass) (tr : EventualityTracker) (l : Label) :
    (expandOnceUnblocked (freshWorldBranchAt l) TimeOrdering.empty fc tr).1
      = ExpansionResult.extended (freshWorldEmittedAt l ++ freshWorldBranchAt l) := by
  have hrule := findApplicableRule_freshWorldWitnessAt fc l
  simp only [freshWorldBranchAt] at hrule
  rw [expandOnceUnblocked]
  simp only [blockedTimes_empty, findUnexpandedUnblockedWith, isExpanded, freshWorldBranchAt,
    List.find?_cons, List.contains_nil, Bool.not_false, Bool.and_true, hrule,
    Option.isNone_some]

/-- **The `Ord` form of the residual is false at every nonempty finite `L`, at every frame class.**

Run the witness at a label `l₀ ∈ L` whose world is maximal in `L.image (·.world)`. The step fires
(`expandOnceUnblocked_freshWorldBranchAt`), the extended branch is an unordered successor, and the
emitted formula sits at world `l₀.world + 1`. If the residual held, that label would be in `L`, so
`l₀.world + 1 ≤ max' (L.image (·.world)) = l₀.world` — impossible.

Stated at the `Ord` form because that is the **weaker** predicate: `OrdTimesKnown` is supplied for
free at `TimeOrdering.empty` by `ordTimesKnown_empty`, so the added hypothesis costs the refutation
nothing, and refuting the weaker predicate refutes the stronger one too. -/
theorem unorderedSuccessorLabelClosedOrd_nonempty_false
    (fc : FormalSystem.ProofSystem.FrameClass) (L : Finset Label) (hne : L.Nonempty) :
    ¬ UnorderedSuccessorLabelClosedOrd fc L := by
  intro h
  have hine : (L.image (·.world)).Nonempty := hne.image _
  obtain ⟨l₀, hl₀, hl₀w⟩ := Finset.mem_image.mp ((L.image (·.world)).max'_mem hine)
  have hstep := expandOnceUnblocked_freshWorldBranchAt fc EventualityTracker.empty l₀
  have hmem : (freshWorldEmittedAt l₀ ++ freshWorldBranchAt l₀)
      ∈ unorderedSuccessorBranches
        (expandOnceUnblocked (freshWorldBranchAt l₀) TimeOrdering.empty fc
          EventualityTracker.empty).1 := by
    rw [hstep]; simp [unorderedSuccessorBranches]
  have hbl : ∀ y ∈ freshWorldBranchAt l₀, y.label ∈ L := by
    intro y hy
    simp only [freshWorldBranchAt, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy
    simpa [freshWorldWitnessAt, SignedFormula.neg] using hl₀
  have hbad := h (freshWorldBranchAt l₀) TimeOrdering.empty EventualityTracker.empty
    (ordTimesKnown_empty (freshWorldBranchAt l₀)) hbl _ hmem
    (SignedFormula.neg fwp ⟨l₀.world + 1, l₀.time⟩) (by simp [freshWorldEmittedAt])
  simp only [SignedFormula.neg] at hbad
  have hle : l₀.world + 1 ≤ (L.image (·.world)).max' hine :=
    Finset.le_max' (L.image (·.world)) (l₀.world + 1)
      (Finset.mem_image.mpr ⟨⟨l₀.world + 1, l₀.time⟩, hbad, rfl⟩)
  rw [hl₀w] at hle
  exact absurd hle (Nat.not_succ_le_self _)

/-- **The residual itself is false at every nonempty finite `L`, at every frame class.**

One line from the `Ord` form through
`unorderedSuccessorLabelClosedOrd_of_unorderedSuccessorLabelClosed`, so the file carries a single
refutation argument rather than two copies of it.

This is the statement any downstream artifact should cite. It says that
`unorderedSuccessorLabelClosed_not_universal`'s single witness was not a peculiarity of
`freshWorldLabels`: there is no finite nonempty label set at which the residual can be assumed, and
so every theorem carrying it as a live hypothesis is a vacuously true conditional wherever its
universe is nonempty. -/
theorem unorderedSuccessorLabelClosed_nonempty_false
    (fc : FormalSystem.ProofSystem.FrameClass) (L : Finset Label) (hne : L.Nonempty) :
    ¬ UnorderedSuccessorLabelClosed fc L :=
  fun h => unorderedSuccessorLabelClosedOrd_nonempty_false fc L hne
    (unorderedSuccessorLabelClosedOrd_of_unorderedSuccessorLabelClosed h)

/-- **And it is true at `∅`** — which, with the refutation above, pins the residual's satisfiability
set to exactly `{∅}`.

Not a discharge in any useful sense: confinement to `∅` forces `b = []`, the pick finds no
unexpanded formula, and `unorderedSuccessorBranches` of a non-firing step is empty, so the
conclusion is quantified over nothing. It is recorded because "refuted at every nonempty `L`" and
"refuted outright" are different statements, and the register should assert the one that is true. -/
theorem unorderedSuccessorLabelClosed_empty
    (fc : FormalSystem.ProofSystem.FrameClass) :
    UnorderedSuccessorLabelClosed fc (∅ : Finset Label) := by
  intro b ord tr hbl nb hnb x hx
  have hb : b = [] := by
    rcases b with _ | ⟨y, ys⟩
    · rfl
    · exact absurd (hbl y (by simp)) (by simp)
  subst hb
  rw [expandOnceUnblocked] at hnb
  simp only [findUnexpandedUnblockedWith, List.find?_nil] at hnb
  simp [unorderedSuccessorBranches] at hnb

end FreshWorldRefutationAtEveryLabel


/-! ## C12. The post-blocking settlement residual: refuted, and repaired

`PostBlockingSettles fc` (section C8) is the last settlement residual on the terminus, and its own
docstring names an open question: whether the gap between what `saturateBlocked` stops at and what
`findUnexpandedUnblockedWith` tests "can be closed by fuel alone". This section decides that
question — the answer is **no** — and lands the repair.

The two tests disagree, and the disagreement has nothing to do with fuel:

* `saturateBlocked` stops at `expandOnceNoFresh`'s `.saturated` verdict (`Saturation.lean`, the
  `(.saturated, _)` arm), and `expandOnceNoFresh` **skips** any candidate whose applicable rule
  mints a fresh label or lengthens the ordering constraints — its `pick` returns `none` for such a
  candidate and the search continues past it.
* `findUnexpandedUnblockedWith` tests `!isExpanded sf b ord fc`, i.e.
  `findApplicableRule sf b ord fc ≠ none`, with **no** reference to label-minting at all.

So a formula sitting at an unblocked time whose only applicable rule mints a fresh label is
invisible to the first test and visible to the second, at **every** fuel figure. That is the
refutation, and it is what the two theorems below decide.
-/

section PostBlockingSettlesRefutation

/-- **`saturateBlocked` at `fuel = 0` returns its input unchanged**, at every branch, ordering and
frame class. This is the `| 0 => some (.inr (b, timeOrd))` arm of `Saturation.lean`'s definition,
recorded here as a named fact because both refutations below run through it. -/
theorem saturateBlocked_fuel_zero (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) :
    saturateBlocked b 0 ord fc = some (.inr (b, ord)) := by
  rw [saturateBlocked]

/-- **The `fuel = 0` half of the witness**: nothing is blocked at the empty ordering, the branch's
one formula has `.impNeg` applicable, so the blocking-aware finder reports it. -/
theorem findUnexpandedUnblockedWith_multBranch_one
    (fc : FormalSystem.ProofSystem.FrameClass) :
    findUnexpandedUnblockedWith (multBranch 1) TimeOrdering.empty fc
        (blockedTimes (multBranch 1) TimeOrdering.empty fc (armTracker (multBranch 1)))
      = some multWitness := by
  have hrule := findApplicableRule_multWitness (multBranch 1) (pos_not_mem_multBranch 1) fc
  rw [blockedTimes_empty]
  have hb : multBranch 1 = multWitness :: ([] : Branch) := by
    simp [multBranch, List.replicate]
  simp only [findUnexpandedUnblockedWith, isExpanded]
  rw [hb, List.find?_cons]
  simp only [← hb, hrule, Option.isNone_some, List.contains_nil, Bool.not_false, Bool.and_true]

/-- **Gate 1: `PostBlockingSettles fc` is refuted at the `fuel = 0` arm**, at every frame class.

Not merely unproved: false. `saturateBlocked` at `fuel = 0` hands its input straight back
(`saturateBlocked_fuel_zero`), so the predicate's hypothesis is satisfied at **every** branch
whatsoever, and the predicate as literally stated therefore asserts that every branch is
blocking-aware saturated. The one-formula branch `[F(p → q)@⟨0,0⟩]` — the landed `multBranch 1`,
reused rather than rebuilt — is not: `.impNeg` applies to its only formula
(`findApplicableRule_multWitness`), nothing is blocked at the empty ordering
(`blockedTimes_empty`), so the finder reports that formula.

**What this does not show.** It is a statement about the `fuel = 0` arm alone, and it settles
nothing about larger fuel: a reader could reasonably suspect the predicate is one `fuel > 0` side
condition away from being true. `postBlockingSettles_fuel_gap_false` is the theorem that closes that
suspicion, and it is the substantive one. -/
theorem postBlockingSettles_fuel_zero_false (fc : FormalSystem.ProofSystem.FrameClass) :
    ¬ PostBlockingSettles fc := by
  intro h
  have hfind := h (multBranch 1) TimeOrdering.empty 0 (multBranch 1) TimeOrdering.empty
    (saturateBlocked_fuel_zero _ _ _)
  rw [findUnexpandedUnblockedWith_multBranch_one fc] at hfind
  exact absurd hfind (by simp)


/-- **The fuel-universal step.** If the branch is not closed and `expandOnceNoFresh` reports
`.saturated` on it, then `saturateBlocked` hands the branch straight back at **every** fuel figure.

No induction is needed and none is used: at `fuel = 0` the pass returns its input by definition, and
at `fuel + 1` it reaches the `(.saturated, _)` arm in one step, whose result is again the input. The
two `constraints.length` rejection guards and the three recursive arms are therefore not on this
branch's path at all, which is what makes the statement universal in `fuel` rather than a ladder of
checked figures. -/
theorem saturateBlocked_eq_self_of_noFresh_saturated
    {b : Branch} {ord ord' : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    (hcl : findClosure b fc = none)
    (hsat : expandOnceNoFresh b ord fc = (ExpansionResult.saturated, ord')) (fuel : Nat) :
    saturateBlocked b fuel ord fc = some (.inr (b, ord)) := by
  cases fuel with
  | zero => exact saturateBlocked_fuel_zero b ord fc
  | succ n => rw [saturateBlocked, hcl, hsat]

/-- The witness branch is open: one `.neg`-signed box between atoms closes nothing, at every frame
class. `checkBotPos` and `checkContradiction` do not read the frame class at all, and
`checkAxiomNeg`'s `matchAxiom` does not recognise `□p` as an axiom instance, so the
`witness.minFrameClass ≤ fc` test is never reached. -/
theorem findClosure_freshWorldBranch (fc : FormalSystem.ProofSystem.FrameClass) :
    findClosure freshWorldBranch fc = none := rfl

/-- **`expandOnceNoFresh` reports `.saturated` on the witness branch, at every frame class.**

Its `pick` runs `findApplicableRule` at the branch's one formula, gets `.boxNeg`
(`findApplicableRule_freshWorldWitness`), and `ruleMintsFreshLabel .boxNeg = true`, so the **first**
rejection test fires and `pick` returns `none` — the candidate is skipped rather than reported. The
branch has nothing else, so the search ends with no pick and the verdict is `.saturated`.

This is the exact disagreement the residual's docstring names, exhibited: there is outstanding work
on the branch, and this pass is by construction unable to see it. -/
theorem expandOnceNoFresh_freshWorldBranch (fc : FormalSystem.ProofSystem.FrameClass) :
    expandOnceNoFresh freshWorldBranch TimeOrdering.empty fc
      = (ExpansionResult.saturated, TimeOrdering.empty) := by
  have hrule := findApplicableRule_freshWorldWitness fc
  simp only [freshWorldBranch] at hrule
  have hmint : ruleMintsFreshLabel TableauRule.boxNeg = true := rfl
  simp only [expandOnceNoFresh, freshWorldBranch, List.findSome?_cons, List.findSome?_nil, hrule,
    hmint, if_true]

/-- **The blocking-aware finder does see it**, at every frame class: nothing is blocked at the empty
ordering, and `.boxNeg` applies, so `isExpanded` is `false` at the branch's one formula. -/
theorem findUnexpandedUnblockedWith_freshWorldBranch
    (fc : FormalSystem.ProofSystem.FrameClass) :
    findUnexpandedUnblockedWith freshWorldBranch TimeOrdering.empty fc
        (blockedTimes freshWorldBranch TimeOrdering.empty fc (armTracker freshWorldBranch))
      = some freshWorldWitness := by
  have hrule := findApplicableRule_freshWorldWitness fc
  simp only [freshWorldBranch] at hrule
  rw [blockedTimes_empty]
  simp only [findUnexpandedUnblockedWith, isExpanded, freshWorldBranch, List.find?_cons, hrule,
    Option.isNone_some, List.contains_nil, Bool.not_false, Bool.and_true]

/-- **The gap is exhibited at every fuel figure, simultaneously.**

Both halves at once, universally quantified in `fuel` and in the frame class: the post-blocking pass
returns the witness branch unchanged, and the saturation test it is measured against reports
outstanding work on that same branch. No fuel figure appears anywhere in either half, which is the
whole content of the verdict below. -/
theorem postBlockingSettles_gap_at_every_fuel
    (fc : FormalSystem.ProofSystem.FrameClass) (fuel : Nat) :
    saturateBlocked freshWorldBranch fuel TimeOrdering.empty fc
        = some (.inr (freshWorldBranch, TimeOrdering.empty)) ∧
      findUnexpandedUnblockedWith freshWorldBranch TimeOrdering.empty fc
          (blockedTimes freshWorldBranch TimeOrdering.empty fc (armTracker freshWorldBranch))
        = some freshWorldWitness :=
  ⟨saturateBlocked_eq_self_of_noFresh_saturated (findClosure_freshWorldBranch fc)
      (expandOnceNoFresh_freshWorldBranch fc) fuel,
    findUnexpandedUnblockedWith_freshWorldBranch fc⟩

/-- **Gate 2: fuel does not close the gap.** The verdict on the open question
`PostBlockingSettles`'s own docstring poses.

`PostBlockingSettles fc` is refuted at a **nonzero** fuel — so this is not a restatement of
`postBlockingSettles_fuel_zero_false` — and `postBlockingSettles_gap_at_every_fuel` records that the
same witness works at every fuel whatsoever, not at the figure chosen here.

**The verdict, in one line.** Fuel does not close it, because `expandOnceNoFresh` *skips*
label-minting candidates while `findUnexpandedUnblockedWith` counts them, and no fuel figure appears
anywhere in that disagreement.

**What the witness is.** The landed `freshWorldBranch = [F(□p)@⟨0,0⟩]`, reused rather than rebuilt.
Its only applicable rule is `.boxNeg`, which mints a fresh **world**, so it trips
`expandOnceNoFresh`'s *first* rejection test (`ruleMintsFreshLabel`). Register entry 13 records that
the label-minting and time-minting rule lists are incomparable and that this is exactly why
`expandOnceNoFresh` runs two rejection tests in sequence; a time-minting witness would trip the
second test and refute the predicate the same way. -/
theorem postBlockingSettles_fuel_gap_false (fc : FormalSystem.ProofSystem.FrameClass) :
    ¬ PostBlockingSettles fc := by
  intro h
  obtain ⟨hsb, hfind⟩ := postBlockingSettles_gap_at_every_fuel fc 1
  rw [h freshWorldBranch TimeOrdering.empty 1 freshWorldBranch TimeOrdering.empty hsb] at hfind
  exact absurd hfind (by simp)


/-! ### The repaired predicate

Phase 2's witness locates the missing content at the **branch**, not at the fuel, so the repair
relocates exactly two hypotheses and changes the conclusion not at all. Both are stated about the
pass's **output** branch, which is where the settlement test is run.
-/

/-- **The pass ran to label-free saturation** rather than being truncated by fuel.

Stated as `(expandOnceNoFresh b ord fc).1 = .saturated` rather than as the pair equation
`expandOnceNoFresh b ord fc = (.saturated, ord)` the plan pre-declared. The narrowing is forced by
the frozen definition and is a *weakening* of the hypothesis, hence a strengthening of every
statement that assumes it: `expandOnceNoFresh`'s `.notApplicable` arm returns `(.saturated, newOrd)`
with the **picked** ordering rather than the incoming one, so the pair equation is strictly stronger
than the fact the settlement argument consumes, and `saturateBlocked`'s own `(.saturated, _)` arm
discards the second component too. -/
def LabelFreeSaturatedExit (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) : Prop :=
  (expandOnceNoFresh b ord fc).1 = ExpansionResult.saturated

/-- **No label-minting work is left sitting at an unblocked time.**

This is the disagreement Phase 2 exhibits, stated as a condition on the branch: every formula at an
unblocked time whose rule the engine finds applicable is one `expandOnceNoFresh` would have been
willing to fire — it neither mints a fresh label nor lengthens the ordering constraints. The witness
`freshWorldBranch` fails it at its one formula, which is exactly why it refutes the residual. -/
def NoUnblockedFreshWork (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) : Prop :=
  ∀ sf ∈ b, ¬ (blockedTimes b ord fc (armTracker b)).contains sf.label.time →
    ∀ rule result newOrd, findApplicableRule sf b ord fc = some (rule, result, newOrd) →
      ruleMintsFreshLabel rule = false ∧
        newOrd.constraints.length ≤ ord.constraints.length

/-- **The repaired residual**: `PostBlockingSettles`'s statement with the two conditions above added
as antecedents on the **output** branch. The conclusion is carried over verbatim — no test is
weakened, no finder is replaced, and the frame class stays universally quantified. -/
def PostBlockingSettlesAt (fc : FormalSystem.ProofSystem.FrameClass) : Prop :=
  ∀ (ob : Branch) (oOrd : TimeOrdering) (fuel : Nat) (satBr : Branch) (satOrd : TimeOrdering),
    saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) →
    LabelFreeSaturatedExit satBr satOrd fc →
    NoUnblockedFreshWork satBr satOrd fc →
    findUnexpandedUnblockedWith satBr satOrd fc
      (blockedTimes satBr satOrd fc (armTracker satBr)) = none

/-- **The direction, fixed.** The hypothesis list is longer, so `PostBlockingSettlesAt` is the
**weaker** predicate, so every theorem restated against it is a **strengthening** — the same
direction `universeClosedAt_of_universeClosed` and `mintPaysForTimeFixed_of_mintPaysForTimeStable`
record for their own repairs, and the reason register entry 7 exists. -/
theorem postBlockingSettlesAt_of_postBlockingSettles
    {fc : FormalSystem.ProofSystem.FrameClass} (h : PostBlockingSettles fc) :
    PostBlockingSettlesAt fc :=
  fun ob oOrd fuel satBr satOrd hsb _ _ => h ob oOrd fuel satBr satOrd hsb

/-! ### The gate: can the consuming sites supply the two antecedents?

The repair is admissible only if `armSettlement_of_postBlockingSettles`'s and
`buildTableauAt_isSome_of_settles`'s proofs can supply the relocated hypotheses where they consume
the residual. Both sites reach the residual holding exactly one fact about the output pair — the
equation `saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd))` — so the question is
whether `LabelFreeSaturatedExit satBr satOrd fc` follows from that equation.

It does not, and the obstruction is decided rather than described.
-/

/-- **`.impNeg` fires on the one-formula branch under the label-free filter too.** Its rule mints no
label and adds no ordering constraint, so `expandOnceNoFresh`'s `pick` accepts it and the verdict is
`.extended`, not `.saturated`. -/
theorem expandOnceNoFresh_multBranch_one (fc : FormalSystem.ProofSystem.FrameClass) :
    expandOnceNoFresh (multBranch 1) TimeOrdering.empty fc
      = (ExpansionResult.extended (multEmitted ++ multBranch 1), TimeOrdering.empty) := by
  have hrule := findApplicableRule_multWitness (multBranch 1) (pos_not_mem_multBranch 1) fc
  have hb : multBranch 1 = multWitness :: ([] : Branch) := by
    simp [multBranch, List.replicate]
  have hmint : ruleMintsFreshLabel TableauRule.impNeg = false := rfl
  conv_lhs => rw [expandOnceNoFresh]
  rw [hb, List.findSome?_cons]
  rw [← hb, hrule]
  simp only [hmint, if_false, TimeOrdering.empty, gt_iff_lt, lt_self_iff_false, if_false, hb]
  simp

/-- **The obstruction, decided.** `saturateBlocked`'s `.inr` exit does **not** carry
`LabelFreeSaturatedExit` on its output: at `fuel = 0` the pass hands back its input untested, and
that input can have label-free work outstanding. So the relocated hypothesis is not derivable from
what either consuming site holds, and it is a genuine residual rather than a side condition a bridge
proof could discharge.

Stated at every frame class, on the landed `multBranch 1` vehicle. -/
theorem labelFreeSaturatedExit_not_of_saturateBlocked_inr
    (fc : FormalSystem.ProofSystem.FrameClass) :
    saturateBlocked (multBranch 1) 0 TimeOrdering.empty fc
        = some (.inr (multBranch 1, TimeOrdering.empty)) ∧
      ¬ LabelFreeSaturatedExit (multBranch 1) TimeOrdering.empty fc := by
  refine ⟨saturateBlocked_fuel_zero _ _ _, ?_⟩
  intro h
  rw [LabelFreeSaturatedExit, expandOnceNoFresh_multBranch_one fc] at h
  exact absurd h (by simp)


/-! ### The settlement lemma

The mathematical content of the repair: the two relocated antecedents really do force the
conclusion. Everything below is proved from the frozen files' **public** interface — `saturateBlocked`,
`expandOnceNoFresh`, `findApplicableRule`, `isExpanded`, `findUnexpandedUnblockedWith`,
`blockedTimes` and `ruleMintsFreshLabel` are all public `def`s, and `private` blocks name resolution
rather than unfolding (register entry 9's observation, used here in the direction where it helps).
-/

/-- **`findApplicableRule` never reports `.notApplicable`.** Its own body maps that constructor to
`none` before the `some` is built, so a reported triple always carries a result the engine can act
on. Needed because `expandOnceNoFresh` has a *second* route to `.saturated` — its `.notApplicable`
arm — and the inversion below has to rule that route out rather than assume it dead. -/
theorem findApplicableRule_result_ne_notApplicable
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass}
    {rule : TableauRule} {result : RuleResult} {newOrd : TimeOrdering}
    (h : findApplicableRule sf b ord fc = some (rule, result, newOrd)) :
    result ≠ RuleResult.notApplicable := by
  rw [findApplicableRule, List.findSome?_eq_some_iff] at h
  obtain ⟨_, r, _, _, hr, _⟩ := h
  intro hna
  subst hna
  repeat' split at hr
  all_goals simp_all

/-- **The `.saturated` verdict inverts to "the label-free filter rejected everything".**

`expandOnceNoFresh` reports `.saturated` in two ways: its `pick` found nothing, or the pick's result
was `.notApplicable`. The second is unreachable
(`findApplicableRule_result_ne_notApplicable`), so `.saturated` means exactly that every formula on
the branch was either not applicable at all, or applicable only through a rule the label-free filter
rejects. -/
theorem expandOnceNoFresh_saturated_imp
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    (hsat : (expandOnceNoFresh b ord fc).1 = ExpansionResult.saturated)
    {sf : SignedFormula} (hsf : sf ∈ b)
    {rule : TableauRule} {result : RuleResult} {newOrd : TimeOrdering}
    (hr : findApplicableRule sf b ord fc = some (rule, result, newOrd)) :
    ruleMintsFreshLabel rule = true ∨
      newOrd.constraints.length > ord.constraints.length := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hmint', hlen'⟩ := hcon
  have hmint : ruleMintsFreshLabel rule = false := by simpa using hmint'
  have hlen : newOrd.constraints.length ≤ ord.constraints.length := Nat.not_lt.mp hlen'
  rw [expandOnceNoFresh] at hsat
  split at hsat
  · rename_i hp
    rw [List.findSome?_eq_none_iff] at hp
    have hx := hp sf hsf
    rw [hr] at hx
    simp only [hmint, Bool.false_eq_true, if_false, Nat.not_lt.mpr hlen, if_false] at hx
    exact absurd hx (by simp)
  · rename_i res nO hp
    have hne : res ≠ RuleResult.notApplicable := by
      rw [List.findSome?_eq_some_iff] at hp
      obtain ⟨_, x, _, _, hx, _⟩ := hp
      cases hfa : findApplicableRule x b ord fc with
      | none => rw [hfa] at hx; simp at hx
      | some tr =>
          obtain ⟨r', res', nO'⟩ := tr
          rw [hfa] at hx
          simp only at hx
          split at hx
          · simp at hx
          · split at hx
            · simp at hx
            · simp only [Option.some.injEq, Prod.mk.injEq] at hx
              obtain ⟨rfl, _⟩ := hx
              exact findApplicableRule_result_ne_notApplicable hfa
    cases res <;> simp_all

/-- **The finder closes when every unblocked formula is expanded.** Pure `List.find?` reasoning. -/
theorem findUnexpandedUnblockedWith_eq_none_of_isExpanded
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    {blocked : List TimeIndex}
    (h : ∀ sf ∈ b, ¬ blocked.contains sf.label.time → isExpanded sf b ord fc = true) :
    findUnexpandedUnblockedWith b ord fc blocked = none := by
  rw [findUnexpandedUnblockedWith, List.find?_eq_none]
  intro x hx hp
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  exact absurd (h x hx (by simp only [hp.1, Bool.false_eq_true, not_false_eq_true]))
    (by simp [hp.2])

/-- **The core lemma.** `.saturated` plus no unblocked fresh work **is** settlement.

If `expandOnceNoFresh` reports `.saturated` then every formula on the branch is either not
applicable at all or applicable only through a label-minting or constraint-lengthening rule
(`expandOnceNoFresh_saturated_imp`). `NoUnblockedFreshWork` rules out the second and third
possibilities at every unblocked time. So every unblocked formula has `findApplicableRule = none`,
i.e. is `isExpanded`, and the blocking-aware finder closes.

Each hypothesis pays for exactly one of the two disagreements Phase 2 exhibits:
`LabelFreeSaturatedExit` pays for the fuel-truncation gap (`saturateBlocked` may hand a branch back
untested), and `NoUnblockedFreshWork` pays for the label-minting gap (`expandOnceNoFresh` skips what
`findUnexpandedUnblockedWith` counts). -/
theorem postBlockingSettlesAt_settlement
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    (hlf : LabelFreeSaturatedExit b ord fc) (hnf : NoUnblockedFreshWork b ord fc) :
    findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc (armTracker b)) = none := by
  refine findUnexpandedUnblockedWith_eq_none_of_isExpanded ?_
  intro sf hsf hub
  rw [isExpanded, Option.isNone_iff_eq_none]
  by_contra hne
  obtain ⟨tr, htr⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨rule, result, newOrd⟩ := tr
  obtain ⟨hm, hl⟩ := hnf sf hsf hub rule result newOrd htr
  rcases expandOnceNoFresh_saturated_imp hlf hsf htr with h | h
  · rw [hm] at h; exact absurd h (by simp)
  · exact absurd hl (Nat.not_le.mpr h)

/-- **The repaired residual is not a residual at all: it is a theorem.**

`PostBlockingSettlesAt fc` holds outright, for every frame class, with no hypothesis and no witness
class. This is the honest resolution of `PostBlockingSettles`'s open question: the settlement test is
decided by the **branch** — whether the label-free pass ran to completion on it, and whether any
label-minting work is left at an unblocked time — and not by the fuel. Neither fact follows from
`saturateBlocked`'s exit equation, which is why the literal predicate is false and why this one is
true. -/
theorem postBlockingSettlesAt_holds (fc : FormalSystem.ProofSystem.FrameClass) :
    PostBlockingSettlesAt fc :=
  fun _ _ _ _ _ _ hlf hnf => postBlockingSettlesAt_settlement hlf hnf


/-! ### The gate's verdict, decided

The two bridges are the anti-weakening gate: the repair is admissible only if
`armSettlement_of_postBlockingSettles` and `buildTableauAt_isSome_of_settles` can supply the
relocated hypotheses where they consume the residual. They cannot, and the failure is now decidable
rather than merely observed.

Both sites hold exactly one fact about the output pair — the exit equation — and
`labelFreeSaturatedExit_not_of_saturateBlocked_inr` shows that equation does not carry
`LabelFreeSaturatedExit`. The remaining question is whether a bridge could carry the two antecedents
as an *extra hypothesis* instead. It can, syntactically, and the hypothesis it would carry is
`PostBlockingExitSettled` below — which is **refuted**. So the only bridge shape that typechecks is a
weakening dressed as a repair, and the gate rejects it. That is the finding, stated as a theorem
rather than as a judgement call.
-/

/-- **The hypothesis a bridge at the repaired predicate would have to carry**: that
`saturateBlocked`'s open exit always lands on a branch satisfying both relocated antecedents. -/
def PostBlockingExitSettled (fc : FormalSystem.ProofSystem.FrameClass) : Prop :=
  ∀ (ob : Branch) (oOrd : TimeOrdering) (fuel : Nat) (satBr : Branch) (satOrd : TimeOrdering),
    saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) →
    LabelFreeSaturatedExit satBr satOrd fc ∧ NoUnblockedFreshWork satBr satOrd fc

/-- Supplying the antecedents at every exit recovers the literal residual, through the settlement
lemma. This is the implication that makes the refutation below possible. -/
theorem postBlockingSettles_of_postBlockingExitSettled
    {fc : FormalSystem.ProofSystem.FrameClass} (h : PostBlockingExitSettled fc) :
    PostBlockingSettles fc := fun ob oOrd fuel satBr satOrd hsb =>
  postBlockingSettlesAt_settlement (h ob oOrd fuel satBr satOrd hsb).1
    (h ob oOrd fuel satBr satOrd hsb).2

/-- **Gate verdict: FALSE, and provably so.** The bridge hypothesis is refuted at every frame class,
because it implies the literal residual that `postBlockingSettles_fuel_zero_false` refutes.

So the pre-declared repair is not admissible: relocating the two conditions to the output branch
leaves the terminus needing them at a site that cannot produce them, and the one way to hand them to
it carries an antecedent no caller can discharge — the `mintPaysForTime_empty` /
`universeClosed_identify_empty` failure mode in its sharpest form, caught before anything was
restated against it.

The repair is not thereby worthless: `postBlockingSettlesAt_holds` says the relocated statement is
**true outright**, which is what identifies where the real residual lives. It is not a settlement
question at all. It is the conjunction of a *fuel-adequacy* fact — that the pass ran to label-free
saturation rather than being truncated — and a *label-minting* fact about the branch the run reaches,
and neither is available from `saturateBlocked`'s exit equation because both are false at the
`fuel = 0` exit. Any admissible repair must therefore restrict the residual's quantification from
"every `(ob, oOrd, fuel)`" to the pair the terminus's own run produces; that is named here and
deliberately left unattempted. -/
theorem postBlockingExitSettled_false (fc : FormalSystem.ProofSystem.FrameClass) :
    ¬ PostBlockingExitSettled fc :=
  fun h => postBlockingSettles_fuel_zero_false fc
    (postBlockingSettles_of_postBlockingExitSettled h)


/-! ### How far the discharge goes

Two questions, kept apart because conflating them is how a weakening gets mistaken for a repair.
**Is the settlement lemma's antecedent pair dischargeable at a class the engine reaches?** Yes, and
the witness below is a branch the post-blocking pass itself produces. **Is that class larger than
the class where the conclusion already holds?** No — and that is the sharp statement of why
`PostBlockingSettlesAt` is a theorem rather than a repair.
-/

/-- **The converse, unconditional.** A branch on which the settlement test already closes satisfies
`NoUnblockedFreshWork` for free, because the antecedent of that condition is then unsatisfiable: no
unblocked formula has an applicable rule at all. No hypothesis about `expandOnceNoFresh` is used. -/
theorem noUnblockedFreshWork_of_settled
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    (h : findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc (armTracker b)) = none) :
    NoUnblockedFreshWork b ord fc := by
  intro sf hsf hub rule result newOrd hr
  exfalso
  rw [findUnexpandedUnblockedWith, List.find?_eq_none] at h
  refine h sf hsf ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true', isExpanded, hr, Option.isNone_some]
  exact ⟨by simpa using hub, trivial⟩

/-- **The equivalence, and the verdict it carries.** Given that the pass ran to label-free
saturation, `NoUnblockedFreshWork` is not a weaker condition than the settlement test — it is that
test, restated. Forward is `postBlockingSettlesAt_settlement`; backward is the unconditional
converse above.

So `PostBlockingSettlesAt` is a theorem for a reason a reader should not mistake for progress: its
second antecedent already says what its conclusion says, once its first antecedent holds. What the
pair *does* buy is a **branch-independent** sufficient condition — `LabelFreeUniverseAt` below is
checkable from the universe alone, without looking at the branch — and that is the only useful
direction the equivalence leaves open. -/
theorem noUnblockedFreshWork_iff_of_labelFreeSaturatedExit
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    (hlf : LabelFreeSaturatedExit b ord fc) :
    NoUnblockedFreshWork b ord fc ↔
      findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc (armTracker b)) = none :=
  ⟨fun hnf => postBlockingSettlesAt_settlement hlf hnf, noUnblockedFreshWork_of_settled⟩

/-- **The label-minting-free fragment**, stated at a fixed ordering because the ordering is part of
what decides it: `orderTrichotomy` is applicable to *every* signed formula and is
constraint-lengthening exactly when the ordering has an incomparable pair, so no condition on the
formula stock alone can be sufficient. At `TimeOrdering.empty` it reports `.notApplicable`, which is
why the concrete witness below runs there. -/
def LabelFreeUniverseAt (fc : FormalSystem.ProofSystem.FrameClass)
    (U : Finset SignedFormula) (ord : TimeOrdering) : Prop :=
  ∀ sf ∈ U, ∀ (b : Branch) (rule : TableauRule) (result : RuleResult) (newOrd : TimeOrdering),
    findApplicableRule sf b ord fc = some (rule, result, newOrd) →
      ruleMintsFreshLabel rule = false ∧
        newOrd.constraints.length ≤ ord.constraints.length

/-- **Confinement to a label-free universe discharges the second antecedent**, for every branch and
every blocked set, without looking at the branch. This is the branch-independent direction the
equivalence above leaves open. -/
theorem noUnblockedFreshWork_of_labelFreeUniverseAt
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula} {ord : TimeOrdering}
    (hU : LabelFreeUniverseAt fc U ord) {b : Branch} (hconf : ∀ x ∈ b, x ∈ U) :
    NoUnblockedFreshWork b ord fc :=
  fun sf hsf _ rule result newOrd hr => hU sf (hconf sf hsf) b rule result newOrd hr

/-! #### The concrete instantiation, and its non-vacuity

The witness is the landed `multBranch 1 = [F(p → q)@⟨0,0⟩]` and its one-step successor. It is
propositional, at `TimeOrdering.empty`, and the branch the discharge is stated at is one the
**post-blocking pass itself produces** — not a hand-assembled `Branch` and not the empty universe.
-/

/-- The pass's output at the witness: `T p, F q, F(p → q)`. -/
def multSettledBranch : Branch := multEmitted ++ multBranch 1

/-- One `.extended` step of the post-blocking pass, in closed form. -/
theorem saturateBlocked_step_extended {b nb : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} (fuel : Nat)
    (hcl : findClosure b fc = none)
    (hext : expandOnceNoFresh b ord fc = (ExpansionResult.extended nb, ord)) :
    saturateBlocked b (fuel + 1) ord fc = saturateBlocked nb fuel ord fc := by
  rw [saturateBlocked, hcl, hext]
  simp

theorem findClosure_multBranch_one (fc : FormalSystem.ProofSystem.FrameClass) :
    findClosure (multBranch 1) fc = none := by
  cases fc <;> rfl

theorem findClosure_multSettledBranch (fc : FormalSystem.ProofSystem.FrameClass) :
    findClosure multSettledBranch fc = none := by
  cases fc <;> rfl

/-- **The first antecedent, decided at every frame class**: the pass's output is label-free
saturated. Both atoms are expanded, and `F(p → q)`'s `.impNeg` is guarded off because the branch now
carries both of its conclusions. -/
theorem labelFreeSaturatedExit_multSettledBranch
    (fc : FormalSystem.ProofSystem.FrameClass) :
    LabelFreeSaturatedExit multSettledBranch TimeOrdering.empty fc := by
  show (expandOnceNoFresh multSettledBranch TimeOrdering.empty fc).1 = _
  cases fc <;> rfl

/-- **The second antecedent, at the same branch.** Discharged through the equivalence, from the
decided settlement test — which is exactly the caveat this section exists to state plainly. -/
theorem noUnblockedFreshWork_multSettledBranch
    (fc : FormalSystem.ProofSystem.FrameClass) :
    NoUnblockedFreshWork multSettledBranch TimeOrdering.empty fc :=
  noUnblockedFreshWork_of_settled (by cases fc <;> rfl)

/-- **The engine actually gets there**, at every frame class and every positive fuel figure: the
post-blocking pass started at `[F(p → q)@⟨0,0⟩]` fires `.impNeg` once and then reports the extended
branch as label-free saturated. So the class the discharge is stated at is inhabited by a branch the
pass produces, not by a hand-assembled one. -/
theorem saturateBlocked_multBranch_one_run
    (fc : FormalSystem.ProofSystem.FrameClass) (fuel : Nat) :
    saturateBlocked (multBranch 1) (fuel + 1) TimeOrdering.empty fc
      = some (.inr (multSettledBranch, TimeOrdering.empty)) := by
  rw [saturateBlocked_step_extended fuel (findClosure_multBranch_one fc)
    (expandOnceNoFresh_multBranch_one fc)]
  exact saturateBlocked_eq_self_of_noFresh_saturated (findClosure_multSettledBranch fc)
    (by
      have h := labelFreeSaturatedExit_multSettledBranch fc
      rw [LabelFreeSaturatedExit] at h
      exact Prod.ext h rfl) fuel

/-- **The concrete discharge.** At every frame class and every positive fuel, the post-blocking pass
run from `[F(p → q)@⟨0,0⟩]` returns a branch at which both antecedents hold and the blocking-aware
saturation test therefore closes. Nothing here is at a vacuous boundary: the branch is nonempty,
three formulas wide, and produced by the pass. -/
theorem postBlockingSettlesAt_labelFree
    (fc : FormalSystem.ProofSystem.FrameClass) (fuel : Nat) :
    ∃ satBr satOrd,
      saturateBlocked (multBranch 1) (fuel + 1) TimeOrdering.empty fc
          = some (.inr (satBr, satOrd)) ∧
        findUnexpandedUnblockedWith satBr satOrd fc
          (blockedTimes satBr satOrd fc (armTracker satBr)) = none :=
  ⟨multSettledBranch, TimeOrdering.empty, saturateBlocked_multBranch_one_run fc fuel,
    postBlockingSettlesAt_settlement (labelFreeSaturatedExit_multSettledBranch fc)
      (noUnblockedFreshWork_multSettledBranch fc)⟩


/-! ### The narrowed repair: the residual at what the terminus instantiates it at

The gate above rejects the *output-branch* repair. What is left is the over-quantification itself,
and that is repairable by the same move every sibling residual on this terminus was repaired by:
state the predicate at what the terminus actually instantiates it at, and fix the direction with a
lemma. `UniverseClosedAt` restricts clause 2's merge target to `b.knownTimes` (entry 10);
`MintPaysForTimeStable` and `MintPaysForTimeFixed` restrict σ (entries 19, 20); and — closest of
all — `ArmSettlement` is *already* stated this way, and says so on its own docstring: "a blanket
'`resolveOpenArm` never reports `none`' is plainly false — at `fuel = 0` and an unsaturated arm it
reports `none` — so this predicate is restricted to arms an engine run actually hands the fold."

`PostBlockingSettles` was never restricted that way, and that is the whole of its defect. It
quantifies over **every** `(ob, oOrd, fuel)`, including branches no run produces and the `fuel = 0`
arm at which its hypothesis is satisfied by every branch whatsoever. `buildTableauAt` reaches it at
exactly one kind of pair: a branch `expandBranchWithFuel` returned open, and the same fuel figure
that call was given.

`PostBlockingSettles` is retained verbatim and the landed termini are untouched. Nine restatements
once stood below, carrying `ArmSettlement` — which the landed chain already needed and already had
— together with the narrowed residual. They have been retired as vacuous, because the narrowed
residual is itself refuted at the figures they were stated at; the retirement record below carries
the disposition, and the live successor line is `PostBlockingSettlesSeedRun`.
-/

/-- **The post-blocking settlement residual, at what the terminus instantiates it at.**

`PostBlockingSettles`'s statement with the pass's input branch restricted to a branch some
`expandBranchWithFuel` call returned open, at the **same** fuel figure that call was given — which
is exactly how `buildTableauAt` reaches it (`Saturation.lean`'s `buildTableauAt`: one
`expandBranchWithFuel … fuel …` call, then `saturateBlocked openBr fuel ord fc`). The conclusion is
carried over verbatim: no test is weakened, no finder is replaced, and the frame class stays
universally quantified.

**Why the unrestricted form is not used.** It is refuted, at every frame class, and register entry
22 records why: `postBlockingSettles_fuel_zero_false` kills it at the `fuel = 0` arm, where
`saturateBlocked` hands its input back untested so the hypothesis is satisfied at *every* branch,
and `postBlockingSettles_fuel_gap_false` kills it at a nonzero one, on a branch
(`freshWorldBranch`) that no engine run hands to the pass. Entry 23 records why relocating
conditions onto the pass's **output** branch is not the repair either.

**The quantification is the honest one as far as it goes**, in the same sense and the same words as
`ArmSettlement`: `ob` is a branch some `expandBranchWithFuel` call returned open, and the fuel is
that call's own. What *is* decided in this narrowing's favour is that the `fuel = 0` degeneracy
which refutes the unrestricted form cannot reach it (`expandBranchWithFuel_eq_none_zero`), and that
its antecedent is genuinely satisfiable at figures the engine reaches — see the non-vacuity
subsection below.

**But the narrowing is incomplete, and the predicate is REFUTED at the terminus's own fuel figure.**
`postBlockingSettlesRun_terminusFuel_false` decides it in the negative at `.Base`, for every value of
every parameter, and `postBlockingSettlesRun_false_dense` / `postBlockingSettlesRun_false_rtime` do
the same at two further classes. The defect is a *second* over-quantification: this predicate
restricts `(ob, oOrd, fuel)` but leaves `expandBranchWithFuel`'s `EventualityTracker` argument
universally quantified, and that argument is the only input the engine's blocked-set computation and
the settlement test's recomputed `armTracker` do not share. Nothing is withdrawn on that account —
this definition is retained verbatim, as everything in this file is — but it is a **false**
hypothesis at those three classes. The nine termini that carried it were vacuous there for exactly
that reason and have been retired; see the retirement record below, the verdict subsection, and
register entries 24 and 25. The completion of the narrowing is
`PostBlockingSettlesSeedRun`, which is carried as a hypothesis and is **not** shown true. -/
def PostBlockingSettlesRun (fc : FormalSystem.ProofSystem.FrameClass) (fuel : Nat) : Prop :=
  ∀ (b ob : Branch) (ord oOrd : TimeOrdering) (tr : EventualityTracker) (ap oAp : AppliedSet)
    (mb bu : Nat) (satBr : Branch) (satOrd : TimeOrdering),
    expandBranchWithFuel b fuel ord fc tr ap mb bu = some (.inr (ob, oOrd, oAp)) →
    saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) →
    findUnexpandedUnblockedWith satBr satOrd fc
      (blockedTimes satBr satOrd fc (armTracker satBr)) = none

/-- **The direction, fixed and stated in words.** `PostBlockingSettlesRun fc fuel` is the **weaker**
predicate: its hypothesis list is longer by one antecedent, and the difference sits at the `(ob,
oOrd)` quantifier — the narrowed form speaks only about pairs an `expandBranchWithFuel` call at this
same fuel returned open, where the unrestricted form speaks about all of them. So the implication
runs `PostBlockingSettles fc → PostBlockingSettlesRun fc fuel`, at every `fuel`, and **every
theorem restated against the narrowed form is a strengthening of its landed original**, never a
weakening. This is the same direction `universeClosedAt_of_universeClosed` and
`mintPaysForTimeFixed_of_mintPaysForTimeStable` record for their own repairs, and register entry 7
is why it is stated rather than assumed.

Retained as the record of the direction; its one consumer was among the retired `_run` termini, so
it has none today. See the retirement record below. -/
theorem postBlockingSettlesRun_of_postBlockingSettles
    {fc : FormalSystem.ProofSystem.FrameClass} (h : PostBlockingSettles fc) (fuel : Nat) :
    PostBlockingSettlesRun fc fuel :=
  fun _ ob _ oOrd _ _ _ _ _ satBr satOrd _ hsb => h ob oOrd fuel satBr satOrd hsb

/-- `expandBranchWithFuel` is `none` at zero fuel, whether or not the budget guard fires first. -/
theorem expandBranchWithFuel_eq_none_zero (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) (tr : EventualityTracker) (ap : AppliedSet)
    (mb bu : Nat) : expandBranchWithFuel b 0 ord fc tr ap mb bu = none := by
  rw [expandBranchWithFuel]
  split <;> rfl

/-- **The degeneracy that refutes the unrestricted form cannot reach the narrowed one.** At
`fuel = 0` the narrowed predicate is vacuously true, because `expandBranchWithFuel` reports `none`
there and its antecedent is unsatisfiable — where the unrestricted predicate is *false* at that
same figure, since `saturateBlocked` hands its input back untested and the hypothesis is then
satisfied at every branch.

Stated so the fuel parameter is visibly load-bearing rather than decoration: at `fuel = 0` the
narrowed predicate says nothing at all, so a discharge has to be claimed at a figure where its
antecedent is satisfiable. The non-vacuity subsection below exhibits such figures. -/
theorem postBlockingSettlesRun_zero (fc : FormalSystem.ProofSystem.FrameClass) :
    PostBlockingSettlesRun fc 0 := by
  intro b _ ord _ tr ap _ mb bu _ _ hE _
  rw [expandBranchWithFuel_eq_none_zero b ord fc tr ap mb bu] at hE
  exact absurd hE (by simp)

/-- **Bridge, and the gate on the whole narrowing: the entry point's arms are discharged by the
narrowed residual.** The analogue of `buildTableauAt_isSome_of_settles`, with
`PostBlockingSettles fc` exchanged for `PostBlockingSettlesRun fc fuel`. The exchange is available
because `buildTableauAt` reaches the residual holding the very equation the narrowed form asks for:
its own `expandBranchWithFuel` call is in scope at the point the post-blocking arm is decided.

Retained as the record of the narrowing; its four consumers were the retired `_run` termini, so it
has none today. See the retirement record below. -/
theorem buildTableauAt_isSome_of_settlesRun {phi : Formula} {fuel : Nat}
    {fc : FormalSystem.ProofSystem.FrameClass} {maxBranches : Nat}
    (hpb : PostBlockingSettlesRun fc fuel)
    (hexp : (expandBranchWithFuel [SignedFormula.neg phi Label.initial] fuel TimeOrdering.empty fc
      (maxBranches := maxBranches)).isSome = true) :
    (buildTableauAt phi fuel fc maxBranches).isSome = true := by
  unfold buildTableauAt
  simp only
  match hE : expandBranchWithFuel [SignedFormula.neg phi Label.initial] fuel TimeOrdering.empty fc
      (maxBranches := maxBranches) with
  | none => rw [hE] at hexp; simp at hexp
  | some (.inl closedBr) => simp
  | some (.inr (ob, oOrd, oAp)) =>
      dsimp only
      split
      · simp
      · match hsb : saturateBlocked ob fuel oOrd fc with
        | none => exact absurd hsb (saturateBlocked_ne_none ob fuel oOrd fc)
        | some (.inl cb) => simp
        | some (.inr (satBr, satOrd)) =>
            dsimp only
            split
            · simp
            · rename_i sf2 hg2
              rw [hpb _ _ _ _ _ _ _ _ _ _ _ hE hsb] at hg2
              simp at hg2


/-! #### The termini restated at the narrowed residual — retired as vacuous

**What stood here.** Nine theorems restated the landed termini against the narrowed residual:

* `buildTableauAt_isSome_of_budget_run`
* `buildTableauAt_isSome_of_budget_of_run`
* `buildTableauAt_isSome_at_seed_run`
* `buildTableauAt_isSome_of_budget_at_run`
* `buildTableauAt_isSome_at_seed_at_run`
* `buildTableauAt_isSome_of_budget_selfGuarded_run`
* `buildTableauAt_isSome_at_seed_selfGuarded_run`
* `buildTableauAt_isSome_of_budget_fixed_run`
* `buildTableauAt_isSome_at_seed_fixed_run`

They are gone from the file. The names are recorded here so a reader arriving from `git log`, from
register entries 24 and 25, or from an external citation still finds them, in the idiom
`Correctness.lean` uses for its own retired pair: delete the theorem, keep the record.

**Why they were retired.** Each read as a headline result — the tableau construction succeeds —
while establishing nothing, because each carried a hypothesis this file itself refutes. That is
worse than the statements being absent: a reader meeting one at its declaration site got no local
signal, and the refutation sits thousands of lines away in the register. Removing them withdraws
no content, because none of them ever delivered any.

**The refutations, at the figures the nine were actually stated at.** Four of them
(`_of_budget_run`, `_at_seed_run`, `_of_budget_at_run`, `_at_seed_at_run`) carried
`PostBlockingSettlesRun fc` at the un-`At` figure `mintAwareFuel …`, refuted by
`postBlockingSettlesRun_mintAwareFuel_false`. Four (`_of_budget_selfGuarded_run`,
`_at_seed_selfGuarded_run`, `_of_budget_fixed_run`, `_at_seed_fixed_run`) carried it at
`mintAwareFuelAt …`, refuted by `postBlockingSettlesRun_terminusFuel_false`. Both figures are
positive at every parameter value (`one_le_mintAwareFuel`, `one_le_mintAwareFuelAt`), and
`postBlockingSettlesRun_false_succ` refutes the predicate at every positive figure. The ninth,
`buildTableauAt_isSome_of_budget_of_run`, carried the unrestricted `PostBlockingSettles`, refuted
by `postBlockingSettles_fuel_zero_false`.

**The frame-class split, which is not uniform and must not be flattened.** The eight carrying
`PostBlockingSettlesRun` are established vacuous at `.Base`, `.Dense` and `.RTime` — the last two
by `postBlockingSettlesRun_false_dense` and `postBlockingSettlesRun_false_rtime`. At `.ZTime`
their hypothesis is *undecided here*: the witness leaves `priorUZ` and `priorSZ` applicable, as
entry 25 records. Undecided is not delivered — at `.ZTime` they proved nothing either, and they
had zero dependents there as everywhere else. `buildTableauAt_isSome_of_budget_of_run` is the
exception in the other direction: carrying the unrestricted predicate, it is refuted by
`postBlockingSettles_fuel_zero_false` at **all four** frame classes, so entry 25's `.ZTime`
caveat does not reach it at all.

**What survives, and why.** Everything but the nine restatements. `PostBlockingSettlesRun` itself
is retained verbatim as the record of the narrowing, with
`postBlockingSettlesRun_of_postBlockingSettles` fixing its direction and
`buildTableauAt_isSome_of_settlesRun` as its bridge. The whole refutation apparatus stands —
`pbrWitnessBranch`, `pbrDoctoredTracker`, `postBlockingSettlesRun_false_succ` and the per-class
records — as does the non-vacuity subsection below. So does the live successor line:
`PostBlockingSettlesSeedRun`, its bridge `buildTableauAt_isSome_of_settlesSeedRun`, and
`buildTableauAt_isSome_of_budget_fixed_seedRun`, the terminus restated against a hypothesis this
file has **not** refuted. The landed termini stated against `PostBlockingSettles` are untouched.

**What the removal cost.** Nothing measurable. A whole-environment reverse-dependency scan found
zero dependents of the nine outside the nine themselves, and the decision procedure
`FormalSystem.Metalogic.Decidability.decide` reaches zero constants from this file at all.
-/


/-! #### Non-vacuity of the narrowed residual

The refutation of the unrestricted form turns on `fuel = 0` making its hypothesis hold at every
branch while carrying no information. A narrowed predicate that were true only because its
restricted antecedent is never satisfied would repeat that failure one level down, so the antecedent
is exhibited holding on runs the terminus actually produces.

Two things are shown, and they are shown by different means, which is stated rather than blurred.

**(a) The pass does real work, proved.** `saturateBlocked_multBranch_one_run` decides — at every
frame class and every positive fuel — that the post-blocking pass started at `[F(p → q)@⟨0,0⟩]`
returns a strictly longer branch, and `postBlockingSettlesAt_labelFree` is the settlement delivered
there. So the residual's conclusion is an obligation about a branch the pass built, never a no-op on
its input.

**(b) The full antecedent is satisfied by seed runs, measured.** The probe below runs the terminus's
own two calls in sequence — `expandBranchWithFuel` from the seed at a fuel figure, then
`saturateBlocked` on its open exit at that same figure — and reports three booleans: the run reached
an open exit, the pass strictly extended it, and the settlement test closed on the result. All three
are `true` at every frame class, on a propositional seed and a temporal one.

This half is a **checked measurement, not a kernel proof**, and the reason is worth stating so a
reader does not mistake one for the other: `expandBranchWithFuel` is compiled by well-founded
recursion and does not reduce definitionally, so a proof of the first equation would require
transcribing its eleven-formula open exit and unfolding the equation lemma once per engine step.
`#guard_msgs` makes the measurement a build-time obligation — the probe's value is checked by
`lake build` — which is the same standing `branchingWitness`'s non-vacuity `#eval` has in section
C7 above, and it is recorded with the same honesty about what it is.

**What the probe did not find.** Across fourteen formula shapes, four frame classes and three fuel
figures, no run made the settlement test fail — so no counterexample to the narrowed residual was
found, at any figure probed. That is evidence and not a proof, and the residual is carried as a
hypothesis accordingly. The same sweep also found `buildTableauAt`'s own guard never firing on those
shapes: the threaded tracker and the recomputed `armTracker` agreed everywhere, so the entry point
did not consult its post-blocking arm on any of them. The residual is therefore live but not yet
exercised by a probed formula, which is a fact about the probe's reach, not about the residual.

**And that warning was the right one: the residual is now refuted.** The subsection below decides
`PostBlockingSettlesRun` in the negative at `.Base`, `.Dense` and `.RTime`, at every positive fuel
figure and hence at the terminus's own. Nothing above is withdrawn — the measurements stand exactly
as recorded, and the pass really does do real work on the shapes probed — but no part of this
subsection should be read as evidence toward the residual's *truth*. The counterexample is reached
by doctoring an input the probes never varied, which is precisely what "a fact about the probe's
reach" left open. -/

/-- The witness pass extends its input strictly: one formula in, three out. The length fact behind
non-vacuity claim (a). -/
theorem multBranch_one_length_lt_multSettledBranch :
    (multBranch 1).length < multSettledBranch.length := by decide


/-! #### The verdict on the narrowed residual: **FALSE**, at the terminus's own fuel figure

`PostBlockingSettlesRun`'s narrowing restricted `(ob, oOrd, fuel)` to a pair some `expandBranchWithFuel` call at
this same fuel returned open. It did **not** restrict the run's other inputs, and one of them is not
inert: the `EventualityTracker` argument `tr`. The two blocked-set computations that the residual
needs to agree — `blockedTimes b ord fc tracker'` inside `expandOnceUnblocked`, where
`tracker' = fulfillEventualities b (registerEventualities b tr)`, and
`blockedTimes satBr satOrd fc (armTracker satBr)`, where `armTracker` re-seeds from
`EventualityTracker.empty` — share their branch, their ordering and their frame class, and differ in
**exactly** the tracker seed.

Blocking is *monotone in pending entries at the ancestor*: `isTemporallyBlockedSaturated` conjoins
`allEventualitiesFulfilledOrDuplicated`, which asks that every eventuality pending at `t` have some
pending entry with the same event formula and the same `isUntil` flag at the ancestor time. Adding a
pending entry at the ancestor therefore makes blocking fire *more* often, so a doctored `tr` yields a
**strictly larger** blocked set than the settlement test's recomputed `armTracker`: the engine skips
a time the settlement test still inspects. Two further facts make the exploit reachable —
`fulfillEventualities` discharges a pending entry only when its event formula occurs positively at
the entry's own **world** at some other time, so an entry parked at an otherwise-unused world is
never discharged; and `Branch.timeType`'s subset test ignores the world component, so the subset half
of blocking is satisfied across worlds while fulfillment, which is world-sensitive, is not.

**The predicate as written quantifies over `tr`, so the predicate as written is false.** This is
stated in the same voice as register entry 22's `fuel = 0` degeneracy, and it is not softened to a
caveat: the finding is that the narrowing was *incomplete*, and the completion is named below
(`PostBlockingSettlesSeedRun`) — carried as a hypothesis, never discharged.

**Why this refutation is a kernel proof where entry 24 records the positive direction as
prohibitive.** Entry 24 is right that `expandBranchWithFuel` is compiled by well-founded recursion
and does not reduce definitionally, so *proving* its half of the antecedent would mean transcribing
an engine exit and unfolding the equation lemma once per engine step. The witness below is returned
at the **first** step — the run reports `.saturated` immediately — so a single `rw` through the
equation lemma reaches the `.saturated` arm and the obligation closes. No engine step is
transcribed. That is the whole qualitative gain over a `#guard_msgs` measurement, and it is why the
verdict here is a theorem rather than an observation.
-/

/-- The witness branch: the verbatim open exit `expandBranchWithFuel` produces from
`seedBranch (p → q)` at `.Base` (its last eleven formulas, times chained `2 < 0 < 1 < 3`, engine
blocked set `[3, 2]`), augmented with world-1 machinery, the two `negPos` conclusions that exit left
outstanding at its blocked times, and the witness formula `T(p untl q)@⟨9,4⟩`.

Every part of the shape is load-bearing, and none of it is decoration:

* the tail is an **engine exit taken verbatim**, so the ancestor times are genuinely
  engine-saturated rather than hand-asserted — that is what makes `expandOnceNoFresh`'s `.saturated`
  verdict below honest instead of arranged;
* the world-1 block puts `T(p untl q)` into the ancestor's time type already expanded and fulfilled,
  which is what lets the duplication half of blocking be satisfied at time 4;
* `T(p untl q)@⟨9,4⟩` is the witness itself: `untlPos` mints a time, so `expandOnceNoFresh` skips it
  (`ruleMintsFreshTime`), and the post-blocking pass is by construction unable to remove it. -/
private def pbrWitnessBranch : Branch :=
  [ SignedFormula.neg .bot ⟨0, 2⟩
  , SignedFormula.neg .bot ⟨0, 3⟩
  , SignedFormula.pos (Formula.untl mfp mfq) ⟨1, 0⟩
  , SignedFormula.pos mfq ⟨1, 0⟩
  , SignedFormula.pos (Formula.untl (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨1, 0⟩
  , SignedFormula.pos (Formula.snce (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨1, 0⟩
  , SignedFormula.pos mfq ⟨1, 1⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨1, 1⟩
  , SignedFormula.pos (Formula.untl (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨1, 1⟩
  , SignedFormula.pos (Formula.snce (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨1, 1⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨1, 2⟩
  , SignedFormula.neg .bot ⟨1, 2⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨1, 3⟩
  , SignedFormula.neg .bot ⟨1, 3⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨1, 0⟩
  , SignedFormula.neg .bot ⟨1, 0⟩
  , SignedFormula.neg .bot ⟨1, 1⟩
  , SignedFormula.pos (Formula.untl mfp mfq) ⟨9, 4⟩
  -- the verbatim engine exit from `seedBranch (p → q)` begins here
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨0, 3⟩
  , SignedFormula.pos (Formula.untl (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨0, 1⟩
  , SignedFormula.pos (Formula.snce (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨0, 1⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨0, 2⟩
  , SignedFormula.neg .bot ⟨0, 1⟩
  , SignedFormula.pos (Formula.imp .bot .bot) ⟨0, 1⟩
  , SignedFormula.pos (Formula.untl (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨0, 0⟩
  , SignedFormula.pos (Formula.snce (Formula.imp .bot .bot) (Formula.imp .bot .bot)) ⟨0, 0⟩
  , SignedFormula.pos mfp ⟨0, 0⟩
  , SignedFormula.neg mfq ⟨0, 0⟩
  , SignedFormula.neg (Formula.imp mfp mfq) ⟨0, 0⟩ ]

/-- The witness ordering: the engine exit's own chain `2 < 0 < 1 < 3`, extended by `3 < 4` so the
witness's time 4 is the chain's last element and time 1 is its ancestor. The extension is the
minimum needed to place time 4 in the ordering at all; nothing else about it is chosen. -/
private def pbrWitnessOrd : TimeOrdering := { constraints := [(3, 4), (1, 3), (2, 0), (0, 1)] }

/-- The doctored tracker: one pending `q`-eventuality parked at world 7, time 0 — a world the
witness branch never mentions.

Both halves of that placement are load-bearing. The *time* is 0, which is the ancestor time
`allEventualitiesFulfilledOrDuplicated` consults for the pending `q`-eventuality that
`registerEventualities` derives from `T(p untl q)@⟨9,4⟩`, so the duplication test is satisfied and
time 4 joins the blocked set. The *world* is unused, so `fulfillEventualities` — which discharges an
entry only on finding `T q` at that entry's own world at some other time — never removes it. This
tracker is not one any engine run threads, and that is not a defect in the refutation: the residual
quantifies over the tracker, so a tracker it admits is a counterexample to it. -/
private def pbrDoctoredTracker : EventualityTracker :=
  { pending := [{ formula := mfq, label := ⟨7, 0⟩, isUntil := true }] }

/-- The witness branch is open, at every frame class. -/
theorem pbrWitness_findClosure_none (fc : FormalSystem.ProofSystem.FrameClass) :
    findClosure pbrWitnessBranch fc = none := by cases fc <;> rfl

/-- **The label-free pass reports `.saturated` on the witness at `.Base`.** Every candidate it can
still see has been discharged by the augmentation; the one formula that is not discharged,
`T(p untl q)@⟨9,4⟩`, is invisible to this pass because `untlPos` mints a time. -/
theorem pbrWitness_expandOnceNoFresh_saturated :
    expandOnceNoFresh pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.Base
      = (ExpansionResult.saturated, pbrWitnessOrd) := by rfl

/-- **The post-blocking pass hands the witness straight back, at every fuel figure.** This is the
existing fuel-universal step `saturateBlocked_eq_self_of_noFresh_saturated`, reused verbatim rather
than rebuilt: no induction on fuel, and no ladder of checked figures. -/
theorem pbrWitness_saturateBlocked_self (fuel : Nat) :
    saturateBlocked pbrWitnessBranch fuel pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.Base
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd)) :=
  saturateBlocked_eq_self_of_noFresh_saturated (pbrWitness_findClosure_none _)
    pbrWitness_expandOnceNoFresh_saturated fuel

/-- **The doctored run returns the witness open at its first step, at every positive fuel.**

This is the obligation register entry 24 records as prohibitive in the *positive* direction, and the
reason it is cheap here is worth stating rather than leaving to be rediscovered: the run reports
`.saturated` **immediately**, so `rw [expandBranchWithFuel]` unfolds the equation lemma exactly
**once** and the `.saturated` arm closes the goal. No engine step is transcribed and no equation
lemma is unfolded per step. That is what makes this a kernel proof where the corresponding positive
statement is a `#guard_msgs` measurement. -/
theorem pbrWitness_expandBranchWithFuel_eq (n : Nat) :
    expandBranchWithFuel pbrWitnessBranch (n + 1) pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.Base pbrDoctoredTracker {} 100 0
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd, {})) := by
  rw [expandBranchWithFuel]
  norm_num
  rfl

/-- **The settlement test does not close on the witness**, and it names the formula it is still
holding: `T(p untl q)@⟨9,4⟩`. The finder recomputes the blocked set with `armTracker`, which is
seeded from `EventualityTracker.empty` and so does not carry the doctored entry; time 4 is therefore
*not* blocked here, where the run's own computation blocked it. -/
theorem pbrWitness_settlement_fails :
    findUnexpandedUnblockedWith pbrWitnessBranch pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.Base
        (blockedTimes pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.Base
          (armTracker pbrWitnessBranch))
      = some (SignedFormula.pos (Formula.untl mfp mfq) ⟨9, 4⟩) := by rfl


/-- **The assembly, stated once and reused at every frame class the witness covers.** Given the
three class-specific `rfl` facts — the label-free pass is saturated on the witness, the doctored run
returns it open at `n + 1`, and the settlement test still reports the minting formula — the narrowed
residual is refuted at that class and that fuel. Nothing here is class-specific; only its three
hypotheses are. -/
private theorem postBlockingSettlesRun_false_succ_of
    {fc : FormalSystem.ProofSystem.FrameClass} (n : Nat)
    (hnf : expandOnceNoFresh pbrWitnessBranch pbrWitnessOrd fc
      = (ExpansionResult.saturated, pbrWitnessOrd))
    (hE : expandBranchWithFuel pbrWitnessBranch (n + 1) pbrWitnessOrd fc pbrDoctoredTracker {} 100 0
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd, {})))
    (hs : findUnexpandedUnblockedWith pbrWitnessBranch pbrWitnessOrd fc
        (blockedTimes pbrWitnessBranch pbrWitnessOrd fc (armTracker pbrWitnessBranch))
      = some (SignedFormula.pos (Formula.untl mfp mfq) ⟨9, 4⟩)) :
    ¬ PostBlockingSettlesRun fc (n + 1) := by
  intro h
  have hsb : saturateBlocked pbrWitnessBranch (n + 1) pbrWitnessOrd fc
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd)) :=
    saturateBlocked_eq_self_of_noFresh_saturated (pbrWitness_findClosure_none fc) hnf (n + 1)
  have hcon := h pbrWitnessBranch pbrWitnessBranch pbrWitnessOrd pbrWitnessOrd pbrDoctoredTracker
    {} {} 100 0 pbrWitnessBranch pbrWitnessOrd hE hsb
  rw [hs] at hcon
  exact absurd hcon (by simp)

/-- **Verdict: `PostBlockingSettlesRun` is FALSE at `.Base`, at every positive fuel figure.**

The five obligations above, assembled. Note what is *not* claimed: this is not a claim that
`buildTableauAt` ever threads `pbrDoctoredTracker`, and it does not have to be. The residual
quantifies over the tracker argument, so a tracker it admits refutes it — exactly as
`postBlockingSettles_fuel_zero_false` refutes the unrestricted form at an arm no caller reaches. -/
theorem postBlockingSettlesRun_false_succ (n : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.Base (n + 1) :=
  postBlockingSettlesRun_false_succ_of n pbrWitness_expandOnceNoFresh_saturated
    (pbrWitness_expandBranchWithFuel_eq n) pbrWitness_settlement_fails

/-- **The terminus's own fuel figure is always positive.** `mintPathBound` ends in `+ 1`, so
`mintPathBoundAt` is at least one, and `fuelFigure_pos` lifts that to the figure itself with no
hypothesis on any parameter. This is what carries the `n + 1` refutation to the figure the termini
are stated at. -/
theorem one_le_mintAwareFuelAt (Ucard Tmax mintBudget D β : Nat) :
    1 ≤ mintAwareFuelAt Ucard Tmax mintBudget D β :=
  fuelFigure_pos (by simp only [mintPathBoundAt, mintPathBound]; omega)

/-- **The un-`At` figure is positive too, by the same route.** The un-`At` counterpart of
`one_le_mintAwareFuelAt`: `mintPathBound` ends in `+ 1`, so `fuelFigure_pos` lifts that to
`mintAwareFuel` itself, with no hypothesis on any parameter. -/
theorem one_le_mintAwareFuel (Ucard Tmax mintBudget D β : Nat) :
    1 ≤ mintAwareFuel Ucard Tmax mintBudget D β :=
  fuelFigure_pos (by simp only [mintPathBound]; omega)

/-- **The dispatch's literal question, answered: FALSE.**

`PostBlockingSettlesRun` does not hold at the terminus's own fuel figure, at `.Base`, for **any**
values of the parameters — the figure is always at least one, and the predicate is refuted at every
positive figure.

**The consequence, stated without hedging.** Eight `_run` termini carried `PostBlockingSettlesRun
fc` as a hypothesis: four at `mintAwareFuelAt …`, refuted here, and four at the un-`At` figure
`mintAwareFuel …`, refuted by `postBlockingSettlesRun_mintAwareFuel_false` immediately below. At
`.Base` (and, by `postBlockingSettlesRun_false_dense` / `postBlockingSettlesRun_false_rtime`, at
`.Dense` and `.RTime`) that hypothesis is **false**: those statements were vacuous there, not merely
unproved, and a reader could not read them as delivering `buildTableauAt … .isSome` at those
classes. They have since been retired for that reason, together with a ninth that carried the
unrestricted `PostBlockingSettles` and is refuted at all four classes — see the retirement record in
section C12. This is the analogue
of `postBlockingExitSettled_false`, and it sits beside it in spirit: a residual decided in the
negative, recorded as a theorem rather than left to be inferred.

The repair is named below (`PostBlockingSettlesSeedRun`) and is carried as a hypothesis, not
discharged. -/
theorem postBlockingSettlesRun_terminusFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.Base
        (mintAwareFuelAt U.card Tmax mintBudget D β) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp (one_le_mintAwareFuelAt U.card Tmax mintBudget D β))
  rw [hn]
  exact postBlockingSettlesRun_false_succ n

/-- **The same verdict at the un-`At` figure.** The un-`At` counterpart of
`postBlockingSettlesRun_terminusFuel_false`, and the reason the vacuity claim covers **both** fuel
figures rather than only the `At` one: four of the nine retired `_run` termini were stated at
`mintAwareFuel …`, not at `mintAwareFuelAt …`. The frame class is written out in full because this
file opens only `FormalSystem.Syntax`. -/
theorem postBlockingSettlesRun_mintAwareFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.Base
        (mintAwareFuel U.card Tmax mintBudget D β) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp (one_le_mintAwareFuel U.card Tmax mintBudget D β))
  rw [hn]
  exact postBlockingSettlesRun_false_succ n


/-! ##### The record at the other frame classes

Refuting at one frame class already refutes the predicate, so what follows completes the **record**,
not the verdict.

`.Dense` and `.RTime` are covered: the same three `rfl` obligations go through unchanged there,
because none of the rules those classes add is applicable to the witness. `.ZTime` is **not** covered
by this witness, and the reason is recorded here rather than left implicit: at that class `priorUZ`
and `priorSZ` remain applicable to `T(⊤ untl ⊤)` and `T(⊤ snce ⊤)` at `⟨0,0⟩`, `⟨0,1⟩`, `⟨1,0⟩` and
`⟨1,1⟩`, so `expandOnceNoFresh` reports `.extended` rather than `.saturated` and the first obligation
fails. Adding those rules' conclusions to the witness would close it; that is mechanical and is left
undone deliberately, because the predicate is already refuted and a fourth class buys nothing beyond
tidiness. A future reader who wants it can re-run the measurement from the two rule names and the
four labels named here without re-deriving anything. -/

/-- The label-free pass is saturated on the witness at `.Dense`. -/
theorem pbrWitness_expandOnceNoFresh_saturated_dense :
    expandOnceNoFresh pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.Dense
      = (ExpansionResult.saturated, pbrWitnessOrd) := by rfl

/-- The doctored run returns the witness open at `.Dense`, at every positive fuel. -/
theorem pbrWitness_expandBranchWithFuel_eq_dense (n : Nat) :
    expandBranchWithFuel pbrWitnessBranch (n + 1) pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.Dense pbrDoctoredTracker {} 100 0
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd, {})) := by
  rw [expandBranchWithFuel]
  norm_num
  rfl

/-- The settlement test still reports the minting formula at `.Dense`. -/
theorem pbrWitness_settlement_fails_dense :
    findUnexpandedUnblockedWith pbrWitnessBranch pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.Dense
        (blockedTimes pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.Dense
          (armTracker pbrWitnessBranch))
      = some (SignedFormula.pos (Formula.untl mfp mfq) ⟨9, 4⟩) := by rfl

/-- The label-free pass is saturated on the witness at `.RTime`. -/
theorem pbrWitness_expandOnceNoFresh_saturated_rtime :
    expandOnceNoFresh pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.RTime
      = (ExpansionResult.saturated, pbrWitnessOrd) := by rfl

/-- The doctored run returns the witness open at `.RTime`, at every positive fuel. -/
theorem pbrWitness_expandBranchWithFuel_eq_rtime (n : Nat) :
    expandBranchWithFuel pbrWitnessBranch (n + 1) pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.RTime pbrDoctoredTracker {} 100 0
      = some (.inr (pbrWitnessBranch, pbrWitnessOrd, {})) := by
  rw [expandBranchWithFuel]
  norm_num
  rfl

/-- The settlement test still reports the minting formula at `.RTime`. -/
theorem pbrWitness_settlement_fails_rtime :
    findUnexpandedUnblockedWith pbrWitnessBranch pbrWitnessOrd
        FormalSystem.ProofSystem.FrameClass.RTime
        (blockedTimes pbrWitnessBranch pbrWitnessOrd FormalSystem.ProofSystem.FrameClass.RTime
          (armTracker pbrWitnessBranch))
      = some (SignedFormula.pos (Formula.untl mfp mfq) ⟨9, 4⟩) := by rfl

/-- **Verdict at `.Dense`: FALSE**, at every positive fuel figure. -/
theorem postBlockingSettlesRun_false_dense (n : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.Dense (n + 1) :=
  postBlockingSettlesRun_false_succ_of n pbrWitness_expandOnceNoFresh_saturated_dense
    (pbrWitness_expandBranchWithFuel_eq_dense n) pbrWitness_settlement_fails_dense

/-- **Verdict at `.RTime`: FALSE**, at every positive fuel figure. -/
theorem postBlockingSettlesRun_false_rtime (n : Nat) :
    ¬ PostBlockingSettlesRun FormalSystem.ProofSystem.FrameClass.RTime (n + 1) :=
  postBlockingSettlesRun_false_succ_of n pbrWitness_expandOnceNoFresh_saturated_rtime
    (pbrWitness_expandBranchWithFuel_eq_rtime n) pbrWitness_settlement_fails_rtime


/-! ##### The minimal further narrowing, named and carried

What the refutation above kills is the residual's quantification over `expandBranchWithFuel`'s
*other* inputs. `buildTableauAt` does not quantify over them: at the one place it reaches the
residual it has just made the call

```
expandBranchWithFuel [F φ @ initial] fuel TimeOrdering.empty fc (maxBranches := maxBranches)
```

which supplies `ord`, `tracker`, `applied` and `branchesUsed` at `TimeOrdering.empty`,
`EventualityTracker.empty`, `{}` and `0`. Quantifying over those four was over-quantification, in the
same sense and for the same reason that quantifying over `(ob, oOrd, fuel)` was: generality the
consuming site never asked for, bought at the price of admitting inputs no run produces.

`PostBlockingSettlesSeedRun` fixes exactly those four and leaves everything else quantified. The
bridge survives verbatim, so the repaired chain is non-vacuous again.

**This is not a proof of the narrowing, and the distinction is the whole point of this subsection.**
-/

/-- **The residual with the four arguments `buildTableauAt` always supplies at their defaults
fixed.** `ord := TimeOrdering.empty`, `tr := EventualityTracker.empty`, `ap := {}` and `bu := 0`;
`b`, `ob`, `oOrd`, `oAp`, `mb`, `satBr` and `satOrd` stay quantified.

**(i) What it fixes, and why exactly those four.** They are precisely the arguments the consuming
site instantiates itself. `buildTableauAt` makes one `expandBranchWithFuel` call, from the seed
branch, at the empty ordering, the empty tracker, the empty applied set and zero branches used. A
predicate quantifying over them was not more general in any way a caller could use; it was admitting
inputs the entry point never produces, which is what
`postBlockingSettlesRun_terminusFuel_false` exploits.

**(ii) It kills that witness, and the reason is checked rather than hoped for.** At
`tr := EventualityTracker.empty` the witness branch's own `expandOnceUnblocked` reports `.extended`,
not `.saturated` — the doctored entry is exactly what made time 4 blocked, and with it gone the run
does not return the witness open at all. The measured genuine run from the witness at the empty
tracker reaches an exit whose settlement test **passes**.

**(iii) It is NOT shown true, and a second, structurally independent refutation route against it is
unprobed.** `saturateBlocked` may *extend* `ob`, and `expandOnceNoFresh` ignores blocking entirely —
so it can do label-free work at a *blocked* time, and the formulas it adds can break
`isSubsetBlocked` (or `timeSaturated` at the ancestor) and thereby **unblock** a time carrying
label-minting work that `expandOnceNoFresh` itself skips. The settlement test on `satBr` would then
report it, with no doctored tracker anywhere. That route needs no over-quantification at all and was
not probed. Any future claim that this predicate holds must gate on it first; the cheapest probe is a
sweep reporting, for engine exits `ob`, whether
`blockedTimes satBr satOrd fc (armTracker satBr)` ever loses a time that
`blockedTimes ob oOrd fc (armTracker ob)` held. -/
def PostBlockingSettlesSeedRun (fc : FormalSystem.ProofSystem.FrameClass) (fuel : Nat) : Prop :=
  ∀ (b ob : Branch) (oOrd : TimeOrdering) (oAp : AppliedSet) (mb : Nat)
    (satBr : Branch) (satOrd : TimeOrdering),
    expandBranchWithFuel b fuel TimeOrdering.empty fc EventualityTracker.empty {} mb 0
      = some (.inr (ob, oOrd, oAp)) →
    saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd)) →
    findUnexpandedUnblockedWith satBr satOrd fc
      (blockedTimes satBr satOrd fc (armTracker satBr)) = none

/-- **The direction, fixed and stated in words**, in the same idiom as
`postBlockingSettlesRun_of_postBlockingSettles`. `PostBlockingSettlesSeedRun fc fuel` is the
**weaker** predicate: it speaks only about runs started from the four defaults, where the run form
speaks about all of them. So the implication runs
`PostBlockingSettlesRun fc fuel → PostBlockingSettlesSeedRun fc fuel`, and **every theorem restated
against the seed form is a strengthening of its `_run` original**, never a weakening. Register entry
7 is why this is stated rather than assumed. -/
theorem postBlockingSettlesSeedRun_of_postBlockingSettlesRun
    {fc : FormalSystem.ProofSystem.FrameClass} {fuel : Nat}
    (h : PostBlockingSettlesRun fc fuel) : PostBlockingSettlesSeedRun fc fuel :=
  fun b ob oOrd oAp mb satBr satOrd hE hsb =>
    h b ob TimeOrdering.empty oOrd EventualityTracker.empty {} oAp mb 0 satBr satOrd hE hsb

/-- **Bridge, at the seed narrowing.** `buildTableauAt_isSome_of_settlesRun` with
`PostBlockingSettlesRun fc fuel` exchanged for `PostBlockingSettlesSeedRun fc fuel`. The exchange is
available for exactly the reason the narrowing is the right one: `buildTableauAt`'s own
`expandBranchWithFuel` call supplies the four fixed arguments at the very values the narrowing pins
them to, so the proof skeleton survives byte for byte. -/
theorem buildTableauAt_isSome_of_settlesSeedRun {phi : Formula} {fuel : Nat}
    {fc : FormalSystem.ProofSystem.FrameClass} {maxBranches : Nat}
    (hpb : PostBlockingSettlesSeedRun fc fuel)
    (hexp : (expandBranchWithFuel [SignedFormula.neg phi Label.initial] fuel TimeOrdering.empty fc
      (maxBranches := maxBranches)).isSome = true) :
    (buildTableauAt phi fuel fc maxBranches).isSome = true := by
  unfold buildTableauAt
  simp only
  match hE : expandBranchWithFuel [SignedFormula.neg phi Label.initial] fuel TimeOrdering.empty fc
      (maxBranches := maxBranches) with
  | none => rw [hE] at hexp; simp at hexp
  | some (.inl closedBr) => simp
  | some (.inr (ob, oOrd, oAp)) =>
      dsimp only
      split
      · simp
      · match hsb : saturateBlocked ob fuel oOrd fc with
        | none => exact absurd hsb (saturateBlocked_ne_none ob fuel oOrd fc)
        | some (.inl cb) => simp
        | some (.inr (satBr, satOrd)) =>
            dsimp only
            split
            · simp
            · rename_i sf2 hg2
              rw [hpb _ _ _ _ _ _ _ hE hsb] at hg2
              simp at hg2

/-- The `_of_budget_fixed` terminus at the seed narrowing — restated so it rests on a hypothesis
this file has **not** refuted. Exactly one entry of the hypothesis list differs from the retired
`buildTableauAt_isSome_of_budget_fixed_run`; the fuel expression is reused byte for byte.

This is the representative restatement, not the family. The nine `_run` termini it once stood beside
have been retired as vacuous (see the retirement record in section C12), so this is now the only
terminus in the file stated at a narrowed post-blocking residual. Widening the seed narrowing to the
rest of that family is deliberately deferred rather than forgotten — but note that widening it now
means restating landed termini, not repairing surviving ones. -/
theorem buildTableauAt_isSome_of_budget_fixed_seedRun
    {fc : FormalSystem.ProofSystem.FrameClass} {U : Finset SignedFormula}
    {mintBudget Tmax D β : Nat} (phi : Formula) (maxBranches : Nat)
    (hβ : 3 ≤ β) (hUcl : UniverseClosedAt fc U) (hD : DifficultyBounded fc U D)
    (hmint : MintPaysForTimeFixed fc U Tmax) (harm : ArmSettlement fc)
    (hpb : PostBlockingSettlesSeedRun fc (mintAwareFuelAt U.card Tmax mintBudget D β))
    (hseed : ∀ x ∈ seedBranch phi, x ∈ U)
    (hmb : 10 * U.card ≤ mintBudget)
    (hT : (seedBranch phi).knownTimes.toFinset.card + mintBudget ≤ Tmax)
    (hbud : β * mintAwareFuelAt U.card Tmax mintBudget D β ≤ maxBranches) :
    (buildTableauAt phi (mintAwareFuelAt U.card Tmax mintBudget D β) fc maxBranches).isSome
      = true := by
  refine buildTableauAt_isSome_of_settlesSeedRun hpb ?_
  exact expandBranchWithFuel_isSome_of_budget_fixed hβ hUcl hD hmint harm
    (seedBranch phi) TimeOrdering.empty EventualityTracker.empty {} maxBranches 0
    hseed (runInvariant_initial _) hmb hT (by omega)

section PostBlockingRunProbe

/-- The terminus's own two calls, run in sequence and reported as three booleans: the seed run
reached an open exit; the post-blocking pass strictly extended that exit; the blocking-aware
saturation test closed on the pass's output. -/
private def postBlockingRunProbe (phi : Formula) (fuel : Nat)
    (fc : FormalSystem.ProofSystem.FrameClass) : Bool × Bool × Bool :=
  match expandBranchWithFuel (seedBranch phi) fuel TimeOrdering.empty fc
      (maxBranches := 50000) with
  | some (.inr (ob, oOrd, _)) =>
      match saturateBlocked ob fuel oOrd fc with
      | some (.inr (satBr, satOrd)) =>
          (true, ob.length < satBr.length,
            (findUnexpandedUnblockedWith satBr satOrd fc
              (blockedTimes satBr satOrd fc (armTracker satBr))).isNone)
      | _ => (true, false, false)
  | _ => (false, false, false)

-- The propositional seed `p → q`, at every frame class. Frame classes are written out rather
-- than abbreviated: inside this namespace the `.Dense` shorthand resolves elsewhere, and the
-- probe silently reported an unexpanded run until the names were qualified.
/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.imp mfp mfq) 40 FormalSystem.ProofSystem.FrameClass.Base

/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.imp mfp mfq) 40 FormalSystem.ProofSystem.FrameClass.Dense

/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.imp mfp mfq) 40 FormalSystem.ProofSystem.FrameClass.ZTime

/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.imp mfp mfq) 40 FormalSystem.ProofSystem.FrameClass.RTime

-- The temporal seed `F p = ⊤ U p`, so the witness set is not purely propositional.
/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.untl (Formula.imp .bot .bot) mfp) 40
  FormalSystem.ProofSystem.FrameClass.Base

/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.untl (Formula.imp .bot .bot) mfp) 40
  FormalSystem.ProofSystem.FrameClass.RTime

-- `□p`, whose expansion mints a fresh world — the shape whose *unrestricted* counterexample
-- `freshWorldBranch` is. The engine never hands that branch to the pass, and the run settles.
/-- info: (true, true, true) -/
#guard_msgs in
#eval postBlockingRunProbe (Formula.box mfp) 40 FormalSystem.ProofSystem.FrameClass.Base

end PostBlockingRunProbe

end PostBlockingSettlesRefutation

/-! ## D3. The residual, discharged at a **nonempty** universe: the `untl`/`snce`-free fragment

**What this section delivers.** `MintPaysForTime fc U Tmax` — the predicate this file started from,
not a repair of it — proved outright, at every frame class and every `Tmax`, for every universe
whose formulas carry no `untl` and no `snce` node. Section D2 left the predicate discharged only at
`U = ∅` (`mintPaysForTime_empty`); this section moves the boundary off the empty universe and onto a
syntactic condition that a genuinely nonempty stock satisfies — in particular the whole **modal
fragment**: atoms, `⊥`, `→`, `□`, and everything built from them, which is `S5` over a single
moment sitting inside the bimodal language.

**Why the two blockers section D2 records do not bite here.** They are both blockers on a *time
mint*, and in this fragment no time is ever minted at all:

* *The engine-level assembly.* D2's residual blocker needs the picked rule's identity threaded to
  the successor so a **per-rule payment** (disjunct 2 or 3) can be cashed there. Here no payment is
  ever needed: the argument runs entirely in disjunct 1, and disjunct 1 is uniform in the rule. All
  the pick has to supply is the *negative* fact `ruleMintsFreshTime r = false`, which
  `pick_stage_source_noMint` reads straight off `isApplicable` without destructuring a single rule
  arm.
* *The density coordinate.* `densityRule` is the rule register entries 17 and 20 name as reachable
  by no disjunct for any `σ` whatsoever. It is nonetheless harmless here, and for a reason that is
  worth stating because it is not the frame-class gate: `isApplicable .densityRule sf fc` requires
  `sf.formula` to match `.allFuture _`, and `Formula.allFuture φ` is
  `((⊥ → ⊥) untl (φ → ⊥)) → ⊥` — an `untl` node. So the shape gate rejects it before the
  `Dense ≤ fc` gate is ever consulted, and the discharge below carries **no frame-class
  restriction**. That is strictly better than the "every frame class except `.Dense`/`.RTime`"
  outcome D2's blocker anticipated.

**The shape of the argument, in one line.** Every one of the nine members of `freshTimeRules` is
gated by `isApplicable` on a formula shape that contains an `untl` or an `snce` node
(`allFutureNeg`, `allPastNeg`, `densityRule` through the `allFuture`/`allPast` abbreviations;
`someFuturePos`, `somePastPos`, `untlPos`, `sncePos`, `untlNeg`, `snceNeg` through their `as…?`
views). The engine's other two stages run exactly one rule each — `serialityRule` and
`timeLinearity` — and neither is in the census. So on an `untl`/`snce`-free branch the picked rule
never mints, `applyRule_emitted_time_mem` applies at every emission, and the successor's known
times are a subset of the predecessor's. Both of disjunct 1's conjuncts follow: the cardinality
directly, and the rank because `splitOrderedRank` is monotone in `knownTimes` and antitone in the
constraint list, which `expandOnceUnblocked_ord_mono` only ever extends.

**What this is not.** It is not a discharge at a universe containing a temporal operator, and it
cannot be turned into one: `mintPaysForTime_untlNeg_false` refutes the predicate at a universe whose
formulas are `untl`-headed, so the syntactic condition below is not removable. The two named next
steps of register entry 20 stand unchanged for the temporal fragment. -/

/-- **The syntactic condition**: no `untl` and no `snce` node anywhere in the formula.

Stated on the raw constructors rather than on the `as…?` views, so it is manifestly closed under
subformulas and manifestly satisfied by the modal fragment. It is *sufficient* rather than
necessary — `asUntil?` also rejects `untl ⊤ φ`, and `isApplicable` rejects some shapes this
predicate admits — and sufficiency is all the discharge needs. -/
def untlSnceFree : Formula → Bool
  | .atom _ => true
  | .bot => true
  | .imp a b => untlSnceFree a && untlSnceFree b
  | .box a => untlSnceFree a
  | .untl _ _ => false
  | .snce _ _ => false

/-- The modal fragment is `untl`/`snce`-free: `□` preserves the condition. -/
theorem untlSnceFree_box {φ : Formula} (h : untlSnceFree φ = true) :
    untlSnceFree φ.box = true := by simpa [untlSnceFree] using h

/-- …and so does `→`, hence `¬`, `∧`, `∨` and `◇` as well, all of which are `imp`/`box` composites
in this language. -/
theorem untlSnceFree_imp {φ ψ : Formula} (hφ : untlSnceFree φ = true)
    (hψ : untlSnceFree ψ = true) : untlSnceFree (φ.imp ψ) = true := by
  simp [untlSnceFree, hφ, hψ]

/-! ### The six shape views, all `none` on an `untl`/`snce`-free formula

One per `as…?` view `isApplicable` consults for a time-minting rule. Each is a two-line `cases`;
they are listed separately rather than bundled because `isApplicable`'s arms consult them
individually and the sweep below feeds them in by name. -/

theorem asUntil_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asUntil? φ = none := by
  cases φ <;> simp_all [untlSnceFree, asUntil?]

theorem asSince_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asSince? φ = none := by
  cases φ <;> simp_all [untlSnceFree, asSince?]

theorem asSomeFuture_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asSomeFuture? φ = none := by
  cases φ <;> simp_all [untlSnceFree, asSomeFuture?]

theorem asSomePast_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asSomePast? φ = none := by
  cases φ <;> simp_all [untlSnceFree, asSomePast?]

/-- The `allFuture` view needs one extra split: `Formula.allFuture φ` is an `imp` whose *antecedent*
is the `untl` node, so the condition has to be pushed through the implication before the
contradiction is visible. -/
theorem asAllFuture_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asAllFuture? φ = none := by
  cases φ with
  | imp a b => cases a <;> simp_all [untlSnceFree, asAllFuture?]
  | _ => simp_all [untlSnceFree, asAllFuture?]

/-- The past mirror. -/
theorem asAllPast_eq_none_of_untlSnceFree {φ : Formula} (h : untlSnceFree φ = true) :
    asAllPast? φ = none := by
  cases φ with
  | imp a b => cases a <;> simp_all [untlSnceFree, asAllPast?]
  | _ => simp_all [untlSnceFree, asAllPast?]

/-- **No time-minting rule is applicable to an `untl`/`snce`-free formula**, at any frame class.

The nine-arm sweep over `freshTimeRules`, run against `isApplicable`'s own match. Note what does
*not* appear in the proof: no frame class is inspected. `densityRule`'s arm is
`| .densityRule, .pos, .allFuture _ => decide (FrameClass.Dense ≤ fc)`, and the shape half of that
arm already fails, so the `decide` is never reached. This is why the discharge below is universal in
`fc` where register entry 20 expected a density-free restriction. -/
theorem isApplicable_eq_false_of_untlSnceFree {r : TableauRule} {sf : SignedFormula}
    {fc : FormalSystem.ProofSystem.FrameClass}
    (hmint : ruleMintsFreshTime r = true) (hfree : untlSnceFree sf.formula = true) :
    isApplicable r sf fc = false := by
  have h1 := asUntil_eq_none_of_untlSnceFree hfree
  have h2 := asSince_eq_none_of_untlSnceFree hfree
  have h3 := asSomeFuture_eq_none_of_untlSnceFree hfree
  have h4 := asSomePast_eq_none_of_untlSnceFree hfree
  have h5 := asAllFuture_eq_none_of_untlSnceFree hfree
  have h6 := asAllPast_eq_none_of_untlSnceFree hfree
  obtain ⟨sign, φ, l⟩ := sf
  simp only at h1 h2 h3 h4 h5 h6 hfree
  cases r <;> try exact Bool.noConfusion hmint
  all_goals (
    cases sign <;>
    (cases φ with
     | imp a b =>
        cases a <;>
          simp_all [isApplicable, asAllFuture?, asAllPast?, asUntil?, asSince?,
            asSomeFuture?, asSomePast?, untlSnceFree]
     | _ =>
        simp_all [isApplicable, asAllFuture?, asAllPast?, asUntil?, asSince?,
          asSomeFuture?, asSomePast?, untlSnceFree]))

/-- **The first stage reports only applicable rules.** The `isApplicable` companion of
`findApplicableRule_applyRule_pair`, read off the same `findSome?` structure: every arm of the
`if isApplicable rule sf fc then … else none` body that can return `some` sits under the `then`. -/
theorem findApplicableRule_isApplicable {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass}
    {r : TableauRule} {res : RuleResult} {o : TimeOrdering}
    (h : findApplicableRule sf b ord fc = some (r, res, o)) :
    isApplicable r sf fc = true := by
  unfold findApplicableRule at h
  obtain ⟨rule, -, hr⟩ := List.exists_of_findSome?_eq_some h
  repeat' split at hr
  all_goals simp_all

/-- **The first stage cannot pick a minting rule on an `untl`/`snce`-free trigger.** -/
theorem findApplicableRule_not_mintsFreshTime {sf : SignedFormula} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    {r : TableauRule} {res : RuleResult} {o : TimeOrdering}
    (hfree : untlSnceFree sf.formula = true)
    (h : findApplicableRule sf b ord fc = some (r, res, o)) :
    ruleMintsFreshTime r = false := by
  rcases hm : ruleMintsFreshTime r with _ | _
  · rfl
  · exact absurd (findApplicableRule_isApplicable h)
      (by simp [isApplicable_eq_false_of_untlSnceFree hm hfree])

/-- **`pick_stage_source` with the no-mint fact attached**, the exact counterpart of
`pick_stage_source_guarded` in the time coordinate. The three stages differ only in how the fact
arrives: stage one has it from `findApplicableRule_not_mintsFreshTime`, stages two and three from
running exactly one rule each, neither of which is in the census
(`findApplicableSerialRule_rule`, `findApplicableLinearityRule_rule`). -/
private theorem pick_stage_source_noMint (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) (tr : EventualityTracker)
    (hfree : ∀ x ∈ b, untlSnceFree x.formula = true) :
    ∀ r res o,
      (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
       | some sf => findApplicableRule sf b ord fc
       | none =>
         match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
             && (findApplicableSerialRule sf b ord).isSome) with
         | some sf => findApplicableSerialRule sf b ord
         | none =>
           match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
               && (findApplicableLinearityRule sf b ord).isSome) with
           | some sf => findApplicableLinearityRule sf b ord
           | none => none) = some (r, res, o) →
      ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧ ruleMintsFreshTime r = false := by
  intro r res o h
  rcases hpick : findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with _ | sf
  · rw [hpick] at h
    rcases hser : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                             && (findApplicableSerialRule sf b ord).isSome) with _ | sf2
    · rw [hser] at h
      rcases hlin : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                               && (findApplicableLinearityRule sf b ord).isSome) with _ | sf3
      · rw [hlin] at h
        simp only at h
        exact absurd h (by simp)
      · rw [hlin] at h
        simp only at h
        refine ⟨sf3, List.mem_of_find?_eq_some hlin,
          findApplicableLinearityRule_applyRule_pair h, ?_⟩
        rw [findApplicableLinearityRule_rule h]
        rfl
    · rw [hser] at h
      simp only at h
      refine ⟨sf2, List.mem_of_find?_eq_some hser,
        findApplicableSerialRule_applyRule_pair h, ?_⟩
      rw [findApplicableSerialRule_rule h]
      rfl
  · rw [hpick] at h
    simp only at h
    have hmem : sf ∈ b := by
      unfold findUnexpandedUnblockedWith at hpick
      exact List.mem_of_find?_eq_some hpick
    exact ⟨sf, hmem, findApplicableRule_applyRule_pair h,
      findApplicableRule_not_mintsFreshTime (hfree sf hmem) h⟩

/-! ### The time sweep with `OrdTimesKnown` traded for branch-level freeness

`applyRule_emitted_time_mem` (section D1) carries `OrdTimesKnown b ord`, and
`applyRule_emitted_time_mem_ordTimesKnown_needed` decides that the *unconditional* statement is
false. Neither fact settles what happens on this section's fragment, and the difference matters
downstream: `UniverseClosedAt`'s clause 1 hands over `∀ x ∈ b, x ∈ signedUniverse C L`, from which
branch-level `untlSnceFree` follows in one line, but it hands over nothing at all about the
ordering. A statement whose only currency is branch-level freeness therefore reaches sites the
`OrdTimesKnown` form cannot.

`haux` is consumed at exactly three closer families in the D1 sweep —
`mem_filterMap_futureOf_time haux`, `mem_filterMap_pastOf_time haux`, and (through
`applyRule_orderTrichotomy_emitted_time`) `mem_knownTimes_of_mem_pastOf haux` — spread across
exactly five rule arms. All five are shape-gated, and the five lemmas below say so one arm at a
time. Four are gated by the *trigger*: `.allFuturePos` and `.allPastPos` match the raw
`Formula.allFuture` / `Formula.allPast` shape, whose head is an `untl` / `snce` node, and
`.someFutureNeg` / `.somePastNeg` consult `asSomeFuture?` / `asSomePast?`, which the view lemmas
above already return `none` for. The fifth is gated by the *branch*: `.orderTrichotomy`'s `fires`
guard demands `branch.contains (SignedFormula.neg d l0)` for one of three `Formula.someFuture`-headed
disjuncts, and an `untl`/`snce`-free branch carries no `untl`-headed formula at all. That asymmetry
is why the restricted sweep takes a branch-level hypothesis rather than a trigger-level one.

Each exclusion concludes `emitted = []` rather than the weaker "every emission is at a known time":
on this fragment the four propagation arms and the trichotomy arm do not merely emit safely, they
do not fire. -/

/-- `.allFuturePos` does not fire on an `untl`/`snce`-free trigger. Its arm matches the raw shape
`Formula.allFuture ψ = ((⊥ → ⊥) untl (ψ → ⊥)) → ⊥`, so the condition has to be pushed through the
implication before the `untl` node is visible — the same extra split
`asAllFuture_eq_none_of_untlSnceFree` needs, and for the same reason. Routing through that view
lemma is not available here: `applyRule`'s arm is a constructor pattern, not a view. -/
theorem applyRule_allFuturePos_emitted_nil_of_untlSnceFree
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hfree : untlSnceFree sf.formula = true) :
    (applyRule .allFuturePos sf b ord).1.emitted = [] := by
  obtain ⟨sign, φ, l⟩ := sf
  simp only at hfree
  cases sign
  case pos =>
    cases φ with
    | imp a c => cases a <;> simp_all [applyRule, untlSnceFree, RuleResult.emitted]
    | _ => simp [applyRule, RuleResult.emitted]
  case neg => simp [applyRule, RuleResult.emitted]

/-- The past mirror, through `Formula.allPast` and `snce`. -/
theorem applyRule_allPastPos_emitted_nil_of_untlSnceFree
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hfree : untlSnceFree sf.formula = true) :
    (applyRule .allPastPos sf b ord).1.emitted = [] := by
  obtain ⟨sign, φ, l⟩ := sf
  simp only at hfree
  cases sign
  case pos =>
    cases φ with
    | imp a c => cases a <;> simp_all [applyRule, untlSnceFree, RuleResult.emitted]
    | _ => simp [applyRule, RuleResult.emitted]
  case neg => simp [applyRule, RuleResult.emitted]

/-- `.someFutureNeg` is view-gated: its arm is `| .someFutureNeg, .neg, φ => match asSomeFuture? φ`,
and `asSomeFuture_eq_none_of_untlSnceFree` sends the view to `none`, hence the arm to
`.notApplicable`. -/
theorem applyRule_someFutureNeg_emitted_nil_of_untlSnceFree
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hfree : untlSnceFree sf.formula = true) :
    (applyRule .someFutureNeg sf b ord).1.emitted = [] := by
  obtain ⟨sign, φ, l⟩ := sf
  simp only at hfree
  have h := asSomeFuture_eq_none_of_untlSnceFree hfree
  cases sign <;> simp [applyRule, h, RuleResult.emitted]

/-- The past mirror, through `asSomePast?`. -/
theorem applyRule_somePastNeg_emitted_nil_of_untlSnceFree
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hfree : untlSnceFree sf.formula = true) :
    (applyRule .somePastNeg sf b ord).1.emitted = [] := by
  obtain ⟨sign, φ, l⟩ := sf
  simp only at hfree
  have h := asSomePast_eq_none_of_untlSnceFree hfree
  cases sign <;> simp [applyRule, h, RuleResult.emitted]

/-- **The branch-level step**: an `untl`-headed formula is not carried by an `untl`/`snce`-free
branch, at any sign and any label. Named separately because it is the one step of the
`.orderTrichotomy` exclusion that is about the branch rather than about `applyRule`'s match, and it
should fail in isolation if it fails. -/
theorem untl_not_contains_of_untlSnceFree {b : Branch}
    (hbfree : ∀ x ∈ b, untlSnceFree x.formula = true)
    {s : Sign} {x y : Formula} {l : Label} :
    b.contains ⟨s, Formula.untl x y, l⟩ = false := by
  rcases hc : b.contains (⟨s, Formula.untl x y, l⟩ : SignedFormula) with _ | _
  · rfl
  · have hm : (⟨s, Formula.untl x y, l⟩ : SignedFormula) ∈ b := mem_of_branch_contains hc
    have := hbfree _ hm
    simp [untlSnceFree] at this

/-- `.orderTrichotomy` does not fire on an `untl`/`snce`-free **branch**. Its `fires` guard ends in
`ds.any fun d => branch.contains (SignedFormula.neg d l0)`, where every `d ∈ disjuncts φ ψ` is
`Formula.someFuture (…) = Formula.untl ⊤ (…)`. So no candidate fires, `candidates.find? fires` is
`none`, and the arm reports `.notApplicable`.

This is the arm the trigger-level hypothesis does not reach: nothing about `sf`'s own shape
constrains what the branch carries, which is why the restricted sweep below takes `hbfree`. -/
theorem applyRule_orderTrichotomy_emitted_nil_of_untlSnceFree
    {sf : SignedFormula} {b : Branch} {ord : TimeOrdering}
    (hbfree : ∀ x ∈ b, untlSnceFree x.formula = true) :
    (applyRule .orderTrichotomy sf b ord).1.emitted = [] := by
  obtain ⟨sign, φ, l⟩ := sf
  cases sign
  case neg => simp [applyRule, RuleResult.emitted]
  case pos =>
    simp only [applyRule]
    repeat' split
    all_goals (try simp only [RuleResult.emitted])
    rename_i heq
    have hfires := List.find?_some heq
    simp only [Formula.someFuture, SignedFormula.neg, List.any_cons, List.any_nil,
      Bool.and_eq_true, Bool.or_eq_true, untl_not_contains_of_untlSnceFree hbfree] at hfires
    simp at hfires

/-- An arm that emits nothing meets the sweep's conclusion vacuously. Stated separately so the five
exclusions can be fed into the sweep's `first` chain as one-line `exact`s. -/
theorem time_mem_of_emitted_nil {b : Branch} {r : RuleResult × TimeOrdering}
    (h : r.1.emitted = []) : ∀ g ∈ r.1.emitted, g.label.time ∈ b.knownTimes := by
  rw [h]; simp

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **The time sweep on the `untl`/`snce`-free fragment, without `OrdTimesKnown`.**

`applyRule_emitted_time_mem` with `haux : OrdTimesKnown b ord` replaced by
`hbfree : ∀ x ∈ b, untlSnceFree x.formula = true`. Three things about it, and no more:

* **It is incomparable to the original, not stronger.** It trades a semantic run invariant for a
  syntactic branch condition. Neither hypothesis implies the other: an ordering can be
  `OrdTimesKnown` over a branch carrying `untl` formulas, and an `untl`/`snce`-free branch can sit
  under an ordering reaching times it does not know. Both statements are needed, and both are kept.
* **It does not contradict `applyRule_emitted_time_mem_ordTimesKnown_needed`.** What that theorem
  refutes is the *unconditional* statement — no `OrdTimesKnown`, no syntactic condition, nothing.
  Its witness branch is `[T(G p)]`, and `Formula.allFuture p` is an `untl` node, so the witness
  fails `hbfree` outright. The refutation stands exactly as stated.
* **The five arms that consume `OrdTimesKnown` are precisely the five the syntactic hypothesis
  shape-gates**: `.allFuturePos` and `.allPastPos` (raw `allFuture` / `allPast` constructor
  patterns), `.someFutureNeg` and `.somePastNeg` (the `asSomeFuture?` / `asSomePast?` views), and
  `.orderTrichotomy` (the `fires` guard's branch lookup). The five exclusions above are inserted
  into the sweep's `first` chain *ahead of* the closers that would have needed `haux`, and the
  `mem_filterMap_futureOf_time` / `mem_filterMap_pastOf_time` alternatives are then simply absent:
  no arm reaches them. Every other arm is closed by the D1 sweep's own `haux`-free alternatives,
  copied verbatim so that the ordering property that script's docstring records — every closer a
  backtrackable `refine … ?_`, never a term-level `by` that could absorb a failing goal into
  `sorryAx` — is preserved.

`hmint : ruleMintsFreshTime rule = false` is retained. It is plausibly droppable on this fragment,
since an `untl`/`snce`-free trigger fails every minting rule's shape view
(`isApplicable_eq_false_of_untlSnceFree`), but `applyRule` is not gated by `isApplicable`, so
dropping it is a separate proof and not one this statement needs. -/
theorem applyRule_emitted_time_mem_of_untlSnceFree {rule : TableauRule} {sf : SignedFormula}
    {b : Branch} {ord : TimeOrdering}
    (hsf : sf ∈ b) (hbfree : ∀ x ∈ b, untlSnceFree x.formula = true)
    (hmint : ruleMintsFreshTime rule = false) :
    ∀ g ∈ (applyRule rule sf b ord).1.emitted, g.label.time ∈ b.knownTimes := by
  have ht : sf.label.time ∈ b.knownTimes := mem_knownTimes_of_mem hsf
  have hfree : untlSnceFree sf.formula = true := hbfree sf hsf
  cases sf with
  | mk sign formula label =>
    cases rule <;> first
      | exact Bool.noConfusion hmint
      | exact time_mem_of_emitted_nil (applyRule_allFuturePos_emitted_nil_of_untlSnceFree hfree)
      | exact time_mem_of_emitted_nil (applyRule_allPastPos_emitted_nil_of_untlSnceFree hfree)
      | exact time_mem_of_emitted_nil (applyRule_someFutureNeg_emitted_nil_of_untlSnceFree hfree)
      | exact time_mem_of_emitted_nil (applyRule_somePastNeg_emitted_nil_of_untlSnceFree hfree)
      | exact time_mem_of_emitted_nil (applyRule_orderTrichotomy_emitted_nil_of_untlSnceFree hbfree)
      | (cases sign <;> simp only [applyRule] <;> (repeat' split) <;>
          (try contradiction) <;>
          intro g hg <;>
          repeat' first
            | exact ht
            | exact mem_knownTimes_of_mem hg
            | (refine mem_identifyTime_time_at_trigger (ord := ord) ?_ hg
               assumption)
            | (refine mem_identifyTime_time_at_trigger_oriented (ord := ord) ?_ hg
               assumption)
            | (refine mem_filterMap_const_time_mem (t := label.time) ht ?_ hg
               clear hg
               intro x y hy
               repeat' first
                 | split at hy
                 | simp only [Option.some.injEq] at hy
               all_goals first
                 | (subst hy; rfl)
                 | (simp only [reduceCtorEq] at hy))
            | (refine mem_filterMap_time ?_ hg
               clear hg
               intro x y hy
               repeat' first
                 | split at hy
                 | simp only [Option.some.injEq] at hy
               all_goals first
                 | (subst hy; rfl)
                 | (simp only [reduceCtorEq] at hy))
            | (simp only [RuleResult.emitted, Branch.boxPosFormulas, Branch.diamondNegFormulas,
                 List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
                 List.append_nil, List.mem_cons, List.mem_append, List.not_mem_nil,
                 or_false, List.mem_filter] at hg)
            | (subst hg; exact ht)
            | (rcases hg with hg | hg))

/-- One pick stage adds no known time, given that its rule mints none. The join of
`applyRule_emitted_time_mem` with the no-mint source, in the shape `pickBranches_world_dichotomy`
uses for the world coordinate. -/
theorem pickBranches_knownTimes_subset {b : Branch} {ord : TimeOrdering}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (haux : OrdTimesKnown b ord)
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧
      ruleMintsFreshTime r = false) :
    ∀ nb ∈ pickBranches b p, ∀ t ∈ nb.knownTimes, t ∈ b.knownTimes := by
  rcases p with _ | ⟨r, res, o⟩
  · simp [pickBranches]
  · obtain ⟨sf, hsf, hA, hnm⟩ := hp r res o rfl
    intro nb hnb t ht
    obtain ⟨-, hsub⟩ := resultBranch_sub (b := b) (nb := nb) (res := res) hnb
    obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_knownTimes ht
    rcases hsub x hx with hxe | hxb
    · refine applyRule_emitted_time_mem (rule := r) (sf := sf) (ord := ord) hsf haux hnm x ?_
      rw [hA]
      exact hxe
    · exact mem_knownTimes_of_mem hxb

/-- **No unordered successor of an `untl`/`snce`-free branch carries a new time.**

The engine-level statement, and the one the discharge consumes. Compare
`unorderedSuccessor_time_dichotomy`, which is unconditional and therefore has to admit
`t = b.nextTime` as a second case: here the second case is *closed*, at the cost of the syntactic
hypothesis. Routed through `pick_branches_eq` and `pick_stage_source_noMint`, so the three-stage
pick is not destructured a second time. -/
theorem unorderedSuccessor_knownTimes_subset {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (haux : OrdTimesKnown b ord) (hfree : ∀ x ∈ b, untlSnceFree x.formula = true) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ t ∈ nb.knownTimes, t ∈ b.knownTimes := by
  have keyB : unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1
      = pickBranches b
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_branches_eq
  rw [keyB]
  exact pickBranches_knownTimes_subset haux (pick_stage_source_noMint b ord fc tr hfree)

/-- The `haux`-free twin of `pickBranches_knownTimes_subset`, routed through
`applyRule_emitted_time_mem_of_untlSnceFree` at the one site where the original calls
`applyRule_emitted_time_mem`. The source obligation `hp` is unchanged and already carries
`ruleMintsFreshTime r = false`, so the restricted sweep's `hmint` costs nothing here; the only new
currency is the branch-level syntactic condition, which `pick_stage_source_noMint`'s own caller
already has in hand. -/
private theorem pickBranches_knownTimes_subset_of_untlSnceFree {b : Branch} {ord : TimeOrdering}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (hbfree : ∀ x ∈ b, untlSnceFree x.formula = true)
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧
      ruleMintsFreshTime r = false) :
    ∀ nb ∈ pickBranches b p, ∀ t ∈ nb.knownTimes, t ∈ b.knownTimes := by
  rcases p with _ | ⟨r, res, o⟩
  · simp [pickBranches]
  · obtain ⟨sf, hsf, hA, hnm⟩ := hp r res o rfl
    intro nb hnb t ht
    obtain ⟨-, hsub⟩ := resultBranch_sub (b := b) (nb := nb) (res := res) hnb
    obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_knownTimes ht
    rcases hsub x hx with hxe | hxb
    · refine applyRule_emitted_time_mem_of_untlSnceFree (rule := r) (sf := sf) (ord := ord)
        hsf hbfree hnm x ?_
      rw [hA]
      exact hxe
    · exact mem_knownTimes_of_mem hxb

/-- **The engine-level statement without the run invariant.** `unorderedSuccessor_knownTimes_subset`
with `OrdTimesKnown b ord` gone: its `hfree` was already exactly the hypothesis the restricted sweep
needs, so the `haux`-free form is strictly stronger at no new cost.

This is the declaration section D4's boundary block said would be needed and did not have. Its point
is not economy — the original's `haux` is available at every site that currently consumes it, via
`hri.ordTimesKnown` — but *reachability*: `UniverseClosedAt`'s clause 1 quantifies `ord` universally
and unconstrained, so it can never supply `OrdTimesKnown b ord`, while branch-level freeness follows
from clause 1's own `∀ x ∈ b, x ∈ signedUniverse C L` in one line.

The original is retained with its signature byte-identical and its proof untouched: it is cited by
name in this section's prose and in D4's boundary block, and `mintPaysForTime_of_untlSnceFree` and
its three descendants continue to consume it unchanged. -/
theorem unorderedSuccessor_knownTimes_subset_of_untlSnceFree {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hfree : ∀ x ∈ b, untlSnceFree x.formula = true) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ t ∈ nb.knownTimes, t ∈ b.knownTimes := by
  have keyB : unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1
      = pickBranches b
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_branches_eq
  rw [keyB]
  exact pickBranches_knownTimes_subset_of_untlSnceFree hfree
    (pick_stage_source_noMint b ord fc tr hfree)

/-- **The rank is monotone in the two things a step can move.** `splitOrderedRank` rises with
`knownTimes` and falls with the constraint list, so a successor that adds no time and loses no
constraint cannot raise it. This is disjunct 1's second conjunct in general form; the first
conjunct is `Finset.card_le_card` on the same subset. -/
theorem splitOrderedRank_le_of_knownTimes_subset {Tmax : Nat} {b nb : Branch}
    {ord ord' : TimeOrdering}
    (hsub : ∀ t ∈ nb.knownTimes, t ∈ b.knownTimes)
    (hmono : ∀ q ∈ ord.constraints, q ∈ ord'.constraints) :
    splitOrderedRank Tmax nb ord' ≤ splitOrderedRank Tmax b ord := by
  have h1 : nb.knownTimes.toFinset ⊆ b.knownTimes.toFinset := by
    intro t ht
    simp only [List.mem_toFinset] at ht ⊢
    exact hsub t ht
  have h2 : incompPairs nb ord' ⊆ incompPairs b ord := by
    intro p hp
    rw [mem_incompPairs] at hp ⊢
    exact ⟨hsub _ hp.1, hsub _ hp.2.1, incomparableB_mono hmono p hp.2.2⟩
  simp only [splitOrderedRank]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (Finset.card_le_card h1))
    (Finset.card_le_card h2)

/-- **The discharge.** `MintPaysForTime` — the predicate as this file first stated it, not a repair
of it — holds at every universe of `untl`/`snce`-free formulas, at every frame class, for every
`Tmax`, and for every renaming `σ`.

Every step lands in **disjunct 1**, and neither the σ-hit obligation nor the self-guard measure is
consulted: `σ` does not appear in the proof at all. That is what makes this a discharge rather than
another repair — the hypothesis list of the predicate is untouched, and the direction lemmas of
section D2 carry it to `MintPaysForTimeStable` and `MintPaysForTimeFixed` for free. -/
theorem mintPaysForTime_of_untlSnceFree {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat}
    (hU : ∀ x ∈ U, untlSnceFree x.formula = true) :
    MintPaysForTime fc U Tmax := by
  intro _σ b ord tr hri hconf nb hnb
  have hfree : ∀ x ∈ b, untlSnceFree x.formula = true := fun x hx => hU x (hconf x hx)
  have hsub := unorderedSuccessor_knownTimes_subset (fc := fc) (tr := tr)
    hri.ordTimesKnown hfree nb hnb
  refine Or.inl ⟨Finset.card_le_card ?_, splitOrderedRank_le_of_knownTimes_subset hsub
    expandOnceUnblocked_ord_mono⟩
  intro t ht
  simp only [List.mem_toFinset] at ht ⊢
  exact hsub t ht

/-- …and at the repaired predicate the terminus chain is stated against, by the direction lemma. No
new hypothesis is introduced: `MintPaysForTimeFixed` is *weaker*. -/
theorem mintPaysForTimeFixed_of_untlSnceFree {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat}
    (hU : ∀ x ∈ U, untlSnceFree x.formula = true) :
    MintPaysForTimeFixed fc U Tmax :=
  mintPaysForTimeFixed_of_mintPaysForTime (mintPaysForTime_of_untlSnceFree hU)

/-- A member of `signedUniverse C L` carries a formula from `C`. The projection the concrete
instantiation below needs; the converse `mem_signedUniverse` is in `Fuel.lean`. -/
theorem formula_mem_of_mem_signedUniverse {C : Finset Formula} {L : Finset Label}
    {x : SignedFormula} (h : x ∈ signedUniverse C L) : x.formula ∈ C := by
  simp only [signedUniverse, Finset.mem_image, Finset.mem_product] at h
  obtain ⟨p, ⟨-, hf, -⟩, rfl⟩ := h
  exact hf

/-- **The discharge at the concrete universe the seed-level termini consume**, for every stock of
`untl`/`snce`-free formulas and every label set. This is the statement
`mintPaysForTimeFixed_signedUniverse_empty` was the `L = ∅` shadow of: the universe here is
nonempty as soon as `C` and `L` are (`signedUniverse_nonempty`). -/
theorem mintPaysForTimeFixed_signedUniverse_untlSnceFree
    (fc : FormalSystem.ProofSystem.FrameClass) {C : Finset Formula} (L : Finset Label)
    (Tmax : Nat) (hC : ∀ φ ∈ C, untlSnceFree φ = true) :
    MintPaysForTimeFixed fc (signedUniverse C L) Tmax :=
  mintPaysForTimeFixed_of_untlSnceFree
    (fun _ hx => hC _ (formula_mem_of_mem_signedUniverse hx))

/-- …and at the original predicate too, since the discharge is at the original. -/
theorem mintPaysForTime_signedUniverse_untlSnceFree
    (fc : FormalSystem.ProofSystem.FrameClass) {C : Finset Formula} (L : Finset Label)
    (Tmax : Nat) (hC : ∀ φ ∈ C, untlSnceFree φ = true) :
    MintPaysForTime fc (signedUniverse C L) Tmax :=
  mintPaysForTime_of_untlSnceFree (fun _ hx => hC _ (formula_mem_of_mem_signedUniverse hx))

/-! ### Non-vacuity

The discharge is at a universe, not at the empty set, and this is where that is checked rather than
asserted. Two facts: the universe is nonempty whenever both its dimensions are, and a concrete
modal stock — an atom, its box, and the `T` axiom's instance over it — satisfies the syntactic
condition. -/

/-- `signedUniverse` is nonempty as soon as both its dimensions are. -/
theorem signedUniverse_nonempty {C : Finset Formula} {L : Finset Label}
    (hC : C.Nonempty) (hL : L.Nonempty) : (signedUniverse C L).Nonempty := by
  obtain ⟨φ, hφ⟩ := hC
  obtain ⟨l, hl⟩ := hL
  exact ⟨⟨Sign.pos, φ, l⟩, mem_signedUniverse hφ hl⟩

/-- A concrete `untl`/`snce`-free stock: `p`, `□p`, and `□p → p`. -/
def modalWitnessStock : Finset Formula :=
  {Formula.atomS "p", (Formula.atomS "p").box,
    ((Formula.atomS "p").box).imp (Formula.atomS "p")}

/-- It satisfies the syntactic condition… -/
theorem modalWitnessStock_untlSnceFree :
    ∀ φ ∈ modalWitnessStock, untlSnceFree φ = true := by
  intro φ hφ
  simp only [modalWitnessStock, Finset.mem_insert, Finset.mem_singleton] at hφ
  rcases hφ with rfl | rfl | rfl <;> rfl

/-- …and it is not empty. -/
theorem modalWitnessStock_nonempty : modalWitnessStock.Nonempty :=
  ⟨Formula.atomS "p", by simp [modalWitnessStock]⟩

/-- **The residual, discharged at a nonempty concrete universe.** Together with
`signedUniverse_nonempty` and `modalWitnessStock_nonempty` this is the residual discharged at a
universe that is not the empty one. -/
theorem mintPaysForTime_modalWitness (fc : FormalSystem.ProofSystem.FrameClass)
    (L : Finset Label) (Tmax : Nat) :
    MintPaysForTime fc (signedUniverse modalWitnessStock L) Tmax :=
  mintPaysForTime_signedUniverse_untlSnceFree fc L Tmax modalWitnessStock_untlSnceFree

/-- **Seed-level terminus 2, with the mint residual discharged rather than assumed.**

The exact statement of `buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_fixed` with its
`hmint` argument gone: on an `untl`/`snce`-free stock the hypothesis is a theorem, so the terminus
carries one named residual fewer. The other three (`UnorderedSuccessorLabelClosed`,
`StepLengthBounded`, `PostBlockingSettles`) are untouched — this section says nothing about them.

**But read the reach honestly: `hlab` makes this statement vacuous wherever the universe is not
empty.** The section heading promises a discharge "at a **nonempty** universe", and the `hmint`
half of that promise is kept. The `hlab` half is not, and cannot be:
`unorderedSuccessorLabelClosed_nonempty_false` refutes `hlab` at every nonempty finite `L`, so at
exactly the `L` this section is interested in, the theorem above is a true conditional with a false
antecedent. It is the failure mode `DifficultyBounded` fell into and that `timeMergeClosed_product`
was added to rule out — a residual nobody can satisfy makes its theorem a true conditional with no
reach. What removes `hlab` is not a better proof of this theorem but a **replacement** for the
predicate — a condition that is actually satisfiable at a nonempty `L`. No artifact should read this
theorem, or any of the eight siblings that carry `hlab`, as claiming a discharge at a nonempty
universe until `hlab` is absent from the signature. -/
theorem buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree
    {fc : FormalSystem.ProofSystem.FrameClass}
    {C : Finset Formula} {L : Finset Label} {L' β : Nat} (phi : Formula) (hβ : 3 ≤ β)
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hlab : UnorderedSuccessorLabelClosed fc L)
    (hSL : StepLengthBounded fc (signedUniverse C L) L')
    (hfree : ∀ φ ∈ C, untlSnceFree φ = true)
    (hpb : PostBlockingSettles fc)
    (hseed : ∀ x ∈ seedBranch phi, x ∈ signedUniverse C L) :
    (buildTableauAt phi
        (mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
        fc
        (β * mintAwareFuelAt (signedUniverse C L).card
          (derivedTmaxAt ((seedBranch phi).knownTimes.toFinset.card)
            (signedUniverse C L).card)
          (10 * (signedUniverse C L).card)
          (difficultyCeiling (signedUniverse C L) L') β)
      ).isSome = true :=
  buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_fixed phi hβ hC hT hL hlab hSL
    (mintPaysForTimeFixed_signedUniverse_untlSnceFree fc L _ hfree) hpb hseed

/-! ## D4. The label residual, **replaced**: the `boxFree` shape gate and the world coordinate

**What this section delivers.** A route to clause 1 at `signedUniverse C L`, and to a seed-level
terminus, that carries **no** `UnorderedSuccessorLabelClosed` hypothesis at all. Section C11 proves
that residual false at every nonempty finite `L` (`unorderedSuccessorLabelClosed_nonempty_false`),
so the nine theorems that assume it are vacuously true at exactly the universes anyone cares about.
A *discharge* of it is therefore not available and never was — it is not a hard lemma, it is a false
statement. What is available is a **replacement**: a different hypothesis, satisfiable at a nonempty
`L` and discharged rather than assumed, bought at the price of a syntactic restriction on the stock.

**Why the replacement has to bite on the stock and not on `L`.** `freshWorldHeadroom_not_universal`
proves that for no nonempty finite `L` does every `L`-confined branch have the headroom: each
enlargement of `L` raises the reachable `maxWorld` at least as much as it adds, so the gap re-opens.
Every `L`-side repair is refuted before it is written. The one remaining place to intervene is
**before the world-minting rules can fire at all**, and that means a condition on the formulas a
branch may carry.

**Why exactly two rules have to be stopped.** `applyRule_emitted_world_mem` bounds the worlds a rule
emits at by `b.worldFinset` under exactly two hypotheses, `rule ≠ .boxNeg` and `rule ≠ .diamondPos`.
Those two inequalities *are* the world-minting census — there is no third rule, and if there were,
`findApplicableRule_not_worldMinting`'s conclusion below would be incomplete rather than merely
weak. `boxFree` closes both at the **shape gate**: `.boxNeg` is gated by `isApplicable`'s
`| .boxNeg, .neg, .box _ => true` arm, and `.diamondPos` by `asDiamond? φ`, whose only matching
pattern is itself built from a `.box` node. A branch carrying no `.box` anywhere can have neither
picked, at any frame class and any tracker.

**No frame-class restriction, for the same structural reason as D3.** The exclusion happens at the
shape gate, before `isApplicable` consults any `fc`-dependent gate, so nothing in this section
quantifies `fc` away or restricts it.

**What this is not — read this before citing anything below.** The terminus this section builds
combines `boxFree` with D3's `untlSnceFree`, and the two together collapse the stock to the **purely
propositional fragment**: atoms, `⊥`, `→`, and nothing else. That is a severe narrowing, and it is
**forced rather than a proof weakness**. `freshWorldHeadroom_not_universal` rules out every `L`-side
alternative, so the only handle is the stock; and stopping `.boxNeg` and `.diamondPos` at the stock
means excluding `□` outright, since both are gated on a `.box` node. No artifact may read this
section as a discharge over the modal fragment, as a general discharge, or as superseding D3's
reach: D3's `MintPaysForTime` result covers the whole modal fragment **including** `□`, and this
section does not. What this section adds is orthogonal to D3 — it removes a *false* hypothesis from
a terminus, at the one fragment where removing it is possible. -/

/-- **The syntactic condition**: no `.box` node anywhere in the formula.

Stated on the raw constructors rather than on the `asDiamond?` view, for the same reason
`untlSnceFree` is: it is then manifestly closed under subformulas and manifestly checkable on a
concrete stock by `rfl`. Like `untlSnceFree` it is *sufficient* rather than necessary — `asDiamond?`
also rejects `.box`-bearing shapes this predicate excludes outright — and sufficiency is all the
replacement needs. -/
def boxFree : Formula → Bool
  | .atom _ => true
  | .bot => true
  | .imp a b => boxFree a && boxFree b
  | .box _ => false
  | .untl a b => boxFree a && boxFree b
  | .snce a b => boxFree a && boxFree b

/-- **The `◇` view is empty on a `boxFree` formula.** `asDiamond? φ` matches only the shape whose
body is a `.box` node, so a formula with no `.box` anywhere cannot present as a diamond. This is the
half of the census that is *not* visible from `isApplicable`'s own pattern match, which is why it is
stated separately. -/
theorem asDiamond_eq_none_of_boxFree {φ : Formula} (h : boxFree φ = true) :
    asDiamond? φ = none := by
  cases φ <;> simp_all [asDiamond?, boxFree]
  rename_i a b
  cases a <;> simp_all [boxFree]

/-- **`.boxNeg` is inapplicable to a `boxFree` trigger**, at every frame class. Straight off
`isApplicable`'s `| .boxNeg, .neg, .box _ => true` arm: the arm requires a `.box` constructor, and
`boxFree` excludes it. -/
theorem isApplicable_boxNeg_false_of_boxFree {sf : SignedFormula}
    {fc : FormalSystem.ProofSystem.FrameClass} (h : boxFree sf.formula = true) :
    isApplicable .boxNeg sf fc = false := by
  cases sf with
  | mk sign formula label =>
    cases sign <;> cases formula <;> simp_all [isApplicable, boxFree]

/-- **`.diamondPos` is inapplicable to a `boxFree` trigger**, at every frame class. Through
`asDiamond_eq_none_of_boxFree`: the arm consults the view, and the view is `none`. -/
theorem isApplicable_diamondPos_false_of_boxFree {sf : SignedFormula}
    {fc : FormalSystem.ProofSystem.FrameClass} (h : boxFree sf.formula = true) :
    isApplicable .diamondPos sf fc = false := by
  cases sf with
  | mk sign formula label =>
    cases sign <;>
      simp_all [isApplicable, asDiamond_eq_none_of_boxFree h]

/-- **The first stage cannot pick a world-minting rule on a `boxFree` trigger.** The world-coordinate
counterpart of `findApplicableRule_not_mintsFreshTime`, and the fact `pick_stage_source_noWorldMint`
threads to the successor.

The conclusion is stated as the pair of inequalities `applyRule_emitted_world_mem` asks for, rather
than as a `ruleMintsFreshLabel` fact, because that lemma's hypotheses are the authoritative census:
`.boxNeg` and `.diamondPos` are the only two rules that can emit outside `b.worldFinset`, and both
are gated on a `.box` node — the first by `isApplicable`'s own pattern, the second through
`asDiamond?`. This is the structural reason the whole route carries no frame-class restriction: the
shape gate is consulted before any `fc`-dependent gate. -/
theorem findApplicableRule_not_worldMinting {sf : SignedFormula} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    {r : TableauRule} {res : RuleResult} {o : TimeOrdering}
    (hfree : boxFree sf.formula = true)
    (h : findApplicableRule sf b ord fc = some (r, res, o)) :
    r ≠ .boxNeg ∧ r ≠ .diamondPos := by
  have happ := findApplicableRule_isApplicable h
  constructor
  · rintro rfl
    simp [isApplicable_boxNeg_false_of_boxFree (fc := fc) hfree] at happ
  · rintro rfl
    simp [isApplicable_diamondPos_false_of_boxFree (fc := fc) hfree] at happ


/-! ### The world-subset machinery, mirroring D3's time machinery

Three declarations, in the same order and the same shapes as `pick_stage_source_noMint`,
`pickBranches_knownTimes_subset` and `unorderedSuccessor_knownTimes_subset`. The mirror is
**strictly simpler than its template** in one respect worth naming rather than leaving a reader to
wonder about: `applyRule_emitted_world_mem` carries no `OrdTimesKnown b ord` hypothesis where
`applyRule_emitted_time_mem` does, so none of the three below takes one either. The asymmetry is
real and is recorded at `applyRule_emitted_time_mem_ordTimesKnown_needed`: the time sweep needs the
ordering's times to be branch-known because `timeLinearity` reads times off `ord`, whereas nothing
reads *worlds* off the ordering at all.

**Footnote, added later.** The asymmetry is real but it is not permanent on this fragment:
`unorderedSuccessor_knownTimes_subset_of_untlSnceFree` (section D3) is the time-coordinate mirror
without the run invariant, and the boundary block at the end of this section records what that
buys. -/

/-- **`pick_stage_source` with the no-world-mint fact attached**, the world-coordinate counterpart
of `pick_stage_source_noMint`. The three stages differ only in how the fact arrives: stage one has
it from `findApplicableRule_not_worldMinting`; stages two and three run exactly one rule each
(`serialityRule` via `findApplicableSerialRule_rule`, `timeLinearity` via
`findApplicableLinearityRule_rule`), and neither is `.boxNeg` or `.diamondPos`, so both close on the
rule identity alone. -/
private theorem pick_stage_source_noWorldMint (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) (tr : EventualityTracker)
    (hfree : ∀ x ∈ b, boxFree x.formula = true) :
    ∀ r res o,
      (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
       | some sf => findApplicableRule sf b ord fc
       | none =>
         match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
             && (findApplicableSerialRule sf b ord).isSome) with
         | some sf => findApplicableSerialRule sf b ord
         | none =>
           match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
               && (findApplicableLinearityRule sf b ord).isSome) with
           | some sf => findApplicableLinearityRule sf b ord
           | none => none) = some (r, res, o) →
      ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧ r ≠ .boxNeg ∧ r ≠ .diamondPos := by
  intro r res o h
  rcases hpick : findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with _ | sf
  · rw [hpick] at h
    rcases hser : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                             && (findApplicableSerialRule sf b ord).isSome) with _ | sf2
    · rw [hser] at h
      rcases hlin : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                               && (findApplicableLinearityRule sf b ord).isSome) with _ | sf3
      · rw [hlin] at h
        simp only at h
        exact absurd h (by simp)
      · rw [hlin] at h
        simp only at h
        refine ⟨sf3, List.mem_of_find?_eq_some hlin,
          findApplicableLinearityRule_applyRule_pair h, ?_⟩
        rw [findApplicableLinearityRule_rule h]
        exact ⟨by simp, by simp⟩
    · rw [hser] at h
      simp only at h
      refine ⟨sf2, List.mem_of_find?_eq_some hser,
        findApplicableSerialRule_applyRule_pair h, ?_⟩
      rw [findApplicableSerialRule_rule h]
      exact ⟨by simp, by simp⟩
  · rw [hpick] at h
    simp only at h
    have hmem : sf ∈ b := by
      unfold findUnexpandedUnblockedWith at hpick
      exact List.mem_of_find?_eq_some hpick
    exact ⟨sf, hmem, findApplicableRule_applyRule_pair h,
      findApplicableRule_not_worldMinting (hfree sf hmem) h⟩

/-- One pick stage adds no world, given that its rule is neither of the two that can. The join of
`applyRule_emitted_world_mem` with the no-world-mint source, in the shape
`pickBranches_knownTimes_subset` uses for the time coordinate — and with no `OrdTimesKnown`
argument, which is exactly the hypothesis its time twin needs and this one does not. -/
private theorem pickBranches_worldFinset_subset {b : Branch} {ord : TimeOrdering}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧
      r ≠ .boxNeg ∧ r ≠ .diamondPos) :
    ∀ nb ∈ pickBranches b p, ∀ w ∈ nb.worldFinset, w ∈ b.worldFinset := by
  rcases p with _ | ⟨r, res, o⟩
  · simp [pickBranches]
  · obtain ⟨sf, hsf, hA, h1, h2⟩ := hp r res o rfl
    intro nb hnb w hw
    obtain ⟨-, hsub⟩ := resultBranch_sub (b := b) (nb := nb) (res := res) hnb
    obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_worldFinset hw
    rcases hsub x hx with hxe | hxb
    · refine applyRule_emitted_world_mem (rule := r) (sf := sf) (ord := ord) hsf h1 h2 x ?_
      rw [hA]
      exact hxe
    · exact Branch.mem_worldFinset hxb

/-- **No unordered successor of a `boxFree` branch carries a new world.**

The engine-level statement, and the world-coordinate half of what the replacement consumes. Compare
`unorderedSuccessor_world_dichotomy`, which is unconditional and therefore has to admit
`w = b.nextWorld` as a second case: here the second case is *closed*, at the cost of the syntactic
hypothesis. That closure is precisely what no condition on `L` could ever buy —
`freshWorldHeadroom_not_universal` refutes every such attempt — and it is why the replacement route
has to restrict the stock.

Routed through `pick_branches_eq` and `pick_stage_source_noWorldMint`, so the three-stage pick is not
destructured a second time. Carries no frame-class restriction and no `OrdTimesKnown`. -/
theorem unorderedSuccessor_worldFinset_subset {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hfree : ∀ x ∈ b, boxFree x.formula = true) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ w ∈ nb.worldFinset, w ∈ b.worldFinset := by
  have keyB : unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1
      = pickBranches b
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_branches_eq
  rw [keyB]
  exact pickBranches_worldFinset_subset (pick_stage_source_noWorldMint b ord fc tr hfree)


/-! ### The composite: clause 1's label dimension at the propositional fragment

The two per-coordinate subset facts, joined by the rectangle. This is the same assembly as
`unorderedSuccessor_label_mem_of_headroom`, with one decisive difference: there the four quadrants
are paid for by `FreshLabelHeadroom L b`, which `freshLabelHeadroom_not_universal` refutes at every
nonempty finite `L`; here they are paid for by `TimeMergeClosed L`, which `timeMergeClosed_product`
exhibits at every rectangle. The hypothesis is satisfiable, and that is the entire point of the
exercise. -/

/-- **Clause 1's label dimension, discharged from satisfiable hypotheses.** Every formula on every
unordered successor of an `L`-confined `boxFree`, `untl`/`snce`-free branch sits at a label of `L`.

**How the four quadrants are paid for.** A label is a *pair*, and the two coordinate facts arrive
separately: `unorderedSuccessor_worldFinset_subset` puts the successor's world among `b`'s worlds,
`unorderedSuccessor_knownTimes_subset` puts its time among `b`'s times. Confinement of `b` then
supplies a formula `y ∈ b` carrying that world and a formula `z ∈ b` carrying that time, each at a
label in `L` — but `y` and `z` are in general *different* formulas, so `⟨y.label.world, z.label.time⟩`
is a quadrant confinement alone does not reach. That cross-product gap is exactly the one register
entry 21 warns about, and `TimeMergeClosed L` is exactly what closes it:
`timeMergeClosed_iff_product` characterizes a time-merge-closed label set as precisely a full
rectangle of worlds against times, which is the cross-product closure a pair-valued label needs. No
further hypothesis is required, and a reader who expects to have to re-derive the worry can stop
here.

`TimeMergeClosed L` is not new currency either: it is already a sibling hypothesis at every terminus
in the chain, where it discharges `UniverseClosedAt`'s clause 2.

`OrdTimesKnown b ord` is inherited from `unorderedSuccessor_knownTimes_subset` and through it from
`applyRule_emitted_time_mem`, where `applyRule_emitted_time_mem_ordTimesKnown_needed` shows it is not
removable. It is the one hypothesis here that the world coordinate does not need — see the section
note on the asymmetry — and it is the reason this composite cannot be stated at
`UniverseClosedAt`'s clause 1, which carries no such hypothesis. -/
theorem unorderedSuccessor_label_mem_of_propositional {L : Finset Label} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (haux : OrdTimesKnown b ord) (hL : TimeMergeClosed L)
    (hbox : ∀ x ∈ b, boxFree x.formula = true)
    (hfree : ∀ x ∈ b, untlSnceFree x.formula = true)
    (hbl : ∀ x ∈ b, x.label ∈ L) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ x ∈ nb, x.label ∈ L := by
  intro nb hnb x hx
  have hw : x.label.world ∈ b.worldFinset :=
    unorderedSuccessor_worldFinset_subset hbox nb hnb x.label.world (Branch.mem_worldFinset hx)
  have ht : x.label.time ∈ b.knownTimes :=
    unorderedSuccessor_knownTimes_subset haux hfree nb hnb x.label.time (mem_knownTimes_of_mem hx)
  obtain ⟨y, hy, hyw⟩ := exists_mem_of_mem_worldFinset hw
  obtain ⟨z, hz, hzt⟩ := exists_mem_of_mem_knownTimes ht
  have hkey := hL y.label (hbl y hy) z.label (hbl z hz)
  rw [hyw, hzt] at hkey
  exact hkey

/-- **The same composite without `OrdTimesKnown`.** Identical to
`unorderedSuccessor_label_mem_of_propositional` except that the time coordinate is routed through
`unorderedSuccessor_knownTimes_subset_of_untlSnceFree`, so the run invariant is not required.

`hfree` was already present for the time coordinate; it now pays for that coordinate outright.
Nothing else changes: the world coordinate is `unorderedSuccessor_worldFinset_subset` as before, and
the four quadrants are still closed by `TimeMergeClosed L`.

The `haux`-carrying original is retained beside it and is unmodified. -/
theorem unorderedSuccessor_label_mem_of_propositional_ordFree {L : Finset Label} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker}
    (hL : TimeMergeClosed L)
    (hbox : ∀ x ∈ b, boxFree x.formula = true)
    (hfree : ∀ x ∈ b, untlSnceFree x.formula = true)
    (hbl : ∀ x ∈ b, x.label ∈ L) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      ∀ x ∈ nb, x.label ∈ L := by
  intro nb hnb x hx
  have hw : x.label.world ∈ b.worldFinset :=
    unorderedSuccessor_worldFinset_subset hbox nb hnb x.label.world (Branch.mem_worldFinset hx)
  have ht : x.label.time ∈ b.knownTimes :=
    unorderedSuccessor_knownTimes_subset_of_untlSnceFree hfree nb hnb x.label.time
      (mem_knownTimes_of_mem hx)
  obtain ⟨y, hy, hyw⟩ := exists_mem_of_mem_worldFinset hw
  obtain ⟨z, hz, hzt⟩ := exists_mem_of_mem_knownTimes ht
  have hkey := hL y.label (hbl y hy) z.label (hbl z hz)
  rw [hyw, hzt] at hkey
  exact hkey


/-- **Clause 1 at `signedUniverse C L`, both dimensions, from satisfiable hypotheses.**

The mirror of `unorderedSuccessor_confined_signedUniverse_of_headroom` with its
`UnorderedSuccessorLabelClosed fc L` argument **gone**: the formula coordinate is discharged as
before by `unorderedSuccessor_formula_mem` from `hC`/`hT`, and the label coordinate by
`unorderedSuccessor_label_mem_of_propositional` from the two syntactic conditions and
`TimeMergeClosed L`. Nothing here is assumed that cannot be exhibited — contrast the `_of_headroom`
original, whose `hlab` is false at every nonempty `L`, and the C11 sibling
`unorderedSuccessor_confined_signedUniverse_of_freshLabelHeadroom`, whose `FreshLabelHeadroom L b` is
refutable as a universally quantified condition.

The `_of_headroom` original is retained byte-identical and is what the landed terminus chain
consumes; this is an additional declaration stated beside it, exactly as
`UnorderedSuccessorLabelClosedOrd` is stated beside `UnorderedSuccessorLabelClosed`.

**Note the `OrdTimesKnown b ord` in the quantifier prefix**, which the `_of_headroom` original does
not have and which the C11 `FreshLabelHeadroom` sibling does. It is not decoration, and it is why
this theorem stops here rather than continuing into a restated terminus — see the boundary note
below. -/
theorem unorderedSuccessor_confined_signedUniverse_of_propositional {C : Finset Formula}
    {L : Finset Label} {fc : FormalSystem.ProofSystem.FrameClass}
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hbox : ∀ φ ∈ C, boxFree φ = true) (hfree : ∀ φ ∈ C, untlSnceFree φ = true) :
    ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker),
      OrdTimesKnown b ord →
      (∀ x ∈ b, x ∈ signedUniverse C L) →
      ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1, ∀ x ∈ nb,
        x ∈ signedUniverse C L := by
  intro b ord tr haux hb nb hnb x hx
  have hbf : ∀ y ∈ b, y.formula ∈ C :=
    fun y hy => (formula_label_of_mem_signedUniverse (hb y hy)).1
  have hbl : ∀ y ∈ b, y.label ∈ L :=
    fun y hy => (formula_label_of_mem_signedUniverse (hb y hy)).2
  exact mem_signedUniverse
    (unorderedSuccessor_formula_mem hC hT hbf nb hnb x hx)
    (unorderedSuccessor_label_mem_of_propositional haux hL
      (fun y hy => hbox _ (hbf y hy)) (fun y hy => hfree _ (hbf y hy)) hbl nb hnb x hx)

/-- **Clause 1 at `signedUniverse C L`, in `UniverseClosedAt`'s own shape.**

`unorderedSuccessor_confined_signedUniverse_of_propositional` with the `OrdTimesKnown b ord →`
arrow deleted from the quantifier prefix and nothing else changed. That arrow was the one thing
standing between the propositional route and `UniverseClosedAt`'s clause 1, which quantifies `ord`
universally and unconstrained; `unorderedSuccessor_knownTimes_subset_of_untlSnceFree` removes it,
and the statement below is now literally clause 1 at `U = signedUniverse C L`.

The `haux`-carrying original is retained beside it and is unmodified. -/
theorem unorderedSuccessor_confined_signedUniverse_of_propositional_ordFree {C : Finset Formula}
    {L : Finset Label} {fc : FormalSystem.ProofSystem.FrameClass}
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hbox : ∀ φ ∈ C, boxFree φ = true) (hfree : ∀ φ ∈ C, untlSnceFree φ = true) :
    ∀ (b : Branch) (ord : TimeOrdering) (tr : EventualityTracker),
      (∀ x ∈ b, x ∈ signedUniverse C L) →
      ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1, ∀ x ∈ nb,
        x ∈ signedUniverse C L := by
  intro b ord tr hb nb hnb x hx
  have hbf : ∀ y ∈ b, y.formula ∈ C :=
    fun y hy => (formula_label_of_mem_signedUniverse (hb y hy)).1
  have hbl : ∀ y ∈ b, y.label ∈ L :=
    fun y hy => (formula_label_of_mem_signedUniverse (hb y hy)).2
  exact mem_signedUniverse
    (unorderedSuccessor_formula_mem hC hT hbf nb hnb x hx)
    (unorderedSuccessor_label_mem_of_propositional_ordFree hL
      (fun y hy => hbox _ (hbf y hy)) (fun y hy => hfree _ (hbf y hy)) hbl nb hnb x hx)

/-- **`UniverseClosedAt fc (signedUniverse C L)` with no residual and no frame-class restriction.**

The theorem section D4's boundary block recorded as *not stateable*. Its hypotheses are two stock
conditions (`TableauClosed C`, `TrichStock C`), the label-set closure condition (`TimeMergeClosed L`,
satisfied by every rectangle — `timeMergeClosed_product`), and the two syntactic shape conditions on
the stock. There is **no** `UnorderedSuccessorLabelClosed`, **no** `OrdTimesKnown`, and **no**
frame-class hypothesis.

Assembled exactly as `universeClosedAt_signedUniverse_of_headroom` is: a two-component anonymous
constructor whose clause 2 is `timeMergeClosed_identifyTime_signedUniverse hL`, unchanged and taking
no argument the `_of_headroom` original does not also give it. Only clause 1 differs, and it is the
`ordFree` composite above.

**It is nevertheless vacuous, for a reason that has nothing to do with `hlab`.** `hC` and `hfree`
are jointly unsatisfiable: `TableauClosed.serialFuture` requires `Formula.top.someFuture ∈ C`, and
`Formula.someFuture ⊤` is `⊤ untl ⊤`, which `untlSnceFree` rejects.
`tableauClosed_untlSnceFree_false` below decides this, and it is stated immediately after this
theorem rather than in a note so that no reader takes the removal of `hlab` for a discharge. The
same collision hits `unorderedSuccessor_confined_signedUniverse_of_propositional` and its `ordFree`
sibling above, and section D3's
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree`, all of which carry both
hypotheses.

What is *not* hit is anything that takes only the syntactic condition:
`applyRule_emitted_time_mem_of_untlSnceFree`,
`unorderedSuccessor_knownTimes_subset_of_untlSnceFree`,
`unorderedSuccessor_label_mem_of_propositional_ordFree`, and section D3's
`mintPaysForTime_of_untlSnceFree` chain take no `TableauClosed` and are non-vacuous. The collision
is between stock *closure* and stock *shape*, and it is located at exactly one field.

What this does **not** do is restate the terminus. The `_at` / `_selfGuarded` / `_fixed` families and
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_*` are untouched, and removing their
`hlab` is separate, downstream work. See the boundary block below. -/
theorem universeClosedAt_signedUniverse_of_propositional {C : Finset Formula} {L : Finset Label}
    {fc : FormalSystem.ProofSystem.FrameClass}
    (hC : TableauClosed C) (hT : TrichStock C) (hL : TimeMergeClosed L)
    (hbox : ∀ φ ∈ C, boxFree φ = true) (hfree : ∀ φ ∈ C, untlSnceFree φ = true) :
    UniverseClosedAt fc (signedUniverse C L) :=
  ⟨unorderedSuccessor_confined_signedUniverse_of_propositional_ordFree hC hT hL hbox hfree,
    fun _ _ _ hbU ht₁ => timeMergeClosed_identifyTime_signedUniverse hL hbU ht₁⟩

/-- **`TableauClosed C` and `∀ φ ∈ C, untlSnceFree φ = true` cannot both hold.** Decided, not
argued, and in one field: `TableauClosed.serialFuture` demands `Formula.top.someFuture ∈ C` —
`serialityRule` emits `T(F⊤)` at every label from no trigger at all, so any stock closed under the
engine's outputs contains it — and `Formula.someFuture ⊤` unfolds to `Formula.untl ⊤ ⊤`, which
`untlSnceFree` rejects by its `untl` arm.

**What this decides, and what it does not.** Every theorem in this file carrying *both* hypotheses is
therefore vacuously true, whatever else its signature says. That is four declarations:
`unorderedSuccessor_confined_signedUniverse_of_propositional` and its `ordFree` sibling,
`universeClosedAt_signedUniverse_of_propositional`, and section D3's
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree` — the last of which register
entry 21 already records as vacuous through `hlab`, and which is now vacuous twice over and for
independent reasons.

Nothing carrying only the syntactic condition is affected, and that is most of the machinery:
section D3's `applyRule_emitted_time_mem_of_untlSnceFree`,
`unorderedSuccessor_knownTimes_subset_of_untlSnceFree`, `mintPaysForTime_of_untlSnceFree` and its
descendants, and this section's `unorderedSuccessor_label_mem_of_propositional_ordFree` all stand
non-vacuously. Removing `OrdTimesKnown` from the time coordinate was real work with a real result;
what it turns out not to buy is a non-vacuous composite at `signedUniverse C L`.

**Where the obstruction actually sits, for whoever picks this up.** Not in the shape condition and
not in the time coordinate, but in `TableauClosed`'s `serialFuture` / `serialPast` fields, which are
forced by `serialityRule` firing unconditionally at every label. A non-vacuous propositional
composite therefore needs either a weakened stock-closure predicate that does not demand the
seriality outputs — and then a re-derivation of `unorderedSuccessor_formula_mem` at it — or a
syntactic condition weaker than `untlSnceFree` that admits `⊤ untl ⊤` while still excluding the four
propagation arms and `.orderTrichotomy`. Neither is attempted here, and neither is refuted. -/
theorem tableauClosed_untlSnceFree_false {C : Finset Formula}
    (hC : TableauClosed C) (hfree : ∀ φ ∈ C, untlSnceFree φ = true) : False := by
  have h := hfree _ hC.serialFuture
  simp [Formula.someFuture, untlSnceFree] at h

/-! ### The boundary: what Route 1 turned out to be, and where this section now stops

**An earlier version of this block recorded a shape mismatch as settled and Route 1 as
unattempted. Both halves are now false, and the block is rewritten rather than patched so that no
reader inherits the superseded verdict.** What it said was this: `UniverseClosedAt fc U`'s clause 1
is

  `∀ b ord tr, (∀ x ∈ b, x ∈ U) → ∀ nb ∈ unorderedSuccessorBranches …, ∀ x ∈ nb, x ∈ U`

with `ord` **universally quantified and unconstrained**, while every theorem closing the time
coordinate carried `OrdTimesKnown b ord`, inherited through `unorderedSuccessor_knownTimes_subset`
from `applyRule_emitted_time_mem` — where `applyRule_emitted_time_mem_ordTimesKnown_needed` proves
the hypothesis is not removable. Two routes past it were named: re-derive the time sweep on this
fragment's reachable rules (Route 1), or thread `OrdTimesKnown` through the whole closure interface
(Route 2).

**Route 1 was attempted and it works.** `applyRule_emitted_time_mem_of_untlSnceFree` (section D3)
is the time sweep with `OrdTimesKnown b ord` replaced by `∀ x ∈ b, untlSnceFree x.formula = true`.
The replacement is exact, not approximate: `haux` is consumed at exactly five rule arms, and all
five are shape-gated by that condition —

* `.allFuturePos` and `.allPastPos`, whose `applyRule` arms match the raw `Formula.allFuture` /
  `Formula.allPast` shapes, each headed by an `untl` / `snce` node;
* `.someFutureNeg` and `.somePastNeg`, gated by `asSomeFuture?` / `asSomePast?`, which section D3's
  view lemmas already send to `none`;
* `.orderTrichotomy`, whose `fires` guard demands the branch carry
  `SignedFormula.neg d l0` for one of three `Formula.someFuture`-headed disjuncts.

The first four are excluded by the *trigger's* shape; the fifth is excluded by what the *branch*
carries, which is why the restricted sweep takes a branch-level hypothesis. That asymmetry is also
what makes the route work at all: clause 1 hands over `∀ x ∈ b, x ∈ signedUniverse C L`, from which
branch-level freeness follows in one line, and hands over nothing whatever about `ord`.

**One correction to the superseded block's own reasoning, recorded because it was load-bearing.**
That block conjectured Route 1 would need the pick to be constrained — the linearity stage yielding
`.branchingOrdered`, the seriality stage emitting at the trigger's label, and so on. None of that is
needed. The five exclusions are local to `applyRule`'s arms, no rule set is restricted, and `boxFree`
plays no part in the time coordinate at all: it is what closes the **world** coordinate
(`unorderedSuccessor_worldFinset_subset`), and the restricted sweep carries one syntactic hypothesis
rather than two.

**What the section now delivers.** `universeClosedAt_signedUniverse_of_propositional`:
`UniverseClosedAt fc (signedUniverse C L)` from `TableauClosed C`, `TrichStock C`,
`TimeMergeClosed L`, and the two shape conditions — with no `UnorderedSuccessorLabelClosed`, no
`OrdTimesKnown`, and no frame-class restriction. It is the statement this block previously recorded
as not stateable, and it is now stated and proved.

**And it is vacuous — a second obstruction, found only once the first was removed.**
`tableauClosed_untlSnceFree_false` decides that `TableauClosed C` and
`∀ φ ∈ C, untlSnceFree φ = true` cannot both hold: `TableauClosed.serialFuture` demands
`Formula.top.someFuture ∈ C`, and `Formula.someFuture ⊤` is `⊤ untl ⊤`. So the composite above,
`unorderedSuccessor_confined_signedUniverse_of_propositional` and its `ordFree` sibling, and section
D3's `buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree` are all vacuously true
— the last one now for two independent reasons, `hlab` and this. This is stated plainly rather than
softened: removing `OrdTimesKnown` was necessary and is done, and it is not sufficient.

**What is not vacuous.** Everything that takes the shape condition without `TableauClosed`:
`applyRule_emitted_time_mem_of_untlSnceFree`,
`unorderedSuccessor_knownTimes_subset_of_untlSnceFree`,
`unorderedSuccessor_label_mem_of_propositional_ordFree`, and section D3's whole
`mintPaysForTime_of_untlSnceFree` chain. The time coordinate is genuinely closed on this fragment;
what is not available is a stock that is simultaneously closed under the engine's outputs and free
of `untl`.

**The boundary that remains, stated exactly.** No theorem in this section removes `hlab` from
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree` or from any of its eight
siblings, and doing so would in any case exchange one vacuity for another. The live question is no
longer `OrdTimesKnown`; it is whether a stock-closure predicate weaker than `TableauClosed` — one
that does not demand `serialityRule`'s two outputs — supports `unorderedSuccessor_formula_mem`, or
whether a shape condition weaker than `untlSnceFree` still excludes the five arms. Neither is
attempted here and neither is refuted.

**Route 2 remains unattempted and is now unnecessary for this purpose.** An `Ord`-flavoured
`UniverseClosedAt`, and the same for `DifficultyBounded`, cascading through roughly twenty
restatements down to `buildTableauAt`, was the fallback if Route 1 failed. It did not fail. Route 2
is neither started nor recommended. -/

/-! ## D5. The engine-level assembly: `MintPaysForTimeFixed` off `.Dense`, at any universe

**What this section delivers.** `MintPaysForTimeFixed fc U Tmax` — the repaired mint residual the
terminus chain is stated against — proved outright at an **arbitrary** universe, for every frame
class `fc` satisfying `¬ (FrameClass.Dense ≤ fc)`. No syntactic condition on the formulas, no
emptiness, no hypothesis added to the predicate, no figure changed, and no engine definition
touched. At the concrete universe the seed-level termini consume it reads
`mintPaysForTimeFixed_signedUniverse_of_not_dense`, which holds for **every** stock `C` — `untl`
and `snce` nodes included.

**The frame restriction is one condition, and it is written in the statement.** `¬ (FrameClass.Dense
≤ fc)` excludes `.Dense` and `.RTime` together, because `Dense ≤ Dedekind` holds in the
`FrameClass` order, and it admits exactly `.Base` and `.ZTime`. It is not hidden behind a
definition, a `variable`, or a typeclass: a reader of `mintPaysForTimeFixed_of_not_dense` alone sees
it. What it buys is the exclusion of `densityRule` — the one rule that mints a fresh time while
sitting outside both `freshLabelRules` and `selfGuardRules`, and therefore outside every disjunct —
via `findApplicableRule_ne_densityRule`. It does not close the density coordinate: `gapPotential` is
still implemented nowhere and assumed by nothing, and register entry 20's item (b) stands exactly as
written.

**What was missing, and what supplies it.** The per-rule payments all existed already. What did not
exist was the picked rule's *identity* at the successor: `pick_stage_source` hands on `applyRule`'s
pair and discards stage one's `findApplicableRule` equation, and the equation is precisely what the
witness-guarded payments need — `findApplicableRule_guard_linear` and its `.branching` twin read
`witnessPresent … = false` off `findApplicableRule`'s own `if`, which `applyRule` does not carry.
`pick_stage_source_rule` is that threading, in the only shape all three stages support: stage one
reports its equation, stages two and three report that their rule (`serialityRule`, `timeLinearity`)
is outside `freshTimeRules`. With it, `pickBranches_mintPays` splits the picked rule into the four
buckets a `decide`-proved census fixes — no fresh time (disjunct 1), witness-guarded mint (disjunct
2), self-guarded mint (disjunct 3), `densityRule` (excluded) — and every bucket closes from a landed
lemma with both budget conjuncts exact.

**What this retires, and what it generalizes.** Register entry 20's item (a), the engine-level
assembly, is the last non-density obstruction to the mint predicate itself, and it is retired here;
entry 20's paragraph is amended in place to say so. `mintPaysForTimeFixed_signedUniverse_of_not_dense`
generalizes section D3's `mintPaysForTimeFixed_signedUniverse_untlSnceFree` off its syntactic
fragment onto arbitrary `C` — the case entry 20 itself calls the hard one, and the case
`mintPaysForTime_untlNeg_false` refutes the *unrepaired* predicate at. Neither D3's discharge nor
`mintPaysForTimeFixed_signedUniverse_empty` is deleted or altered; both are superseded in prose
only, and D3's remains the statement to reach for at `.Dense` and `.RTime`, where this section is
silent. The discharge here is satisfiable rather than vacuous: `signedUniverse_nonempty` makes the
universe nonempty as soon as `C` and `L` are, and the hypothesis discharged is a *theorem* there.

**And now the part that must not be omitted: this makes NO terminus in this file non-vacuous.**
Landing it unlocks nothing downstream, and saying otherwise would reproduce exactly the failure mode
register entry 21 documents for
`buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse_untlSnceFree`. Both halves of that, named:

* *The nine `hlab` carriers stay vacuous.* Nine statements in this file carry
  `hlab : UnorderedSuccessorLabelClosed fc L` as a live hypothesis, and every one of them is a true
  conditional with a false antecedent at every nonempty `L`, because
  `unorderedSuccessorLabelClosed_nonempty_false` pins that predicate's satisfiability set at exactly
  `{∅}`. Removing `hmint` from such a statement changes nothing about its reach — and this section
  removes `hmint` from none of them in any case, because it restates no terminus at all.
* *The `hlab`-free `hmint`-carrying termini stay conditioned elsewhere.* Each of them still requires
  `UniverseClosedAt fc U`, plus `DifficultyBounded` or `StepLengthBounded`, plus `PostBlockingSettles`
  or `PostBlockingSettlesRun`. Three of those are refuted outright — `DifficultyBounded` by register
  entry 9, clause 1 of `UniverseClosed`/`UniverseClosedAt` at a fixed finite `signedUniverse C L` by
  entry 11, and `PostBlockingSettles` by entry 22. A discharged mint residual does not touch any of
  them.

So the honest reading of this section is: one named residual of the four is now a theorem at a
nonempty universe off `.Dense`, and the count of *satisfiable* residual conditions blocking any
terminus is unchanged. No artifact should read `mintPaysForTimeFixed_of_not_dense` as de-vacuifying
anything. -/

/-- **The strengthened pick-stage bridge.** `pick_stage_source` with the picked rule's *identity*
threaded through, in the only form the three stages can all support: stage one hands on its own
`findApplicableRule` equation, and stages two and three report that their rule is outside the time
census.

This is the whole of what the engine-level assembly was missing. `pick_stage_source` discards the
stage-one equation and keeps only `applyRule`'s pair, which is enough for the disjunct-1 arguments
(`pickBranches_ordTimes`, `pickBranches_time_dichotomy`) and not enough for disjunct 2: the
witness-guard the per-rule payment lemmas consume — `findApplicableRule_guard_linear` and its
`.branching` twin — lives in `findApplicableRule`'s own `if`, not in `applyRule`, and there is no
route to it from `applyRule r sf b ord = (res, o)` alone.

Its two precedents are `pick_stage_source_guarded`, which attaches the blocking-side fact by the
same three-stage `rcases`, and `pick_stage_source_noMint`, whose proof skeleton this is verbatim:
the only difference is that the two later stages report `Or.inr` of the no-mint fact where that
lemma reports it bare, and the first stage reports `Or.inl` of its own equation where that lemma
computes the no-mint fact from a syntactic hypothesis it does not have here. The disjunction is the
honest shape — stages two and three run `serialityRule` and `timeLinearity`, neither of which is
in `freshTimeRules`, and neither of which has a `findApplicableRule` equation to give. -/
private theorem pick_stage_source_rule (b : Branch) (ord : TimeOrdering)
    (fc : FormalSystem.ProofSystem.FrameClass) (tr : EventualityTracker) :
    ∀ r res o,
      (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
       | some sf => findApplicableRule sf b ord fc
       | none =>
         match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
             && (findApplicableSerialRule sf b ord).isSome) with
         | some sf => findApplicableSerialRule sf b ord
         | none =>
           match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
               && (findApplicableLinearityRule sf b ord).isSome) with
           | some sf => findApplicableLinearityRule sf b ord
           | none => none) = some (r, res, o) →
      ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧
        (findApplicableRule sf b ord fc = some (r, res, o)
          ∨ ruleMintsFreshTime r = false) := by
  intro r res o h
  rcases hpick : findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with _ | sf
  · rw [hpick] at h
    rcases hser : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                             && (findApplicableSerialRule sf b ord).isSome) with _ | sf2
    · rw [hser] at h
      rcases hlin : b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                               && (findApplicableLinearityRule sf b ord).isSome) with _ | sf3
      · rw [hlin] at h
        simp only at h
        exact absurd h (by simp)
      · rw [hlin] at h
        simp only at h
        refine ⟨sf3, List.mem_of_find?_eq_some hlin,
          findApplicableLinearityRule_applyRule_pair h, Or.inr ?_⟩
        rw [findApplicableLinearityRule_rule h]
        rfl
    · rw [hser] at h
      simp only at h
      refine ⟨sf2, List.mem_of_find?_eq_some hser,
        findApplicableSerialRule_applyRule_pair h, Or.inr ?_⟩
      rw [findApplicableSerialRule_rule h]
      rfl
  · rw [hpick] at h
    simp only at h
    have hmem : sf ∈ b := by
      unfold findUnexpandedUnblockedWith at hpick
      exact List.mem_of_find?_eq_some hpick
    exact ⟨sf, hmem, findApplicableRule_applyRule_pair h, Or.inl h⟩

/-- **The density exclusion, by frame class.** `densityRule`'s arm of `isApplicable` is
`| .densityRule, .pos, .allFuture _ => decide (FrameClass.Dense ≤ fc)`, so a first-stage pick of it
carries `Dense ≤ fc` as a decided fact; denying that fact excludes the rule outright. Reached
through `findApplicableRule_isApplicable`, which is what makes this ten lines rather than a walk
over `findApplicableRule`'s arm list.

**One hypothesis, not two.** `¬ (FrameClass.Dense ≤ fc)` excludes `.Dense` and `.RTime`
*together*: `Dense ≤ Dedekind` holds in the `FrameClass` order, so a `fc` above `.Dense` is
excluded whether it is `.Dense` itself or anything above it. What it admits is exactly `.Base` and
`.ZTime`. Stating it as a pair of disequalities would be both weaker in form and redundant, and
it is deliberately not hidden behind a definition: a reader of the discharge below sees the
restriction in the statement.

This is the whole of the density treatment in this section. `gapPotential` — register entry 19's
and entry 20's item (b) — is not introduced, not assumed, and not needed here; buying the
exclusion with a frame-class hypothesis is what makes that so. -/
theorem findApplicableRule_ne_densityRule {sf : SignedFormula} {b : Branch}
    {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    {r : TableauRule} {res : RuleResult} {o : TimeOrdering}
    (hfc : ¬ (FormalSystem.ProofSystem.FrameClass.Dense ≤ fc))
    (h : findApplicableRule sf b ord fc = some (r, res, o)) :
    r ≠ TableauRule.densityRule := by
  intro hr
  subst hr
  have hA := findApplicableRule_isApplicable h
  simp only [isApplicable] at hA
  split at hA <;> simp_all


/-! ### The leaf inversions the census case split consumes

Four kinds of fact, all of them read straight off `isApplicable` and `applyRule`: the result shapes
the six witness-guarded minting rules can report, the trigger shape `untlNeg` / `snceNeg` fire on,
their ACTIVE guard, and the four-bucket partition of all thirty-six constructors. None of them is
new mathematics; each is an inversion of an engine definition that is already frozen. -/

set_option maxHeartbeats 4000000 in
/-- **None of the six witness-guarded minting rules ever reports `.persistent`.**

The six are `freshLabelRules ∩ freshTimeRules` — `allFutureNeg`, `allPastNeg`, `someFuturePos`,
`somePastPos`, `untlPos`, `sncePos` — and the two payment lemmas that cover them,
`mintPotential_lt_of_pick_linear_sigmaFixed` and `..._branching_sigmaFixed`, between them cover
`.linear` and `.branching` only. `.branchingOrdered` and `.notApplicable` need no cover: neither
contributes a successor branch to `pickBranches`. `.persistent` would, and this lemma is what
closes it.

**Why the cheaper route is not available, recorded so it is not re-costed.** The obvious saving is
a `.persistent` variant of `mintPotential_lt_of_pick_linear_sigmaFixed`, since
`nonBranchingResultBranch` treats `.linear` and `.persistent` alike and
`applyRule_fresh_witness_nonbranching` is shape-agnostic. It does not exist, and cannot: the
missing input is `witnessPresent r sf b ord = false`, which the `.linear` and `.branching` arms of
`findApplicableRule` supply from their own `if` and the `.persistent` arm **deliberately does not**
— that arm carries no guard at all, by a design decision `findApplicableRule`'s own comment
records. So there is no `findApplicableRule_guard_persistent` to be had, and the exclusion has to
come from the rule side. It does, decidably, and that is this lemma.

`applyRule` has `.persistent` arms in plenty — `boxPos`, `diamondNeg`, `boxTemporal`,
`allFuturePos`, `allPastPos`, `someFutureNeg`, `somePastNeg`, `densityRule`, `priorUZ`, `priorSZ`,
`z1Rule`, `priorUGap`, `priorSGap`, `sepRule` and `serialityRule` all have one — and not one of them
is among the six. -/
private theorem applyRule_ne_persistent_of_fresh {r : TableauRule} {sf : SignedFormula}
    {b : Branch} {ord : TimeOrdering} {fs : List SignedFormula} {o : TimeOrdering}
    (hlab : ruleMintsFreshLabel r = true) (htime : ruleMintsFreshTime r = true)
    (hA : applyRule r sf b ord = (RuleResult.persistent fs, o)) : False := by
  cases r <;>
    first
      | exact Bool.noConfusion hlab
      | exact Bool.noConfusion htime
      | (simp only [applyRule] at hA
         (repeat' split at hA)
         all_goals simp_all)

/-- **`untlNeg`'s trigger shape, recovered from `isApplicable`.** The rule's arm is
`| .untlNeg, .neg, φ => (asUntil? φ).isSome`, so applicability fixes the sign and hands back the
`asUntil?` view's two components. Destructuring `sf` in the conclusion rather than asserting
`sf.sign = .neg` is what lets the consumer feed `selfGuardPotential_lt_of_untlNeg`, whose trigger
argument is a literal `⟨Sign.neg, φ, l⟩`, without a further rewrite. -/
theorem isApplicable_untlNeg_trigger {sf : SignedFormula}
    {fc : FormalSystem.ProofSystem.FrameClass}
    (hA : isApplicable TableauRule.untlNeg sf fc = true) :
    ∃ e g l, sf = ⟨Sign.neg, sf.formula, l⟩ ∧ asUntil? sf.formula = some (e, g) := by
  rcases sf with ⟨sign, φ, l⟩
  cases sign
  · simp only [isApplicable] at hA; simp at hA
  · rcases h : asUntil? φ with _ | ⟨e, g⟩
    · simp only [isApplicable, h] at hA; simp at hA
    · exact ⟨e, g, l, rfl, rfl⟩

/-- **The `snceNeg` mirror**, through `asSince?`. -/
theorem isApplicable_snceNeg_trigger {sf : SignedFormula}
    {fc : FormalSystem.ProofSystem.FrameClass}
    (hA : isApplicable TableauRule.snceNeg sf fc = true) :
    ∃ e g l, sf = ⟨Sign.neg, sf.formula, l⟩ ∧ asSince? sf.formula = some (e, g) := by
  rcases sf with ⟨sign, φ, l⟩
  cases sign
  · simp only [isApplicable] at hA; simp at hA
  · rcases h : asSince? φ with _ | ⟨e, g⟩
    · simp only [isApplicable, h] at hA; simp at hA
    · exact ⟨e, g, l, rfl, rfl⟩

/-- **`untlNeg`'s ACTIVE guard, inverted from a non-`notApplicable` result.**

One `by_contra` and no arm analysis, and the absence of the arm analysis is the point: the rule's
PASSIVE arm was retired from `applyRule`, so on a trigger the `asUntil?` view accepts there are
exactly two outcomes — the ACTIVE arm under its own `if`, or `.notApplicable`. A reported result
that is not `.notApplicable` therefore *forces* the guard, and the guard is transcribed here
character for character as the arm's `if` writes it, which is also character for character what
`selfGuardPotential_lt_of_untlNeg` asks for. -/
theorem applyRule_untlNeg_active_guard {φ : Formula} {l : Label} {b : Branch} {ord : TimeOrdering}
    {e g : Formula} {res : RuleResult} {o : TimeOrdering}
    (hform : asUntil? φ = some (e, g))
    (hA : applyRule TableauRule.untlNeg ⟨Sign.neg, φ, l⟩ b ord = (res, o))
    (hne : res ≠ RuleResult.notApplicable) :
    ((ord.futureOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true := by
  by_contra hg
  simp only [Bool.not_eq_true] at hg
  rw [show applyRule TableauRule.untlNeg ⟨Sign.neg, φ, l⟩ b ord
      = (RuleResult.notApplicable, ord) by
    simp only [applyRule, hform]
    simp_all] at hA
  exact hne (by simp_all)

/-- **The `snceNeg` mirror**: `pastOf` in place of `futureOf`, same one-`by_contra` inversion, same
absent PASSIVE arm. -/
theorem applyRule_snceNeg_active_guard {φ : Formula} {l : Label} {b : Branch} {ord : TimeOrdering}
    {e g : Formula} {res : RuleResult} {o : TimeOrdering}
    (hform : asSince? φ = some (e, g))
    (hA : applyRule TableauRule.snceNeg ⟨Sign.neg, φ, l⟩ b ord = (res, o))
    (hne : res ≠ RuleResult.notApplicable) :
    ((ord.pastOf l.time).isEmpty && decide (0 < ord.timeCount)
      && decide (ord.timeCount < 4)) = true := by
  by_contra hg
  simp only [Bool.not_eq_true] at hg
  rw [show applyRule TableauRule.snceNeg ⟨Sign.neg, φ, l⟩ b ord
      = (RuleResult.notApplicable, ord) by
    simp only [applyRule, hform]
    simp_all] at hA
  exact hne (by simp_all)

/-- **The four-bucket census, decided over all thirty-six constructors.**

Every rule either mints no fresh time, or mints one *and* is witness-guarded (the six of
`freshLabelRules ∩ freshTimeRules`), or is one of the two self-guarded minters, or is
`densityRule`. There is no fifth bucket and no residue, and `decide` rather than a hand-written
case list is what guarantees it: a constructor added to `TableauRule` without a home here would
break this proof rather than fall silently into a catch-all. The split is `cases r <;> decide`
rather than `revert r; decide` because `TableauRule` carries no `Fintype` instance, so the
quantified form has no `Decidable` instance to run; `cases` is exhaustive by construction, so the
anti-drift guarantee is the same.

The census is stated over `TableauRule` as a whole rather than over the rules the engine's three
stages can pick, so it covers `serialityRule` and `timeLinearity` too — both in the first bucket,
neither in `freshTimeRules`. -/
private theorem rule_census (r : TableauRule) :
    ruleMintsFreshTime r = false
    ∨ (r ∈ freshLabelRules ∧ ruleMintsFreshTime r = true)
    ∨ r = TableauRule.untlNeg ∨ r = TableauRule.snceNeg
    ∨ r = TableauRule.densityRule := by
  cases r <;> decide


/-! ### The four-bucket case split at the `pickBranches` level

The bulk of the section. `MintPaysForTimeFixed`'s three-way disjunct is proved for every successor
branch a pick reports, by splitting the picked rule into the census's four buckets and closing each
from a payment lemma that is already landed. Every bucket's arithmetic is **exact** — the two
budget conjuncts close by `omega` from inequalities with no slack in them — and no bucket adds a
hypothesis to the predicate.

The buckets are stated separately, each with the pick already destructured, so that each is a
standalone obligation with a readable statement rather than a branch of a long tactic block. -/

/-- The pick-source hypothesis `pick_stage_source`'s consumers take, specialised to a pick that has
already been destructured. Saves repeating the `Option`/`Prod` injectivity dance in every bucket. -/
private theorem pick_singleton_source {b : Branch} {ord : TimeOrdering} {r : TableauRule}
    {sf : SignedFormula} {res : RuleResult} {o : TimeOrdering}
    (hsf : sf ∈ b) (hA : applyRule r sf b ord = (res, o)) :
    ∀ r' res' o', (some (r, res, o) : Option (TableauRule × RuleResult × TimeOrdering))
      = some (r', res', o') → ∃ x, x ∈ b ∧ applyRule r' x b ord = (res', o') := by
  rintro r' res' o' h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨sf, hsf, hA⟩

/-- The same, carrying the no-mint fact `pickBranches_knownTimes_subset` additionally wants. -/
private theorem pick_singleton_source_noMint {b : Branch} {ord : TimeOrdering} {r : TableauRule}
    {sf : SignedFormula} {res : RuleResult} {o : TimeOrdering}
    (hsf : sf ∈ b) (hA : applyRule r sf b ord = (res, o))
    (hnm : ruleMintsFreshTime r = false) :
    ∀ r' res' o', (some (r, res, o) : Option (TableauRule × RuleResult × TimeOrdering))
      = some (r', res', o') → ∃ x, x ∈ b ∧ applyRule r' x b ord = (res', o')
        ∧ ruleMintsFreshTime r' = false := by
  rintro r' res' o' h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨sf, hsf, hA, hnm⟩

/-- **One step adds at most one known time, at the pick level.** The `pickBranches` counterpart of
`knownTimes_card_le_succ_of_unorderedSuccessor`, whose proof this is verbatim with
`pickBranches_time_dichotomy` in place of its engine-level lift. Buckets B and C both need the
inequality *before* the engine lift, because that is where the payment lemmas live. -/
private theorem pickBranches_knownTimes_card_le_succ {b : Branch} {ord : TimeOrdering}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (haux : OrdTimesKnown b ord)
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o)) :
    ∀ nb ∈ pickBranches b p, nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card + 1 := by
  intro nb hnb
  have hsub : nb.knownTimes.toFinset ⊆ insert b.nextTime b.knownTimes.toFinset := by
    intro t ht
    rcases pickBranches_time_dichotomy haux hp nb hnb t (List.mem_toFinset.mp ht) with h | h
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)
    · exact h ▸ Finset.mem_insert_self _ _
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- **Bucket A — the rule mints no fresh time: disjunct 1.**

Twenty-seven of the thirty-six constructors, plus `serialityRule` and `timeLinearity`, which is
what the engine's second and third stages run. Nothing about the rule's identity is used beyond the
negative fact: `applyRule_emitted_time_mem` turns it into a `knownTimes` subset, and both of
disjunct 1's conjuncts are read off that subset — the cardinality by `Finset.card_le_card`, the
rank by `splitOrderedRank_le_of_knownTimes_subset` against the ordering growth `pickOrd_mono`
supplies. `σ` does not appear.

This is also the bucket the strengthened bridge's *right* disjunct lands in: stages two and three
report no `findApplicableRule` equation, and they do not need one. -/
private theorem mintPays_bucketA {b : Branch} {ord : TimeOrdering} {Tmax : Nat}
    {r : TableauRule} {sf : SignedFormula} {res : RuleResult} {o : TimeOrdering} {nb : Branch}
    (haux : OrdTimesKnown b ord) (hsf : sf ∈ b)
    (hA : applyRule r sf b ord = (res, o)) (hnm : ruleMintsFreshTime r = false)
    (hnb : nb ∈ pickBranches b (some (r, res, o))) :
    nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
      splitOrderedRank Tmax nb o ≤ splitOrderedRank Tmax b ord := by
  have hsub := pickBranches_knownTimes_subset haux
    (pick_singleton_source_noMint hsf hA hnm) nb hnb
  refine ⟨Finset.card_le_card ?_, ?_⟩
  · intro t ht
    simp only [List.mem_toFinset] at ht ⊢
    exact hsub t ht
  · exact splitOrderedRank_le_of_knownTimes_subset hsub
      (pickOrd_mono (p := some (r, res, o)) (pick_singleton_source hsf hA))

/-- **Bucket B — the rule is witness-guarded and mints a time: disjunct 2.**

The six of `freshLabelRules ∩ freshTimeRules`. This is the bucket the strengthened bridge exists
for: the payment lemmas consume `findApplicableRule_guard_linear` / `_branching`, whose
`witnessPresent … = false` guard lives inside `findApplicableRule`'s own `if` and **not** inside
`applyRule`, so `pick_stage_source`'s `applyRule` pair is not enough and the stage-one equation is.

Three of the five result shapes are reachable and only two of them carry a successor branch:
`.branchingOrdered` and `.notApplicable` contribute nothing to `pickBranches`, and `.persistent` is
excluded by `applyRule_ne_persistent_of_fresh`. The remaining two are exactly the two the payment
lemmas cover.

Conjunct 1 is the sum, and it is exact: `|kt nb| ≤ |kt b| + 1` from the pick-level dichotomy, and
`mintPotential nb o + 1 ≤ mintPotential b ord` from the payment, add to
`mintTimeBudget nb o ≤ mintTimeBudget b ord` with nothing left over. -/
private theorem mintPays_bucketB {U : Finset SignedFormula} {σ : SignedFormula → SignedFormula}
    {b : Branch} {ord : TimeOrdering} {fc : FormalSystem.ProofSystem.FrameClass}
    {r : TableauRule} {sf : SignedFormula} {res : RuleResult} {o : TimeOrdering} {nb : Branch}
    (haux : OrdTimesKnown b ord) (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) (hsf : sf ∈ b)
    (hpick : findApplicableRule sf b ord fc = some (r, res, o))
    (hlab : ruleMintsFreshLabel r = true) (htime : ruleMintsFreshTime r = true)
    (hnb : nb ∈ pickBranches b (some (r, res, o))) :
    mintTimeBudget U σ nb o ≤ mintTimeBudget U σ b ord ∧
      mintPotential U σ nb o < mintPotential U σ b ord := by
  have hA : applyRule r sf b ord = (res, o) := findApplicableRule_applyRule_pair hpick
  have hlt : mintPotential U σ nb o < mintPotential U σ b ord := by
    cases res with
    | notApplicable =>
        simp [pickBranches, nonBranchingResultBranch, branchingResultBranches] at hnb
    | branchingOrdered bs =>
        simp [pickBranches, nonBranchingResultBranch, branchingResultBranches] at hnb
    | persistent fs => exact (applyRule_ne_persistent_of_fresh hlab htime hA).elim
    | linear fs =>
        simp only [pickBranches, nonBranchingResultBranch, branchingResultBranches,
          Option.toList, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hnb
        subst hnb
        exact mintPotential_lt_of_pick_linear_sigmaFixed hconf hfix hsf hpick hlab
    | branching bss =>
        simp only [pickBranches, nonBranchingResultBranch, branchingResultBranches,
          Option.toList, List.nil_append, List.mem_map] at hnb
        obtain ⟨arm, harm, rfl⟩ := hnb
        exact mintPotential_lt_of_pick_branching_sigmaFixed hconf hfix hsf hpick hlab arm harm
  refine ⟨?_, hlt⟩
  have hcard := pickBranches_knownTimes_card_le_succ haux
    (pick_singleton_source hsf hA) nb hnb
  simp only [mintTimeBudget]
  omega

/-- **Bucket C, the `untlNeg` half — the rule is self-guarded: disjunct 3.**

`untlNeg` mints a fresh time and is not in `freshLabelRules`, so disjunct 1 fails (a known time was
added) and disjunct 2 cannot move (`mintPotential`'s index set does not mention the rule). What
pays is the rule's own guard: the ACTIVE arm fires only into an empty future and leaves an edge
behind, so `selfGuardPotential` strictly drops. That is register entry 19's route 2 working exactly
as designed — the drop is *paired* with the combined-budget conjunct rather than offered bare,
because a bare drop is refuted there.

The combined conjunct is again exact: `|kt nb| ≤ |kt b| + 1`, `mintPotential nb o ≤ mintPotential b
ord` (branch and ordering both only grow), and `selfGuardPotential o + 1 ≤ selfGuardPotential ord`
sum to the required inequality with nothing to spare.

`sigmaTimeStable_of_sigmaFixed` is what lets `selfGuardPotential_lt_of_untlNeg` — stated at the
time-level hypothesis — be fed from the predicate's formula-level one. -/
private theorem mintPays_bucketC_untlNeg {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {sf : SignedFormula} {res : RuleResult}
    {o : TimeOrdering} {nb : Branch}
    (haux : OrdTimesKnown b ord) (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) (hsf : sf ∈ b)
    (hAp : isApplicable TableauRule.untlNeg sf fc = true)
    (hA : applyRule TableauRule.untlNeg sf b ord = (res, o))
    (hnb : nb ∈ pickBranches b (some (TableauRule.untlNeg, res, o))) :
    mintTimeBudget U σ nb o + selfGuardPotential U σ o
        ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
      selfGuardPotential U σ o < selfGuardPotential U σ ord := by
  obtain ⟨e, g, l, hsfeq, hform⟩ := isApplicable_untlNeg_trigger hAp
  have hne : res ≠ RuleResult.notApplicable := by
    rintro rfl
    simp [pickBranches, nonBranchingResultBranch, branchingResultBranches] at hnb
  have hsfb : (⟨Sign.neg, sf.formula, l⟩ : SignedFormula) ∈ b := by
    rw [← hsfeq]; exact hsf
  have hA' : applyRule TableauRule.untlNeg ⟨Sign.neg, sf.formula, l⟩ b ord = (res, o) := by
    rw [← hsfeq]; exact hA
  have hguard := applyRule_untlNeg_active_guard hform hA' hne
  have hdrop : selfGuardPotential U σ o < selfGuardPotential U σ ord := by
    have h := selfGuardPotential_lt_of_untlNeg (U := U) (σ := σ) hconf
      (sigmaTimeStable_of_sigmaFixed hfix) hsfb hform hguard
    rwa [hA'] at h
  refine ⟨?_, hdrop⟩
  have hcard := pickBranches_knownTimes_card_le_succ haux
    (pick_singleton_source hsf hA) nb hnb
  have hgrow : mintPotential U σ nb o ≤ mintPotential U σ b ord := by
    refine mintPotential_le_of_grow (resultBranch_sub (b := b) (nb := nb) (res := res) hnb).1 ?_
    have hm := applyRule_ord_mono TableauRule.untlNeg sf b ord
    rwa [hA] at hm
  simp only [mintTimeBudget]
  omega

/-- **Bucket C, the `snceNeg` half.** The exact past mirror, `pastOf` for `futureOf` throughout. -/
private theorem mintPays_bucketC_snceNeg {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {sf : SignedFormula} {res : RuleResult}
    {o : TimeOrdering} {nb : Branch}
    (haux : OrdTimesKnown b ord) (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) (hsf : sf ∈ b)
    (hAp : isApplicable TableauRule.snceNeg sf fc = true)
    (hA : applyRule TableauRule.snceNeg sf b ord = (res, o))
    (hnb : nb ∈ pickBranches b (some (TableauRule.snceNeg, res, o))) :
    mintTimeBudget U σ nb o + selfGuardPotential U σ o
        ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
      selfGuardPotential U σ o < selfGuardPotential U σ ord := by
  obtain ⟨e, g, l, hsfeq, hform⟩ := isApplicable_snceNeg_trigger hAp
  have hne : res ≠ RuleResult.notApplicable := by
    rintro rfl
    simp [pickBranches, nonBranchingResultBranch, branchingResultBranches] at hnb
  have hsfb : (⟨Sign.neg, sf.formula, l⟩ : SignedFormula) ∈ b := by
    rw [← hsfeq]; exact hsf
  have hA' : applyRule TableauRule.snceNeg ⟨Sign.neg, sf.formula, l⟩ b ord = (res, o) := by
    rw [← hsfeq]; exact hA
  have hguard := applyRule_snceNeg_active_guard hform hA' hne
  have hdrop : selfGuardPotential U σ o < selfGuardPotential U σ ord := by
    have h := selfGuardPotential_lt_of_snceNeg (U := U) (σ := σ) hconf
      (sigmaTimeStable_of_sigmaFixed hfix) hsfb hform hguard
    rwa [hA'] at h
  refine ⟨?_, hdrop⟩
  have hcard := pickBranches_knownTimes_card_le_succ haux
    (pick_singleton_source hsf hA) nb hnb
  have hgrow : mintPotential U σ nb o ≤ mintPotential U σ b ord := by
    refine mintPotential_le_of_grow (resultBranch_sub (b := b) (nb := nb) (res := res) hnb).1 ?_
    have hm := applyRule_ord_mono TableauRule.snceNeg sf b ord
    rwa [hA] at hm
  simp only [mintTimeBudget]
  omega

/-- **The census case split, assembled: `MintPaysForTimeFixed`'s disjunct at the pick level.**

The four buckets joined by `rule_census`, with `densityRule` — bucket D — discharged rather than
proved: `findApplicableRule_ne_densityRule` excludes it outright under the frame-class hypothesis,
and it is the only place that hypothesis is used in the whole section. When the bridge reports its
*right* disjunct instead, the rule is outside `freshTimeRules` and lands in bucket A, so no density
case arises on that side either.

Because the split is driven by a `decide`-proved census rather than by a hand-written constructor
list, no rule is handled by an unexamined catch-all: a rule with no bucket would break `rule_census`
rather than pass through here silently. -/
private theorem pickBranches_mintPays {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {Tmax : Nat}
    {p : Option (TableauRule × RuleResult × TimeOrdering)}
    (hfc : ¬ (FormalSystem.ProofSystem.FrameClass.Dense ≤ fc))
    (haux : OrdTimesKnown b ord) (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b)
    (hp : ∀ r res o, p = some (r, res, o) → ∃ sf, sf ∈ b ∧ applyRule r sf b ord = (res, o) ∧
      (findApplicableRule sf b ord fc = some (r, res, o) ∨ ruleMintsFreshTime r = false)) :
    ∀ nb ∈ pickBranches b p,
      (nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb (pickOrd ord p) ≤ splitOrderedRank Tmax b ord)
      ∨ (mintTimeBudget U σ nb (pickOrd ord p) ≤ mintTimeBudget U σ b ord ∧
          mintPotential U σ nb (pickOrd ord p) < mintPotential U σ b ord)
      ∨ (mintTimeBudget U σ nb (pickOrd ord p) + selfGuardPotential U σ (pickOrd ord p)
            ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
          selfGuardPotential U σ (pickOrd ord p) < selfGuardPotential U σ ord) := by
  rcases p with _ | ⟨r, res, o⟩
  · simp [pickBranches]
  · obtain ⟨sf, hsf, hA, hsrc⟩ := hp r res o rfl
    intro nb hnb
    rcases hsrc with hpick | hnm
    · rcases rule_census r with hnm | ⟨hlabmem, htime⟩ | hun | hsn | hden
      · exact Or.inl (mintPays_bucketA (Tmax := Tmax) haux hsf hA hnm hnb)
      · exact Or.inr (Or.inl (mintPays_bucketB haux hconf hfix hsf hpick
          (mem_freshLabelRules.mp hlabmem) htime hnb))
      · subst hun
        exact Or.inr (Or.inr (mintPays_bucketC_untlNeg haux hconf hfix hsf
          (findApplicableRule_isApplicable hpick) hA hnb))
      · subst hsn
        exact Or.inr (Or.inr (mintPays_bucketC_snceNeg haux hconf hfix hsf
          (findApplicableRule_isApplicable hpick) hA hnb))
      · exact absurd hden (findApplicableRule_ne_densityRule hfc hpick)
    · exact Or.inl (mintPays_bucketA (Tmax := Tmax) haux hsf hA hnm hnb)


/-! ### The engine lift and the discharge -/

/-- **The engine-level lift.** The `keyO`/`keyB` pattern of `expandOnceUnblocked_ordTimes`, run
once more: `pick_ord_eq` and `pick_branches_eq` restate the step's two components as `pickOrd` and
`pickBranches` over the three-stage `match`, and the pick-level result is applied to it with
`pick_stage_source_rule` as the source. The three-stage pick is not destructured a second time. -/
theorem expandOnceUnblocked_mintPays {U : Finset SignedFormula}
    {σ : SignedFormula → SignedFormula} {b : Branch} {ord : TimeOrdering}
    {fc : FormalSystem.ProofSystem.FrameClass} {tr : EventualityTracker} {Tmax : Nat}
    (hfc : ¬ (FormalSystem.ProofSystem.FrameClass.Dense ≤ fc))
    (haux : OrdTimesKnown b ord) (hconf : ∀ x ∈ b, x ∈ U) (hfix : SigmaFixed σ b) :
    ∀ nb ∈ unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1,
      (nb.knownTimes.toFinset.card ≤ b.knownTimes.toFinset.card ∧
        splitOrderedRank Tmax nb (expandOnceUnblocked b ord fc tr).2
          ≤ splitOrderedRank Tmax b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord ∧
          mintPotential U σ nb (expandOnceUnblocked b ord fc tr).2
            < mintPotential U σ b ord)
      ∨ (mintTimeBudget U σ nb (expandOnceUnblocked b ord fc tr).2
            + selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            ≤ mintTimeBudget U σ b ord + selfGuardPotential U σ ord ∧
          selfGuardPotential U σ (expandOnceUnblocked b ord fc tr).2
            < selfGuardPotential U σ ord) := by
  have keyO : (expandOnceUnblocked b ord fc tr).2
      = pickOrd ord
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_ord_eq
  have keyB : unorderedSuccessorBranches (expandOnceUnblocked b ord fc tr).1
      = pickBranches b
          (match findUnexpandedUnblockedWith b ord fc (blockedTimes b ord fc tr) with
           | some sf => findApplicableRule sf b ord fc
           | none =>
             match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                 && (findApplicableSerialRule sf b ord).isSome) with
             | some sf => findApplicableSerialRule sf b ord
             | none =>
               match b.find? (fun sf => !(blockedTimes b ord fc tr).contains sf.label.time
                   && (findApplicableLinearityRule sf b ord).isSome) with
               | some sf => findApplicableLinearityRule sf b ord
               | none => none) := pick_branches_eq
  rw [keyO, keyB]
  exact pickBranches_mintPays hfc haux hconf hfix (pick_stage_source_rule b ord fc tr)

/-- **The discharge.** `MintPaysForTimeFixed fc U Tmax` at an **arbitrary** universe — no syntactic
condition on the formulas, no emptiness, no added hypothesis on the predicate — for every frame
class the density rule cannot fire at.

**The one restriction, in the statement.** `¬ (FrameClass.Dense ≤ fc)` is a single hypothesis and
it is written here rather than hidden behind a definition, a `variable`, or a typeclass. It covers
`.Dense` and `.RTime` together and admits exactly `.Base` and `.ZTime`, and it is what buys
the exclusion of the density coordinate — register entry 20's item (b) — rather than closing it.
`gapPotential` is still implemented nowhere and assumed by nothing.

**What this retires.** Entry 20's item (a): the engine-level assembly. The per-rule payments all
existed; what was missing was the pick's rule identity at the successor, which
`pick_stage_source_rule` now threads. The predicate's hypothesis list is untouched.

**What this does not do.** It makes no terminus in this file non-vacuous. See the section prose. -/
theorem mintPaysForTimeFixed_of_not_dense {fc : FormalSystem.ProofSystem.FrameClass}
    {U : Finset SignedFormula} {Tmax : Nat}
    (hfc : ¬ (FormalSystem.ProofSystem.FrameClass.Dense ≤ fc)) :
    MintPaysForTimeFixed fc U Tmax := by
  intro σ b ord tr hri hconf hfix nb hnb
  exact expandOnceUnblocked_mintPays hfc hri.ordTimesKnown hconf hfix nb hnb

/-- **The discharge at the concrete universe the seed-level termini consume**, for **every** stock
`C` and every label set `L`.

This supersedes `mintPaysForTimeFixed_signedUniverse_empty`, whose universe is the `L = ∅` shadow,
and generalizes `mintPaysForTimeFixed_signedUniverse_untlSnceFree` off its syntactic fragment: `C`
here may carry `untl` and `snce` nodes freely, which is the case register entry 20 itself calls the
hard one. Neither of those two is deleted or altered; they are superseded in prose only, and
`mintPaysForTimeFixed_signedUniverse_untlSnceFree` remains the statement to reach for at `.Dense`
and `.RTime`, where this one is silent.

**Satisfiable rather than vacuous.** `signedUniverse_nonempty` makes the universe nonempty as soon
as `C` and `L` are, and the discharged hypothesis is a *theorem* there rather than a condition
nobody meets — which is exactly what separates this from the `hlab` residual. -/
theorem mintPaysForTimeFixed_signedUniverse_of_not_dense
    {fc : FormalSystem.ProofSystem.FrameClass} (C : Finset Formula) (L : Finset Label)
    (Tmax : Nat) (hfc : ¬ (FormalSystem.ProofSystem.FrameClass.Dense ≤ fc)) :
    MintPaysForTimeFixed fc (signedUniverse C L) Tmax :=
  mintPaysForTimeFixed_of_not_dense hfc

end FormalSystem.Metalogic.Decidability
