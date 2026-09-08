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
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.TimeReuse
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.MonotoneIssuance
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.OrientedGate
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.FourComponent
import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound.SigmaFixed
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
