/-
Copyright (c) 2025 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Semantics.TaskFrame
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.SuccPred.Archimedean

-- Lower semantic layer: must not reach the proof system (G-15). `FrameClassValidity.lean`
-- is the one documented seam that imports `ProofSystem.Axioms`; nothing below it may.
assert_not_exists FormalSystem.ProofSystem.Axiom FormalSystem.ProofSystem.DerivationTree
  FormalSystem.ProofSystem.Derivable FormalSystem.ProofSystem.FrameClass

/-!
# Frame Properties — `def:frame-properties` as predicates on frames

`def:frame-properties` states its three clauses of a *task frame*: "A task frame
`F = ⟨W, D, ⇒⟩` is Discrete/Dense/Complete if ...". This module renders each of them as exactly
that — a `TaskFrame → Prop` — which is possible because `TaskFrame` carries its `Duration` as a
field rather than as an index (see `Semantics/TaskFrame.lean`'s module docstring).

## Main Definitions

- `TaskFrame.IsDense` — `def:frame-properties`' Dense clause
- `TaskFrame.IsDiscrete` — `def:frame-properties`' Discrete clause, verbatim
- `TaskFrame.IsSuccArchDiscrete` — `def:TMplus-f`'s Hölder narrowing of the discrete class to
  `ℤ`-time; strictly stronger than `IsDiscrete`, and the predicate the proof side's
  `FrameClass.Discrete` actually admits axioms for
- `TaskFrame.IsComplete` — `def:frame-properties`' Complete clause
- `TaskFrame.IsDedekind` — dense *and* complete: `cor:tm-completeness`'s TM⁺_c target
- `TaskFrame.Deterministic` — `def:deterministic`: every fibre of the task relation is a
  subsingleton, the frame condition the stability modal `⊡` collapses over

## Why five predicates and not three

Two of `def:frame-properties`' clauses each split in this tree, and in both cases collapsing the
split would silently widen a soundness target:

- **Discrete splits.** `def:frame-properties`' bare Discrete clause is `IsDiscrete`.
  `def:TMplus-f` narrows the class its axioms are sound over — "the successor-Archimedean discrete
  class to which BX_f and TM⁺_f are sound and complete is exactly `ℤ`-time" — and that narrowed
  class is `IsSuccArchDiscrete`. Only the narrowed one is a sound interpretation of the proof
  side's `FrameClass.Discrete`.
- **Complete splits.** `def:frame-properties`' bare Complete clause is `IsComplete`, which `ℤ`
  satisfies. `IsDedekind` adds density, deleting exactly the `ℤ` branch of the Hölder dichotomy
  (`Semantics/DurationClassification.lean`'s `complete_duration_discrete_or_dense`).

Neither pair is bridged by a duplicate definition: each of the five is defined once, and the two
splits are related by the projections `isDense_of_isDedekind` / `isComplete_of_isDedekind` and by
the implication from `IsSuccArchDiscrete` to `IsDiscrete` recorded on the former's docstring.

## Naming deviation of record: `Dedekind`, not `Complete`

`def:frame-properties` names the dense-and-complete class **Complete**. This tree deliberately
does not, and the deviation is recorded at each definition site below rather than left implicit.
See `TaskFrame.IsDedekind`.

## Why `IsDense` is an `abbrev`

`IsDense` is declared `abbrev` (i.e. `@[reducible] def`) rather than `def`, and that is
load-bearing rather than cosmetic. Lean's instance-cache registration whnfs a candidate
hypothesis at *reducible* transparency only, so a single non-reducible `def` anywhere in the
chain `FrameClass.Sat .Dense F ⇝ TaskFrame.IsDense F ⇝ DenselyOrdered F.Duration` stops
`h : Sat .Dense F` from ever reaching the local instance cache, no matter how the hypothesis is
introduced. `FrameClass.Sat` carries `@[reducible]` for the same reason; see its docstring in
`Semantics/FrameClassValidity.lean`. `IsComplete` and `IsDedekind` need no such change: they are
consumed by `obtain`/`rcases`, which whnf at *default* transparency.

## Frame properties as instance-resolvable classes: scope of the fix

Making the density chain reducible is the whole of what "frame properties resolve as instances"
buys here, and it is deliberately narrow. The strong form — restating each frame property as a
`class` with an `instance [F.IsDedekind] : F.IsDense` bridge — is *impossible* for
`IsSuccArchDiscrete`: a `Prop`-valued structure cannot project the `Type`-valued `SuccOrder`
field it must carry (the same reason `Nonempty` has no `.val`). The narrow fix nevertheless
achieves the goal it was proposed for, namely that instance resolution carries the
Dense/Dedekind inclusion at a `Sat` hypothesis.

One consequence that does **not** follow: the eight `by decide` regression examples elsewhere in
the tree are *not* made redundant by this. `FrameClass.Sat.anti`'s `decide` branch discharges
seven absurd order hypotheses and is still required and still cheap. Do not delete them on the
theory that instance resolution now covers them.

## References

* [TaskFrame.lean](TaskFrame.lean) — the bundled frame whose `Duration` field makes these
  ordinary predicates on a frame
* [DurationClassification.lean](DurationClassification.lean) — the Hölder dichotomy that makes the
  `IsComplete` / `IsDedekind` split exactly the `ℤ` / `ℝ` split
-/

namespace FormalSystem.Semantics

/--
`def:frame-properties`, Dense clause, verbatim: a task frame is **Dense** "if for any `x, y ∈ D`
where `x < y`, there exists `z ∈ D` where `x < z < y`".

That is Mathlib's `DenselyOrdered` on the frame's duration carrier on the nose, so the clause is
recorded by naming that class rather than by restating its body — `DenselyOrdered.dense` is the
recorded sentence.
-/
abbrev TaskFrame.IsDense (F : TaskFrame) : Prop := DenselyOrdered F.Duration

/--
`def:frame-properties`, Discrete clause, verbatim: a task frame is **Discrete** "if for any
`x ∈ D`, whenever there exists `y > x`, there is a least such `y' > x` satisfying `z ≥ y'` for all
`z > x`".

**Form chosen, and why.** The clause's closing conjunct — "a least such `y' > x` satisfying
`z ≥ y'` for all `z > x`" — is precisely `IsLeast {z | x < z} y'`, which unfolds to
`y' ∈ {z | x < z} ∧ ∀ z ∈ {z | x < z}, y' ≤ z`. The `IsLeast` spelling is used rather than the
equivalent least-positive-element form (`∃ p, IsLeast {d | 0 < d} p`) because the paper states the
clause pointwise at an arbitrary `x`, not at `0`, and the two agree only after the
translation-invariance of the duration group is invoked. Recording the clause as stated keeps that
invocation a proof step rather than a definitional assumption.

**This is not the predicate `FrameClass.Discrete` is interpreted by.** See
`TaskFrame.IsSuccArchDiscrete`, which is strictly stronger.
-/
def TaskFrame.IsDiscrete (F : TaskFrame) : Prop :=
  ∀ x : F.Duration, (∃ y, x < y) → ∃ y', IsLeast {z | x < z} y'

/--
The **successor-Archimedean discrete** class: `def:TMplus-f`'s narrowing of `IsDiscrete`.

`def:TMplus-f` closes with the Hölder sentence: "It follows by Hölder's theorem that a nontrivial
discrete Archimedean totally ordered abelian group is isomorphic to `ℤ`, and so the
successor-Archimedean discrete class to which **BX**`_f` and **TM**⁺`_f` are sound and complete is
exactly `ℤ`-time."

**It is this predicate, not `TaskFrame.IsDiscrete`, that `FrameClass.Discrete` admits axioms
for.** `Axiom.prior_UZ`, `Axiom.prior_SZ` and `Axiom.z1` all carry `.Discrete` as their
`minFrameClass`, and by the sentence above they are sound over `ℤ`-time rather than over every
frame satisfying `def:frame-properties`' bare Discrete clause. Interpreting `FrameClass.Discrete`
by `IsDiscrete` would silently widen the class under `soundness_ztime` — the defect that the
retired marker-typeclass frame-condition layer carried, and part of why that layer was removed.

**Existential, not instance binders, and deliberately so.** `SuccOrder` and `PredOrder` are
data-carrying structures, so a `TaskFrame → Prop` cannot take them as instance arguments; the
`Prop`-valued existential is what lets the property be predicated of a frame at all. Downstream
consumers destructure it with `obtain` and pass the witnesses positionally with `@` — never with
`haveI`, which breaks definitional equality against instances already baked into the types of `F`
and its models.

**There are, and can be, no named accessors — this form is final.** The obvious-looking
alternative, `structure TaskFrame.IsSuccArchDiscrete (F : TaskFrame) : Prop where [succ :
SuccOrder F.Duration] …`, does not compile: a `Prop`-valued structure cannot project a
`Type`-valued field, for exactly the reason `Nonempty` has no `.val`. An `inductive` reformulation
does compile but buys only `⟨⟩`-introduction and has no projections either, so it changes a
`def:TMplus-f`-citing definition for nothing. The existential therefore stays, and the two bridge
lemmas below — `isSuccArchDiscrete_of_instances` and `IsSuccArchDiscrete.elim` — are the
introduction and elimination interface in place of accessors. Use `.elim` or `obtain`; do not
expect a `.succ` field to appear later.

This predicate implies `IsDiscrete` (a successor order supplies the least strict upper bound at
every point), but that implication is not proved here: nothing in the tree consumes it, and the
two predicates are kept independent so that neither definition is stated in terms of the other.
-/
def TaskFrame.IsSuccArchDiscrete (F : TaskFrame) : Prop :=
  ∃ (_ : SuccOrder F.Duration) (_ : PredOrder F.Duration),
    IsSuccArchimedean F.Duration ∧ IsPredArchimedean F.Duration

/--
`def:frame-properties`, Complete clause, verbatim: a task frame is **Complete** "if every nonempty
`S ⊆ D` bounded above has a least upper bound in `D`".

Expressed as the explicit `Prop`-valued hypothesis rather than by demanding a
`ConditionallyCompleteLinearOrder` instance on the carrier: every downstream lemma indexed by the
frame's existing `LinearOrder` continues to apply, with no instance-unification risk.

**`ℤ` satisfies this.** The integers carry a Mathlib `ConditionallyCompleteLinearOrder` instance
(`Mathlib/Data/Int/ConditionallyCompleteOrder.lean`), so this clause does not single out the real
flow; by `Semantics.complete_duration_discrete_or_dense` its models are `{ℤ, ℝ}` up to
order-and-group isomorphism. The dense-and-complete narrowing is `TaskFrame.IsDedekind`.

**Reciprocal pointer for `ValidComplete`.** `Semantics/Validity.lean`'s `ValidComplete` is
`ValidOnFrames` at *this* bare clause, not at `IsDedekind` below, and is the one `Valid*` name
that is not `ValidIn` at its apparent tag. See the `ValidComplete` caveat in `Semantics/Validity.lean` — the one place the `ValidComplete` / `ValidRTime` distinction is argued in full.
-/
def TaskFrame.IsComplete (F : TaskFrame) : Prop :=
  ∀ s : Set F.Duration, s.Nonempty → BddAbove s → ∃ x, IsLUB s x

/--
The **dense and Dedekind-complete** class: `def:frame-properties`' Dense clause conjoined with its
Complete clause. This is `cor:tm-completeness`'s TM⁺_c target — that corollary states TM⁺_c
complete over "the dense-and-complete class" — and the semantic interpretation of the proof side's
`FrameClass.Dedekind`.

Adding density to `IsComplete` deletes precisely the `ℤ` branch of the Hölder dichotomy and
nothing else: by `Semantics.complete_duration_discrete_or_dense` a complete duration group is
either `≃+o ℤ` or densely ordered, and by `Semantics.complete_not_dense_iso_int` those branches
are exclusive. So up to order-and-group isomorphism this class is the real flow.

## Naming deviation of record

**`def:frame-properties` calls this property Complete; this tree calls it Dedekind.** That is a
deliberate divergence from the definition of record, not an oversight and not a synonym chosen at
random, and it is the only naming deviation sanctioned on this front. The word "complete" is
already load-bearing here for *proof-theoretic* completeness — `completeness`,
`completeness_dense`, `completeness_ztime`, `completeness_rtime`,
`Metalogic/StrongCompleteness.lean` — so a `TaskFrame.IsComplete`-versus-`FrameClass.Complete`
pair would collide with the tree's most-cited word at exactly the point where the two senses meet.
"Dedekind complete" is the standard and unambiguous name for the order-theoretic property, so it
is what the dense-and-complete class is called here, in `FrameClass.Dedekind`, and in
`ValidRTime`.

Note that the bare Complete clause above *does* keep the paper's name (`IsComplete`); only the
dense-and-complete conjunction is renamed.
-/
def TaskFrame.IsDedekind (F : TaskFrame) : Prop := F.IsDense ∧ F.IsComplete

namespace TaskFrame

/-- Introduce `IsSuccArchDiscrete` from the four instances it existentially quantifies, so that a
site holding them as instance binders does not have to write the nested anonymous constructor. -/
theorem isSuccArchDiscrete_of_instances (F : TaskFrame)
    [SuccOrder F.Duration] [PredOrder F.Duration]
    [IsSuccArchimedean F.Duration] [IsPredArchimedean F.Duration] :
    F.IsSuccArchDiscrete :=
  ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

/-- Eliminate `IsSuccArchDiscrete` by running a continuation under its four instances. This is the
substitute for the projections the definition cannot have (see its docstring): the witnesses reach
the continuation through the instance cache rather than through named accessors. -/
theorem IsSuccArchDiscrete.elim {F : TaskFrame} {motive : Prop} (h : F.IsSuccArchDiscrete)
    (k : ∀ [SuccOrder F.Duration] [PredOrder F.Duration] [IsSuccArchimedean F.Duration]
           [IsPredArchimedean F.Duration], motive) : motive := by
  obtain ⟨_, _, _, _⟩ := h
  exact k

/-- A dense-and-complete frame is dense. Named so that downstream sites cite a lemma rather than
an anonymous `And` projection. -/
theorem isDense_of_isDedekind {F : TaskFrame} (h : F.IsDedekind) : F.IsDense := h.1

/-- A dense-and-complete frame is complete. Named so that downstream sites cite a lemma rather
than an anonymous `And` projection. -/
theorem isComplete_of_isDedekind {F : TaskFrame} (h : F.IsDedekind) : F.IsComplete := h.2

/-!
## Determinism

`def:deterministic` — the sixth frame property, and the only one here that constrains the *task
relation* rather than the duration order.
-/

/--
`def:deterministic`: **the frame is deterministic** — every fibre of the task relation is a
subsingleton. Equivalently (`TaskFrame.deterministic_iff`), `w ⇒_x u` and `w ⇒_x v` force
`u = v`.

Stated in the tree's own `Fib` idiom rather than pointwise so that the two existing helpers
consume it verbatim: `TaskFrame.saturation_of_fib_subsingleton` turns it into the frame's
*Saturation* field (`TaskFrame.saturation_of_deterministic` below), and
`translationRel_fib_subsingleton` (`Semantics/Frames/Standard.lean`) is already literally a proof
of it for the translation frames.

**One bidirectional condition, not a forward/backward conjunction.** `d` ranges over *all* of
`F.Duration`, negative durations included. That is not a strengthening bolted on for convenience:
`FrameOver.converse` is a structure field, so `w ⇒_x u ↔ u ⇒_{-x} w` holds in every frame, and
the past instances of this predicate are therefore already determined by the future ones being
asserted about *every* state. Writing it with an unrestricted binder is what makes that visible.

**Restricting `d` to `0 ≤ d` gives a strictly weaker predicate that does NOT support the bridge
lemma.** `states_eq_of_deterministic` (`Semantics/StarDeterminism.lean`) applies this at the
possibly negative duration `s - t`; under a `0 ≤ d` guard the frame `natFrame` over `ℤ` (which
relates every state to every state at every nonzero duration in the past direction) would count
as "deterministic" while refuting the collapse. The unrestricted binder is a correctness
requirement, not fidelity to a particular phrasing.
-/
def Deterministic (F : TaskFrame) : Prop :=
  ∀ (w : F.WorldState) (d : F.Duration), (TaskFrame.Fib F.TaskRel w d).Subsingleton

/-- The `Fib` form and the pointwise form of `def:deterministic` agree — one line each way. The
pointwise form is the one a refutation is easiest to state against (see
`Metalogic/Independence/DriftFrame.lean`); the `Fib` form is the one the helpers consume. -/
theorem deterministic_iff (F : TaskFrame) :
    F.Deterministic ↔
      ∀ (w u v : F.WorldState) (x : F.Duration), F.TaskRel w x u → F.TaskRel w x v → u = v :=
  ⟨fun h w _ _ x hu hv => h w x hu hv, fun h w x _ hu _ hv => h w _ _ x hu hv⟩

/-- A deterministic frame gets its *Saturation* field for free, via
`TaskFrame.saturation_of_fib_subsingleton`: a fibre that is a subsingleton is trivially
spherically well-behaved, and `Seg` is a subset of a fibre. No Zorn, no frame machinery. This is
what lets a determinism hypothesis be *assumed* on an abstract frame without also assuming
anything else. -/
theorem saturation_of_deterministic {F : TaskFrame} (h : F.Deterministic) :
    TaskFrame.Saturation F.TaskRel :=
  TaskFrame.saturation_of_fib_subsingleton h

end TaskFrame

end FormalSystem.Semantics
