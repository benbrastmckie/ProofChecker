# Semantics

Task frame semantics for TM bimodal logic.

## Contents

This table is ordered by the layering, not alphabetically, and carries no line counts, so it is
registered as hand-maintained rather than generated. Registration is not an exemption from being
checked: the `INV` check in `scripts/check-module-invariants.sh` asserts it has a row for every
live file and subdirectory here, and no row for anything else.

<!-- INVENTORY: hand-maintained (dir=FormalSystem/Semantics) -->

| File | Description |
|------|-------------|
| TemporalOrder.lean | `TemporalOrder` — a nontrivial totally ordered abelian group, `def:temporal-order`'s object, bundled with its four algebraic instances; `intOrder` |
| TaskFrame.lean | Task frame structure (worlds, times, accessibility), the fibre/total-space pair, the class-helper families A-D, and the frame constants |
| Frames/ | The standard-frame index: `Standard` (1 file) — home of `translationFrame` and `permissiveFrame`, and the linked census of every other standard frame |
| FrameProperty.lean | Frame properties as predicates on `TaskFrame` (`IsDense`, `IsDiscrete`, `IsSuccArchDiscrete`, `IsComplete`, `IsDedekind`, and `Deterministic`), and the `FrameClass` ordering they induce |
| FrameClassValidity.lean | `FrameClass.Sat` and the `sat_intro` binder adapters: validity relative to a frame class |
| IntNormalForm.lean | The ℤ-frame normal form: over `D = ℤ` a frame is its one-step relation |
| TaskModel.lean | Task models with valuation functions |
| ConvexHistory.lean | Convex histories for temporal evaluation, and `TaskFrame.HF` — the paper's possible worlds |
| Truth.lean | `TruthAt`, the truth relation for formula evaluation, with its `truth_norm` simp-normal form; the relational truth transport `TruthCorr` / `Truth.truthAt_of_truthCorr` (one `induction φ`) from which `timeShift_preserves_truth`, `truthAt_of_truthIso`, and `IntTransfer.truthAt_map` are derived; `TruthIso`/`TruthAntiIso` |
| BLTruth.lean | `BLTruthAt` — the same truth relation for the tense-primitive base language, by native six-clause recursion on `BLFormula` per `def:BL-semantics` (not `TruthAt ∘ tr`) |
| ShiftSet.lean | Shift-set representation theorem: task models ↔ shift sets, both directions with truth correspondence |
| Validity.lean | Validity and semantic consequence |
| BLValidity.lean | `BLValid`, `BLSemanticConsequence`, `BLValidDense`, `BLValidDiscrete`, `BLValidDiscreteSucc`, `BLValidDedekind` — binder-for-binder base-language mirrors of Validity.lean |
| BLSchemaValidity.lean | DF/DN semantic lemmas (Lemmas B/C) and DF's `PredOrder` past-dual, consumed by `Metalogic/Conservativity/SpWitness.lean` and `bl_soundness_discrete_succ` |
| StarTruth.lean | `SameStateAt` (the paper's `⟨τ⟩_x`) and `StarTruthAt` — the truth recursion for L⋆ (L⁺ plus the stability modal `⊡`, `StarLanguage/Formula.lean`), the `StarTruth.*` clause lemmas, the S5 validities of `⊡`, and `stab_state_only` |
| StarValidity.lean | `StarValidOnFrames`, `StarValidIn`, `StarValid` and per-class abbreviations — L⋆ mirrors of Validity.lean; `starTruthAt_ofFormula` and `starValidIn_ofFormula_iff`, semantic conservativity of L⋆ over L⁺ at every frame class |
| StarPasting.lean | `paste` — two total histories sharing a state paste into a total history — the purity congruences, and the pasting validities PS/US/FS/GS with their past mirrors |
| StarNonValidities.lean | The five refutations on `natFrame` over ℤ that bound the `⊡` axiom set from above (`⊡p → □⊡p`, `G⊡p → ⊡Gp`, `⊡GPp → G⊡Pp`, *Determined*, `P⊡p → ⊡Pp`) |
| StarDeterminism.lean | `app:deterministic`'s positive half: `states_eq_of_deterministic` (the singleton bridge), `stab_iff_of_deterministic`, `determined_of_deterministic`, `stab_biconditional_starValidOn_of_deterministic` — the collapse `⊡φ ↔ φ` over every `TaskFrame.Deterministic` frame, choice-free (`[propext]` only) |
| DurationClassification.lean | Classification of Dedekind-complete duration groups: discrete (`≃+o ℤ`) or densely ordered; also `duration_dense_or_least_pos`, the Archimedean-free order dichotomy |
| LexCarrier.lean | `LexInt`: `SuccOrder`/`PredOrder` instances, `isLeast_pos`, and the three non-Archimedean theorems for `α ×ₗ ℤ` at an arbitrary ordered abelian group `α` — instantiated at `ℚ` for the CEF countermodel and at `ℤ` for the `Sat .Discrete` separation |
| FrameAxioms.lean | The frame axioms (nullity, compositionality, reflection) as standalone statements |
| IntTransfer.lean | Transfer of ℤ-frame facts across the normal form |
| PartialHistory.lean | Partial histories on arbitrary nonempty subsets of the duration group — the tier *below* convexity |
| PartialHistoryOrder.lean | The order structure on partial histories |
| Extension/ | Extension of partial histories: `Admissible`, `Constraint`, `Extension`, `PeriodicExtension`, `Step` (5 files) |
| Ultraproduct/ | The dependent ultraproduct of shift sets and Łoś's theorem: `Carrier`, `IndexFilter`, `ShiftSetProduct`, `Los` (4 files) |
| Correspondence/ | The frame-class Galois layer: `Galois`, `Indicator`, `DurationFrames`, `FwdRec`, `FwdRecPeriodicity`, `FwdRecBridge` (6 files) |

## Key Definitions

- `TaskFrame`: Frame structure with world-time pairs and accessibility
- `TaskModel`: Frame with valuation function for atoms
- `ConvexHistory`: World states indexed by a convex set of times; the domain need not be all of `D`, so a convex history may be bounded
- `truth_at`: Truth of formula at convex history and time
- `valid`: Formula true in all models at all possible worlds

## The ℤ-frame normal form

`IntNormalForm.lean` establishes that over `D = ℤ` a task frame is determined by its **one-step**
relation `step w u := TaskRel w 1 u`, in both directions:

- **Decomposition** — `taskRel_eq_iter`: `TaskRel w d u` is an `|d|`-fold iterate of `step`,
  forwards for `d ≥ 0` and backwards for `d ≤ 0`. The zero case is `nullity_identity`, the positive
  case is *Compositionality* at `y = 1`, and the negative case is the converse convention.
- **Synthesis** — `TaskFrame.ofStep`: a bi-serial relation on a finite nonempty carrier generates a
  `TaskFrame ℤ` with all seven fields discharged. Six are free from the normal form; *Seriality* is
  the one genuine obligation, and the module records the `Unit`-carrier counterexample showing that
  neither finiteness nor discreteness supplies it.
- **History space** — `mem_HF_iff_adjacent`: `H_F` over ℤ is exactly the set of bi-infinite
  step-paths `f : ℤ → WorldState` with `step (f n) (f (n+1))`. `def:world-history`'s all-pairs
  task-respect obligation is redundant over ℤ; adjacency implies it.

`Truth.box_const` is the companion fact on the truth side: a boxed formula's truth value depends on
neither the history nor the time, so it is a constant of the model. History-independence is
definitional (the box clause never mentions `τ`); time-independence is time-homogeneity.

Together these reduce the semantics of a finite-`WorldState` ℤ-frame to reachability in a finite
directed graph — the presentation `Metalogic/Decidability/IntPresentation.lean` computes on.

## Related Documentation

- [Parent README](../README.md)
- [Metalogic Soundness](../Metalogic/README.md) - Uses semantics for soundness

---

*Last verified: 2026-09-07*
