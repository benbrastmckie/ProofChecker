# Implementation Summary: The Stability Modal and the Deterministic Task Frames

**Task**: 536
**Plan**: `plans/01_determinism-collapse-and-non-definability.md`
**Report**: `reports/01_determinism-collapse-and-store-recall.md`
**Record artifacts**: `reports/02_correspondence-record-and-store-recall-recommendation.md`
**Phases**: 8 of 8 executed; 7 `[COMPLETED]`, 1 (`Phase 7`) `[COMPLETED WITH EXCLUSIONS]`

## What landed

### Deliverable (a) — the deterministic collapse, choice-free (Phase 1)

`FormalSystem/Semantics/FrameProperty.lean` gained `TaskFrame.Deterministic` — every fibre of the
task relation is a subsingleton, with the duration binder **unrestricted** over `F.Duration` —
plus `TaskFrame.deterministic_iff` (the `Fib` form agrees with the pointwise form) and
`TaskFrame.saturation_of_deterministic` (a deterministic frame's *Saturation* field is free).

`FormalSystem/Semantics/StarDeterminism.lean` (new) carries the singleton bridge and the collapse:

| Declaration | Statement |
|---|---|
| `states_eq_of_deterministic` | two total histories agreeing at one time agree at every time |
| `stab_iff_of_deterministic` | `⊡φ ↔ φ` at every total history and time |
| `determined_of_deterministic` | *Determined* `φ → ⊡φ` is frame-valid |
| `stab_biconditional_starValidOn_of_deterministic` | both halves of `⊡φ ↔ φ` as frame validities |

All four report `#print axioms → [propext]`. **No `Classical.choice`.** These are the names task
537 imports.

`refute_determined`'s docstring in `Semantics/StarNonValidities.lean` was repaired: it asserted
"Validity over deterministic frames is not formalized here", which Phase 1 falsified. It now
cross-references `determined_of_deterministic`, records that the refuting instance is `Fp` and not
an atom (at atoms the schema holds on every frame, so no substitution argument is available), and
records that `natFrame`'s discreteness is a genuine hypothesis.

### Deliverable (b) — non-definability of determinism (Phases 2-7)

Six new modules under `FormalSystem/Metalogic/Independence/`:

| Module | Lines | Contents |
|---|---|---|
| `RealTranslationFrame.lean` | 189 | `realOrder`, `oneShift`, `F1`; `f1_deterministic`, `f1_total_eq_orbit`, `f1_eq_of_states_eq` |
| `DriftFrame.lean` | 254 | `fzeroRel`, `fzeroFrame`/`F0` with all six `FrameOver` axioms, `fzero_not_deterministic` |
| `DriftHistories.lean` | 178 | the order-isomorphism core; (H1) `fzero_orderFlow`, (H2) `fzero_stateOccurs` |
| `OrderTransfer.lean` | 197 | the generic layer: `OrderFlow` (H1), `StateOccurs` (H2), the transfer lemmas |
| `StateSetTruth.lean` | 240 | `satSet`, `starTruthAt_iff_mem_satSet`, `starValidOn_iff_satSet_univ`, `determined_of_orderFlow` |
| `DeterminismUndefinable.lean` | 183 | (T3), (T4), `deterministic_not_starDefinable` |

The headline results:

- **(T3)** `determined_valid_on_non_deterministic` — `F°` validates every instance of *Determined*
  and is not deterministic. The converse of the Phase 1 collapse is therefore **false**, not
  merely unproved.
- **(T4)** `fzero_starValidOn_iff_f1` — `F°` and `F¹` validate exactly the same `StarFormula`s.
- `deterministic_not_starDefinable` — no set of `StarFormula`s defines the deterministic frames.

### Deliverables (c) and (d) — records only (Phase 8)

`reports/02_correspondence-record-and-store-recall-recommendation.md`: the paper-`\label`↔Lean
correspondence table (including what is deliberately *not* formalized and why), the four points
where the tree and the manuscript must agree, the rename list, and the spawn-ready follow-up
description for narrow world store/recall with a single register (~600-900 lines), with its
transport-layer breakage table and the choice-asymmetry finding.

## Architectural choices worth knowing

- **The `ShiftSet` route to `F¹` was mandatory.** `translationFrame` is a plain `def`, so
  `τ.states` returns an unreduced `WorldState` and the world-set characterization does not
  elaborate — a failure no type ascription or `@[reducible]` alias repairs. `ShiftSet.fibre` and
  `.frame` are `@[reducible]`, and the route additionally hands over `total_eq_orbit`, which *is*
  that characterization. `probes/02`'s bespoke `foneFrame` was deliberately not promoted.
- **One generic bridge, two instantiations, not two parallel inductions.** The state-set recursion
  mentions only the order on the carrier and neither task relation. That is the crux of
  `cor:no-characterization`, and writing it once against (H1)/(H2) makes it visible.
- **The `box` clause needs no decidability.** It is written as the argument-ignoring set
  `{_w | ∀ v, v ∈ satSet V φ}`, extensionally the `univ`/`∅` split but requiring no set-equality
  decision. The plan's fallback (`Classical` or a disjunction encoding) was not needed.
- **(H2) is discharged by explicit affine witnesses at both frames**, never by `cor:occurrence`.
  This is what keeps the argument free of `thm:extension` and Zorn.

## Verification

| Check | Result |
|---|---|
| `lake build` (full tree) | green |
| `sorry` in new/modified files | none |
| New `axiom` declarations | none |
| `grep -rn 'task [0-9]' FormalSystem/` new hits | none |
| Files outside `specs/536_*/` and `FormalSystem/` modified | none; **nothing under `/home/benjamin/Philosophy/`** |
| `#print axioms` on the Phase 1 collapse theorems | `[propext]` — no `Classical.choice` |
| `#print axioms` on `starTruthAt_iff_mem_satSet` | `[propext]` |
| `#print axioms` on `determined_of_orderFlow` | `[propext, Quot.sound]` |
| `#print axioms` on (T3)/(T4)/`deterministic_not_starDefinable` | `[propext, Classical.choice, Quot.sound]` — **see the exclusion below** |

### The one verification criterion not met as literally written

The plan's Phase 7 verification asked for "`#print axioms` on (T3) and (T4): no
`Classical.choice`". **That is not achievable and the plan's stated contingency does not apply.**

The plan anticipated that a `Classical.choice` would come from the Phase 6 `box`-case encoding and
prescribed switching to a disjunction form. It does not. Three checks establish the actual source:

1. `#print axioms fzero_not_deterministic` — whose whole proof is two `norm_num` facts about `1`
   and `2` — already reports `Classical.choice`. It comes with `ℝ`, whose order and field
   structure are classical in Mathlib.
2. `#print axioms starTruthAt_iff_mem_satSet` reports `[propext]` **alone**, and
   `determined_of_orderFlow` reports `[propext, Quot.sound]`. The entire generic argument is
   choice-free; only its instantiation at a real carrier is not.
3. `fzero_stateOccurs` and `f1_stateOccurs` — the two hypotheses that could have needed
   `thm:extension` — are discharged by explicit affine witnesses.

So constraint C4's substance (no "validity ⟹ frame condition" step, no Zorn) **is** met and is
pinned by sharper evidence than the plan's criterion would have provided; the criterion itself was
unsatisfiable for any statement mentioning `ℝ`. This is recorded in
`DeterminismUndefinable.lean`'s module docstring rather than left implicit, and Phase 7 is marked
`[COMPLETED WITH EXCLUSIONS]` accordingly.

## Plan Deviations

- **Phase 1** — *altered*: the `#print axioms` pin was recorded as a re-runnable comment block in
  `StarDeterminism.lean`'s module docstring rather than as a new test file, keeping the touched-file
  set to the plan's list. Verified externally with `lake env lean` on a scratch file.
- **Phase 2** — *altered*: `import Mathlib.Data.Real.Basic` was needed.
  `Semantics/ShiftSet.lean` does not in fact re-export `ℝ`, contrary to a note at
  `Metalogic/DedekindNonCompactness.lean`'s `realOrder`. One import line, no scope change.
- **Phase 4** — *recorded choice* (the plan permitted either): the order-isomorphism core went into
  a new `Independence/DriftHistories.lean` rather than extending `DriftFrame.lean`, which was
  already 254 lines.
- **Phase 6** — *altered*: the `box` decidability question was resolved by neither of the plan's two
  options. The argument-ignoring set encoding needs no decidability at all. The `atom` case was
  additionally rewritten off `Exists.choose` for the same reason.
- **Phase 7** — *altered*: `fzeroFrame` is the `FrameOver realOrder`; the `TaskFrame` it includes
  into is `F0`, matching `F1`'s spelling. Validity statements are on `F0`/`F1`.
- **Phase 7** — *exclusion*: the "no `Classical.choice` on (T3)/(T4)" criterion, as described above.
