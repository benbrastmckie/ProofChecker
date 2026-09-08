# Implementation Plan: Task #544

- **Task**: 544 - Machine-check the failing half of CEB: `(Sp)` is not a theorem of TM, via a native BL frame notion and native BL soundness
- **Status**: [IMPLEMENTING]
- **Effort**: 6 hours
- **Dependencies**: None (all prerequisites are in-tree and built)
- **Research Inputs**: `specs/544_machine_check_sp_underivable_native_bl_soundness/reports/01_sp-underivable-native-bl-soundness.md` (plus its compiling prototype at `specs/544_machine_check_sp_underivable_native_bl_soundness/prototype/SpCountermodelPrototype.lean`)
- **Artifacts**: plans/01_sp-underivable-native-bl-soundness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Machine-check the one claim in the paper's TM^- fragment discussion that is currently recorded
as *not verified*: `(Sp) := □(DF φ) ∨ □(DN ψ)` is BL-valid on every task frame but is **not**
derivable in TM (`BaseLanguage.DerivationTree FrameClass.Base`). Because `(Sp)` is valid on the
whole task-frame class, no `TaskFrame`-bound refutation can exist; the refutation must live on a
structure outside that class on which every TM schema remains sound. The work therefore adds a
*native* BL frame notion and truth definition (unbound from `TaskFrame`), a native BL soundness
theorem proved by recursion on the derivation tree, the concrete two-fibre countermodel, and the
two headline results `not_derivable_sp` and `tmCompleteBase_refuted`. Definition of done: all
five deliverables land sorry-free with the standard `[propext, Classical.choice, Quot.sound]`
axiom profile, `lake build` is green, `scripts/check-module-invariants.sh` and
`scripts/readme-lint.sh` pass, and every repository record that currently says this result is
"not machine-checkable in this tree, and not close" has been corrected.

### Research Integration

The research report is unusually load-bearing here: it delivered a **340-line, sorry-free,
already-compiling end-to-end prototype** covering all five scope items, verified with
`lake env lean` against the current tree and reporting the standard three-axiom profile for
`not_derivable_sp`, `tmCompleteBase_refuted` and `blFrameValid_of_derivation`. This plan is
therefore a *promotion* plan, not a discovery plan: the mathematical risk is discharged and what
remains is module placement, docstrings, wiring, and repository-gate compliance. Four research
findings shape the phases directly:

1. **The countermodel is `ℤ ⊕ ℝ`, Mathlib's disjoint-sum order, not the lexicographic `ℤ + ℚ`
   named in the task description.** A lexicographic sum is still a single linear order, and the
   report's sharpened impossibility argument shows no single linear order can refute `(Sp)` at a
   fixed time (a `DF` instance can fail only where there is no immediate successor; a `DN`
   instance only where there is one). Two simultaneously `□`-accessible order-shapes are
   required, which is exactly the disjoint sum. No bespoke carrier module is needed.
2. **`□` is read as the universal modality over the whole point set.** This is the cheapest
   condition making MF (`□φ → □Gφ`) sound, and it matches `Metalogic/Conservativity.lean`'s own
   description of the intended two-fibre structure.
3. **TD is discharged by a swap-*transfer* lemma, not the swap-strengthened induction the task
   description prescribes.** The frame class is closed under order reversal, so
   `truth_swap : BLFrameTruth F.swap V w φ ↔ BLFrameTruth F V w φ.swapBL` (six one-line cases)
   closes `temporal_duality` in a single line. The simultaneous validity/swap-validity recursion
   of `bl_derivable_valid_and_swap_valid_zTimeSucc` is not needed.
4. **Three corrections to the task description are adopted by this plan** (see Goals & Non-Goals
   and Risks): the mirrored corollary is `tmCompleteZTime_refuted`, not
   `tmCompleteDiscrete_refuted`; the axiom list "MK, MT, M5, MF, TD, TK, T4, TB, TA, TL" is stale
   and mis-typed; and the universally quantified reading of "no instance of `(Sp)` is a theorem
   of TM" is **false** — `Sp ⊤ ψ` is true on the countermodel — so the deliverable is the
   schema-level claim witnessed by the atomic instance.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` was consulted read-only; no `roadmap_path` was supplied in this dispatch, so
no roadmap review/update phases are added and ROADMAP.md is not modified. Alignment: this task
serves the **Paper Alignment Programme (possible_worlds.tex)** section and **Phase 5: Publication
and Documentation**. It converts one paper footnote from "stated, not verified" into a citable,
machine-checked repository result, and it closes the last outstanding row of the CEB analysis in
`FormalSystem/Metalogic/Conservativity.lean`. It does not touch the Phase 1 completeness or
Phase 2 decidability fronts.

## Goals & Non-Goals

**Goals** (the identifiers this plan commits to; statements pinned in the Lean Challenge
Statements section below):

- A native BL frame notion not bound to the task-frame class: `BLFrame`, with its
  order-reversal `BLFrame.swap`.
- A native BL truth definition over it and the matching validity notion: `BLFrameTruth`,
  `BLFrameValid`.
- The swap-transfer lemma that makes TD sound: `truth_swap`.
- Native BL soundness for TM, verifying every axiom schema and every derivation rule directly:
  `axiom_valid`, `blFrameValid_of_derivation`.
- The concrete countermodel and its valuation: `twoFibre`, `twoV`.
- The evaluation and the two headline results: `sp_false`, `not_derivable_sp`,
  `tmCompleteBase_refuted`.

**Non-Goals**:

- Whether TM^-_d and TM^-_dc are complete over the dense and dense-and-complete classes. This
  remains an open question and is untouched.
- Any theorem whose *conclusion* is forward conservativity (`forward`, `ForwardBase`,
  `TMCompleteBase`). The hard constraint inherited from `Metalogic/Conservativity.lean` stands:
  forward conservativity is refuted, not open, and must never be stated and discharged with
  `sorry`. This plan states only the **negation** `¬ TMCompleteBase`, which is exactly the shape
  `Z1Countermodel.tmCompleteZTime_refuted` already has.
- Editing the JPL paper. `possible_worlds.tex` does not live in this repository; updating the
  footnote to cite this result is downstream work outside this task.
- Any universally quantified "no instance of `(Sp)`" statement — see Risks; it is false.
- Reworking `BLTruthAt`, `bl_soundness`, or anything in the existing `TaskFrame`-bound semantic
  stack. The native semantics is additive and sits beside them.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| The task description's "no instance of `(Sp)` is a theorem of TM" is **false as literally stated** — `DF ⊤` is true at every point of every `BLFrame` (from `no_max`), so `□(DF ⊤)` holds and `Sp ⊤ ψ` is not refuted by the countermodel | H | Certain (already established) | State the deliverable at the schema level, witnessed by the atomic instance `Sp (.atom a) (.atom a)`. Refuting `TMCompleteBase` needs exactly one non-derivable BL-valid formula, so nothing is lost. Record the `⊤` observation in the new module's docstring so the universally quantified form is never re-attempted. |
| `autoImplicit` is on: an unimported name such as `TMCompleteBase` silently becomes an auto-bound implicit `Prop` variable, producing a type error that reads like a defeq failure | M | M (cost one debugging cycle in the prototype) | `SpCountermodel.lean` must `import FormalSystem.Metalogic.Conservativity.TMCompletenessReduction` explicitly (`SpWitness.lean` does not import it). Set `set_option autoImplicit false` in both new modules. |
| `h : TMCompleteBase` does not apply directly as a function (`have h' : … := h` fails) | L | Certain | `unfold TMCompleteBase TMComplete at h` first, as the prototype does. |
| `twoFibre` without `@[reducible]` causes `rw [BLFrameTruth.and_iff]` to fail on a transparency-level mismatch between `ℤ ⊕ ℝ → Atom → Prop` and `twoFibre.Point → Atom → Prop` | M | Certain if omitted | Mark `twoFibre` `@[reducible]`. Verified both ways in the prototype. |
| New `@[simp]` lemmas (`neg_iff`, `top_true`, `and_iff`, `or_iff`, `diamond_iff`, `someFuture_iff`, `somePast_iff`) enter the library-wide simp set once `BLFrame.lean` is wired into `Semantics.lean`, potentially perturbing unrelated proofs | M | L | Phase 1 closes on a full `lake build`, so any perturbation surfaces before 400 further lines are written. Fallback if it does: drop `@[simp]` and use the lemmas by name (the prototype's own proofs already `rw` them explicitly rather than relying on the attribute). |
| Repository gates: C3 (zero `sorry`), C2/C14 (`#print axioms` baselines and documented axiom/sorry counts in docstrings and READMEs), C16 `docBlame` (every declaration needs a docstring, including private helpers), C15 paper anchors, readme-lint (every `.lean` listed in its directory README) | H | M | Phase 4 is reserved for exactly this and closes on `bash scripts/check-module-invariants.sh` plus `bash scripts/readme-lint.sh`. Note `tmCompleteZTime_refuted` is **not** in the C14 baseline today, so a baseline addition is expected to be unnecessary — but this is a hypothesis to confirm, not an assumption (see Phase 4's Scope Hypothesis). |
| Import-cycle discipline: children of `Metalogic/Conservativity.lean` must never import the aggregator | H | L | `SpCountermodel.lean` imports `Conservativity/SpWitness.lean`, `Conservativity/TMCompletenessReduction.lean` and `Semantics/BLFrame.lean` directly, and is added to the aggregator's import list and module table exactly as `Z1Countermodel.lean` is. Confirm with `bash scripts/check-metalogic-cycles.sh`. |
| G-15 layering: `Semantics/` must not reach the proof system | M | L | `Semantics/BLFrame.lean` carries the same `assert_not_exists FormalSystem.ProofSystem.Axiom …` guard `Semantics/BLTruth.lean` carries, and imports only `BaseLanguage.Formula` plus Mathlib order. All `ProofSystem` contact (`FrameClass`, `Axiom`, `DerivationTree`) lives in `Metalogic/Conservativity/SpCountermodel.lean`. |
| Full `lake build` is slow (hundreds of modules) | L | Certain | Use `lake env lean <single file>` against the existing olean cache during development — this is what verified the prototype in seconds. Reserve full builds for phase-close gates, and run them detached per `context/project/lean4/operations/long-builds.md`. |
| `push_neg` is deprecated in this toolchain | L | Certain | Use `push Not`, as the prototype does. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 4 | 3 |

Phases within the same wave can execute in parallel. This plan is fully sequential: Phase 2
needs `BLFrame`/`BLFrameTruth` to exist, Phase 3 extends the same module Phase 2 creates and
consumes its soundness theorem, and Phase 4 documents theorem names that must already exist.

---

### Phase 1: Native BL frame and truth (`Semantics/BLFrame.lean`) [COMPLETED]

**Goal**: A `TaskFrame`-free frame notion, a native truth recursion over it, the characterization
lemma family, the swap-transfer lemma, and the validity notion — wired into the `Semantics`
aggregator and green on a full build.

**Tasks**:
- [x] Create `FormalSystem/Semantics/BLFrame.lean` with the standard copyright header, `import FormalSystem.BaseLanguage.Formula` plus the Mathlib order imports only, the `assert_not_exists FormalSystem.ProofSystem.Axiom FormalSystem.ProofSystem.DerivationTree FormalSystem.ProofSystem.Derivable FormalSystem.ProofSystem.FrameClass` G-15 guard copied from `Semantics/BLTruth.lean`, and `set_option autoImplicit false`.
- [x] Write the module docstring: what a `BLFrame` is, why it exists (`BLTruthAt` is `TaskFrame`-bound through `Duration : TemporalOrder`, and that group hypothesis is exactly what `DurationClassification.duration_dense_or_least_pos` consumes to make `blValid_sp` go through, so a native recursion is mandatory rather than a reindexing); that `□` is the universal modality over `Point` and why that is the cheapest condition making MF sound; and the contrast that in the task-frame semantics MF is underwritten instead by shift-closure of `H_F` plus `Duration` being a group — a different route to the same axiom, which is a feature, since underivability needs only *some* class on which TM is sound.
- [x] Declare `structure BLFrame` in `namespace FormalSystem.Semantics`: fields `Point : Type`, `[pointNonempty : Nonempty Point]`, `lt`, `lt_trans`, `lt_irrefl`, `no_max`, `no_min`, `fut_lin`, `past_lin`. Add `attribute [instance] BLFrame.pointNonempty`.
- [x] Add the private `triRotate` trichotomy-rotation helper (with a docstring — C16 `docBlame` covers private declarations).
- [x] Define `BLFrame.swap`, reversing `lt` and cross-wiring `no_max`/`no_min` and `fut_lin`/`past_lin`. Document that `no_min` and `past_lin` are fields precisely so the class is converse-closed, which is what makes the TD route in Phase 2 available.
- [x] Define `BLFrameTruth` by recursion on `BLFormula`'s six constructors, and `BLFrameValid`.
- [x] Add the `BLFrameTruth` namespace characterization lemmas mirroring `BLTruth.*` one for one: `imp_iff`, `box_iff`, `past_iff`, `future_iff`, `neg_iff`, `top_true`, `and_iff`, `or_iff`, `diamond_iff`, `someFuture_iff`, `somePast_iff`. Use `push Not` (not the deprecated `push_neg`) in the three existential cases. *(deviation: altered — Scope Hypothesis confirmed the enumerated 11 is short of `BLTruth`'s actual 13; `bot_false` and `always_iff` were added so the mirror really is one for one)*
- [x] Prove `truth_swap` by `induction φ generalizing w` — six cases, `Iff.rfl` / `imp_congr` / `forall_congr'`.
- [x] Add `import FormalSystem.Semantics.BLFrame` to `FormalSystem/Semantics.lean` (place it adjacent to the `BLTruth` import) and add a `- BLFrame:` submodule bullet to that file's `## Submodules` docstring list.
- [x] Add a `BLFrame.lean` row to `FormalSystem/Semantics/README.md` (readme-lint check 2) and refresh its "Last verified" date (check 4).
- [x] Verify: `lake env lean FormalSystem/Semantics/BLFrame.lean` clean, then a full `lake build`.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts (a) ~230 lines and (b) an eleven-lemma
characterization family mirroring `BLTruth.*` "one for one". Confirm at implementation time by
`grep -c '' FormalSystem/Semantics/BLFrame.lean` and by diffing the declared lemma names against
`grep -n 'theorem' FormalSystem/Semantics/BLTruth.lean`'s `BLTruth` namespace — if `BLTruth`
carries a lemma with no `BLFrameTruth` counterpart, either add it or record why it does not
apply. Neither number is a fact until confirmed.

**Files to modify**:
- `FormalSystem/Semantics/BLFrame.lean` - NEW; the whole native frame/truth layer
- `FormalSystem/Semantics.lean` - add one import and one `## Submodules` bullet
- `FormalSystem/Semantics/README.md` - add the file row, refresh "Last verified"

**Verification**:
- `lake env lean FormalSystem/Semantics/BLFrame.lean` reports no errors, no `sorry`, no warnings
- `lake build` green (this is where any global `@[simp]`-set perturbation surfaces)
- `bash scripts/readme-lint.sh FormalSystem` reports no new finding
- No `FormalSystem.ProofSystem.*` name reachable from the new module (the `assert_not_exists` guard elaborates)

---

### Phase 2: Native BL soundness (`Conservativity/SpCountermodel.lean`, part 1) [COMPLETED]

**Goal**: Every TM axiom schema admissible at `FrameClass.Base` verified directly against
`BLFrameValid`, and native soundness proved by recursion on `BaseLanguage.DerivationTree`.

**Tasks**:
- [x] Create `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` with the copyright header, `set_option autoImplicit false`, `namespace FormalSystem.Metalogic`, and imports `FormalSystem.Metalogic.Conservativity.SpWitness`, `FormalSystem.Metalogic.Conservativity.TMCompletenessReduction` (required explicitly — `SpWitness.lean` does not pull it in, and without it `TMCompleteBase` silently auto-binds), and `FormalSystem.Semantics.BLFrame`. Open `FormalSystem.Syntax`, `FormalSystem.BaseLanguage`, `FormalSystem.ProofSystem`, `FormalSystem.Semantics`. Do **not** import the `Conservativity.lean` aggregator.
- [x] Write the module docstring: the deliverable, the sharpened order-theoretic impossibility argument (a `DF` instance can fail at `t` only if `t` has no immediate successor; a `DN` instance only if it does — so on any single linear order the two failures are mutually exclusive at a fixed time, regardless of valuation, history count, or group structure), and the consequence that a CEB countermodel needs two order-shapes simultaneously `□`-accessible.
- [x] *(deviation: altered — `FormalSystem.Metalogic.axiom_valid` already exists in scope (`Metalogic/Soundness.lean`, about `Formula`), so `axiom_valid` and `blFrameValid_of_derivation` live in a nested `namespace SpCountermodel` inside `FormalSystem.Metalogic`. Short names and signatures are exactly as pinned in Lean Challenge Statements; only the qualification gained one segment. The two deliverable theorems `not_derivable_sp` / `tmCompleteBase_refuted` and `sp_false` sit at `FormalSystem.Metalogic.*`, mirroring `Z1Countermodel`.)* Prove `axiom_valid {φ} (ax : BaseLanguage.Axiom φ) (h_fc : ax.minFrameClass ≤ FrameClass.Base) : BLFrameValid φ` by `cases ax`, covering every constructor: the four propositional (`prop_k`, `prop_s`, `ex_falso`, `peirce`), the four modal (`modal_k`, `modal_t`, `modal_5`, `modal_future`), the five temporal (`temp_k`, `temp_4`, `temp_serial`, `temp_connect`, `temp_linearity`), and the three excluded by the side condition (`df`, `dn`, `co`, each `absurd h_fc (by decide)` against `FrameClass.ZTime`/`.Dense`/`.RTime` ≰ `.Base`).
- [x] `temp_linearity` is the longest branch: `rcases F.fut_lin` and select the matching disjunct in each of the three cases, using `and_iff`, `or_iff`, `someFuture_iff`.
- [x] Prove `blFrameValid_of_derivation {φ} (d : BaseLanguage.DerivationTree FrameClass.Base [] φ) : BLFrameValid φ` as a `match d with` recursion over all seven constructors (`axiom`, `assumption`, `modus_ponens`, `necessitation`, `temporal_necessitation`, `temporal_duality`, `weakening`), with `termination_by d.height` and the `decreasing_by` block copied verbatim from `BaseLanguageSoundness.lean`'s `bl_derivable_valid_and_swap_valid_zTimeSucc`. `temporal_duality` is one line via `truth_swap` at `F.swap`; `weakening` goes through `DerivationTree.ofWeakeningNil` and `height_ofWeakeningNil_lt`.
- [x] Docstring every declaration including private helpers (C16 `docBlame`).
- [x] Verify: `lake env lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` clean.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts a specific axiom census. The research report states
"15 constructors" in one place and enumerates 13 Base-admissible plus 3 excluded elsewhere;
counting `FormalSystem/BaseLanguage/Axioms.lean` directly gives **16** constructors — 13 whose
`minFrameClass` is `.Base` and 3 (`df`, `dn`, `co`) excluded by the side condition — and
`FormalSystem/BaseLanguage/Derivation.lean` gives **7** `DerivationTree` constructors. Confirm at
implementation time with `sed -n '/^inductive Axiom/,/^\/-!/p' FormalSystem/BaseLanguage/Axioms.lean | grep -cE '^\s*\| [a-z_]+'`
(subtracting the four `minFrameClass` match arms that pattern also catches) and by letting Lean's
exhaustiveness checker on `cases ax` / `match d with` be the real arbiter: a missing branch is a
compile error, so the census is confirmed by the build, not by the count. Also confirm the task
description's stale axiom list ("MK, MT, M5, MF, TD, TK, T4, TB, TA, TL") is not used as the
obligation: `TD` is a *rule* (`DerivationTree.temporal_duality`), `TB`/`TA` are the pre-rename
names of `TS`/`TC` (`Axiom.temp_serial`, `Axiom.temp_connect`), and the four propositional axioms
are omitted from it but must be verified.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` - NEW; `axiom_valid` and `blFrameValid_of_derivation`

**Verification**:
- `lake env lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` reports no errors and no `sorry`
- `cases ax` and `match d with` are exhaustive (Lean errors otherwise), confirming the census
- No `sorry`, no new `axiom`, no `@[nolint]` added

---

### Phase 3: The two-fibre countermodel and the headline results [COMPLETED]

**Goal**: The concrete `ℤ ⊕ ℝ` frame, its valuation, the two disjunct refutations, and the two
deliverable theorems — with their axiom profiles confirmed.

**Tasks**:
- [x] Add the private trichotomy helpers `sum_tri` / `sum_tri'` over `ℤ ⊕ ℝ` (`rintro … <;> simp_all <;> exact lt_trichotomy _ _`; the cross-fibre cases die by `simp_all` on Mathlib's `Sum` order `@[simp]` set), with docstrings.
- [x] Define `@[reducible] def twoFibre : BLFrame` over `ℤ ⊕ ℝ` with `lt := (· < ·)`, discharging `no_max`/`no_min` by `rintro (n | x)` and `n ± 1` / `x ± 1`, and `fut_lin`/`past_lin` from the helpers. Document why `@[reducible]` is load-bearing (without it `rw [BLFrameTruth.and_iff]` fails on a transparency-level mismatch) and why the *disjoint* sum is required where the task description's *lexicographic* `ℤ + ℚ` is not (a lexicographic sum is a single linear order; `ℝ` over `ℚ` only because `linarith` is frictionless there).
- [x] Define `twoV : (ℤ ⊕ ℝ) → Atom → Prop` as `inl n ↦ n ≠ 1`, `inr r ↦ r ≤ 0` (atom-independent), with a docstring.
- [x] Add the two `@[simp]` bridges `twoFibre_lt` and `twoFibre_atom`.
- [x] Prove `df_fails (a : Atom)`: the `DF` instance is false at `inr 0` on the `ℝ`-fibre — `H p ∧ p ∧ F⊤` holds there while `F(H p)` fails, the witness contradiction closing by `linarith` on `r / 2`.
- [x] Prove `dn_fails (a : Atom)`: the `DN` instance is false at `inl 0` on the `ℤ`-fibre — `GG p` holds while `G p` fails at `inl 1`, closing by `omega`.
- [x] Prove `sp_false (a : Atom) (w : ℤ ⊕ ℝ) : ¬ BLFrameTruth twoFibre twoV w (Sp (.atom a) (.atom a))` by unfolding `Sp`, `or_iff`, `box_iff` twice and feeding the two failures. Record in its docstring that a *single* atom suffices for both disjuncts, so no second atom is introduced.
- [x] Prove `not_derivable_sp (a : Atom) : ¬ BaseLanguage.Derivable FrameClass.Base [] (Sp (.atom a) (.atom a))` by `rintro ⟨d⟩` and composing `blFrameValid_of_derivation` with `sp_false`.
- [x] Prove `tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase` — `unfold TMCompleteBase TMComplete at h` first (direct application fails), then `not_derivable_sp a (h _ (blValid_sp _ _))`. Mirror `Z1Countermodel.tmCompleteZTime_refuted`'s statement shape exactly.
- [x] Add a docstring note on `sp_false` or `not_derivable_sp` recording that the *universally quantified* form ("no instance of `(Sp)` is a theorem") is **false**: `DF ⊤` is true at every point of every `BLFrame` (from `no_max`), so `□(DF ⊤)` holds and `Sp ⊤ ψ` is not refuted here. The claim is schema-level, witnessed by the atomic instance.
- [x] Confirm axiom profiles: `#print axioms` for `not_derivable_sp`, `tmCompleteBase_refuted` and `blFrameValid_of_derivation` all report `[propext, Classical.choice, Quot.sound]`. Remove the `#print axioms` lines before committing if the repository convention forbids them in live modules; otherwise keep them where `Z1Countermodel.lean` keeps its own. *(confirmed: all three report exactly that profile, verified in a scratch file; `Z1Countermodel.lean` carries no `#print axioms`, so the live module carries none either. `Semantics.truth_swap` is axiom-free.)*
- [x] Verify: `lake env lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` clean.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts (a) ~180 further lines and (b) that the three
`#print axioms` outputs are exactly `[propext, Classical.choice, Quot.sound]`. Confirm (b) by
running it — the prototype already did, so a divergence means the promotion introduced something
the prototype did not have, and is a stop-and-diff signal, not a new baseline. Confirm (a) by
`grep -c ''` on the module. Also confirm the `#print axioms`-in-live-module convention by
`grep -n '#print axioms' FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean` rather than
assuming either way.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` - append the countermodel, the evaluation, and the two headline theorems

**Verification**:
- `lake env lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` reports no errors and no `sorry`
- The three `#print axioms` outputs match `[propext, Classical.choice, Quot.sound]`
- `tmCompleteBase_refuted`'s statement is the negation `¬ TMCompleteBase` — grep the module to confirm no theorem in it concludes `TMCompleteBase`, `ForwardBase` or `forward` positively

---

### Phase 4: Wiring, record correction, and the full gate [NOT STARTED]

**Goal**: The new module is reachable from the aggregator, every repository record that says this
result is not machine-checkable is corrected, and the complete gate set is green.

**Tasks**:
- [ ] Add `import FormalSystem.Metalogic.Conservativity.SpCountermodel` to `FormalSystem/Metalogic/Conservativity.lean` (alongside the `Z1Countermodel` import) and add its row to that file's module table (`| Conservativity/SpCountermodel.lean | not_derivable_sp and tmCompleteBase_refuted |`).
- [ ] Update the aggregator's dependency-chain sentence (currently `Backward ← BaseLanguageSoundness ← TMCompletenessReduction ← Z1Countermodel ← Fragment ← FragmentCompactness ← Star/Forward`, with `SpWitness` hanging off `BaseLanguageSoundness`) to place `SpCountermodel` correctly.
- [ ] Rewrite the aggregator's `## CEB / FrameClass.Base` section: it currently says the TM half is "not machine-checkable here" and describes what a refutation *would* need. It now IS machine-checked; state the result, name `not_derivable_sp`/`tmCompleteBase_refuted`, and keep the two-fibre description (which the implementation vindicates) as the *explanation* rather than a wish list.
- [ ] Rewrite the aggregator's later "**CEB (`FrameClass.Base`) — still not machine-checkable in this tree, and not close**" bullet to record the landed result. Preserve the correct surrounding claim that TM^+ is unsound on the two-fibre class — the native soundness theorem is about TM (`BaseLanguage.DerivationTree`), not TM^+, and the docstring must not blur the two.
- [ ] Update `FormalSystem/Metalogic/Conservativity/SpWitness.lean`'s "What this does **not** do" section: the CEB half it disclaims is now discharged in `SpCountermodel.lean`; point there.
- [ ] Add the `SpCountermodel.lean` row to `FormalSystem/Metalogic/Conservativity/README.md` and refresh its "Last verified" date. (Note the existing `Z1Countermodel.lean` row carries a `<!-- TODO: add description -->` placeholder; do not propagate that pattern to the new row.)
- [ ] Check and update, where they assert the CEB status: `FormalSystem/Metalogic/README.md`, `FormalSystem/README.md`, `README.md` (its conservativity table row currently reads "refuted at Base/ZTime … `tmCompleteZTime_refuted`"), and `docs/theorem-index.md`. Each row touched must carry its paper anchor or the literal `Paper: —` plus a reason (C15).
- [ ] Run `bash scripts/check-metalogic-cycles.sh` to confirm no import cycle was introduced.
- [ ] Run the full gate: `lake build`, then `bash scripts/check-module-invariants.sh`, then `bash scripts/readme-lint.sh FormalSystem`. Fix every finding attributable to this task; do not re-baseline C2/C14 to accommodate a divergence.
- [ ] Confirm zero task-number citations were introduced under `FormalSystem/`, `scripts/`, `docs/` or `README.md` (C9/C9D) — cite `SpCountermodel.lean` and theorem names, never a task number.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts an enumerated file list for the record correction and
asserts that **no C2/C14 axiom-baseline addition is required**. The baseline hypothesis rests on
`tmCompleteZTime_refuted` not appearing in either baseline today (confirmed by grep over
`scripts/check-module-invariants.sh`), so its `.Base` mirror should not need one either — but
C14 additionally pins "every subject of a SORRY-FREE claim in `Metalogic.lean`" and C21 requires
every declaration named in `FormalSystem/MainResults.lean` to be pinned, so **if** Phase 4 adds a
SORRY-FREE claim or a MainResults entry naming the new theorems, a baseline row becomes
mandatory. Confirm by running `bash scripts/check-module-invariants.sh` and reading C14/C21's
own verdict rather than predicting it. The file list is likewise a hypothesis: confirm by
`grep -rln "not machine-checkable\|not close" --include=*.lean --include=*.md . | grep -v specs/`
and treating every hit in live scope as in-scope for this phase.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity.lean` - import, module table, dependency chain, both CEB status passages
- `FormalSystem/Metalogic/Conservativity/SpWitness.lean` - "What this does not do" section
- `FormalSystem/Metalogic/Conservativity/README.md` - new file row, "Last verified"
- `FormalSystem/Metalogic/README.md` - CEB status, if asserted there
- `FormalSystem/README.md`, `README.md` - conservativity status rows, if asserted there
- `docs/theorem-index.md` - rows for the new headline theorems
- `scripts/check-module-invariants.sh` - C2/C14 baseline rows only if the gate demands them

**Verification**:
- `lake build` green
- `bash scripts/check-module-invariants.sh` exits 0 (C1, C2, C3, C4, C5, C14, C15, C16, C21, C22, C23 all pass; no new nolint entry)
- `bash scripts/readme-lint.sh FormalSystem` reports no new finding
- `bash scripts/check-metalogic-cycles.sh` clean
- `grep -rn "not machine-checkable" FormalSystem/ docs/ README.md` returns no stale CEB claim

---

## Lean Challenge Statements

```lean
import FormalSystem.Metalogic.Conservativity.TMCompletenessReduction
import FormalSystem.Metalogic.Conservativity.SpWitness

open FormalSystem FormalSystem.Syntax FormalSystem.BaseLanguage FormalSystem.ProofSystem

namespace FormalSystem.Semantics

structure BLFrame where
  Point : Type
  [pointNonempty : Nonempty Point]
  lt : Point → Point → Prop
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  lt_irrefl : ∀ a, ¬ lt a a
  no_max : ∀ a, ∃ b, lt a b
  no_min : ∀ a, ∃ b, lt b a
  fut_lin : ∀ {a b c}, lt a b → lt a c → lt b c ∨ b = c ∨ lt c b
  past_lin : ∀ {a b c}, lt b a → lt c a → lt b c ∨ b = c ∨ lt c b

attribute [instance] BLFrame.pointNonempty

def BLFrame.swap (F : BLFrame) : BLFrame := sorry

def BLFrameTruth (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) :
    BLFormula → Prop := sorry

def BLFrameValid (φ : BLFormula) : Prop := sorry

theorem truth_swap (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) (φ : BLFormula) :
    BLFrameTruth F.swap V w φ ↔ BLFrameTruth F V w φ.swapBL := sorry

end FormalSystem.Semantics

namespace FormalSystem.Metalogic

open FormalSystem.Semantics

theorem axiom_valid {φ : BLFormula} (ax : BaseLanguage.Axiom φ)
    (h_fc : ax.minFrameClass ≤ FrameClass.Base) : BLFrameValid φ := sorry

theorem blFrameValid_of_derivation {φ : BLFormula}
    (d : BaseLanguage.DerivationTree FrameClass.Base [] φ) : BLFrameValid φ := sorry

@[reducible] def twoFibre : BLFrame := sorry

def twoV : (ℤ ⊕ ℝ) → Atom → Prop := sorry

theorem sp_false (a : Atom) (w : twoFibre.Point) :
    ¬ BLFrameTruth twoFibre twoV w (Sp (BLFormula.atom a) (BLFormula.atom a)) := sorry

theorem not_derivable_sp (a : Atom) :
    ¬ BaseLanguage.Derivable FrameClass.Base [] (Sp (BLFormula.atom a) (BLFormula.atom a)) :=
  sorry

theorem tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase := sorry

end FormalSystem.Metalogic
```

Note on `sp_false` and `twoV`: the prototype states `sp_false` at `w : ℤ ⊕ ℝ` and `twoV` at
`(ℤ ⊕ ℝ) → Atom → Prop`, which type-check against `twoFibre.Point` only because `twoFibre`
carries `@[reducible]`. The block above writes `twoFibre.Point` in `sp_false` for statement
clarity; either surface form is acceptable in the landed module provided `@[reducible]` is
present.

## Testing & Validation

- [ ] `lake env lean FormalSystem/Semantics/BLFrame.lean` — no errors, no `sorry`, no warnings
- [ ] `lake env lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` — same
- [ ] `lake build` green after each of Phases 1 and 4
- [ ] `#print axioms FormalSystem.Metalogic.not_derivable_sp` = `[propext, Classical.choice, Quot.sound]`
- [ ] `#print axioms FormalSystem.Metalogic.tmCompleteBase_refuted` = `[propext, Classical.choice, Quot.sound]`
- [ ] `#print axioms FormalSystem.Metalogic.blFrameValid_of_derivation` = `[propext, Classical.choice, Quot.sound]`
- [ ] `bash scripts/check-module-invariants.sh` exits 0 (C3 zero-sorry in particular)
- [ ] `bash scripts/readme-lint.sh FormalSystem` — no new finding
- [ ] `bash scripts/check-metalogic-cycles.sh` — no cycle
- [ ] No theorem anywhere in the new modules concludes `TMCompleteBase`, `ForwardBase` or `forward` positively; only their negations appear
- [ ] `grep -rn "sorry" FormalSystem/Semantics/BLFrame.lean FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` returns nothing

## Artifacts & Outputs

- `FormalSystem/Semantics/BLFrame.lean` (new, ~230 lines) — `BLFrame`, `BLFrame.swap`, `BLFrameTruth`, the `BLFrameTruth.*` characterization family, `truth_swap`, `BLFrameValid`
- `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` (new, ~380 lines) — `axiom_valid`, `blFrameValid_of_derivation`, `twoFibre`, `twoV`, `df_fails`, `dn_fails`, `sp_false`, `not_derivable_sp`, `tmCompleteBase_refuted`
- Edits to `FormalSystem/Semantics.lean`, `FormalSystem/Semantics/README.md`, `FormalSystem/Metalogic/Conservativity.lean`, `FormalSystem/Metalogic/Conservativity/SpWitness.lean`, `FormalSystem/Metalogic/Conservativity/README.md`, and the status rows in `FormalSystem/Metalogic/README.md`, `FormalSystem/README.md`, `README.md`, `docs/theorem-index.md`
- `specs/544_machine_check_sp_underivable_native_bl_soundness/summaries/01_*-summary.md` at completion

## Rollback/Contingency

Every phase is additive and confined to two new files plus documentation edits, so rollback is
`git revert` of the phase commits — no existing declaration is renamed, retyped, or deleted, and
nothing in the `TaskFrame`-bound semantic stack is touched.

Targeted contingencies:

- **If the new `@[simp]` lemmas perturb unrelated proofs** (surfaces at Phase 1's full build):
  drop the `@[simp]` attributes and use the lemmas by name. The prototype's proofs already `rw`
  them explicitly, so nothing downstream in this task depends on the attribute.
- **If the frame class turns out not to be converse-closed** under some later change: fall back
  to the swap-strengthened simultaneous induction of
  `BaseLanguageSoundness.lean`'s `bl_derivable_valid_and_swap_valid_zTimeSucc` for the TD case,
  which is the route the task description originally prescribed.
- **If a repository gate demands a change this task cannot satisfy honestly** (a C2/C14 axiom
  divergence in particular): stop and report rather than re-baselining. An axiom-set divergence
  from the prototype's confirmed `[propext, Classical.choice, Quot.sound]` means the promotion
  introduced something the prototype did not have, and is a hard stop.
- **Under no circumstance** discharge a forward-conservativity statement with `sorry` to make a
  gate pass; forward conservativity is refuted, not open.
