# Implementation Summary: Task #544

- **Task**: 544 - Machine-check the failing half of CEB: `(Sp)` is not a theorem of TM, via a native BL frame notion and native BL soundness
- **Status**: [COMPLETED]
- **Started**: 2026-09-07T23:18:00Z
- **Completed**: 2026-09-07T23:55:00Z
- **Effort**: ~40 minutes
- **Dependencies**: None (all prerequisites were in-tree and built)
- **Artifacts**: plans/01_sp-underivable-native-bl-soundness.md
- **Standards**: summary-format.md, status-markers.md, artifact-management.md, tasks.md

## Overview

The one claim in the paper's TM⁻ fragment discussion recorded as *not verified* — that the boxed
dichotomy `(Sp) := □(DF φ) ∨ □(DN ψ)` is BL-valid on every task frame yet **not** derivable in
TM — is now machine-checked. Because `(Sp)` is valid on the whole task-frame class, no
`TaskFrame`-bound refutation can exist; the work therefore adds a native, `TaskFrame`-free frame
notion, proves BL soundness for TM directly against it, and refutes the atomic instance on the
disjoint sum `ℤ ⊕ ℝ`. The corollary `tmCompleteBase_refuted : ¬ TMCompleteBase` closes the last
outstanding row of the CEB analysis, mirroring `Z1Countermodel.tmCompleteZTime_refuted` at
`.Base`.

## What Changed

- `FormalSystem/Semantics/BLFrame.lean` — NEW (309 lines). `BLFrame` (a nonempty point set with
  an unbounded, transitive, irreflexive, forward- and backward-linear strict order and **no**
  group structure), `BLFrame.swap`, the truth recursion `BLFrameTruth` with `□` read as the
  universal modality over the points, `BLFrameValid`, the 13-lemma `BLFrameTruth.*`
  characterization family mirroring `BLTruth.*` one for one, and the order-reversal transfer
  lemma `truth_swap` (axiom-free).
- `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean` — NEW (390 lines).
  `blFrameValid_of_axiom` (all 16 `BaseLanguage.Axiom` constructors: 13 Base-admissible verified,
  3 excluded by the side condition), `blFrameValid_of_derivation` (native BL soundness, recursion
  over all 7 `DerivationTree` constructors, `temporal_duality` closed in one line by
  `truth_swap`), the countermodel `twoFibre : ℤ ⊕ ℝ` and its valuation `twoV`, `df_fails` /
  `dn_fails`, `sp_false`, and the two deliverables `not_derivable_sp` and
  `tmCompleteBase_refuted`.
- `FormalSystem/Semantics.lean` — import plus a `## Submodules` bullet for `BLFrame`.
- `FormalSystem/Semantics/README.md` — hand-maintained inventory row for `BLFrame.lean`.
- `FormalSystem/Metalogic/Conservativity.lean` — import; module-table row; dependency-chain
  sentence; the `## CEB / FrameClass.Base` section heading and body rewritten from "TM half not
  machine-checkable here" to the landed result; the later "still not machine-checkable in this
  tree, and not close" bullet rewritten to "done, both halves machine-checked".
- `FormalSystem/Metalogic/Conservativity/SpWitness.lean` — "What this does **not** do" now points
  at `SpCountermodel.lean` for the half it disclaims; a reference row added.
- `FormalSystem/Metalogic/Conservativity/README.md` — status-table row now records both `.Base`
  and `.ZTime` as machine-checked; two Key Results bullets; generated inventory row with a
  hand-written description.
- `README.md`, `docs/theorem-index.md` — the single CEB-status assertion in each now names
  `tmCompleteBase_refuted`; generated count blocks refreshed.
- `FormalSystem/Metalogic/README.md`, `FormalSystem/README.md` — generated count blocks only.

## Decisions

- **`□` is the universal modality over `BLFrame.Point`.** The cheapest condition making MF
  (`□φ → □Gφ`) sound. The task-frame semantics reaches MF by a different route (shift-closure of
  `H_F` plus `Duration` being a group); both module docstrings record that this is two sufficient
  conditions for one axiom, not a discrepancy, since underivability needs only *some* class on
  which TM is sound.
- **TD discharged by swap *transfer*, not swap-strengthened induction.** `no_min` and `past_lin`
  are `BLFrame` fields precisely so the class is converse-closed, which makes `truth_swap`
  available and closes `temporal_duality` in one line.
- **The countermodel is the *disjoint* sum `ℤ ⊕ ℝ`, not the lexicographic `ℤ + ℚ`.** The
  sharpened impossibility argument (recorded in the module docstring) shows a `DF` instance can
  fail only where there is no immediate successor and a `DN` instance only where there is one, so
  no single linear order — lexicographic sums included — can refute both disjuncts at a fixed
  time.
- **The claim is schema-level.** The universally quantified reading is *false*: `□(DF ⊤)` holds
  on every `BLFrame`, so `Sp ⊤ ψ` is not refuted. Recorded in three docstrings so it is never
  re-attempted.
- **`@[reducible]` on `twoFibre` is load-bearing**, not decoration; without it
  `rw [BLFrameTruth.and_iff]` fails on a transparency mismatch.
- **No `#print axioms` in the live modules**, matching `Z1Countermodel.lean`'s own convention
  (confirmed by grep, not assumed).
- **No C2/C14 baseline addition and no new `docs/theorem-index.md` row**, mirroring
  `tmCompleteZTime_refuted`'s own absence from that ledger. C14 and C21 both pass.

## Plan Deviations

- **`axiom_valid` landed as `blFrameValid_of_axiom`** — same signature, same namespace, different
  base name. This is the only divergence from the plan's `## Lean Challenge Statements` block, and
  it is forced twice over: `FormalSystem.Metalogic.axiom_valid` already exists
  (`Metalogic/Soundness.lean:1345`, the BL⁺ lemma about `Formula`), so the pinned name is a
  duplicate-declaration error in that namespace; and the first fix attempted — nesting a
  `namespace SpCountermodel` — was **rejected by repository invariant C23** (`outer-shadows-inner
  bare-declaration pair`, because C17's dead-declaration census keys on the last dot-segment).
  Renaming was the only route satisfying both the compiler and the gates. The plan's Challenge
  block was annotated with this divergence rather than rewritten to match the implementation.
  Every other pinned identifier landed at its pinned name, namespace and signature.
- **Phase 1 characterization family widened from 11 lemmas to 13** — the phase's own Scope
  Hypothesis directed a diff against `BLTruth`'s namespace, which showed `bot_false` and
  `always_iff` were missing from the plan's enumeration. Added so the mirror is genuinely
  one-for-one.
- **Phase 4's Conservativity README row was generated, not hand-added** — that table is
  machine-owned (`<!-- BEGIN GENERATED: inventory -->`), so the row came from
  `--emit-inventory` and only its description column was authored by hand.
- Two Scope Hypotheses were confirmed rather than assumed: the axiom census (16 `Axiom` / 7
  `DerivationTree` constructors, arbitrated by Lean's exhaustiveness checker, matching the plan's
  count and refuting the task description's stale "MK, MT, M5, MF, TD, TK, T4, TB, TA, TL" list);
  and the record-correction file list (`FormalSystem/Metalogic/README.md` and
  `FormalSystem/README.md` turned out to assert no CEB status prose at all).

## Verification

- Build: Success — full `lake build` green, 2612 jobs, exit 0, real build (`--no-share`, no
  REPLAY marker), run detached through `.claude/scripts/lake-build-guard.sh`
- Sorry count: 0 in both new files; C3 reports the structural sorry inventory is ZERO across
  `FormalSystem/` (`Boneyard/` excluded, where the only hits live and are pre-existing)
- Vacuous count: 0
- Axiom count: 0 new `axiom` declarations
- Axiom profiles: `not_derivable_sp`, `tmCompleteBase_refuted`, `blFrameValid_of_derivation`,
  `blFrameValid_of_axiom` all `[propext, Classical.choice, Quot.sound]`; `Semantics.truth_swap`
  depends on no axioms at all
- `bash scripts/check-module-invariants.sh` — **ALL CHECKS PASSED**, exit 0 (C2, C3, C14, C15,
  C16, C21, C22, C23, INV inclusive)
- `bash scripts/readme-lint.sh FormalSystem` — RESULT: PASS, 0 broken references
- `bash scripts/check-metalogic-cycles.sh` — PASS, exactly the one pre-existing directory-level
  cycle; none introduced
- Forward-conservativity prohibition honoured: `tmCompleteBase_refuted` states only the negation
  `¬ TMCompleteBase`; no theorem in either new module concludes `TMCompleteBase`, `ForwardBase`
  or `forward` positively
- No task-number citations introduced under `FormalSystem/`, `docs/` or `README.md`
- Files verified: Yes

## Impacts

- CEB now joins CEF as a fully machine-checked row: forward proof-theoretic conservativity of
  TM⁺ over TM is refuted at `.Base` and `.ZTime` with a witness in-tree for each, and the
  repository no longer carries any record saying the `.Base` half is "not machine-checkable in
  this tree, and not close".
- `FormalSystem/Semantics/BLFrame.lean` is a reusable, `TaskFrame`-free semantic layer for BL,
  additive to and independent of the existing `BLTruthAt`/`bl_soundness` stack. Any future TM
  underivability result that needs a structure outside the task-frame class can now be stated
  against `BLFrameValid` and discharged through `blFrameValid_of_derivation`.
- The paper's `possible_worlds.tex` footnote (`sub:Logic`, TM⁻ paragraph) can now cite this
  repository for the claim it currently states as unverified.

## Follow-ups

- Editing `possible_worlds.tex` to cite `not_derivable_sp` is downstream work in another
  repository and was explicitly out of scope.
- Whether TM⁻_d and TM⁻_dc are complete over the dense and dense-and-complete classes remains a
  separate open question, untouched.
- `Z1Countermodel.lean`'s generated README row still carries a `<!-- TODO: add description -->`
  placeholder (pre-existing; the new row does not propagate the pattern).

## References

- `specs/544_machine_check_sp_underivable_native_bl_soundness/plans/01_sp-underivable-native-bl-soundness.md`
- `specs/544_machine_check_sp_underivable_native_bl_soundness/reports/01_sp-underivable-native-bl-soundness.md`
- `specs/544_machine_check_sp_underivable_native_bl_soundness/prototype/SpCountermodelPrototype.lean`
- `FormalSystem/Semantics/BLFrame.lean`, `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean`
