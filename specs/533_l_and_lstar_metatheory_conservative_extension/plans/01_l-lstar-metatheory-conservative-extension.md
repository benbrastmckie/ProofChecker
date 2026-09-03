# Implementation Plan: L and L⋆ metatheory and conservative extension over L⁺

- **Task**: 533 - l_and_lstar_metatheory_conservative_extension
- **Status**: [NOT STARTED]
- **Effort**: 32 hours (16 leaf phases, 8 dependency waves, ~3,300 lines of Lean)
- **Dependencies**: 535 (binding axiom set and corrections; satisfied — its report and probes are read below)
- **Research Inputs**:
  - `specs/533_l_and_lstar_metatheory_conservative_extension/reports/01_l-lstar-metatheory-conservative-extension.md` (architecture decision (b), TMFrag deliverable, the compiled Appendix A prototypes)
  - `specs/535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md` (BINDING: ⊡-axiom set, closed `StarAxiom`, TM⁺ schemata re-declared over `StarFormula`, atomization, semantic TD discharge)
  - `specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean` (632 lines, 60 declarations, compiles from disk sorry-free; the transcription source for Phases 3.1-3.4)
  - Task description scope amendment of 2026-09-03 (items (1)-(5)); where it conflicts with the 533 report, the amendment wins
- **Artifacts**: plans/01_l-lstar-metatheory-conservative-extension.md (this file)
- **Standards**:
  - .claude/context/formats/plan-format.md
  - .claude/context/standards/status-markers.md
  - .claude/rules/artifact-formats.md
  - .claude/rules/state-management.md
  - .claude/context/contracts/reference-grounding.md (H3, Lean4 Tier 1 override)
  - .claude/rules/no-task-references-in-deliverables.md
  - `scripts/check-module-invariants.sh` (C1-C15; C3 zero `sorry`, C8 aggregator convention, C9 no task numbers under `FormalSystem/`, C14 documented counts)
- **Type**: lean4
- **Mode**: hard (`--hard --fable`); reference tier: **Tier 1** (literature-backed: JPL paper + 535 probes)

## Overview

Deliver the metatheory the scope amendment fixes for the two extension directions of the landed
L⁺ tree. For **L ⊂ L⁺** (via `tr`): semantic conservativity is already landed
(`blValidIn_iff_validIn_tr`, `Metalogic/Conservativity/BaseLanguageSoundness.lean:177`); this
plan adds the H/G-fragment logic `TMFrag fc φ := Derivable fc [] (tr φ)` with transferred
soundness, completeness at all four classes, Base/Dense compactness, and the strict inclusion
`TM ⊊ TMFrag` at `.Discrete`. For **L⁺ ⊂ L⋆** (via a constructor-to-constructor embedding
`ofFormula`): a new syntax `StarFormula` (L⁺ plus the stability modal `⊡`, paper line 1114),
native semantics `StarTruthAt`/`SameStateAt`/`StarValidIn`, the closed proof system `StarAxiom`
built around exactly the 535 axiom set {SK, ST, S4, S5, MS, AS, PS, US} with the TM⁺ schemata
re-declared over `StarFormula`, soundness at all four classes (TM⁺ arm by atomization, TD by the
tree's companion recursion), semantic conservativity, and proof-theoretic conservativity of TM⋆
over TM⁺ in both directions — the forward direction from TM⋆ soundness plus the four existing
completeness engines, needing no TM⋆ completeness.

Definition of done: every phase's declarations land sorry-free under `FormalSystem/`, are
reachable from the `FormalSystem` root, `lake build` and `scripts/check-module-invariants.sh`
are green, no landed theorem is modified, and the four flagship statements
`tmFrag_iff_blValidIn`, `star_soundness_validIn`, `starDerivable_ofFormula_iff`, and
`tm_lt_tmFrag_discrete` `#print axioms` to the standard three.

### Research Integration

| Report | Integrated in plan version | Date |
|---|---|---|
| 533 `reports/01_l-lstar-metatheory-conservative-extension.md` | 1 | 2026-09-03 |
| 535 `reports/01_stability-modal-axiomatization.md` + `probes/01_stab-axiom-probes.lean` | 1 | 2026-09-03 |

Corrections applied to the 533 report per the amendment: the Phase 7 TM⋆ completeness spike is
removed (task 537); the Phase 8 L⋆ compactness (Łoś `stab` case) is dropped from scope (not an
amendment deliverable); `ofPlus` is a *function* `Axiom φ → StarAxiom (ofFormula φ)`, never the
TM⁺ part of `StarAxiom`; `⊡`-necessitation is a derived rule, not a constructor.

### Preserved Assets

No prior plan exists for this task. The landed work this plan builds on and must not regress:

| Component | File | Status | Verified |
|---|---|---|---|
| L syntax, TM axioms, derivations, `tr`, axiom discharge | `FormalSystem/BaseLanguage/{Formula,Axioms,Derivation,Translation,AxiomDischarge}.lean` (1,243 lines) | landed, sorry-free | 2026-09-03 (report §2; C3) |
| `BLTruthAt`, `BLValidIn` family | `FormalSystem/Semantics/{BLTruth,BLValidity}.lean` | landed | 2026-09-03 |
| `truthAt_tr`, `blValidIn_iff_validIn_tr`, `bl_soundness_*` | `Metalogic/Conservativity/BaseLanguageSoundness.lean:110,177,232-429` | landed | 2026-09-03 |
| `translate`, `derivable_translate`, `z1_translate` | `Metalogic/Conservativity/Backward.lean:64,88,188` | landed | 2026-09-03 |
| `TMComplete`, `Forward`, `tmComplete_iff_forward` | `Metalogic/Conservativity/TMCompletenessReduction.lean:94,102,125` | landed | 2026-09-03 |
| `not_bl_derivable_z1`, `tmCompleteDiscrete_refuted` | `Metalogic/Conservativity/Z1Countermodel.lean:175,199` | landed | 2026-09-03 |
| `completeness_base/dense/discrete/dedekind : WeakCompleteness fc` | `Metalogic/StrongCompleteness.lean:879/987/1101/775` | landed | 2026-09-03 |
| `compactBase`, `compactDense` | `Metalogic/Compactness.lean:183,186` | landed | 2026-09-03 |
| `axiom_validIn_min`, `axiom_swap_validIn_min`, `derivable_valid_and_swap_validIn`, `soundness_validIn` | `Metalogic/Soundness.lean:1141,1190,1217,1316` | landed | 2026-09-03 |
| `ProofSystem.Axiom` (documented constructor count 45), `DerivationTree` (7 rules) | `ProofSystem/Axioms.lean:111`, `ProofSystem/Derivation.lean:91` | landed; count pinned by C14 | 2026-09-03 |

### Source-to-implementation mapping (H3, Lean4 Tier 1, 5-column)

"JPL paper" = `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`.
"535 probes" = `specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean`
(all `compiled` rows there are the literal transcription source; the paper rows are the
mathematical anchor). Status `pending` = to be produced by the named phase.

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|---|---|---|---|---|
| JPL paper | line 1108, `⟨τ⟩_x := {σ ∈ H_F \| σ(x) = τ(x)}` | `Semantics.SameStateAt` (Phase 3.1) | `(τ σ : WorldHistory F) (t : F.Duration) : Prop` | pending (probes Part A compiled) |
| JPL paper | line 1114, `($\Stability$)` clause | `Semantics.StarTruthAt … (.stab φ)` (Phase 3.1) | `∀ σ, σ.IsTotal → SameStateAt τ σ t → StarTruthAt M σ t φ` | pending (compiled) |
| JPL paper | line 1118 footnote, "monomodal logic of ⊡ is S5" | `StarAxiom.stab_t/stab_4/stab_5` (4.1); `of_stab`, `stab_four`, `stab_five` (3.1) | T/4/5 instances; validity at total `τ` | pending (probes A2-A4 compiled) |
| JPL paper | line 1119 footnote, `φ → ⊡φ` non-temporal | `StarAxiom.atom_stab` (4.1); `stab_atom_of_atom` (3.1) | `StarAxiom ((.atom p).imp (.stab (.atom p)))` | pending (A5 compiled) |
| JPL paper | line 1108, `⟨τ⟩_x ⊆ H_F` | `StarAxiom.box_stab` (4.1); `stab_of_box` (3.1) | `StarAxiom ((.box φ).imp (.stab φ))` | pending (A1 compiled) |
| JPL paper | line 1121, `⟐φ := ¬⊡¬φ` | `StarFormula.dstab` (2); `dstab_iff` (3.1) | `dstab φ = neg (stab (neg φ))` | pending (compiled) |
| JPL paper | lines 1125-1129, `Will/will/Could/could` | `StarFormula.Will/will/Could/could` (2) | `Will := stab ∘ allFuture` etc. | pending |
| JPL paper | `def:frame` Compositionality + converse (`TaskFrame.lean:629-696`) | `paste`, `paste_rel`, `paste_isTotal` (3.3) | pasting of total histories at a shared state is total | pending (C0 compiled) |
| 535 probes | C2 `paste_valid` (PS) | `StarAxiom.paste` (4.1); `paste_valid` (3.3) | `IsPureFuture φ → IsPurePast ψ → StarAxiom ((dstab φ).imp ((dstab ψ).imp (dstab (conj φ ψ))))` | pending (compiled) |
| 535 probes | C5 `untl_dstab_valid` (US) | `StarAxiom.untl_paste` (4.1); `untl_dstab_valid` (3.3) | `IsPurePast α → IsPureFuture φ → StarAxiom ((.untl α (dstab φ)).imp (dstab (.untl α φ)))` | pending (compiled) |
| 535 probes | C3/C4 (FS/GS) | `future_dstab_valid`, `stab_allFuture_valid` (3.3) — theorems, not constructors | derived validities | pending (compiled) |
| 535 probes (mirror, UNVERIFIED there) | SS = TD-mirror of C5 | `snce_dstab_valid` (3.3); used by `starAxiom_swap_validIn_min` (5.3) | `IsPureFuture α → IsPurePast φ → StarValidIn fc ((.snce α (dstab φ)).imp (dstab (.snce α φ)))` | pending (mirror of a compiled proof) |
| 535 probes | B1, E1, E2 (`⊡φ` is a state formula) | `stab_congr_sameState`, `starTruthAt_timeShift`, `stab_state_only` (3.1) | E2: `τ.states t _ = σ.states s _ → (⊡φ at (τ,t) ↔ ⊡φ at (σ,s))` | pending (compiled) |
| 535 report §8.2 | atomization of TM⁺ schemata | `Encoding`, `atomize`, `TaskModel.atomModel`, `starTruthAt_iff_atomize` (5.1) | `StarTruthAt M τ t φ ↔ TruthAt (M.atomModel e) τ t (atomize e φ)` | pending |
| 535 probes | D1-D5 refutations (`natFrame` over ℤ) | `refute_stab_box`, `refute_allFuture_stab`, `refute_stab_allFuture_past`, `refute_determined`, `refute_somePast_stab` (3.4) | `¬ StarValid (…)` | pending (compiled) |
| JPL paper | line 1426 *Determined*, `app:non-deterministic` line 4130 | `refute_determined` (3.4) only | `¬ StarValid ((someFuture (.atom p)).imp (.stab (someFuture (.atom p))))` | pending; the deterministic half is NOT in scope and NO "exactly" claim is made (amendment (4)) |
| JPL paper | `def:BX` line 4110 (BX lists future halves; past halves by TD) | `star_derivable_valid_and_swap_validIn` (5.4) — companion recursion, mirror of `Soundness.lean:1217` | `StarDerivationTree fc [] φ → StarValidIn fc φ ∧ StarValidIn fc φ.swapTemporal` | pending |
| JPL paper | `def:BLplus-language` 3729-3752; `def:TMplus` 4656 | TM⁺ arms of `StarAxiom` (4.1), re-declared over `StarFormula` from `ProofSystem/Axioms.lean:111-464` | 45 constructors (Scope Hypothesis in 4.1) | pending |
| JPL paper | `cor:tm-completeness` 4668 | `forward_star` + four rows (6), via `completeness_{base,dense,discrete,dedekind}` | `WeakCompleteness fc → StarDerivable fc [] (ofFormula φ) → Derivable fc [] φ` | pending (`forward_star_of_sound` compiled in 533 Appendix A) |
| Burgess 1982 §1.3 (via `ProofSystem/Axioms.lean` docstrings) | BX axiom list | TM⁺ arms of `StarAxiom` | as above | pending |
| Repo | `blValidIn_iff_validIn_tr` (`BaseLanguageSoundness.lean:177`) | `tmFrag_sound`, `tmFrag_complete`, `tmFrag_iff_blValidIn` (1.1) | `TMFrag fc φ ↔ BLValidIn fc φ` given `WeakCompleteness fc` | pending |
| Repo | `z1_translate` (`Backward.lean:188`), `not_bl_derivable_z1` (`Z1Countermodel.lean:175`) | `tmFrag_z1_discrete`, `tm_lt_tmFrag_discrete` (1.1) | `TMFrag .Discrete (Z1 (.atom p)) ∧ ¬ BaseLanguage.Derivable .Discrete [] (Z1 (.atom p))` | pending |
| Repo | `compactBase`/`compactDense` (`Compactness.lean:183,186`); `Compact` (`SetConsequence.lean:197`) | `blCompactBase`, `blCompactDense` (1.2) | `BLCompact .Base`, `BLCompact .Dense` (consequence form, mirror of `Compact`) | pending |

### Literature Proof Structure

1. **Backward conservativity (both pairs)**: structural recursion on derivation trees with an
   axiom-discharge map. For L⁺ ⊂ L⋆ the discharge map is `StarAxiom.ofPlus` (constructor to
   re-declared twin, `rfl` per arm) — no `F/P` bridge as `AxiomDischarge.lean` needed for
   `tr`, because the embedding is constructor-to-constructor.
2. **Forward conservativity via semantics** (Venema 1993 §1 "completeness via completeness"):
   `⊢⋆ e(φ) ⇒ ⊨⋆ e(φ) ⇒ ⊨ φ ⇒ ⊢ φ` — TM⋆ soundness, truth transfer along `ofFormula`, TM⁺
   engine. Works for L⁺ ⊂ L⋆ (base complete); fails for L ⊂ L⁺ (TM incomplete,
   `tmComplete_iff_forward`), which is why the L side delivers `TMFrag` instead.
3. **⊡-axiom validities**: S5 from `∼_t` being an equivalence (paper 1118); PS/US from the
   pasting lemma (paper Compositionality + converse), with the purity side conditions.
4. **TM⁺ schemata over L⋆ by atomization** (535 §8.2): `⊡χ` is a state formula (E2), so
   replacing each `⊡χ` by a fresh state-valued atom turns any L⋆ instance of a TM⁺ schema into
   an L⁺ instance evaluated in a model on the same frame; the landed `axiom_validIn_min` /
   `axiom_swap_validIn_min` then discharge all 45 constructors, validity and swap-validity, at
   once.
5. **TD**: the tree discharges `temporal_duality` by the companion recursion
   `derivable_valid_and_swap_validIn` (`Soundness.lean:1217`, the TD arm swaps the pair) with
   per-constructor swap-validity (`Soundness.lean:1190`); `truthAt_of_truthAntiIso` is used
   only in `Metalogic/Independence/CoNotPriorU.lean:463`, never in soundness (verified by grep).
   The L⋆ mirror is the same companion recursion. This satisfies amendment (5)'s *semantic*
   requirement; a `StarFormula` `TruthAntiIso` twin is a contingency tool (Rollback section),
   not a critical-path deliverable.

### Design note: how task 537 extends `StarAxiom` without re-running this task's soundness

`StarAxiom` is a **closed** inductive (535 §8.1, SETTLED). Extension cost is bounded by
construction because exactly three declarations pattern-match on `StarAxiom` constructors:

1. `StarAxiom.minFrameClass` (Phase 4.1),
2. `starAxiom_validIn_min : (ax : StarAxiom φ) → StarValidIn ax.minFrameClass φ` (Phase 5.2),
3. `starAxiom_swap_validIn_min : (ax : StarAxiom φ) → StarValidIn ax.minFrameClass φ.swapTemporal` (Phase 5.3).

Everything downstream — `StarDerivationTree`, `ofPlus`, `star_derivable_valid_and_swap_validIn`,
`star_soundness_validIn`, `forward_star`, `starDerivable_ofFormula_iff`, atomization — refers to
`StarAxiom` only through `minFrameClass`, `starAxiom_validIn`, and `starAxiom_swap_validIn`
(the `ValidIn.mono`-lifted forms). Adding a constructor `c` therefore means: one constructor
line, one `minFrameClass` arm, one arm in each dispatch lemma; all other files recompile
unchanged. (`ofPlus` recurses on `ProofSystem.Axiom`, not on `StarAxiom`, so it is untouched.)

Two hooks are provided for 537's specific deliverables:
- **Frame-predicate validity primitive**: Phase 3.2 defines `StarValidOnFrames (P : TaskFrame →
  Prop)` as the primitive and `StarValidIn fc := StarValidOnFrames fc.Sat` (exactly the
  `BLValidity.lean:96-123` shape). 537's "TM⋆ + Determined over deterministic frames" can state
  validity over `{F | F.Deterministic} ∩ fc.Sat` without touching the semantics, and its
  soundness for the Determined schema is a `StarValidOnFrames` statement over that predicate —
  it must NOT be added to `StarAxiom` (it is refuted at `.Base`, `refute_determined`, so adding
  it would falsify `star_soundness_validIn`).
- **Rule set identical to TM⁺**: `StarDerivationTree` has the same seven rules as
  `ProofSystem.DerivationTree` (`axiom, assumption, modus_ponens, necessitation,
  temporal_necessitation, temporal_duality, weakening`); ⊡-necessitation is the derived theorem
  `stab_necessitation` (necessitation then `box_stab`). 537's canonical-model work therefore
  inherits the exact `DerivationTree` shape the four engines already consume.

### File territory (H7)

New directories: `FormalSystem/StarLanguage/` (syntax + proof system; imports nothing from
`FormalSystem.Semantics`, mirroring the `BaseLanguage/` invariant documented in
`BaseLanguage/Formula.lean:32`) and `FormalSystem/Metalogic/Conservativity/Star/`. New
`Semantics/Star*.lean` modules sit beside `BLTruth.lean`/`BLValidity.lean`. Because
`lakefile.lean` builds only modules reachable from the `FormalSystem` root (`roots :=
#[`FormalSystem]`), each phase builds its module explicitly (`lake build
FormalSystem.<Module>`) and aggregator wiring is owned by exactly one phase per aggregator file
(see the per-phase Territory lines; wave-parallel phases never share a file).

## Postmortem Constraints

Binding rules for all implementation dispatches. No prior implementation attempt exists; rules
derive from the tree's own machine-checked refutations, the amendment, and the 535 corrections.

**Do NOT**:
1. State, prove, or `sorry` `Forward fc` / any `Derivable fc [] (tr φ) → BaseLanguage.Derivable
   fc [] φ` shape (forward proof-theoretic conservativity of TM⁺ over TM). It is refuted at
   `.Discrete` (`tmCompleteDiscrete_refuted`, `Z1Countermodel.lean:199`), refuted-in-source at
   `.Base`, and equal to TM completeness by `tmComplete_iff_forward`; the standing prohibition
   in `Metalogic/Conservativity.lean`'s docstring stays in force. Deliver `TMFrag` instead.
2. Transcribe the claim that *Determined* (`φ → ⊡φ`) is valid *exactly* over deterministic
   frames (amendment (4), paper line 1437). This task lands only the refutation over a
   non-deterministic frame (`refute_determined`); the deterministic half and its converse belong
   to tasks 536/537. No docstring may say "exactly", "iff", or "characterizes".
3. Build the TM⁺ part of `StarAxiom` as an `ofPlus : Axiom φ → StarAxiom (ofFormula φ)`
   constructor. It yields only ⊡-free instances; `□⊡p → □G⊡p` (MF at `⊡p`) would be
   underivable (535 §8.2). The 45 schemata are re-declared with `StarFormula` parameters;
   `ofPlus` is a *function* used only for backward conservativity.
4. Attempt TM⋆ completeness at any class, a canonical model on ⊡-classes of MCSs, the Lifting
   Lemma, the bundled semantics, or deterministic-class completeness — all task 537 (amendment
   (2); 535 §4, §7.3, §8.4).
5. Discharge `temporal_duality` proof-theoretically (mapping derivations to mirrored
   derivations). The BX axiom set is not mirror-closed (paper `def:BX` line 4110;
   `Soundness.lean:1027`), so that route is circular. Use the companion recursion with
   per-constructor swap-validity (Literature Proof Structure item 5).
6. Re-prove the 45 TM⁺ schemata over `StarTruthAt` axiom by axiom (~1,500 lines). Use
   atomization (Phase 5.1): one transfer lemma plus `axiom_validIn_min` /
   `axiom_swap_validIn_min`.
7. Add a `stab` constructor to `Syntax.Formula`, parameterize `Formula` by a signature, replace
   it by a subtype, or edit any landed theorem (414 match arms across 57 files; 533 report §4).
   Every deliverable is a new file or an aggregator import line.
8. Import anything from `FormalSystem.Semantics` inside `FormalSystem/StarLanguage/`
   (mirror of the `BaseLanguage/` import-direction invariant). Purity predicates
   `IsPureFuture`/`IsPurePast` are syntactic and live in `StarLanguage/Formula.lean`.
9. Cite task numbers in any file under `FormalSystem/`, `docs/`, or `README.md` (C9, C9D).
   Refer to "the stability-modal probes" and to file/section names instead.
10. Describe TM⋆ in any docstring as "S5 for ⊡ plus two bridge axioms": the naive set is
    provably incomplete without PS/US (535 §2.4). Do not promise or deny decidability of TM⋆
    (535 §5: open, no easier than TM⁺).
11. Add a ⊡-necessitation rule constructor to `StarDerivationTree`. It is derivable
    (`necessitation` + `box_stab`), and a seventh-rule-plus-one shape would break the exact
    mirror of `DerivationTree` that `ofPlus` and the companion recursion rely on.
12. Land any `sorry`, any `axiom`, or any `[PARTIAL]` module under `FormalSystem/` (C3). This
    plan is not a skeleton; no strategic sorries are planned. If a phase cannot close, it closes
    `[BLOCKED]` with a written obstruction and the file is not wired into an aggregator.
13. Claim BL non-compactness at `.Discrete`/`.Dedekind` transfers from L⁺ (witnesses use
    `Formula.next = untl bot` and `K⁺`, outside `range tr`; 533 report §5). Only the positive
    Base/Dense rows are delivered.
14. Attempt L⋆ compactness (a `stab` case for `los_truthAt`) or any L⋆ decidability work
    — both out of scope (amendment (2); `README.md` decidability section).

**MUST preserve**:
- Every file in the Preserved Assets table, byte-for-byte (no edits to landed proofs).
- The C2 `#print axioms` baseline for the four flagship theorems and the documented
  `ProofSystem.Axiom` constructor count (`StarAxiom` is a new inductive; the TM⁺ count is
  unchanged).
- The `BaseLanguage/ → Semantics/` import-direction invariant (and its new `StarLanguage/`
  mirror).
- Zero structural `sorry` outside `Boneyard/`.

**Design decisions are SETTLED** (do not re-open without a concrete counterexample):
- Separate inductive `StarFormula` + `ofFormula` embedding (option (b), 533 report §4).
- `StarAxiom` closed inductive; TM⁺ schemata re-declared over `StarFormula`; ⊡ constructors
  `{stab_k, stab_t, stab_4, stab_5, box_stab, atom_stab, paste, untl_paste}` with purity side
  conditions on the last two; `minFrameClass := .Base` for every ⊡ constructor (535 §8.1).
- TM⁺ arm soundness and swap-soundness by atomization with an injective encoding
  `Atom ⊕ StarFormula → Atom` (535 §8.2).
- TD via the companion recursion, semantic, never proof-theoretic (535 §8.3; the tree's own
  pattern at `Soundness.lean:1217`).
- Past mirrors of PS/US (`snce_dstab_valid`, flipped-conjunct PS) are proved directly by the
  mirrored pasting argument, not added as constructors (535 §8.1: TD derives them).
- `StarValidOnFrames` frame-predicate primitive with `StarValidIn fc := StarValidOnFrames fc.Sat`
  (the 537 hook).
- File layout as in File territory; aggregator ownership as in the per-phase Territory lines.

## Goals & Non-Goals

- **Goals**:
  - L side: `TMFrag` with soundness, completeness (4 classes), Base/Dense compactness,
    `TM ⊆ TMFrag` (all classes), `TM ⊊ TMFrag` at `.Discrete`.
  - L⋆ side: `StarFormula` + `ofFormula`; `SameStateAt`/`StarTruthAt`/`StarValidIn`; the
    pasting lemma and the PS/US/FS/GS/SS validities; the five refutations; `StarAxiom` (535 set,
    TM⁺ schemata re-declared); `StarDerivationTree`/`StarDerivable`; soundness at all four
    classes; semantic conservativity `starValidIn_ofFormula_iff`; proof-theoretic conservativity
    both directions (`ofPlus` backward; `forward_star` forward) at all four classes; composed
    L ⊂ L⋆ backward rows; `tmFrag_iff_star`.
  - Documentation: `StarLanguage/README.md`, aggregator docstrings, `Conservativity.lean` "Star"
    section, `README.md` metatheory/open-problems rows, invariants green.
- **Non-Goals** (explicitly excluded; see Postmortem Constraints):
  - TM⋆ completeness (any semantics, any class), non-definability of ⊡, deterministic-class
    results — task 537; the deterministic-collapse lemma and store/recall — task 536; a native
    finite axiomatization of the H/G-fragment — task 534.
  - Forward proof-theoretic conservativity of TM⁺ over TM at any class.
  - L⋆ compactness, L⋆ or L decidability, BL non-compactness at Discrete/Dedekind.
  - The paper's `\BL^\star` store/recall operators (line 1374).

## Risks & Mitigations

- Risk: the 45-constructor re-declaration in Phase 4.1 drifts from `ProofSystem.Axiom` (a
  typo in one schema silently changes TM⋆). Mitigation: `ofPlus` (Phase 4.2) is a total
  function by `cases` whose every arm must be `rfl`-shaped; any drift fails to typecheck. Phase
  4.1 also states `minFrameClass_ofPlus`.
- Risk: derived operators on `StarFormula` are defined with a different right-hand side than
  `Formula`'s, breaking the `rfl` reductions that `ofPlus` (4.2) and the atomization arms
  (5.2/5.3) depend on. Mitigation: Phase 2 copies the RHS of every derived operator from
  `Syntax/Formula.lean:148-180` verbatim and pins each with an `example : ofFormula (Formula.op
  φ) = StarFormula.op (ofFormula φ) := rfl`.
- Risk: atomization transfer lemma (5.1) `stab` case needs a history through an arbitrary
  state. Mitigation: the `atomModel` valuation is defined existentially ("some total history
  through `w` at some time satisfies `⊡χ`") so the `→` direction uses `τ` itself and the `←`
  direction is E2 (`stab_state_only`); no extension theorem is needed.
- Risk: `atomize` does not commute with `swapTemporal` (fresh atoms for `⊡χ` and `⊡χ.swap`
  differ). Mitigation: the encoding is a parameter; the lemma is `atomize e (φ.swapTemporal) =
  (atomize (e.swap) φ).swapTemporal` with `e.swap := e ∘ Sum.map id swapTemporal` (injective
  because `swapTemporal` is an involution). Phase 5.3 uses `axiom_swap_validIn_min` at the
  `e.swap`-instance.
- Risk: `Semantics.lean` / `Conservativity.lean` aggregator edits collide between wave-parallel
  phases. Mitigation: single-owner wiring (Phase 3.5 for `Semantics.lean`; Phases 1.2 and 6
  for `Conservativity.lean`, sequential); every other phase builds its module explicitly.
- Risk: `SameStateAt` quantifying over domain proofs is awkward downstream. Mitigation: Phase 3.1
  provides `sameStateAt_iff_of_total` on `HF`/total histories (`τ.states t (hτ t) = σ.states t
  (hσ t)`), which is what every later phase uses.
- Risk: `TMFrag` compactness (1.2) needs list-level pullback along `tr`. Mitigation: `tr` is
  injective (`tr_injective`), `tr` commutes with `imp` (definitional), and each element of the
  witnessing list lies in `tr '' Γ`, so a `List.map`-based choice pulls it back; if
  `Compact`'s consequence form resists, deliver the model-existence form
  (`BLFinitelySatisfiableSet → BLSatisfiableSet`) from `modelExistenceBase/Dense` and record
  the shape in the summary.
- Risk: C14 documented counts change (new inductive, new theorems). Mitigation: Phase 7 runs
  `scripts/check-module-invariants.sh` and updates every count it flags; `StarAxiom` is a new
  inductive so the TM⁺ count (45) is untouched.
- Risk: phase inflation via per-constructor arms. Mitigation: arms are one-liners via the
  helpers `starValidIn_of_plus` / `starValidIn_swap_of_plus`; each dispatch lemma is one bounded
  unit; the H8 bounded-unit test is met because each arm has a fixed closing term.

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1.1, 2 | -- |
| 2 | 1.2, 3.1, 4.1 | 1.1 (for 1.2); 2 (for 3.1, 4.1) |
| 3 | 3.2, 3.3, 3.4, 4.2 | 3.1 (for 3.2, 3.3, 3.4); 4.1 (for 4.2) |
| 4 | 3.5, 5.1 | 3.2, 3.3, 3.4 |
| 5 | 5.2, 5.3 | 3.3, 4.1, 5.1 |
| 6 | 5.4 | 4.2, 5.2, 5.3 |
| 7 | 6 | 1.1, 3.2, 4.2, 5.4 |
| 8 | 7 | all |

Phases within the same wave can execute in parallel; their Territory lines are pairwise
disjoint. Group labels below are prose only; the `### Phase` headings are the leaf phases.

**Group A — L side: the H/G-fragment logic (Phases 1.1-1.2)**

### Phase 1.1: `TMFrag` — fragment logic, soundness, completeness, strict inclusion [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/Fragment.lean` defining the H/G-fragment
  of TM⁺ and transferring soundness and completeness through `blValidIn_iff_validIn_tr`.
- **Tasks:**
  - [ ] `def TMFrag (fc : FrameClass) (φ : BLFormula) : Prop := ProofSystem.Derivable fc [] (tr φ)`
        with a docstring naming it "the H/G-fragment of TM⁺" and stating why it, not TM, is the
        complete logic of `BLValidIn` (cite `tmComplete_iff_forward`).
  - [ ] `theorem tmFrag_sound {fc} (φ) : TMFrag fc φ → BLValidIn fc φ` — from `soundness_validIn`
        (`Soundness.lean:1316`) and `(blValidIn_iff_validIn_tr fc φ).mpr`.
  - [ ] `theorem tmFrag_complete {fc} (engine : WeakCompleteness fc) (φ) : BLValidIn fc φ → TMFrag fc φ`;
        `theorem tmFrag_iff_blValidIn (engine) (φ) : TMFrag fc φ ↔ BLValidIn fc φ`.
  - [ ] Four rows `tmFrag_complete_base/dense/discrete/dedekind` from
        `completeness_base/dense/discrete/dedekind`.
  - [ ] `theorem tm_le_tmFrag {fc} (φ) : BaseLanguage.Derivable fc [] φ → TMFrag fc φ` — the
        `Γ = []` instance of `derivable_translate` (`Backward.lean:88`; confirm the context
        shape `trCtx [] = []` reduces).
  - [ ] `theorem tmFrag_z1_discrete (p) : TMFrag .Discrete (Z1 (.atom p))` (= `z1_translate`);
        `theorem tm_lt_tmFrag_discrete : (∀ φ, BaseLanguage.Derivable .Discrete [] φ → TMFrag .Discrete φ) ∧ ∃ φ, TMFrag .Discrete φ ∧ ¬ BaseLanguage.Derivable .Discrete [] φ`
        from `not_bl_derivable_z1` (`Z1Countermodel.lean:175`).
  - [ ] `theorem tmComplete_iff_tmFrag_le_tm {fc} : TMComplete fc ↔ ∀ φ, TMFrag fc φ → BaseLanguage.Derivable fc [] φ`
        given an engine (one line from `tmComplete_iff_forward`; `Forward` is unfolded, never
        asserted).
  - [ ] Inline `example`s: `tmFrag_iff_blValidIn completeness_base` typechecks; `#print axioms
        tm_lt_tmFrag_discrete` shows only `propext`, `Classical.choice`, `Quot.sound`.
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity.Fragment`.
- **Territory:** creates `FormalSystem/Metalogic/Conservativity/Fragment.lean` only.
- **Estimated output:** ~150 lines. **Done when:** the module builds sorry-free and every
  theorem above is present with the stated statement shape.
- **Timing:** 1.5 hours
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** the statements compose on the nose with `soundness_validIn`
  (`Soundness.lean:1316`), `WeakCompleteness` (`SetConsequence.lean:234`, `∀ ψ, ValidIn fc ψ →
  Derivable fc [] ψ`), and `TMComplete` (`TMCompletenessReduction.lean:94`); confirm by
  `lean_hover_info` on each before writing.

### Phase 1.2: `TMFrag` compactness at Base and Dense, and `Conservativity.lean` wiring [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/FragmentCompactness.lean` transferring
  `compactBase`/`compactDense` to the base language, and wire both Group A modules into the
  `Conservativity.lean` aggregator.
- **Tasks:**
  - [ ] Native definitions mirroring `SetConsequence.lean:153-197` shapes for `BLFormula`:
        `BLSetSemanticConsequenceOn fc (Γ : Set BLFormula) (φ)` (every model in `fc`, every
        total history and time satisfying `Γ` satisfies `φ`, via `BLTruthAt`) and
        `BLCompact fc := ∀ Γ φ, BLSetSemanticConsequenceOn fc Γ φ → ∃ L : List BLFormula, (∀ ψ ∈ L, ψ ∈ Γ) ∧ BLValidIn fc (L.foldr BLFormula.imp φ)`.
  - [ ] `theorem blSetConsequence_iff_image : BLSetSemanticConsequenceOn fc Γ φ ↔ SetSemanticConsequenceOn fc (tr '' Γ) (tr φ)`
        via `truthAt_tr` (`BaseLanguageSoundness.lean:110`).
  - [ ] `theorem tr_foldr_imp (L : List BLFormula) (φ) : tr (L.foldr BLFormula.imp φ) = (L.map tr).foldr Formula.imp (tr φ)`
        by induction on `L` (`tr` is definitional on `imp`).
  - [ ] `theorem blCompact_of_compact {fc} (h : Compact fc) : BLCompact fc` — obtain the L⁺
        witness list `L' ⊆ tr '' Γ`, pull each element back along `tr` (choice on the image
        membership, or `List.map` over a chosen preimage function on `tr '' Γ`), rewrite with
        `tr_foldr_imp` and `blValidIn_iff_validIn_tr`.
  - [ ] `theorem blCompactBase : BLCompact .Base := blCompact_of_compact compactBase`;
        `theorem blCompactDense : BLCompact .Dense := blCompact_of_compact compactDense`.
  - [ ] Docstring: state that the Discrete/Dedekind rows do NOT transfer (Postmortem rule 13)
        and why (`tr_ne_untl`; `Formula.next`/`K⁺` outside `range tr`).
  - [ ] Add `import FormalSystem.Metalogic.Conservativity.Fragment` and
        `import FormalSystem.Metalogic.Conservativity.FragmentCompactness` to
        `FormalSystem/Metalogic/Conservativity.lean` (aggregator, lines 7-11 pattern) and a
        one-paragraph "## The H/G-fragment logic" section to its module docstring pointing at
        the two files (the full "Star" section is Phase 6's).
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity` (direct dependents of the
        aggregator: `FormalSystem.Metalogic`).
- **Territory:** creates `Conservativity/FragmentCompactness.lean`; edits
  `FormalSystem/Metalogic/Conservativity.lean` (import lines + one docstring section).
- **Estimated output:** ~170 lines. **Done when:** `blCompactBase`/`blCompactDense` build
  sorry-free and `lake build FormalSystem.Metalogic` is green.
- **Timing:** 2 hours
- **Depends on:** 1.1
- **Verification Tier:** interface
- **Scope Hypothesis:** `Compact` is the consequence form at `SetConsequence.lean:197`
  (`∀ Γ φ, SetSemanticConsequenceOn fc Γ φ → ∃ L, (∀ ψ ∈ L, ψ ∈ Γ) ∧ ValidIn fc (L.foldr Formula.imp φ)`);
  `SetSemanticConsequenceOn`'s binder shape is to be read from the same file before mirroring.
  If the list pullback resists, the fallback statement is the model-existence form from
  `modelExistenceBase` (`Compactness.lean:161`) — record which form landed.

**Group B — L⋆ syntax (Phase 2)**

### Phase 2: `StarFormula` syntax, derived operators, purity predicates, and `ofFormula` [NOT STARTED]
- **Goal:** Land `FormalSystem/StarLanguage/Formula.lean`: the 7-constructor `StarFormula`,
  derived operators with right-hand sides identical to `Formula`'s, `swapTemporal`, the
  purity predicates, and the embedding with its algebraic lemmas.
- **Tasks:**
  - [ ] `inductive StarFormula` with constructors `atom, bot, imp, box, untl, snce, stab` (order
        and argument order as in `Syntax/Formula.lean:74`), `deriving Repr, DecidableEq`; add
        `Countable` the way `Formula` obtains it; `instance : Infinite StarFormula` via
        `Infinite.of_injective (StarFormula.atom)`; `noncomputable instance : Denumerable
        StarFormula := Classical.choice (nonempty_denumerable _)` (mirror `Formula.lean:126`).
  - [ ] `abbrev StarContext := List StarFormula`.
  - [ ] Derived operators, each with the RHS copied from `Syntax/Formula.lean:148-180` and the
        operators referenced by any `Axiom` constructor statement (`neg`, `top`, `conj`, `disj`,
        `iff`, `diamond`, `someFuture`, `allFuture`, `somePast`, `allPast`, and every other
        derived operator the 45 constructors mention — enumerate by reading
        `ProofSystem/Axioms.lean:111-464`); plus the ⊡-specific `dstab := neg ∘ stab ∘ neg`,
        `Will := stab ∘ allFuture`, `will := stab ∘ someFuture`, `Could := dstab ∘ allFuture`,
        `could := dstab ∘ someFuture` (paper 1121, 1125-1129).
  - [ ] `def swapTemporal : StarFormula → StarFormula` (mirror `Formula.lean:668`; `stab φ ↦
        stab φ.swapTemporal`), involution lemma, and the `swap_temporal_*` push-through lemmas
        for every derived operator (mirror the eleven `Formula.swap_temporal_*` lemmas).
  - [ ] `inductive IsPureFuture : StarFormula → Prop` and `IsPurePast` exactly as in the 535
        probes (`box`/`stab` are leaves); `theorem IsPureFuture.swapTemporal : IsPureFuture φ →
        IsPurePast φ.swapTemporal`, `theorem IsPurePast.swapTemporal : IsPurePast φ → IsPureFuture
        φ.swapTemporal` (induction on the predicate); `IsPureFuture` closure lemmas for `neg`,
        `conj`, `someFuture`, `allFuture` (needed by Phase 5.3's swap arms).
  - [ ] `def ofFormula : Formula → StarFormula` (constructor to constructor);
        `theorem ofFormula_injective` (per-constructor `cases ψ <;> simp [ofFormula] at h <;> rw
        [ih …]` — the compiled proof from the 533 report Appendix A; `simp_all` alone fails);
        `theorem ofFormula_ne_stab`; `theorem ofFormula_swapTemporal : ofFormula φ.swapTemporal =
        (ofFormula φ).swapTemporal`; `def ofCtx : Context → StarContext := List.map ofFormula`
        with `ofCtx_nil`, `mem_ofCtx`.
  - [ ] `rfl` pins: `example : ofFormula (Formula.allFuture φ) = StarFormula.allFuture (ofFormula φ) := rfl`
        and one such `example` for every derived operator (these are what Phases 4.2 and 5.1
        rely on).
  - [ ] Module docstring: the `StarLanguage/ → Semantics/` import prohibition (mirror
        `BaseLanguage/Formula.lean:32-39`), the paper anchors (lines 1108-1129), and the
        statement that the paper's `\BL^\star` store/recall operators are out of scope.
  - [ ] `FormalSystem/StarLanguage/README.md` (short: purpose, invariant, module list — the two
        later modules listed as "landed by later phases" is not acceptable under C5/C12; list
        only `Formula.lean` now, Phase 7 completes it).
  - [ ] Build: `lake build FormalSystem.StarLanguage.Formula`.
- **Territory:** creates `FormalSystem/StarLanguage/Formula.lean`,
  `FormalSystem/StarLanguage/README.md`.
- **Estimated output:** ~260 lines Lean + ~30 lines README. **Done when:** the module builds,
  every `rfl` pin passes, `ofFormula_injective` and both purity-swap lemmas are sorry-free.
- **Timing:** 2 hours
- **Depends on:** none
- **Verification Tier:** local
- **Scope Hypothesis:** the derived-operator list is whatever `Syntax/Formula.lean:148-180`
  defines plus whatever the 45 `Axiom` constructors reference; the eleven `swap_temporal_*`
  lemmas are the count the `Truth.lean:1108` docstring reports — confirm both by
  `lean_local_search` / `lean_file_outline` before writing.

**Group C — L⋆ semantics (Phases 3.1-3.5)**

### Phase 3.1: `SameStateAt`, `StarTruthAt`, clause lemmas, definitional validities, shift invariance [NOT STARTED]
- **Goal:** Land `FormalSystem/Semantics/StarTruth.lean` by transcribing probes Parts A, B and E
  into repo style (docstrings with paper anchors, `FormalSystem.Semantics` namespace, no
  `Scratch535` namespace, no task numbers).
- **Tasks:**
  - [ ] `def SameStateAt (τ σ : WorldHistory F) (t : F.Duration) : Prop` (paper line 1108);
        `theorem sameStateAt_iff_of_total (hτ : τ.IsTotal) (hσ : σ.IsTotal) : SameStateAt τ σ t ↔ τ.states t (hτ t) = σ.states t (hσ t)`;
        reflexivity/symmetry/transitivity lemmas at total histories; `sameStateAt_timeShift`
        (A6, `Iff.rfl`); `sameStateAt_congr_left`.
  - [ ] `def StarTruthAt (M : TaskModel F) (τ) (t) : StarFormula → Prop` with the seven clauses
        exactly as in the probes (the six L⁺ clauses verbatim from `Truth.lean:223`'s shape, the
        `stab` clause per paper line 1114).
  - [ ] Clause lemmas: `atom_iff`, `conj_iff`, `neg_iff`, `dstab_iff`, `someFuture_iff`,
        `allFuture_iff`, `somePast_iff`, `allPast_iff`, `untl_iff`, `snce_iff`, `box_iff`, and
        `stab_iff` (all `Iff.rfl` or `simp`), in a `StarTruth` namespace mirroring `BLTruth.*`.
  - [ ] A1-A5: `stab_of_box`, `of_stab`, `stab_four`, `stab_five`, `stab_atom_of_atom`.
  - [ ] B1-B3: `stab_congr_sameState`, `box_stab_iff`, `stab_box_of_box`.
  - [ ] E0-E2: `states_congr`, `truth_congr_ext`, `timeShift_isTotal'` (check whether
        `WorldHistory.timeShift_isTotal` already exists and reuse it), `shift_neg_shift_domain`,
        `shift_neg_shift_states`, `starTruthAt_timeShift`, `stab_state_only`.
  - [ ] Build: `lake build FormalSystem.Semantics.StarTruth`.
- **Territory:** creates `FormalSystem/Semantics/StarTruth.lean` only (no aggregator edit;
  wiring is Phase 3.5).
- **Estimated output:** ~330 lines (transcription of ~280 compiled probe lines plus
  docstrings). **Done when:** all listed declarations build sorry-free.
- **Timing:** 2 hours
- **Depends on:** 2
- **Verification Tier:** local
- **Scope Hypothesis:** the probes compile against the live tree today (`lake env lean` exit 0
  per the 535 report); re-run that command first — if it fails, the tree moved and the
  transcription adapts to the failing lemma names before anything else.

### Phase 3.2: `StarValidIn` family and semantic conservativity along `ofFormula` [NOT STARTED]
- **Goal:** Land `FormalSystem/Semantics/StarValidity.lean` mirroring `BLValidity.lean:96-123`
  binder for binder, plus the truth-transfer and validity-transfer lemmas.
- **Tasks:**
  - [ ] `def TaskFrame.StarValidOn (F) (φ : StarFormula)`, `def StarValidOnFrames (P : TaskFrame → Prop) (φ)`
        (the primitive; the 537 hook), `def StarValidIn (fc) (φ) := StarValidOnFrames fc.Sat φ`,
        `def StarValid (φ) := StarValidIn .Base φ`; per-class abbreviations
        `StarValidDense/Discrete/Dedekind` if `BLValidity.lean:204-268` has them.
  - [ ] `StarValidIn.of_forall_total`, `StarValidIn.apply_total`, `StarValidIn.mono` (mirror
        `Validity.lean:551,558` and `ValidIn.mono`), `StarValidOnFrames.mono` on the predicate.
  - [ ] `theorem starTruthAt_ofFormula (M) (φ : Formula) : ∀ τ t, StarTruthAt M τ t (ofFormula φ) ↔ TruthAt M τ t φ`
        (compiled in the 533 report Appendix A: `induction φ` with `Iff.rfl`/`Iff.imp`/
        `forall_congr'`/`exists_congr`/`and_congr`); `starTruthAt_ofCtx`.
  - [ ] `theorem starValidIn_ofFormula_iff (fc) (φ) : StarValidIn fc (ofFormula φ) ↔ ValidIn fc φ`
        — **semantic conservativity of L⋆ over L⁺, all classes** (generic `fc` form of the
        compiled `starValid_ofFormula_iff`, using `ValidIn.of_forall_total`/`apply_total`).
  - [ ] `theorem starValid_ofFormula_iff (φ) : StarValid (ofFormula φ) ↔ Valid φ` corollary.
  - [ ] Build: `lake build FormalSystem.Semantics.StarValidity`.
- **Territory:** creates `FormalSystem/Semantics/StarValidity.lean` only.
- **Estimated output:** ~200 lines. **Done when:** `starValidIn_ofFormula_iff` builds
  sorry-free at generic `fc`.
- **Timing:** 1.5 hours
- **Depends on:** 3.1
- **Verification Tier:** local
- **Scope Hypothesis:** the `BLValidity.lean:96-123` binder shapes and the per-class abbreviations at `:204-268` are the template; confirm the exact list with `lean_file_outline` before mirroring, and the ~200-line estimate follows that list.

### Phase 3.3: History pasting, purity congruences, and the PS/US/FS/GS/SS validities [NOT STARTED]
- **Goal:** Land `FormalSystem/Semantics/StarPasting.lean` by transcribing probes Part C and
  adding the two past mirrors Phase 5.3 needs.
- **Tasks:**
  - [ ] `pasteFun`, `paste_rel_le_lt`, `paste_rel`, `paste` (via `WorldHistory.ofTotal`),
        `paste_isTotal`, `AgreeFrom`, `AgreeUpTo`, `agreeFrom_mono`, `agreeUpTo_mono`,
        `paste_agreeFrom`, `paste_agreeUpTo` — verbatim from the probes with docstrings citing
        `TaskFrame.comp`/`TaskFrame.converse` (paper `def:frame`).
  - [ ] `truth_congr_agreeFrom` (C1a), `truth_congr_agreeUpTo` (C1b) — inductions on
        `IsPureFuture`/`IsPurePast` from Phase 2.
  - [ ] `paste_valid` (C2, PS), `future_dstab_valid` (C3, FS), `stab_allFuture_valid` (C4, GS),
        `untl_dstab_valid` (C5, US) — verbatim.
  - [ ] New: `paste_valid'` — PS with the conjunct order exchanged
        (`(dstab ψ).imp ((dstab φ).imp (dstab (conj ψ φ)))` for pure-past `ψ`, pure-future `φ`),
        proved by the same argument (this is exactly `(StarAxiom.paste φ ψ).formula.swapTemporal`
        up to the purity swap); and `snce_dstab_valid` (SS) — the `snce` mirror of C5:
        witness `ρ` at a past time `y < t`, paste `ρ` (up to `y`) with `τ` (after `y`), agreement
        with `τ` from `y` onward, pure-past `φ` at `y` sees `ρ`, the pure-future guard on
        `(y, t)` sees `τ`. Mirror the C5 proof line by line with `paste_agreeUpTo`/`AgreeFrom`
        roles exchanged.
  - [ ] Package the class-level statements the dispatch lemmas will consume:
        `theorem paste_starValid (hφ) (hψ) : StarValid (…)`, likewise `untl_paste_starValid`,
        `paste'_starValid`, `snce_paste_starValid`, each by `StarValidIn.of_forall_total`.
  - [ ] Build: `lake build FormalSystem.Semantics.StarPasting`.
- **Territory:** creates `FormalSystem/Semantics/StarPasting.lean` only.
- **Estimated output:** ~330 lines (≈250 transcribed + ≈80 new). **Done when:** all four probe
  validities and both mirrors build sorry-free; the `StarValid` packagings typecheck.
- **Timing:** 2.5 hours
- **Depends on:** 3.1 (and 2 for the purity predicates)
- **Verification Tier:** local
- **Scope Hypothesis:** the SS mirror closes by the literal role exchange (535 report marks it
  "mechanical, UNVERIFIED as a compiled statement"); budget one attempt of the mirrored proof
  and, if a bound orientation resists, one attempt via `truth_congr_ext` on the pasted history —
  after that the phase closes `[BLOCKED]` with the goal state recorded, and Phase 5.3's US swap
  arm is the only consumer affected.

### Phase 3.4: Non-validity witnesses D1-D5 on the permissive frame over ℤ [NOT STARTED]
- **Goal:** Land `FormalSystem/Semantics/StarNonValidities.lean` by transcribing probes Part D,
  so that every docstring claim of the form "X is not an axiom because it is refuted" is
  machine-backed.
- **Tasks:**
  - [ ] `NF := FrameOver.natFrame (D := ℤ)` (`TaskFrame.lean:1602`), `natHist`,
        `natHist_isTotal`, `natModel` — verbatim, with the `Mathlib.Algebra.Order.Group.Int`
        and `Mathlib.Data.Int.SuccPred` imports the probes use.
  - [ ] `refute_stab_box` (D1: `⊡p → □⊡p`), `refute_allFuture_stab` (D2: `G⊡p → ⊡Gp`),
        `refute_stab_allFuture_past` (D3: `⊡GPp → G⊡Pp`, the pure-future restriction is
        necessary), `refute_determined` (D4: `Fp → ⊡Fp` over a non-deterministic frame),
        `refute_somePast_stab` (D5: `P⊡p → ⊡Pp`).
  - [ ] Docstrings: D4 says only "refuted over a non-deterministic frame (paper
        `app:non-deterministic`); validity over deterministic frames is not formalized here" —
        no "exactly" (Postmortem rule 2). D2/D3 docstrings state that GS (`stab_allFuture_valid`)
        needs its purity side condition.
  - [ ] Build: `lake build FormalSystem.Semantics.StarNonValidities`.
- **Territory:** creates `FormalSystem/Semantics/StarNonValidities.lean` only.
- **Estimated output:** ~150 lines. **Done when:** the five refutations build sorry-free.
- **Timing:** 1.5 hours
- **Depends on:** 3.1
- **Verification Tier:** local
- **Scope Hypothesis:** five refutations, ~150 lines, transcribed from probes Part D (`natFrame` over ℤ); the count is fixed by the probes file — no new refutation is added here (the DAG-frame refutation the 535 report leaves UNVERIFIED belongs to a follow-up, not this phase).

### Phase 3.5: `Semantics.lean` aggregator wiring and docstring rows [NOT STARTED]
- **Goal:** Make the four `Semantics/Star*.lean` modules reachable from the root and document
  them in the aggregator, in one owner phase.
- **Tasks:**
  - [ ] Add `import FormalSystem.Semantics.StarTruth`, `…StarValidity`, `…StarPasting`,
        `…StarNonValidities` to `FormalSystem/Semantics.lean` next to the `BLTruth`/`BLValidity`
        imports (lines 24, 31-32).
  - [ ] Add four docstring rows to the aggregator's module list (mirror the `BLTruth`/
        `BLValidity` rows at lines 106-112), naming the paper anchor (line 1114) and the
        pasting lemma.
  - [ ] Add a "Star" paragraph to `FormalSystem/Semantics/README.md` if it carries a module
        inventory (check; C5/C12 require every listed path to resolve).
  - [ ] Build: `lake build FormalSystem.Semantics` and its direct dependents
        (`FormalSystem.Metalogic` is the transitive consumer; a full `lake build` is acceptable
        here since nothing else changes).
- **Territory:** edits `FormalSystem/Semantics.lean` and (if present in inventory form)
  `FormalSystem/Semantics/README.md` only.
- **Estimated output:** ~25 lines. **Done when:** `lake build` is green with all four modules
  reachable.
- **Timing:** 0.5 hours
- **Depends on:** 3.2, 3.3, 3.4
- **Verification Tier:** interface
- **Scope Hypothesis:** four import lines plus four docstring rows (~25 lines); if `FormalSystem/Semantics/README.md` carries a module inventory, one more paragraph — confirm by reading it first.

**Group D — L⋆ proof system (Phases 4.1-4.2)**

### Phase 4.1: `StarAxiom` — closed inductive with the TM⁺ schemata over `StarFormula` and the eight ⊡ constructors [NOT STARTED]
- **Goal:** Land `FormalSystem/StarLanguage/Axioms.lean` defining the TM⋆ axiom schemata
  exactly as 535 §8.1 prescribes, plus `minFrameClass`.
- **Tasks:**
  - [ ] `inductive StarAxiom : StarFormula → Type` whose first block re-declares every
        constructor of `ProofSystem.Axiom` (`Axioms.lean:111-464`) with the same name, the same
        parameter list with `StarFormula` in place of `Formula`, and the same statement using the
        Phase 2 derived operators; copy each docstring's first sentence and its Burgess 1982 /
        paper anchor.
  - [ ] Second block, the ⊡ constructors (docstrings cite paper 1118/1119/1108 and the probes
        C2/C5 by lemma name):
        `stab_k (φ ψ) : StarAxiom ((.stab (φ.imp ψ)).imp ((.stab φ).imp (.stab ψ)))`,
        `stab_t (φ) : StarAxiom ((.stab φ).imp φ)`,
        `stab_4 (φ) : StarAxiom ((.stab φ).imp (.stab (.stab φ)))`,
        `stab_5 (φ) : StarAxiom ((dstab φ).imp (.stab (dstab φ)))` (state 5 in the form the
        A4 probe proves, `¬⊡φ → ⊡¬⊡φ`, and note the `dstab` reading),
        `box_stab (φ) : StarAxiom ((.box φ).imp (.stab φ))`,
        `atom_stab (p : Atom) : StarAxiom ((.atom p).imp (.stab (.atom p)))`,
        `paste (φ ψ) (hφ : IsPureFuture φ) (hψ : IsPurePast ψ) : StarAxiom ((dstab φ).imp ((dstab ψ).imp (dstab (conj φ ψ))))`,
        `untl_paste (α φ) (hα : IsPurePast α) (hφ : IsPureFuture φ) : StarAxiom ((.untl α (dstab φ)).imp (dstab (.untl α φ)))`.
  - [ ] `def StarAxiom.minFrameClass : StarAxiom φ → FrameClass` — TM⁺ arms copied from
        `Axiom.minFrameClass` (`Axioms.lean:599-607`), the eight ⊡ arms `.Base`.
  - [ ] Module docstring: the axiom inventory table (validated / derived / refuted, pointing at
        Phase 3.3/3.4 lemma names), the statement that the naive S5-plus-bridges set is
        incomplete without `paste`/`untl_paste` (Postmortem rule 10, phrased positively), that
        the past mirrors are derived by TD, that ⊡-necessitation is derived, and that
        completeness/decidability of TM⋆ are open and out of this module's scope.
  - [ ] Build: `lake build FormalSystem.StarLanguage.Axioms`.
- **Territory:** creates `FormalSystem/StarLanguage/Axioms.lean` only.
- **Estimated output:** ~380 lines (45 + 8 constructors with one-line docstrings, one
  `minFrameClass`). Over the advisory band but one bounded unit: one inductive, transcribed from
  an existing file. **Done when:** the module builds and `minFrameClass` is total.
- **Timing:** 2.5 hours
- **Depends on:** 2
- **Verification Tier:** local
- **Scope Hypothesis:** `ProofSystem.Axiom` has 45 constructors (533 report §2, C14 documented
  count). Confirm with `lean_file_outline` on `ProofSystem/Axioms.lean` before writing; the
  re-declared block must have exactly that many.

### Phase 4.2: `StarDerivationTree`, `StarDerivable`, derived ⊡-necessitation, and backward conservativity via `ofPlus` [NOT STARTED]
- **Goal:** Land `FormalSystem/StarLanguage/Derivation.lean` and the `FormalSystem/StarLanguage.lean`
  aggregator; prove the easy conservativity direction at all four classes.
- **Tasks:**
  - [ ] `inductive StarDerivationTree (fc : FrameClass) : StarContext → StarFormula → Type`
        with exactly the seven rules of `ProofSystem.DerivationTree` (`Derivation.lean:98-164`):
        `axiom (Γ φ) (h : StarAxiom φ) (h_fc : h.minFrameClass ≤ fc)`, `assumption`,
        `modus_ponens`, `necessitation`, `temporal_necessitation`, `temporal_duality`
        (concluding `φ.swapTemporal`), `weakening` — same argument shapes.
  - [ ] `def StarDerivable (fc) (Γ) (φ) : Prop := Nonempty (StarDerivationTree fc Γ φ)`;
        the `lift`/`mono` helpers `BaseLanguage/Derivation.lean` provides.
  - [ ] `theorem stab_necessitation (d : StarDerivationTree fc [] φ) : StarDerivationTree fc [] (.stab φ)`
        — `necessitation` then `modus_ponens` with `box_stab` (Postmortem rule 11).
  - [ ] `def StarAxiom.ofPlus : Axiom φ → StarAxiom (ofFormula φ)` by `cases` (45 arms, each
        `exact .c _ …` after the `rfl` reduction of `ofFormula` through the derived operators),
        and `theorem minFrameClass_ofPlus (ax) : (StarAxiom.ofPlus ax).minFrameClass = ax.minFrameClass`.
  - [ ] `def StarDerivationTree.ofPlus : DerivationTree fc Γ φ → StarDerivationTree fc (ofCtx Γ) (ofFormula φ)`
        by structural recursion (the TD arm uses `ofFormula_swapTemporal`; the `weakening` arm
        uses `mem_ofCtx`); `theorem starDerivable_of_derivable : Derivable fc Γ φ → StarDerivable fc (ofCtx Γ) (ofFormula φ)`.
  - [ ] Four row corollaries `star_backward_base/dense/discrete/dedekind` at `Γ = []`.
  - [ ] Create the aggregator `FormalSystem/StarLanguage.lean` importing `Formula`, `Axioms`,
        `Derivation` (C8: sibling `X.lean` beside `X/`), with a module docstring mirroring
        `FormalSystem/BaseLanguage.lean`'s.
  - [ ] Build: `lake build FormalSystem.StarLanguage`.
- **Territory:** creates `FormalSystem/StarLanguage/Derivation.lean`,
  `FormalSystem/StarLanguage.lean`.
- **Estimated output:** ~230 lines. **Done when:** `starDerivable_of_derivable` builds
  sorry-free at generic `fc` and `Γ`.
- **Timing:** 2 hours
- **Depends on:** 4.1
- **Verification Tier:** local
- **Scope Hypothesis:** every `ofPlus` arm is `rfl`-shaped given Phase 2's derived-operator
  pins; if an arm is not, the fix is in Phase 2's RHS (never a rewrite inside `ofPlus`).

**Group E — L⋆ soundness (Phases 5.1-5.4)**

### Phase 5.1: Atomization — encoding, `atomize`, `atomModel`, transfer lemma, swap commutation [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/Star/Atomization.lean`, the single
  lemma that discharges all 45 TM⁺ schemata over L⋆ (535 §8.2).
- **Tasks:**
  - [ ] `structure Encoding where ι : Atom ⊕ StarFormula → Atom; inj : Function.Injective ι`;
        `theorem Encoding.nonempty : Nonempty Encoding` from `Denumerable (Atom ⊕ StarFormula)`
        and `Denumerable Atom` (both `Countable` + `Infinite`; `Atom` is a structure with an
        `Option Nat` fresh index, `Syntax/Atom.lean:75`); `def Encoding.swap (e) : Encoding :=
        ⟨e.ι ∘ Sum.map id StarFormula.swapTemporal, …⟩` (injective by the involution).
  - [ ] `def atomize (e : Encoding) : StarFormula → Formula` — structural on the six L⁺
        constructors, `atom p ↦ .atom (e.ι (.inl p))`, `stab χ ↦ .atom (e.ι (.inr χ))`;
        push-through lemmas `atomize_neg`, `atomize_allFuture`, … for every derived operator
        (all `rfl`), and `theorem atomize_swapTemporal (e) (φ) : atomize e φ.swapTemporal = (atomize e.swap φ).swapTemporal`
        (induction; the `stab` and `atom` cases are the only non-structural ones).
  - [ ] `def TaskModel.atomModel (M : TaskModel F) (e : Encoding) : TaskModel F` with
        `valuation w a := (∃ p, e.ι (.inl p) = a ∧ M.valuation w p) ∨ (∃ χ, e.ι (.inr χ) = a ∧ ∃ (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration), τ.states t (hτ t) = w ∧ StarTruthAt M τ t (.stab χ))`.
  - [ ] `theorem starTruthAt_iff_atomize (M) (e) (φ) : ∀ τ (hτ : τ.IsTotal) t, StarTruthAt M τ t φ ↔ TruthAt (M.atomModel e) τ t (atomize e φ)`
        — induction on `φ`; `atom` case by injectivity (the `inr` disjunct is impossible);
        `stab` case: `→` witnesses `τ` itself, `←` is `stab_state_only` (E2); `box` case ranges
        over total `σ`; `untl`/`snce` stay on the total `τ`.
  - [ ] `theorem starValidIn_of_plus {fc} (e : Encoding) (φ : StarFormula) (ax : Axiom (atomize e φ)) (h : ax.minFrameClass ≤ fc) : StarValidIn fc φ`
        and `theorem starValidIn_swap_of_plus {fc} (e) (φ) (ax : Axiom (atomize e.swap φ)) (h) : StarValidIn fc φ.swapTemporal`
        — from `axiom_validIn`/`axiom_swap_validIn` (`Soundness.lean:1206-1214`) at
        `M.atomModel e` (same frame, so `fc.Sat` is inherited) and the transfer lemma
        (the swap form rewrites with `atomize_swapTemporal`).
  - [ ] Acceptance `example` (535's acceptance test): `StarValidIn .Base ((.box (.stab (.atom p))).imp (.box (allFuture (.stab (.atom p)))))`
        via `starValidIn_of_plus e _ (Axiom.modal_future _) le_rfl` for some `e := Classical.choice Encoding.nonempty`.
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity.Star.Atomization`.
- **Territory:** creates `FormalSystem/Metalogic/Conservativity/Star/Atomization.lean` only.
- **Estimated output:** ~300 lines. **Done when:** the transfer lemma, `atomize_swapTemporal`,
  and both `starValidIn_*_of_plus` helpers build sorry-free and the acceptance `example`
  typechecks.
- **Timing:** 3 hours
- **Depends on:** 3.2 (and 2)
- **Verification Tier:** local
- **Scope Hypothesis:** `Denumerable Atom` is obtainable as `Formula`'s is (`Formula.lean:126`
  pattern; `Atom` derives `Countable`? — confirm; otherwise prove `Countable Atom` from
  `String`/`Option Nat` encodings) and `Infinite Atom` exists or follows from the fresh index.
  Confirm both by `lean_local_search` before writing.

### Phase 5.2: `starAxiom_validIn_min` — validity dispatch over every `StarAxiom` constructor [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/Star/AxiomValidity.lean` (first half):
  one lemma, one arm per constructor.
- **Tasks:**
  - [ ] `theorem starAxiom_validIn_min {φ} (ax : StarAxiom φ) : StarValidIn ax.minFrameClass φ := by cases ax with …`
        — the 45 TM⁺ arms each `exact starValidIn_of_plus e _ (Axiom.c (atomize e ψ₁) …) le_rfl`
        (with `e` fixed once by `Classical.choice Encoding.nonempty` at the top of the file);
        the ⊡ arms: `stab_k` (direct from the `stab` clause), `stab_t`/`stab_4`/`stab_5`/
        `box_stab`/`atom_stab` from Phase 3.1's A1-A5 via `StarValidIn.of_forall_total`;
        `paste`/`untl_paste` from Phase 3.3's `paste_starValid`/`untl_paste_starValid`.
  - [ ] `theorem starAxiom_validIn {fc} (ax : StarAxiom φ) (h : ax.minFrameClass ≤ fc) : StarValidIn fc φ := StarValidIn.mono h (starAxiom_validIn_min ax)`.
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity.Star.AxiomValidity`.
- **Territory:** creates `Conservativity/Star/AxiomValidity.lean` (Phase 5.3 appends to the same
  file in the next wave; no parallel edit).
- **Estimated output:** ~180 lines. **Done when:** the dispatch lemma builds with no `sorry`
  and no `_ =>` wildcard arm (every constructor named explicitly, so a future constructor fails
  the build until its arm is added — the 537 extension discipline).
- **Timing:** 2.5 hours
- **Depends on:** 3.3, 4.1, 5.1
- **Verification Tier:** local
- **Scope Hypothesis:** each TM⁺ arm's `atomize e (schema instance)` reduces by `rfl` to the
  `Formula` schema instance at `atomize e ψᵢ` (Phase 2 derived-operator pins + Phase 5.1
  push-through lemmas). If an arm needs `simp only [atomize_*]` first, that is acceptable; if it
  needs anything else, the derived-operator RHS in Phase 2 is wrong and is fixed there.

### Phase 5.3: `starAxiom_swap_validIn_min` — swap-validity dispatch (the semantic TD input) [NOT STARTED]
- **Goal:** Complete `Conservativity/Star/AxiomValidity.lean` with the mirrored dispatch, which
  is what makes `temporal_duality` sound without any proof-theoretic mirror argument.
- **Tasks:**
  - [ ] `theorem starAxiom_swap_validIn_min {φ} (ax : StarAxiom φ) : StarValidIn ax.minFrameClass φ.swapTemporal := by cases ax with …`
        — TM⁺ arms: `exact starValidIn_swap_of_plus e _ (Axiom.c (atomize e.swap ψ₁) …) le_rfl`
        (mirror of `axiom_swap_validIn_min`, `Soundness.lean:1190`, but uniform: no per-class
        case split is needed because the L⁺ lemma already carries it);
        ⊡ arms: `stab_k/stab_t/stab_4/stab_5/box_stab/atom_stab` — `swapTemporal` fixes `stab`
        and is structural, so the swapped instance is the same constructor at swapped
        arguments; `exact` the Phase 3.1 validity at `φ.swapTemporal` after `simp only
        [StarFormula.swapTemporal, swap_temporal_*]`;
        `paste φ ψ hφ hψ`: the swapped formula is `paste_valid'` at `(ψ.swapTemporal,
        φ.swapTemporal)` with `hψ.swapTemporal : IsPureFuture ψ.swapTemporal`,
        `hφ.swapTemporal : IsPurePast φ.swapTemporal` (Phase 2) — `exact paste'_starValid …`;
        `untl_paste α φ hα hφ`: the swapped formula is SS at `(α.swapTemporal, φ.swapTemporal)`
        — `exact snce_paste_starValid hα.swapTemporal hφ.swapTemporal`.
  - [ ] `theorem starAxiom_swap_validIn {fc} (ax) (h : ax.minFrameClass ≤ fc) : StarValidIn fc φ.swapTemporal`.
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity.Star.AxiomValidity`.
- **Territory:** edits `Conservativity/Star/AxiomValidity.lean` (append) only.
- **Estimated output:** ~180 lines. **Done when:** the swap dispatch builds sorry-free with
  every constructor named explicitly.
- **Timing:** 2.5 hours
- **Depends on:** 3.3, 4.1, 5.1 (and 2's purity-swap lemmas)
- **Verification Tier:** local
- **Scope Hypothesis:** the `dstab`/`conj` push-through of `swapTemporal` is by the Phase 2
  `swap_temporal_*` lemmas; the `paste` arm's target matches `paste_valid'` syntactically after
  `simp only` — if the conjunct order differs, add the missing `conj` commutation lemma in this
  file rather than re-opening Phase 3.3.

### Phase 5.4: `star_derivable_valid_and_swap_validIn` companion recursion and the four soundness rows [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean`: soundness of
  TM⋆ at every class, TD discharged semantically.
- **Tasks:**
  - [ ] `theorem star_derivable_valid_and_swap_validIn {fc} {φ} (d : StarDerivationTree fc [] φ) : StarValidIn fc φ ∧ StarValidIn fc φ.swapTemporal`
        — mirror `derivable_valid_and_swap_validIn` (`Soundness.lean:1217-1315`) arm by arm:
        `axiom` uses `starAxiom_validIn`/`starAxiom_swap_validIn`; `assumption` is absurd at
        `[]`; `modus_ponens` pointwise; `necessitation` and `temporal_necessitation` from the
        clause lemmas (the `box`/`allFuture` clauses quantify over total histories / later
        times, and `swapTemporal` sends `allFuture` to `allPast`); `temporal_duality` swaps
        the pair using the involution lemma; `weakening` at `[]` is the identity.
  - [ ] `theorem star_soundness_validIn {fc} {φ} : StarDerivable fc [] φ → StarValidIn fc φ`.
  - [ ] `theorem star_soundness_in {fc} (Γ) (φ) (d : StarDerivationTree fc Γ φ) (F) (hF : fc.Sat F) (M) (τ) (hτ : τ.IsTotal) (t) (h_ctx : ∀ ψ ∈ Γ, StarTruthAt M τ t ψ) : StarTruthAt M τ t φ`
        — the context form, mirror of `bl_soundness_in` (`BaseLanguageSoundness.lean:232`);
        obtain it from the `[]` form by the deduction-theorem-free route the L⁺ tree uses
        (`Soundness.lean:1377`'s `soundness (Γ) (φ)` — read its proof and mirror).
  - [ ] Rows `star_soundness_base/dense/discrete/dedekind` and the `StarValid` corollary at
        `.Base`.
  - [ ] Inline `example`: `star_soundness_validIn ⟨stab_necessitation d⟩` typechecks for a
        derivable `d`; `#print axioms star_soundness_validIn` is the standard three.
  - [ ] Build: `lake build FormalSystem.Metalogic.Conservativity.Star.StarSoundness`.
- **Territory:** creates `Conservativity/Star/StarSoundness.lean` only.
- **Estimated output:** ~220 lines. **Done when:** `star_soundness_validIn` and
  `star_soundness_in` build sorry-free at generic `fc`.
- **Timing:** 2 hours
- **Depends on:** 4.2, 5.2, 5.3
- **Verification Tier:** local
- **Scope Hypothesis:** the seven-arm companion recursion transcribes from `Soundness.lean:
  1217-1315` with only the `axiom` arm's callee renamed; if the L⁺ `soundness (Γ) (φ)` proof
  routes through machinery `StarFormula` lacks (e.g. a deduction lemma), the context form is
  restated over the `[]` form plus `weakening`, and the deviation is recorded in the summary.

**Group F — L⋆ conservativity (Phase 6)**

### Phase 6: Forward conservativity via the engines, composed rows, `tmFrag_iff_star`, and `Conservativity/Star` wiring [NOT STARTED]
- **Goal:** Land `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` and the
  `Conservativity/Star.lean` aggregator; wire into `Conservativity.lean` with the "Star"
  docstring section.
- **Tasks:**
  - [ ] `theorem forward_star {fc} (engine : WeakCompleteness fc) (φ : Formula) : StarDerivable fc [] (ofFormula φ) → Derivable fc [] φ`
        := `engine φ ((starValidIn_ofFormula_iff fc φ).mp (star_soundness_validIn h))` — the
        compiled `forward_star_of_sound` shape from the 533 report Appendix A, now with real
        soundness.
  - [ ] Four rows `forward_star_base/dense/discrete/dedekind` from the engines
        (`StrongCompleteness.lean:879/987/1101/775`).
  - [ ] `theorem starDerivable_ofFormula_iff {fc} (engine) (φ) : StarDerivable fc [] (ofFormula φ) ↔ Derivable fc [] φ`
        (backward from Phase 4.2, forward from above) — **proof-theoretic conservativity of TM⋆
        over TM⁺, both directions**; four instantiated rows.
  - [ ] Composed L ⊂ L⋆ backward rows: `theorem star_of_tm {fc} (φ : BLFormula) : BaseLanguage.Derivable fc [] φ → StarDerivable fc [] (ofFormula (tr φ))`
        (`derivable_translate` then `starDerivable_of_derivable`), four class rows; docstring
        stating that the forward direction for this pair inherits the L ⊂ L⁺ status
        (refuted at Base/Discrete, open at Dense/Dedekind) and is not asserted (Postmortem
        rule 1).
  - [ ] `theorem tmFrag_iff_star {fc} (engine) (φ : BLFormula) : TMFrag fc φ ↔ StarDerivable fc [] (ofFormula (tr φ))`
        (one line from `starDerivable_ofFormula_iff`).
  - [ ] Create `FormalSystem/Metalogic/Conservativity/Star.lean` (C8 sibling aggregator)
        importing `Atomization`, `AxiomValidity`, `StarSoundness`, `Forward`, with a module
        docstring: what TM⋆ is, the five files, the exact statement "`Forward⋆` (TM⋆ over TM⁺)
        holds at all four classes, unlike `Forward` (TM⁺ over TM)", and the open items (TM⋆
        completeness, decidability) named as open without promises.
  - [ ] Add `import FormalSystem.Metalogic.Conservativity.Star` to
        `FormalSystem/Metalogic/Conservativity.lean` and a "## The stability extension L⋆ (Star)"
        docstring section there (5-10 lines pointing at `Star.lean`).
  - [ ] Build: `lake build FormalSystem.Metalogic` (the aggregator's dependents).
- **Territory:** creates `Conservativity/Star/Forward.lean`, `Conservativity/Star.lean`; edits
  `FormalSystem/Metalogic/Conservativity.lean` (import + docstring section).
- **Estimated output:** ~200 lines. **Done when:** `starDerivable_ofFormula_iff` builds at all
  four classes and `lake build` is green with every `Star/` module reachable.
- **Timing:** 1.5 hours
- **Depends on:** 1.1, 3.2, 4.2, 5.4
- **Verification Tier:** interface
- **Scope Hypothesis:** ~200 lines assumes `WeakCompleteness fc` unfolds to `∀ ψ, ValidIn fc ψ → Derivable fc [] ψ` (`SetConsequence.lean:234`, read) and that the four engines have exactly that type (`StrongCompleteness.lean:879/987/1101/775`, grep-confirmed); the composed L ⊂ L⋆ rows are four one-liners.

**Group G — documentation and invariants (Phase 7)**

### Phase 7: Documentation, README rows, invariants, and root reachability [NOT STARTED]
- **Goal:** Bring every inventory and count into agreement with the tree and close the task
  with the full gate set green.
- **Tasks:**
  - [ ] Complete `FormalSystem/StarLanguage/README.md` (module list with all three files, the
        import invariant, the extension recipe for adding a `StarAxiom` constructor — the three
        dispatch points from the Design note — phrased without task numbers).
  - [ ] `FormalSystem/Metalogic.lean` module docstring: add the "Star" rows next to the
        Conservativity rows (lines 36-60 pattern); state that the four completeness engines'
        countermodels are deterministic and therefore do not transfer to L⋆ (535 §4.1 — a
        durable fact, cite `FlowFrame.lean:145-160` and `ReynoldsBridge.lean:464`).
  - [ ] `README.md`: metatheory table rows for L (`TMFrag`) and L⋆ (soundness, semantic
        conservativity, proof-theoretic conservativity both directions), and open-problems rows
        for TM⋆ completeness (all-histories semantics) and TM⋆ decidability, citing Reynolds
        2003 and Zanardo 1991 as the nearest literature (535 Recommendation 6) — no promises
        either way (Postmortem rule 10).
  - [ ] Confirm root reachability: every new module is reachable from `FormalSystem` (through
        `Semantics.lean`, `Conservativity.lean`, and `StarLanguage.lean`); if the root
        `FormalSystem.lean` lists `BaseLanguage` explicitly, add `StarLanguage` alongside.
  - [ ] Run `bash scripts/check-module-invariants.sh` (full, with build); fix every C4/C5/C8/
        C9/C12/C13/C14 finding it reports (documented counts in `docs/` and `README.md`).
  - [ ] `#print axioms` for `tmFrag_iff_blValidIn`, `star_soundness_validIn`,
        `starDerivable_ofFormula_iff`, `tm_lt_tmFrag_discrete` recorded in the summary.
  - [ ] Optional (only if time remains in the dispatch): `docs/` note "adding a language
        extension" distilled from `BaseLanguage/` + `StarLanguage/` (533 report Context
        Extension Recommendations).
- **Territory:** edits `FormalSystem/StarLanguage/README.md`, `FormalSystem/Metalogic.lean`
  (docstring only), `README.md`, `docs/**` count lines the invariants script names, and
  optionally the root `FormalSystem.lean` import list.
- **Estimated output:** ~120 lines of prose/docstrings. **Done when:**
  `scripts/check-module-invariants.sh` exits 0 and `lake build` is green.
- **Timing:** 2 hours
- **Depends on:** 1.2, 3.5, 6 (i.e. all)
- **Verification Tier:** full
- **Scope Hypothesis:** the set of files carrying counts/inventories is whatever C5/C12/C14
  flag; enumerate with `grep -rl "BLTruth\|BaseLanguage" README.md docs/ FormalSystem/**/README.md`
  and the script's own output before editing.

## Testing & Validation

- [ ] Per phase: `lake build FormalSystem.<Module>` for the module created (explicit, because
      unwired modules are not built by the root target); `grep -n "sorry" <file>` returns only
      prose.
- [ ] Wiring phases (1.2, 3.5, 6, 7): full `lake build`.
- [ ] Phase 7: `bash scripts/check-module-invariants.sh` (C1-C15) exits 0.
- [ ] `#print axioms` on the four flagship theorems: `propext`, `Classical.choice`,
      `Quot.sound` only.
- [ ] Acceptance tests (inline `example`s, never separate `sorry`-bearing files):
  - `starValidIn_of_plus … (Axiom.modal_future _)` at `⊡p` (Phase 5.1) — the 535 acceptance
    test "`□⊡p → □G⊡p` is an axiom instance and sound".
  - `ofFormula` derived-operator `rfl` pins (Phase 2).
  - `stab_necessitation` derivable (Phase 4.2) and sound (Phase 5.4).
  - `tmFrag_iff_blValidIn completeness_base` and `starDerivable_ofFormula_iff completeness_base`
    typecheck (Phases 1.1, 6).
- [ ] Negative checks: `grep -rn "Forward\b" FormalSystem/Metalogic/Conservativity/Star/
      FormalSystem/Metalogic/Conservativity/Fragment*.lean` shows no asserted `Forward fc`
      statement; `grep -rn "exactly\|iff.*deterministic" FormalSystem/Semantics/StarNonValidities.lean`
      is empty; `grep -rn "task [0-9]" FormalSystem/ README.md docs/` is empty (C9/C9D).
- [ ] No test file under `Tests/BimodalTest/` is required (the base-language work has none);
      the module-level `example`s are the executable checks.

## Artifacts & Outputs

- `specs/533_l_and_lstar_metatheory_conservative_extension/plans/01_l-lstar-metatheory-conservative-extension.md` (this file)
- Lean modules (new): `FormalSystem/StarLanguage/{Formula,Axioms,Derivation}.lean`,
  `FormalSystem/StarLanguage.lean`, `FormalSystem/StarLanguage/README.md`,
  `FormalSystem/Semantics/{StarTruth,StarValidity,StarPasting,StarNonValidities}.lean`,
  `FormalSystem/Metalogic/Conservativity/{Fragment,FragmentCompactness}.lean`,
  `FormalSystem/Metalogic/Conservativity/Star/{Atomization,AxiomValidity,StarSoundness,Forward}.lean`,
  `FormalSystem/Metalogic/Conservativity/Star.lean`
- Edited (import lines / docstrings only): `FormalSystem/Semantics.lean`,
  `FormalSystem/Metalogic/Conservativity.lean`, `FormalSystem/Metalogic.lean`, `README.md`,
  `docs/**` count lines, optionally `FormalSystem.lean`, `FormalSystem/Semantics/README.md`
- `specs/533_l_and_lstar_metatheory_conservative_extension/summaries/01_l-lstar-metatheory-conservative-extension-summary.md`
  (written at implementation close; records `#print axioms` output, which compactness form
  landed in 1.2, and any Scope Hypothesis that was corrected)

## Rollback/Contingency

- Every phase is new-file-only except the four aggregator/docstring edits (1.2, 3.5, 6, 7).
  Rollback of any phase = delete its files and revert its import lines; no landed file is ever
  modified, so the tree returns to today's state exactly.
- If Phase 3.3's SS mirror (`snce_dstab_valid`) blocks: Phase 5.3's `untl_paste` swap arm is
  the only consumer. Contingency: prove that one arm through a `StarFormula` `TruthAntiIso`
  twin (copy `Truth.lean:1092-1130`'s six-constructor induction, add the `stab` case via
  `forall_congr'` over `I.hist` with `SameStateAt` transported through `I.hist`/`I.dur`) applied
  to a time-reversed model — the tool 535 §8.3 names — as a new file
  `Conservativity/Star/AntiIso.lean` (~200 lines, one extra sub-phase 5.3.1 is NOT allowed by
  the heading rule; open it as Phase 5.5 in the next wave). Never fall back to a proof-theoretic
  mirror.
- If Phase 5.1's encoding cannot be built classically from `Denumerable` instances: use
  `Atom`'s `freshIndex : Option Nat` to construct an explicit injection from a `Nat`-encoding of
  `StarFormula` (via `Encodable`) into fresh atoms with a reserved base string; the transfer
  lemma is unchanged.
- If Phase 1.2's list pullback along `tr` resists: land the model-existence form (see its Scope
  Hypothesis) and record the shape; do not weaken to a single class.
- If any phase cannot close sorry-free within its dispatch: close it `[BLOCKED]` with the goal
  state and the last attempted tactic recorded in the summary, leave its file unwired (so C3
  and the build stay green), and continue with phases not depending on it. No `sorry` is ever
  committed under `FormalSystem/`.
