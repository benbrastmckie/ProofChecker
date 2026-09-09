# Implementation Plan: Star proof theory and conservativity

- **Task**: 573 - Star proof theory and conservativity
- **Status**: [COMPLETED]
- **Effort**: 14 hours
- **Dependencies**: None (every consumed asset is landed)
- **Research Inputs**: `specs/573_star_proof_theory_and_conservativity/reports/01_star-proof-theory-conservativity.md`
- **Artifacts**: plans/01_star-proof-theory-conservativity.md (this file), summaries/01_star-proof-theory-conservativity-summary.md
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

Build TM⋆ — the proof system for L⋆ — and land the conservativity verdict Phase 0 established.
The system is `StarAxiom` (one `ofBase` constructor embedding all 45 TM⁺ schemata at `ofPlus`
instances, plus 16 register schemata) and `StarDerivationTree` with notation `⊢⋆[fc]`, mirroring
`PlusAxiom`/`PlusDerivationTree`/`⊢⁺[fc]` constructor for constructor. Soundness at all four frame
classes follows by the companion recursion that carries validity and swap-validity together, the
`ofBase` block discharged in two lines by transporting `plusAxiom_validIn_min` /
`plusAxiom_swap_validIn_min` along `starValidOnFrames_ofPlus`. Done means: `lake build` green, no
new `sorry`, C2/C3/C9/C14/C15/C24/C26 green, and the conservativity row stated at the strength the
research actually supports — unconditionally over TM, conditionally-plus-contrapositive over TM⁺,
with TM⋆ completeness recorded as OPEN under two named obstructions.

### Research Integration

The Phase 0 report is consumed, not re-derived. The five findings that shape this plan:

1. **MF (`modal_future`, `□φ → □Gφ`) does not transfer schematically to `StarFormula`** — refuted
   over `NF` at `φ := ↓¹p → p`, because `starTruthAt_timeShift` shifts the register vector along
   with the history. MF is the sole `timeShift` consumer in the TM schema block. Consequence: no
   TM schema may be re-declared over `StarFormula` by fiat; `ofBase` is the only sound route, and
   the report's optional `RegFree`-guarded MF re-declaration is **omitted** (Non-Goals).
2. **The register axiomatization is derivable from the truth clauses and mostly `Iff.rfl`** — the
   report's ACCEPT table (S1–S10) supplies each schema with its machine-checked proof shape. The
   dispatch's candidate `↑ⁱ↓ⁱφ ↔ φ` is refuted; the correct law is `↑ⁱ↓ⁱφ ↔ ↑ⁱφ`.
3. **Naive register erasure is not a conservativity translation** — `↑¹G↓¹p → p` is `StarValid`
   while its erasure `Gp → p` is refuted over `NF`. Register collapse fails too, on the rigidity
   schema. Both routes to a syntactic translation are closed.
4. **TM⁺-conservativity is sandwiched inside the tree's own open problem** — given TM⋆ soundness,
   any separating witness for non-conservativity *is* a TM⁺ completeness failure. So the verdict
   is neither "true" nor "false" but a proved conditional pair, which is what Phase 8 states.
5. **TM⋆ completeness is not reachable and the obstruction is nameable** — every existing engine
   produces deterministic countermodels, every deterministic frame validates `sentDet`, and
   `sentDet` is not `StarValid`. Separately, the hybrid pure-axiom/PASTE route needs nominals,
   which L⋆ has none of. No completeness phase is planned; the obstruction is recorded instead.

**One correction to the report's own Phase 1 recommendation.** The report lists
`IsPureFuture`/`IsPurePast` and `RegFree` on `StarFormula` as Phase 1 work. Under the settled
`ofBase` decision neither is consumed: `PlusAxiom.paste` and `PlusAxiom.untl_paste` carry their
purity hypotheses on `PlusFormula`, so `ofBase` needs no `StarFormula`-side purity predicate, and
`RegFree` exists only to guard a re-declared MF that this plan does not declare. Both are moved to
Non-Goals rather than built unused. This is a scope reduction against the report, recorded here so
it reads as a decision rather than an omission.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

No `roadmap_path` was supplied in this dispatch and no roadmap consultation was performed.

## Goals & Non-Goals

**Goals**:

- Land the syntax scaffolding `StarFormula.swapTemporal`, `swap_temporal_involution`,
  `ofPlus_swapTemporal` in `FormalSystem/StarLanguage/Formula.lean`.
- Record the three machine-checked non-validities that justify the design — `mfWitness`,
  `refute_modal_future`, `storeG_recall_valid`, `refute_erasure` — in
  `FormalSystem/Semantics/StarNonValidities.lean`, so the reason MF is unavailable and erasure is
  not a translation lives in the tree rather than only in a spec artifact.
- Declare the proof system: `StarAxiom`, `StarAxiom.minFrameClass`, `StarDerivationTree`,
  `StarDerivable`, and the notation `⊢⋆[fc]`.
- Prove per-schema validity and swap-validity: `starAxiom_validIn_min`,
  `starAxiom_swap_validIn_min`.
- Prove soundness of TM⋆ at every frame class: `star_derivable_valid_and_swap_validIn`,
  `star_soundness_validIn`.
- Land the embedding `StarAxiom.minFrameClass_ofBase`, `StarDerivationTree.ofPlusTree`,
  `starDerivable_of_plusDerivable`, `starDerivable_of_derivable`.
- Land the conservativity trio: `forward_star`, `starDerivable_ofFormula_iff`,
  `starConservative_of_plusComplete`, `plusIncomplete_of_starNonconservative`.
- Update `FormalSystem/StarLanguage/README.md`, `FormalSystem/Metalogic/Conservativity/README.md`
  and the `Plus/README.md` metatheory rows so the TM⋆ status — proved, conditional, and open — is
  stated plainly with its obstructions and citations.

**Non-Goals**:

- **TM⋆ completeness at any frame class.** Not attempted, not sorried, not stubbed. Recorded as
  OPEN with the two obstructions named (Phase 9).
- **A re-declared `modal_future` over `StarFormula`, with or without a `RegFree` side condition.**
  MF is available through `ofBase` at every `ofPlus` instance, which is everything Phases 5–8
  consume. `RegFree` is therefore not built.
- **`IsPureFuture` / `IsPurePast` on `StarFormula`.** Not consumed under the `ofBase` design (see
  the correction above). If a later task re-declares the pasting schemata natively it will need
  them; nothing here does.
- **The coincidence lemma and the register-closure axiom S11 (`↑ⁱφ ↔ φ` for `i` not free in
  `φ`).** Needs `NotFreeReg` plus an inductive coincidence argument, consumed by nothing in this
  plan.
- **Register renaming / normal forms.** Needs a register substitution; nothing consumes it.
- **An L⋆ atomization.** Provably cannot exist over the same frame: neither `↓ⁱχ` nor `↑ⁱχ` is
  state-determined, so `stab_state_only` fails. Do not attempt one.
- **Re-declaring the 45 TM schemata over `StarFormula`.** Settled in the prior-decision record;
  the recorded cost is that TM temporal schemata are available only at register-free instances.
- **Any argument by uniform substitution.** Unsound here; TM⁺ is already not substitution-closed
  via `atom_stab`.
- **Any write to the manuscript or draft manuscript prose.**
- **World registers `↑_M` / `↓_M`**, and any `Det-m` half.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| `ofPlus_swapTemporal` is not `rfl`-shaped, breaking the `ofBase` swap arm | H | L | Phase 1 proves this pin **first** and stops if it needs more than the structural induction `ofFormula_swapTemporal` uses. Every later swap obligation routes through it. |
| A register schema in the ACCEPT table fails once stated at formula level rather than truth level (e.g. `.iff` unfolding through `and`/`neg` blocks an `Iff.rfl`) | M | M | The report checked each schema semantically; the formula-level `.iff` unfolds through `StarTruth.and_iff` plus the clause lemmas. If an arm resists, drop that single constructor and record it as a reasoned exclusion — do not weaken a neighbouring arm to cover it. |
| The `StarAxiom` set is not swap-closed, so `starAxiom_swap_validIn_min` has an unprovable arm | H | L | The constructor list is chosen swap-closed by construction (S1–S7, S9 self-dual; the four rigidity arms pair; `recall_export_until`/`recall_export_since` pair). Phase 3 must verify swap-closure constructor-by-constructor before Phase 6 starts. |
| The soundness companion recursion's termination argument does not transfer | M | L | It is `plus_derivable_valid_and_swap_validIn` verbatim, well-founded on `d.height` with the same `weakening` re-target. Phase 4 must land `height`, `ofWeakeningNil`, `height_ofWeakeningNil_lt` and the two `mp_height_gt_*` lemmas, or Phase 7 cannot close. |
| The `⊢⋆[fc]` notation collides with an existing parse | M | L | `⊢[fc]`, `⊢⁻[fc]`, `⊢⁺[fc]` already coexist at precedence 50; `⊢⋆[fc]` is a fourth distinct token. Phase 4 is tiered `full` for exactly this reason. |
| Documentation drift: `StarLanguage/README.md` currently declares the four names "reserved, unbuilt" and TM⋆ "**Excluded**" | M | H | Phase 3 rewrites the reserved-names section in the same commit that declares `StarAxiom`; Phase 9 rewrites the correspondence row and the metatheory rows. C15 (paper anchors) and C14 (documented counts) are re-run in Phase 9. |
| C9 forbids task-number citations under `FormalSystem/` | M | M | No new module or README may cite a task number. Cite declaration names and paper anchors only. |
| The conservativity verdict reads as a shortfall in the docs | M | M | Phase 9's wording is prescribed: the TM⁺ row is a *proved conditional pair* placing the question inside the tree's recorded open problem, and the TM row is an unconditional two-directional conservative-extension theorem. Neither is a failure. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2, 3 | -- |
| 2 | 4, 6 | 1, 3 |
| 3 | 5, 7 | 4, 6 |
| 4 | 8 | 5, 7 |
| 5 | 9 | 2, 8 |

Phases within the same wave can execute in parallel. Each phase owns a disjoint file set; the
owning file is named in every phase's **Files to modify** block.

### Phase 1: `StarFormula.swapTemporal` and the `ofPlus` pin [COMPLETED]

**Goal**: Give `StarFormula` the temporal-duality involution that `StarDerivationTree`'s
`temporal_duality` rule and the whole swap-validity half of soundness require, with the `ofPlus`
commutation pin that makes the `ofBase` swap arm free.

**Tasks**:
- [ ] Add `StarFormula.swapTemporal` mirroring `PlusFormula.swapTemporal` constructor for
      constructor, with `timeStore i φ ↦ timeStore i φ.swapTemporal` and
      `timeRecall i φ ↦ timeRecall i φ.swapTemporal` (registers hold times and are unoriented).
- [ ] Prove `swap_temporal_involution` by the same induction `PlusFormula.swap_temporal_involution`
      uses, extended with the two register cases.
- [ ] Prove `ofPlus_swapTemporal : ofPlus φ.swapTemporal = (ofPlus φ).swapTemporal`, mirroring
      `ofFormula_swapTemporal` (`PlusLanguage/Formula.lean`). **Do this pin first** — every later
      swap obligation routes through it.
- [ ] Add the push-through lemmas the later phases actually consume (`swap_temporal_all_future`
      and `swap_temporal_all_past` analogues), following the `PlusFormula.swap_temporal_*` family.
- [ ] Update the `StarLanguage/Formula.lean` module docstring's Main Results list and
      `StarLanguage/README.md`'s `Formula.lean` module-table row.

**Timing**: 1 hour

**Depends on**: none

**Verification Tier**: full

**Files to modify**:
- `FormalSystem/StarLanguage/Formula.lean` - add `swapTemporal`, `swap_temporal_involution`,
  `ofPlus_swapTemporal`, the push-through family; extend the docstring
- `FormalSystem/StarLanguage/README.md` - the `Formula.lean` module-table row only

**Verification**:
- `lake build` green; `grep -c sorry` unchanged under `FormalSystem/`
- `example (φ : PlusFormula) : ofPlus φ.swapTemporal = (ofPlus φ).swapTemporal := rfl` succeeds,
  or the pin is recorded as needing induction (which is still fine — `ofFormula_swapTemporal` is
  itself an induction)
- `bash scripts/check-module-invariants.sh --no-build` green (C9, C15, C26)

---

### Phase 2: The non-validity record [COMPLETED]

**Goal**: Put the three machine-checked refutations that justify this plan's design into the tree,
so a future reader who reaches for a schematic MF or a register-erasure translation finds a
theorem saying why not, rather than nothing.

**Tasks**:
- [ ] Add `mfWitness (p : Atom) : StarFormula := .imp (.timeRecall 1 (.atom p)) (.atom p)`.
- [ ] Prove `refute_modal_future : ¬ NF.StarValidOn (.imp (.box (mfWitness p)) (.box (allFuture
      (mfWitness p))))` over `NF` at `x = 0`, `v ≡ 0`, with the history
      `σ = fun s => if s ≤ 0 then 0 else 1` and `s = 1`, following the `refute_sentDet` shape
      (`h.apply_total` + explicit `natHist` witnesses + `StarTruth.allFuture_iff`).
- [ ] Prove `storeG_recall_valid : StarValid (.imp (.timeStore 1 (allFuture (.timeRecall 1 (.atom
      p)))) (.atom p))` via `StarValid.of_forall_total`, `exists_gt`, `Function.update_self`.
- [ ] Prove `refute_erasure : ¬ StarValid (.imp (allFuture (.atom p)) (.atom p))` over `NF` at
      `τ = fun s => if s ≤ 0 then 1 else 0`, `x = 0`.
- [ ] Extend the module docstring: MF is the sole `timeShift` consumer in the TM schema block, and
      the erasure pair is why no register-erasing translation can serve conservativity. Cite
      `def:BLstar-semantics` and declaration names only — no task numbers (C9).

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Scope Hypothesis**: This phase asserts exactly three refutations plus one witness definition
(four new declarations). Confirm at implementation time by re-reading the report's Appendix
"Machine-checked statements" block: if a fourth refutation from the REJECT table
(`↑ⁱ↓ⁱφ ↔ φ`, `↓ⁱ⊡φ → ⊡↓ⁱφ`) proves as cheap to transcribe, adding it is in scope; if any of the
three named above resists, it is a reasoned exclusion, not a weakened restatement.

**Files to modify**:
- `FormalSystem/Semantics/StarNonValidities.lean` - the four declarations and the docstring
  extension

**Verification**:
- `lake build` green; zero new `sorry`
- Each new theorem has a `#print axioms` line consistent with the module's existing baseline
- `bash scripts/check-module-invariants.sh` green (C3, C9, C14, C26)

---

### Phase 3: `StarAxiom` and `StarAxiom.minFrameClass` [COMPLETED]

**Goal**: Declare the TM⋆ axiom set as one `ofBase` constructor over `PlusAxiom` plus the register
schemata from the report's ACCEPT table, routed to their minimum frame classes.

**Tasks**:
- [ ] Create `FormalSystem/StarLanguage/Axioms.lean` importing `StarLanguage.Formula` and
      `PlusLanguage.Axioms` (never `FormalSystem.Semantics.*` — the `StarLanguage/` module
      invariant).
- [ ] Declare `StarAxiom : StarFormula → Type` with:
      `ofBase (φ : PlusFormula) (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)`, and the register
      arms `store_recall_same`, `recall_store_same`, `recall_recall`, `store_store_comm`,
      `store_k`, `recall_k`, `store_box`, `recall_box`, `store_stab`, `store_atom`,
      `recall_rigid_future`, `future_rigid_recall`, `recall_rigid_past`, `past_rigid_recall`,
      `recall_export_until`, `recall_export_since` — statements exactly as pinned in
      `## Lean Challenge Statements`.
- [ ] Define `StarAxiom.minFrameClass` with `| .ofBase _ ax => ax.minFrameClass` and `| _ => .Base`
      (every register schema is valid over every task frame).
- [ ] Add `example` pins: `(StarAxiom.ofBase _ (PlusAxiom.density φ)).minFrameClass = .Dense` and
      `(StarAxiom.store_box i φ).minFrameClass = .Base`, both by `rfl`.
- [ ] **Verify swap-closure constructor by constructor before closing the phase**: S1–S7 and S9
      are self-dual (their `.iff` shapes swap to themselves at swapped arguments, `stab` being
      swap-fixed); the four rigidity arms pair G↔H; `recall_export_until` and
      `recall_export_since` pair. Record the check in the module docstring as a stated invariant.
- [ ] Wire `FormalSystem/StarLanguage/Axioms.lean` into `FormalSystem/StarLanguage.lean` in the
      same commit (C24: every module in the root closure transitively imports `FormalSystem.Init`).
- [ ] Rewrite `StarLanguage/README.md`'s "Reserved and unbuilt" section and
      `StarLanguage.lean`'s corresponding docstring section: `StarAxiom` is now declared;
      `StarDerivationTree`, `⊢⋆[fc]` and `TM⋆` land in Phase 4.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: interface

**Scope Hypothesis**: 17 constructors (1 `ofBase` + 16 register arms), giving 34 proof obligations
in Phase 6. This count is a hypothesis from the report's ACCEPT table, not a fact. Confirm by
counting `^  | ` lines in the finished inductive and reconciling against the ACCEPT table; if an
arm is dropped or split, update Phase 6's Scope Hypothesis in the same commit rather than letting
the two drift.

**Files to modify**:
- `FormalSystem/StarLanguage/Axioms.lean` - new module
- `FormalSystem/StarLanguage.lean` - import the new module, extend the Modules list
- `FormalSystem/StarLanguage/README.md` - module table row; rewrite "Reserved and unbuilt"

**Verification**:
- `lake build` green; both `minFrameClass` pins close by `rfl`
- `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/` returns nothing (module
  invariant)
- `bash scripts/check-module-invariants.sh` green (C24 closure, C26 camelCase `def`, C9, C15)

---

### Phase 4: `StarDerivationTree`, `⊢⋆[fc]`, and `StarDerivable` [COMPLETED WITH EXCLUSIONS]

**Goal**: Declare the TM⋆ proof system as a constructor-for-constructor copy of
`PlusDerivationTree`, with the structural apparatus the soundness recursion needs.

**Tasks**:
- [ ] Create `FormalSystem/StarLanguage/Derivation.lean` importing `StarLanguage.Axioms`.
- [ ] Declare `StarDerivationTree (fc : FrameClass) : StarContext → StarFormula → Type` with the
      seven rules `axiom` (gated by `h.minFrameClass ≤ fc`), `assumption`, `modus_ponens`,
      `necessitation`, `temporal_necessitation`, `temporal_duality`, `weakening` — verbatim the
      `PlusDerivationTree` shape.
- [ ] Add `notation:50 Γ " ⊢⋆[" fc "] " φ => StarDerivationTree fc Γ φ` and the empty-context form
      `notation:50 "⊢⋆[" fc "] " φ => StarDerivationTree fc [] φ`, at the same precedence as
      `⊢[fc]` / `⊢⁻[fc]` / `⊢⁺[fc]`.
- [ ] Define `StarDerivable (fc) (Γ) (φ) : Prop := Nonempty (StarDerivationTree fc Γ φ)` and prove
      `StarDerivable.mono`.
- [ ] Add the structural apparatus Phase 7 consumes: `lift`, `height`, `ofWeakeningNil`,
      `height_ofWeakeningNil`, `height_ofWeakeningNil_lt`, `mp_height_gt_left`,
      `mp_height_gt_right` — each mirroring its `PlusDerivationTree` counterpart.
- [x] Add a derived `⊡`-necessitation (`⊢⋆[fc] φ → ⊢⋆[fc] StarFormula.stab φ`, via `necessitation`
      then `ofBase (PlusAxiom.box_stab _)`), mirroring the `PlusDerivationTree` derived rule so the
      7-rule mirror stays exact. *(deviation: altered — landed as `stabNecessitationOfPlus`, at
      `ofPlus` instances only; the general form is not derivable from the Phase 3 axiom set. See
      the Reasoned Exclusions record below.)*
- [ ] Wire into `FormalSystem/StarLanguage.lean`; finish the "Reserved and unbuilt" rewrite begun
      in Phase 3 (all four names are now declared).

**Timing**: 1.5 hours

**Depends on**: 1, 3

**Verification Tier**: full

#### Reasoned Exclusions

| Item | Reason | Evidence |
|---|---|---|
| `⊡`-necessitation at an arbitrary `φ : StarFormula` (`⊢⋆[fc] φ → ⊢⋆[fc] StarFormula.stab φ`), as the phase's bullet spells it | Not derivable from the Phase 3 axiom set, and the bullet's own prescribed route is what shows why. MS reaches TM⋆ only as `StarAxiom.ofBase _ (PlusAxiom.box_stab ψ)`, whose type is `StarAxiom (ofPlus ((box ψ).imp (stab ψ)))` — i.e. `□(ofPlus ψ) → ⊡(ofPlus ψ)`. There is no instance at a register-containing formula, so `modus_ponens` cannot be applied at one. Widening `StarAxiom` with a native `box_stab` arm would fix this and would be sound, but that constructor list is pinned in `## Lean Challenge Statements` at one embedding arm plus sixteen register arms, and adding an eighteenth would break the pinned statement. | `FormalSystem/StarLanguage/Derivation.lean` — `stabNecessitationOfPlus` is stated at `{ψ : PlusFormula}` and closes; the general form has no `StarAxiom` instance to feed `modus_ponens`. The rule remains **sound** at every `φ` (the `stab` clause restricts the `box` clause's quantifier), so this is an underivability, not an unsoundness, and it is recorded in the module docstring and in `StarLanguage/README.md` rather than papered over. Nothing in Phases 5–8 consumes it. |

**Files to modify**:
- `FormalSystem/StarLanguage/Derivation.lean` - new module
- `FormalSystem/StarLanguage.lean` - import, Modules list
- `FormalSystem/StarLanguage/README.md` - module table row; close out "Reserved and unbuilt"

**Verification**:
- `lake build` green across the whole tree (the notation is global — this is why the tier is
  `full`)
- The seven constructor names and arities match `PlusDerivationTree`'s one for one
- `bash scripts/check-module-invariants.sh` green (C24, C26, C9)

---

### Phase 5: The embedding `⊢⁺[fc] φ → ⊢⋆[fc] (ofPlus φ)` [COMPLETED]

**Goal**: Deliverable (3): every TM⁺ theorem is a TM⋆ theorem at its embedded formula, by a
seven-case structural recursion.

**Tasks**:
- [ ] Create `FormalSystem/StarLanguage/Embedding.lean` importing `StarLanguage.Derivation` and
      `PlusLanguage.Derivation`.
- [ ] Prove `StarAxiom.minFrameClass_ofBase : (StarAxiom.ofBase φ ax).minFrameClass =
      ax.minFrameClass` (by `rfl` under the Phase 3 definition), mirroring
      `PlusAxiom.minFrameClass_ofTM`.
- [ ] Define `StarDerivationTree.ofPlusTree : PlusDerivationTree fc Γ φ → StarDerivationTree fc
      (ofStarCtx Γ) (ofPlus φ)`, seven cases: `axiom` via `ofBase` plus `minFrameClass_ofBase`,
      `assumption` via `mem_ofStarCtx`, `temporal_duality` transporting along `ofPlus_swapTemporal`
      (Phase 1), the rest structural. Verbatim the shape of `PlusDerivationTree.ofTM`.
- [ ] Prove `starDerivable_of_plusDerivable : PlusDerivable fc Γ φ → StarDerivable fc (ofStarCtx Γ)
      (ofPlus φ)`.
- [ ] Prove the composed `starDerivable_of_derivable : ProofSystem.Derivable fc [] φ →
      StarDerivable fc [] (ofPlus (ofFormula φ))` by composing with `plusDerivable_of_derivable`.
      This is the backward half of Phase 8's biconditional.
- [ ] Wire into `FormalSystem/StarLanguage.lean`.

**Timing**: 1 hour

**Depends on**: 4

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/StarLanguage/Embedding.lean` - new module
- `FormalSystem/StarLanguage.lean` - import, Modules list
- `FormalSystem/StarLanguage/README.md` - module table row

**Verification**:
- `lake build` green; no `sorry`
- All seven `PlusDerivationTree` constructors are matched (no wildcard arm in `ofPlusTree`)
- `bash scripts/check-module-invariants.sh` green

---

### Phase 6: Per-schema validity and swap-validity [COMPLETED]

**Goal**: The two dispatch lemmas — every `StarAxiom` constructor is valid at its own minimum
frame class, and so is its temporal dual — with the `ofBase` block discharged by transport rather
than re-proof.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` importing
      `StarLanguage.Axioms`, `Semantics.StarValidity`, and
      `Metalogic.Conservativity.Plus.AxiomValidity`.
- [ ] Prove the `ofBase` arm of `starAxiom_validIn_min` by
      `(starValidOnFrames_ofPlus _ _).mpr (plusAxiom_validIn_min ax)` — two lines, no re-proof of
      45 schemata. **Do not attempt an L⋆ atomization**; it provably cannot exist.
- [ ] Prove the 16 register arms of `starAxiom_validIn_min` from the report's ACCEPT table, using
      the recorded proof shapes: `Iff.rfl` / `simp [StarTruthAt]` for S1–S7 and S9;
      `rw [StarTruth.allFuture_iff]` / `allPast_iff` plus `serial_future` / `serial_past` and K for
      the four rigidity arms; `rw [and_iff, untl_iff, untl_iff, timeRecall_iff]` + `constructor`
      for the two export arms.
- [ ] Prove `starAxiom_swap_validIn_min`: the `ofBase` arm by `plusAxiom_swap_validIn_min`
      transported along `ofPlus_swapTemporal` and `starValidOnFrames_ofPlus`; each register arm by
      computing `swapTemporal` (definitional under Phase 1) and reusing the matching validity arm
      established by Phase 3's swap-closure check.
- [ ] Add the `.mono`-lifted forms `starAxiom_validIn` / `starAxiom_swap_validIn`, mirroring the
      `plusAxiom_validIn` / `plusAxiom_swap_validIn` pair.
- [ ] Create the aggregator `FormalSystem/Metalogic/Conservativity/Star.lean` and import it from
      `FormalSystem/Metalogic/Conservativity.lean` in the same commit (C24).

**Timing**: 2 hours

**Depends on**: 1, 3

**Verification Tier**: interface

**Scope Hypothesis**: 34 proof obligations (17 constructors × validity + swap-validity), of which
2 are the `ofBase` transport pair and 32 are register arms. *(Confirmed: the finished Phase 3
inductive has exactly 17 constructors, and both dispatch lemmas match all 17 by name with no
wildcard arm. The 16 register schemata are additionally landed as named `starValid_*` lemmas, so
each swap arm reuses its validity arm at swapped arguments rather than re-proving it.)* Confirm at implementation time against
the finished Phase 3 inductive by checking that both dispatch lemmas match every constructor with
**no wildcard arm** — a wildcard would silently hide a missing case. If an arm resists proof,
close it as a reasoned exclusion (drop the constructor in Phase 3 and re-verify swap-closure);
never restate the schema in weakened form under the same name.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean` - new module
- `FormalSystem/Metalogic/Conservativity/Star.lean` - new aggregator
- `FormalSystem/Metalogic/Conservativity.lean` - import the new aggregator

**Verification**:
- `lake build` green; zero `sorry`
- Neither dispatch lemma contains a wildcard `| _ =>` arm
- `bash scripts/check-module-invariants.sh` green (C3, C24, C26)

---

### Phase 7: Soundness of TM⋆ [COMPLETED]

**Goal**: Deliverable (2). Every TM⋆ theorem at `fc` is `StarValidIn fc`, with temporal duality
discharged semantically by carrying swap-validity alongside.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean`.
- [ ] Prove `star_derivable_valid_and_swap_validIn : StarDerivationTree fc [] φ → StarValidIn fc φ
      ∧ StarValidIn fc φ.swapTemporal`, mirroring `plus_derivable_valid_and_swap_validIn` arm for
      arm: `termination_by d.height`, with the same `decreasing_by` block and the same
      `weakening` re-target through `ofWeakeningNil`.
- [ ] Prove `star_soundness_validIn : StarDerivable fc [] φ → StarValidIn fc φ` and the per-class
      rows at `.Base`, `.Dense`, `.ZTime`, `.RTime`, mirroring `plus_soundness_validIn` /
      `plus_soundness_in`.
- [ ] Prove consistency at `.Base` (`¬ StarDerivable FrameClass.Base [] StarFormula.bot`),
      mirroring the TM⁺ row.
- [ ] Record in the module docstring that necessitation, temporal necessitation and temporal
      duality are all sound over register-containing formulas because `StarValidIn` quantifies the
      register vector universally and every register clause maps a point to a point — and that no
      argument here uses uniform substitution.
- [ ] Wire into `FormalSystem/Metalogic/Conservativity/Star.lean`.

**Timing**: 1.5 hours

**Depends on**: 4, 6

**Verification Tier**: interface

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` - new module
- `FormalSystem/Metalogic/Conservativity/Star.lean` - import

**Verification**:
- `lake build` green; zero `sorry`; the recursion elaborates without a `decreasing_by` failure
- `#print axioms star_soundness_validIn` recorded and consistent with the TM⁺ counterpart
- `bash scripts/check-module-invariants.sh` green

---

### Phase 8: Conservativity [COMPLETED]

**Goal**: Deliverable (4), at the strength Phase 0 established: an unconditional two-directional
conservative-extension theorem over TM, plus the proved conditional pair that places TM⁺
conservativity inside the tree's own recorded open problem.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Conservativity/Star/Forward.lean`.
- [ ] Prove `forward_star {fc} (engine : WeakCompleteness fc) (φ : Formula) : StarDerivable fc []
      (ofPlus (ofFormula φ)) → ProofSystem.Derivable fc [] φ`, by TM⋆ soundness (Phase 7), then
      `starValidOnFrames_ofPlus`, then `plusValidIn_ofFormula_iff`, then the engine. **No TM⁺
      completeness is needed** — this is the unconditional half.
- [ ] Prove `starDerivable_ofFormula_iff {fc} (engine) (φ : Formula) : StarDerivable fc [] (ofPlus
      (ofFormula φ)) ↔ ProofSystem.Derivable fc [] φ`, backward by `starDerivable_of_derivable`
      (Phase 5). Add the four per-class rows `_base`, `_dense`, `_ztime`, `_rtime` via
      `completeness_base` / `_dense` / `_ztime` / `_rtime`, mirroring
      `plusDerivable_ofFormula_iff`. **This is the headline: the L ⊂ L⋆ row.**
- [ ] Prove `starConservative_of_plusComplete {fc} (h : ∀ ψ : PlusFormula, PlusValidIn fc ψ →
      PlusDerivable fc [] ψ) (φ : PlusFormula) : StarDerivable fc [] (ofPlus φ) → PlusDerivable fc
      [] φ` — the conditional L⁺ ⊂ L⋆ row.
- [ ] Prove its unconditional contrapositive `plusIncomplete_of_starNonconservative {fc} (φ :
      PlusFormula) (hd : StarDerivable fc [] (ofPlus φ)) (hnd : ¬ PlusDerivable fc [] φ) : ¬ (∀ ψ :
      PlusFormula, PlusValidIn fc ψ → PlusDerivable fc [] ψ)` — any separating witness for
      non-conservativity is, verbatim, a witness of TM⁺ incompleteness.
- [ ] Write the module docstring to state plainly what is and is not proved: TM⋆ is an
      unconditional conservative extension of TM at all four classes; TM⁺-conservativity is
      equivalent-modulo-soundness to the tree's open general TM⁺ completeness problem, and is
      therefore stated as the conditional pair rather than asserted or denied. Name the two closed
      translation routes (naive erasure, refuted by Phase 2's `storeG_recall_valid` /
      `refute_erasure`; register collapse, which sends the rigidity schema to a TM⁺ non-theorem).
- [ ] Wire into `FormalSystem/Metalogic/Conservativity/Star.lean`.

**Timing**: 2 hours

**Depends on**: 5, 7

**Verification Tier**: full

**Scope Hypothesis**: 3 headline theorems plus 4 per-class rows plus `forward_star` = 8 new
declarations. *(Confirmed against `Conservativity/Plus/Forward.lean`'s row structure at
implementation time, and widened by 4: that file carries `forward_plus_base`/`_dense`/`_ztime`/
`_rtime` alongside the `plusDerivable_ofFormula_iff_*` rows, so `Forward.lean` here mirrors both
families and lands 12 declarations. `MainResults.lean` was not touched and no flagship theorem's
axiom set was affected, so no C2 re-baseline arises.)* Confirm against `Conservativity/Plus/Forward.lean`'s own row structure at
implementation time; if `MainResults.lean` or a flagship theorem's axiom set is touched, the C2
baseline must be re-measured and the divergence treated as a HARD STOP, not re-baselined.

**Files to modify**:
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` - new module
- `FormalSystem/Metalogic/Conservativity/Star.lean` - import

**Verification**:
- `lake build` green; zero `sorry`
- `#print axioms starDerivable_ofFormula_iff_base` recorded; compare against
  `plusDerivable_ofFormula_iff_base`
- `bash scripts/check-module-invariants.sh` green — C2 flagship axiom sets unchanged, C3 zero
  structural sorry, C14 documented counts match

---

### Phase 9: Documentation, metatheory rows, and the completeness OPEN record [COMPLETED]

**Goal**: Make the tree's prose say exactly what landed — including that TM⋆ completeness is open,
under two named obstructions with citations, and not a shortfall.

**Tasks**:
- [ ] `FormalSystem/StarLanguage/README.md`: add correspondence-table rows for the proof system
      (`StarAxiom`, `StarDerivationTree`, `⊢⋆[fc]`, `TM⋆` — replacing the current
      "**Excluded**: … reserved, unbuilt names" row), for TM⋆ soundness, for the embedding, and
      for the conservativity verdict. Add a module-table row per new `StarLanguage/` module.
- [ ] `FormalSystem/Metalogic/Conservativity/Plus/README.md` metatheory table: add the TM⋆ rows —
      *TM⋆ soundness, all four classes* (**landed**); *TM⋆ conservative over TM, both directions,
      all four classes* (**landed**); *TM⋆ conservative over TM⁺* (**CONDITIONAL on general TM⁺
      completeness**, with the contrapositive named); *TM⋆ completeness, any class* (**OPEN**).
- [ ] `FormalSystem/Metalogic/Conservativity/README.md` and
      `FormalSystem/Metalogic/Conservativity/Star/README.md` (new): the module inventory and key
      results for the new `Star/` directory.
- [ ] Write the completeness OPEN record with **both** obstructions named, never a bare "open":
      (a) the engine obstruction — all four TM completeness engines produce deterministic
      countermodels, every deterministic frame validates `sentDet` (`sentDet_of_deterministic`),
      and `sentDet` is not `StarValid` (`refute_sentDet`, `not_starValid_sentDet`), so no existing
      engine can countermodel `¬ sentDet p`; and note this is strictly worse than the L⁺ case
      because registers do not collapse on deterministic frames, so the "narrow to the
      deterministic class" escape has no L⋆ analogue; (b) the literature obstruction — the
      standard hybrid pure-axiom/PASTE completeness route requires nominals, and L⋆ has none.
      Cite SEP *Temporal Logic* §7.1, Blackburn–de Rijke–Venema §7.3, Goranko 1996, Reynolds 2003,
      Zanardo 1991.
- [ ] Update `FormalSystem/Metalogic/README.md`'s directory inventory row for `Conservativity/`
      (file and line counts) and add the `Star/` entry where the inventory tables require it.
- [ ] Re-check every asserted count and every paper anchor: C14 (documented axiom/sorry counts) and
      C15 (paper-anchor resolution) both read prose, so this phase can break them.
- [ ] Confirm no new file or README under `FormalSystem/` cites a task number (C9).

**Timing**: 1.5 hours

**Depends on**: 2, 8

**Verification Tier**: local

**Scope Hypothesis**: 5 documentation sites are enumerated above (`StarLanguage/README.md`,
`Conservativity/Plus/README.md`, `Conservativity/README.md`, new `Conservativity/Star/README.md`,
`Metalogic/README.md`). *(Confirmed at implementation time: `grep -rln 'reserved, unbuilt\|StarAxiom\|TM⋆'
FormalSystem/ --include=*.md` found no site outside the enumerated list. Two `.lean` sites were
additionally updated, both of them created by this task's own edits rather than found by that
grep: `FormalSystem/Metalogic/Conservativity.lean`, whose module table and import-chain paragraph
had to gain the `Star/` child added in Phase 6, and `FormalSystem/README.md`, whose hand-written
`StarLanguage.lean` row still read "semantic-only, no proof system". The `README.md`,
`FormalSystem/README.md`, `Metalogic/README.md` and `Conservativity/README.md` inventory blocks
were refreshed with `check-module-invariants.sh --emit-inventory`.)* Confirm the list is complete at implementation time by
`grep -rln 'reserved, unbuilt\|StarAxiom\|TM⋆' FormalSystem/ --include=*.md` and by re-running
the invariant script — any site the grep finds that is not on this list is in scope.

**Files to modify**:
- `FormalSystem/StarLanguage/README.md`
- `FormalSystem/Metalogic/Conservativity/Plus/README.md`
- `FormalSystem/Metalogic/Conservativity/README.md`
- `FormalSystem/Metalogic/Conservativity/Star/README.md` - new
- `FormalSystem/Metalogic/README.md`

**Verification**:
- `bash scripts/check-module-invariants.sh` green in full — C14 (documented counts), C15 (paper
  anchors), C9 (no task numbers under `FormalSystem/`)
- `grep -rn 'reserved, unbuilt' FormalSystem/` returns nothing
- Every "OPEN" claim in the new prose carries its obstruction and at least one citation

---

## Lean Challenge Statements

```lean
import FormalSystem.StarLanguage.Formula
import FormalSystem.PlusLanguage.Derivation
import FormalSystem.Semantics.StarNonValidities
import FormalSystem.Metalogic.Conservativity.Plus.AxiomValidity
import FormalSystem.Metalogic.Conservativity.Plus.Forward

/-! ### Phase 1, 3, 4, 5 — syntax and proof system -/

namespace FormalSystem.StarLanguage

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.PlusLanguage

/-- Phase 1. Registers hold times and are unoriented, so both arms are structural. -/
def StarFormula.swapTemporal : StarFormula → StarFormula
  | .atom p => .atom p
  | .bot => .bot
  | .imp φ ψ => .imp φ.swapTemporal ψ.swapTemporal
  | .box φ => .box φ.swapTemporal
  | .untl ψ φ => .snce ψ.swapTemporal φ.swapTemporal
  | .snce ψ φ => .untl ψ.swapTemporal φ.swapTemporal
  | .stab φ => .stab φ.swapTemporal
  | .timeStore i φ => .timeStore i φ.swapTemporal
  | .timeRecall i φ => .timeRecall i φ.swapTemporal

theorem StarFormula.swap_temporal_involution (φ : StarFormula) :
    φ.swapTemporal.swapTemporal = φ := sorry

theorem ofPlus_swapTemporal (φ : PlusFormula) :
    ofPlus φ.swapTemporal = (ofPlus φ).swapTemporal := sorry

/-- Phase 3. One `ofBase` arm carries all 45 TM⁺ schemata at `ofPlus` instances; the register
arms are the report's ACCEPT table. MF is deliberately absent as a native schema — it is refuted
over `StarFormula` and reaches TM⋆ only through `ofBase`. -/
inductive StarAxiom : StarFormula → Type where
  | ofBase (φ : PlusFormula) (ax : PlusAxiom φ) : StarAxiom (ofPlus φ)
  | store_recall_same (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.timeRecall i φ)).iff (.timeStore i φ))
  | recall_store_same (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.timeStore i φ)).iff (.timeRecall i φ))
  | recall_recall (i j : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.timeRecall j φ)).iff (.timeRecall j φ))
  | store_store_comm (i j : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.timeStore j φ)).iff
        (StarFormula.timeStore j (.timeStore i φ)))
  | store_k (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (φ.imp ψ)).iff
        ((StarFormula.timeStore i φ).imp (.timeStore i ψ)))
  | recall_k (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (φ.imp ψ)).iff
        ((StarFormula.timeRecall i φ).imp (.timeRecall i ψ)))
  | store_box (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.box φ)).iff (StarFormula.box (.timeStore i φ)))
  | recall_box (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i (.box φ)).iff (StarFormula.box (.timeRecall i φ)))
  | store_stab (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeStore i (.stab φ)).iff (StarFormula.stab (.timeStore i φ)))
  | store_atom (i : ℕ) (p : Atom) :
      StarAxiom ((StarFormula.timeStore i (.atom p)).iff (StarFormula.atom p))
  | recall_rigid_future (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i φ).imp (StarFormula.allFuture (.timeRecall i φ)))
  | future_rigid_recall (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.allFuture (.timeRecall i φ)).imp (StarFormula.timeRecall i φ))
  | recall_rigid_past (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.timeRecall i φ).imp (StarFormula.allPast (.timeRecall i φ)))
  | past_rigid_recall (i : ℕ) (φ : StarFormula) :
      StarAxiom ((StarFormula.allPast (.timeRecall i φ)).imp (StarFormula.timeRecall i φ))
  | recall_export_until (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.untl ψ (.timeRecall i φ)).iff
        ((StarFormula.timeRecall i φ).and (StarFormula.untl ψ StarFormula.top)))
  | recall_export_since (i : ℕ) (φ ψ : StarFormula) :
      StarAxiom ((StarFormula.snce ψ (.timeRecall i φ)).iff
        ((StarFormula.timeRecall i φ).and (StarFormula.snce ψ StarFormula.top)))

/-- Phase 3. Every register schema is valid over every task frame. -/
def StarAxiom.minFrameClass {φ : StarFormula} : StarAxiom φ → FrameClass
  | .ofBase _ ax => ax.minFrameClass
  | _ => .Base

/-- Phase 4. Constructor for constructor with `PlusDerivationTree`. -/
inductive StarDerivationTree (fc : FrameClass) : StarContext → StarFormula → Type where
  | «axiom» (Γ : StarContext) (φ : StarFormula) (h : StarAxiom φ) (h_fc : h.minFrameClass ≤ fc) :
      StarDerivationTree fc Γ φ
  | assumption (Γ : StarContext) (φ : StarFormula) (h : φ ∈ Γ) : StarDerivationTree fc Γ φ
  | modus_ponens (Γ : StarContext) (φ ψ : StarFormula)
      (d1 : StarDerivationTree fc Γ (φ.imp ψ)) (d2 : StarDerivationTree fc Γ φ) :
      StarDerivationTree fc Γ ψ
  | necessitation (φ : StarFormula) (d : StarDerivationTree fc [] φ) :
      StarDerivationTree fc [] (StarFormula.box φ)
  | temporal_necessitation (φ : StarFormula) (d : StarDerivationTree fc [] φ) :
      StarDerivationTree fc [] (StarFormula.allFuture φ)
  | temporal_duality (φ : StarFormula) (d : StarDerivationTree fc [] φ) :
      StarDerivationTree fc [] φ.swapTemporal
  | weakening (Γ Δ : StarContext) (φ : StarFormula) (d : StarDerivationTree fc Γ φ) (h : Γ ⊆ Δ) :
      StarDerivationTree fc Δ φ

@[inherit_doc] notation:50 Γ " ⊢⋆[" fc "] " φ => StarDerivationTree fc Γ φ

/-- Phase 4. -/
def StarDerivable (fc : FrameClass) (Γ : StarContext) (φ : StarFormula) : Prop :=
  Nonempty (StarDerivationTree fc Γ φ)

/-- Phase 5. -/
theorem StarAxiom.minFrameClass_ofBase {φ : PlusFormula} (ax : PlusAxiom φ) :
    (StarAxiom.ofBase φ ax).minFrameClass = ax.minFrameClass := sorry

/-- Phase 5. Deliverable (3): the embedding of TM⁺ derivations. -/
def StarDerivationTree.ofPlusTree {fc : FrameClass} {Γ : PlusContext} {φ : PlusFormula} :
    PlusDerivationTree fc Γ φ → StarDerivationTree fc (ofStarCtx Γ) (ofPlus φ) := sorry

theorem starDerivable_of_plusDerivable {fc : FrameClass} {Γ : PlusContext} {φ : PlusFormula}
    (h : PlusDerivable fc Γ φ) : StarDerivable fc (ofStarCtx Γ) (ofPlus φ) := sorry

theorem starDerivable_of_derivable {fc : FrameClass} {φ : Formula}
    (h : ProofSystem.Derivable fc [] φ) : StarDerivable fc [] (ofPlus (ofFormula φ)) := sorry

end FormalSystem.StarLanguage

/-! ### Phase 2 — the non-validity record -/

namespace FormalSystem.Semantics

open FormalSystem.Syntax
open FormalSystem.PlusLanguage
open FormalSystem.StarLanguage

/-- The MF counterexample formula: `↓¹p → p`. -/
def mfWitness (p : Atom) : StarFormula := .imp (.timeRecall 1 (.atom p)) (.atom p)

/-- MF (`□φ → □Gφ`) is NOT valid over `StarFormula`: the sole schema in the TM block whose
soundness consumes time-shift homogeneity, which `starTruthAt_timeShift` breaks by shifting the
register vector with the history. -/
theorem refute_modal_future (p : Atom) :
    ¬ NF.StarValidOn (.imp (.box (mfWitness p)) (.box (StarFormula.allFuture (mfWitness p)))) :=
  sorry

/-- Half one of the erasure refutation: the store/recall formula is `StarValid`. -/
theorem storeG_recall_valid (p : Atom) :
    StarValid (.imp (.timeStore 1 (StarFormula.allFuture (.timeRecall 1 (.atom p)))) (.atom p)) :=
  sorry

/-- Half two: its register erasure is not. Together: naive erasure is not a conservativity
translation. -/
theorem refute_erasure (p : Atom) :
    ¬ StarValid (.imp (StarFormula.allFuture (.atom p)) (.atom p)) := sorry

end FormalSystem.Semantics

/-! ### Phases 6, 7, 8 — validity, soundness, conservativity -/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.PlusLanguage
open FormalSystem.StarLanguage
open FormalSystem.Semantics
open FormalSystem.Metalogic

/-- Phase 6. -/
theorem starAxiom_validIn_min {φ : StarFormula} (ax : StarAxiom φ) :
    StarValidIn ax.minFrameClass φ := sorry

/-- Phase 6. -/
theorem starAxiom_swap_validIn_min {φ : StarFormula} (ax : StarAxiom φ) :
    StarValidIn ax.minFrameClass φ.swapTemporal := sorry

/-- Phase 7. The companion recursion, well-founded on the derivation's height. -/
theorem star_derivable_valid_and_swap_validIn {fc : FrameClass} {φ : StarFormula}
    (d : StarDerivationTree fc [] φ) : StarValidIn fc φ ∧ StarValidIn fc φ.swapTemporal := sorry

/-- Phase 7. Deliverable (2): soundness of TM⋆ over the task-frame semantics. -/
theorem star_soundness_validIn {fc : FrameClass} {φ : StarFormula}
    (h : StarDerivable fc [] φ) : StarValidIn fc φ := sorry

/-- Phase 8. Forward conservativity of TM⋆ over TM: soundness, truth transfer, then the engine.
No TM⁺ completeness is used. -/
theorem forward_star {fc : FrameClass} (engine : WeakCompleteness fc) (φ : Formula)
    (h : StarDerivable fc [] (ofPlus (ofFormula φ))) : ProofSystem.Derivable fc [] φ := sorry

/-- Phase 8, headline. **TM⋆ is a conservative extension of TM**, both directions, at every class
with an engine — the L ⊂ L⋆ row, unconditional. -/
theorem starDerivable_ofFormula_iff {fc : FrameClass} (engine : WeakCompleteness fc)
    (φ : Formula) : StarDerivable fc [] (ofPlus (ofFormula φ)) ↔ ProofSystem.Derivable fc [] φ :=
  sorry

/-- Phase 8. The L⁺ ⊂ L⋆ row, stated conditionally: general TM⁺ completeness implies TM⋆ is
conservative over TM⁺. -/
theorem starConservative_of_plusComplete {fc : FrameClass}
    (hcomplete : ∀ ψ : PlusFormula, PlusValidIn fc ψ → PlusDerivable fc [] ψ) (φ : PlusFormula)
    (h : StarDerivable fc [] (ofPlus φ)) : PlusDerivable fc [] φ := sorry

/-- Phase 8, unconditional contrapositive: any separating witness for non-conservativity is,
verbatim, a witness of TM⁺ incompleteness. This is why the TM⁺ row is stated as a conditional
pair rather than asserted or denied. -/
theorem plusIncomplete_of_starNonconservative {fc : FrameClass} (φ : PlusFormula)
    (hd : StarDerivable fc [] (ofPlus φ)) (hnd : ¬ PlusDerivable fc [] φ) :
    ¬ (∀ ψ : PlusFormula, PlusValidIn fc ψ → PlusDerivable fc [] ψ) := sorry

end FormalSystem.Metalogic.Conservativity
```

**What this block pins and what it does not.** It pins the *statements* of every deliverable, plus
the three structural declarations (`StarAxiom`, `StarDerivationTree`, `StarDerivable`) without
which those statements cannot be typed. The four per-class rows of `starDerivable_ofFormula_iff`
(`_base`, `_dense`, `_ztime`, `_rtime`) are deliberately not spelled out — they are mechanical
specializations at `completeness_base`/`_dense`/`_ztime`/`_rtime`, exactly as
`plusDerivable_ofFormula_iff_base` and its siblings are. The `.iff`-shaped register axioms are a
deliberate departure from `PlusAxiom`'s uniformly `.imp` style: the report's ACCEPT table
establishes these as biconditionals, and `StarTruth.and_iff` plus the clause lemmas unfold
`.iff` in about three lines per arm. If an arm proves unworkable in that shape, split it into two
`.imp` constructors — do **not** keep the name and weaken the statement.

## Testing & Validation

- [ ] `lake build` green after every phase, with zero new `sorry` (C3 asserts zero structural
      `sorry` by content).
- [ ] `bash scripts/check-module-invariants.sh` green after every phase; the `--no-build` fast
      structural pass is acceptable mid-phase, the full pass is required before a phase closes.
- [ ] C2: the four flagship theorems' axiom sets match the recorded baseline. A divergence is a
      HARD STOP, never a new baseline.
- [ ] C9: no task-number citation appears under `FormalSystem/`.
- [ ] C14: every documented axiom/sorry count in `docs/`, `README.md` and module docstrings matches
      the tree after Phase 9.
- [ ] C15: every paper-anchor citation added in Phases 2, 3 and 9 resolves against the pinned
      definitions of record.
- [ ] C24: every new module is reachable in the `FormalSystem` root closure and transitively
      imports `FormalSystem.Init` — wired in the same commit that creates it.
- [ ] C26: every new `def`/`abbrev` is camelCase (`ofBase`, `minFrameClass`, `ofPlusTree`,
      `mfWitness`, `swapTemporal`); theorem names may stay snake_case, matching the
      `swap_temporal_involution` family.
- [ ] No wildcard arm in `starAxiom_validIn_min`, `starAxiom_swap_validIn_min`, or
      `StarDerivationTree.ofPlusTree` — a wildcard would hide a missing case.
- [ ] `grep -rn 'import FormalSystem.Semantics' FormalSystem/StarLanguage/` stays empty.

## Artifacts & Outputs

New Lean modules:
- `FormalSystem/StarLanguage/Axioms.lean` — `StarAxiom`, `StarAxiom.minFrameClass`
- `FormalSystem/StarLanguage/Derivation.lean` — `StarDerivationTree`, `⊢⋆[fc]`, `StarDerivable`,
  the structural apparatus
- `FormalSystem/StarLanguage/Embedding.lean` — `ofPlusTree`, `starDerivable_of_plusDerivable`
- `FormalSystem/Metalogic/Conservativity/Star.lean` — aggregator
- `FormalSystem/Metalogic/Conservativity/Star/StarAxiomValidity.lean`
- `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean`
- `FormalSystem/Metalogic/Conservativity/Star/Forward.lean`
- `FormalSystem/Metalogic/Conservativity/Star/README.md`

Modified Lean modules:
- `FormalSystem/StarLanguage/Formula.lean` — `swapTemporal` and pins
- `FormalSystem/StarLanguage.lean` — imports and Modules list
- `FormalSystem/Semantics/StarNonValidities.lean` — the three refutations
- `FormalSystem/Metalogic/Conservativity.lean` — import the `Star/` aggregator

Modified documentation:
- `FormalSystem/StarLanguage/README.md`, `FormalSystem/Metalogic/README.md`,
  `FormalSystem/Metalogic/Conservativity/README.md`,
  `FormalSystem/Metalogic/Conservativity/Plus/README.md`

## Rollback/Contingency

Every phase is a separate commit under the per-green-substep mandate, and every phase but 1, 2 and
9 is additive-only (a new module plus one aggregator import line), so rollback is
`git revert` of that phase's commits in reverse order. Phase 1 touches a shared core module: if it
must be reverted after later phases land, revert Phases 5, 7 and 8 first (they consume
`ofPlus_swapTemporal`).

Contingencies:
- **A register axiom will not prove (Phase 6).** Drop the constructor from Phase 3, re-verify
  swap-closure, and record the drop as a reasoned exclusion with the failing goal as evidence.
  Never restate the schema in weakened form under the same name.
- **The soundness recursion will not terminate-check (Phase 7).** The blocker is a missing height
  lemma from Phase 4, not the recursion; add it there rather than restructuring the recursion.
- **Phase 8's conditional pair proves harder than the report's checked chains suggest.** The
  unconditional `starDerivable_ofFormula_iff` is independent of it and lands regardless; mark the
  conditional pair `[BLOCKED]` and escalate rather than sorrying it or weakening the statement.
- **A phase runs past one agent run.** Mark it `[PARTIAL]` with the resume point named, commit the
  green prefix, and re-dispatch — never commit a half-applied edit.
