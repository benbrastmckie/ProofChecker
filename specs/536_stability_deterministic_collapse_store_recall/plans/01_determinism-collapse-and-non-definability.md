# Implementation Plan: The Stability Modal and the Deterministic Task Frames

- **Task**: 536 - Establish in Lean the exact relationship between the stability modal `⊡` and the Deterministic task frames
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours
- **Dependencies**: None (task 537 depends on this plan's Phase 1 output)
- **Research Inputs**: `specs/536_stability_deterministic_collapse_store_recall/reports/01_determinism-collapse-and-store-recall.md`
- **Artifacts**: plans/01_determinism-collapse-and-non-definability.md (this file)
- **Standards**: plan-format.md; status-markers.md; artifact-management.md; tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

The claim under correction — "*Determined* (`φ → ⊡φ`) is valid exactly over the Deterministic
frames" — is false in the ⇐ direction, and the research report splits it into three distinct
collapse phenomena. This plan lands two of them in the library: (a) the **deterministic collapse**
`Deterministic F → ⊨_F ⊡φ ↔ φ` (choice-free, already machine-checked in the probes), and (b) the
**non-definability** of `Deterministic` in L⋆, via the F°/F¹ **indistinguishable pair** over ℝ.
Deliverable (c) — the store/recall apparatus needed for the *exact* correspondence — is a
recommendation only, recorded as a spawn-ready follow-up description, and (d) is a read-and-record
correspondence between the Lean tree and `possible_worlds.tex` that authors **no** manuscript text.

Definition of done: `lake build` green and sorry-free; `TaskFrame.Deterministic` and the collapse
theorems live at stable, importable library paths that task 537 consumes; F° and F¹ are legal
`FrameOver realOrder`s in the library with the `S_φ` state-set bridge proved **once, generically**
and instantiated twice; the choice-freeness of (a) and (b) is pinned by `#print axioms`.

### Research Integration

Integrated from `reports/01_determinism-collapse-and-store-recall.md`:

- **§3 corrected statement set (T1)–(T6)** drives the phase goals. This plan lands (T2) in Phase 1
  and (T3)/(T4) in Phase 7. (T1)'s ⇐ half (ZFC, via `thm:extension`) and (T6) are explicitly out of
  scope.
- **§4.2 / probes/03**: the determinism predicate takes the tree's `Fib`-subsingleton shape, not the
  pointwise shape of probes/01. Two concrete wins, both verified against the tree:
  `TaskFrame.saturation_of_fib_subsingleton` (`Semantics/TaskFrame.lean:1401`) consumes exactly that
  shape, so a deterministic frame gets its `saturation` field free; and
  `translationRel_fib_subsingleton` (`Semantics/Frames/Standard.lean:58`) is already literally a
  proof of the predicate.
- **§5.3 reducibility trap**: the `ShiftSet` route to F¹ is the **only** working route for anything
  touching histories (Phase 2, Constraint C5).
- **§5.4 architecture**: `satSet` plus a single generic bridge theorem under hypotheses (H1)/(H2),
  instantiated at F° and F¹ — not two parallel inductions.
- **§6.3/§6.4**: deliverable (c) narrowed to Option 1 (single world register), with the
  choice-asymmetry finding attached to the follow-up description.
- **§7.1 / §7.1bis**: read-and-record only; no writes to `possible_worlds.tex`, no `Det-pm`/`Det-m`
  manuscript prose.

**One research recommendation validated as already done, and therefore dropped**: the report's
suggested Phase 2 ("promote task 535's `refute_determined`") is **already in the library** at
`FormalSystem/Semantics/StarNonValidities.lean:142`, over `NF := FrameOver.natFrame (D := ℤ)`, with
a `Semantics/README.md` row already naming *Determined*. It must not be re-derived. What remains is
a one-line docstring repair: that theorem currently says "Validity over deterministic frames is
**not formalized here**", which Phase 1 falsifies. That repair is folded into Phase 1.

### Prior Plan Reference

No prior plan. `plans/` was empty at plan time.

### Roadmap Alignment

No `specs/ROADMAP.md` in this repository; `roadmap_flag` not set. No roadmap phases added.

## Preserved Assets — DO NOT RE-DERIVE

Three sorry-free probe files exist and recompile. Every phase below **transcribes** from them;
no phase re-derives their content. Any phase that finds itself proving one of these from scratch
has gone off-plan.

| Asset | Contents | Promoted by |
|---|---|---|
| `probes/01_determinism-collapse-probes.lean` (45 lines) | Pointwise `IsDeterministic`, forward singleton bridge, collapse `⊡φ ↔ φ`, `Determined` as frame validity. Choice-free. **Superseded on the predicate shape by probes/03** — transcribe the proof bodies, take the statement shapes from probes/03. | Phase 1 |
| `probes/02_fzero-frame-probes.lean` (272 lines) | F° over ℝ as a `FrameOver` with **all six axioms** including `limit` and `saturation`; `fzero_not_deterministic`; the full order-isomorphism core (`fzero_bounds`, `fzero_lipschitz`, `fzero_continuous`, `fzero_strictMono`, `fzero_hits_future`, `fzero_hits_past`). **The expensive, load-bearing asset.** | Phases 3, 4 |
| `probes/02`'s `foneRel` / `fone_saturation` / `foneFrame` / `fone_deterministic` section (lines 218-272) | Bespoke F¹. **NOT PROMOTED — probe artifact only.** F¹ already exists generically in the library; rebuilding it is wasted work. Do not restore it. | *(none)* |
| `probes/03_fib-form-and-translation-frame.lean` (94 lines) | `Fib`-form `TaskFrame.Deterministic`, `deterministic_iff` (the two forms agree), `saturation_of_deterministic`, deliverable (a) restated against the `Fib` form, F¹ from `translationFrame`, and **both reproduced instances of the reducibility trap**. **The authoritative version of (a).** | Phases 1, 2 |

**Library assets to reuse, not rebuild** (each verified present at plan time):

| Declaration | Location | Use |
|---|---|---|
| `TaskFrame.Fib` | `Semantics/TaskFrame.lean:260` | the predicate's shape |
| `TaskFrame.saturation_of_fib_subsingleton` | `Semantics/TaskFrame.lean:1401` | free `saturation` for deterministic frames |
| `TaskFrame.fib_subsingleton_of_functional` | `Semantics/TaskFrame.lean:1389` | functional relations are deterministic |
| `translationRel_fib_subsingleton` | `Semantics/Frames/Standard.lean:58` | F¹'s determinism, verbatim |
| `ShiftSet.fibre` / `ShiftSet.frame` (`@[reducible]`) | `Semantics/ShiftSet.lean:157` / `:199` | the only working F¹ route |
| `ShiftSet.hist`, `hist_isTotal`, `total_eq_orbit` | `Semantics/ShiftSet.lean` (`total_eq_orbit` at `:228`) | F¹'s world-set characterization, free |
| `truth_congr_ext`, `of_stab` | `Semantics/StarTruth.lean:265`, `:206` | the collapse proof's two inputs |
| `refute_determined` | `Semantics/StarNonValidities.lean:142` | `app:deterministic`'s negative half — **already landed** |
| `Extension.extension` (takes a `PartialHistory`, no convexity field) | `Semantics/Extension/Extension.lean:208` | *not used* — recorded so nobody "fixes" it |
| `realOrder` (`@[reducible] noncomputable`) | `Metalogic/DedekindNonCompactness.lean:318` | placement precedent (see Phase 2, R5) |

## Hard Constraints (carried into every phase)

- **C1 — No manuscript writes.** MUST NOT write to
  `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`, and MUST NOT draft
  manuscript prose for `Det-pm` or `Det-m`. PossibleWorlds task 105 holds staged LaTeX for those in
  its Phase 3/5 handoff, and a stale-buffer incident previously destroyed an edit to that file.
  Deliverable (d) is **read-and-record only**, in this task's own `specs/536_*/` artifacts.
- **C2 — Unrestricted duration quantifier.** The determinism predicate MUST quantify `d` over all of
  `F.Duration`, never `0 ≤ d`. The bridge applies it at the possibly negative `s - t`; a
  positives-only formulation would make the frame `F^N` "Deterministic" and **falsify** the bridge
  lemma. This is a correctness requirement, not fidelity-to-the-paper.
- **C3 — No uniform substitution.** US is **unsound** here: `p → ⊡p` is frame-valid over F° while
  `Fp → ⊡Fp` is refutable over `F′`. No proof in this development may use a US argument, and every
  refuting instance must be a genuinely temporal formula.
- **C4 — Keep both directions constructive.** Choice dependence tracks a *direction*: any
  "validity ⟹ frame condition" step needs Zorn via `thm:extension`. (a) and (b) as scoped state the
  safe direction. MUST NOT restate (a) as a biconditional correspondence, and MUST NOT generalize
  (b) to arbitrary frames — either would break constructivity. Say so in the docstrings and pin it
  with `#print axioms`.
- **C5 — F¹ through `ShiftSet`, never through `translationFrame` directly.** `translationFrame` is a
  plain `def`, not `@[reducible]`. The frame-level failure is fixable by typing variables at
  `↑rOrder`; the **history-level failure is not** — `τ.states` returns
  `F1.toTaskFrame.WorldState`, and neither a type ascription nor a `@[reducible]` alias reaches
  inside `translationFrame`. `cor:no-characterization`'s F¹ half is entirely about histories. A
  phase that starts from `translationFrame` will fail late and expensively.
- **C6 — Stable importable path for task 537.** Task 537 is instructed to **consume** the collapse
  lemma, not duplicate it. It must land in the library at the exact names fixed in Phase 1, not in
  `probes/`.
- **C7 — No task-number references under `FormalSystem/`.** Cite `\label`s (`def:deterministic`,
  `lem:deterministic-singleton`, `app:deterministic`, `app:drift`, `cor:no-characterization`) and
  file/declaration names, never "task N". Line numbers into `possible_worlds.tex` have been stale in
  three independent extractions — cite labels only.

## Goals & Non-Goals

**Goals**:
- (a) `TaskFrame.Deterministic F → F.StarValidOn (⊡φ ↔ φ)` for every `StarFormula φ`, choice-free,
  at a stable library path.
- (b) F° and F¹ in the library as legal `FrameOver realOrder`s, with the `S_φ` state-set bridge
  proved once generically and instantiated at both, concluding: F° validates *Determined* while
  being non-deterministic (T3), and F°/F¹ validate exactly the same `StarFormula`s, so
  `Deterministic` is not L⋆-definable (T4).
- (c) A spawn-ready follow-up **recommendation** for narrow world store/recall (single register),
  with its cost and choice-asymmetry notes. **Recommendation only — no implementation.**
- (d) A Lean↔paper correspondence record under `specs/536_*/`, authoring no manuscript text.
- Choice-freeness of (a) and (b) pinned by an `#print axioms` regression check.

**Non-Goals**:
- The ⇐ half of `lem:deterministic-singleton` (`⟨τ⟩_x = {τ}` ⟹ Deterministic) — ZFC, via
  `thm:extension`; not needed by anything here.
- Any store/recall operator, vector, or register in `StarFormula` (deliverable (c) is a
  recommendation, per §6.3).
- `Det`, `Det-pm`, `Det-m` in Lean, and Theorem C in either direction.
- Re-deriving `refute_determined` or `F′` — already in the library.
- `F^N` and the forward-vs-bidirectional separation (report §5bis, optional phase 8 there) —
  **cut**: it is blocked on a finite-*fibres* saturation helper that may not exist (R11), and the
  bidirectional quantifier it motivates is already secured by C2 plus the docstring.
- Generalizing (b) to arbitrary frames (report §6.4's Theorem D scoping) — would reintroduce choice.
- Any statement of the *history-equality* form `⟨τ⟩_x = {τ}`; the pointwise state form is weaker,
  sufficient, and free (§4.2 finding 2).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| A phase rebuilds F¹ from `translationFrame` and hits the history-level reducibility wall | H | M | C5 is stated as a constraint, not a footnote; Phase 2 starts from `ShiftSet` and its verification lists `total_eq_orbit` as the acceptance signal |
| `realOrder` reuse pulls `Metalogic.StrongCompleteness` into a light module (`DedekindNonCompactness` imports it) | M | H | Phase 2 decides explicitly: define a local `@[reducible] noncomputable def realOrder : TemporalOrder := ⟨ℝ⟩` in the new `Independence/` module with a docstring citing the `DedekindNonCompactness:318` precedent and the import-weight reason. **Do not** duplicate it into `Semantics/` (that would pull `Mathlib.Data.Real.Basic` into the most upstream layer) |
| New topology imports (`isCompact_Icc`, IVT) in the library | L | M | Precedent exists (`Metalogic/Bundle/LimitMCS.lean`, `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean`); the `Semantics/TaskFrame.lean:897` "no topology" remark concerns the *cone* topology only. Placement under `Metalogic/Independence/` contains the blast radius. A topology-free `csSup` route to saturation exists as a fallback (report §5.1) |
| `satSet`'s `box` case uses a `Set` equality test, which is undecidable | M | M | `open scoped Classical` (as `StarTruth.lean` already does), or encode as the disjunction `satSet V φ = univ ∨ satSet V φ = ∅`. Prefer the disjunction if `Decidable` friction appears — and note this cannot break C4: `Classical` in a *definition* is not `Classical.choice` in the proof term, but the Phase 7 `#print axioms` pin is what actually settles it. If the pin shows `Classical.choice`, switch to the disjunction encoding |
| `ShiftSet` carries a valuation field `A`, but validity must quantify over **all** `TaskModel`s | M | M | Phase 2: supply a trivial/parameterized `A` and use only `S.frame`; never route validity through `S.model`. State this in the module docstring |
| The `untl`/`snce` cases of the induction are harder than the change-of-variables estimate | M | M | Phase 5 lands the order-transfer lemmas as standalone green work *before* Phase 6's induction, so the risk is isolated to one phase with its inputs already proved |
| Scope creep into deliverable (c) | M | L | (c) is a written recommendation in Phase 8 with an explicit non-goal above; no Lean file may gain a store/recall constructor |
| Accidental manuscript edit (stale-buffer incident precedent) | H | L | C1; Phase 8's file list contains no path outside `specs/536_*/` |
| Retired/renamed paper labels produce dangling citations | L | M | Rename list to apply in docstrings: `Spherical` → `Saturation`; `cor:spherical-finite` → `cor:saturation-finite`; `app:non-deterministic` **retired** (merged into `app:deterministic`); `def:BLplus-semantics` **no longer exists** (repoint to `def:BLstar-semantics`) |

## Implementation Phases

**Dependency Analysis**:
| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1 | -- |
| 2 | 2, 5 | 1 |
| 3 | 3, 6 | 2, 5 |
| 4 | 4 | 3 |
| 5 | 7 | 4, 6 |
| 6 | 8 | 7 |

Phases within the same wave can execute in parallel. Phase 1 is the **green milestone for
deliverable (a)**: it is complete, choice-free, and independently useful (task 537 consumes it)
before any frame construction begins.

---

### Phase 1: Determinism predicate, singleton bridge, and the collapse [COMPLETED]

**Goal**: Deliverable (a), complete and choice-free, at stable library paths.

**Tasks**:
- [x] Add to `FormalSystem/Semantics/FrameProperty.lean`, beside `IsDense`/`IsDiscrete`/
      `IsSuccArchDiscrete`/`IsComplete`/`IsDedekind`:
      `def TaskFrame.Deterministic (F : TaskFrame) : Prop := ∀ (w : F.WorldState) (d : F.Duration), (TaskFrame.Fib F.TaskRel w d).Subsingleton`
      — `d` unrestricted (C2), transcribing `probes/03`.
- [x] Add `TaskFrame.deterministic_iff` (the `Fib` form agrees with the pointwise form, one line each
      way, from `probes/03`) and `TaskFrame.saturation_of_deterministic` (the free `saturation`
      field, via `saturation_of_fib_subsingleton`).
- [x] Docstring `Deterministic` with: `def:deterministic`; that it is **one bidirectional
      condition**, not a forward/backward conjunction (`FrameOver.converse` is a structure field, so
      past instances come free); and that restricting `d` to `0 ≤ d` yields the strictly weaker
      *forward* determinism, which does **not** support the bridge lemma (C2).
- [x] Create `FormalSystem/Semantics/StarDeterminism.lean` importing `Semantics.FrameProperty` and
      `Semantics.StarValidity`, carrying, from `probes/03`:
      `states_eq_of_deterministic` (the forward singleton bridge, ~8 lines),
      `stab_iff_of_deterministic`, `determined_of_deterministic`, and the biconditional frame
      validity `stab_biconditional_starValidOn_of_deterministic`.
- [x] Module docstring: this is `app:deterministic`'s positive half; it uses only the (⇒) half of
      `lem:deterministic-singleton` and is therefore **choice-free** — no `thm:extension`, no Zorn,
      no `serial`/`limit`/`saturation`; and the bridge is stated **pointwise on states**, not as
      history equality, because `truth_congr_ext` already converts pointwise agreement into L⋆ truth
      agreement for every `StarFormula` including `stab` (§4.2 finding 2). Record C4: the statement
      stays an implication; restating it as a biconditional correspondence would make the converse
      half ZFC.
- [x] Repair the now-false sentence in `refute_determined`'s docstring
      (`Semantics/StarNonValidities.lean:142`): "Validity over deterministic frames is not
      formalized here" → cross-reference `determined_of_deterministic`, so the two halves of
      `app:deterministic` cite each other. Record there that the refuting instance is `Fp`, **not**
      an atom (at atoms the schema holds on every frame), and that `F′`'s discreteness is a genuine
      hypothesis carried by `natFrame`'s `[SuccOrder D] [NoMaxOrder D]` binders — in a dense order
      the cone is all of `W` and *Limit* fails outright (C3).
- [x] Wire `import FormalSystem.Semantics.StarDeterminism` into `FormalSystem/Semantics.lean` and add
      a `Semantics/README.md` module row.
- [x] Add `#print axioms determined_of_deterministic` (and the biconditional) as a comment block or
      test recording the absence of `Classical.choice` (C4). *(deviation: altered — recorded as a
      re-runnable comment block in the `StarDeterminism` module docstring rather than a new test
      file, to keep the touched-file set to the plan's list; verified externally by
      `lake env lean` on a scratch file: all four report `[propext]` only)*

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: ~140 new lines across one new file plus four edited files
(`FrameProperty.lean`, `StarNonValidities.lean`, `Semantics.lean`, `Semantics/README.md`).
Confirm at implementation time by `wc -l` on the new module and `git diff --stat`; if the touched
file set differs, record the deviation rather than silently widening.

**Files to modify**:
- `FormalSystem/Semantics/FrameProperty.lean` — add `Deterministic`, `deterministic_iff`,
  `saturation_of_deterministic`
- `FormalSystem/Semantics/StarDeterminism.lean` — **new**: bridge + collapse
- `FormalSystem/Semantics/StarNonValidities.lean` — docstring repair only
- `FormalSystem/Semantics.lean` — aggregator import
- `FormalSystem/Semantics/README.md` — module row

**Verification**:
- `lake build` green, sorry-free.
- `#print axioms` on the collapse theorems shows no `Classical.choice`.
- `grep` confirms `Deterministic`'s binder is `(d : F.Duration)` with no `0 ≤ d` guard (C2).
- The names task 537 will import are fixed and stated in the module docstring (C6).

---

### Phase 2: F¹ over ℝ through `ShiftSet` [NOT STARTED]

**Goal**: F¹ — the deterministic translation flow over ℝ — in the library via the only route that
survives at the history level, with its world-set characterization free.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean`.
- [ ] Decide and record the `realOrder` placement (R5): define
      `@[reducible] noncomputable def realOrder : TemporalOrder := ⟨ℝ⟩` **locally in this module**,
      with a docstring citing the `Metalogic/DedekindNonCompactness.lean:318` precedent, noting both
      annotations are load-bearing, and stating the reason for not importing it there
      (`DedekindNonCompactness` imports `Metalogic.StrongCompleteness`, far too heavy for this
      module) and the reason for not lifting it into `Semantics/` (it would pull
      `Mathlib.Data.Real.Basic` into the most upstream layer).
- [ ] Build the ℝ shift set (`sh w d := w + d`; the `sep` field is the only content, ~15 lines,
      mirroring `rShift`'s `sep` proof) and take `F1 := (…).frame`. Supply a trivial valuation for
      the `A` field and **document that only `.frame` is used** — validity quantifies over all
      `TaskModel`s, never `S.model`.
- [ ] `f1_deterministic : TaskFrame.Deterministic F1` — either
      `fib_subsingleton_of_functional` or `translationRel_fib_subsingleton`, a one-liner either way.
- [ ] Specialize `ShiftSet.total_eq_orbit` to record the F¹ world-set characterization: total
      histories are **exactly** the translations `τ(t) = τ(0) + t`. This is what
      `cor:no-characterization`'s F¹ half needs.
- [ ] `f1_determined (φ) : F1.StarValidOn (.imp φ (.stab φ))` from Phase 1, as a smoke test.
- [ ] Module docstring: state C5 (the reproduced reducibility trap, both instances, and why the
      `translationFrame` route is unusable at the history level) and mark `probes/02`'s bespoke
      `foneFrame` as a probe artifact deliberately **not** promoted, so no later reader restores it.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~100 lines in one new file, with **zero** `FrameOver` axiom obligations
discharged by hand (all seven come from `ShiftSet.fibre`). Confirm by grepping the new file for
`nullity_identity|comp|converse|serial|limit|saturation` — a hit outside a docstring means the
route was abandoned and must be justified.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean` — **new**

**Verification**:
- `lake build` green, sorry-free.
- The world-set characterization elaborates — this is the acceptance signal that C5 was honoured;
  it is exactly the statement that fails on the `translationFrame` route.
- No hand-written frame axiom fields in the file.

---

### Phase 3: F° — the drift frame over ℝ [NOT STARTED]

**Goal**: F° as a legal `FrameOver realOrder`, all six axioms, plus its non-determinism.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/DriftFrame.lean`, importing Phase 2's module for
      `realOrder`.
- [ ] Transcribe from `probes/02` (lines 17-137): `fzeroRel w d u := u - w ∈ Set.uIcc d (2 * d)`,
      `fzeroRel_iff`, `mem_fib_iff`, `fib_eq_Icc`/`fib_eq_Icc'`, `isCompact_fib`, `isClosed_fib`, and
      the six axiom proofs `fzero_nullity`, `fzero_converse`, `fzero_serial`, `fzero_comp`,
      `fzero_limit`, `fzero_saturation`, assembled into `fzeroFrame : FrameOver realOrder`.
- [ ] Transcribe `fzero_not_deterministic` (`0 ⇒_1 1` and `0 ⇒_1 2`), restated against Phase 1's
      `TaskFrame.Deterministic`.
- [ ] Docstring the **uIcc encoding**: the paper states the relation only for `x ≥ 0`;
      `FrameOver.converse` forces a two-sided extension, and the unordered interval is the extension
      that makes `converse` hold on the nose.
- [ ] Docstring the **`comp` scope note**: the repo's `Compositional` (`Semantics/TaskFrame.lean:474`)
      is confined to `0 ≤ x, 0 ≤ y`, so mixed-sign composition — which F° genuinely *fails* — is
      never demanded. Had `comp` been two-sided, F° would not be a frame.
- [ ] Docstring the **two deliberate deviations** from `app:drift`'s proof: the interpolant splits on
      `le_total (w+x) (v-2y)` (no division, no degenerate `x+y = 0` case) rather than using
      `λ := (v-w)/(x+y)`; and `saturation` goes through Mathlib's Cantor lemma rather than an
      explicit FIP argument. `limit_of_shift` does **not** apply — the relation is not functional.
- [ ] Docstring **why F° survives density where `F′` does not**: F°'s fibres are bounded intervals
      shrinking linearly to `{w}`, so its cone shrinks in any order; `F′`'s fibres at nonzero
      duration are all of `W`. The two frames are not interchangeable.
- [ ] Docstring: **a ℤ-carrier version does not work** — over `W = D = ℤ` histories are not
      surjective, so the `untl` case of Phase 6's induction fails. The choice of ℝ is essential and
      the `[d, 2d]` bracket is what forces surjectivity via IVT. Record so nobody "simplifies" it.

**Timing**: 1.5 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~150 lines, six axiom fields, transcription only — no new mathematical
content beyond `probes/02` lines 17-160. Confirm by diffing the promoted declarations against the
probe; any *new* lemma needed is a deviation to record.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/DriftFrame.lean` — **new**

**Verification**:
- `lake build` green, sorry-free; all six `FrameOver` fields present.
- `fzero_not_deterministic` typechecks against Phase 1's predicate.
- New Mathlib topology imports are confined to this module.

---

### Phase 4: F°'s histories are order-isomorphisms of `(ℝ, <)` [NOT STARTED]

**Goal**: The order-isomorphism core, lifted from bare state functions to F°'s `WorldHistory`s.

**Tasks**:
- [ ] Transcribe from `probes/02` (lines 139-216), on the bare function `f : ℝ → ℝ` with
      `hf : ∀ s t, fzeroRel (f s) (t - s) (f t)`: `fzero_bounds`, `fzero_lipschitz`,
      `fzero_continuous`, `fzero_strictMono`, `fzero_hits_future`, `fzero_hits_past`.
- [ ] Lift each to total `WorldHistory fzeroFrame`s: derive `hf` from `respects_task` plus
      `IsTotal`, and state the history-level forms the Phase 7 instantiation consumes.
- [ ] Add the "every world state occurs at every time" witness: for any `w` and `x`, the translation
      `δ(t) := t + w - x` is a total history of F° with `δ(x) = w`. This is hypothesis (H2)'s F°
      half, and it is what keeps (b) constructive (C4) — no appeal to `thm:extension` or
      `cor:occurrence`.
- [ ] Docstring: `fzero_hits_future` is the crux and the expensive part of `app:drift`'s key lemma
      (`a := x + (v - f x)/2`, `b := x + (v - f x)`, then `intermediate_value_Icc` on the
      Lipschitz-hence-continuous `f`); it was independently corroborated by a second derivation.

**Timing**: 1.5 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~110 lines — six transcribed lemmas plus their history-level lifts and the
translation witness. Confirm by enumerating the promoted declaration names against `probes/02`.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/DriftFrame.lean` — extend, or a new
  `Independence/DriftHistories.lean` if the implementer judges `DriftFrame.lean` full; record which

**Verification**:
- `lake build` green, sorry-free.
- The history-level forms are stated in exactly the shape Phase 5's (H1) hypothesis expects (check
  against Phase 5's signature before closing).

---

### Phase 5: Generic order-transfer lemmas under (H1) [NOT STARTED]

**Goal**: The frame-independent content of the `S_φ` induction's temporal cases, proved once against
an abstract hypothesis, so Phase 6's induction has its inputs already green.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/OrderTransfer.lean`.
- [ ] Package hypothesis **(H1)** for a frame `F` with `F.WorldState = ℝ` (or an abstract linear
      order): every total history's state function is strictly monotone, hits every strictly greater
      state at a strictly later time, and every strictly lesser state at a strictly earlier time.
      Package **(H2)**: every world state lies on some total history at every time.
- [ ] Prove, from (H1) alone: the future-image lemma `{τ(y) : y > x} = {v : v > τ(x)}`, its past
      mirror, and the **betweenness/change-of-variables** lemma — `x < y < z` matches
      `τ(x) < τ(y) < τ(z)` in both directions. These are exactly what the `untl`/`snce` cases need.
- [ ] Prove, from (H2): the `box` transfer — `{ρ(x) : ρ a total history} = univ`.
- [ ] Docstring: **the recursion mentions only the order on `W` and neither task relation** — this is
      the crux clause of `cor:no-characterization` and the reason this is one generic lemma with two
      instantiations rather than two parallel developments. Also record the terminology: F° and F¹
      are an **indistinguishable** pair, not a "separating" pair — they *agree* on every store-free,
      recall-free sentence while differing in determinism, and the argument is
      elimination-by-indistinguishability. Calling them "separating" inverts the mechanism and has
      already misled one reader into expecting F° to refute *Determined*, which it validates.

**Timing**: 1.5 hours

**Depends on**: 1

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~120 lines, no frame construction and no ℝ-specific reasoning beyond the
carrier's linear order. Confirm by grepping the module for `fzero|drift|translation` — any hit
means frame-specific content leaked into the generic layer.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/OrderTransfer.lean` — **new**

**Verification**:
- `lake build` green, sorry-free.
- No dependency on `DriftFrame.lean` or `RealTranslationFrame.lean` in the import list — the
  genericity claim is mechanically checkable this way.

---

### Phase 6: `satSet` and the generic state-set bridge theorem [NOT STARTED]

**Goal**: The one real proof obligation of deliverable (b): truth over an (H1)+(H2) frame depends
only on the world state of evaluation.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/StateSetTruth.lean`.
- [ ] Define `satSet (V : ℝ → Atom → Prop) : StarFormula → Set ℝ` by the report §5.4 recursion:
      `atom ↦ {w | V w p}`, `bot ↦ ∅`, `imp ↦ (satSet φ)ᶜ ∪ satSet ψ`,
      `box ↦ univ if satSet φ = univ else ∅`, `stab ↦ satSet φ`, and the `untl`/`snce` interval
      forms.
- [ ] Resolve the `box` decidability question: `open scoped Classical` (as `StarTruth.lean` does) or
      the `= univ ∨ = ∅` disjunction encoding. Prefer the disjunction if `Decidable` friction
      appears, and re-check the Phase 7 `#print axioms` pin either way (C4).
- [ ] Prove the bridge: for any frame satisfying (H1) and (H2), any `M`, total `τ`, and `x`,
      `StarTruthAt M τ x φ ↔ τ.states x _ ∈ satSet M.valuation φ`, by induction on `StarFormula` with
      the history universally quantified **inside** the induction (the `Independence/` house style,
      per that directory's README) so the `box` case can apply the IH.
- [ ] The `stab` case is `S_{⊡φ} = S_φ` — one line, and it holds for **both** frames for different
      reasons: over F° because `σ ∈ ⟨τ⟩_x` are exactly the histories with `σ(x) = τ(x)` and truth
      depends only on that state; over F¹ because `⟨τ⟩_x = {τ}` by Phase 1's bridge. Docstring both,
      and note that the F¹ reason uses only the choice-free (⇒) half (C4).
- [ ] Derive the validity corollary: `F.StarValidOn φ ↔ ∀ V, satSet V φ = univ`.

**Timing**: 2 hours

**Depends on**: 5

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: ~200 lines; the `untl`/`snce` cases are a change of variables along the
order-isomorphism using Phase 5's transfer lemmas, and should need no new analytic content.
Confirm at implementation time: if either temporal case requires a new IVT/continuity argument, the
Phase 5 boundary was drawn wrong — record that as a deviation rather than importing `DriftFrame`
here.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/StateSetTruth.lean` — **new**

**Verification**:
- `lake build` green, sorry-free.
- The bridge theorem's statement mentions neither `fzeroRel` nor the translation relation.
- Every `StarFormula` constructor has a case: `atom`, `bot`, `imp`, `box`, `untl`, `snce`, `stab`.

---

### Phase 7: Instantiate at F° and F¹ — (T3), (T4), and the axiom pins [NOT STARTED]

**Goal**: The two headline results, plus the constructivity pins and aggregator wiring.

**Tasks**:
- [ ] Create `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean`.
- [ ] Discharge (H1) and (H2) for F° from Phase 4, and for F¹ from Phase 2's `total_eq_orbit`
      specialization (translations are trivially strictly monotone and surjective).
- [ ] **(T3)**: `fzeroFrame.StarValidOn (.imp φ (.stab φ))` for every `φ`, together with
      `fzero_not_deterministic` — a non-deterministic frame validating *Determined*, so the converse
      of Phase 1's collapse fails. State it as the refutation of the "exactly" claim.
- [ ] **(T4)**: `fzeroFrame.StarValidOn φ ↔ F1.StarValidOn φ` for every `StarFormula φ` (both sides
      reduce to `∀ V, satSet V φ = univ`), and the non-definability conclusion: no set of
      `StarFormula`s valid over every `Deterministic` frame excludes the non-deterministic F°, so
      `Deterministic` is not L⋆-definable.
- [ ] `#print axioms` on the (T3) and (T4) statements; record the absence of `Classical.choice` in
      the module docstring (C4). If `Classical.choice` appears, trace it to the `box`-case encoding
      (Phase 6) and switch to the disjunction form.
- [ ] Docstring the **three-way split** the task description conflates (report §3): `⊡` trivializes
      *semantically* (`⟨τ⟩_x` a singleton) **exactly** on the Deterministic frames; it trivializes
      *logically* (*Determined* valid) on a class **strictly containing** them; and neither region is
      L⋆-definable. Note also C3: US is unsound here, `p → ⊡p` being frame-valid over F° while
      `Fp → ⊡Fp` is refutable over `F′` — so no proof here argues by substitution.
- [ ] Wire the four new `Independence/` modules into
      `FormalSystem/Metalogic/Independence.lean` and add rows to
      `FormalSystem/Metalogic/Independence/README.md` (file/lines/description table) and the
      `FormalSystem/Metalogic.lean` docstring.

**Timing**: 1.5 hours

**Depends on**: 4, 6

**Verification Tier**: full

**Commit Mode**: per-substep

**Scope Hypothesis**: ~130 lines in one new module plus three wiring edits
(`Independence.lean`, `Independence/README.md`, `Metalogic.lean`). Confirm by `git diff --stat`.

**Files to modify**:
- `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` — **new**
- `FormalSystem/Metalogic/Independence.lean` — imports
- `FormalSystem/Metalogic/Independence/README.md` — module rows and a Key Results entry
- `FormalSystem/Metalogic.lean` — docstring row

**Verification**:
- Full `lake build` green and sorry-free across the whole tree.
- `#print axioms` on (T3) and (T4): no `Classical.choice`.
- `grep -rn 'task [0-9]' FormalSystem/` finds no new hits (C7).

---

### Phase 8: Deliverables (c) and (d) — recommendation and correspondence record [NOT STARTED]

**Goal**: The two non-Lean deliverables, written entirely inside `specs/536_*/`.

**Tasks**:
- [ ] Write the deliverable (d) **correspondence record**: a table mapping each paper `\label`
      (`def:deterministic`, `lem:deterministic-singleton`, `app:deterministic` both halves,
      `app:drift`, `cor:no-characterization`, `app:deterministic-future`) to its Lean declaration and
      path, marking what is formalized, what is deliberately not (the ⇐ half of the bridge; `Det`,
      `Det-pm`, `Det-m`), and where the two must agree. Include the rename list from R9 so a future
      reader does not restore dangling references.
- [ ] Write the deliverable (c) **recommendation** as a spawn-ready task description: narrow world
      store/recall with a **single** register (evaluation point `(τ, x, μ)`), ~600-900 lines,
      sufficient for `Det-m`, leaving time-shift invariance intact and the `untl`/`snce` clauses
      unchanged. Record the rejected alternative — the full ℕ-indexed four-operator BL⋆ apparatus,
      2500+ lines, which additionally invalidates the atomization route that task 533's
      conservativity rests on — and the choice-asymmetry finding (validity ⟹ frame condition needs
      Zorn; the reverse direction is safe), so it is not rediscovered late.
- [ ] Record the transport-layer breakage table (`truth_congr_ext`, `starTruthAt_timeShift`,
      `stab_state_only`, `TruthCorr`/`TruthAntiIso`, `Atomization`, `StarPasting`) as the follow-up's
      known cost.
- [ ] Note explicitly, for whoever runs the follow-up, that this task's relationship to the
      manuscript is **read and record only** (C1), and that PossibleWorlds task 105 holds staged
      LaTeX for `Det-pm`/`Det-m` — cite Theorem C as a report-level result pending paper
      integration, never as manuscript text and never as a conjecture.

**Timing**: 1 hour

**Depends on**: 7

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: one or two markdown files under
`specs/536_stability_deterministic_collapse_store_recall/`, and **no** file outside that directory.
Confirm by `git status` before committing — any path outside `specs/536_*/` is a C1 violation.

**Files to modify**:
- `specs/536_stability_deterministic_collapse_store_recall/summaries/` or `reports/` — the
  correspondence record and the follow-up recommendation

**Verification**:
- `git status` shows no modification to any path under `/home/benjamin/Philosophy/` (C1).
- The record contains no drafted manuscript prose for `Det-pm` or `Det-m` (C1).
- No `.lean` file gained a store/recall constructor (non-goal check).

---

## Testing & Validation

- [ ] `lake build` green and sorry-free after every phase.
- [ ] `grep -rn 'sorry' FormalSystem/Semantics/StarDeterminism.lean FormalSystem/Metalogic/Independence/` returns nothing.
- [ ] `#print axioms` on `determined_of_deterministic`, the F° *Determined* validity, and the
      F°/F¹ indistinguishability shows no `Classical.choice` (C4).
- [ ] The determinism predicate's duration binder is unrestricted (C2) — check by inspection and by
      the fact that the bridge proof applies it at `s - t`.
- [ ] No `.lean` file under `FormalSystem/` references a task number (C7).
- [ ] No file outside `specs/536_*/` and `FormalSystem/` is modified; in particular nothing under
      `/home/benjamin/Philosophy/` (C1).
- [ ] Task 537 can `import FormalSystem.Semantics.StarDeterminism` and cite the collapse by name
      (C6) — verify the names appear in `Semantics/README.md`.

## Artifacts & Outputs

- `FormalSystem/Semantics/FrameProperty.lean` (extended) — `TaskFrame.Deterministic`,
  `deterministic_iff`, `saturation_of_deterministic`
- `FormalSystem/Semantics/StarDeterminism.lean` (new) — bridge + collapse, deliverable (a)
- `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean` (new) — F¹
- `FormalSystem/Metalogic/Independence/DriftFrame.lean` (new) — F° and its histories
- `FormalSystem/Metalogic/Independence/OrderTransfer.lean` (new) — generic (H1)/(H2) transfer
- `FormalSystem/Metalogic/Independence/StateSetTruth.lean` (new) — `satSet` and the bridge theorem
- `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` (new) — (T3), (T4)
- Wiring/doc edits: `Semantics.lean`, `Semantics/README.md`, `Semantics/StarNonValidities.lean`
  (docstring), `Metalogic/Independence.lean`, `Metalogic/Independence/README.md`, `Metalogic.lean`
- `specs/536_*/` — the deliverable (d) correspondence record and the deliverable (c) follow-up
  recommendation

## Rollback/Contingency

Every phase is a separate module plus its aggregator import, so reverting is `git revert` of that
phase's commits plus removal of the import line; nothing downstream depends on the new modules until
Phase 7 wires them.

- **If Phase 6's induction stalls**: Phases 1-4 stand on their own — deliverable (a) is complete and
  choice-free at Phase 1, and F°/F¹ are legal library frames after Phases 2-4. Close the task
  `[PARTIAL]` with (b) outstanding, and do **not** discharge the bridge theorem with `sorry`.
- **If new topology imports prove unacceptable**: the topology-free `csSup` route to `saturation`
  (`Set.Icc_inter_Icc`, `le_csSup`, `Real.sSup_le`) replaces the Cantor lemma; the IVT use in
  Phase 4 has no equivalent escape and would need `StrictMono` surjectivity proved by hand.
- **If the `#print axioms` pin shows `Classical.choice`**: it will be the Phase 6 `box`-case
  encoding; switch to the `= univ ∨ = ∅` disjunction. C4 is a hard requirement, not a preference.
