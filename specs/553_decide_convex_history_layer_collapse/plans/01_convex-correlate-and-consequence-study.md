# Implementation Plan: Task #553

- **Task**: 553 - Decide convex history layer collapse (reframed: develop the categorical
  correlate of convex histories and the alternative consequence relations)
- **Status**: [IMPLEMENTING]
- **Effort**: 12 hours
- **Dependencies**: 552 (`align_history_vocabulary_with_paper`) — **satisfied**, status
  `completed`; `FormalSystem/Semantics/ConvexHistory.lean` exists and `ConvexHistory` is the
  convex layer, so the description's precondition ("the history-vocabulary rename must land
  first") holds.
- **Research Inputs**: None (no research artifact was dispatched for this round; see
  "Research-on-Demand Assessment" below for why none was requested)
- **Artifacts**: plans/01_convex-correlate-and-consequence-study.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md
- **Type**: lean4
- **Lean Intent**: false

## Overview

The task description is verdict-first: decide whether the convex-history layer should exist,
and if not, how to collapse it. The dispatch's User focus block materially reframes it. The
user asks that the categorical correlate of convex histories — the paper's
`app:Structure` (behavior presheaf, interval site, path category) — be **developed rather than
suppressed**, in both directions: drawing on the category theory for insight into the logic,
and drawing on this repository's proof theory and semantics for insight into the category
theory. The user further asks for careful study of two alternative consequence relations: one
ranging over convex histories, and one additionally restricting the temporal quantifiers to the
domain of the convex world. The stated aim is "learn, planning and creating additional tasks as
appropriate based on these learnings, revising the task description along the way if need be."

Where the description and the User focus pull apart, the User focus governs. This plan therefore
keeps every measurement and hunt the description demands — they are the evidence base either way
— but retargets the terminus. The output is no longer a collapse verdict with a collapse plan
attached; it is a **study** whose verdict is a consequence of the categorical and logical
findings, plus a set of proposed follow-on tasks and a proposed revision of the task description
in `specs/state.json`. Task 553 remains research-only: no edit to `FormalSystem/` at any phase,
probes under this task's directory only.

The plan also adds a fourth option to the description's three-way enum in (e). See
"Decision: the enum in (e) is incomplete" below.

### Research Integration

No research report exists for this round. The description's own "EVIDENCE ALREADY GATHERED"
block is treated as the research input, with the standing instruction to verify rather than
re-derive it. Three of its four numbered claims were spot-checked during planning; the results
are recorded under Phase 1's Scope Hypothesis, and two of its measurements are already
demonstrably stale (see that phase).

Grounding gathered during planning, which the implementation should build on rather than
rediscover:

- **The paper's `app:Structure` runs from line 3716 to line 3992 of**
  `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`, and contains, in
  order: `def:task-topology`, `app:topology-t1`, `app:topology-r0`, `app:gluing`,
  `def:interval-site`, `def:behavior-presheaf`, `def:twisted-arrow`,
  `lem:interval-twisted-arrow`, `app:presheaf-dictionary` (seven clauses: Germs, Sheaf,
  Directed Gluing, Totality, Possible Worlds, Determinism, Reflection), `def:conduche`,
  `def:path-category`, `fact:conduche-equivalence`, `cor:path-fibration`. The section carries a
  `% TODO: review in full` marker in the source.
- **`Beh(F)(ℓ)` is the set of convex histories with domain `[0, ℓ]`** — a *closed bounded
  interval*, not an arbitrary convex set. The repository's `ConvexHistory.domain` is an
  arbitrary convex predicate, hence a strict superset of what the presheaf needs. Any
  formalization of `Beh(F)` selects the interval-domain sub-family.
- **The alternative semantics the description calls a footnote is at line 1102** of the same
  file, and the paper's own commented-out sentence there already states the key consequence:
  "At the final move of a finished game there is no later time in that history's domain, and so
  `F⊤` — the seriality axiom TS of the logic TM presented below — and its past dual both fail,
  making `F⊥` satisfiable and the unboundedness of time contingent." The corresponding Lean
  axiom constructors are `Axiom.serial_future` and `Axiom.serial_past`
  (`FormalSystem/ProofSystem/Axioms.lean:140` and `:144`).
- **Parts of the presheaf apparatus already exist in the tree in total-only disguise.**
  `ConvexHistory.timeShift` (`Semantics/ConvexHistory.lean:330`) is the translation `Tr p`;
  `StarPasting.paste` (`Semantics/StarPasting.lean:109`) is two-piece gluing at a shared time,
  restricted to total histories; the Extension Theorem (`Semantics/Extension/`) is exactly the
  input `app:presheaf-dictionary` uses for its *Totality* and *Directed Gluing* clauses. This
  materially lowers the estimated cost of formalizing the presheaf appendix, and is a
  first-order argument against treating the convex layer as prospective-only.

### Prior Plan Reference

No prior plan.

### Roadmap Alignment

`specs/ROADMAP.md` exists but was not supplied as a `roadmap_path` in this dispatch, so it was
consulted read-only and no roadmap phases are added. Note for the implementation: the roadmap's
fronts are completeness, decidability/tableau, and publication; nothing in it currently names
the presheaf/categorical appendix as a front. If Phase 7 recommends developing that material,
proposing a new roadmap front is in scope for the *proposed tasks*, not for this task's edits —
`ROADMAP.md` must not be modified by this task.

## Goals & Non-Goals

**Goals**:
- Verify (and correct) the description's four evidence claims, and complete the hunt for a
  genuine consumer of a convex, non-total, non-partial history.
- Establish plainly what `TruthAt` currently *means* at a bounded index, with machine-checked
  probes, and say whether that reading is degenerate.
- Define and separate the candidate consequence relations — the current/paper one, the
  convex-indexed one, and the paper's domain-restricted alternative — and determine, with
  probes, which of TM's axioms survive each.
- Map the paper's `app:Structure` onto the repository's existing types, and record what the
  repository's proof theory and decidability results teach *about* that categorical structure,
  not only what the category theory teaches about the logic.
- Cost the structural options honestly, including the fourth option this plan adds, and
  recommend exactly one with reasoning a follow-up task can execute against.
- Produce concrete, sized follow-on task specifications, and a proposed revised description for
  task 553 in `specs/state.json`.

**Non-Goals**:
- Any edit to `FormalSystem/`. Probes live under
  `specs/553_decide_convex_history_layer_collapse/probes/` and are compiled with
  `lake env lean <path>`, never added to the library or its imports.
- Any edit to `specs/state.json`, `specs/TODO.md`, or `specs/ROADMAP.md`. The revised
  description is *proposed* in the report, not applied.
- Touching `PartialHistory` or the Extension Theorem, per the description's constraint.
- Executing whichever structural option is recommended. That is follow-on work.
- Formalizing `app:presheaf-dictionary` in full. Phase 5's probe is a skeleton sized to one
  agent run, whose purpose is to measure the real cost of the full formalization, not to
  achieve it.

## Decision: the enum in (e) is incomplete

The description's (e) offers exactly three verdicts: COLLAPSE, KEEP, COLLAPSE-PARTIALLY. Under
the User focus a fourth is on the table and is likely the right one:

> **DEVELOP-AND-RETARGET** — retarget the primary semantics to a total-by-construction index
> (`PossibleWorld`), so that the central type means the paper's central notion with no side
> condition, *while simultaneously growing* the convex layer into the interval-site / behavior-
> presheaf apparatus and adding the alternative consequence relations as explicitly named
> second definitions rather than as the accidental generality of the first.

This differs from COLLAPSE-PARTIALLY, which retains `ConvexHistory` as a definition the
semantics no longer uses — a preservation posture. DEVELOP-AND-RETARGET is a development
posture: the convex layer acquires new, deliberate consumers (the presheaf, the alternative
consequence relations) at the same time the primary semantics stops carrying it as a side
condition. The two moves are independent and can be phased separately, which is what makes the
combination coherent rather than contradictory.

This is recorded as a planning decision, with its reasoning, rather than raised as a
`user_decision`: the User focus block already answers the question it would ask ("develop rather
than suppress"), so putting it back to the user would be asking something already decided.
Phase 7 must still argue the verdict from the evidence and may land on a different one.

## Research-on-Demand Assessment

No `research_path` was provided. Research was **not** requested, and the reason is recorded here
so a later reader does not reopen it: the open questions in this task are ones an agent answers
by reading this repository and this paper — both of which are on disk and were read during
planning — and by writing Lean probes against the live tree. There is no external API, no
unfamiliar third-party behavior, and no literature question that a research dispatch could
settle and this dispatch could not. The task's *deliverable* is a study; that is not the same
thing as the task *needing a research phase before it can be planned*.

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Phase 5's presheaf skeleton overruns one agent run (the categorical material is the deepest here) | M | H | The phase's Scope Hypothesis fixes an explicit stop line: functoriality + Germs + two-piece gluing only. Directed Gluing, Totality, Determinism and Reflection are *stated* and left to the proposed follow-on task, not proved. |
| The axiom-survival audit (45 constructors) is treated as 45 Lean proofs | M | M | Phase 4 machine-checks a named separating subset only; the rest are audited by argument in prose with the constructor name cited. The Scope Hypothesis names the subset. |
| A genuine non-total, non-partial convex consumer is found late, invalidating Phase 6's costing | H | L | Phase 1 runs first and is a hard gate: its finding is an explicit input to Phase 6, and a positive find changes Phase 6's recommendation rather than being absorbed silently. |
| The description's stale measurements are copied forward as fact | M | M | Phase 1 re-measures and records both the old and new numbers, flagging every divergence as a correction under the description's own "report any of it that turns out to be wrong" instruction. |
| Probe files drift out of compilability as the tree changes under concurrent tasks | L | M | Every probe carries the exact `lake env lean` command in its header comment (the `specs/535_.../probes/` convention) and each probe-bearing phase re-runs it as its verification step. |
| Scope creep into actually performing the retarget | H | L | Non-Goals are explicit; the phase gate for every phase is "no file under `FormalSystem/` modified", checked with `git status --short FormalSystem/`. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 2 | -- |
| 2 | 3, 6 | 1, 2 |
| 3 | 4, 5 | 3 |
| 4 | 7 | 1, 2, 3, 4, 5, 6 |

Phases within the same wave can execute in parallel. Phases 1 and 2 both open the shared report
file; if they are actually run in parallel, Phase 1 creates the file with §0 and §1 and Phase 2
appends §2 after Phase 1 commits, so the two do not contend for the same region.

---

### Phase 1: Evidence audit and convex-consumer hunt [COMPLETED]

**Goal**: Settle question (a). Verify or correct each of the description's four evidence claims
against the current tree, and determine whether any site genuinely requires a convex, non-total,
non-partial history.

**Tasks**:
- [x] Create `specs/553_decide_convex_history_layer_collapse/reports/01_convex-correlate-and-consequence.md`
      with a §0 scope/method note and a §1 "Evidence audit" section.
- [x] Re-measure each claim and record measured-vs-claimed: occurrences of `IsTotal`, `.domain`,
      `ConvexHistory`, and `.convex`; the count of non-`fun _ => True` `domain` fields at the
      convex layer; the bundled/predicate bridge inventory named in claim 3.
- [x] Enumerate every construction of a `ConvexHistory` value in the tree and classify each as
      total-by-construction, generic transport, or genuinely bounded. `ConvexHistory.ofTotal`
      (`Semantics/ConvexHistory.lean:178`) and its listed twelve unmigrated skeleton sites are a
      starting index, not the whole set.
- [x] Hunt the named surfaces for a genuine bounded consumer: `Semantics/StarPasting.lean`,
      `Semantics/ShiftSet.lean`, `Semantics/Ultraproduct/`, `Metalogic/Decidability/BiLasso/`,
      `Metalogic/WeakCanonical/`, `Semantics/IntTransfer.lean`, and `FormalSystem/Boneyard/`.
      For `Boneyard/`, additionally check whether any live task in `specs/state.json` names a
      revival of the subtree in question.
- [x] Record, for each of the four claims, one of: CONFIRMED, CORRECTED (with the correction),
      or REFUTED (with the counter-evidence).

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The description asserts `IsTotal` on 322 lines, `.domain` on 198 lines,
the `convex` field discharged 22 times, and every concrete convex-layer value total. Planning
spot-checks over the post-rename tree measured **305** `IsTotal` occurrences, **228** `.domain`
occurrences, and **598** `ConvexHistory` occurrences across `FormalSystem/`, with `IsTotal`
appearing in **58** files. Occurrences and lines are different metrics and the tree has moved
since the claims were written, so these are hypotheses to confirm, not corrections yet — the
phase must state which metric it is reporting and re-derive both if they differ. The claim most
at risk is claim 1's completeness (not its truth): it enumerates constructions by grep on
`domain`, which will miss a bounded history built by a helper that sets `domain` indirectly.

**Files to modify**:
- `specs/553_decide_convex_history_layer_collapse/reports/01_convex-correlate-and-consequence.md`
  — created; §0 and §1 written.

**Verification**:
- `git status --short FormalSystem/` reports no modification under `FormalSystem/`.
- Every one of the four claims carries an explicit CONFIRMED/CORRECTED/REFUTED verdict with the
  command or file:line that grounds it.
- The consumer hunt covers every surface named in the task list above, each with a stated result
  (including the negative ones).

---

### Phase 2: What `TruthAt` means at a bounded index [COMPLETED]

**Goal**: Settle question (b) with machine-checked evidence: establish what the current
`TruthAt` clauses actually mean when the index is a non-total convex history, and state plainly
whether that reading is degenerate.

**Tasks**:
- [x] Read `FormalSystem/Semantics/Truth.lean`'s `TruthAt` (the five clauses at approximately
      `:234-241`) and the docstring above it, which already records the atom clause's
      `∃ (ht : τ.domain t)` conjunct as "Decision A, accepted gap".
- [x] Write `specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean`
      establishing, sorry-free, on a concrete small frame: (i) an atom is *false*, not
      ill-formed, at a time outside the index's domain; (ii) the `untl`/`snce` clauses quantify
      over all of `D` irrespective of the domain, so a bounded index still "sees" times it does
      not settle; (iii) the resulting failure of at least one axiom that is valid at a total
      index — the T-schema `□φ → φ` at an out-of-domain time is the expected witness, since
      `□p` may hold while `p` is false for want of a domain proof.
- [x] State in §2 of the report which of the three readings the current clauses realize: the
      paper's `def:BL-semantics` (agrees under totality), the paper's line-1102 alternative
      (it is *not* this — the tense clauses are unrestricted), or a third, unintended reading.
- [x] State whether any lemma in the tree is stated for an arbitrary `(τ : ConvexHistory F)`
      where the intended content is the total one, and would therefore be asserting something
      weaker or different than its name suggests. List them if so.

**Timing**: 1.5 hours

**Depends on**: none

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts that the current bounded-index reading is a third,
unintended one and that the T-schema is refutable at an out-of-domain time. Both are planning-
time derivations from the clause text, not established facts; the probe must confirm or refute
each, and a refutation is a reportable finding, not a phase failure.

**Files to modify**:
- `specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean` — new.
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §2 appended.

**Verification**:
- `lake env lean specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean`
  exits 0 with no error and no `sorry` warning; the probe header states this command verbatim.
- `grep -c 'sorry' ` on the probe returns 0 for actual `sorry` terms.
- `git status --short FormalSystem/` reports no modification.
- §2 gives a one-paragraph plain answer to "is the current bounded-index reading degenerate?",
  either way.

---

### Phase 3: The candidate consequence relations, defined and separated [COMPLETED]

**Goal**: The core of the User focus. Give precise definitions of the alternative consequence
relations, and separate them from each other and from the current one with machine-checked
validities and refutations.

**Tasks**:
- [x] Write §3 of the report defining, side by side and in the repository's own notation, at
      least these four:
      - **C1** (current / paper): `ConsequenceOnFrames` as it stands
        (`Semantics/Validity.lean:78`) — index total, tense over `D`, `□` over total histories,
        `t` ranging over `D`.
      - **C2** (convex index, unrestricted tense): the same with the `(_ : τ.IsTotal)` binder
        dropped — i.e. what the current `TruthAt` already computes at a bounded index.
      - **C3** (the paper's line-1102 alternative): index any convex `τ` with `x ∈ dom τ`; `□`
        quantifies over all convex `σ` with `x ∈ dom σ`; `Past`/`Future` (and `untl`/`snce`)
        restricted to `dom τ`; consequence quantifies `x` over `dom τ` rather than `D`.
      - **C4** (interval-indexed): C3 restricted to the closed bounded interval domains
        `[0, ℓ]` — that is, indexed by the sections of `Beh(F)`. This is the one that has a
        categorical reading, and it is the bridge to Phase 5.
- [x] Write `specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean`
      giving C2, C3 and C4 as actual Lean definitions over the existing `ConvexHistory` /
      `Formula` types (a local `TruthAtConvex` recursion beside the library's `TruthAt`, not a
      modification of it), and proving the separating facts.
- [x] Establish at probe level, at minimum: `F⊤` (`Formula.someFuture Formula.top`, i.e.
      `untl ⊤ ⊤`) is C1-valid but **not** C3-valid, witnessed at the right endpoint of a bounded
      interval; and the S5 modal core (`modal_t`, `modal_4`, `modal_5_collapse`, `modal_b`)
      survives C3, because C3's `□` quantifies over a set determined by `x` alone and containing
      the index itself.
- [x] Record the structural observation and check it: under C3, `□φ` at `(τ, x)` does not depend
      on `τ` at all, so `□` remains a universal modality; and because point histories `{⟨x,w⟩}`
      are legal C3 indices for every `w` (by Nullity), `□` at C3 ranges over strictly more
      indices than at C1. State what that does to formulas mixing `□` with tense.

**Timing**: 2 hours

**Depends on**: 2

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts four consequence relations and a specific separating
witness (`F⊤` C1-valid, C3-invalid). The four-way split is a planning proposal — if C2 and C4
collapse into C1 or C3 under examination, say so and reduce the count rather than manufacturing
a distinction. The `F⊤` separation is corroborated by the paper's own commented-out sentence at
line 1102 but must still be machine-checked here, not cited.

**Files to modify**:
- `specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean` — new.
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §3 appended.

**Verification**:
- `lake env lean specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean`
  exits 0, sorry-free.
- Each of C1–C4 (or the reduced set) appears as a Lean definition in the probe, not only as prose.
- The `F⊤` separation is a proved pair (`Valid`-side and refutation-side), not an assertion.
- `git status --short FormalSystem/` reports no modification.

---

### Phase 4: Axiom survival audit under the alternative semantics [COMPLETED]

**Goal**: Determine what logic C3 (and C4) actually is, by auditing TM's axiom set constructor
by constructor.

**Tasks**:
- [x] Enumerate the `Axiom` constructors of `FormalSystem/ProofSystem/Axioms.lean` by layer
      (propositional, S5 modal, Burgess-Xu temporal, additional BX temporal, modal-temporal
      interaction, uniformity, Prior-UZ/SZ, Z1, density, Reynolds) and, for each, record
      SURVIVES / FAILS / CONDITIONAL under C3, with a one-line reason.
- [x] Machine-check the named separating subset in
      `specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean`:
      `serial_future`, `serial_past` (expected FAILS), `modal_t`, `modal_4`,
      `modal_5_collapse` (expected SURVIVES), `modal_future` and one of the
      `connect_future`/`temp_linearity` pair (the modal-temporal interaction, where the answer
      is genuinely unclear and matters most).
- [x] Characterize the resulting logic as precisely as the evidence supports: name the axioms
      that must be dropped, say whether the remainder is a known system (a tense logic of
      bounded/interval time), and say explicitly what is *not* established — in particular
      whether completeness or decidability transfers is out of scope here and belongs to a
      proposed task.
- [x] Do the same, briefly, for C2, whose interest is diagnostic rather than logical: if C2's
      logic is degenerate (Phase 2's finding), say that C2 is an artifact to be eliminated, not
      an alternative to be developed.
- [x] Write §4 of the report.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: `Axioms.lean` carries 45 constructors per `.claude/CLAUDE.md`'s
architecture note; planning counted roughly 44 constructor lines by grep, so the exact figure
must be re-derived from the file rather than quoted. Only the seven-constructor subset named
above is machine-checked; the remainder are audited by argument. If an audited-by-argument
constructor's verdict turns out to be genuinely uncertain, promote it into the probe rather than
recording a guess.

**Files to modify**:
- `specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean` — new.
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §4 appended.

**Verification**:
- `lake env lean specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean`
  exits 0, sorry-free.
- Every `Axiom` constructor in `Axioms.lean` appears exactly once in the §4 table with a verdict;
  the table's row count equals the constructor count re-derived in this phase.
- `git status --short FormalSystem/` reports no modification.

---

### Phase 5: The categorical correlate, both directions [COMPLETED]

**Goal**: Map the paper's `app:Structure` onto the repository's existing types, and — the half
the User focus asks for that the paper does not supply — record what this repository's proof
theory, semantics and decidability results teach *about* that categorical structure.

**Tasks**:
- [x] Write §5.1 of the report: a dictionary from `app:Structure` to the tree, entry by entry.
      Seed entries established during planning, to be verified and extended: `Tr p` ↔
      `ConvexHistory.timeShift` (`Semantics/ConvexHistory.lean:330`); two-piece gluing at a
      shared time ↔ `StarPasting.paste` (`Semantics/StarPasting.lean:109`), currently
      total-only; `thm:extension` ↔ `Semantics/Extension/`, which is the input
      `app:presheaf-dictionary` uses for its *Totality* and *Directed Gluing* clauses;
      `H_F ≅ lim Beh(F)(2x)` ↔ `TaskFrame.HF` (`Semantics/ConvexHistory.lean:450`). For each
      entry state what exists, what is total-only, and what is absent.
- [x] Write `specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean`:
      the interval-domain convex history (`domain := fun z => 0 ≤ z ∧ z ≤ ℓ`), the restriction
      along `Tr p`, presheaf functoriality (identity and composition), and the *Germs* clause
      (`Beh(F)(0) ≅ W`). Stop there — see Scope Hypothesis. *(deviation: altered — functoriality and Germs delivered as planned; the Scope Hypothesis's budget-permitting two-piece gluing was delivered as its composition step `glue_seam` only, the section assembly and restriction identities handed to the §7.3 follow-on task)*
- [x] Write §5.2, the reverse direction, developing at least these three connections and
      stating for each what is established, what is conjectural, and what a follow-on task would
      have to prove:
      1. **Determinism ↔ injectivity of restriction.** `app:presheaf-dictionary`'s *Determinism*
         clause says `F` is deterministic iff every restriction map of `Beh(F)` is injective.
         The repository has a modal-formula treatment of determinism
         (`Semantics/StarDeterminism.lean`, and the stability/`timeRecall` material). Composing
         the two would give a *modal-formula characterization of when the behavior presheaf is
         separated* — a categorical property named by a sentence of the object language.
      2. **BiLasso as the effective content of `cor:path-fibration`.** Over `D = ℤ`,
         `cor:path-fibration` identifies `Path(F)` with the free category on `⟨W, ⇒₁⟩`, and the
         paper's line 1773 observes that over a finite `W` every bounded convex history extends
         to an eventually-periodic possible world — a finite prefix plus a cycle each way. That
         is precisely a *lasso*. `Metalogic/Decidability/BiLasso/` is therefore a computational
         witness for the path-category correspondence, and the decision procedure is the
         categorical statement made effective. Establish how close the correspondence actually
         is, and where it breaks.
      3. **A restriction-invariance fragment.** Under C4, truth at a point of a section is
         preserved under restriction to smaller subintervals containing that point for some
         syntactic fragment and not for others (`□` and atoms are expected invariant, `F`/`P`
         expected only co-monotone). Characterizing that fragment syntactically is a
         sheaf-theoretic locality result about the logic. State the conjecture precisely and
         check the two easy directions in the probe if they fit in budget; otherwise state it
         and hand it to a proposed task.
- [x] Note explicitly that `app:Structure` carries a `% TODO: review in full` marker in the
      paper source, so any formalization proposed here should be flagged as tracking material
      the author has not finished reviewing.

**Timing**: 2 hours

**Depends on**: 3

**Verification Tier**: local

**Commit Mode**: per-substep

**Scope Hypothesis**: The probe is scoped to functoriality + Germs + (budget permitting) the
two-piece gluing existence. *Directed Gluing*, *Totality*, *Determinism* and *Reflection* are to
be **stated** in the report and left unproved — they are the proposed follow-on task's content,
not this phase's. The phase asserts that `timeShift`, `paste` and `Extension` cover a substantial
fraction of the analytic input to `app:presheaf-dictionary`; that fraction is a hypothesis, and
the phase must say which clauses those three actually reach and which they do not.

**Files to modify**:
- `specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean` — new.
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §5.1 and §5.2 appended.

**Verification**:
- `lake env lean specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean`
  exits 0, sorry-free.
- The §5.1 dictionary has one row per named item of `app:Structure` (`def:task-topology`
  through `cor:path-fibration`), each marked present / total-only / absent.
- §5.2's three connections each carry an explicit established/conjectural split.
- `git status --short FormalSystem/` reports no modification.

---

### Phase 6: Costing the structural options [COMPLETED]

**Goal**: Settle questions (c) and (d). Cost each option by file and by obligation class,
against the counterfactual of doing nothing.

**Tasks**:
- [x] Partition the cost of retargeting the semantics to a total index into: (i) mechanical
      rewrites (`τ.states t ht` → `τ.states t`, dropped `IsTotal` binders, deleted
      bundled/predicate bridges), and (ii) proofs that must genuinely be rethought. Give a file
      list with a count for each class, derived from Phase 1's measurements.
- [x] Confirm or refute the description's expectation that the change removes code rather than
      adding it, with a measured net-line estimate.
- [x] Cost all four options — COLLAPSE, KEEP, COLLAPSE-PARTIALLY, DEVELOP-AND-RETARGET — on the
      same basis, including what each forecloses. Cost the middle answers as carefully as the
      extremes, per the description's instruction, and do not let DEVELOP-AND-RETARGET escape
      costing merely because this plan proposed it.
- [x] Cost the counterfactual explicitly: what the ongoing per-site tax of the status quo is,
      and what it would cost to *not* decide.
- [x] Note the constraint every proposed COLLAPSE-shaped plan must meet: each phase one agent
      run, `lake build FormalSystem` green with no new `sorry` at each phase end, and
      `PartialHistory` and the Extension Theorem untouched.
- [x] Write §6 of the report.

**Timing**: 1.5 hours

**Depends on**: 1, 2

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: This phase asserts per-file counts and a net-line direction. Every number
must be reproduced by a command recorded next to it in the report; no figure may be carried over
from the task description without re-measurement (see Phase 1's corrections).

**Files to modify**:
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §6 appended.

**Verification**:
- Each of the four options has a cost line with a mechanical/rethink split and a foreclosure
  note.
- Every quantitative claim in §6 is accompanied by the command that produced it.
- `git status --short FormalSystem/` reports no modification.

---

### Phase 7: Verdict, proposed description revision, and follow-on tasks [COMPLETED]

**Goal**: Close the study. Recommend exactly one option with reasoning sufficient for a
follow-up task to execute without re-deriving it; propose the revised task description; and
specify the follow-on tasks.

**Tasks**:
- [x] Write §7.1: the verdict — exactly one of COLLAPSE, KEEP, COLLAPSE-PARTIALLY, or
      DEVELOP-AND-RETARGET — with the reasoning, not just the label. If the verdict is KEEP,
      the description requires the reason be recorded once in the `ConvexHistory` module
      docstring; since this task may not edit `FormalSystem/`, that docstring edit becomes a
      one-line proposed task rather than an edit here.
- [x] Write §7.2: the proposed revised `description` field for task 553 in `specs/state.json`,
      as a fenced block ready to paste. It must retain the ANALYSIS SURFACE note, the
      no-`file_scope` rationale, and the CONSTRAINTS paragraph; retarget the framing from
      verdict-first collapse to develop-the-correlate; add the fourth option to (e); and cite the
      paper anchors (`app:Structure` and its named items, and the line-1102 footnote). State
      explicitly that this is a proposal and that `specs/state.json` was not edited.
- [x] Write §7.3: follow-on task specifications, each with a title, a type, a one-paragraph
      description, a rough size, and its dependencies. Candidates established during planning,
      to be confirmed, pruned or extended by the study's own findings:
      1. Formalize `app:gluing` at the `ConvexHistory` layer (two-piece, arbitrary convex
         domains), generalizing `StarPasting.paste` off its totality hypothesis.
      2. Formalize the interval site `Int(D)` and the behavior presheaf `Beh(F)`, with the
         *Germs*, *Sheaf* and *Totality* clauses of `app:presheaf-dictionary`.
      3. `H_F ≅ lim Beh(F)(2x)` — the *Possible Worlds* clause, tying `TaskFrame.HF` to the
         presheaf limit.
      4. Determinism ⟺ injectivity of the restriction maps, joined to the repository's existing
         modal treatment of determinism.
      5. The `D = ℤ` path-category / free-category corollary and its relation to BiLasso.
      6. Define the C3/C4 semantics and consequence relations as named library definitions
         (not probes), with the axiom-survival results as theorems.
      7. The retarget itself, if the verdict calls for it: a phased plan with each phase one
         agent run leaving `lake build FormalSystem` green.
- [x] Write §7.4: what was *not* settled, stated plainly, so the next reader does not mistake
      the study's boundaries for its conclusions.
- [x] Optionally create the follow-on tasks via the repository's task-creation path if the
      dispatch's mode permits it; if it does not, say so in §7.3 and leave the specifications as
      the deliverable.

**Timing**: 1.5 hours

**Depends on**: 1, 2, 3, 4, 5, 6

**Verification Tier**: prose

**Commit Mode**: per-substep

**Scope Hypothesis**: The seven candidate follow-on tasks are a planning-time list, not a
finding. Phase 7 must prune the ones its own evidence does not support and add any the study
turned up; a §7.3 that reproduces this list unchanged is a signal the pruning step was skipped.

**Files to modify**:
- `specs/.../reports/01_convex-correlate-and-consequence.md` — §7 appended.

**Verification**:
- Exactly one verdict is stated, and it is one of the four named options.
- §7.2 contains a paste-ready description block and an explicit statement that `state.json` was
  not edited.
- Every §7.3 entry has a title, type, description, size and dependency list.
- `git status --short FormalSystem/ specs/state.json specs/TODO.md specs/ROADMAP.md` reports no
  modification to any of them.

---

## Testing & Validation

- [ ] All four probe files compile with `lake env lean <path>`, exit 0, and are sorry-free.
- [ ] `git status --short FormalSystem/` is empty at the end of every phase — this task modifies
      nothing in the library.
- [ ] `specs/state.json`, `specs/TODO.md` and `specs/ROADMAP.md` are unmodified by this task's
      own edits (status-sync writes by the orchestrator's postflight are not this task's edits).
- [ ] The report answers each of (a) through (e) from the task description, and each of the two
      questions the User focus adds (the consequence relations, and the bidirectional
      categorical connection), with a section pointer for each.
- [ ] Every quantitative claim in the report cites the command that produced it.
- [ ] Any plan the report *proposes* for a COLLAPSE-shaped change sizes each phase to one agent
      run and requires `lake build FormalSystem` green with no new `sorry` at each phase end.

## Artifacts & Outputs

- `specs/553_decide_convex_history_layer_collapse/reports/01_convex-correlate-and-consequence.md`
  — the study, §0 through §7.
- `specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean`
- `specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean`
- `specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean`
- `specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean`
- A proposed revised `description` for task 553 (in §7.2, not applied).
- Follow-on task specifications (in §7.3), and the tasks themselves if creation is permitted.

## Rollback/Contingency

Every artifact this plan produces is confined to
`specs/553_decide_convex_history_layer_collapse/`. Rollback is deletion of that directory's
`reports/` and `probes/` contents plus a `git revert` of the phase commits; nothing in
`FormalSystem/` is touched, so no build state can regress. If a phase's probe cannot be made to
compile within its budget, mark that phase `[PARTIAL]`, record the obstruction in the report
section it was writing, and carry the unproved claim forward as a stated conjecture rather than
dropping it — a conjecture with its obstruction named is a usable output; a silent omission is
not.
