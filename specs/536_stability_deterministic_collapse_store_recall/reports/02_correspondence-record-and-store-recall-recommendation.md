# Lean↔Paper Correspondence Record, and the Store/Recall Follow-Up Recommendation

**Task**: 536 — stability deterministic collapse, its failing converse, and the store/recall correspondence
**Type**: lean4 · record (deliverables (c) and (d))
**Status**: recorded
**Inputs**: `reports/01_determinism-collapse-and-store-recall.md`; `plans/01_determinism-collapse-and-non-definability.md`
**Scope**: read-and-record only. **No file under `/home/benjamin/Philosophy/` was read into, written to, or drafted for by this task.** No manuscript prose for `Det-pm` or `Det-m` appears here or anywhere in this task's output.

---

## Part I — Deliverable (d): the correspondence record

### I.1 What each paper `\label` corresponds to in the Lean tree

Cited by `\label` only. Line numbers into `possible_worlds.tex` have been observed stale in three
independent extractions (drifts of ~30, ~60 and ~130 lines), so no line number appears in this
table or in any docstring this task wrote.

| Paper `\label` | Lean declaration | Path | Formalized? |
|---|---|---|---|
| `def:deterministic` | `TaskFrame.Deterministic` | `FormalSystem/Semantics/FrameProperty.lean` | **Yes**, in the tree's `Fib`-subsingleton idiom; `TaskFrame.deterministic_iff` records that it agrees with the paper's pointwise phrasing |
| `def:deterministic` (free consequence) | `TaskFrame.saturation_of_deterministic` | `FormalSystem/Semantics/FrameProperty.lean` | **Yes** — a deterministic frame's *Saturation* field is free |
| `lem:deterministic-singleton`, (⇒) half | `states_eq_of_deterministic` | `FormalSystem/Semantics/StarDeterminism.lean` | **Yes**, choice-free. Stated **pointwise on states**, not as history equality — weaker, sufficient, and free |
| `lem:deterministic-singleton`, (⇐) half | — | — | **Deliberately not.** ZFC via `thm:extension`/Zorn; nothing in this development needs it. See §I.3 |
| `lem:deterministic-singleton` at `F¹` (history-equality form) | `f1_eq_of_states_eq` | `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean` | **Yes**, at that one frame, where it is free from the pointwise form plus `ShiftSet.wh_ext` |
| `app:deterministic`, positive half | `determined_of_deterministic`, `stab_biconditional_starValidOn_of_deterministic`, `stab_iff_of_deterministic` | `FormalSystem/Semantics/StarDeterminism.lean` | **Yes**, choice-free (`#print axioms` → `[propext]`) |
| `app:deterministic`, negative half | `refute_determined` | `FormalSystem/Semantics/StarNonValidities.lean` | **Yes** (pre-existing; this task repaired its docstring, which asserted the positive half was not formalized) |
| `app:drift` — the frame `F°` | `fzeroFrame`, `F0` | `FormalSystem/Metalogic/Independence/DriftFrame.lean` | **Yes**, all six `FrameOver` axioms including `limit` and `saturation` |
| `app:drift` — `F°` is not deterministic | `fzero_not_deterministic` | `FormalSystem/Metalogic/Independence/DriftFrame.lean` | **Yes** |
| `app:drift` — the key lemma (histories are order-isomorphisms) | `fzero_bounds`, `fzero_lipschitz`, `fzero_continuous`, `fzero_strictMono`, `fzero_hits_future`, `fzero_hits_past`, `fzero_orderFlow` | `FormalSystem/Metalogic/Independence/DriftHistories.lean` | **Yes** |
| `app:drift` — `⊨_{F°} φ → ⊡φ` | `fzero_determined`; `determined_valid_on_non_deterministic` | `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` | **Yes** |
| `app:drift` — the `S_φ` induction | `satSet`, `starTruthAt_iff_mem_satSet`, `starValidOn_iff_satSet_univ` | `FormalSystem/Metalogic/Independence/StateSetTruth.lean` | **Yes**, and generically: proved once under hypotheses (H1)/(H2), instantiated at `F°` and `F¹` |
| `cor:no-characterization` — the frame `F¹` | `oneShift`, `F1`, `f1_deterministic` | `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean` | **Yes** |
| `cor:no-characterization` — `F¹`'s world-set characterization | `f1_total_eq_orbit`, `f1_states_eq`, `f1_states_sub` | `FormalSystem/Metalogic/Independence/RealTranslationFrame.lean` | **Yes**, free from `ShiftSet.total_eq_orbit` |
| `cor:no-characterization` — the conclusion | `fzero_starValidOn_iff_f1`, `deterministic_not_starDefinable` | `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` | **Yes** |
| `cor:occurrence` ("every state occurs at every time") | `fzero_stateOccurs`, `f1_stateOccurs` | `Independence/DriftHistories.lean`, `Independence/DeterminismUndefinable.lean` | **Not used.** Both frames get it from an **explicit affine witness**; the general theorem (Zorn-based) is deliberately bypassed |
| `app:deterministic-future` | — | — | **Deliberately not.** Needs store/recall; see Part II |
| `sent:det`, `Det`, `Det-pm`, `Det-m`, Theorem C | — | — | **Deliberately not.** Out of scope by plan non-goal; `Det-pm`/`Det-m` manuscript text is owned by PossibleWorlds task 105 |
| footnote collapse for non-temporal `φ` | `stab_atom_of_atom` | `FormalSystem/Semantics/StarTruth.lean` | **Yes** (pre-existing) |

### I.2 Where the Lean tree and the manuscript must agree

Four points, each a place where a divergence would be a real error rather than a presentational one:

1. **The determinism predicate's duration binder is unrestricted.** `TaskFrame.Deterministic`
   quantifies `d` over all of `F.Duration`. This matches `def:deterministic`'s own note that
   `def:task-relation`'s converse convention already extends `x` over all of `D`. It is **not**
   a stylistic choice: the singleton bridge applies determinism at the possibly negative duration
   `s - t`, and a `0 ≤ d` guard would make the bridge false. Any manuscript rewording that reads
   as forward-only determinism would diverge from the Lean statement in a way that matters.
2. **`app:deterministic` is an implication in both halves, never a characterization.** The Lean
   statements are `Deterministic F → ⊨_F (φ → ⊡φ)` and a refutation at one frame. The tree now
   *proves* the converse false (`determined_valid_on_non_deterministic`), so a manuscript sentence
   of the form "valid exactly over the Deterministic frames" would be false, not merely stronger.
3. **`lem:deterministic-singleton` is a biconditional in the manuscript and an implication in
   Lean.** That is deliberate and recorded at the Lean site: the (⇐) half is ZFC and unused. The
   two do not conflict; the Lean tree simply formalizes the half it needs.
4. **`app:drift`'s two proof deviations are recorded at the Lean sites, not silently taken.**
   Interpolation splits on `le_total (w + x) (v - 2y)` rather than using `λ := (v-w)/(x+y)`,
   avoiding the degenerate `x + y = 0` case; and *Saturation* goes through Mathlib's compactness
   lemma rather than an explicit finite-intersection argument. Both are recorded in
   `DriftFrame.lean`'s module docstring, so a reader comparing the two texts is not left to guess.

### I.3 What is deliberately **not** formalized, and why

| Not formalized | Reason |
|---|---|
| `lem:deterministic-singleton` (⇐): `⟨τ⟩_x = {τ}` ⟹ Deterministic | ZFC via `thm:extension` and Zorn; nothing downstream needs it. Formalizing it would add a choice dependence for no consumer |
| `Det`, `Det-pm`, `Det-m`, Theorem C | Need store and recall operators, which `StarFormula` does not have. See Part II |
| `app:deterministic-future` | Same |
| Generalization of the non-definability result to arbitrary frames | Would reintroduce choice: the general argument appeals to `cor:occurrence` for nonemptiness of `H_F` in the `□` case. Over `F°`/`F¹` that appeal is removable by explicit witnesses; at full generality it is not |
| The frame `F^N` and the forward-vs-bidirectional separation | Blocked on a finite-fibres saturation helper that may not exist; the bidirectional quantifier it would motivate is already secured by the predicate's binder plus its docstring |
| Any history-equality statement `⟨τ⟩_x = {τ}` at the general level | The pointwise state form is weaker, sufficient, and free |

### I.4 Rename list — apply when reading older secondary sources

Recorded so that a future reader does not restore a dangling reference:

| Old | Current |
|---|---|
| `Spherical` | `Saturation` |
| `cor:spherical-finite` | `cor:saturation-finite` |
| `app:non-deterministic` | **retired** — merged into `app:deterministic` |
| `def:frame-properties` (as the home of the Deterministic clause) | `def:frame-properties` now holds only Discrete/Dense/Complete; the Deterministic condition is `def:deterministic` |
| `def:BLplus-semantics` | **no longer exists** — repoint to `def:BLstar-semantics` |

### I.5 Relationship to the manuscript: read and record only

This task wrote nothing outside `specs/536_*/` and `FormalSystem/`. In particular it made no edit
to `possible_worlds.tex` and drafted no manuscript prose for `Det-pm` or `Det-m`. PossibleWorlds
task 105 owns that text and holds staged LaTeX for it (a Phase 3 display plus connecting prose,
and a Phase 5 theorem). Anyone picking up the follow-up in Part II should cite **Theorem C as a
report-level result pending paper integration** — never as manuscript text, and never as a
conjecture: it is proved, in task 105's own report, just not yet integrated.

---

## Part II — Deliverable (c): the store/recall follow-up **recommendation**

**This is a recommendation only. No Lean file in this task gained a store or recall constructor,
and none should until a follow-up task is opened.**

### II.1 Spawn-ready task description

> **Title**: Narrow world store/recall for L⋆ — a single world register, sufficient for `Det-m`
>
> **Type**: lean4
>
> **Goal**: Extend the evaluation point of `StarTruthAt` from `(τ, x)` to `(τ, x, μ)` with a
> **single** world register `μ : F.HF`, and add exactly two constructors — world-store `↑_M` and
> world-recall `↓_M` — to a new formula type. Then prove Theorem C's `Det-m` half: `Det-m`
> defines the deterministic frames, i.e. it is valid over `F` iff `F` satisfies
> `TaskFrame.Deterministic` (`FormalSystem/Semantics/FrameProperty.lean`).
>
> **Consume, do not duplicate**: `determined_of_deterministic` and `states_eq_of_deterministic`
> (`FormalSystem/Semantics/StarDeterminism.lean`) give the (⇐) direction's engine;
> `deterministic_not_starDefinable`
> (`FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean`) is the theorem this
> follow-up is the answer to, and is what makes the extension necessary rather than decorative.
>
> **Estimated size**: ~600-900 lines, one task.
>
> **Why a single register and not the full apparatus**: see II.2.
>
> **Known cost**: the transport-layer breakage table in II.3.
>
> **Choice asymmetry — read before scoping**: see II.4. The (⇒) direction of Theorem C is ZFC.
> Do not promise a choice-free pin for it.

### II.2 Why Option 1 (single register) and not Option 2 (full BL⋆)

| | Option 1 — world store/recall, one register | Option 2 — full `↑_T/↓_T/↑_M/↓_M`, `ℕ`-indexed vectors |
|---|---|---|
| Evaluation point | `(τ, x, μ)` | `(τ, x, v⃗, μ⃗)` with `v⃗ : ℕ → F.Duration`, `μ⃗ : ℕ → F.HF` |
| Buys | `Det-m`, which **defines** the deterministic frames exactly | `Det`, `Det-pm`, `app:deterministic-future`, the paper's BL⋆ proper |
| Time-shift invariance | **survives** — `μ` is carried untouched, there is no stored *time* | **breaks** — a shift must act on `v⃗` too, and the invariance statement must be restated on the whole point |
| `untl` / `snce` clauses | **unchanged** — `↓_M` is a history *swap*, not a time jump | changed |
| Vector-update lemmas | none — a single register needs no `ℕ`-indexing | a full layer of them |
| `truth_congr_ext` | one lemma restated (agreement of *both* `τ` and `μ`) | re-founded |
| Atomization / task 533 conservativity | survives outside recall scopes | **invalidated** — atomization's licensing fact is `stab_state_only`, which fails outright once `↓_M`/`↓_T` are inside a `⊡` scope |
| Estimate | ~600-900 lines, one task | 2500+ lines, multiple tasks |

**Recommendation: Option 1.** Option 2 should be revisited only if BL⋆ metatheory becomes a goal
in its own right, and its collision with task 533's conservativity route must be resolved first.

**The mechanism, in one sentence** — worth carrying into the follow-up's plan, because it explains
why the extension is *necessary* rather than convenient: the `(⊡)` clause passes the stored
register through **unchanged** when it swaps `τ` for `σ`, so a recall inside a `⊡` scope compares
the *same* stored world against an arbitrary alternative. That comparison is exactly what `⊡`
alone cannot express, and exactly why `deterministic_not_starDefinable` holds.

### II.3 Transport-layer breakage — the follow-up's known cost

| Lemma | File | Breakage under store/recall |
|---|---|---|
| `truth_congr_ext` | `FormalSystem/Semantics/StarTruth.lean` | **breaks structurally** under `↓_M`: pointwise-equal histories no longer suffice, since the register can point at a third history. Must be restated as agreement of both components |
| `starTruthAt_timeShift` | `FormalSystem/Semantics/StarTruth.lean` | breaks under a stored *time* (`↓_T`) only — **survives Option 1**, which stores no time |
| `stab_state_only` | `FormalSystem/Semantics/StarTruth.lean` | **fails outright** inside a recall scope: `⊡φ` no longer depends on the world state alone |
| `TruthCorr` / `TruthAntiIso` | `FormalSystem/Semantics/` | `Formula`-only; task 533's TD/swap soundness route relies on them |
| Atomization | `FormalSystem/Metalogic/Conservativity/Star/Atomization.lean` | its licensing fact **is** `stab_state_only`; the conservativity route is invalidated inside recall scopes |
| Pasting (`PS`/`US`/`FS`/`GS`) | `FormalSystem/Semantics/StarPasting.lean` | `SameStateAt`-based; re-derivation needed |

Two entries deserve emphasis for Option 1 specifically: `starTruthAt_timeShift` **survives**
(no stored time), and `stab_state_only` **does not** (that is unavoidable — it is the very
invariant the extension is designed to break).

### II.4 The choice asymmetry — record it in the follow-up's description

**The choice dependence tracks a *direction*, not a deliverable.** Any step of the form
"validity of a sentence ⟹ frame condition" needs Zorn, because it must *manufacture* separating
worlds, and `thm:extension` is the only tool for that. The opposite direction, "frame condition ⟹
validity", is safe.

| Result | Half of the bridge used | Choice |
|---|---|---|
| `determined_of_deterministic` — the collapse | (⇒) only | **choice-free** (`[propext]`) |
| `starTruthAt_iff_mem_satSet` — the generic state-set bridge | — | **choice-free** (`[propext]`) |
| `deterministic_not_starDefinable` | (⇒) only | argument choice-free; the reported `Classical.choice` is carrier-borne, inherited from `ℝ` (`fzero_not_deterministic`, proved by two `norm_num` facts, already reports it) |
| `lem:deterministic-singleton` (⇐) | — | **ZFC** (`thm:extension`, Zorn) |
| Theorem C (`Det-m`), ⇐ direction | (⇒) only | choice-free |
| Theorem C (`Det-m`), ⇒ direction — *concludes* a frame is deterministic | (⇐) | **ZFC** |

So deliverables (a) and (b) of this task carry an `#print axioms` pin, and the follow-up's
Theorem C **cannot** — in one direction. That is a cost signal, not a blocker: `Classical.choice`
is ordinary mathematics in this tree (see `Semantics/ShiftSet.lean`'s note on `reverse_repr`).
Record it in the follow-up's description so it is not discovered late.

### II.5 Non-goals for the follow-up, inherited from this task

- Do not restate `determined_of_deterministic` as a biconditional; the converse is now *proved
  false*, not merely unproved.
- Do not generalize the non-definability result to arbitrary frames without re-auditing the
  `cor:occurrence` appeal (§I.3).
- Do not argue by uniform substitution anywhere: it is unsound here. `p → ⊡p` is frame-valid over
  `F°` while `Fp → ⊡Fp` is refutable over `natFrame`.
- Do not write to `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`, and
  do not draft `Det-pm`/`Det-m` manuscript prose. Task 105 owns that text and holds staged LaTeX.
