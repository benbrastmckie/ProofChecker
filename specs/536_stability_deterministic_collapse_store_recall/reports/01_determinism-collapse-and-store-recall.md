# The Stability Modal and the Deterministic Task Frames

**Task**: 536 — stability deterministic collapse, its failing converse, and the store/recall correspondence
**Type**: lean4 · research
**Status**: researched
**Evidence of record**: `specs/536_stability_deterministic_collapse_store_recall/probes/01_determinism-collapse-probes.lean` (45 lines) and `probes/02_fzero-frame-probes.lean` (272 lines), both compiled sorry-free against the current tree with `lake env lean`.

---

## 1. Executive summary

The claim under correction — *"Determined `φ → ⊡φ` is valid exactly over the deterministic
frames"* — is false, and the paper already says so. But the correction that the task description
itself offers ("the region where `⊡` trivializes **is** the Deterministic frames, but membership
in that region is not expressible in L⋆") is *also* imprecise, and the imprecision matters for
what gets stated in Lean. There are **three distinct collapse phenomena**, and conflating any two
of them produces a false theorem:

| # | Collapse | Scope | Status |
|---|----------|-------|--------|
| **C1** | `φ → ⊡φ` valid for **non-temporal** `φ` | **every** task frame | paper footnote (§ `sub:RestrictedModalities`); already in the tree as `stab_atom_of_atom` |
| **C2** | `⟨τ⟩_x = {τ}` — `⊡` is *semantically* the identity | **exactly** the Deterministic frames (biconditional) | `lem:deterministic-singleton`; ⇐ direction is ZFC |
| **C3** | `φ → ⊡φ` valid for **every** L⋆ `φ` | a class **strictly larger** than the Deterministic frames | `app:deterministic` (⊇) + `app:drift` (strict) |

C2 is a biconditional; C3 is not. `⊡` trivializes *semantically* exactly on the Deterministic
frames, but trivializes *logically* on strictly more of them. The witness to strictness is the
paper's drift frame F°, on which `⟨τ⟩_x` is an uncountable set of distinct histories that are
nonetheless pairwise L⋆-indistinguishable at `x`.

**What was machine-checked in this research round** (both probe files sorry-free, no `Classical.choice`
introduced by the new proofs):

1. **Deliverable (a) is done, and it is choice-free.** `Deterministic F → ⊨_F ⊡φ ↔ φ` for every
   `StarFormula φ`, in 45 lines, using only the forward half of the singleton bridge. It does
   **not** need `thm:extension`, Zorn, or the paper's biconditional. This is strictly sharper than
   the paper's presentation suggests.
2. **Deliverable (b)'s single largest risk is retired.** F° **is** a legal `FrameOver realOrder`:
   all six axiom fields discharged, including the two that were flagged as doubtful — `limit`
   (which fails for the two-world frame F′ in a dense order) and `saturation` (discharged by
   Cantor's intersection theorem, since every fibre of F° is a compact interval). F° is verified
   non-deterministic. The whole order-isomorphism core of the key lemma — strict monotonicity,
   2-Lipschitz continuity, and forward/backward surjectivity by IVT — is machine-checked. F¹, the
   deterministic translation flow over ℝ, is also built and verified deterministic.
3. **The only unproved piece of (b) is the state-set induction `S_φ`**, and §5 gives a
   architecture for it that discharges F° and F¹ from one generic lemma.
4. **Deliverable (c): recommend a follow-up task, but a much narrower one than the full BL⋆
   store/recall apparatus.** §6 gives the cost analysis and a two-option recommendation.

Two further findings that are not deliverables but bear on how the deliverables must be stated:

5. **The choice dependence tracks a *direction*, not a deliverable** (§6.4). Any step of the form
   "validity of a sentence ⟹ frame condition" needs Zorn, because it must *manufacture* separating
   worlds. Deliverables (a) and (b) as scoped state the safe direction and are constructive; only
   the (⇒) half of the store/recall correspondence is ZFC. Stated with the scoping conditions that
   make it true — restating (a) as a biconditional, or generalizing (b) to arbitrary frames, breaks
   it.
6. **Uniform substitution is unsound in this setting** (§6.1) — `p → ⊡p` is frame-valid over F°
   while `Fp → ⊡Fp` is refutable over `F′`. No proof in this development may use a US argument,
   and every refuting instance must be a genuinely *temporal* formula: testing at atoms shows
   nothing (`app:deterministic`'s own countermodel refutes at `Fp`, not at `p`).
7. **`IsDeterministic` must quantify `x` over all of `D`, not the positive cone** (§5bis). This is
   not fidelity-to-the-paper: weakening it would make the frame `F^N` "Deterministic" and
   *falsify* the bridge lemma. Confirmed from three independent directions.

---

## 2. The exact statements, in the paper's terms

Cite by `\label`, never by line number: line numbers have now been observed stale in **three**
independent extractions from `possible_worlds.tex` (drifts of ~30, ~60 and ~130 lines). Two
renames also postdate most secondary sources: **`Spherical` is now `Saturation`** (and
`cor:spherical-finite` is now `cor:saturation-finite`), and **`app:non-deterministic` is
retired**, folded into `app:deterministic`.

### 2.1 `def:deterministic`

> A task frame `F = ⟨W, D, ⇒⟩` is **Deterministic** just in case `u = v` whenever `w ⇒_x u` and
> `w ⇒_x v` for `w, u, v ∈ W` and `x ∈ D`, holding in both temporal directions since
> `def:task-relation`'s converse convention already extends `x` over all of `D`.

**Formalization constraint (load-bearing).** This is **one bidirectional condition**, not a
conjunction of a forward and a backward clause. The quantifier `x ∈ D` already ranges over
negative durations, and `FrameOver.converse` (`TaskRel w d u ↔ TaskRel u (-d) w`) is a *structure
field* in Lean, so the past-directed instances come free. Do **not** define a separate
backward-determinism predicate and conjoin it: that diverges from the paper and makes the forward
half of the bridge lemma look like it needs more than it does. Restricting the quantifier to
`0 ≤ x` yields the strictly weaker **forward** determinism, which does **not** support the bridge
lemma (see §7 on task 105's `F^N`).

### 2.2 `lem:deterministic-singleton` (the bridge, a biconditional)

> `F` is Deterministic if and only if `⟨τ⟩_x = {τ}` for all `τ ∈ H_F` and `x ∈ D`.
>
> *Footnote*: Only the left-to-right direction is choice-free. The converse appeals to
> `thm:extension` and hence to Zorn's lemma, and so is a theorem of ZFC, as with `cor:occurrence`.

- **(⇒)** uses no frame axiom beyond `def:world-history`, and is choice-free. It applies
  Determinism at duration `y − x`, which is negative when `y < x` — hence the bidirectional
  reading above.
- **(⇐)** is by contraposition and uses Seriality + Limit (to get `⇒_0 = id`), `lem:nullity`, and
  `thm:extension`. It builds the two-point partial histories `τ₁ = {0 ↦ w, x ↦ u}` and
  `τ₂ = {0 ↦ w, x ↦ v}` and extends both to total histories.

**Convexity trap, and why the tree is already safe.** The domain `{0, x}` is **not convex**. The
paper's proof is admissible only because convexity is required of *world* histories while
`thm:extension` is stated for *partial* histories. This tree gets that right already:
`FormalSystem/Semantics/Extension/Extension.lean:208` reads
`theorem extension (F : TaskFrame) (τ : PartialHistory F) : ∃ σ : F.HF, Extends σ.val.toPartialHistory τ`
— the hypothesis is a `PartialHistory`, which carries `domain`, `nonempty_domain`, `states` and
`respects_task` but **no** `convex` field (that field is added by `WorldHistory`, which *extends*
`PartialHistory`). So the paper's argument transcribes directly. **No action needed**; recorded so
that a future reader does not "fix" it.

### 2.3 `app:deterministic` (both halves, after the merge)

> `⊨_F φ → ⊡φ` for every Deterministic task frame `F`, while `⊭_{F'} φ → ⊡φ` for some task frame
> `F'` that is not.

Positive half, verbatim:

> Let `F = ⟨W, D, ⇒⟩` be Deterministic. Let `M = ⟨W, D, ⇒, |·|⟩` be a model over `F` with
> `τ ∈ H_F` and `x ∈ D` where `M,τ,x ⊨ φ`. By `lem:deterministic-singleton`, `⟨τ⟩_x = {τ}`, so
> `M,σ,x ⊨ φ` for all `σ ∈ ⟨τ⟩_x`. Therefore `M,τ,x ⊨ ⊡φ` by `def:BLstar-semantics`. Since `M`,
> `τ`, and `x` were chosen arbitrarily, `⊨_F φ → ⊡φ` for every deterministic task frame `F`.

This uses **only** the (⇒) direction of the bridge, i.e. the choice-free one — which is exactly
why deliverable (a) below carries no ZFC dependence.

Negative half — the frame `F′`: `D` a **discrete** temporal order with least positive duration
`d`; `W = {w₀, w₁}`; `w ⇒_0 w'` iff `w = w'`, and `w ⇒_z w'` for all `w, w'` and `z > 0`. Model
`|p| = {w₀}`; `τ(y) = w₀` everywhere; `σ(y) = w₁` iff `y = d`. Then `σ ∈ ⟨τ⟩_0`,
`M,τ,0 ⊨ Fp`, `M,σ,0 ⊭ Fp`, so `M,τ,0 ⊭ Fp → ⊡Fp`.

**The refuting instance is `φ := Fp`, not an atom.** At an atom the schema holds even in `F′` by
C1. Any separating construction must separate at a *temporal* formula; testing at atoms shows
nothing.

**Discreteness in `F′` is a genuine hypothesis, not scene-setting.** The cone is
`(w)_x := ⋃_{|y| < x} fib(w, y)`, and in `F′` `fib(w,0) = {w}` while `fib(w,z) = W` for every
`z ≠ 0`. So `(w)_x = W` as soon as *any* `y` with `0 < |y| < x` exists. The step `(w)_d = {w}`
works only because `d` is *least* positive. **In a dense order every `(w)_x = W` and Limit fails
outright**, so `F′` is not a task frame there.

### 2.4 `app:drift` (recovered) — F° and the failure of the converse

**There are two texts, and this report cites both — keep them distinct.**

- **The live footnote** (working tree, `sub:OpenFuture`, sentence + footnote): a *summary*, with
  no theorem, no label, no axiom verification, and no induction. A `grep` for `F^{\circ}` over the
  whole current `.tex` returns **exactly one hit**, inside this footnote. Verbatim:

  > *Determined* does not characterize the task frames satisfying **Deterministic**.
  >
  > *Footnote*: Let `F°` have `W = ℝ` and `D = ⟨ℝ,+,0,≤⟩` with `w ⇒_x u` just in case
  > `x ≤ u−w ≤ 2x` for `x ≥ 0`, and let `F¹` agree except that `u = w + x`, so that `F¹` is
  > **Deterministic** whereas `F°` is not. Since every possible world over either task frame is an
  > order-isomorphism of `(ℝ,<)` onto itself, an induction on complexity assigns each store-free
  > and recall-free `φ` the same set of world states at which it is true over both task frames,
  > and so no set of such sentences characterizes the **Deterministic** task frames.

  (The line immediately above it is a live source `TODO`: *"It would be good to say what
  axiomatizes determinism in the expanded language here, or reference the axiom where it goes in
  the discussion below, making sure these match."* — deliverable (c) is the answer to that TODO.)

- **The deleted rigorous version**: `app:drift` (T18) and `cor:no-characterization` (C7),
  commented out by commit `692dd4b7` (19 Aug, *"cut drift-frame theorem and non-characterization
  corollary to a footnote"*), the dead block then deleted by commit `8934748e` (a deliberate
  dead-source cleanup). **Nothing was accidentally clobbered.** Persisted with a provenance header
  at `.../PossibleWorlds/specs/105_characterize_deterministic_task_frames/reports/recovered-drift-noncharacterization.tex`;
  re-derivable with `git show 692dd4b7 -- JPL/possible_worlds.tex`.

**Source-reliability note, stated carefully because it is easy to get backwards.** The *footnote*
was **never deleted** and is in the working tree today; what was deleted is the *rigorous* version.
And the deleted `app:drift` proof **discharges all four frame axioms explicitly**, including the
compactness-plus-FIP argument for Saturation. So this is **a verified result that was cut for
length**, not an unverified authorial assertion. Do not write that the paper asserts F°'s
framehood without proof. (This report's `probes/02` independently re-derives all six Lean axiom
fields and agrees with the recovered proof line for line.)

**The footnote names BOTH F° and F¹.** The two-frame framing in this task's description comes from
there and is correct. **The recovered text is pre-rename** — it says "Spherical" where the current
manuscript says "Saturation" — and it cites `def:BLplus-semantics`, a label that **no longer
exists** (0 occurrences in the working tree). `def:frame-properties` now holds only
Discrete/Dense/Complete; the Deterministic condition is `def:deterministic`, and
`def:BLstar-semantics` has been added, carrying Stability / `\timeStore` / `\timeRecall`. Anyone
restoring the deleted proof must repair those references.

> **Statement.** There is a non-deterministic frame over which `φ → ⊡φ` is valid for every
> sentence `φ` of BL⁺ extended with `⊡` — equivalently, of BL⋆ without the store and recall
> operators.

**The frame F°**: `W = ℝ`, `D = ⟨ℝ, +, 0, ≤⟩`, and `w ⇒_x u` iff `x ≤ u − w ≤ 2x` for `x ≥ 0`,
extended to negative durations by `def:task-relation`. *Each world state drifts rightward along ℝ
at a rate nondeterministically between 1 and 2.* So `fib(w,x) = [w+x, w+2x]` for `x ≥ 0` and
`[w+2x, w+x]` for `x < 0` — **every fibre is a compact interval**, which is what makes Limit and
Saturation go through where they fail for `F′`.

**Worlds.** `H_{F°}` is exactly the functions `τ : ℝ → ℝ` with `y − x ≤ τ(y) − τ(x) ≤ 2(y − x)`
whenever `x < y`. Every world is strictly increasing and 2-Lipschitz hence continuous, and
unbounded in both directions. **Every possible world is therefore an order-isomorphism of `(ℝ,<)`
onto itself, passing through every world state exactly once.** And for any `w` and `x` the
translation `δ(t) := t + w − x` is a world with `δ(x) = w`, so every world state occurs at every
time in some world.

**The key lemma (the object to formalize).** For every well-formed `φ` and model `M` over F°
there is a set `S_φ ⊆ W` with `M,τ,x ⊨ φ` iff `τ(x) ∈ S_φ`, for all `τ ∈ H_{F°}` and `x ∈ D` —
**truth depends only on the world state of evaluation.** By induction on complexity:

- `S_{p_i} = |p_i|`, `S_⊥ = ∅`, `S_{φ→ψ} = (W \ S_φ) ∪ S_ψ`.
- **Until**: each world restricts to an order-isomorphism of the times `z > x` onto the world
  states `v > τ(x)`, matching intermediate times `x < y < z` with intermediate states
  `τ(x) < u < v`. Hence `S_{φUψ} = {w : ∃ v > w, v ∈ S_ψ ∧ (w,v) ⊆ S_φ}`, and symmetrically
  `S_{φSψ} = {w : ∃ v < w, v ∈ S_ψ ∧ (v,w) ⊆ S_φ}`.
- **Box**: since every world state occurs at every time, `{ρ(x) : ρ ∈ H_{F°}} = W`, so
  `S_{□φ} = W` when `S_φ = W` and `∅` otherwise.
- **Stability**: `σ ∈ ⟨τ⟩_x` are exactly those with `σ(x) = τ(x)`, so `S_{⊡φ} = S_φ`.

**Conclusion**: `⊨_{F°} φ → ⊡φ` while F° is non-deterministic (`0 ⇒_1 1` and `0 ⇒_1 2`).

**Store/recall is essential — a worked refutation, not an assertion.** Let `|p| = [3/2, ∞)`,
`τ(t) := t`, `σ(t) := 2t`. Then `τ ∈ ⟨σ⟩_0` while `σ(1) = 2 ∈ |p|` and `τ(1) = 1 ∉ |p|`. So
`M,σ,0,v⃗[1/v₂] ⊨ ↓²_T p` but `M,σ,0,v⃗[1/v₂] ⊭ ⊡↓²_T p`, witnessed by `τ`; and `σ` itself
witnesses the failure of `⊡↓²_T ¬p` at the same point, so **both** disjuncts of `sent:det` fail
there. **F° refutes `sent:det` while validating Determined over the operator-only language.**
This is the sharpest available evidence for deliverable (c).

### 2.5 `app:deterministic-future` and the store/recall sentences

> `↑¹_T F ↑²_T ↓¹_T (⊡↓²_T ¬φ ∨ ⊡↓²_T φ)` is valid over every deterministic task frame, and
> invalid over some non-deterministic task frame.

The countermodel is the **same** `F′` as `app:deterministic`, so its discreteness hypothesis
carries over: formalize `F′` **once**, with discreteness explicit, and share it between the two
appendices. (See §5.4 — the tree very nearly has it already.)

Store/recall clauses (`sub:Extension`): the evaluation point carries **both** a stored-time vector
`v⃗ = ⟨v₁, v₂, …⟩` and a stored-world vector `μ⃗ = ⟨μ₁, μ₂, …⟩`:

```
(↑_T)  M,τ,x,v⃗,μ⃗ ⊨ ↑ⁱ_T φ  iff  M,τ,x,v⃗[x/vᵢ],μ⃗ ⊨ φ
(↓_T)  M,τ,x,v⃗,μ⃗ ⊨ ↓ⁱ_T φ  iff  M,τ,vᵢ,v⃗,μ⃗ ⊨ φ
(↑_M)  M,τ,x,v⃗,μ⃗ ⊨ ↑ⁱ_M φ  iff  M,τ,x,v⃗,μ⃗[τ/μᵢ] ⊨ φ
(↓_M)  M,τ,x,v⃗,μ⃗ ⊨ ↓ⁱ_M φ  iff  M,μᵢ,x,v⃗,μ⃗ ⊨ φ
```

**Notation trap.** Task 105's report 02 renders these in ASCII as `⇃` and `↾`, and the glyphs read
**backwards** relative to their meaning (`⇃¹` is `\timeStore`, i.e. `↑`; `↾¹` is `\timeRecall`,
i.e. `↓`). **The LaTeX macro is ground truth**; never transcribe from the ASCII rendering.

Authoritative macro forms:

```
Det (= sent:det)  \timeStore^1 F \timeStore^2 \timeRecall^1 (\Stability\timeRecall^2 \neg\varphi \vee \Stability\timeRecall^2 \varphi)
Det-pm            \timeStore^1 \always \timeStore^2 \timeRecall^1 (\Stability\timeRecall^2 \neg\varphi \vee \Stability\timeRecall^2 \varphi)
Det-m             \worldStore^1 \Stability \always (\varphi \leftrightarrow \worldRecall^1 \varphi)
```

Det uses `F` (Future); Det-pm replaces it with `always`; Det-m is the world-store variant.

---

## 3. The corrected statement set (what should be true in the Lean tree)

```
(T1)  Deterministic F  ↔  ∀ τ ∈ H_F, ∀ x, ⟨τ⟩_x = {τ}                    -- ⇐ is ZFC
(T2)  Deterministic F  →  ⊨_F ⊡φ ↔ φ,   for every StarFormula φ          -- choice-free  [DONE]
(T3)  ¬(T2 converse):  F° is non-Deterministic and ⊨_{F°} φ → ⊡φ          -- app:drift
(T4)  Deterministic is not L⋆-definable: F° and F¹ validate the same StarFormulas  -- cor:no-characterization
      (an INDISTINGUISHABLE pair, not a separating one: they agree, and differ only in determinism)
(T5)  ⊨_{F′} is a task frame only over a DISCRETE D, and ⊭_{F′} Fp → ⊡Fp  -- already checked in tree
(T6)  Det-pm and Det-m each define the Deterministic frames exactly       -- needs store/recall
```

**Correction to the task description's own framing.** The description says *"the region where `⊡`
trivializes **is** the Deterministic frames, but membership in that region is not expressible in
L⋆."* That reads the region as C2 while the sentence about expressibility is about C3. The
accurate statement splits into two: the region where `⊡` trivializes **semantically** (`⟨τ⟩_x` a
singleton) **is** exactly the Deterministic frames, by (T1); the region where `⊡` trivializes
**logically** (`Determined` valid) **strictly contains** them, by (T3); and neither region is
L⋆-definable, by (T4). Recommend the plan carry all three sentences, not one.

---

## 4. Deliverable (a) — DONE, machine-checked, choice-free

`probes/01_determinism-collapse-probes.lean`, 45 lines, compiles clean.

```lean
def TaskFrame.IsDeterministic (F : TaskFrame) : Prop :=
  ∀ (w u v : F.WorldState) (x : F.Duration), F.TaskRel w x u → F.TaskRel w x v → u = v

theorem states_eq_of_deterministic (hD : TaskFrame.IsDeterministic F)
    {τ σ : WorldHistory F} (hτ : τ.IsTotal) (hσ : σ.IsTotal) {t : F.Duration}
    (h : SameStateAt τ σ t) (s : F.Duration) :
    τ.states s (hτ s) = σ.states s (hσ s) := by
  have hτr := τ.respects_task t s (hτ t) (hτ s)
  have hσr := σ.respects_task t s (hσ t) (hσ s)
  rw [h (hτ t) (hσ t)] at hτr
  exact hD (σ.states t (hσ t)) _ _ (s - t) hτr hσr

theorem stab_iff_of_deterministic (hD : TaskFrame.IsDeterministic F) (M : TaskModel F)
    {τ : WorldHistory F} (hτ : τ.IsTotal) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (.stab φ) ↔ StarTruthAt M τ t φ

theorem determined_starValidOn_of_deterministic (hD : TaskFrame.IsDeterministic F)
    (φ : StarFormula) : F.StarValidOn (.imp φ (.stab φ))

theorem stab_biconditional_starValidOn_of_deterministic (hD) (φ) :
    F.StarValidOn (.imp (.stab φ) φ) ∧ F.StarValidOn (.imp φ (.stab φ))
```

### Three engineering findings

1. **It is choice-free.** `states_eq_of_deterministic` is the (⇒) half of
   `lem:deterministic-singleton` and consumes only `WorldHistory.respects_task` plus
   `IsDeterministic` at the (possibly negative) duration `s - t`. No `thm:extension`, no Zorn, no
   `F.serial`, no `F.limit`, no `F.saturation`. **State this explicitly in the Lean docstring** —
   it is strictly sharper than the paper's biconditional presentation suggests, and it means (a)
   and (c) sit on opposite sides of a choice boundary (§6.4).

2. **Do not state the bridge as history equality.** The paper's `⟨τ⟩_x = {τ}` is an equality of
   *history objects*. In Lean that would need funext plus proof irrelevance over
   `WorldHistory`'s dependent `states : (t : F.Duration) → domain t → F.WorldState` field. The
   pointwise form above is weaker, sufficient, and free: `truth_congr_ext`
   (`Semantics/StarTruth.lean`) already converts pointwise state agreement into L⋆ truth
   agreement, for *every* `StarFormula` including the `stab` case. Setting the bridge up as an
   equality is pure avoidable cost.

3. **The `x : F.Duration` quantifier must stay unrestricted.** `states_eq_of_deterministic`
   applies `hD` at `s - t`, negative whenever `s < t`. A `0 ≤ x`-guarded predicate breaks the proof
   at exactly that point — which is the Lean shadow of task 105's `F^N` observation that `Det`
   defines only forward determinism.

### Placement recommendation

`TaskFrame.IsDeterministic` belongs in `FormalSystem/Semantics/FrameProperty.lean`, beside
`IsDense` / `IsDiscrete` / `IsSuccArchDiscrete` / `IsComplete` / `IsDedekind` — it is exactly the
same kind of object (a `TaskFrame → Prop` transcribing a `def:`-level frame condition), and that
module's docstring conventions already cover how such predicates are named and cited. The collapse
theorems belong beside the other `⊡` validities in `FormalSystem/Semantics/StarTruth.lean`, or in a
new `Semantics/StarDeterminism.lean` if `StarTruth.lean` is judged full.

---

## 5. Deliverable (b) — frames built and verified; one lemma remains

`probes/02_fzero-frame-probes.lean`, 272 lines, compiles clean.

### 5.1 F° is a legal task frame — the flagged risk, resolved positively

The two-sided extension is the load-bearing encoding choice. The paper states the relation only
for `x ≥ 0`; `FrameOver.converse` forces an extension to all of `D`, and the extension that makes
`converse` hold **on the nose** is the unordered interval:

```lean
def fzeroRel (w : ℝ) (d : ℝ) (u : ℝ) : Prop := u - w ∈ Set.uIcc d (2 * d)
```

For `d ≥ 0` this is `[d, 2d]`; for `d ≤ 0` it is `[2d, d]`, which is exactly `fzeroRel u (-d) w`.
All six `FrameOver` fields discharged:

| Field | How | Note |
|---|---|---|
| `nullity_identity` | `uIcc 0 0 = {0}` | trivial |
| `converse` | `mem_uIcc` + `linarith` | the encoding is chosen to make this hold definitionally-modulo-`linarith` |
| `serial` | `u := w + x`, `v := w - x` | `d ∈ uIcc d (2d)` in both signs |
| `comp` | explicit interpolant, split on `le_total (w+x) (v-2y)`: `v - 2y` or `w + x` | **note**: the repo's `Compositional` is confined to `0 ≤ x, 0 ≤ y`, so mixed-sign composition — which F° genuinely *fails* — is never demanded. Had `comp` been two-sided, F° would not be a frame. Worth a docstring. |
| `limit` | `x ∈ uIcc y (2y) → \|x\| ≤ 2\|y\|`, so the cone is inside `(w-2x, w+2x)` | **the flagged risk; it holds** |
| `saturation` | Cantor: `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed` | every fibre is `Set.Icc`; every segment is `Fib ∩ Fib` |

**Two deviations from the paper's proof, both deliberate and both improvements.**

1. **The interpolant.** `app:drift` factors `w ⇒_{x+y} v` by setting `λ := (v−w)/(x+y) ∈ [1,2]`
   and `u := w + λx`, which needs a **separate degenerate argument** when `x + y = 0`. The probe
   instead splits on `le_total (w+x) (v−2y)` and takes `u := v − 2y` or `u := w + x`. **No
   division, no degenerate case**, four `linarith` goals. Strictly cleaner proof of the same
   statement; record the deviation in the Lean docstring so a reader comparing against the paper
   is not confused.
2. **Saturation.** The paper argues compactness + the finite intersection property; the probe uses
   Mathlib's Cantor lemma `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed`
   directly on the `⊇`-directed family. A **topology-free alternative** exists and may be preferred
   at plan time: every fibre is an `Set.Icc`, every segment is `Icc ∩ Icc = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂)`
   by `Set.Icc_inter_Icc`, and a `⊇`-directed family of nonempty `Icc`s has `aᵢ ≤ b_j` pairwise, so
   `c := sSup {left endpoints}` lies in every member — `csSup`/`le_csSup`/`Real.sSup_le` suffice.
   The compactness route is already compiled, so this is an option, not a repair.
   (Note the tree is **not** topology-free: `Metalogic/Bundle/LimitMCS.lean` and
   `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` already import
   `Mathlib.Topology.*`. The "no topology" remark at `Semantics/TaskFrame.lean:897` is about the
   *cone* topology specifically, not a repo-wide ban. This softens R6 below.)

**`limit_of_shift` does not apply to F°** — the relation is not functional, so there is no position
function. The direct proof is ~10 lines and is what the probe uses.

**Why F° survives density where `F′` does not**, stated as the contrast the plan should record:
`F′`'s fibres at nonzero duration are *all of `W`*, so its cone blows up unless `D` is discrete;
F°'s fibres are *bounded intervals shrinking linearly to `{w}`*, so its cone shrinks in any order.
The two frames are **not interchangeable** and live in different frame classes.

Also machine-checked: `fzero_not_deterministic` (`0 ⇒_1 1` and `0 ⇒_1 2`).

### 5.2 The order-isomorphism core — machine-checked

Stated on the bare state function `f : ℝ → ℝ` with hypothesis
`hf : ∀ s t, fzeroRel (f s) (t - s) (f t)` (which is exactly `respects_task` for a total history):

```lean
theorem fzero_bounds  {s t} (hst : s ≤ t) : t - s ≤ f t - f s ∧ f t - f s ≤ 2 * (t - s)
theorem fzero_lipschitz  : LipschitzWith 2 f
theorem fzero_continuous : Continuous f
theorem fzero_strictMono : StrictMono f
theorem fzero_hits_future {x v} (hv : f x < v) : ∃ c, x < c ∧ f c = v
theorem fzero_hits_past   {x v} (hv : v < f x) : ∃ c, c < x ∧ f c = v
```

**Independently corroborated.** A separate session, without sight of the paper, derived exactly
this: every total history of F° is a strictly increasing 2-Lipschitz bijection `ℝ → ℝ`; hence
`{τ(s) : s > t} = (τ(t), ∞)` *exactly*, with no dependence on `τ` beyond its value at `t`; hence
for an atom `p` with truth-set `P`, `Fp` at `(τ,t)` iff `P ∩ (τ(t), ∞) ≠ ∅`, depending only on
`τ(t)`; hence any two histories agreeing at `t` agree on `Fp`, so `Fp → ⊡Fp` is valid on F°. That
is the `untl` case of the `S_φ` induction, rediscovered from a completely separate direction — a
useful check, given that the primary source for the recovered proof is a file pulled from git
history.

`fzero_hits_future` is the crux, and it is short: from `f x < v`, put `a := x + (v - f x)/2` and
`b := x + (v - f x)`; the bounds give `f a ≤ v ≤ f b`, and `intermediate_value_Icc` on the
Lipschitz-hence-continuous `f` produces `c ∈ [a,b]` with `f c = v` and `c ≥ a > x`.
`fzero_hits_past` is the mirror. **This is the "real mathematical content and the expensive part"
of the key lemma, and it is done.**

### 5.3 F¹ — cheap, and worth keeping

`app:drift` alone gives the weaker **non-characterization** claim: F° is non-deterministic and
validates Determined, which with `app:deterministic` already refutes the exact-characterization
claim. But the paper does **not** stop there — `cor:no-characterization` is the companion result,
and it is exactly deliverable (b):

> **`cor:no-characterization`**: No set of sentences of BL⋆ without the store and recall operators
> characterizes the **Deterministic** frames.

Its proof introduces F¹ explicitly:

> Let `F¹ = ⟨W, D, ⇒¹⟩` agree with `F°` from `app:drift` except that `w ⇒¹_x u` just in case
> `u = w + x`, a **Deterministic** frame whose possible worlds are exactly the translations
> `τ(t) := t + c` for `c ∈ ℝ`, each an order-isomorphism of `(ℝ,<)` passing through every world
> state at every time. The induction of `app:drift` then applies verbatim to `F¹`, where
> `S_{⊡φ} = S_φ` holds over `F¹` because `⟨τ⟩_x = {τ}` by `lem:deterministic-singleton`, and so
> truth over either frame depends only on the world state of evaluation through the same sets
> `S_φ`, **whose recursion mentions only the order on `W` and neither task relation**. Since
> validity over either frame requires that `S_φ = W` under every interpretation, exactly the same
> sentences without store and recall operators are valid over `F°` and `F¹`. Any such set of
> sentences valid over every **Deterministic** frame is thus valid over `F¹` and so over the
> non-deterministic `F°`, and therefore characterizes no class excluding it.

**The emphasised clause is the crux for Lean.** The `S_φ` recursion is a function of `(W, <)`
*alone*; the frames enter **only** through which functions count as possible worlds, and both
yield order-isomorphisms of `(ℝ,<)`. So this is **one theorem plus two instantiations**, not two
parallel developments — which is the architecture §5.4 recommends.

F¹ is nearly free: `foneRel w d u := u = w + d` over `rOrder`, six axioms in ~30 lines
(`saturation` by the functional-relation argument — every fibre and segment is a singleton or
empty), plus a one-line `fone_deterministic`. All machine-checked in `probes/02`.

Note also `FormalSystem/Semantics/ShiftSet.lean` builds exactly F¹'s shape generically
(`TaskRel w d u := u = sh w d`, all seven fields discharged, with `total_eq_orbit` giving that
every total history is the orbit history). If F¹ is wanted with less bespoke code, instantiate
`ShiftSet` at `Carrier := ℝ`, `sh := (· + ·)` rather than rebuilding; the probe's direct version
exists because it was faster to write, not because `ShiftSet` is unsuitable.

### 5.4 What remains: the `S_φ` induction

Recommended architecture — **one generic lemma, two instantiations**, rather than two parallel
inductions:

```lean
def satSet (V : ℝ → Atom → Prop) : StarFormula → Set ℝ
  | .atom p   => {w | V w p}
  | .bot      => ∅
  | .imp φ ψ  => (satSet V φ)ᶜ ∪ satSet V ψ
  | .box φ    => if satSet V φ = Set.univ then Set.univ else ∅
  | .stab φ   => satSet V φ
  | .untl ψ φ => {w | ∃ v, w < v ∧ v ∈ satSet V φ ∧ ∀ u, w < u → u < v → u ∈ satSet V ψ}
  | .snce ψ φ => {w | ∃ v, v < w ∧ v ∈ satSet V φ ∧ ∀ u, v < u → u < w → u ∈ satSet V ψ}
```

Bridge theorem, stated over an arbitrary `F : FrameOver rOrder` with `F.WorldState = ℝ` and two
hypotheses:

- **(H1)** every total history's state function is strictly monotone and hits every strictly
  greater state at a strictly later time and every strictly lesser state at a strictly earlier
  time — *machine-checked for F°, trivial for F¹*;
- **(H2)** every world state lies on some total history at every time (the translation history) —
  *this is what the `box` case needs*;

concluding `StarTruthAt M τ x φ ↔ τ.states x _ ∈ satSet M.valuation φ`. Then:

```
F°.StarValidOn φ  ↔  satSet V φ = univ for every V  ↔  F¹.StarValidOn φ
```

- **Cost estimate**: 250–400 lines beyond the probes. **Risk: LOW** — the expensive part (H1) is
  already checked, the `stab` case is `S_{⊡φ} = S_φ` (one line), and the `untl`/`snce` cases are
  a change of variables along the order-isomorphism.
- **`box` case caution**: `satSet` is defined by a `Set` equality test, which is not decidable;
  the `if` needs `open scoped Classical` (`StarTruth.lean` already does this) or a
  `Set.univ = · ∨ ∅ = ·` disjunction encoding. Prefer the latter if `Decidable` friction appears.

### 5.5 Terminology, and two frames explicitly ruled out as substitutes

**F° and F¹ are an *indistinguishable* pair, not a "separating" pair.** They are a pair precisely
because they **agree** on every store-free, recall-free sentence while differing in determinism;
the non-definability argument is elimination-by-indistinguishability. Calling them "separating"
inverts the mechanism and has already misled one reader into expecting F° to *refute* Determined,
which it does not — it *validates* it. Use "indistinguishable pair" in the Lean docstrings.

- **`F′` (the two-world discrete countermodel) cannot serve deliverable (b).** It *refutes*
  Determined, so it is L⋆-**distinguishable** from every Deterministic frame — the opposite of what
  non-definability needs. It serves `app:deterministic`'s negative half only.
- **A ℤ-carrier version of F° does not work either.** Over `W = D = ℤ` the histories are the maps
  with `τ(t+1) - τ(t) ∈ {1,2}`, which are **not** surjective onto ℤ, so the `untl` case of the
  `S_φ` induction fails (a history's future skips states). **The choice of ℝ is essential**, and
  the bi-Lipschitz bracket `[d, 2d]` is exactly what forces surjectivity via IVT. Record this so
  nobody "simplifies" the construction to ℤ.

### 5.6 `F′` is nearly already in the tree — do not rebuild it

`FormalSystem/Semantics/TaskFrame.lean:1602` defines
`FrameOver.natFrame` with `WorldState := Nat` and `TaskRel := fun w d u => d ≠ 0 ∨ w = u`, with all
six axioms discharged by a reusable `*_of_permissive` helper family, **and with
`[SuccOrder D] [NoMaxOrder D]` binders** — i.e. the tree already carries `F′`'s discreteness
hypothesis exactly where the paper needs it. Independent corroboration that the discreteness
condition is real.

Moreover `app:deterministic`'s negative half is **already machine-checked**: task 535's probe D4,
`refute_determined (p : Atom) : ¬ StarValid (.imp (someFuture (.atom p)) (.stab (someFuture (.atom p))))`
in `specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean:439`, over
`NF := FrameOver.natFrame (D := ℤ)`. Promote that probe rather than writing a new `F′`.

---

## 5bis. Forward determinism vs. Deterministic: the frame `F^N`

This is the fact behind "one bidirectional condition, not two" (§2.1), and it is now confirmed
from **three** independent directions: the paper's own `def:deterministic` wording, Lean's
`FrameOver.converse` structure field, and the counterexample below.

**`F^N`** (task 105 report 02; machine-verified by a frame-check script in the PossibleWorlds
repo): `W = ℕ`, `D = ⟨ℤ,+,0,≤⟩`, `f(0) = 0` and `f(n) = n−1`, with `w ⇒_n u` iff `u = fⁿ(w)` for
`n ≥ 0`, negatives by the converse convention.

| Axiom | Discharge |
|---|---|
| Seriality | surjectivity of `f` |
| Compositionality, both directions | `f^{x+y} = f^y ∘ f^x` |
| `⇒_0 = id` | immediate |
| Limit | least positive duration is `1`, so `(w)_1 = fib(w,0) = {w}` |
| **Saturation** | **by FINITE FIBRES, not finite `W`** — see below |

**Saturation subtlety — do not get this wrong.** `cor:saturation-finite` **does not apply**: it
requires `W` finite, and here `W = ℕ`. The argument is that `f^{−m}(0) = {0,…,m}` and
`f^{−m}(w) = {w+m}` for `w > 0`, so all fibres are finite, and a downward-directed family of
nonempty finite sets has a least-cardinality member contained in all of them. **If `F^N` is
formalized, the tree needs a finite-*fibres* variant of the saturation helper, which may not
exist** — the existing `*_of_permissive` family (`Semantics/TaskFrame.lean:1602ff`) covers the
permissive class, not this one. **Flag as a gap at plan time.**

`F^N` is **forward-deterministic** (`⇒_x` is a function for every `x ≥ 0`) but **not
Deterministic**: `fib(0, −1) = {0, 1}`, i.e. `0 ⇒_{−1} 0` and `0 ⇒_{−1} 1`. The separating worlds
are `τ(n) = 0` and `σ(n) = max(0, −n)`, both total, agreeing at `0` and differing at every `n < 0`.
So `⟨τ⟩_0 ≠ {τ}` while `F^N` validates `sent:det`.

**What it shows**: `sent:det`, which uses `Future`, defines only **forward** determinism — a
semiflow, a monoid action — whereas `Deterministic` quantifies `x` over all of `D` and is
bidirectional, a flow, a group action. `F^N` is irreversible dynamics with an absorbing state:
Laplacian about the future, indeterminate about the past. This is why `Det-pm` (with `always` in
place of `Future`) is needed for the exact correspondence.

**Consequence, and the reason it matters for Lean**: weakening `IsDeterministic`'s quantifier to
`0 ≤ x` would make `F^N` "Deterministic" and **falsify the bridge lemma**. The unrestricted
quantifier is not stylistic fidelity to the paper — getting it wrong breaks a theorem.

**A constraint on any future witness: it must be infinite.** On a finite `W`, Seriality makes each
`⇒_x` (`x ≥ 0`) surjective, and a surjective self-map of a finite set is injective, hence
bidirectionally deterministic. So **no finite frame separates forward determinism from
Deterministic**, and `F^N`'s infinitude is essential rather than incidental. Do not overgeneralize
this: it says nothing about separating *Determined-validity*, where the finite two-world `F′`
works perfectly well.

---

## 6. Deliverable (c) — what store/recall adds, at what cost, and the recommendation

### 6.1 Why it is genuinely needed

Three independent facts, all now established:

1. `⊡` alone cannot define the Deterministic class: F° and F¹ (§5) agree on every `StarFormula`.
2. `app:drift`'s worked refutation shows F° **does** refute `sent:det` — the store/recall sentence
   separates exactly where the operator-only language cannot. With `|p| = [3/2, ∞)`, `τ(t) = t`,
   `σ(t) = 2t`, both disjuncts of `sent:det` fail at `⟨M, σ, 0⟩`.
3. `Det-pm` and `Det-m` each **define** the Deterministic frames exactly (task 105 report 02,
   Theorem C — proved, report-level, not yet in the manuscript).

**Theorem C, in full**, since the plan for the follow-up task will need it:

> Each of `Det-pm` and `Det-m` **defines** the Deterministic frames: valid over `F` iff `F` is
> Deterministic.

- **`Det-pm`** is `sent:det` with `F` replaced by `always`, so `app:deterministic-future`'s
  unfolding chain `(∗)` transfers verbatim with "for all `y > x`" replaced by "for all `y ∈ D`"
  (temporal operators do not disturb `v⃗`). Unfolding `⊡`: `Det-pm` is true at `τ, x` iff for every
  `y ∈ D`, every `σ ∈ ⟨τ⟩_x` agrees with `τ` on `p` at `y`.
  **(⇐)** If `F` is Deterministic then `⟨τ⟩_x = {τ}` by the bridge lemma and one disjunct holds
  trivially at every `y`. **(⇒)** Suppose `⊨_F Det-pm`. Fix `τ`, `x`, `σ ∈ ⟨τ⟩_x`, `y ∈ D`; take
  the model with `|p| = {τ(y)}`. The `¬p` disjunct fails, witnessed by `τ` itself, so the `p`
  disjunct holds and `σ(y) ∈ {τ(y)}`, i.e. `σ(y) = τ(y)`. As `y` was arbitrary, `σ = τ`, so
  `⟨τ⟩_x = {τ}`; the bridge lemma yields Deterministic.
- **`Det-m`**: `↑¹_M` pins `μ₁ := τ` **before** `⊡` moves the world of evaluation to an arbitrary
  `σ ∈ ⟨τ⟩_x`; `always` then ranges over all `y ∈ D`, and `↓¹_M` evaluates `p` back at `(τ, y)`
  holding the time fixed. So `Det-m` is true at `τ, x` iff `σ(y) ∈ |p| ⟺ τ(y) ∈ |p|` for all
  `σ ∈ ⟨τ⟩_x` and all `y`. Both directions as above, same singleton valuation.

**Do not use a uniform-substitution argument anywhere in this development — it is unsound here.**
Theorem C's (⇒) direction needs only *one* sentence letter, with the single valuation
`|p| = {τ(y)}`; (⇐) is proved for arbitrary `φ`. That is deliberate, not an economy. Uniform
substitution **fails** in this setting: `p → ⊡p` is frame-valid over F° while `Fp → ⊡Fp` is
refutable over the two-world `F′`. This is the same phenomenon as `app:deterministic`'s refuting
instance being `Fp` rather than an atom, and as task 535's observation that `AS` behaves like
Reynolds 2003's atomic-non-futurity *rule* rather than a schema.

**The mechanism that makes store/recall work, in one sentence**: the `(⊡)` clause of
`def:BLstar-semantics` passes the stored-time vector through **unchanged** when it swaps `τ` for
`σ`. **The stored time being world-independent is the entire reason `Det` separates the frames
where `Determined` cannot.** `↓²` inside `⊡` recalls time `y` in a *different* world — which is
exactly the comparison `⊡` alone cannot express.

So the full correspondence result is unobtainable in the `⊡`-only L⋆ of task 533, and this is not a
gap in the Lean development but a fact about the language.

### 6.2 The Lean cost, concretely

The evaluation point becomes `(τ, x, v⃗, μ⃗)` with `v⃗ : ℕ → F.Duration` and `μ⃗ : ℕ → F.HF`.
Every existing transport lemma in the tree is `(τ, x)`-only and would need the vectors threaded:

| Lemma | File | Breakage |
|---|---|---|
| `truth_congr_ext` | `Semantics/StarTruth.lean` | **breaks structurally** under `↓_M`: pointwise-equal histories no longer suffice, because `μᵢ` can point at a *third* history |
| `starTruthAt_timeShift` | `Semantics/StarTruth.lean` | **breaks** under `↓_T`: a shift must act on `v⃗` too; the invariance statement must be re-stated as `shift` acting on the whole point |
| `stab_state_only` | `Semantics/StarTruth.lean` | fails outright — `⊡φ` no longer depends on the world state alone once `↓_M`/`↓_T` are inside its scope |
| `TruthCorr` / `TruthAntiIso` | `Semantics/` | `Formula`-only; the TD/swap soundness route in task 533 relies on these |
| Atomization | `Metalogic/Conservativity/Star/Atomization.lean` | its licensing fact **is** `stab_state_only`; the whole conservativity route is invalidated inside store/recall scopes |
| Pasting (`PS`/`US`) | `Semantics/StarPasting.lean` | `SameStateAt`-based; re-derivation needed |

That is not a mechanical port; it is a re-founding of the transport layer.

### 6.3 Recommendation — a **narrow** follow-up task, not the full apparatus

**Do not extend L⋆ by the full BL⋆ store/recall apparatus.** Two graded options; recommend Option 1.

- **Option 1 (recommended): world store/recall only, with a SINGLE register.** Evaluation point
  becomes `(τ, x, μ)` with `μ : F.HF`. This suffices for
  `Det-m = ↑¹_M ⊡ always(φ ↔ ↓¹_M φ)`, which per task 105 defines the Deterministic frames exactly.
  Advantages, all structural: no stored-*time* vector, so **time-shift invariance survives** with
  `μ` carried untouched; `↓_M` is a history *swap* rather than a time jump, so the `untl`/`snce`
  clauses are unchanged; a single register avoids `ℕ`-indexed vector update lemmas entirely.
  `truth_congr_ext` must still be restated (as agreement of *both* `τ` and `μ`), but that is one
  lemma, not a layer. **Estimate: one task, ~600–900 lines.**

- **Option 2 (not recommended now): the full `↑_T/↓_T/↑_M/↓_M` with `ℕ`-indexed vectors**, needed
  for `Det` and `Det-pm`. Buys the `app:deterministic-future` result and the paper's BL⋆ proper,
  at several times the cost, and invalidates the atomization route that task 533's conservativity
  rests on. **Estimate: 2500+ lines across multiple tasks.** Revisit only if BL⋆ metatheory becomes
  a goal in its own right.

### 6.4 The choice asymmetry — a finding in its own right

**Named finding: the choice dependence tracks a DIRECTION, not a deliverable.** This is presented
as this report's own analysis; the paper's footnote to `lem:deterministic-singleton` records the
asymmetry at the *lemma* level and nobody has propagated it to the *results*.

The rule: **any step of the form "validity of a sentence ⟹ frame condition" needs Zorn**, because
that direction must *manufacture* separating worlds and `thm:extension` is the only tool for it.
The opposite direction, "frame condition ⟹ validity", is safe. This is not special to store/recall
— task 105 report 02's Theorem B (*Forward-Separated iff `⇒_x` is a partial function for every
`x > 0`*) has the same shape, so its (⇒) direction is ZFC too.

Applied, **with the directions and scopes that make each line true**:

| Result | Which half of the bridge it uses | Choice |
|---|---|---|
| `app:deterministic` positive half — the plain collapse | (⇒) only | **choice-free** |
| `app:deterministic-future` positive half | (⇒) only | **choice-free** |
| `cor:no-characterization` — `S_{⊡φ} = S_φ` over F¹ needs `⟨τ⟩_x = {τ}` for a frame *known* to be Deterministic | (⇒) only | **choice-free** |
| `lem:deterministic-singleton` (⇐) | — | ZFC (`thm:extension`, Zorn) |
| Theorem C (`Det-pm`/`Det-m`), ⇐ direction | (⇒) only | choice-free |
| Theorem C, ⇒ direction — derives Deterministic *from* `⟨τ⟩_x = {τ}` | (⇐) | **ZFC** |

So the whole of deliverables (a) and (b) **as scoped** is constructive, and the choice dependence
appears at exactly one place: the direction of Theorem C that *concludes* a frame is Deterministic.
In Lean that is `Extension.extension` (Zorn-based) via `PartialHistory.hF_nonempty`.

**Two scoping conditions, without which the finding is false.** State the direction, not just the
conclusion:

- **(a) is choice-free *because of the direction it states*** — `Deterministic F → ⊨_F ⊡φ ↔ φ` is
  frame-condition ⟹ validity. If anyone later restates (a) as a *biconditional* correspondence, the
  converse half becomes ZFC. The Lean statement must stay an implication.
- **(b) is choice-free *because `cor:no-characterization` characterizes both world-sets
  explicitly*** — `H_{F°}` is *exactly* the functions with `y−x ≤ τ(y)−τ(x) ≤ 2(y−x)`, `H_{F¹}` is
  *exactly* the translations, and "every world state occurs at every time" has the explicit witness
  `δ(t) := t + w − x`. Nothing appeals to `thm:extension` or `cor:occurrence`. **But** scoping (b)
  up to task 105 report 02's Theorem D (letter-free non-definability *for arbitrary `F`*) would
  reintroduce choice, because Theorem D appeals to `cor:occurrence` for nonemptiness of `H_F` in
  the `□φ` case. Over F°/F¹ that appeal is removable (the translations are explicit witnesses); at
  full generality it is not. **Do not generalize (b) to arbitrary frames without re-auditing this.**

**`(a)` and `(b)` are cheap and constructive; `(c)` is expensive and, in one direction,
choice-dependent.** Record this in the follow-up task's description so it is not discovered late.

This is a cost signal, not a blocker: `Classical.choice` is ordinary mathematics in this tree
(see `ShiftSet.lean`'s note on `reverse_repr`). But it does mean deliverables (a) and (b) can carry
an `#print axioms` regression pin showing no `Classical.choice`, and (c) cannot.

---

## 7. Coordination with PossibleWorlds task 105, and the `d`-deliverable scoping decision

### 7.1 Scoping decision (settle this in the plan; stated here so it is inherited)

**This task must NOT write to `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`.**

Deliverable (d) says to "record the exact statements in the paper's terms so that
`possible_worlds.tex` and the Lean tree agree, coordinating wording with task 105 rather than
duplicating its mathematics." Read that as: record the wording **in this task's own artifacts under
`specs/536_*/`**, for task 105 to integrate. Reasons:

1. Task 105 owns the manuscript and is `[IMPLEMENTING]`, stalled at Phase 3 of 8.
2. A live `nvim` session there previously saved `possible_worlds.tex` from a **stale buffer** ~30s
   after an agent's edit built green, erasing it; a `vimtex latexmk -pvc` was also running.
   Concurrent writes to that file are actively unsafe.

§2 of this report is the deliverable-(d) wording package. It is deliberately generous in quoting
`app:drift` verbatim, because that text has been deleted from the working tree and this report may
be among the more accessible surviving copies (the authoritative copy is
`specs/105_characterize_deterministic_task_frames/reports/recovered-drift-noncharacterization.tex`).

### 7.1bis Scope CUT: do not draft manuscript prose for `Det-pm` or `Det-m`

Task 105's phase-collision analysis returns **direct collisions**:

| Object | Task 105 phase | State | Collision |
|---|---|---|---|
| `lem:deterministic-singleton` | Phase 2 (also cited by Phase 5) | **DONE and committed** | already a biconditional in the manuscript with the ZFC footnote and full converse proof — **formalize against that committed text; do not redraft it** |
| `Det-pm` | Phase 3 (the display) + Phase 5 (the theorem, `app:deterministic-characterization`) | Phase 3 `[PARTIAL]` and erased; Phase 5 `[NOT STARTED]` | 105 holds **literal ready-to-apply LaTeX** for the Phase 3 display and connecting prose in its handoff, plus a Phase 5 task list — drafting here produces a competing second version of text that is already written and staged |
| `Det-m` (`rmk:det-m`) | Phase 5 | `[NOT STARTED]`, flagged first for trimming | same |

**So deliverable (d) is scoped to: recording the exact statements in the paper's *current* terms as
they bear on the Lean tree, and noting where the Lean formalization and the manuscript must agree.
It must NOT produce manuscript prose for `Det-pm`/`Det-m`.** §2 of this report is that
correspondence record and stops at that line: it quotes the committed and recovered text needed to
pin the Lean statements, and gives Theorem C (§6.1) as *input to the Lean follow-up task*, not as
manuscript copy.

Combined with §7.1's no-write rule, this task's relationship to the manuscript is **read and
record only**.

### 7.2 Division of labour

| Result | Owner | Status |
|---|---|---|
| `lem:deterministic-singleton` (biconditional, ZFC) | task 105 (paper) | **landed**, `possible_worlds.tex` |
| `app:deterministic` both halves, `F′` | task 105 (paper) | **landed**, merged; `app:non-deterministic` retired |
| `app:drift` / F° non-characterization | task 105 (paper) | **cut to a footnote**; recovered text preserved |
| `F^N`, forward-vs-backward determinism | task 105 report 02 | report-level; **not yet in the manuscript** |
| `Det-pm`, `Det-m` correspondence (Theorem C) | task 105 report 02 | **proved on paper**, report-level; **not yet in the manuscript** |
| Lean (T2) collapse | **this task** | **done** (§4) |
| Lean (T3)/(T4) F°, F¹, `S_φ` | **this task** | frames done, `S_φ` remains (§5) |
| Lean (T6) store/recall correspondence | follow-up task | recommended, Option 1 (§6.3) |

**Citation discipline for `Det-pm`/`Det-m` and `F^N`.** These are *proved*, not open — task 105's
status table rates Theorem C "Proved, given 1". But a grep for `det-pm|det-forward|
deterministic-characterization` in `possible_worlds.tex` returns nothing today, and the `% TODO`
placeholder is still in place. So cite them as **report-level results pending paper integration**,
never as established manuscript text, and never as conjectures.

---

## 8. Risks and open items

| # | Item | Severity | Mitigation / status |
|---|---|---|---|
| R1 | F° is not a task frame | **RETIRED** | all six axioms machine-checked (§5.1) |
| R2 | F°'s `limit` fails in a dense order (as `F′`'s does) | **RETIRED** | `fzero_limit` compiles; fibres are bounded, not all of `W` |
| R3 | F°'s `saturation` needs frame-theoretic machinery | **RETIRED** | Cantor + `isCompact_Icc`; ~15 lines |
| R4 | `S_φ` `untl`/`snce` cases need surjectivity | **LOW** | `fzero_hits_future`/`_past` machine-checked |
| R5 | `realOrder` placement | **OPEN — plan decides** | `realOrder` exists only downstream, at `Metalogic/DedekindNonCompactness.lean:318`, as `@[reducible] noncomputable def realOrder : TemporalOrder := ⟨ℝ⟩`. Both annotations are load-bearing per that file's own docstring. Do **not** silently duplicate it into `Semantics/`: that would pull `Mathlib.Data.Real.Basic` and the ℝ topology into the most upstream layer of the tree. **Recommendation**: place the F°/F¹ development downstream, in a new `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` — `Independence/` already hosts `ClockFrame.lean`, the separating-frame neighbourhood — and reuse the existing `realOrder`. Verify acyclicity at plan time. |
| R6 | New topology imports in the library | **LOW** | the probe needs `Mathlib.Topology.Order.Compact` (for `isCompact_Icc`) and the IVT. **Not a novelty**: `Metalogic/Bundle/LimitMCS.lean` and `Metalogic/BXCanonical/Chronicle/ChronicleToCountermodelBasic.lean` already import `Mathlib.Topology.*`; the "no topology" remark at `Semantics/TaskFrame.lean:897` concerns the *cone* topology only. A topology-free `csSup` route to saturation also exists (§5.1). Placing the module under `Metalogic/Independence/` (R5) contains the blast radius regardless. |
| R7 | `StarFormula` might already carry store/recall | **RETIRED** | it does not: constructors are `atom / bot / imp / box / untl / snce / stab` (`Semantics/StarTruth.lean:110-123`). `app:drift`'s "BL⁺ extended with `⊡`" is exactly task 533's `StarFormula`. |
| R8 | Duplicating task 105's mathematics | **MANAGED** | §7.2 division of labour; §7.1 no-write rule |
| R9 | Stale line numbers / retired labels | **MANAGED** | cite `\label`s only — line numbers have been stale in three independent extractions. Rename list: `Spherical` → `Saturation`; `cor:spherical-finite` → `cor:saturation-finite`; `app:non-deterministic` **retired** (merged into `app:deterministic`); `def:frame-properties` now holds only Discrete/Dense/Complete, so the Deterministic condition is `def:deterministic`; `def:BLstar-semantics` **added** (carries Stability / `\timeStore` / `\timeRecall`); **`def:BLplus-semantics` no longer exists** — the recovered `app:drift` proof cites it, and a verbatim restoration would introduce a dangling reference (plausible repoints: `def:BL-semantics` or `def:BLstar-semantics`) |
| R11 | `F^N` saturation needs a **finite-fibres** helper that may not be in the tree | **OPEN — plan checks** | `cor:saturation-finite` requires finite `W`; `F^N` has `W = ℕ`. Only relevant if `F^N` is formalized, which is optional for this task (§5bis) |
| R10 | Task 105 phases 4–8 collide with (b)/(c) | **OPEN** | not yet determined; task 105 is stalled at Phase 3. Plan should check before dispatching (c). |

---

## 9. Recommended phase decomposition for the plan

| Phase | Content | Size | Risk |
|---|---|---|---|
| 1 | `TaskFrame.IsDeterministic` into `Semantics/FrameProperty.lean`; the bridge + collapse from `probes/01` into the `⊡` validity layer; docstring the choice-freeness and the unrestricted-`x` requirement | ~120 lines | none — transcription of compiled probes |
| 2 | Promote task 535's `refute_determined` (over `natFrame`, ℤ) as `app:deterministic`'s negative half; docstring the discreteness hypothesis and its `[SuccOrder D] [NoMaxOrder D]` encoding | ~60 lines | none |
| 3 | F° as a `FrameOver realOrder` (from `probes/02`), with the `comp`-is-positive-cone-only note; `fzero_not_deterministic` | ~140 lines | low — settles R5/R6 placement |
| 4 | The order-isomorphism core (`fzero_bounds` … `fzero_hits_past`) lifted from bare functions to `WorldHistory` | ~90 lines | low |
| 5 | `satSet` + the generic (H1)+(H2) bridge theorem | ~250 lines | **the one real phase**; `untl`/`snce` cases |
| 6 | F¹ (or a `ShiftSet` instantiation); discharge (H1)/(H2) for both; conclude `⊨_{F°} φ → ⊡φ`, non-characterization, and non-L⋆-definability | ~120 lines | low |
| 7 | README / `Metalogic.lean` docstring rows; §2 cross-referenced for task 105 (**record only — no manuscript prose, §7.1bis**) | ~40 lines | none |
| 8 *(optional)* | `F^N` and the forward-vs-bidirectional separation (§5bis) — only if the forward/backward distinction is wanted in Lean. Blocked on a **finite-fibres** saturation helper that may not exist (R11) | ~150 lines | medium — gap check first |

Deliverable (c) is **not** a phase of this task: it is the recommended follow-up (§6.3, Option 1),
to be `/spawn`ed with the choice-asymmetry note (§6.4) in its description.

---

## 10. Evidence table

| Claim | Source | Method | Confidence |
|---|---|---|---|
| `Deterministic F → ⊨_F ⊡φ ↔ φ`, choice-free | `probes/01`, all 4 theorems | compiled | **High** |
| F° is a `FrameOver`, six axioms | `probes/02`, `fzeroFrame` | compiled | **High** |
| F° non-deterministic | `probes/02`, `fzero_not_deterministic` | compiled | **High** |
| F° histories are order-isos of `(ℝ,<)` | `probes/02`, `fzero_strictMono` + `_hits_future` + `_hits_past` | compiled | **High** |
| F¹ is a `FrameOver` and Deterministic | `probes/02`, `foneFrame`, `fone_deterministic` | compiled | **High** |
| `⊨_{F°} φ → ⊡φ` | `app:drift` (recovered) | paper proof read; `S_φ` not yet in Lean | **High** (paper) / **not machine-checked** |
| Deterministic not L⋆-definable | `S_φ` applied to F° and F¹ | derivation, §5.4 | **Medium-High** — follows once `S_φ` lands |
| `Det-pm`/`Det-m` define the Deterministic frames | task 105 report 02, Theorem C | report-level proof, ZFC via bridge (⇐) | **Medium-High** (not in manuscript) |
| `refute_determined` = `app:deterministic` negative half | `specs/535_*/probes/01_stab-axiom-probes.lean:439` | compiled (task 535) | **High** |
| `Extension.extension` takes a `PartialHistory` (no convexity) | `Semantics/Extension/Extension.lean:208` | file read | **High** |
| `Compositional` is positive-cone-only | `Semantics/TaskFrame.lean:474` | file read | **High** |
| `natFrame` carries `[SuccOrder D] [NoMaxOrder D]` | `Semantics/TaskFrame.lean:1602` | file read | **High** |
| `realOrder` exists only downstream | `Metalogic/DedekindNonCompactness.lean:318` | reported + consistent with `Semantics/` grep | **Medium-High** |
| `cor:no-characterization` is the deliverable-(b) statement, and uses F¹ | recovered `692dd4b7`; live footnote names both frames | verbatim quotes, two sources | **High** |
| `S_φ` recursion mentions only `(W,<)`, not the task relation | `cor:no-characterization` proof, verbatim | paper read | **High** |
| (a) and (b) are choice-free; only Theorem C's (⇒) is ZFC | this report's §6.4 analysis, from report 02's status table + the paper's lemma footnote | derivation, independently confirmed | **High** |
| Uniform substitution is unsound here (`p → ⊡p` valid on F°, `Fp → ⊡Fp` refutable) | `app:deterministic` countermodel + `app:drift` | paper read; the F° half follows from `S_{⊡φ} = S_φ` | **High** |
| `F^N` separates forward from bidirectional determinism | task 105 report 02; frame-check script | reported, machine-verified in PossibleWorlds repo | **Medium-High** |
| No **finite** frame separates forward from bidirectional determinism | Seriality ⇒ surjective ⇒ injective on finite `W` | derivation | **High** |
| Task 105 holds staged LaTeX for `Det-pm`; do not redraft | task 105 phase-collision analysis | reported | **Medium-High** |
