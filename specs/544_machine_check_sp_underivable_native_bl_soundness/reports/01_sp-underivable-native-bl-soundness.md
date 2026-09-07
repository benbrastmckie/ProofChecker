# Research Report: Task #544

**Task**: 544 - Machine-check the failing half of CEB: `(Sp)` is not a theorem of TM, via a native BL frame notion and native BL soundness
**Started**: 2026-09-07
**Completed**: 2026-09-07
**Effort**: ~4-6 hours implementation (4 phases, ~700 lines of new Lean across 2 modules plus docstring edits)
**Dependencies**: None (all prerequisites are in-tree and built)
**Sources/Inputs**: - Codebase (`FormalSystem/Metalogic/Conservativity/**`, `FormalSystem/Semantics/**`, `FormalSystem/BaseLanguage/**`), lean-lsp/`lake env lean` verification, Mathlib `Mathlib/Data/Sum/Order.lean`
**Artifacts**: - `specs/544_machine_check_sp_underivable_native_bl_soundness/reports/01_sp-underivable-native-bl-soundness.md`
  - `specs/544_machine_check_sp_underivable_native_bl_soundness/prototype/SpCountermodelPrototype.lean` (a **fully compiling, sorry-free** end-to-end prototype of every deliverable)
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The whole task is already demonstrated to be achievable, end to end, with no `sorry` and
  no new axiom.** A 340-line prototype covering all five scope items compiles against the
  current tree (`lake env lean`, Lean v4.33.0-rc1) and reports
  `[propext, Classical.choice, Quot.sound]` for `not_derivable_sp`,
  `tmCompleteBase_refuted` and the native soundness theorem. The prototype is saved as
  `specs/544_machine_check_sp_underivable_native_bl_soundness/prototype/SpCountermodelPrototype.lean`.
- **The countermodel is much cheaper than expected.** It is not the lexicographic sum `ℤ + ℚ`
  and it needs no bespoke carrier module: it is Mathlib's *disjoint sum order* `ℤ ⊕ ℝ`
  (`Mathlib/Data/Sum/Order.lean`'s `Sum.instPartialOrder`, where `inl` and `inr` points are
  mutually incomparable), with `□` read as the **universal modality over the whole point set**.
  One atom, one valuation, and two evaluation points (`inr 0` on the ℝ-fibre, `inl 0` on the
  ℤ-fibre) suffice.
- **The native frame notion is small**: a bare structure `⟨Point, lt⟩` with six order
  conditions (transitivity, irreflexivity, forward/backward seriality, forward/backward
  trichotomy on cones). No task relation, no world states, no `Duration` group — this is
  precisely what escapes the `TaskFrame` binding.
- **TD is better handled by a swap-*transfer* lemma than by the swap-strengthened induction the
  task description prescribes.** Because the frame class is closed under order reversal,
  `BLFrameTruth F.swap V w φ ↔ BLFrameTruth F V w φ.swapBL` (a 6-case induction on `BLFormula`,
  all cases one line) discharges the `temporal_duality` case of soundness in one line, and the
  simultaneous "validity ∧ swap-validity" recursion of
  `bl_derivable_valid_and_swap_valid_zTimeSucc` is not needed.
- **Three corrections to the task description are required before planning** (details in
  Findings): the mirrored corollary is `tmCompleteZTime_refuted`, not
  `tmCompleteDiscrete_refuted`; the axiom list "MK, MT, M5, MF, TD, TK, T4, TB, TA, TL" is
  stale and mis-typed (TD is a *rule*; TB/TA are the pre-rename names of TS/TC; the four
  propositional axioms are omitted); and **"no instance of `(Sp)` is a theorem of TM" is false
  as literally stated** — `Sp ⊤ ψ` is true on the countermodel, so the deliverable must be the
  *schema*-level claim witnessed by the atomic instance.

## Context & Scope

Researched: what it takes to machine-check the failing half of CEB — that the boxed dichotomy
`(Sp) := □(DF φ) ∨ □(DN ψ)` is not derivable in TM (`BaseLanguage.DerivationTree
FrameClass.Base`) — given that `Metalogic/Conservativity/SpWitness.lean` already has
`blValid_sp` (BL-validity on every task frame) and `sp_translate` (the TM⁺ half), and given
`Metalogic/Conservativity.lean`'s standing verdict that this half is "not machine-checkable in
this tree, and not close".

Constraints honoured throughout:

- **Zero-debt.** No approach below needs a `sorry`; the prototype proves it by compiling.
- **The forward-conservativity prohibition** (`Metalogic/Conservativity.lean`): nothing here
  states `forward`, `TMCompleteBase` or `ForwardBase` as the conclusion of a theorem. The new
  corollary is the *negation* `¬ TMCompleteBase`, which is exactly the shape
  `Z1Countermodel.tmCompleteZTime_refuted` already has and is not covered by the prohibition.
- **No new axiom.** The countermodel is built from Mathlib order instances only.

Out of scope, unchanged: whether TM_d / TM_dc are complete over the dense and
dense-and-complete classes.

## Findings

### Codebase Patterns

**What already exists and is reused unchanged.**

| Asset | Location | Role here |
|---|---|---|
| `Sp`, `blValid_sp` | `Metalogic/Conservativity/SpWitness.lean` | the witness formula and its BL-validity half |
| `TMCompleteBase`, `TMComplete` | `Metalogic/Conservativity/TMCompletenessReduction.lean` | the unasserted `Prop` whose negation is deliverable 5 |
| `tmCompleteZTime_refuted` | `Metalogic/Conservativity/Z1Countermodel.lean` | the structural model to mirror |
| `BaseLanguage.Axiom` (15 ctors), `Axiom.minFrameClass` | `BaseLanguage/Axioms.lean` | the schemata to verify natively |
| `BaseLanguage.DerivationTree` (7 rules), `.height`, `.ofWeakeningNil`, `height_ofWeakeningNil_lt` | `BaseLanguage/Derivation.lean` | the induction target and its termination scaffolding |
| `BLFormula.swapBL`, `swapBL_involution` | `BaseLanguage/Formula.lean` | TD |
| `bl_derivable_valid_and_swap_valid_zTimeSucc` | `Metalogic/Conservativity/BaseLanguageSoundness.lean` | the `match … termination_by d.height` recursion shape to copy |
| `Sum.instPartialOrder`, `inl_lt_inl_iff`, `not_inl_lt_inr`, … | Mathlib `Data/Sum/Order.lean` | the countermodel carrier |

**Why `BLTruthAt` cannot be reused.** `Semantics/BLTruth.lean`'s `BLTruthAt` is indexed by
`TaskFrame`, whose `Duration` field is a `TemporalOrder` = *nontrivial totally ordered abelian
group*. That is exactly the hypothesis `Semantics/DurationClassification.lean`'s
`duration_dense_or_least_pos` consumes to make `blValid_sp` go through. A native truth
definition on a bare order is therefore mandatory, and it must be a **new** recursion, not a
reindexing of `BLTruthAt`.

**The sharpened impossibility argument (new, and worth a docstring).** `SpWitness.lean` records
that a CEB countermodel needs "different histories seeing differently-shaped time" but derives
it from the group dichotomy. There is a stronger, purely order-theoretic reason, and it should
be recorded because it tells the implementer exactly which degrees of freedom the frame notion
must have:

- A `DF φ` instance can fail at a point `t` **only if `t` has no immediate successor**. (If
  `Hφ ∧ φ` holds at `t`, then any `t' > t` with `(t, t') = ∅` satisfies `Hφ`, so `F(Hφ)` holds.)
- A `DN ψ` instance can fail at `t` **only if `t` does have an immediate successor**. (A
  `¬ψ`-witness `s > t` with some `r ∈ (t, s)` would be reachable as `r`-then-`s`, contradicting
  `GGψ`.)

So on **any single linear order**, at any single time `t`, the two failures are mutually
exclusive — regardless of valuation, regardless of how many histories the structure carries, and
regardless of whether the order is a group. Refuting `□(DF φ) ∨ □(DN ψ)` therefore requires the
`□`-accessible points to include points from **two order-shapes at once**, which is precisely
what a `TaskFrame`'s single shared `Duration` forbids and what a two-fibre point set supplies.

**`□` must be the universal modality (or something very close).** MF (`□φ → □Gφ`) is what pins
this down. In a two-sorted Kripke frame `⟨P, R, <⟩` MF is sound as soon as `R`-classes are
closed under `<`; taking `R` universal is the cheapest such choice and is also what
`Metalogic/Conservativity.lean` itself describes ("a ℤ-fibre and an ℝ-fibre with `□` read
globally over both"). Note the contrast worth recording in the new module's docstring: in the
*task-frame* semantics MF is **not** underwritten by that condition (there `□` fixes the time
coordinate) but by shift-closure of `H_F` together with `Duration` being a group. The native
semantics reaches the same axiom by a different route — that is a feature, not a mismatch,
because underivability only needs *some* class on which TM is sound.

### External Resources

- Mathlib `Mathlib/Data/Sum/Order.lean` supplies the entire countermodel carrier: `LE`/`LT` on
  `α ⊕ β` via `Sum.LiftRel` (cross-fibre pairs are incomparable), `Preorder`/`PartialOrder`
  instances, and the `@[simp]` lemmas `inl_lt_inl_iff`, `inr_lt_inr_iff`, `not_inl_lt_inr`,
  `not_inr_lt_inl`. No new carrier module (nothing like `Semantics/LexCarrier.lean`) is needed.
- Mathlib's `lt_trichotomy` closes both trichotomy fields after the cross-fibre cases die by
  `simp_all`.
- No LeanSearch/Loogle/Leanfinder query was required: every lemma needed was found by
  `grep`/`Read` against Mathlib's source and the local tree, and every candidate was verified by
  actually compiling it rather than by name-matching.

### Recommendations

**A sorry-free path exists and has been executed end to end.** The recommended implementation is
the prototype, promoted into two modules with docstrings.

**Module 1 — `FormalSystem/Semantics/BLFrame.lean`** (native frame + native truth; imports
`FormalSystem.BaseLanguage.Formula` and Mathlib order only; carries the same
`assert_not_exists FormalSystem.ProofSystem.*` G-15 guard `Semantics/BLTruth.lean` carries):

```lean
structure BLFrame where
  Point : Type
  [pointNonempty : Nonempty Point]
  lt : Point → Point → Prop
  lt_trans  : ∀ {a b c}, lt a b → lt b c → lt a c
  lt_irrefl : ∀ a, ¬ lt a a
  no_max    : ∀ a, ∃ b, lt a b
  no_min    : ∀ a, ∃ b, lt b a
  fut_lin   : ∀ {a b c}, lt a b → lt a c → lt b c ∨ b = c ∨ lt c b
  past_lin  : ∀ {a b c}, lt b a → lt c a → lt b c ∨ b = c ∨ lt c b

def BLFrame.swap (F : BLFrame) : BLFrame := …   -- reverses `lt`; the class is closed under it

def BLFrameTruth (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) : BLFormula → Prop
  | .atom p      => V w p
  | .bot         => False
  | .imp φ ψ     => BLFrameTruth F V w φ → BLFrameTruth F V w ψ
  | .box φ       => ∀ v : F.Point, BLFrameTruth F V v φ
  | .allPast φ   => ∀ v, F.lt v w → BLFrameTruth F V v φ
  | .allFuture φ => ∀ v, F.lt w v → BLFrameTruth F V v φ

def BLFrameValid (φ : BLFormula) : Prop := ∀ F V w, BLFrameTruth F V w φ
```

plus the `BLFrameTruth.*` characterization lemmas (`imp_iff`, `box_iff`, `past_iff`,
`future_iff`, `neg_iff`, `top_true`, `and_iff`, `or_iff`, `diamond_iff`, `someFuture_iff`,
`somePast_iff` — mirroring the `BLTruth.*` namespace one for one), and the swap transfer:

```lean
theorem truth_swap (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) (φ : BLFormula) :
    BLFrameTruth F.swap V w φ ↔ BLFrameTruth F V w φ.swapBL
```

Six cases, each one line (`Iff.rfl`, `imp_congr`, `forall_congr'`); `induction φ generalizing w`.

**Module 2 — `FormalSystem/Metalogic/Conservativity/SpCountermodel.lean`** (imports
`Conservativity/SpWitness.lean`, `Conservativity/TMCompletenessReduction.lean`,
`Semantics/BLFrame.lean`):

1. `axiom_valid {φ} (ax : BaseLanguage.Axiom φ) (h_fc : ax.minFrameClass ≤ FrameClass.Base) :
   BLFrameValid φ` — a single `cases ax` with 15 branches. Twelve are ≤ 3 lines; `temp_linearity`
   is the longest (a `fut_lin` trichotomy feeding the three disjuncts); `df`/`dn`/`co` are
   discharged by `absurd h_fc (by decide)` on the `FrameClass` order.
2. `blFrameValid_of_derivation {φ} (d : BaseLanguage.DerivationTree FrameClass.Base [] φ) :
   BLFrameValid φ` — the **native soundness theorem**, a `match d with` recursion with
   `termination_by d.height`, copying `bl_derivable_valid_and_swap_valid_zTimeSucc`'s shape
   including its `decreasing_by` block. `temporal_duality` is one line via `truth_swap` at
   `F.swap`.
3. `twoFibre : BLFrame` over `ℤ ⊕ ℝ`, `twoV` (`inl n ↦ n ≠ 1`, `inr r ↦ r ≤ 0`, atom-independent).
4. `df_fails`, `dn_fails`, `sp_false` — the evaluation; then
   `not_derivable_sp (a : Atom) : ¬ BaseLanguage.Derivable FrameClass.Base [] (Sp (.atom a) (.atom a))`
   and `tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase`.

**Suggested phase decomposition** (each phase is one agent run and ends `lake build`-green):

| Phase | Content | Approx. size |
|---|---|---|
| 1 | `Semantics/BLFrame.lean`: structure, `swap`, `BLFrameTruth`, characterization lemmas, `truth_swap`, `BLFrameValid`; wire into `Semantics.lean` + `Semantics/README.md` | ~230 lines |
| 2 | `SpCountermodel.lean`: `axiom_valid` + `blFrameValid_of_derivation` | ~200 lines |
| 3 | same module: `twoFibre`, `twoV`, `df_fails`, `dn_fails`, `sp_false`, `not_derivable_sp`, `tmCompleteBase_refuted` | ~180 lines |
| 4 | Docstring/record updates: `Metalogic/Conservativity.lean` (the CEB row and the "what a machine-checked refutation would need" list), `SpWitness.lean`'s "What this does **not** do" section, aggregator table row, README/inventory, `scripts/check-module-invariants.sh` baselines if C2/C14 counts move | ~doc-only |

**Statement shape for deliverable 5** — mirror `Z1Countermodel` exactly:

```lean
theorem tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase
```

Note `TMCompleteBase` is a `def`, and `h : TMCompleteBase` does **not** apply directly; the
prototype uses `unfold TMCompleteBase TMComplete at h` first. (`have h' : … := h` fails; see
Risks.)

## Decisions

1. **Countermodel carrier: `ℤ ⊕ ℝ` (Mathlib disjoint sum order), not `ℤ + ℚ` lexicographic.**
   The task description names "the lexicographic sum Z + Q" as a candidate. Rejected: a
   *lexicographic* sum is still a single linear order, and by the sharpened impossibility
   argument above no single linear order can refute `(Sp)` at a fixed time. The disjoint (not
   lexicographic) sum is what makes the two order-shapes simultaneously `□`-accessible. `ℝ` is
   used rather than `ℚ` only because `linarith` over `ℝ` is frictionless; `ℚ` would work
   identically.
2. **`□` is the universal modality over `Point`.** Cheapest sufficient condition for MF; also
   matches `Conservativity.lean`'s own description of the intended two-fibre structure. Recorded
   in Findings with the contrast against the task-frame route to MF.
3. **TD via `truth_swap` (frame reversal), not via swap-strengthened induction.** The task
   description prescribes the latter; the former is strictly simpler here because the frame
   class *is* closed under converse (which is why `no_min` and `past_lin` are fields rather than
   derived). Both were considered; only the transfer route was implemented, and it compiles. If
   a future variant of the frame class stops being converse-closed, fall back to the
   `bl_derivable_valid_and_swap_valid_zTimeSucc` pattern.
4. **Single atom, one valuation.** Both disjuncts are refuted with the *same* atom, so
   `not_derivable_sp` is stated at `Sp (.atom a) (.atom a)`. Two distinct atoms are not needed.
5. **`twoFibre` must be `@[reducible]`.** Without it, `rw [BLFrameTruth.and_iff]` fails with a
   transparency-level type mismatch between `ℤ ⊕ ℝ → Atom → Prop` and
   `twoFibre.Point → Atom → Prop`. Verified both ways.

## Risks & Mitigations

| Risk | Evidence | Mitigation |
|---|---|---|
| **The task description's "no instance of `(Sp)` is a theorem of TM" is not provable — it is false.** `DF ⊤` is true at every point of every `BLFrame` (`F(H⊤)` follows from `no_max`), so `□(DF ⊤)` is true and the countermodel does not refute `Sp ⊤ ψ`. (`DF ⊤` also looks TM-derivable from TS + temporal necessitation + TK, though that was not machine-checked.) | prototype: `sp_false` is stated at the atomic instance and its proof visibly depends on the valuation | State the deliverable at the schema level, witnessed by the atomic instance, and record the `⊤` observation in the module docstring so nobody re-attempts the universally quantified form. This is a **factual correction to the task description**, not a scope reduction: refuting `TMCompleteBase` needs exactly one non-derivable BL-valid formula. |
| **Stale names in the task description.** `tmCompleteDiscrete_refuted` does not exist (it is `tmCompleteZTime_refuted`, renamed in the `FrameClass` `.Discrete`/`.Dedekind` → `.ZTime`/`.RTime` round). | `grep` over `Z1Countermodel.lean` | Use `tmCompleteZTime_refuted` in plan and docstrings. |
| **Stale/mis-typed axiom list.** The description lists "MK, MT, M5, MF, TD, TK, T4, TB, TA, TL". `TD` is a *rule* (`DerivationTree.temporal_duality`), not an axiom; `TB`/`TA` are the paper's pre-rename names for `TS`/`TC` (`Axiom.temp_serial`, `Axiom.temp_connect`); and the four propositional axioms (`prop_k`, `prop_s`, `ex_falso`, `peirce`) are omitted but must be verified. | `BaseLanguage/Axioms.lean` "Paper Name Correspondence" table | The real obligation is **13 `Axiom` constructors** whose `minFrameClass` is `.Base` (4 propositional + `modal_k`, `modal_t`, `modal_5`, `modal_future`, `temp_k`, `temp_4`, `temp_serial`, `temp_connect`, `temp_linearity`), plus `df`/`dn`/`co` excluded by the `≤ .Base` side condition, plus 7 derivation rules. All 13 + 7 are done in the prototype. |
| **`autoImplicit` is on**: an unimported name like `TMCompleteBase` silently becomes an auto-bound implicit `Prop` variable, producing a baffling "Type mismatch: `h` has type `TMCompleteBase`". Cost one debugging cycle in the prototype. | reproduced and fixed | The new module must `import FormalSystem.Metalogic.Conservativity.TMCompletenessReduction` explicitly (`SpWitness.lean` does **not** import it). Consider `set_option autoImplicit false` in the new modules. |
| Repo gates: C3 (zero `sorry`), C2/C14 (`#print axioms` baselines and *documented* axiom/sorry counts in docstrings/READMEs), C16 `docBlame` (every declaration needs a docstring), readme-lint (every `.lean` listed in its directory README). | `scripts/check-module-invariants.sh` header | Phase 4 is reserved for exactly this: docstrings on every new declaration including the private helpers, `Semantics/README.md` + `Semantics.lean` wiring, aggregator table row in `Metalogic/Conservativity.lean`, and a `bash scripts/check-module-invariants.sh` run. |
| Import-cycle discipline: children of `Metalogic/Conservativity.lean` must never import the aggregator. | aggregator docstring | New module imports `Conservativity/SpWitness.lean` + `Conservativity/TMCompletenessReduction.lean` directly, and is added to the aggregator's import list + module table, exactly as `Z1Countermodel.lean` is. |
| Long `lake build` after wiring the new modules into `Semantics.lean`. | full library ≈ hundreds of modules | Run the detached, guarded build (`context/project/lean4/operations/long-builds.md`); during development use `lake env lean <file>` on the single new file, which is what verified the prototype in seconds against the existing olean cache. |

## Tactic Survey Results

Tactics were exercised directly against the real goals in the compiling prototype rather than
probed with `lean_multi_attempt`; the table records what actually discharged each goal.

| Goal | Tactic | Result | Premises/Config |
|---|---|---|---|
| cross-fibre trichotomy `sum_tri` on `ℤ ⊕ ℝ` | `rintro … <;> simp_all <;> exact lt_trichotomy _ _` | success | Mathlib `Sum` order `@[simp]` set |
| `no_max` / `no_min` on `ℤ ⊕ ℝ` | `rintro (n \| x)` then `⟨Sum.inl (n+1), by simp⟩` | success | `Sum.inl_lt_inl_iff` |
| `BLFrameTruth.and_iff` / `or_iff` (derived Booleans) | `simp only [BLFormula.and, BLFormula.neg, BLFrameTruth]; tauto` | success | mirrors `BLTruth`'s own proofs |
| `diamond_iff` / `someFuture_iff` / `somePast_iff` | `constructor` + `by_contra` + `push Not` | success | `push_neg` is deprecated in this toolchain — use `push Not` |
| `truth_swap` (all 6 cases) | `induction φ generalizing w` + `Iff.rfl` / `imp_congr` / `forall_congr'` | success | none |
| `axiom_valid` propositional + modal cases | bare term-mode `intro … ; exact …` | success | `BLFrameTruth` reduces definitionally under `intro` |
| `axiom_valid` `peirce` | `by_contra` + `absurd` | success | classical |
| `axiom_valid` `temp_linearity` | `rcases F.fut_lin …` + explicit disjunct selection | success | `and_iff`, `someFuture_iff`, `or_iff` |
| `df`/`dn`/`co` exclusion | `absurd h_fc (show ¬ (… ≤ FrameClass.Base) by decide)` | success | `FrameClass` `DecidableRel` |
| soundness recursion termination | `termination_by d.height` + `decreasing_by all_goals first \| omega \| (simp only [DerivationTree.height]; omega)` | success | copied verbatim from `BaseLanguageSoundness.lean` |
| `ℝ`-fibre arithmetic (`r/2 ≤ 0` contradiction) | `linarith` | success | none |
| `ℤ`-fibre arithmetic (`0 < n < m → m ≠ 1`) | `omega` | success | none |
| `h : TMCompleteBase` applied as a function | `have h' : … := h` | **fail** | defeq not attempted at the ambient transparency |
| same, via unfolding | `unfold TMCompleteBase TMComplete at h` | success | requires the `TMCompletenessReduction` import |

## Context Extension Recommendations

- **Topic**: Native (non-`TaskFrame`) Kripke semantics for BL, and when a repository result
  requires leaving the primary semantic class.
- **Gap**: `context/project/lean4/` has no note on this repository's semantic layering — that
  `BLTruthAt` is `TaskFrame`-bound by construction, that the `assert_not_exists` G-15 guard
  governs what `Semantics/` may import, and that an underivability result may legitimately be
  stated against *any* class on which the proof system is sound, not only the intended one.
- **Recommendation**: after this task lands, add
  `context/project/lean4/patterns/native-semantics-for-underivability.md` recording the
  pattern (define a minimal frame class → prove soundness of the object system by recursion on
  the derivation tree → evaluate the target formula → conclude underivability), with this
  module and `Z1Countermodel.lean` as the two worked examples.
- **Topic**: `autoImplicit` traps.
- **Gap**: no context note warns that an unimported uppercase identifier becomes a silent
  auto-bound implicit, producing type errors that look like defeq failures.
- **Recommendation**: one paragraph in `context/project/lean4/` troubleshooting notes.

## Appendix

**Verification commands run** (from the repository root, against the existing `.lake` cache):

```
lake env lean specs/544_.../prototype/SpCountermodelPrototype.lean
```

Final output (no errors, no `sorry`, no warnings beyond none):

```
'Scratch544.not_derivable_sp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Scratch544.tmCompleteBase_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Scratch544.blFrameValid_of_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The countermodel, in one block.**

```
Points : ℤ ⊕ ℝ                (Mathlib disjoint-sum order: inl/inr incomparable)
lt     : (· < ·)
V w _  : (inl n ↦ n ≠ 1)  |  (inr r ↦ r ≤ 0)

at inr 0 (ℝ-fibre) : H p ∧ p ∧ F⊤ holds, F(H p) fails   ⟹  DF p false   ⟹  ¬□(DF p)
at inl 0 (ℤ-fibre) : GG p holds, G p fails (witness inl 1) ⟹  DN p false ⟹  ¬□(DN p)
hence Sp p p is false at every point, while blValid_sp says it is BL-valid on every task frame.
```

**Files read**: `Metalogic/Conservativity.lean`, `Metalogic/Conservativity/{SpWitness,
Z1Countermodel, BaseLanguageSoundness, TMCompletenessReduction}.lean`,
`Semantics/{BLTruth, BLValidity, TemporalOrder, TaskFrame}.lean`,
`BaseLanguage/{Formula, Axioms, Derivation}.lean`, `ProofSystem/Axioms.lean` (FrameClass),
`Mathlib/Data/Sum/Order.lean`, `scripts/check-module-invariants.sh`, `scripts/readme-lint.sh`.

**Searches used**: `grep`/`find` over `FormalSystem/` and `.lake/packages/mathlib/`; no
rate-limited Mathlib search tool was needed or called.
