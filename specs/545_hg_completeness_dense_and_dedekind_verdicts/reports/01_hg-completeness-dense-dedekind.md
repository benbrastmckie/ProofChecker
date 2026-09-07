# Research Report: H/G completeness verdicts at Dense and Dedekind

- **Task**: 545 - Decide whether TM_d (Dense) and TM_dc (Dedekind) are weakly complete
- **Started**: 2026-09-07T11:57:33-07:00
- **Completed**: 2026-09-07T12:35:00-07:00
- **Effort**: ~40 minutes wall clock; implementation estimate given in Recommendations
- **Dependencies**: None blocking. Independent of the CEB (Sp underivability) work at `.Base`.
- **Sources/Inputs**:
  - Repository (Lean): `FormalSystem/Semantics/{BLTruth,BLValidity,Truth,TaskFrame,FrameProperty,FrameClassValidity}.lean`
  - Repository (Lean): `FormalSystem/BaseLanguage/{Axioms,Derivation,Formula,Translation,AxiomDischarge}.lean`
  - Repository (Lean): `FormalSystem/Metalogic/Conservativity/{TMCompletenessReduction,Fragment,SpWitness,Z1Countermodel,BaseLanguageSoundness,Backward}.lean`
  - Repository (Lean): `FormalSystem/Metalogic/BXCanonical/{Completeness,CompletenessDedekind}.lean`, `Chronicle/`, `FormalSystem/Metalogic/Algebraic/FlowFrame.lean`
  - Repository (Lean): `FormalSystem/Metalogic/WeakCanonical/RealModel/{DoetsTheorem,ChronicleRealFlow}.lean`, `WeakCanonical/DenseModelSurgery/{NoGaps,Singletons,ChronicleInstance}.lean`
  - Prior artifact: `specs/archive/495_determine_tm_completeness_status_over_task_frames/reports/01_tm-completeness-status.md` (§5(i), §6.1)
  - Mathlib: `Mathlib/Order/CountableDenseLinearOrder.lean` (`Order.iso_of_countable_dense`)
  - Literature (named in the task brief, not in-repo): Bull 1968; Burgess, *Basic Tense Logic*; Goldblatt, *Logics of Time and Computation*; Reynolds 1992
  - Live Lean elaboration: two probe declarations compiled sorry-free via `lean_run_code` (Appendix A)
- **Artifacts**:
  - `specs/545_hg_completeness_dense_and_dedekind_verdicts/reports/01_hg-completeness-dense-dedekind.md`
- **Standards**: report-format.md, subagent-return.md, status-markers.md, artifact-management.md

## Executive Summary

- **Dense (TM_d) verdict: EXPECTED COMPLETE, no obstruction found.** The Base-row and
  Discrete-row obstructions both provably fail to transfer, and the semantic target class is now
  pinned exactly. What remains is a large but wholly standard formalization, not an open problem.
- **Dedekind (TM_dc) verdict: OPEN, with a precisely named obstruction.** The classical
  literature answer (Bull 1968) is positive, but the in-tree route that would deliver it needs
  D1/D2 Doets conditions discharged from **CO alone**, whereas every existing discharge consumes
  the BL⁺-only axioms `prior_U_gap` / `prior_S_gap` / `sep`, none of which has an H/G counterpart.
  That is the exact gap; it is a research gap, not a bookkeeping one.
- **New structural fact, machine-checked this dispatch:** in the BL task semantics `□` is the
  **universal modality** over the whole model — `□φ` at `(τ,t)` iff `φ` at *every* total history
  and *every* time. This collapses the "product S5 ⊗ Kt" reading to "temporal logic + universal
  modality", and it is what makes the Kripke-to-task-frame transfer sound. Verified declaration
  `bl_box_universal` (Appendix A.1), 11 lines, axioms `[propext]`.
- **The Base obstruction demonstrably does not survive to Dense**, machine-checked: `Sp φ ψ` —
  the `.Base` dichotomy witness of `Conservativity/SpWitness.lean` — is a *TM_d theorem*
  (Appendix A.2, `sp_derivable_dense`, axioms `[propext]`), because `□(DN ψ)` follows from the DN
  axiom by necessitation at `.Dense`. The Discrete obstruction does not survive either: `Z1` is
  refutable on `ℚ`, so it is not `BLValidIn .Dense`.
- **The product/translation transfer the brief asks for is already in-tree and generic.**
  `multiFamTaskFrameGen D FamIdx` (`Metalogic/Algebraic/FlowFrame.lean:146`) discharges all four
  frame axioms for an arbitrary `TemporalOrder D` and arbitrary inhabited `FamIdx`, and
  `multiFamGen_total_eq_range` (`:396`) proves its total histories are **exactly** the translates.
  Step (3) of the brief's Dense route is therefore essentially free.
- **The only genuinely missing content at Dense is a BL-side (H/G-only) canonical model.** Every
  other step is either in-tree or a short new lemma. Attempting to borrow the BL⁺ chronicle
  machinery instead is circular — that borrowing *is* forward conservativity.

## Context & Scope

The two rows under decision are, in repository terms, `TMComplete FrameClass.Dense` and
`TMComplete FrameClass.RTime` (`Conservativity/TMCompletenessReduction.lean:96`):

```
def TMComplete (fc : FrameClass) : Prop :=
  ∀ φ : BLFormula, BLValidIn fc φ → BaseLanguage.Derivable fc [] φ
```

Both are already known to be **equivalent to forward conservativity at the same tag**
(`tmCompleteDense_iff_forwardDense`, `tmCompleteRTime_iff_forwardRTime`, both landed and
sorry-free), because `WeakCompleteness` engines exist at both classes
(`Metalogic.completeness_dense` at `StrongCompleteness.lean:987`, `Metalogic.completeness_rtime`
at `:775`). Consequently:

- The *semantic* half is finished. `BLValidIn fc φ → TMFrag fc φ` is landed at all four classes
  (`Fragment.lean:105,115`). The whole residual content is `TMFrag fc φ → Derivable fc [] φ`,
  i.e. "the H/G fragment of TM⁺ collapses onto TM at `fc`".
- Frame-class gating is one side condition on one constructor: `h_fc : h.minFrameClass ≤ fc`
  in `BaseLanguage.DerivationTree.axiom`. TM_d is `fc := .Dense` (adds DN), TM_dc is `fc := .RTime`
  (adds DN **and** CO, since `Dense ≤ RTime`).
- `Sat .Dense F = DenselyOrdered F.Duration`; `Sat .RTime F = F.IsDense ∧ F.IsComplete`
  (`Semantics/FrameClassValidity.lean:121`, `Semantics/FrameProperty.lean:105,212`). `F.Duration`
  is always a nontrivial linearly ordered abelian group (`Semantics/TemporalOrder.lean:76`).

The hard constraint inherited from `Metalogic/Conservativity.lean` — never state a completeness or
forward-conservativity theorem and discharge it with `sorry` — is respected throughout. Note the
prohibition is against *sorry-ing*, not against *proving*: `forward` is refuted only at `.Base`
and `.ZTime`, so a genuine proof at `.Dense` or `.RTime` is a legitimate outcome.

## Literature Proof Structure

**Source**: the task brief's own citations — Bull 1968 (algebraic study of tense logics with
linear time); Burgess, *Basic Tense Logic* (Handbook of Philosophical Logic II); Goldblatt,
*Logics of Time and Computation*; Reynolds 1992 (the U/S axiomatization of ℝ, already formalized
in this tree). None of these is present in `specs/literature/` or the global Literature index —
the structure below is reconstructed from the brief plus the repository's own §5(i) record, and
each step is flagged with its confidence.

**Strategy**: Sahlqvist canonicity for the Dense half; a non-canonical step-by-step /
completion argument for the Dedekind half.

### Step Map

1. **Frame correspondents of TM.** `R_□` an equivalence (MK/MT/M5); `R_<` transitive (T4),
   serial (TS), converse-connected (TC), weakly linear (TL); MF (`□φ → □Gφ`) corresponds to
   `R_□ ∘ R_< ⊆ R_□`, which with reflexivity of `R_□` yields `R_< ⊆ R_□`. — [§5(i) of the
   archived TM-completeness-status report; textbook, high confidence]
2. **All of them are Sahlqvist**, hence TM is canonical and complete over exactly that Kripke
   class. DN (`GGφ → Gφ`) is Sahlqvist too and corresponds to density. — [textbook, high
   confidence]
3. **Bulldozing** replaces `R_<`-clusters by strict dense chains (Segerberg / Bull). — [textbook]
4. **Cantor**: every countable dense unbounded linear order is order-isomorphic to ℚ, so a
   countable model's chains can all be taken to be ℚ. — [Mathlib: `Order.iso_of_countable_dense`]
5. **Product/translation transfer**: realize the bulldozed union-of-ℚ-chains as a task frame over
   `D := ℚ`. — [this repository already supplies it, see Findings]
6. **Dedekind half**: Kt4.3 + Dens + Unb + the Dedekind axiom axiomatizes the H/G logic of ℝ
   (Bull 1968; reproved by Burgess). CO in this tree *is* that Dedekind axiom (verified
   semantically below). — [literature claim, **medium confidence — unverified against source**]
7. **Dedekind transfer**: because CO is not Sahlqvist, step 2 does not apply; a step-by-step
   construction, a Dedekind-completion argument, or a Doets-style ℚ→ℝ monadic transfer is needed.

### Dependencies

- Step 2 depends on step 1. Step 3 depends on step 2. Step 4 depends on step 3 plus a countability
  step (downward Löwenheim–Skolem on the standard translation, or a Henkin construction that is
  countable by design). Step 5 depends on step 4.
- Step 7 depends on step 6 and replaces steps 2–4 for the Dedekind row; steps 1 and 5 are shared.

### Potential Formalization Challenges

- **Step 2**: no Sahlqvist machinery exists in this tree; canonicity must be proved by hand, for
  this specific axiom set, over BL-MCSs (sets of `BLFormula`, a type that currently has no MCS
  layer at all — the entire `Metalogic/Core/` MCS apparatus is over `Formula`).
- **Step 3**: bulldozing is fiddly in a dependently typed setting (cluster quotients, then a
  lexicographic re-expansion).
- **Step 4**: Mathlib's downward Löwenheim–Skolem (`FirstOrder.Language`) would require encoding
  the bimodal model as a first-order structure and relating modal truth to the standard
  translation — a substantial detour. Building the countable model directly is likely cheaper.
- **Step 6/7**: the honest blocker. See Findings → Dedekind.

## Findings

### Codebase Patterns

#### F1. `□` is the universal modality (new, machine-checked)

`BLTruthAt`'s box clause is `∀ σ, σ.IsTotal → BLTruthAt M σ t φ` — same time, all total histories
(`Semantics/BLTruth.lean:103`). Because `WorldHistory.timeShift` preserves totality
unconditionally (`WorldHistory.isTotal_timeShift`) and truth (`TimeShift.timeShift_preserves_truth`,
`Semantics/Truth.lean:792`), the box clause is *also* time-blind. The tree already records half of
this as `Truth.box_const` (`Semantics/Truth.lean:862`, "`□` is a model constant"). The full
statement — that `□` is the **universal modality over the whole model** — is new and was compiled
sorry-free this dispatch:

```
theorem bl_box_universal {F : TaskFrame} (M : TaskModel F) (τ σ₀ : WorldHistory F)
    (t : F.Duration) (hτ : τ.IsTotal) (φ : BLFormula) :
    BLTruthAt M τ t φ.box ↔ ∀ (σ : WorldHistory F), σ.IsTotal → ∀ s, BLTruthAt M σ s φ
```

Consequence, and the pivot of the whole verdict: **BL over task frames is not a product logic in
the hard sense.** The `□`/`H`,`G` interaction contributes no "same-time alignment" validities,
because `□` quantifies over the whole model rather than over a time-indexed fibre. TM's H/G core
plus a universal modality is therefore the right Kripke target, exactly as §5(i) of the archived
report predicted at the Kripke level.

#### F2. The exact semantic target class

Combining F1 with the classification of total histories (F3), `BLValidIn fc φ` is refutable
precisely on structures of the following shape, for `D` an `fc`-admissible temporal order:

> a nonempty index set `FamIdx` of **chains**, each a copy of `D`; points are `FamIdx × D`;
> `H`/`G` quantify within a chain by the `D`-order; `□` quantifies over all points.

So:

- `TMComplete .Dense` ⟺ TM_d is complete for **disjoint unions of ℚ-chains with `□` universal**.
- `TMComplete .RTime` ⟺ TM_dc is complete for **disjoint unions of ℝ-chains with `□` universal**.

(ℚ and ℝ, not "some dense/complete order", because the completeness direction only needs *some*
admissible `D`, and `Order.iso_of_countable_dense` collapses countable dense unbounded chains to ℚ
while Bull's theorem, if true, delivers ℝ-chains directly.)

#### F3. The product/translation transfer already exists and is generic

`FormalSystem/Metalogic/Algebraic/FlowFrame.lean`:

- `multiFamTaskFrameGen (D : TemporalOrder) (FamIdx : Type) [Nonempty FamIdx] : FrameOver D`
  (`:146`) — world states `FamIdx × ↑D`, task relation `p ⇒_d q ↔ p.1 = q.1 ∧ q.2 = p.2 + d`.
  All four frame axioms discharged generically: `comp` by `TaskFrame.comp_of`, `serial` by explicit
  successor/predecessor, `limit` by `TaskFrame.limit_of_shift`, `saturation` by
  `TaskFrame.saturation_of_fib_subsingleton` (fibres are singletons).
- `multiFamHistoryGen f w₀` (`:177`), total by `multiFamHistoryGen_total` (`:204`) definitionally.
- `multiFamHistoryGen_shift_eq` (`:190`) — the shift of a translate is a translate.
- **`multiFamGen_total_eq_range` (`:396`)** — `{σ | ∀ t, σ.domain t} = Set.range (fun p =>
  multiFamHistoryGen p.1 p.2)`. The total histories are *exactly* the translates.

This is precisely the brief's "disjoint union of translation task frames, each satisfying
Compositionality, Seriality, Limit, Saturation with singleton fibres" — already landed, already
generic in both `D` and `FamIdx`, and already the frame used by both existing completeness proofs
(`bundleFlowFrame` is *definitionally* `multiFamTaskFrameGen`, `FlowFrame.lean:450`).

What is missing is only the **semantic** transfer lemma at the BL level: an induction showing
`BLTruthAt (bundleModel v) (multiFamHistoryGen f w₀) t φ ↔ KripkeSat v (f, w₀ + t) φ` for a bare
valuation `v : FamIdx × D → Atom → Prop`. The BL⁺ analogue exists but is entangled with MCS data
(`bundleFlow_truth_lemma`, `FlowFrame.lean:662`, stated over `BFMCS`). A valuation-only restatement
is the right shape and is a ~100-line induction; its `box` case is `multiFamGen_total_eq_range`
plus F1.

#### F4. The BL side has no time-shift lemma, and it is three lines away

`Semantics/BLTruth.lean` (204 lines) has the six clause lemmas and nothing about shifting. A
repo-wide grep of `BLTruthAt` against `shift|timeShift` returns zero hits. The derivation is:

```
BLTruthAt M (σ.timeShift (y-x)) x φ
  ↔ TruthAt M (σ.timeShift (y-x)) x (tr φ)   -- (truthAt_tr …).symm
  ↔ TruthAt M σ y (tr φ)                     -- TimeShift.timeShift_preserves_truth
  ↔ BLTruthAt M σ y φ                        -- truthAt_tr
```

with `truthAt_tr` at `Metalogic/Conservativity/BaseLanguageSoundness.lean:110`, fully polymorphic
in `F` and carrying no frame-class hypothesis.

#### F5. Neither closed row's obstruction transfers

- **Base row.** `Sp φ ψ := □(DF φ) ∨ □(DN ψ)` (`Conservativity/SpWitness.lean:74`) is `BLValid`
  because a frame's single `Duration` decides `duration_dense_or_least_pos` once. At `.Dense` the
  right disjunct's inner formula *is* the DN axiom, so `⊢ᴮᴸ[.Dense] □(DN ψ)` by `Axiom.dn` +
  `necessitation`, and `Sp` follows by `Axiom.prop_s`. Compiled sorry-free as
  `sp_derivable_dense` (Appendix A.2). Since `Dense ≤ RTime`, it lifts to `.RTime` too.
- **Discrete row.** `Z1 p = G(Gp→p) → (FGp→Gp)` fails on ℚ: take `p := {x | 1 ≤ x}`; then
  `Gp(t) ↔ 1 ≤ t`, so `G(Gp→p)` holds at `0`, `FGp` holds at `0` (witness `1`), and `Gp` fails at
  `0`. So `Z1` is not `BLValidIn .Dense` and cannot separate. (Hand-checked, not machine-checked;
  cheap to formalize if wanted.)

This is the structural reason the brief's expected verdict is the right prior: the closed rows are
both closed by **dichotomy/rigidity** witnesses that need the frame class to split into two
H/G-distinguishable subclasses. `.Dense` and `.RTime` do not split.

#### F6. Why the BL⁺ machinery cannot be borrowed

The tree's dense and Dedekind completeness proofs are over `Formula` (BL⁺, with `untl`/`snce`
primitive) and start from a `SetMaximalConsistent` set of `Formula`s:

- `BXCanonical.completeness_dense` (`Completeness.lean:255`), via `Chronicle.cantorBfmcsDense` at ℚ.
- `BXCanonical.completeness_rtime_engine` (`CompletenessDedekind.lean:590`), via the five Reynolds
  1992 §9 steps to ℝ.
- Both sorry-free (`[propext, Classical.choice, Quot.sound]`). The `Chronicle/` spine is 16 358
  lines; the whole `BXCanonical/` tree is 23 120.

To reuse any of it for BL one would need "`{¬φ}` is TM_d-consistent ⟹ `{tr ¬φ}` is
TM⁺_d-consistent", which is the contrapositive of forward conservativity — the thing being proved.
The circularity is unavoidable: `Fragment.lean`'s own docstring already says a native
axiomatization of the H/G fragment "is open research and is not attempted here".

#### F7. CO is the Dedekind axiom (semantic check)

`Axiom.co φ := △(Hφ → F Hφ) → (Hφ → Gφ)` (`BaseLanguage/Axioms.lean:214`, `△` the *temporal*
triangle). Reading `S := {u | Hφ(u)}`: `S` is downward closed; the antecedent says `S` has no
maximum; the conclusion says `t ∈ S → Gφ(t)`. On a Dedekind-complete order a downward-closed
maximum-free `S` cannot have a supremum (the supremum would lie in `S`), hence `S` is unbounded
above, hence `Gφ(t)`. On ℚ it fails: take `φ(w) :↔ w < √2`; then `S = {u | u < √2}`, the antecedent
holds, `0 ∈ S`, and `Gφ(0)` is false at `2`. So CO corresponds exactly to Dedekind completeness,
as the brief states. (Hand-checked. `Metalogic/SoundnessLemmas/CoValidity.lean:75` already carries
the BL⁺ soundness half, `co_valid : ValidRTime (Formula.co φ)`.)

#### F8. The Dedekind obstruction, named precisely

The abstract Doets layer is genuinely reusable — this was the most valuable negative-risk finding:

- `DoetsD1` / `DoetsD2` (`WeakCanonical/RealModel/DoetsTheorem.lean:403,410`) are predicates over
  an **arbitrary** `OrderedMonadicStructure` at an **arbitrary** `MonadicSignature`.
- `doets_theorem_dense` (`:2190`) transfers any countable dense unbounded structure satisfying
  D1/D2 to a real flow, preserving `KEquiv` at depth `k`. Binders: `Countable`, `Nonempty`,
  `DenselyOrdered`, `NoMaxOrder`, `NoMinOrder` on the carrier, plus D1 and D2.
- The D1/D2 **suppliers** are abstract too: `no_gaps_dense_prior`
  (`DenseModelSurgery/NoGaps.lean:1051`) and `reynolds_theorem5`
  (`DenseModelSurgery/Singletons.lean:523`), stated for any structure with a surjective `atomMap`
  and `SemanticPriorU` / `SemanticPriorS` / `SemanticSepOpen`.

**The gap**: every existing discharge of those three semantic conditions consumes the BL⁺-only
axioms. `chronicleMonadic_semanticPriorU` (`Chronicle/ChronicleMonadicBridge.lean:815`) consumes
`Axiom.prior_U_gap`; `…semanticPriorS` (`:864`) consumes `Axiom.prior_S_gap`;
`…semanticSep` (`:912`) consumes `Axiom.sep`. D1 needs PriorU+PriorS; D2 needs all three
(`ChronicleRealFlow.lean:90,105` → `ChronicleInstance.lean:79,94,121`). None of `prior_U_gap`,
`prior_S_gap`, `sep` is expressible in BL: each is built from `untl`/`snce`/`kPlus`/`kMinus`, and
`BLFormula` has only `atom | bot | imp | box | allPast | allFuture`.

So the Dedekind row's obstruction is exactly: **discharge `SemanticPriorU` / `SemanticPriorS` /
`SemanticSepOpen` (or weaker H/G-sufficient replacements for D1/D2) on a BL-side canonical
structure from CO alone.** Whether CO suffices is, in classical terms, precisely the content of
Bull's theorem; nothing in this tree or in Mathlib bears on it. This is a research gap.

Two secondary risks compound it: (a) the brief's own note that CO is not Sahlqvist, so the Dense
route's canonicity argument does not carry over; (b) `sep` is named for **separability**, which
strongly suggests that in the U/S language ℝ is distinguished from other Dedekind-complete chains
— if the same is true in the H/G language, the Dedekind verdict flips to **negative** and the
separating witness is an ℝ-valid formula refuted on (say) the double long line. That flip is not
ruled out by anything found here.

### External Resources

- **`Order.iso_of_countable_dense`** — Mathlib, `Mathlib/Order/CountableDenseLinearOrder.lean`,
  verified present in this checkout:
  `∀ (α β) [LinearOrder α] [LinearOrder β] [Countable α] [DenselyOrdered α] [NoMinOrder α]
  [NoMaxOrder α] [Nonempty α] [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β]
  [Nonempty β], Nonempty (α ≃o β)`. This is Cantor's theorem and is exactly step 4 of the Dense
  route. Sibling `Order.embedding_from_countable_to_dense` also available.
- **`FirstOrder.Language.aleph0_categorical_dlo`** (`Mathlib.ModelTheory.Order`) — an alternative,
  model-theoretic phrasing; not recommended, since it would force the whole construction into
  Mathlib's `FirstOrder` encoding.
- **`orderIsoIntOfLinearSuccPredArch`** (`Mathlib.Order.SuccPred.LinearLocallyFinite`) — the
  discrete analogue this tree already leans on for `.ZTime`; listed only as the pattern to imitate.
- **Bull 1968 / Burgess / Goldblatt** — not present in `specs/literature/` and not in the global
  Literature index. If the Dedekind row is pursued, ingesting Burgess's *Basic Tense Logic* (or
  Gabbay–Hodkinson–Reynolds vol. 1) is a prerequisite; the step map above is reconstructed, not
  transcribed, and step 6 is flagged medium-confidence for that reason.

### Recommendations

Priority order. Owner for all: a `lean-implementation` dispatch under this task unless noted.

1. **[P1] Land the infrastructure round, sorry-free, asserting no completeness theorem.**
   Estimated 350–500 lines. Nothing here is at risk, and all of it is reusable by both rows.
   - `BLTruth.timeShift_preserves_truth` (F4, three lines via `truthAt_tr`).
   - `bl_box_universal` (Appendix A.1, verbatim — it compiles today).
   - `sp_derivable_dense` (Appendix A.2, verbatim) plus its `.RTime` lift, and the
     `Z1` non-Dense-validity counterpart of F5. These are the machine-checked record that neither
     closed row's obstruction transfers, and they belong next to `SpWitness.lean` /
     `Z1Countermodel.lean`.
   - A valuation-only chain-bundle truth lemma for `multiFamTaskFrameGen` (F3): define
     `chainSat (v : FamIdx × D → Atom → Prop) : FamIdx × D → BLFormula → Prop` with `□` universal,
     and prove
     `BLTruthAt (chainModel v) (multiFamHistoryGen f w₀) t φ ↔ chainSat v (f, w₀ + t) φ`.
     This is the brief's route step (3), and it converts *any* union-of-`D`-chains countermodel
     into a task-frame countermodel.
   - A corollary `¬ chainSat … φ → ¬ BLValidIn fc φ` for `fc.Sat`-admissible `D`, which is the
     single interface the canonical-model work will consume.
2. **[P1] Record the Dense verdict as EXPECTED COMPLETE with the route de-risked**, and the
   Dedekind verdict as **OPEN with the F8 obstruction named**, in a module docstring alongside
   `TMCompletenessReduction.lean`. The brief explicitly sanctions an honest OPEN verdict that
   names the precise obstruction; F8 is that obstruction, stated at declaration granularity.
3. **[P2] Scope the Dense canonical model as its own task, not as a phase of this one.** It needs:
   a BL-MCS layer over `BLFormula` (Lindenbaum for `BaseLanguage.DerivationTree`; the existing
   `Metalogic/Core/` apparatus is `Formula`-only and does not transfer for free), the canonical
   frame with `BxLe`-style G/H-content order, canonicity for the eleven Base axioms + DN,
   bulldozing, and a countable-ℚ realization. Estimate **2 500–4 000 lines**, comparable to a
   scaled-down `Chronicle/` but without any Until/Since defect discharge — the H/G case has no
   eventualities to schedule, which is the single largest saving. Deliverable:
   `TMComplete FrameClass.Dense`, equivalently `Forward FrameClass.Dense`. Asserting it is
   *permitted* — `forward` is refuted only at `.Base` and `.ZTime`.
4. **[P3] Do not attempt the Dedekind row until (3) lands.** If pursued afterwards, the two
   candidate routes are, in order of expected cost:
   (a) reuse `doets_theorem_dense` with new BL-side D1/D2 suppliers proved from CO — cheapest if
   it works, since the abstract layer is already generic (F8), but its feasibility is unknown;
   (b) formalize Bull's step-by-step construction directly. Either way, ingest the literature
   first (`/literature` on Burgess or Gabbay–Hodkinson–Reynolds).
5. **[P3] Before committing to (4), spend one dispatch trying to *refute* the Dedekind row.**
   The `sep`-is-separability signal (F8, risk (b)) makes a negative verdict live. A concrete
   probe: is there an H/G formula valid on ℝ but refuted on a Dedekind-complete non-separable
   dense unbounded chain? A yes is a *complete outcome* at a fraction of the cost of (4), because
   TM_dc is sound over all such chains and the formula is then `BLValidIn .RTime` but underivable.

## Decisions

- **D1. Verdict recorded as: Dense = expected complete (no obstruction); Dedekind = OPEN with
  named obstruction.** Not "both complete". The brief's expected verdict is upheld for Dense on
  the strength of F1/F2/F3/F5, but the Dedekind half rests on an unverified literature claim
  (step 6) *and* on an in-tree gap (F8) that is not merely a cost, so asserting it would overstate.
- **D2. `□` is treated as the universal modality, not as one half of a product.** F1 is
  machine-checked, so the Kripke target class (F2) is settled rather than conjectured. This is the
  decision that makes the brief's suggested Dense route sound rather than plausible.
- **D3. The BL⁺ chronicle machinery is ruled out as a shortcut** (F6). Any plan that proposes
  reusing `Chronicle/` for the BL rows should be rejected as circular.
- **D4. The transfer step is declared already-solved** (F3). Plans should not budget for
  constructing task frames from chains; only for the truth-transfer induction.
- **D5. No `user_decision` is raised.** The brief itself licenses an OPEN verdict that names the
  obstruction, so the scope call (settle Dense, defer Dedekind) is one research can make on the
  evidence rather than a preference the artifacts cannot infer.
- **D6. No completeness or forward-conservativity theorem is stated anywhere in the recommended
  P1 round**, honouring the `Conservativity.lean` hard constraint. `TMComplete .Dense` is stated
  only when it is proved, in the task recommended at (3).

## Risks & Mitigations

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| R1 | Bull's theorem (step 6) is misremembered, or is stated for a different axiom than CO | Medium | Ingest the source before any Dedekind work; recommendation (4) gates on this. The report flags step 6 as medium-confidence rather than asserting it. |
| R2 | The H/G logic of ℝ is *strictly stronger* than TM_dc (separability detectable), flipping Dedekind to negative | Medium | Recommendation (5) turns this risk into the cheapest possible complete outcome instead of a late surprise. |
| R3 | The Dense canonical model exceeds its estimate and stalls in `[IMPLEMENTING]` | Medium-high | Scope it as its own task (recommendation 3) with per-phase sorry-free milestones (MCS layer → canonical frame → canonicity per axiom → bulldozing → ℚ realization), and never state `TMComplete` until the last phase. |
| R4 | Downward Löwenheim–Skolem proves to be the wrong tool for the countability step | Medium | Prefer a directly countable Henkin/step-by-step construction; the tree's own `Chronicle` spine is evidence that the direct route is tractable here, and Mathlib's `FirstOrder` encoding detour can be avoided entirely. |
| R5 | Bulldozing interacts badly with the `□`-class structure (clusters spanning chains) | Low-medium | F1 makes `□` universal and therefore *independent* of the temporal structure; bulldozing acts on `R_<` only and cannot disturb a universal relation. |
| R6 | A BL-MCS layer duplicates `Metalogic/Core/` and drifts from it | Medium | Mirror `Core/MaximalConsistent.lean`'s statement shapes deliberately, and note the duplication in the new module's docstring; the two languages genuinely differ (six constructors vs. the `untl`/`snce` primitives), so sharing is not available. |
| R7 | Landing `Forward FrameClass.Dense` is read as violating the `Conservativity.lean` prohibition | Low | State explicitly in the docstring that the prohibition is against `sorry`-ing, and that `forward` is refuted only at `.Base` and `.ZTime`; `tmCompleteDense_iff_forwardDense` already exists precisely so the two readings stay linked. |

## Tactic Survey Results

A tactic survey in the `lean_multi_attempt` sense was not the right instrument for this dispatch —
there is no open proof goal to close; the deliverable is a verdict plus a route. What was done
instead is stronger: two candidate lemmas were written out and **elaborated against the live
project** via `lean_run_code`, and both compile sorry-free.

| Goal | Instrument | Result | Notes |
|------|-----------|--------|-------|
| `bl_box_universal` (F1) | `lean_run_code`, full elaboration | success | `[propext]`; proof is `truthAt_tr` + `Truth.box_const`, no induction |
| `sp_derivable_dense` (F5) | `lean_run_code`, full elaboration | success | `[propext]`; `Axiom.dn` + `necessitation` + `Axiom.prop_s` + MP |
| `by decide` for `Axiom.dn ψ |>.minFrameClass ≤ .Dense` | `lean_run_code` | fail | free variables in the expected type; use `le_refl FrameClass.Dense` and `FrameClass.base_le _` instead — recorded so the implementation dispatch does not rediscover it |

`lean_local_search` confirmed `Order.iso_of_countable_dense` is present in the pinned Mathlib;
`lean_leansearch` supplied its full signature. No rate limits were hit, no fallbacks were needed,
and no blocked tool (`lean_diagnostic_messages`, `lean_file_outline`) was called.

## Context Extension Recommendations

- **Topic**: the Kripke-level reading of the task semantics.
  **Gap**: `context/project/logic/domain/kripke-semantics-overview.md` does not record that BL's
  `□` over task frames is the *universal* modality, nor the F2 correspondence between task frames
  and unions-of-`D`-chains. Both are now machine-checked and are the single most reusable fact for
  any future completeness or definability work in this repository.
  **Recommendation**: add a short section to that file citing `Truth.box_const`
  (`Semantics/Truth.lean:862`) and the new `bl_box_universal`.
- **Topic**: the FrameClass row status table.
  **Gap**: the four-row status (Base refuted, Discrete refuted, Dense expected-complete, Dedekind
  open-with-obstruction) is currently spread across `Metalogic.lean`, `Conservativity.lean`,
  `Fragment.lean`, and an archived report.
  **Recommendation**: one canonical table, in `Conservativity/TMCompletenessReduction.lean`'s
  docstring, updated by whichever dispatch lands recommendation (2).

## Appendix

### A.1 `bl_box_universal` — verified this dispatch

Elaborated against the live project via `lean_run_code`; result `success`, sole warning an unused
binder. Imports `FormalSystem.Semantics.BLTruth` and
`FormalSystem.Metalogic.Conservativity.BaseLanguageSoundness`; opens
`FormalSystem.Syntax FormalSystem.Semantics FormalSystem.BaseLanguage`.

```lean
theorem bl_box_universal {F : TaskFrame} (M : TaskModel F) (τ σ₀ : WorldHistory F)
    (t : F.Duration) (hτ : τ.IsTotal) (φ : BLFormula) :
    BLTruthAt M τ t φ.box ↔ ∀ (σ : WorldHistory F), σ.IsTotal → ∀ s, BLTruthAt M σ s φ := by
  constructor
  · intro h σ hσ s
    have hb : TruthAt M τ t (tr φ).box := (truthAt_tr M φ.box τ t).mpr h
    have h2 := (Truth.box_const M τ σ hτ hσ t s (tr φ)).mp hb
    exact (truthAt_tr M φ σ s).mp (h2 σ hσ)
  · intro h σ hσ
    exact h σ hσ t
```

The `σ₀` binder is vestigial and should be dropped when the lemma is landed.

### A.2 `sp_derivable_dense` — verified this dispatch

Elaborated via `lean_run_code`; `#print axioms sp_derivable_dense` reported `[propext]`.
Imports `FormalSystem.Metalogic.Conservativity.SpWitness`; opens
`FormalSystem.Syntax FormalSystem.ProofSystem FormalSystem.BaseLanguage FormalSystem.Metalogic`.

```lean
noncomputable def sp_derivable_dense (φ ψ : BLFormula) :
    ⊢ᴮᴸ[FrameClass.Dense] Sp φ ψ :=
  let dn : ⊢ᴮᴸ[FrameClass.Dense] (ψ.allFuture.allFuture.imp ψ.allFuture) :=
    .axiom [] _ (Axiom.dn ψ) (le_refl FrameClass.Dense)
  let boxdn := DerivationTree.necessitation _ dn
  let s : ⊢ᴮᴸ[FrameClass.Dense]
      ((ψ.allFuture.allFuture.imp ψ.allFuture).box.imp
        ((((φ.allPast.and φ).and BLFormula.top.someFuture).imp
          φ.allPast.someFuture).box.neg.imp
          (ψ.allFuture.allFuture.imp ψ.allFuture).box)) :=
    .axiom [] _ (Axiom.prop_s _ _) (FrameClass.base_le _)
  DerivationTree.modus_ponens [] _ _ s boxdn
```

### A.3 Key declaration index

| Declaration | Location |
|---|---|
| `TMComplete`, `Forward`, `tmComplete_iff_forward` | `Metalogic/Conservativity/TMCompletenessReduction.lean:96,104,125` |
| `tmCompleteDense_iff_forwardDense`, `tmCompleteRTime_iff_forwardRTime` | same file, `:176,182` |
| `TMFrag`, `tmFrag_complete_dense`, `tmFrag_complete_rtime` | `Metalogic/Conservativity/Fragment.lean:76,105,115` |
| `BLTruthAt` | `Semantics/BLTruth.lean:103` |
| `Truth.box_const`, `TimeShift.timeShift_preserves_truth` | `Semantics/Truth.lean:862,792` |
| `truthAt_tr`, `blValidIn_iff_validIn_tr` | `Metalogic/Conservativity/BaseLanguageSoundness.lean:110` |
| `Axiom.dn`, `Axiom.co`, `Axiom.modal_future`, `Axiom.minFrameClass` | `BaseLanguage/Axioms.lean:208,214,178,228` |
| `FrameClass`, `LE FrameClass` | `ProofSystem/Axioms.lean:529` |
| `FrameClass.Sat`, `TaskFrame.IsDense`, `TaskFrame.IsRTime` | `Semantics/FrameClassValidity.lean:121`, `Semantics/FrameProperty.lean:105,212` |
| `multiFamTaskFrameGen`, `multiFamHistoryGen`, `multiFamGen_total_eq_range` | `Metalogic/Algebraic/FlowFrame.lean:146,177,396` |
| `bundleFlow_truth_lemma` | `Metalogic/Algebraic/FlowFrame.lean:662` |
| `completeness_dense`, `completeness_rtime_engine` | `Metalogic/BXCanonical/Completeness.lean:255`, `CompletenessDedekind.lean:590` |
| `WeakCompleteness` | `Metalogic/SetConsequence.lean:234` |
| `DoetsD1`, `DoetsD2`, `doets_theorem_dense` | `Metalogic/WeakCanonical/RealModel/DoetsTheorem.lean:403,410,2190` |
| `no_gaps_dense_prior`, `reynolds_theorem5` | `WeakCanonical/DenseModelSurgery/NoGaps.lean:1051`, `Singletons.lean:523` |
| `chronicleMonadic_semanticPriorU/S/Sep` | `BXCanonical/Chronicle/ChronicleMonadicBridge.lean:815,864,912` |
| `Sp`, `blValid_sp` | `Metalogic/Conservativity/SpWitness.lean:74,105` |
| `Z1`, `not_bl_derivable_z1`, `blValidZTime_z1` | `Metalogic/Conservativity/Z1Countermodel.lean` |
| `Order.iso_of_countable_dense` | Mathlib, `Mathlib/Order/CountableDenseLinearOrder.lean` |

### A.4 Searches run

- `lean_local_search`: `Order.iso_of_countable_dense`, `iso_of_countable_dense`
- `lean_leansearch`: "any two countable dense unbounded linear orders are order isomorphic (Cantor)"
- `lean_run_code`: three elaborations (two successful lemmas, one failed `by decide` variant)
- Repository greps: `tmCompleteDiscrete`, `refuted`, `sorry` in term position, `timeShift`,
  `modal_future_valid`, `bl_soundness_dense`, `structure TaskFrame`, `truthAt_tr`
- Three parallel `Explore` sweeps: BaseLanguage proof system and FrameClass gating; BXCanonical
  dense/RTime completeness architecture and sorry audit; FlowFrame transfer machinery, Fragment
  theorem, and Doets/Reynolds genericity
- Blocked tools `lean_diagnostic_messages` and `lean_file_outline` were not called.
