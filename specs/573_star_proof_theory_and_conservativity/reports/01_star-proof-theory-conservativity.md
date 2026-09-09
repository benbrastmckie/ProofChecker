# Research Report: Task #573

**Task**: 573 - Star proof theory and conservativity
**Started**: 2026-09-08T00:00:00Z
**Completed**: 2026-09-08T00:00:00Z
**Effort**: large (Phase 0 gate for a 5-phase Lean deliverable)
**Dependencies**: None (all consumed groundwork is landed)
**Sources/Inputs**:
- Codebase: `FormalSystem/StarLanguage/`, `FormalSystem/Semantics/Star*.lean`,
  `FormalSystem/PlusLanguage/{Axioms,Derivation,Formula}.lean`,
  `FormalSystem/Metalogic/{Soundness.lean,Conservativity/Plus/*}`
- Machine checking: `lake env lean` on three scratch modules (all statements below marked
  **[checked]** compile with zero `sorry`; sources archived in the session scratchpad)
- Literature: SEP *Temporal Logic* §7.1 (hybrid temporal logics; local corpus
  `sources/sep_temporal-logic/chunk_006{5,6,7}.md`); Blackburn–de Rijke–Venema *Modal Logic*
  §7.3 (local corpus `sources/blackburn_2002/ch07_since-until-hybrid.md`)
**Artifacts**: - `specs/573_star_proof_theory_and_conservativity/reports/01_star-proof-theory-conservativity.md`
**Standards**: report-format.md, subagent-return.md

## Executive Summary

- **The TM⁺ axiom set does NOT transfer schematically to `StarFormula`.** Exactly one schema
  fails: **MF, `modal_future` (`□φ → □Gφ`)**. It is refuted **[checked]** over `NF` at
  `φ := ↓¹p → p`. Every other TM/TM⁺ schema survives, because MF is the only one whose
  soundness proof uses time-shift homogeneity (`Metalogic/Soundness.lean:303-311` is the sole
  `timeShift` consumer in the schema block), and `starTruthAt_timeShift` shifts the stored-time
  vector along with the history. This single fact is the gate on the whole plan.
- **The axiomatization is derivable from the truth clauses and is mostly `Iff.rfl`.** Both
  registers are self-dual normal (functional) modalities that commute with `□`; `↑ⁱ` also
  commutes with `⊡`, `↓ⁱ` does **not** (refuted **[checked]**); `↓ⁱ` is time-rigid. Nine
  positive schemata are machine-checked below. The dispatch's candidate `↑ⁱ↓ⁱφ ↔ φ` is
  **refuted**; the correct law is `↑ⁱ↓ⁱφ ↔ ↑ⁱφ`.
- **Naive register erasure is provably not a conservativity translation** **[checked]**:
  `↑¹G↓¹p → p` is `StarValid` while its erasure `Gp → p` is refuted over `NF`. The dispatch's
  conjecture on this point is confirmed.
- **Conservativity over TM⁺ is neither provable nor refutable by any route in this tree, and
  the reason is a theorem, not a gap.** Given TM⋆ soundness, `⊢⋆ ofPlus φ ⟹ PlusValid φ`; hence
  *any* separating witness for non-conservativity **is** a TM⁺ completeness failure
  **[checked]**. So Phase 4 must deliver (a) the conditional `TM⁺ complete ⟹ TM⋆ conservative`,
  (b) its unconditional contrapositive `TM⋆ non-conservative ⟹ TM⁺ incomplete`, and
  (c) the **unconditional** result that *does* land: **TM⋆ is a conservative extension of TM,
  both directions, at all four frame classes** **[checked]** — a strictly stronger deliverable
  than the dispatch's "strictly weaker fallback" framing suggests, because the backward half
  composes for free.
- **TM⋆ completeness is not reachable and the obstruction is nameable**: all four TM
  completeness engines produce **deterministic** countermodels, and every deterministic frame
  validates `sentDet` (`sentDet_of_deterministic`) which is **not** `StarValid`
  (`refute_sentDet`). So no existing engine can ever countermodel `¬sentDet p`. Phase 5 must be
  recorded as OPEN with that obstruction plus the literature verdicts, not attempted.

## Context & Scope

Researched: (a) which schema set over `StarFormula` the `StarTruthAt` clauses license;
(b) whether the `PlusAxiom`/`PlusDerivationTree` shape mirrors verbatim; (c) whether
`⊢⋆[fc] (ofPlus φ) → ⊢⁺[fc] φ` is true, false, or unreachable; (d) whether TM⋆ completeness is
reachable.

Constraints honoured: no `sorry` is proposed anywhere; no argument by uniform substitution is
used or recommended (TM⁺ is already not substitution-closed — `atom_stab` is atom-restricted);
no manuscript prose is touched; every rejected candidate carries a refutation over a task frame.

**Notation bridge (recorded once, used throughout).** The manuscript's `↑ⁱ` is the hybrid
*binder* (`↓xᵢ` in Blackburn–Seligman notation, Goranko's *reference pointer*): it writes the
present time into register `i`. The manuscript's `↓ⁱ` is the hybrid *satisfaction operator*
(`@ᵢ`): it jumps evaluation to the time register `i` holds. The notation is therefore
**reversed** relative to the hybrid-logic literature, and every literature citation below has
been translated into the manuscript's spelling. One decisive difference from `H(@,↓)`:
**L⋆ has no nominals** — a register is only ever an operator index, never a formula — so no
formula of L⋆ is known to express "the present time is register `i`".

## Findings

### Codebase Patterns

**What is landed and must be consumed, not rebuilt.**

| Asset | Location | Role in this task |
|---|---|---|
| `ofPlus`, `ofStarCtx`, `mem_ofStarCtx`, `ofPlus_injective` | `StarLanguage/Formula.lean` | Phase 3 embedding |
| the `rfl` commutation pins (`ofPlus_neg`, `ofPlus_allFuture`, …) | `StarLanguage/Formula.lean` | make `StarAxiom.ofBase` arms `rfl`-shaped |
| `starTruthAt_ofPlus` | `Semantics/StarTruth.lean` | truth transfer |
| `starValidOn_ofPlus`, `starValidOnFrames_ofPlus` | `Semantics/StarValidity.lean` | **the Phase-4 workhorse** |
| `StarTruth.timeStore_iff` / `timeRecall_iff` and the seven mirrored clause lemmas | `Semantics/StarTruth.lean` | every axiom-validity proof |
| `starTruthAt_timeShift`, `update_shift_comm`, `star_truth_congr_ext` | `Semantics/StarTruth.lean` | the MF analysis |
| `NF`, `natHist`, `natModel`, `natHist_isTotal` | `Semantics/PlusNonValidities.lean` | every refutation below |
| `plusAxiom_validIn_min` / `plusAxiom_swap_validIn_min` | `Conservativity/Plus/AxiomValidity.lean` | discharge `ofBase` soundness **for free** |
| `plusValidIn_ofFormula_iff`, the four `WeakCompleteness` engines | `Semantics/`, `Metalogic/StrongCompleteness.lean` | the unconditional Phase-4 chain |

**Atomization is unavailable for L⋆, and this is load-bearing.** `Conservativity/Plus/Atomization.lean`
discharges the 45 TM arms of `plusAxiom_validIn_min` by encoding maximal `⊡χ` subformulas as
fresh atoms; the enabling invariant is `stab_state_only`, i.e. `⊡χ`'s truth is determined by the
world state alone. Neither register-headed formula is state-determined: `↓ⁱχ` at `(τ,x,v)` is
`χ` at `(τ, v i, v)`, which depends on the whole of `τ` and not on `τ.states x`; `↑ⁱχ` depends on
`x` through the register it writes. So **no atomization into `Formula` over the same frame can
exist**, exactly as `StarLanguage/README.md` and `Semantics/StarTruth.lean` §(b) already warn.
This is the single biggest phase-sizing fact in the report (see Recommendations, Phase 2).

### External Resources

- **SEP, *Temporal Logic* §7.1** (local corpus): nominals ("clock variables"), satisfaction
  operators `@ᵢ`, and *reference pointers* `↓ᵢ` (introduced in **Goranko 1996**; a similar
  mechanism in Alur–Henzinger 1994). Verdict quoted: "*While the weaker versions of hybrid
  logics — with nominals, satisfaction operators, universal modality, and difference modality —
  are still decidable, the more expressive ones — with quantifiers over nominals or reference
  pointers — are usually undecidable*" (citing Goranko 1996; Areces & ten Cate 2007). The same
  section records that `U` and `S` are *definable* from nominals + reference pointers
  (`φUψ := ↓ᵢF(ψ ∧ H(Pi → φ))`) — which is why a reference-pointer temporal logic is expected
  to be strictly more expressive than its `U`/`S` base.
- **Blackburn–de Rijke–Venema, *Modal Logic* §7.3** (local corpus): the hybrid completeness
  theory rests on **nominals as first-class atoms** and on the non-orthodox rule **PASTE**
  (a relative of the IRR rule of §4.7); the headline result is that **pure** axioms — formulas
  whose only atoms are nominals — automatically yield systems complete for the frame class they
  define. **This apparatus cannot be stated in L⋆**: a pure formula requires a nominal, and L⋆
  has none. This is the concrete, sourced reason the standard hybrid completeness route is
  closed here, and it is the citation Phase 5 should carry.
- **Reynolds (2003)** and **Zanardo (1991)**, already cited by the TM⁺ row
  (`Conservativity/Plus/README.md`, `docs/theorem-index.md`): neither settles the all-histories
  semantics, so neither transfers to L⋆ either.
- Not consulted from primary text (flagged as literature *expectation*, not verified locally):
  Blackburn–ten Cate on pure extensions and non-orthodox rules; Areces–Blackburn–Marx on
  `H(@,↓)` undecidability and non-compactness. The SEP and BdRV passages above cover the same
  ground at the level of detail this task needs; a Phase-5 write-up that wants the sharper
  citations should fetch them rather than take them from this report.

### The axiomatization: schema-by-schema

Points are `(τ, x, v)` with `v : ℕ → F.Duration`. Recall the two clauses verbatim:
`↑ⁱφ` at `(τ,x,v)` is `φ` at `(τ, x, Function.update v i x)`; `↓ⁱφ` at `(τ,x,v)` is `φ` at
`(τ, v i, v)`. `F.Duration` is a **nontrivial** linearly ordered abelian group
(`Semantics/TemporalOrder.lean:81-91`), so `exists_gt` / `exists_lt` hold and the frame is
serial in both directions.

#### ACCEPT — machine-checked valid

Every entry compiles; `Iff.rfl` means the schema is a *definitional* validity of `StarTruthAt`.

| # | Schema | Justification | Proof shape |
|---|---|---|---|
| S1 | `↑ⁱ↓ⁱφ ↔ ↑ⁱφ` | `update v i x` at `i` is `x` | `simp [StarTruthAt]` |
| S2 | `↓ⁱ↑ⁱφ ↔ ↓ⁱφ` | `update v i (v i) = v` | `simp [StarTruthAt]` |
| S3 | `↓ⁱ↓ʲφ ↔ ↓ʲφ` (all `i,j`) | `↓ⁱ` discards the time, `↓ʲ` resets it | `Iff.rfl` |
| S4 | `↑ⁱ↑ʲφ ↔ ↑ʲ↑ⁱφ` (and `↑ⁱ↑ⁱφ ↔ ↑ⁱφ`) | `Function.update_comm` | `rcases` + `update_comm` |
| S5 | `↑ⁱ(φ→ψ) ↔ (↑ⁱφ → ↑ⁱψ)`, same for `↓ⁱ` | both registers are *functional* | `Iff.rfl` |
| S5′ | self-duality `↑ⁱ¬φ ↔ ¬↑ⁱφ`, `↓ⁱ¬φ ↔ ¬↓ⁱφ` | corollary of S5 (`neg = imp bot`) | `Iff.rfl` |
| S6 | `↑ⁱ□φ ↔ □↑ⁱφ` and `↓ⁱ□φ ↔ □↓ⁱφ` | `□` moves the history, never the time or the vector | `Iff.rfl` |
| S7 | `↑ⁱ⊡φ ↔ ⊡↑ⁱφ` | `⊡`'s `SameStateAt` is taken at the *current* time, which is what `↑ⁱ` writes | `Iff.rfl` |
| S8 | `↓ⁱφ → G↓ⁱφ` and `↓ⁱφ → H↓ⁱφ` (**rigidity**) | `↓ⁱφ`'s truth does not read the time of evaluation | `allFuture_iff` / `allPast_iff` |
| S9 | `↑ⁱp ↔ p` for **atoms** `p` | the atom clause does not read `v` | `Iff.rfl` |
| S10 | `ψ U ↓ⁱφ ↔ (↓ⁱφ ∧ (ψ U ⊤))` (**recall export**; `S` mirror likewise) | rigidity + the `untl` clause | 6-line `constructor` |

The converses of S8 (`G↓ⁱφ → ↓ⁱφ`, `H↓ⁱφ → ↓ⁱφ`) are valid too, by `serial_future` /
`serial_past` plus K; they are cheap and should be axioms (or derived) so the register set is
swap-closed. **Necessitation for both registers is sound** (`⊢ φ ⟹ ⊢ ↑ⁱφ`, `⊢ ↓ⁱφ`): validity
quantifies `v` universally and both register clauses land on legitimate points. There is no
`↓`-binder necessitation hazard here.

Still to be built (not a validity question, a *definition* question):

- `NotFreeReg i : StarFormula → Prop` — the standard free-register predicate: `↓ⁱψ` has `i`
  free; `↑ⁱψ` binds it; `↑ʲ`/`↓ʲ` for `j ≠ i` pass it through. With it:
  **S11 `↑ⁱφ ↔ φ` whenever `¬ NotFreeReg i φ`** (the coincidence axiom; S9 is its atomic case),
  proved from a coincidence lemma `starTruthAt_congr_of_agree` (vectors agreeing on the free
  registers give the same truth). This is the one genuinely new inductive lemma Phase 1 needs.
- Index renaming `↑ⁱφ ↔ ↑ʲ(φ[i:=j])` for fresh `j` needs a register substitution and is only
  wanted for a normal-form theorem. **Recommend deferring**: nothing in Phases 1–4 consumes it.

#### REJECT — refuted, with the refutation

| Candidate | Verdict | Refutation |
|---|---|---|
| `↑ⁱ↓ⁱφ ↔ φ` (the dispatch's candidate) | **FALSE** | **[checked]** `↑¹↓¹↓¹p → ↓¹p` fails over `NF` at `τ = (s ↦ if s ≤ 0 then 0 else 1)`, `x = 0`, `v ≡ 1`: `↑¹` overwrites register 1 with `0`, where `p` holds; the consequent still reads register 1 = `1`, where `p` fails. Correct law: **S1**. |
| `↓ⁱ⊡φ ↔ ⊡↓ⁱφ` | **FALSE** | **[checked]** `↓¹⊡p → ⊡↓¹p` fails over `NF` at `τ ≡ 0`, `x = 0`, `v ≡ 1`: `⊡` at `v 1 = 1` constrains histories agreeing with `τ` at time 1, `⊡` at `x = 0` constrains those agreeing at time 0, and `σ = (s ↦ if s ≤ 0 then 0 else 1)` separates them. This is `stab_state_only`'s documented failure inside a recall scope, now a theorem rather than a remark. The converse direction is expected to fail as well and should be settled in Phase 1. |
| `↑ⁱ(ψ U φ) ↔ (↑ⁱψ U ↑ⁱφ)` (and the `S`, `G`, `H` analogues) | **FALSE** | On the left `↑ⁱ` writes the *evaluation* time `x` once; on the right each temporal quantifier re-writes register `i` with the *quantified* time `s`. Semantically transparent; refute at `φ := ↓ⁱp` on `NF` by the same two histories as above. |
| `↑ⁱ↓ʲφ ↔ ↓ʲ↑ⁱφ` for `i ≠ j` | **FALSE** | Left stores `x` in register `i`; right stores `v j`. At `φ := ↓ⁱp` the two read `p` at different times. |
| **`modal_future` (MF), `□φ → □Gφ`, at arbitrary `φ : StarFormula`** | **FALSE** | see next subsection |
| *Determined*-style or any substitution-closed reading of `atom_stab` | **excluded, unchanged** | already atom-restricted in TM⁺; nothing here changes that, and no argument below uses substitution |

#### The MF failure, in full

MF's L⁺/L soundness proof (`Metalogic/Soundness.lean:303-311`, `modal_future_valid`) is the
**only** schema proof in the TM block that consumes `timeShift`: from `□φ` at `t` one reaches
`φ` at `s > t` by shifting the quantified history. The L⋆ restatement
`starTruthAt_timeShift` reads

```
StarTruthAt M (σ.timeShift Δ) t v φ ↔ StarTruthAt M σ (t + Δ) (fun i => v i + Δ) φ
```

— the vector **shifts with the history**, by design and for a good reason
(`Semantics/StarTruth.lean`, design decision (a)). So the shift argument delivers `φ` at
`(σ, s, v + Δ)`, never at `(σ, s, v)`, and the gap is real:

> **[checked]** `¬ NF.StarValidOn (□(↓¹p → p) → □G(↓¹p → p))`.
> At `x = 0` with `v ≡ 0`, the antecedent is a tautology in every history (`↓¹p` and `p` are read
> at the same time `0`), so `□(↓¹p → p)` holds outright. The consequent fails at
> `σ = (s ↦ if s ≤ 0 then 0 else 1)` and `s = 1`: `σ` has `p` at time `0` and not at time `1`.
> The same statement at unrestricted `StarValid` follows.

Note how weak the refuting hypothesis is: the antecedent is valid on *every* frame and model,
so MF fails on any frame carrying a single history that changes `p`-value forward in time.

**The repair.** MF is valid over `StarFormula` under the side condition that `φ` has **no free
register** (then truth is `v`-independent by the coincidence lemma, and the shifted vector is
harmless). Two candidate side conditions:

| Side condition | Strength | Cost |
|---|---|---|
| `RegFree φ` — no `timeStore`/`timeRecall` anywhere | weakest; excludes MF at `↑¹↓¹p` | one trivial inductive predicate, no coincidence lemma |
| `¬ ∃ i, NotFreeReg i φ` — register-*closed* | principled; the true semantic condition | needs `NotFreeReg` + the coincidence lemma (which S11 needs anyway) |

**Recommendation: `RegFree` for the axiom, with the closed-formula strengthening deferred.**
Rationale: `ofPlus φ` is `RegFree` for every `φ`, so Phase 3's embedding is unaffected; nothing
in Phases 2–4 consumes MF at a register-closed-but-not-register-free instance; and it keeps
Phase 1 free of the coincidence machinery. If S11 lands in Phase 1 anyway, upgrade.

### Proof-system shape: the two hazards, settled

**(i) `swapTemporal` does extend, and the register arms are the obvious ones.**
`swapTemporal` does not exist on `StarFormula` (confirmed: `PlusFormula.swapTemporal` at
`PlusLanguage/Formula.lean:208-215`; no `StarFormula` counterpart). It extends soundly with

```
| timeStore i φ  => timeStore i φ.swapTemporal
| timeRecall i φ => timeRecall i φ.swapTemporal
```

exactly as `stab φ ↦ stab φ.swapTemporal`, and for the same reason: the registers hold *times*
and are invariant under time reversal, neither one being oriented. The involution proof and the
`rfl`-shaped `ofPlus_swapTemporal` pin follow the `PlusFormula` file verbatim. Free registers are
preserved, so the MF side condition survives duality.

Crucially, TD is discharged **semantically** in this tree (`plusAxiom_swap_validIn_min` +
the companion recursion of `PlusSoundness.lean`), never by a mirror argument, so the only
obligation is: *each `StarAxiom` arm's `swapTemporal` is valid*. For the `ofBase` arm this is
`plusAxiom_swap_validIn_min` transported by `starValidOnFrames_ofPlus` — free. For the register
arms, S1–S7, S9, S10 are self-dual or dual-paired, and S8's two halves are each other's duals,
so **the register set is swap-closed by construction** provided both S8 halves are constructors.

**(ii) The 7 rules transfer; the `↓`-binder soundness hazard does not arise.**
`necessitation`, `temporal_necessitation` and `temporal_duality` are all empty-context rules over
a validity notion that quantifies `v` universally, and every register clause maps a point to a
point. So all three are sound over register-containing formulas. The classical hybrid hazard is
*uniform substitution*, and it does not bite here for two independent reasons: TM⁺ already is not
substitution-closed (`atom_stab`), and no argument in this plan uses substitution — as the task
requires. `⊡`-necessitation stays derived (`necessitation` then `box_stab`), so the 7-rule mirror
is exact and `StarDerivationTree` can be a constructor-for-constructor copy of
`PlusDerivationTree` with `StarAxiom` in the `axiom` rule.

**Naming.** Settle on **`StarAxiom.ofBase`**. `ofTM` is already taken one level down for a
*different* embedding (`PlusAxiom.ofTM : Axiom φ → PlusAxiom (ofFormula φ)`); reusing the
spelling for `PlusAxiom φ → StarAxiom (ofPlus φ)` would make any composed reference ambiguous
about which system is being embedded. `ofBase` names the system directly below L⋆, and the
collision with `FrameClass.Base` is harmless (different namespace, different type). Note C26
forbids snake_case `def`/`abbrev` names, so all new definitions must be camelCase.

**`IsPureFuture` / `IsPurePast` on `StarFormula`.** Required by the two pasting schemata.
Recommendation: mirror the `PlusFormula` inductive (`Formula.lean:299-308`) with **no register
arms at all** — a register makes a formula impure. This is sound-by-construction, keeps
`ofPlus` purity-preserving (so the `ofBase` arm typechecks), and costs nothing downstream.
A `timeStore` arm (`IsPureFuture φ → IsPureFuture (↑ⁱφ)`) is semantically defensible — `↑ⁱ`
changes only the vector, not the `τ`-dependence — but requires re-proving the pasting validity
over `StarTruthAt` and buys nothing in Phases 2–4. A `timeRecall` arm is **unsound**: `↓ⁱφ` with
`v i < x` reads the past.

### Conservativity

**The semantic route is blocked exactly as the dispatch says.** `Conservativity/Plus/Forward.lean`
runs *star soundness → truth transfer → base completeness*. One level up that reads
*TM⋆ soundness → `starValidOnFrames_ofPlus` → **TM⁺ completeness***, and general nondeterministic
TM⁺ completeness is OPEN at every class (`Conservativity/Plus/README.md` metatheory table;
`docs/theorem-index.md` §"TM⁺ over the deterministic frames").

**Route (a), a register-eliminating translation: both natural candidates provably fail.**

1. *Naive erasure* (delete every `↑ⁱ`/`↓ⁱ`). The dispatch's suspicion is **confirmed**:
   **[checked]** `StarValid (↑¹G↓¹p → p)` — by seriality, `↑¹G↓¹p` is `↑¹p`, and `p` is an atom
   so `↑¹p ↔ p` — while **[checked]** `¬ StarValid (Gp → p)`, refuted over `NF` at
   `τ = (s ↦ if s ≤ 0 then 1 else 0)`, `x = 0`. Erasure sends a TM⋆-valid formula to a
   TM⁺-non-theorem, so it is not a translation of the required kind.
   *(Sharpening the dispatch's phrasing: `↑ⁱG↓ⁱφ → φ` is valid only when `i` is not free in `φ`
   — at `φ := ↓ⁱp` it fails, since `↑ⁱG↓ⁱφ ↔ ↑ⁱφ`, not `φ`. The atomic instance used above is
   valid and is all the refutation needs.)*
2. *Register collapse* (interpret every register as always holding the present time, i.e.
   `↑ⁱφ ↦ φ*`, `↓ⁱφ ↦ φ*`). Every register schema S1–S7, S9, S10 maps to a TM⁺ tautology, but
   **the rigidity schema S8 maps to `φ* → Gφ*`**, which is not a TM⁺ theorem (it is not even
   valid). Collapse fails on the one schema that carries the registers' expressive power.

A proof-normalization or `↓`-free normal-form route would have to come from the hybrid
literature, and §"External Resources" records why the standard apparatus is unavailable: it
needs nominals, which L⋆ does not have.

**Route (b), an explicit separating witness: provably as hard as refuting TM⁺ completeness.**
This is the report's main structural result, and it is machine-checked:

> **[checked]** `plus_of_starValidIn`: if every `PlusValidIn fc` formula is TM⁺-derivable, then
> `StarValidIn fc (ofPlus φ) → PlusDerivable fc [] φ`.
> **[checked]** `incompleteness_of_nonconservativity`: if `ofPlus φ` is `StarValidIn fc` and
> `φ` is not TM⁺-derivable, then TM⁺ is *incomplete* at `fc`.

Composed with TM⋆ soundness (Phase 2), this says: **any separating witness for
non-conservativity is, verbatim, a witness of TM⁺ incompleteness**, and conversely TM⁺
completeness implies conservativity. The question is therefore *sandwiched inside* the tree's
recorded open problem. This is a positive, publishable finding — it explains the failure rather
than reporting one — and it is exactly what Phase 4 should state.

**What Phase 4 lands unconditionally, and it is stronger than the dispatch's fallback.** The
dispatch describes conservativity of TM⋆ over TM on the `ofPlus ∘ ofFormula` fragment as a
"strictly weaker fallback". It is in fact a **two-directional** conservative-extension theorem,
because the backward half composes for free:

- forward **[checked]** (`tm_of_starValidIn`): `StarValidIn fc (ofPlus (ofFormula φ))
  → PlusValidIn fc (ofFormula φ) → ValidIn fc φ → Derivable fc [] φ`, via
  `starValidOnFrames_ofPlus`, `plusValidIn_ofFormula_iff`, and the `WeakCompleteness` engine.
  With Phase 2's soundness in front: `⊢⋆[fc] ofPlus (ofFormula φ) ⟹ ⊢[fc] φ`. **No TM⁺
  completeness needed.**
- backward: `⊢[fc] φ ⟹ ⊢⁺[fc] ofFormula φ` (`plusDerivable_of_derivable`, landed)
  `⟹ ⊢⋆[fc] ofPlus (ofFormula φ)` (Phase 3's embedding).

So Phase 4's headline is `starDerivable_ofFormula_iff` at all four classes — the **L ⊂ L⋆ row**,
the exact analogue of `plusDerivable_ofFormula_iff`. It should be stated as the deliverable, with
the conditional/contrapositive TM⁺ pair stated alongside as the honest account of the L⁺ ⊂ L⋆ row.

### Completeness reachability: NOT reachable, obstruction named

**The engine-level obstruction, and it is sharper than the L⁺ one.** The tree records that the
countermodels of all four TM completeness engines are deterministic, so `⊡` collapses to the
identity on them. For L⋆ the obstruction becomes a flat impossibility rather than a mismatch:

- `sentDet φ` is valid on **every** deterministic frame (`sentDet_of_deterministic`,
  `Semantics/StarDeterminism.lean`);
- `sentDet (ofPlus p)` is **not** `StarValid` (`refute_sentDet`, `not_starValid_sentDet`);
- so TM⋆ completeness at any class requires a task-frame model of `¬ sentDet p`, and **no
  deterministic model can ever be one**.

Hence not one of the four existing engines can be reused, narrowed, or adapted: a genuinely
nondeterministic canonical construction is required, and that is precisely the open TM⁺
problem one level down. Note this is *strictly worse* than the L⁺ situation: registers do **not**
collapse on deterministic frames (`↓ⁱ` still moves the time), so the "narrow to the deterministic
class" escape that produced `Metalogic/Deterministic/Completeness.lean` for TM⁺ + *Determined*
has no L⋆ analogue that would decide the general question — it would decide only the logic of
the deterministic frames, where `sentDet` is a theorem-candidate.

**The literature obstruction.** L⋆'s registers are Goranko's reference pointers, and SEP records
that reference-pointer temporal logics are "usually undecidable" (Goranko 1996;
Areces & ten Cate 2007). Axiomatizability is a separate matter from decidability, and the
standard hybrid route to it — Blackburn–de Rijke–Venema §7.3's pure-axiom completeness via the
non-orthodox PASTE rule — **cannot be stated in L⋆ at all**, because a pure formula is one whose
only atoms are nominals and L⋆ has no nominals. Reynolds (2003) and Zanardo (1991), the nearest
results already cited for the TM⁺ row, do not reach the all-histories semantics and so do not
reach L⋆ either.

**Verdict: record TM⋆ completeness as OPEN with the two obstructions above named, and carry no
Phase 5.** This is a well-evidenced "not reachable by this route", not a bare "open".

### Recommendations

Phase decomposition, each phase one agent run, `lake build` green, no new `sorry`:

- **Phase 1 — `StarLanguage/Axioms.lean` + `swapTemporal`.** `StarFormula.swapTemporal` with the
  two register arms and its involution/`ofPlus` pins; `IsPureFuture`/`IsPurePast` with no
  register arms; `RegFree`; the `StarAxiom` inductive: one `ofBase (φ : PlusFormula) (ax :
  PlusAxiom φ) : StarAxiom (ofPlus φ)` constructor, `modal_future` re-declared with the `RegFree`
  side condition, and the register schemata S1–S10 (both S8 halves). `StarAxiom.minFrameClass`
  routes `ofBase ax ↦ ax.minFrameClass` and every register schema to `.Base`. Size: ~250 lines.
  Note that `ofBase` already supplies MF at `RegFree` instances, so re-declaring `modal_future`
  is optional — **recommend omitting it in Phase 1** and adding it only if a later phase needs
  MF at a `RegFree` formula outside `ofPlus`'s image.
- **Phase 2 — `Metalogic/Conservativity/Star/StarSoundness.lean` (+ `StarAxiomValidity.lean`).**
  This is the phase the `ofBase` design exists to shrink. With `ofBase`, the entire TM⁺ axiom
  block is discharged by `plusAxiom_validIn_min` / `plusAxiom_swap_validIn_min` composed with
  `starValidOnFrames_ofPlus` — **two lines, no re-proof of 45 schemata**. Only the ~11 register
  arms need validity + swap-validity proofs, and every one of them is in the ACCEPT table above
  with its proof shape. Then the companion recursion mirrors `plus_derivable_valid_and_swap_validIn`
  arm for arm. Size: ~300 lines. **Do not attempt an L⋆ atomization** — the module docstrings
  and this report both establish it cannot exist.
- **Phase 3 — the embedding.** `StarDerivationTree.ofPlusTree : PlusDerivationTree fc Γ φ →
  StarDerivationTree fc (ofStarCtx Γ) (ofPlus φ)`, seven cases, the `axiom` case being `ofBase`
  and the `temporal_duality` case transporting along `ofPlus_swapTemporal`. Verbatim the shape
  of `PlusDerivationTree.ofTM`. Size: ~120 lines.
- **Phase 4 — conservativity.** (a) `starDerivable_ofFormula_iff` at all four classes, both
  directions, unconditional — the L ⊂ L⋆ row; (b) `starConservative_of_plusComplete`, the
  conditional TM⁺ row; (c) `plusIncomplete_of_starNonconservative`, its unconditional
  contrapositive. The three semantic chains are already machine-checked (see the summary), so
  this phase is composition plus documentation. Size: ~200 lines.
- **Phase 5 — none.** Record TM⋆ completeness as OPEN in `StarLanguage/README.md` and the
  `Metalogic` README with both obstructions named and SEP §7.1 / BdRV §7.3 / Goranko 1996 /
  Reynolds 2003 / Zanardo 1991 cited.

**Zero-`sorry` compliance.** Nothing above is deferred with a stub. The two results that cannot
be proved (TM⁺-conservativity, TM⋆ completeness) are delivered as *reasoned exclusions with
their obstruction stated as a theorem* — (b) and (c) of Phase 4 are the machine-checked content
of the exclusion, which is why this is not a shortfall.

## Decisions

1. **`StarAxiom.ofBase`**, not `ofTM` — `ofTM` is occupied one level down for a different
   embedding.
2. **`ofBase` embedding over verbatim re-declaration of the 45 TM schemata.** Re-declaration
   would force ~45 direct validity + swap-validity proofs over `StarTruthAt` (atomization being
   unavailable), for no gain in any Phase 1–4 deliverable. Recorded cost: the TM temporal
   schemata are then available only at register-free instances. If a later development needs
   e.g. `G(↓¹p → ↓¹q) → (G↓¹p → G↓¹q)` as an axiom, it is a schema-by-schema addition, and the
   register-formula instances of the BX schemata *are* valid (they are order-theoretic in the
   parameters); only the labour was declined, not the mathematics.
3. **MF carries a `RegFree` side condition** (or is omitted entirely in favour of `ofBase`) —
   forced by the machine-checked refutation.
4. **`IsPureFuture`/`IsPurePast` exclude both registers.**
5. **Phase 4 states three theorems**, not one: the unconditional L ⊂ L⋆ biconditional, the
   conditional L⁺ ⊂ L⋆ row, and the incompleteness contrapositive.
6. **No Phase 5.**

## Risks & Mitigations

| Risk | Mitigation |
|---|---|
| The `ofBase` design is judged too weak a "TM⋆" for the manuscript | Decision 2 records exactly what is declined and why, and the addition path is schema-by-schema; nothing is foreclosed. Raise with the user only if the plan wants the full re-declaration, which is a multi-phase cost. |
| `swapTemporal`'s register arms turn out to break some `ofBase` swap arm | The `ofBase` swap obligation is `swapTemporal (ofPlus φ) = ofPlus (φ.swapTemporal)`, which is `rfl`-shaped by the same argument as `ofFormula_swapTemporal`. Verify that pin first in Phase 1. |
| The coincidence lemma (S11) proves fiddlier than expected | It is not on the critical path: `RegFree` (Decision 3) avoids it entirely for Phases 1–4. |
| `↓ⁱ⊡` converse direction turns out valid, weakening a rejection | Only the `↓ⁱ⊡ → ⊡↓ⁱ` direction is machine-checked; the report says so. Phase 1 should settle the converse before claiming non-commutation in a README. |
| Documentation drift: `StarLanguage/README.md` currently says the four names are "reserved, unbuilt" and TM⋆ is "**Excluded**" | Phase 1 must rewrite that section and the correspondence table's last row in the same commit that declares `StarAxiom`; C15/C24/C26 stay green. |
| C9 forbids task numbers under `FormalSystem/` | No new file may cite a task number; use declaration names and paper anchors. |

## Tactic Survey Results

| Goal | Tactic | Result | Premises/Config |
|------|--------|--------|-----------------|
| S3, S5, S5′, S6, S7, S9 (register/`□`/`⊡` commutation, K, self-duality) | `Iff.rfl` | success | none — definitional in `StarTruthAt` |
| S1, S2 (`↑ⁱ↓ⁱφ ↔ ↑ⁱφ`, `↓ⁱ↑ⁱφ ↔ ↓ⁱφ`) | `simp [StarTruthAt]` | success | `Function.update_self`, `Function.update_idem` reached by `simp` |
| S4 (`↑ⁱ↑ʲφ ↔ ↑ʲ↑ⁱφ`) | `simp only [StarTruthAt]` + `rcases eq_or_ne i j` + `Function.update_comm` | success | `Function.update_comm` |
| S8 (rigidity) | `rw [StarTruth.allFuture_iff]` / `allPast_iff` then `intro` | success | the clause lemmas |
| S10 (recall export) | `rw [and_iff, untl_iff, untl_iff, timeRecall_iff]` + `constructor` | success | `StarTruth.top_true` |
| `↑¹G↓¹p → p` valid | `StarValid.of_forall_total` + `exists_gt` + `Function.update_self` | success | `exists_gt` on `F.Duration` |
| MF refutation over `NF` | `intro h` + `h.apply_total` + explicit `natHist` witnesses | success | `natModel`, `natHist_isTotal`, `StarTruth.allFuture_iff` |
| `↑ⁱ↓ⁱφ ↔ φ` refutation | same shape | success | `natHist (s ↦ if s ≤ 0 then 0 else 1)` |
| `↓¹⊡p → ⊡↓¹p` refutation | same shape | success | `SameStateAt` witness by `simp` |
| `Gp → p` refutation | same shape | success | `not_le.mpr` |
| Phase-4 chains A/B and the contrapositive | direct term-mode composition | success | `starValidOnFrames_ofPlus`, `plusValidIn_ofFormula_iff`, `WeakCompleteness` |

`lean_multi_attempt`, `lean_state_search` and `lean_hammer_premise` were not needed: every goal
above is either definitional or a two-to-six line transcription of an existing `NF` refutation
in `Semantics/PlusNonValidities.lean`. No search tool hit a rate limit; no blocked tool was
called.

## Context Extension Recommendations

- **Topic**: hybrid/reference-pointer logic as it bears on this tree.
  **Gap**: `.claude/context/project/logic/domain/` has Kripke-semantics material but nothing on
  nominals, satisfaction operators, reference pointers, or the notation reversal between the
  manuscript's `↑`/`↓` and the hybrid-logic literature's `↓`/`@`. Every future L⋆ task will
  re-derive that bridge.
  **Recommendation**: add `.claude/context/project/logic/domain/hybrid-reference-pointers.md`
  carrying the notation bridge, the "L⋆ has no nominals" fact and its consequence for
  completeness technique, and the SEP §7.1 / BdRV §7.3 pointers.
- **Topic**: which soundness proofs in this tree depend on time-shift homogeneity.
  **Gap**: that `modal_future_valid` is the *sole* `timeShift` consumer in the schema block is
  the single fact that decides this task, and it is discoverable only by grepping
  `Metalogic/Soundness.lean`.
  **Recommendation**: record it in `FormalSystem/Metalogic/README.md` (or the Soundness module
  docstring) as a stated invariant, so the next language extension checks it first.

## Appendix

### Machine-checked statements

All statements marked **[checked]** were compiled with `lake env lean` against the live tree
(Lean v4.33.0-rc1, Mathlib `79d0395a`) in three throwaway modules, all `sorry`-free; the sources
are archived in the session scratchpad as `Scratch573.lean` (S1–S9),
`Scratch573b.lean` (the four refutations and `↑¹G↓¹p → p`), and `Scratch573c.lean` (S10 and the
three Phase-4 chains). They are **not** committed to the repository — they are Phase 0 evidence,
and Phases 1–4 will re-derive each statement in its proper module.

Headline signatures, verbatim:

```lean
theorem refute_modal_future (p : Atom) :
    ¬ NF.StarValidOn (.imp (.box (mfWitness p)) (.box (allFuture (mfWitness p))))
-- where  mfWitness p := StarFormula.imp (.timeRecall 1 (.atom p)) (.atom p)

theorem storeG_recall_valid (p : Atom) :
    StarValid (.imp (.timeStore 1 (allFuture (.timeRecall 1 (.atom p)))) (.atom p))

theorem refute_erasure (p : Atom) :
    ¬ StarValid (.imp (allFuture (.atom p)) (.atom p))

theorem incompleteness_of_nonconservativity {fc : FrameClass} (φ : PlusFormula)
    (hvalid : StarValidIn fc (ofPlus φ)) (hnd : ¬ PlusDerivable fc [] φ) :
    ¬ (∀ ψ : PlusFormula, PlusValidIn fc ψ → PlusDerivable fc [] ψ)
```

### Search queries and sources used

- Local corpus (`~/Projects/Literature/`): `sources/sep_temporal-logic/chunk_006{5,6,7}.md`
  (hybrid temporal logics: nominals, `@`, reference pointers, the decidability verdict);
  `sources/blackburn_2002/ch07_since-until-hybrid.md` (basic hybrid language, nominals,
  satisfaction operators, pure-axiom completeness via PASTE).
- No web search was performed; the two local sources cover every claim this report makes, and
  the Blackburn–ten Cate and Areces–Blackburn–Marx claims are explicitly flagged as unverified
  literature expectation rather than asserted.
- Codebase greps: `timeShift` in `Metalogic/Soundness.lean` (the MF finding); `swapTemporal` in
  `PlusLanguage/Formula.lean`; `IsPureFuture` inductive; `WeakCompleteness`;
  `plusValidIn_ofFormula_iff`; `natFrame`/`natModel`/`natHist`.
- Constraint checks consulted: `scripts/check-module-invariants.sh` header (C2, C3, C9, C14,
  C15, C24, C26).
