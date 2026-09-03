# Research Report: Axiomatizing the stability modal ⊡ and the completeness strategy for TM⋆

- **Task**: 535 - axiomatize_stability_modal_tm_star
- **Started**: 2026-09-03T18:05:00Z
- **Completed**: 2026-09-03T20:10:00Z
- **Effort**: ~2 hours (hard mode, single agent, `--lit`)
- **Dependencies**: None (task 533 depends on this task; task 537 is the Lean follow-up)
- **Sources/Inputs**:
  - Primary source: `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` (lines 1102-1175, 1418-1440, 3440-3500, 4105-4160)
  - Prior task artifact (read in full): `specs/533_l_and_lstar_metatheory_conservative_extension/reports/01_l-lstar-metatheory-conservative-extension.md` (Appendix A prototypes reused verbatim as Part A of the probes)
  - Repository (opened and read): `FormalSystem/Semantics/{TaskFrame,WorldHistory,PartialHistory,TaskModel,Truth}.lean`, `FormalSystem/ProofSystem/Axioms.lean`, `FormalSystem/Metalogic/Soundness.lean` (TD case, lines 1217-1330), `FormalSystem/Metalogic/BXCanonical/{Frame,Completeness,CompletenessDedekind}.lean`, `FormalSystem/Metalogic/Algebraic/FlowFrame.lean:140-160`, `FormalSystem/Metalogic/WeakCanonical/IntegerModel/ReynoldsBridge.lean:460-470`, `FormalSystem/Syntax/Atom.lean`, `specs/511_research_frame_correspondence_infrastructure/reports/02_probes.lean` (style exemplar)
  - Literature, read on disk under `~/Projects/Literature/sources/`: `thomason_1984/sec05_4-the-technical-side-of-historical-neces.md` (T×W, Kamp and neutral frames, AK0-AK13, Gabbay's rules, Ockhamist decidability remark); `reynolds_1992/sec02_3-irr.md`, `reynolds_1992/sec07_9-completeness.md`; `venema_1993/sec01_derivation-rules-as-anti-axioms-in-modal.md`, `venema_1993/sec09_92-conservativity.md` (Zanardo references [44]-[46]); `venema_2001/sec03_since-and-until.md` (Ockhamist open problem, lines 36-58); `reynolds-2003-ockhamist/chunk_0001-0008, chunk_0029.md`; `reynolds_2002_axioms_for_branching_time/chunk_0001-0006.md`; `gabbay_kurucz_wolter_zakharyaschev_2003_many_dimensional_modal_logics/` (grep across chunks; chunk_0351, 0361, 0392, 0405 read at the hit lines)
  - Web (Appendix C): Brown-Goranko 1999 JoLLI PDF (fetched, `pdftotext`, read at lines 40-70, 136-152, 1025-1050); SpringerLink and Semantic Scholar records for Zanardo 1991 (abstract not retrievable - see Adversarial Self-Verification)
  - Lean tooling: `lean_run_code` (five compile rounds) and `lake env lean` on the probes file (three rounds, final exit 0)
- **Artifacts**: this report; `specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean` (632 lines, 60 declarations, sorry-free, compiles from disk); `specs/535_axiomatize_stability_modal_tm_star/.return-meta.json`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `FormalSystem/Semantics/{TaskFrame,WorldHistory,Truth}.lean` (`TaskFrame.comp`, `TaskFrame.converse`, `WorldHistory.ofTotal`, `timeShift`), `FormalSystem/ProofSystem/Axioms.lean` (the 45-constructor TM⁺ schema), `FormalSystem/Metalogic/Soundness.lean` (`derivable_valid_and_swap_validIn`, the TD discharge pattern), the four completeness engines (`StrongCompleteness.lean:879/987/1101/775`) and their countermodel frames (`Algebraic/FlowFrame.lean`, `WeakCanonical/IntegerModel/ReynoldsBridge.lean`)
- **Downstream Dependents**: task 533's plan (L⋆ syntax, `StarAxiom`, soundness, conservativity), task 537 (TM⋆ completeness attempt and the non-definability theorem)
- **Alternative Paths**: bundled TM⋆ semantics (Findings §4.4) if full-class completeness is wanted at any price; deterministic-class completeness (Findings §7.3) as the honest partial result
- **Potential Extensions**: open-future/open-past operators (paper lines 1136-1146) need the same pasting lemma with a different agreement predicate

## Executive Summary

- **The naive ⊡-axiom set {K, Nec, T, 4, 5, `□φ→⊡φ`, `p→⊡p`} is incomplete for TM⋆ over task frames.** Three further principles are valid and machine-checked (probes C2, C3/C5, C4): the same-time pasting schema `⟐φ⁺ ∧ ⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻)`, the future pasting schema `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)` (hence `F⟐φ⁺ → ⟐Fφ⁺` and `⊡Gφ⁺ → G⊡φ⁺`), and their TD-mirrors, where `φ⁺` ranges over *pure-future* and `ψ⁻`, `α⁻` over *pure-past* formulas (syntactic side conditions, `IsPureFuture`/`IsPurePast` in the probes). They express the one structural fact about `⟨τ⟩_x` that the S5 axioms miss: histories through a state are the *product* of its possible pasts and possible futures (the Markov property of task frames). A paper argument (§2.4) shows the pasting schema is not derivable from the naive set plus TM⁺: it fails in "E-models" that validate every naive axiom and every rule.
- **The pure-future restriction is essential**, and so is the absence of any Ockhamist-style interaction: `G⊡p → ⊡Gp`, `⊡GPp → G⊡Pp`, `P⊡p → ⊡Pp` (the ⊡-analogue of Kamp's AK12 / Reynolds's HN) and `⊡p → □⊡p` are all refuted by compiled countermodels on `natFrame` over ℤ (probes D1-D5). The paper's "no ⊡/tense interaction in general" is therefore exactly right for arbitrary `φ` and exactly wrong for pure-future/pure-past `φ`.
- **`⊡φ` is a state formula in the strong sense** (probe E2, via a `StarFormula` time-shift lemma E1): its value at `(τ,t)` depends only on the world state `τ(t)`, not on `t`. This is the key engineering lever for task 533: every TM⁺ axiom schema instantiated over `StarFormula` is sound by *atomization* (replace each maximal `⊡χ` by a fresh state-valued atom and apply the landed TM⁺ `soundness`), so no per-axiom re-proof over `StarTruthAt` is needed. Task 533's report assumed the TM⁺ axioms transfer through `ofPlus`; that gives only the ⊡-free instances and is not enough (Findings §8.2).
- **Completeness of TM⋆ over the paper's (all-histories) semantics is research-grade and must not be planned as a normal phase.** (i) Every completeness engine in the tree builds a *deterministic* countermodel (`FlowFrame.lean:148` `WorldState := FamIdx × D`, `TaskRel p d q := p.1 = q.1 ∧ q.2 = p.2 + d`; `ReynoldsBridge.lean:464` `u = w + d`), on which `⊡` is the identity, so none of them can refute `¬⊡`-formulas and none transfers. (ii) The canonical model on ⊡-classes of MCSs needs a *Lifting Lemma* (every task-respecting sequence of classes carries a tense-coherent MCS labelling), which is exactly the closure that the pasting axioms approximate for pure formulas but not for mixed ones; and *Limit* is at risk on dense classes. (iii) The literature analogue - the *complete-tree* Ockhamist logic - was open from Burgess 1979 until Reynolds 2003, whose proof for the F/P language alone needs an IRR rule, an atomic-non-futurity rule, "banning" ideas and a trans-countable construction of over 100 pages; the S/U version was left as future work. Zanardo 1991 (S/U) and Zanardo 1985 axiomatize only the *bundled* semantics, with Burgess-Gabbay rules. Reynolds 1992's IRR-free technique rests on Doets' theorem for linear orders and has no branching analogue.
- **Decidability: open, and at least as hard as TM⁺'s open decidability** (TM⋆ decidable ⇒ TM⁺ decidable via the provable forward conservativity). No undecidability follows from the product-logic results: TM⋆'s abstraction is `Lin × S5` with a refining equivalence, and GKWZ prove `L × S5` decidable (2EXPTIME) for `L ∈ {K4.3, Log(ℚ,<), Lin, ...}` and `PTL × S5` decidable; the undecidability theorems (`S5³`, any `L₁ × L₂ × L₃` between K4 and S5) need three independent product dimensions, which ⊡ is not. Task 537 must not promise decidability either way.
- **Binding engineering recommendations for task 533**: (a) `StarAxiom` is a *closed* inductive whose TM⁺ part re-declares the schemata with `StarFormula` parameters and whose ⊡ part is {SK, ST, S4, S5, MS, AS, PS, US} plus the necessitation rule; soundness is one lemma per constructor, the TM⁺ arm discharged once by atomization; (b) the TD/swap case is discharged *semantically* via a `StarFormula` twin of `TruthAntiIso` (the `stab` case is trivial because `swapTemporal` fixes `stab` and time reversal preserves `∼_t`), never proof-theoretically (the TM⁺ axiom set is not mirror-closed, so the proof-theoretic route is circular); (c) the completeness deliverable of task 537 is restated as: TM⋆ + *Determined* is complete over deterministic task frames (provable now from the engines), plus a gated spike on the Lifting Lemma.
- **Non-definability of ⊡ in L⁺** (deliverable 3): the right invariance notion is already in the tree as `TruthCorr` (`Truth.lean:604`): a relation on histories with atom harmony and total-history forth/back. Two models are given (§6) that are `TruthCorr`-related at `(const u, 0)` yet differ on `⊡Fp` - a permissive two-state frame versus a three-state frame where state `u` has a unique history; `□Fp` is false in both. Ready for transcription.

## Context & Scope

Language L⋆ = L⁺ + `⊡` with the paper's semantics (line 1114): `M,τ,x ⊨ ⊡φ iff M,σ,x ⊨ φ for all σ ∈ ⟨τ⟩_x`, `⟨τ⟩_x := {σ ∈ H_F | σ(x) = τ(x)}` (line 1108). The repo transcription is `SameStateAt`/`StarTruthAt` (probes Part A, unchanged from task 533's prototype). Store/recall operators are out of scope (task 533 Decision 2).

Notation used below: `⟐ := ¬⊡¬`; `F := ⊤U`, `P := ⊤S`, `G := ¬F¬`, `H := ¬P¬`; `φ⁺` a pure-future formula (built from atoms, `⊥`, `→`, and arbitrary `□ψ`, `⊡ψ` by `U` only), `ψ⁻` a pure-past formula (same with `S`); "state formula" = a formula whose truth at `(τ,t)` depends on `τ(t)` only.

Constraints in force: research only; no changes under `FormalSystem/` or `Tests/`; probes file sorry-free; no task numbers outside `specs/`.

Reference grounding: **Tier 1** (paper + Thomason, Reynolds, Venema, Zanardo, GKWZ), with the lemma-level mapping table in Findings §1.

## Findings

### 1. Reference grounding (H3, Tier 1) - lemma-level mapping table

| Source | Prop/Location | Lean Identifier (probes file unless noted) | Type Signature | Status |
|---|---|---|---|---|
| JPL paper | line 1108 `⟨τ⟩_x` | `SameStateAt` | `(τ σ : WorldHistory F) (t : F.Duration) : Prop` | compiled (Part A) |
| JPL paper | line 1114 `($\Stability$)` | `StarTruthAt … (.stab φ)` | `∀ σ, σ.IsTotal → SameStateAt τ σ t → StarTruthAt M σ t φ` | compiled |
| JPL paper | line 1118 footnote "monomodal logic of ⊡ is S5" | `of_stab`, `stab_four`, `stab_five` | T/4/5 at total `τ` | compiled (A2-A4) |
| JPL paper | line 1119 footnote `φ → ⊡φ` non-temporal | `stab_atom_of_atom` (atoms); Boolean/□/⊡ closure by S5 "fully modalized" derivation (§2.2) | `StarTruthAt M τ t (.atom p) → StarTruthAt M τ t (.stab (.atom p))` | compiled (A5); closure paper-derived |
| JPL paper | `⟨τ⟩_x ⊆ H_F` (line 1108) | `stab_of_box` | `… (.box φ) → … (.stab φ)` | compiled (A1) |
| JPL paper | line 1121 `⟐φ := ¬⊡¬φ` | `StarFormula.dstab`, `dstab_iff` | `… (dstab φ) ↔ ∃ σ, σ.IsTotal ∧ SameStateAt τ σ t ∧ …` | compiled |
| JPL paper | lines 1125-1129 Will/will/Could/could | `allFuture`, `someFuture` under `stab`/`dstab` | derived operators | compiled (used by C4, D2-D4) |
| JPL paper | `lem:deterministic-singleton` (line 3441), `app:deterministic` (3474) | `refute_determined` (non-deterministic half, `natFrame` shape); deterministic half = `stab_congr_sameState` + singleton class | `¬ StarValid (Fp → ⊡Fp)` | compiled (D4); deterministic half not needed as a probe |
| JPL paper | `def:frame` Compositionality / converse convention (`TaskFrame.lean:629-696`) | `paste_rel_le_lt`, `paste_rel`, `paste` | pasting of two total histories at a shared state is a total history | compiled (C0) - uses `F.comp` and `F.converse` only |
| Thomason 1984 §4 Def. 6 (T×W frames, condition (2) backward closure), (AK12) `□Pφ → P□φ`, (AK13) `□p ∨ □¬p` for atoms | `refute_somePast_stab` (⊡ lacks backward closure); `stab_atom_of_atom` (AK13 analogue) | `¬ StarValid (P⊡p → ⊡Pp)` | compiled (D5) |
| Thomason 1984 §4, formulas (19) `□G◇Fp → ◇GFp` (Burgess) and (20): valid on complete trees, not on Kamp/bundled frames; Gurevich-Shelah decidability; "Gabbay's completeness techniques do not seem to extend to the treelike case" | - (no repo target) | - | grounding for §4.4 (bundled vs complete) |
| Reynolds 2003 §3 (`chunk_0007-0008`): bundled system `⊢_B` = L1-L4 + S5(□) + HN + MB + IRR rule + ANF rule (`p → □p` for atoms) + "no substitution rule as it is not valid" | `stab_atom_of_atom` (= ANF); the `IsPureFuture` side condition plays the role substitution-closure cannot | - | grounding for §3 |
| Reynolds 2003 §1 (`chunk_0003-0004`): complete axiom system for Prior's (complete-tree) Ockhamist logic, F/P only, "banning" ideas, trans-countable construction, >100 pages; S/U extension = future work | - | - | grounding for §3, §4 |
| Reynolds 1992 §3 (`sec02_3-irr.md`): IRR's role = naming points; IRR-free route = Burgess-Xu strong completeness + Prior-U/S + Sep + Doets' theorem | - (the repo's `completeness_dedekind` already follows it) | - | grounding for §3.2 |
| Venema 1993 §1, §9.2: non-ξ rules as anti-axioms; "Zanardo [45] for branching-time"; Zanardo [46] replaced Burgess's IRR by infinitely many axioms | - | - | grounding for §3 |
| Venema 2001 §4 lines 36-58: "outstanding open problem to find an explicit axiomatization for the Ockhamist tree logic"; S/U extension noted | - | - | grounding |
| Brown-Goranko 1999 (JoLLI, web): Zanardo 1985 (bundle trees, F/P) and Zanardo 1991 (bundle trees, Since-Until) axiomatize the *bundle* semantics; T×W finitely axiomatized by von Kutschera 1997 with a Gabbay-style rule and by Di Maio-Zanardo 1996 without such a rule but with infinitely many axioms; "Burgess-Gabbay style rules … Zanardo 1991, 1996" | - | - | second-hand for Zanardo 1991 (abstract itself not retrieved) |
| GKWZ 2003 Thm 6.61/6.69 (`chunk_0351`, `0361`): `L × S5` decidable in 2EXPTIME for `L ∈ {K4.3, Log(ℚ,<), Lin, Log_pp(ℚ)}`; Thm 6.68: `PTL × S5`, `Log(ℕ,<) × S5` decidable; Thm 8.22 (`chunk_0405`): `L₁ × L₂ × L₃` undecidable for `K4 ⊆ Lᵢ ⊆ S5`; `S5ⁿ` undecidable for `n ≥ 3` (`chunk_0392`) | - | - | grounding for §5 |
| Repo: `multiFamTaskFrameGen` (`FlowFrame.lean:145-160`), `zTaskFrameV2` (`ReynoldsBridge.lean:464-470`) | the countermodel frames of all four engines are deterministic | `TaskRel p d q := p.1 = q.1 ∧ q.2 = p.2 + d`; `u = w + d` | read (load-bearing for §4.1, §7.3) |
| Repo: `TruthCorr` (`Truth.lean:604`), `truthAt_of_truthCorr` | the L⁺-invariance notion for deliverable 3 | `Rel : WorldHistory F → WorldHistory F' → Prop`, `atom`, `total_fwd`, `total_bwd` | read (load-bearing for §6) |
| Repo: `derivable_valid_and_swap_validIn` (`Soundness.lean:1217`), `TruthAntiIso` (`Truth.lean:1092`) | the TD discharge pattern to mirror for L⋆ | companion recursion carrying `ValidIn fc φ ∧ ValidIn fc φ.swapTemporal` | read (load-bearing for §8.3) |

Reference-grounding notes. The `reynolds-2003-ockhamist` chunks are OCR of a scanned conference paper: modal symbols are dropped, so axiom HN's exact orientation is unreadable (`chunk_0008.md:4`); the report only uses the fact that HN is the single tense/□ interaction axiom, which the surrounding text states. Zanardo 1991 is paywalled; SpringerLink (303 to an auth wall), PhilPapers (403) and Semantic Scholar ("abstract elided") were all tried; every Zanardo claim below is second-hand from Reynolds 2003, Venema 1993, Venema 2001 or Brown-Goranko 1999 and is marked as such.

### 2. Question 1 - the ⊡-axiom inventory (deliverable 1)

#### 2.1 Validated, refuted and unverified candidates

All probe identifiers refer to `probes/01_stab-axiom-probes.lean`; "compiled" means the file compiles from disk with `lake env lean` (exit 0, sorry-free).

| # | Candidate | Verdict | Evidence |
|---|---|---|---|
| SK | `⊡(φ→ψ) → (⊡φ→⊡ψ)` | valid | universal-quantifier shape of `StarTruthAt … (.stab _)`; K is immediate (no probe needed; same as task 533) |
| SN | from `⊢ φ` infer `⊢ ⊡φ` | sound | same |
| ST | `⊡φ → φ` | valid | A2 `of_stab` (needs `τ.IsTotal`) |
| S4 | `⊡φ → ⊡⊡φ` | valid | A3 `stab_four` |
| S5 | `¬⊡φ → ⊡¬⊡φ` | valid | A4 `stab_five` |
| MS | `□φ → ⊡φ` | valid | A1 `stab_of_box` |
| AS | `p → ⊡p` (atoms) | valid | A5 `stab_atom_of_atom` |
| - | `⊡φ` is a state formula at fixed `t` | valid | B1 `stab_congr_sameState` |
| - | `□⊡φ ↔ □φ`, `□φ → ⊡□φ` | valid, derivable (K, T(⊡), 4(□), MS) | B2 `box_stab_iff`, B3 `stab_box_of_box` |
| - | `⊡φ` depends on the world state alone (any two times) | valid | E2 `stab_state_only` via E1 `starTruthAt_timeShift` |
| **PS** | `⟐φ⁺ ∧ ⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻)` | **valid, new** | C2 `paste_valid` |
| **US** | `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)` | **valid, new** | C5 `untl_dstab_valid` |
| FS | `F⟐φ⁺ → ⟐Fφ⁺` | valid (= US at `α⁻ := ⊤`) | C3 `future_dstab_valid` |
| GS | `⊡Gφ⁺ → G⊡φ⁺` | valid (= contrapositive of FS with `¬φ⁺` pure-future) | C4 `stab_allFuture_valid` |
| SS, PS-mirror | `(α⁺ S ⟐ψ⁻) → ⟐(α⁺ S ψ⁻)`, `P⟐ψ⁻ → ⟐Pψ⁻`, `⊡Hψ⁻ → H⊡ψ⁻` | valid by TD from US/FS/GS (`swapTemporal` exchanges `IsPureFuture` and `IsPurePast`) | not separately probed; the swap argument is mechanical (UNVERIFIED as a compiled statement) |
| - | `⊡φ → □⊡φ` | **refuted** | D1 `refute_stab_box` |
| - | `G⊡p → ⊡Gp` | **refuted** (even for atoms) | D2 `refute_allFuture_stab` |
| - | `⊡GPp → G⊡Pp` | **refuted** (GS needs the pure-future restriction) | D3 `refute_stab_allFuture_past` |
| - | *Determined* `Fp → ⊡Fp` | **refuted** over non-deterministic frames | D4 `refute_determined` |
| - | `P⊡p → ⊡Pp` (⊡-analogue of AK12/HN) | **refuted** | D5 `refute_somePast_stab` |
| - | `⟐F⟐φ → ⟐Fφ` for arbitrary `φ` | refuted on paper (3-state DAG frame over ℤ, `φ := Pq`; §2.3) | UNVERIFIED by probe - needs a non-permissive frame, not built |
| - | `⟐F⟐φ⁺ → ⟐Fφ⁺` for pure-future `φ⁺` | valid on paper (two pastings) and derivable from US + S5 | UNVERIFIED by probe; derivability is a paper argument |
| - | any ⊡/MF interaction beyond the derivable `□⊡φ ↔ □φ`, `□Gφ ↔ G□φ` family | none found | `□ψ` is constant across all `(τ,t)` (E1 + `box` clause), so every `□`-prefixed ⊡-formula collapses to a `□`-formula; nothing new arises |

Reading of the table: the naive set is exactly the *fusion* S5(⊡) ⊕ TM⁺ plus the two bridge axioms MS and AS; it knows that `∼_t` is an equivalence contained in the universal relation and respected by atoms, and nothing else. The frame-derived content of `⟨τ⟩_x` that it misses is the pasting property, which is what PS and US add.

#### 2.2 Why the naive set is complete for the tense-free fragment (and only there)

For `φ` in the fragment `{p, ⊥, →, □, ⊡}`, `⊢ φ ↔ ⊡φ` is derivable from the naive set: atoms by AS + ST; `⊥` trivially; `□ψ` by 4(□) + MS; `⊡ψ` by S4; implications because every formula of the fragment is provably equivalent to a Boolean combination of `⊡`-formulas, and S5 proves `α → ⊡α` for fully modalized `α`. So `⊡` collapses to the identity on this fragment, matching the paper's footnote (line 1119), and completeness of the fragment reduces to S5(□), which the TM⁺ engines already deliver. This is a paper derivation (Medium confidence); it is not load-bearing for any recommendation.

#### 2.3 The pasting property and its consequences (the new principles)

Probe C0 (`paste`) shows: if `ρ` and `σ` are total histories with `ρ(t) = σ(t)`, then `ρ|(-∞,t] ⌢ σ|(t,∞)` is a total history, using only *Compositionality* (`TaskFrame.comp`) across `t` and the converse convention (`TaskFrame.converse`) for the reverse orientation. No Saturation, no extension theorem, no frame-class assumption. Hence, for every state `w` of any task frame, `{σ ∈ H_F | σ(t) = w} = Past_t(w) × Future_t(w)`.

Pure-future formulas see only `σ|[t,∞)` (C1a `truth_congr_agreeFrom`) and pure-past formulas only `σ|(-∞,t]` (C1b); `□ψ` and `⊡ψ` are admitted inside both because `□ψ` is history-independent and `⊡ψ` depends on `σ(t)` only (B1). The three validities follow:

- PS (C2): witnesses `σ` (for `φ⁺`) and `ρ` (for `ψ⁻`) in `⟨τ⟩_t` paste to `ρ ⌢ σ ∈ ⟨τ⟩_t` satisfying both.
- US (C3, C5): a witness `ρ ∈ ⟨τ⟩_y` for `φ⁺` at a future time `y` pastes with `τ` to `τ ⌢_y ρ ∈ ⟨τ⟩_t`, which still satisfies the pure-past guard `α⁻` on `(t,y)` and `φ⁺` at `y`.
- GS (C4): the contrapositive.

Why the restriction is necessary: with `φ := Pq` the pasted history `τ ⌢_y ρ` has `τ`'s past, not `ρ`'s, so `Pq` can flip - this is D3. With `φ := Fp` in `G⊡p → ⊡Gp` the direction is simply wrong - D2. Both countermodels live on the permissive `natFrame` over ℤ, where every `ℤ → ℕ` is a history; the paper-only refutation of `⟐F⟐Pq → ⟐FPq` needs a frame where state `a`'s past is forced (`R = {a→a, a→c, b→b, b→c, c→c}` with `R∘R = R`, `q` at `b`), which is why it is left UNVERIFIED.

#### 2.4 Independence of PS from the naive set plus TM⁺ (paper argument, Medium-High)

Define an *E-model* as a task model `M` over a disjoint-lines frame (`multiFamTaskFrameGen`, `FlowFrame.lean:145`) together with a family `E_t` of equivalence relations on total histories with `E_t ⊆ ∼_t`, and interpret `⊡` by `E_t` instead of `∼_t`. Every naive axiom is valid in every E-model (S5 because `E_t` is an equivalence; MS because `E_t` is contained in the universal relation; AS because `E_t ⊆ ∼_t`), and every TM⁺ schema instance over L⋆ is valid because on a disjoint-lines frame each `(σ,t)` *is* a world state, so `⊡_E χ` is a state formula and atomization (§8.2) reduces the instance to an L⁺ instance, valid by the landed `soundness`. The rules MP, Nec(□), Nec(⊡), temporal necessitation and weakening preserve E-validity, and the class of E-models is closed under the mirror construction used for TD. Now take two lines `τ`, `σ` over ℤ, `E_0 = {τ,σ}`-universal and `E_t` the identity for `t ≠ 0`, `p` true only at `(τ,1)`, `q` only at `(σ,-1)`, atoms equal at `(τ,0)`, `(σ,0)`. At `(τ,0)`: `⟐_E Fp` (via `τ`), `⟐_E Pq` (via `σ`), but `⟐_E(Fp ∧ Pq)` fails. Hence PS is not derivable from the naive set plus TM⁺ with all its rules, while it is valid in every task model (C2). **The naive axiomatization is incomplete.** Whether PS + US together are complete is open (§4).

### 3. Question 2 - orthodox or unorthodox rules?

#### 3.1 What the literature actually says (first-hand chunks)

- Thomason 1984 §4: for T×W validity Burgess remarked it is recursively axiomatizable "since it is essentially first-order", but a "reasonable axiomatization" was open; Gabbay's irreflexivity method gives Kamp-frame completeness with (AG1) + rule (RG2); "Gabbay's completeness techniques do not seem (at first glance, anyway) to extend to the treelike case"; Ockhamist validity is decidable (Gurevich-Shelah) but its axiomatization was open, with Burgess's 1979 proof challenged by Kripke.
- Reynolds 2003: the *bundled* system uses an IRR rule and the ANF rule; the *complete-tree* system (the analogue of the paper's all-histories semantics) needs in addition "banning" ideas and a trans-countable construction, proof of over 100 pages, F/P only; S/U left to future work.
- Reynolds 1992 §3: the whole point of IRR is naming points; without names, `U`/`S` are not definable from `F`/`P` and one needs the Burgess-Xu construction plus (for ℝ) Doets' theorem on monadic sentences of bounded quantifier depth over countable dense orders. That machinery is about *linear* flows.
- Venema 1993 §1 and §9.2: Zanardo [45] (= 1991) uses rules "styled after Gabbay's Irreflexivity Rule" for branching time; Zanardo [46] (= 1990, Peircean) replaced the rule by infinitely many axioms.
- Brown-Goranko 1999 (second-hand for Zanardo): Zanardo 1985/1991 axiomatize *bundle-tree* validity (F/P, then S/U); T×W validity has both a Gabbay-rule axiomatization (von Kutschera 1997) and a rule-free but infinite one (Di Maio-Zanardo 1996).

#### 3.2 Transfer analysis

The role of IRR in all of these is to give each point (or each history) a name so that a step-by-step construction can *refer back* to it. In TM⋆ the object that needs naming is the *world state* of an MCS: the ⊡-class. TM⁺ escaped this because the canonical model can be deterministic (§4.1) - there is nothing to name when every state lies on exactly one history. As soon as genuine branching is required (which `¬(φ → ⊡φ)`-consistent sets force), the construction must keep track of which MCSs share a state across different chronicles, and that is the classical IRR/ANF territory: Reynolds 2003 even keeps `p → □p` as a *rule* (ANF) because substitution is unsound for it, exactly as AS behaves here (`Fp → ⊡Fp` is not valid, D4).

Reynolds 1992's IRR-free route does not carry over: it replaces names by expressive completeness over *linear* orders (Doets), and there is no analogue for "which histories pass through which state". Di Maio-Zanardo's rule-free T×W axiomatization uses infinitely many axioms and backward-closed alternatives; ⊡ lacks backward closure (D5), so even that template does not apply as is.

**Verdict.** An orthodox finite Hilbert axiomatization of TM⋆ over the paper's semantics is *not* in reach from the literature: every complete branching-time system with S/U (Zanardo 1991, bundled) or with complete trees (Reynolds 2003, F/P) uses a Gabbay-style rule, and the paper's semantics is the complete-tree kind. The naive-plus-pasting set {SK, SN, ST, S4, S5, MS, AS, PS, US, mirrors} is the right *sound* orthodox core; if a completeness proof is ever attempted it should expect to add (at least) a state-naming rule of the form "from `⊢ (q ∧ ⊡q ∧ □H¬q ∧ □G¬q) → φ` infer `⊢ φ`, `q` fresh" - offered here as the natural candidate only, UNVERIFIED for soundness and untested.

### 4. Question 3 - the canonical model on ⊡-classes, per axiom and per class

#### 4.1 Decisive repo fact: all four engines are deterministic

`BXCanonical.completeness` (Base), `completeness_dense`, `completeness_dedekind` build their countermodel on `bundleFlowFrame`, i.e. `multiFamTaskFrameGen` with `WorldState := FamIdx × D` and `TaskRel p d q := p.1 = q.1 ∧ q.2 = p.2 + d` (`FlowFrame.lean:145-160`, cited by `BXCanonical/Completeness.lean:130-145`, `CompletenessDedekind.lean:78`); `completeness_discrete` goes through `zTaskFrameV2` with `WorldState := ℤ`, `TaskRel w d u := u = w + d`, documented as "deterministic" (`ReynoldsBridge.lean:464`). On every one of these frames each state lies on exactly one total history, so `⟨τ⟩_x = {τ}` and `⊡ = id`. Consequences: (i) they validate *Determined*, so they cannot refute any consistent set containing `¬(φ → ⊡φ)`; (ii) no existing engine can be reused for TM⋆ completeness by adding a `stab` case; (iii) they *do* deliver deterministic-class completeness (§7.3).

#### 4.2 The candidate construction and its obstruction

Design (from the task description): `W := MCS/≈` with `Γ ≈ Δ iff {⊡χ ∈ Γ} = {⊡χ ∈ Δ}` (an equivalence by S5; classes are the canonical `∼`-clusters), `[Γ] ⇒_d [Δ]` iff some canonical chronicle has a member of `[Γ]` at `s` and a member of `[Δ]` at `s + d`, valuation `[Γ] ⊨ p iff p ∈ Γ` (well defined by AS + ST), and the total histories of this frame are *all* `⇒`-respecting maps `D → W`.

Truth lemma for `⊡`: `⊡φ ∈ Γ` iff for every `σ ∈ H_F` through `[Γ]` at `x`, `φ` holds at `(σ,x)`. The right-to-left direction (`¬⊡φ ∈ Γ` gives `Δ ≈ Γ` with `¬φ ∈ Δ` by S5 canonicity, then a chronicle through `Δ`) is the Burgess-Xu construction applied to `Δ` and is fine. The left-to-right direction is the problem: `σ` may be a *pasted* class-sequence that is not the class-image of any single chronicle; for it the induction hypothesis says nothing unless `σ` can be *lifted* to a tense-coherent MCS sequence `Λ : D → MCS` with `Λ(t) ∈ σ(t)`.

**Lifting Lemma (the research obstruction, named precisely):** every `⇒`-respecting `σ : D → MCS/≈` admits `Λ : D → MCS` with `Λ(t) ∈ σ(t)` for all `t` and `Λ` a canonical chronicle (all `U`/`S` witness and guard conditions between all pairs). PS and US are exactly the pure-future/pure-past shadow of this lemma - they guarantee the needed MCS exists for any *pure* demand from either side - but a chronicle condition such as `FPq ∈ Λ(s)` is mixed, and nothing in PS/US forces a single MCS in `σ(t)` to satisfy simultaneously all mixed demands from all `Λ(s)`, `s ≠ t`. The lemma either needs (a) stronger axioms (mixed pasting schemata, whose validity would first have to be probed) or (b) a naming rule so that the construction never has to lift a sequence it did not itself build - the Reynolds 2003 "banning" pattern. This is the same obstruction as the complete-tree Ockhamist case, in the same place.

#### 4.3 The six `TaskFrame` axioms on the class frame (`TaskFrame.lean:629-696`)

| Axiom | Status on `W := MCS/≈`, `⇒` := chronicle-realized pairs | Notes |
|---|---|---|
| `nullity_identity` | provable | `[Γ] ⇒_0 [Δ]` iff some chronicle has members of both classes at the same time; a chronicle has one MCS per time, so `[Γ] = [Δ]` |
| `comp` (Compositional, both directions) | interpolation `→` provable (take the same chronicle's point at `s + x`); composition `←` **fails as defined** | two chronicles meeting in a class `[Θ]` at different MCSs do not paste into a chronicle; the fix (close `⇒` under composition) makes `H_F` contain exactly the sequences the Lifting Lemma must handle - the obstruction moves, it does not disappear |
| `converse` | provable by definition | orient `⇒_{-d}` by the converse convention |
| `serial` | provable | every MCS lies on a total chronicle in every engine |
| `limit` | **at risk on dense classes** | `⋂_{x>0}(w)_x = {w}` needs that no other class is reachable at arbitrarily small durations; nothing in the axioms prevents two classes being "infinitesimally close" along dense chronicles. Over ℤ (`.Discrete`) it holds by `limit_of_succOrder` given nullity |
| `saturation` | UNVERIFIED | `W` is uncountable; a directed family of nonempty fibres/segments must have nonempty intersection; a compactness argument over MCSs is plausible but not attempted |

#### 4.4 Per-class feasibility verdict

| Class | Engine and its countermodel | Verdict for TM⋆ (all-histories semantics) | Alternative |
|---|---|---|---|
| Base | `BXCanonical.completeness` on `bundleFlowFrame` (deterministic) | **BLOCKED** by the Lifting Lemma; engine unusable | deterministic-class completeness (§7.3) is provable now; bundled TM⋆ (below) is the tractable research target |
| Dense | `completeness_dense`, same frame | BLOCKED, plus *Limit* at risk on the class frame | same |
| Discrete | `completeness_discrete` via `zTaskFrameV2` (single ℤ-line) | BLOCKED by Lifting; *Limit* fine over ℤ; the ℤ setting is the most promising for a mosaic-style finite argument (`Saturation` from finiteness, `limit_of_succOrder`) | same; also the only class where a filtration/FMP route is thinkable, and the tree's FMP is itself only conditional (`BiLasso/Assembly.lean:86,111`) |
| Dedekind | `completeness_dedekind` (Doets route on ℝ) | BLOCKED; Doets' theorem is a linear-order result with no branching analogue; do not attempt | same |

Bundled TM⋆ (what Zanardo 1991 actually axiomatizes, transposed): models `(F, B, V)` with `B ⊆ H_F` a set of total histories closed under time shift and pasting, `□` and `⊡` quantifying over `B`. The canonical bundle is the set of class-images of chronicles closed under pasting; the Lifting Lemma is replaced by pasting-closure of the bundle, which PS/US-style axioms are designed to secure. This is a *different semantics* from the paper's (as bundled trees differ from complete trees - Thomason's (19), (20)), so it is not a deliverable of task 537 as stated; it is the honest fallback if any TM⋆ completeness at all is wanted, and it is where the naming-rule question would be settled first.

Mosaic/quasi-model route (Caleiro-Viganò-Volpe; Blackburn et al. §6.4-6.5): the natural tool for *decidability* of `S5 + linear tense` combinations, not for Hilbert completeness with a fixed axiom list; the tree has no mosaic infrastructure (task 434 is blocked on exactly this), so it does not do better than the canonical route for task 537's stated goal.

### 5. Question 4 - decidability

- TM⋆ decidable ⇒ TM⁺ decidable: `Derivable fc [] φ ↔ StarDerivable fc [] (ofFormula φ)` holds at all four classes (backward by `ofPlus`, forward by TM⋆ soundness + the engines, task 533 §5 and Appendix A `forward_star_of_sound`), so a decision procedure for TM⋆ decides TM⁺, whose decidability is open for every class (`README.md:200-215`, task 533 §2). TM⋆ is therefore at least as hard as an open problem.
- No undecidability follows from the product results. Abstractly, an L⋆ model is a `Lin × S5` product frame (`□` = "all histories at the same time") with an extra equivalence `∼_t ⊆` the S5 relation at each time and the pasting closure. GKWZ Thm 6.61/6.69: `L × S5` is decidable in 2EXPTIME for `L ∈ {K4.3, Log(ℚ,<), Lin, Log_pp(ℚ)}`; Thm 6.68: `PTL × S5` and `Log(ℕ,<) × S5` are decidable. The undecidability results (Thm 8.22: `L₁ × L₂ × L₃` for `K4 ⊆ Lᵢ ⊆ S5`; `S5³`) need three *independent* product dimensions; `⊡` refines the S5 dimension rather than adding one, and a reduction from a 3-D product would have to simulate an independent third coordinate with `∼_t`, which the pasting closure (`Past × Future`) actively obstructs. The task-frame constraints (duration *group*, `U`/`S` rather than `F`/`P`, Limit/Saturation) push in the harder direction and are what keep TM⁺ open.
- Ockhamist decidability (Gurevich-Shelah, via the monadic theory of trees with quantification over maximal chains) does not transfer either: task frames are not trees (histories re-merge), and their duration group is not a tree order.
- **Verdict**: open; not undecidable by any known reduction; not decidable by any known technique; strictly no easier than TM⁺. Tasks 533/537 must promise nothing here, and the report recommends the README's "open" row be extended to TM⋆ verbatim.

### 6. Question 5 - the bisimulation and the separating models (deliverable 3)

#### 6.1 The invariance notion

The right notion is already in the tree: `TruthCorr M M'` (`Truth.lean:604`): an order isomorphism of durations, a relation `Rel` on histories, atom harmony at every related pair and every time, and total-history forth/back (`total_fwd`, `total_bwd`). `truthAt_of_truthCorr` proves that every L⁺ formula is invariant under it, with the `□` case using forth/back and the `U`/`S` cases the order isomorphism. It is a *valuation-sequence* bisimulation: `Rel σ σ'` is intended for histories with the same atom profile `t ↦ {p | p ∈ V(σ(t))}`. Nothing in it mentions world states, which is precisely why `⊡` can escape it.

#### 6.2 Two models that `TruthCorr`-agree but differ on `⊡Fp`

Time ℤ (any `D` with `[SuccOrder]` works the same way).

- `M₁`: the permissive two-state frame `W₁ = {u, v}`, `w ⇒_d w'` iff `d ≠ 0 ∨ w = w'` (the `natFrame` shape, `TaskFrame.lean:1602`; every `ℤ → W₁` is a total history), `V(p) = {u}`.
- `M₂`: `W₂ = {u, u', v}` with `R = {u→u, u'→u', u'→v, v→v, v→u'}`, `w ⇒_0 w'` iff `w = w'`, `w ⇒_d w'` iff `R w w'` for `d > 0`, converse for `d < 0`; `V(p) = {u, u'}`. `R∘R = R`, so Compositionality holds; `R` is reflexive and every state has an `R`-predecessor, so Seriality holds; *Limit* by `limit_of_succOrder`; *Saturation* by `saturation_of_finite`. Total histories: `const u`, and all `ℤ → {u', v}`.
- `Rel σ σ'` iff `∀ s, p ∈ V(σ(s)) ↔ p ∈ V(σ'(s))` (for every atom; only `p` matters). Atom harmony holds by definition; `total_fwd`/`total_bwd` hold because both models realize exactly the atom profiles `ℤ → {p, ¬p}` (in `M₁` by any function, in `M₂` through `{u', v}`); `dur := id`.
- Hence `(const u, 0)` in `M₁` and `(const u, 0)` in `M₂` satisfy the same L⁺ formulas (`truthAt_of_truthCorr`).
- `⊡Fp` at `(const u, 0)`: in `M₂` the only history through `u` is `const u`, so `⊡Fp` is **true**; in `M₁` the history `u` up to `0`, `v` afterwards lies in `⟨const u⟩_0` and refutes `Fp`, so `⊡Fp` is **false**. `□Fp` is false in both (`const v` in `M₁`, `const v` in `M₂`). So `⊡Fp` is not equivalent to any L⁺ formula over task frames, and the separation is *temporal* as the task requires (`p ↔ ⊡p` for atoms rules out atomic separators).
- Transcription notes for task 537: `M₁` is `natFrame` with `Nat` cut down to two states or used as is (`V(p) = {0}`; the D-probes already do this); `M₂` needs a `FrameOver (TemporalOrder.of ℤ)` with `WorldState := Fin 3`, fields discharged by `comp_of` (R∘R = R by `decide`), `serial`, `limit_of_succOrder`, `saturation_of_finite`, `converse` by definition; the `TruthCorr` instance is ten lines; the `⊡Fp` evaluation is the D-probe pattern (`dstab_iff`/`allFuture_iff` style unfolding). The existing invariance theorem does the whole L⁺ half, so nothing about bisimulations needs to be developed.

### 7. Deliverable 4 - what the addition of ⊡ permits beyond task 533's TM⋆/TM⁺ result

#### 7.1 Composed rows

- L ⊂ L⋆ via `ofFormula ∘ tr`: backward `TM ⊢ φ ⟹ TM⋆ ⊢ ofFormula (tr φ)` composes `derivable_translate` with `ofPlus` at all four classes; forward inherits the L ⊂ L⁺ status (refuted at Base/Discrete, open at Dense/Dedekind) unchanged, because `Forward⋆` holds everywhere. No new mathematics.
- `TMFrag ⊂ TM⋆`: `TMFrag fc φ ↔ StarDerivable fc [] (ofFormula (tr φ))` is one line from `Forward⋆`/`ofPlus`; the ⊡-fragment logic `TM⋆ᴸ⁺ := {φ ∈ L⁺ | TM⋆ ⊢ ofFormula φ}` equals TM⁺ by the same two directions, so nothing new is "transferred back" - TM⋆ completeness would give TM⁺ completeness as a corollary, but the tree already has the latter.
- What TM⋆ completeness *would* add that nothing else gives: derivability of every valid mixed ⊡/tense principle (e.g. whether `⟐F⟐φ⁺ → ⟐Fφ⁺` follows from PS/US), and a semantic characterization of the defined modals. Since completeness is blocked, these stay semantic (probe-level) facts.

#### 7.2 The logic of the defined modals (sound facts, derivable from the extended set unless marked)

- `Will φ⁺ → G Will φ⁺` for pure-future `φ⁺`: from `⊡Gφ⁺ → ⊡GGφ⁺` (K(⊡) on `T4`) and GS applied to `Gφ⁺`. Persistence of *Will* is thus a theorem for pure-future content and (by D3's pattern) fails for mixed content.
- `Will φ → will φ` (`⊡Gφ → ⊡Fφ`) from TB (`F⊤`) under `⊡`.
- `will φ⁺ → G will φ⁺` is **not** valid (the witness may become past); `could φ⁺ ↔ ⟐Fφ⁺` and `F could φ⁺ → could φ⁺` (FS) is valid.
- `Will φ⁺ → □ Will φ⁺` is refuted (D1 pattern); `□Gφ → Will φ` (MS) and `Will φ → Gφ` (ST) are derivable; `Will` sits strictly between `□G` and `G`.
- *Determined* `φ → ⊡φ`: refuted on non-deterministic frames (D4, the paper's `app:deterministic` second half); over deterministic frames `⟨τ⟩_x = {τ}` (`lem:deterministic-singleton`) so every instance is valid and TM⋆ + Determined proves `φ ↔ ⊡φ`, `Will ↔ G`, `will ↔ F`, `Could ↔ G`, `could ↔ F`.

#### 7.3 A completeness result that is provable now: TM⋆ + Determined over deterministic frames

Let `Det` be the class of deterministic task frames (paper `def:deterministic`, line 3418). Claim: `StarValidDet φ → StarDerivable⁺ᴰ fc [] φ` where `⁺ᴰ` adds the *Determined* schema, at every class whose engine's countermodel is deterministic - i.e. all four (§4.1). Proof shape: (a) on deterministic frames `⊡ψ ↔ ψ` pointwise, so `φ ↔ erase φ` (erase = delete every `stab`) pointwise; (b) `StarValidDet φ` gives `ValidDet (erase φ)`; (c) the engine's countermodel for `erase φ` is deterministic, so `ValidDet (erase φ) → Valid_fc (erase φ)`-in-effect, i.e. the engine yields `Derivable fc [] (erase φ)` directly from a `Det`-restricted validity hypothesis (this needs the engine's statement to be re-read as "valid on `bundleFlowFrame`/`zTaskFrameV2` ⇒ derivable", which is what the proofs establish); (d) `ofPlus` lifts to `StarDerivable`, and Determined + ST give `⊢ φ ↔ erase φ` by induction. Steps (a), (b), (d) are routine; step (c) is a *re-statement* of the existing engines with a narrower hypothesis and should be checked against `bundleFlow_completeness_from_neg_membership` (`FlowFrame.lean:781`) before being promised. Marked Medium confidence; it is the one completeness theorem task 537 can honestly deliver.

### 8. Deliverable 5 - engineering recommendations binding on task 533's plan

#### 8.1 `StarAxiom`: closed inductive, one soundness lemma per constructor

Parameterizing `StarAxiom` over an axiom set (`StarAxiom (S : Set StarFormula)`) makes every downstream statement (`StarDerivable`, both conservativity directions, soundness) carry `S` and its soundness proof as parameters, buys nothing for the landed L⁺ code, and does not match `ProofSystem.Axiom`'s closed shape. Adding a constructor later costs one arm in `minFrameClass`, one arm in the soundness dispatch and one arm in the swap-validity dispatch - the same discipline the TM⁺ tree already follows (`axiom_validIn_min`/`axiom_swap_validIn_min`, `Soundness.lean:821,1190`). **Decision: closed inductive** with constructors `{ofPlus-schemata (§8.2), stab_k, stab_t, stab_4, stab_5, box_stab, atom_stab, paste, untl_paste}`, `minFrameClass := .Base` for every ⊡-constructor (all probes are class-free), and side-condition arguments `(hφ : IsPureFuture φ) (hψ : IsPurePast ψ)` on `paste`/`untl_paste` (the predicates as `inductive … : StarFormula → Prop`, exactly as in the probes; decidable instances are optional). The TD-mirrors `snce_paste` etc. need not be constructors: TD derives them, provided `IsPureFuture φ → IsPurePast φ.swapTemporal` is proved (one induction).

#### 8.2 The TM⁺ schemata must range over `StarFormula`; discharge them by atomization

Task 533's `ofPlus : Axiom φ → StarAxiom (ofFormula φ)` yields only ⊡-free instances of MF, the S5 axioms and BX. TM⋆ needs, e.g., `□⊡p → □G⊡p` (MF at `⊡p`), so the schemata must be re-declared with `StarFormula` parameters (45 constructors, mechanical; or a `StarAxiom.plus : PlusSchema → StarAxiom …` wrapper). Their soundness should **not** be re-proved axiom by axiom over `StarTruthAt`. Instead:

1. `starTruthAt_timeShift` (E1) and `stab_state_only` (E2) show every `⊡χ` is a function of the world state.
2. Define `atomize : StarFormula → Formula` replacing each maximal `⊡χ` by a fresh atom `q_χ`, using an injection `Atom ⊕ StarFormula ↪ Atom` (`Atom` is a `Countable`, `Infinite` structure, `Syntax/Atom.lean:75`; `nonempty_denumerable` gives the encoding classically, as the tree already does for `Formula`).
3. For a task model `M` build `M⁺` on the same frame with `valuation⁺ w (q_χ) := ⊡χ true at (any total history through w, any time)` - well defined by E2 and the extension theorem's existence of a history through `w` (or by choosing, for each `w`, the value at a fixed witness).
4. Prove `StarTruthAt M τ t φ ↔ TruthAt M⁺ τ t (atomize φ)` by induction (the `stab` case is E2 plus the definition of `valuation⁺`).
5. A TM⁺ schema instance `A[ψ₁,…,ψₙ]` over L⋆ then holds at `(τ,t)` in `M` iff the L⁺ instance `A[atomize ψ₁,…]` holds in `M⁺`, which is `axiom_validIn_min` applied to `M⁺`. One lemma covers all 45 constructors and all four classes (`M⁺` lives on `M`'s frame, so `FrameClass.Sat` is inherited).

Cost: ~300 lines (atomization, fresh-atom encoding, one transfer induction) against ~1,500 for a per-axiom re-proof.

#### 8.3 TD/swap soundness: semantic, via a `StarFormula` `TruthAntiIso`

The proof-theoretic route ("swap maps derivations to derivations") needs the axiom set to be mirror-closed; TM⁺'s is not (BX lists future halves and obtains past halves by TD - `def:BX`, paper line 4110; `Soundness.lean:1027` explains why `sep_swap_valid` exists separately). So it is circular. The tree's own pattern is the companion recursion `derivable_valid_and_swap_validIn` (`Soundness.lean:1217`) with `truthAt_of_truthAntiIso` (`Truth.lean:1124`). For L⋆: copy the six-constructor anti-iso induction and add the `stab` case, which is `forall_congr'` over `I.hist` with `SameStateAt` transported through `I.hist` and `I.dur` - the atom clause of `TruthAntiIso` already gives state agreement at reindexed times, and `swapTemporal` fixes `stab`. The ⊡-axioms are all swap-invariant (their mirrors are themselves or, for `paste`/`untl_paste`, the past-side instance obtained by exchanging the side conditions), so `axiom_swap_validIn_min`'s ⊡ arms are the same probes applied to the swapped instance. Do **not** try to derive TD from the other rules.

#### 8.4 Non-recommendations (ruled out with reasons)

- Do not plan "canonical model on ⊡-classes, verify the six axioms" as a phase: §4.2-4.3 name two independent obstructions (Lifting, Limit-on-dense) and the composition direction of `comp` is false for the literal definition.
- Do not add sorries or new axioms for any of this (zero-debt policy): every blocked item above is either restated as a provable weaker theorem (§7.3) or scoped as a spike with a postmortem exit.
- Do not describe TM⋆ as "S5 for ⊡ plus two bridge axioms" in any docstring: it is provably incomplete (§2.4).

## Decisions

1. The ⊡-axiom inventory for `StarAxiom` is {SK, SN(rule), ST, S4, S5, MS, AS, PS, US}; `FS`, `GS` and the past mirrors are derived; everything else in §2.1 is either derivable or refuted.
2. `StarAxiom` is a closed inductive with one soundness lemma per constructor; TM⁺ schemata are re-declared over `StarFormula` and discharged by atomization.
3. TD is discharged semantically through a `StarFormula` `TruthAntiIso`.
4. TM⋆ completeness over the paper's semantics is **[BLOCKED] as research** for all four classes; the plan carries (a) deterministic-class completeness of TM⋆ + Determined as the deliverable, (b) a single gated spike on the Lifting Lemma with a written postmortem exit, (c) bundled TM⋆ as the documented fallback semantics, not as a deliverable.
5. Decidability of TM⋆ is recorded as open and no easier than TM⁺'s; nothing is promised.
6. The non-definability theorem uses `TruthCorr` as is, with the two models of §6.2.

## Recommendations (for task 533's plan and task 537)

1. **Task 533 Phase 3 (semantics)**: transcribe probes Parts A, B, C, E into `Semantics/StarTruth.lean` (definitions, `paste`, `IsPureFuture`/`IsPurePast`, C1a/b, C2-C5, E0-E2) - they are already in repo style and sorry-free; ~450 lines.
2. **Task 533 Phase 4 (proof system)**: `StarAxiom` per §8.1 with the TM⁺ schemata over `StarFormula`; `IsPureFuture.swapTemporal` lemma; `StarDerivationTree` mirroring `DerivationTree` including TD.
3. **Task 533 Phase 5 (soundness)**: atomization (§8.2) for the TM⁺ arm; the ⊡ arms are the probes; TD via the anti-iso twin (§8.3). Budget ~600 lines total, one dispatch each for atomization and for the anti-iso.
4. **Task 533 Phase 6 (conservativity)**: unchanged from task 533's report.
5. **Task 537 (completeness/non-definability)**: (a) non-definability per §6.2 first (small, certain); (b) deterministic-class completeness of TM⋆ + Determined per §7.3, after checking the engine restatement against `FlowFrame.lean:781`; (c) one gated spike: attempt the Lifting Lemma over ℤ (`.Discrete`) only, exit criterion "sorry-free lemma or a postmortem naming the first mixed-formula demand that PS/US cannot meet"; never a sorry.
6. **Documentation**: add TM⋆ to the README's open-problems table (completeness over the all-histories semantics; decidability), citing Reynolds 2003 and Zanardo 1991 as the nearest results and stating that the bundled semantics is where the literature's completeness theorems live.
7. **Optional probes before 537** (cheap, would upgrade UNVERIFIED rows): the 3-state DAG frame of §2.3 as a reusable `FrameOver` (it also serves §6.2's `M₂` with `u'` renamed), the compiled `¬StarValid (⟐F⟐Pq → ⟐FPq)`, and the swap lemma for the purity predicates.

## Risks & Mitigations

- **Risk**: task 533 implements `ofPlus` only and ships a TM⋆ that cannot derive `MF` at ⊡-formulas. Mitigation: §8.2 is binding; the atomization lemma is the acceptance test ("`□⊡p → □G⊡p` derivable and sound").
- **Risk**: PS/US are added as constructors but a mixed-formula validity later turns out necessary for completeness. Mitigation: closed-inductive-plus-one-lemma discipline makes adding a constructor cheap; the report's independence argument only shows the naive set is incomplete, not that the extended set is complete, and says so.
- **Risk**: the deterministic-class completeness restatement (§7.3 step (c)) does not fall out of the engines' statements. Mitigation: it is marked Medium and gated on reading `bundleFlow_completeness_from_neg_membership`; if it fails, deliver the deterministic-class *soundness* plus the `⊡ ↔ id` collapse lemma and record the gap.
- **Risk**: the Lifting spike consumes the budget. Mitigation: one dispatch, ℤ only, postmortem exit.
- **Risk**: Zanardo 1991 says something first-hand that contradicts the second-hand summary. Mitigation: every Zanardo claim is marked second-hand; nothing load-bearing depends on the paper's internals (the bundled/complete distinction is from Thomason 1984 and Reynolds 2003, both read first-hand).

## Adversarial Self-Verification

### Claim Verification Table

| Claim | Source/Counterexample | Verification Method | Confidence |
|---|---|---|---|
| Stability clause and `⟨τ⟩_x` are lines 1114/1108 | `possible_worlds.tex` read (sed) | file read | High |
| T, 4, 5, `□→⊡`, `p→⊡p`, shift commutation valid | probes A1-A6 | `lake env lean` exit 0 on the probes file | High |
| `⊡φ` state formula at fixed `t`; `□⊡φ ↔ □φ`; `□φ → ⊡□φ` | probes B1-B3 | compiled | High |
| Pasting of two total histories at a shared state is a total history, using only `comp` and `converse` | probe C0 (`paste`, `paste_rel`) | compiled | High |
| PS, FS, GS, US valid with the purity side conditions | probes C2, C3, C4, C5 | compiled | High |
| `⊡p → □⊡p`, `G⊡p → ⊡Gp`, `⊡GPp → G⊡Pp`, `Fp → ⊡Fp`, `P⊡p → ⊡Pp` refuted | probes D1-D5 on `natFrame` over ℤ | compiled | High |
| `⊡φ` depends on the world state alone (any two times) | probes E1, E2 | compiled | High |
| PS not derivable from the naive set + TM⁺ + all rules | §2.4 E-model argument | paper argument; relies on TM⁺ soundness over disjoint-lines frames (landed) and on E-model closure under the mirror construction | Medium-High (not machine-checked; the E-model is a semantic object outside the tree) |
| Naive set complete for the tense-free fragment | §2.2 | paper derivation (S5 fully-modalized fact) | Medium (not load-bearing) |
| All four engines' countermodels are deterministic | `FlowFrame.lean:145-160` (`TaskRel p d q := p.1 = q.1 ∧ q.2 = p.2 + d`), `ReynoldsBridge.lean:464-470`, cited from `BXCanonical/Completeness.lean:145`, `CompletenessDedekind.lean:78`, `StrongCompleteness.lean:438` | file reads + grep | High |
| `comp`'s composition direction fails for the literal class-frame definition | §4.3 | reasoning over `TaskFrame.Compositional` as read | High |
| *Limit* at risk on dense class frames | §4.3 | reasoning; no counterexample constructed | Medium (flagged as risk, not as theorem) |
| Reynolds 2003: bundled system uses IRR + ANF; complete-tree system needs "banning" + trans-countable construction, >100 pages, F/P only, S/U future work | `reynolds-2003-ockhamist/chunk_0003, 0004, 0007, 0008` | chunk read (OCR) | High for the rule inventory; HN's orientation unreadable |
| Reynolds 1992 IRR-free route depends on Doets' theorem over linear orders | `reynolds_1992/sec02_3-irr.md`, `sec07_9-completeness.md` | chunk read | High |
| Thomason 1984: T×W condition (2), AK12/AK13, Gabbay's technique "does not seem to extend to the treelike case", Gurevich-Shelah decidability | `thomason_1984/sec05` | chunk read | High |
| Zanardo 1985/1991 axiomatize *bundle* semantics with Burgess-Gabbay rules; von Kutschera 1997 and Di Maio-Zanardo 1996 for T×W | Brown-Goranko 1999 lines 40-70, 136-152; Venema 1993 §1, §9.2; Reynolds 2003 §1 | web PDF + chunks; **second-hand** for Zanardo's own text | Medium-High |
| GKWZ: `L × S5` decidable for `L ∈ {K4.3, Log(ℚ,<), Lin, …}`; `PTL × S5` decidable; 3-D products between K4 and S5 undecidable | `chunk_0351` (Thm 6.61), `chunk_0361` (Thm 6.68/6.69), `chunk_0405` (Thm 8.22), `chunk_0392` | grep + read at hit lines | High |
| TM⁺ decidability open for all classes | task 533 §2 citing `README.md:200-215`, `BiLasso/Assembly.lean:86,111` | prior report (cross-checked by that report's grep) | High |
| `TruthCorr` has the `Rel`/`atom`/`total_fwd`/`total_bwd` shape and `truthAt_of_truthCorr` proves L⁺ invariance | `Truth.lean:604-660` | file read | High |
| `M₂` of §6.2 is a task frame | `R∘R = R`, reflexivity, `limit_of_succOrder`, `saturation_of_finite` | reasoning over read definitions; not compiled | Medium (transcription target for task 537) |
| Deterministic-class completeness of TM⋆ + Determined | §7.3 | paper sketch; step (c) unverified against `FlowFrame.lean:781` | Medium |
| `ofPlus` gives only ⊡-free schema instances | `ProofSystem.Axiom` constructors take `Formula` parameters (`Axioms.lean:125-295`) | file read | High |
| TM⁺ axiom set not mirror-closed (TD needed) | `def:BX` line 4110; `Soundness.lean:1027-1047` | file reads | High |
| `⟐F⟐Pq → ⟐FPq` refuted | §2.3 DAG frame | paper only | UNVERIFIED |
| Past mirrors of PS/US/FS/GS derivable by TD | swap exchanges the purity predicates | paper only | UNVERIFIED (mechanical) |
| Candidate naming rule sound | §3.2 | none | UNVERIFIED (offered as candidate only) |

### Contradiction Log

- **Task 533 report vs. this report on TM⁺ schemata**: task 533 §5 states "every TM⁺ axiom is a TM⋆ axiom under the embedding, so the axiom case is one line". True for the *backward* conservativity direction, false as a description of TM⋆'s axiom set (it would omit MF at ⊡-formulas). Resolution by precedence (definition of `ProofSystem.Axiom` as read > prior report prose): §8.2; the backward-direction claim stands, the axiom-set claim is corrected.
- **Task 533 report vs. this report on completeness cost**: task 533 §8 lists TM⋆ completeness as "open research: needs a canonical model whose world states are ⊡-classes" without noting that the engines are deterministic. Resolution: `FlowFrame.lean:145-160` read; the engines cannot be reused; recorded in §4.1.
- **Paper (line 1129 context, "no ⊡/tense interaction") vs. probes C3-C5**: the paper's claim is about arbitrary `φ`; the probes show interaction for pure-future/pure-past `φ`. Resolution: machine-checked probes > prose; both statements are true at their respective scopes and the report states the scope.
- **Literature briefing vs. corpus**: the briefing said Zanardo 1991 was not retrieved; confirmed (three retrieval attempts failed). Additional relevant sources not in the briefing were found on disk (`reynolds-2003-ockhamist`, `reynolds_2002_axioms_for_branching_time`, `thomason-1970`, `rumberg-zanardo-2019`) and the first two were used.
- **Reynolds 2003 OCR**: HN's shape is unreadable; the report does not rely on its orientation.

### Recommendations modified after verification

- First draft listed only PS (same-time pasting) as the new axiom; the adversarial pass asked whether pasting at a *future* time yields more, which produced FS/GS (C3/C4) and then the general US (C5). The recommended constructor set was updated to {PS, US}.
- First draft recommended "TM⁺ axioms via `ofPlus`" as in task 533; corrected to §8.2 after checking `ProofSystem.Axiom`'s constructor signatures.
- First draft phrased the decidability answer as "likely decidable by mosaics"; downgraded to "open, no easier than TM⁺" after reading GKWZ's actual theorem statements and noting the tree's own open status.
- First draft of D1-D4 used `obtain ⟨-, h⟩` on dependent witnesses and did not compile; fixed with an explicit `atom_iff` unfolding and `⟨_, h⟩`.

## Literature Proof Structure

1. **Pasting (C0)**: paper *Compositionality* `w ⇒_{x+y} v ⟺ ∃u, w ⇒_x u ∧ u ⇒_y v` (`def:frame`), used in the `←` direction across the shared state, plus the converse convention for `s' < t < s`. Lean: `paste_rel_le_lt` (the `→`-free composition), `paste_rel` (four orientation cases), `paste := ofTotal`.
2. **Purity lemmas (C1)**: the standard "future/past fragment sees only the future/past" induction, with `□` and `⊡` as leaves; Lean: `truth_congr_agreeFrom/UpTo` by induction on the purity predicate, `stab` case via `sameStateAt_congr_left`.
3. **Pasting validities (C2-C5)**: existential witnesses assembled by `paste`; each is a three-line `refine` after `dstab_iff`.
4. **Shift invariance (E1)**: the `StarFormula` twin of `lem:history-time-shift-preservation`; the `box` and `stab` cases need the inverse shift and the pointwise-extensionality lemma E0 because `timeShift` is not definitionally involutive.
5. **Refutations (D)**: the paper's `app:deterministic` countermodel shape (two states, universal relation at nonzero durations) realized as `natFrame` over ℤ where every function is a history.
6. **Independence (§2.4)**: Venema 1993's "anti-axiom" viewpoint in reverse - a class of generalized models validating a derivation system but not a candidate axiom.

## Tactic Survey Results

| Target | Tactic/term that closed it | Notes |
|---|---|---|
| `dstab_iff`, `conj_iff`, `allFuture_iff`, … | `simp [dstab, neg, StarTruthAt]` | `Classical` open; push-through of `¬∀` is automatic |
| `paste_rel` orientation cases | `by_cases … <;> by_cases …` then `rw [if_pos/if_neg, F.converse, neg_sub]` | `abel` unavailable in this import set; `heq` via `add_comm` + `sub_add_sub_cancel` |
| `paste_agreeFrom`/`UpTo` | `show pasteFun … = …; unfold pasteFun; rw [if_…]` | `ofTotal.states` is definitionally the function |
| purity inductions | `induction hφ with …` on the `Prop`-valued predicate; `exists_congr`/`forall_congr'`/`imp_congr_left` | `imp_congr_left` needs the `SameStateAt` congruence lemma |
| atom-clause destructuring on `natFrame` | `rw [atom_iff] at h; obtain ⟨_, v⟩ := h; have v' : (if (s:ℤ) … then (1:ℕ) else 0) = 0 := v` | `⟨-, v⟩` fails (dependent witness); numerals need explicit `ℕ`/`ℤ` ascriptions because `NF.WorldState`/`NF.Duration.carrier` do not reduce for instance search |
| E1 `untl`/`snce` bounds | `lt_sub_iff_add_lt`, `sub_lt_iff_lt_add`, `(add_lt_add_iff_right Δ).mpr` | `add_lt_add_right` has the other argument order here |
| E1 inverse-shift | `truth_congr_ext` + `states_congr` (`subst; rfl`) | avoids proving `timeShift (-Δ) ∘ timeShift Δ = id` as a structure equality |

## Context Extension Recommendations

- **Topic**: the deterministic shape of every completeness engine's countermodel. **Gap**: not stated in `Metalogic.lean`'s docstring or the README metatheory table; it decides what any extension by a history-restricted modality can reuse. **Recommendation**: one paragraph in `FormalSystem/Metalogic.lean`'s docstring and a README row "countermodel frames: `bundleFlowFrame` (disjoint lines), `zTaskFrameV2` (single line)".
- **Topic**: adding a language extension. **Gap**: task 533 already asked for a "how to add a language extension" note; this report adds the atomization pattern for schema transfer and the pasting lemma as reusable tools. **Recommendation**: `docs/` note covering `BaseLanguage/` (translation), the L⋆ pattern (constructor-to-constructor embedding), schema transfer by atomization, and the TD anti-iso twin.
- **Topic**: literature sub-index. **Gap**: `reynolds-2003-ockhamist`, `reynolds_2002_axioms_for_branching_time`, `thomason-1970-indeterminist-time`, `rumberg-zanardo-2019-transition-structures` exist on disk but were absent from the `--lit` briefing; Zanardo 1991/1985/1996 are absent altogether. **Recommendation**: add the four to `specs/literature-index.json`; acquire Zanardo 1991 through library access.

## Appendix

### A. Probes index (`specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean`)

| Part | Declarations | Establishes |
|---|---|---|
| A | `StarFormula`, `SameStateAt`, `StarTruthAt`, `StarValid`, derived operators, `atom_iff`…`untl_iff`, A1-A6 | the semantics and the definitional validities (reused) |
| B | `stab_congr_sameState`, `box_stab_iff`, `stab_box_of_box` | state-formula at fixed time; `□⊡ ↔ □`; `□ → ⊡□` |
| C | `pasteFun`, `paste_rel_le_lt`, `paste_rel`, `paste`, `paste_isTotal`, `AgreeFrom/UpTo`, monotonicity, `paste_agreeFrom/UpTo`, `IsPureFuture/Past`, `sameStateAt_congr_left`, `truth_congr_agreeFrom/UpTo`, `paste_valid` (C2), `future_dstab_valid` (C3), `stab_allFuture_valid` (C4), `untl_dstab_valid` (C5) | the pasting construction and the new valid schemata |
| D | `NF`, `natHist`, `natHist_isTotal`, `natModel`, `refute_stab_box` (D1), `refute_allFuture_stab` (D2), `refute_stab_allFuture_past` (D3), `refute_determined` (D4), `refute_somePast_stab` (D5) | five refutations |
| E | `states_congr`, `truth_congr_ext` (E0), `timeShift_isTotal'`, `shift_neg_shift_domain/states`, `starTruthAt_timeShift` (E1), `stab_state_only` (E2) | shift invariance; `⊡φ` depends on the world state alone |

Compile command and result: `lake env lean specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean` - exit 0, no diagnostics, no `sorry` (the only textual occurrence is the word "sorry-free" in the header).

### B. Literature files read on disk

- `~/Projects/Literature/sources/thomason_1984/sec05_4-the-technical-side-of-historical-neces.md` (whole chunk)
- `~/Projects/Literature/sources/reynolds_1992/sec02_3-irr.md`, `sec07_9-completeness.md` (whole)
- `~/Projects/Literature/sources/venema_1993/sec01_derivation-rules-as-anti-axioms-in-modal.md` (§1.1), `sec09_92-conservativity.md` (line 6, references 44-46)
- `~/Projects/Literature/sources/venema_2001/sec03_since-and-until.md` (lines 28-58)
- `~/Projects/Literature/sources/reynolds-2003-ockhamist/chunk_0001-0008.md`, `chunk_0029.md`
- `~/Projects/Literature/sources/reynolds_2002_axioms_for_branching_time/chunk_0001-0006.md`
- `~/Projects/Literature/sources/gabbay_kurucz_wolter_zakharyaschev_2003_many_dimensional_modal_logics/chunk_0351, 0361, 0392, 0405.md` (at the grep hits)
- Not read (listed for completeness of the briefing check): `rumberg-zanardo-2019-transition-structures`, `thomason-1970-indeterminist-time`, `venema_1991` chapters, `caleiro_2013`, `blackburn_2002` §6.4-6.5 - none was needed once the complete-tree/bundled distinction was settled from Thomason 1984 and Reynolds 2003.

### C. Web sources consulted

- Brown, Goranko, "An Extended Branching-Time Ockhamist Temporal Logic", JoLLI 8 (1999) - [PDF](https://www2.philosophy.su.se/goranko/papers/JoLLI-An%20Extended%20Branching-Time%20Ockhamist%20Temporal%20Logic.pdf) (fetched, converted with `pdftotext`, quoted at lines 40-70, 136-152, 1025-1050)
- Zanardo, "A complete deductive-system for since-until branching-time logic", JPL 20 (1991) 131-148 - [SpringerLink record](https://link.springer.com/article/10.1007/BF00284972) (redirects to an authentication wall; abstract not retrieved); Semantic Scholar API record (abstract elided); PhilPapers (HTTP 403)
- Reynolds, "An axiomatization for until and since over the reals without the IRR rule", Studia Logica 51 (1992) - [SpringerLink](https://link.springer.com/article/10.1007/BF00370112) (read from the corpus, not the web)
