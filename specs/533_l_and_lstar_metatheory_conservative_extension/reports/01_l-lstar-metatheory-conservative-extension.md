# Research Report: L and L⋆ metatheory and conservative extension over L⁺

- **Task**: 533 - l_and_lstar_metatheory_conservative_extension
- **Started**: 2026-09-03T17:10:00Z
- **Completed**: 2026-09-03T17:55:00Z
- **Effort**: ~45 minutes (hard mode, single agent)
- **Dependencies**: None (builds on the landed work recorded under tasks 413, 495, 524, 526)
- **Sources/Inputs**:
  - Primary source: `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex` (lines 233-234, 1102-1175, 1177-1258, 1355-1380, 1418-1432, 3729-3775, 4105-4135, 4656-4700)
  - Repository (opened and read): `FormalSystem/BaseLanguage/{Formula,Axioms,Derivation,Translation,AxiomDischarge}.lean`, `FormalSystem/Syntax/Formula.lean`, `FormalSystem/ProofSystem/Axioms.lean`, `FormalSystem/Semantics/{Truth,BLTruth,BLValidity,Validity,WorldHistory,TaskFrame}.lean`, `FormalSystem/Metalogic.lean`, `FormalSystem/Metalogic/{Conservativity,Soundness,StrongCompleteness,Compactness,SetConsequence,Decidability}.lean`, `FormalSystem/Metalogic/Conservativity/{Backward,BaseLanguageSoundness,TMCompletenessReduction,SpWitness,Z1Countermodel}.lean`, `FormalSystem/Metalogic/BXCanonical/Completeness.lean`, `FormalSystem/Metalogic/Decidability/{Correctness,BiLasso/Assembly,Verified/Decidable}.lean`, `README.md`, `scripts/check-module-invariants.sh`
  - Prior task artifacts: `specs/495_.../reports/01_tm-completeness-status.md`, `specs/495_.../summaries/01_...md`, `specs/524_.../summaries/01_...md`
  - Literature (global corpus, read on disk under `~/Projects/Literature/sources/`): `venema_2001/sec03_since-and-until.md`, `venema_1993_since/sec01_completeness-via-completeness-since-and.md`, `burgess_1982_i/Burgess_1982_Axioms_for_tense_logic_Since_and_Until.md`, `burgess_1984/sec08_temporal-conjunctions-eliminability.md`, `reynolds_1992/sec01_an-axiomatization-for-until-and-since-ov.md`
  - Lean tooling: `lean_loogle`, `lean_local_search`, `lean_run_code` (three compiled prototypes, Appendix A)
  - Web: WebSearch/WebFetch (Appendix B)
- **Artifacts**: this report; `specs/533_l_and_lstar_metatheory_conservative_extension/.return-meta.json`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Project Context

- **Upstream Dependencies**: `FormalSystem/BaseLanguage/` (L syntax, TM axioms, `tr`), `FormalSystem/Metalogic/Conservativity/` (backward bridge, BL soundness, TM-completeness reduction), `FormalSystem/Metalogic/StrongCompleteness.lean` (four `WeakCompleteness` engines), `FormalSystem/Metalogic/Compactness.lean` (ultraproduct compactness at Base/Dense), `FormalSystem/Semantics/Truth.lean` (`TruthAt`, `TruthCorr`)
- **Downstream Dependents**: any future L⋆ tableau/decision work; documentation under `docs/` (C14 count checks); `scripts/check-module-invariants.sh` C2/C3/C14
- **Alternative Paths**: none for L (already built); for L⋆ see Findings §4
- **Potential Extensions**: open-future/open-past operators (paper lines 1136-1146) follow the same recipe as the stability modal with a different `SameStateAt` relation

## Executive Summary

- **The L half of the task is largely already in the tree.** `BLFormula` (H/G-primitive), the TM axiom set, `DerivationTree`, the translation `tr : BLFormula → Formula`, native semantics `BLTruthAt`, per-class validity `BLValidIn`, BL soundness for all four frame classes, and the backward bridge `TM ⊢ φ ⟹ TM⁺ ⊢ tr φ` are all landed and sorry-free (`FormalSystem/BaseLanguage/`, `FormalSystem/Metalogic/Conservativity/`). Zero structural `sorry` exists anywhere under `FormalSystem/` outside `Boneyard/` (verified by grep; pinned by invariant C3).
- **Proof-theoretic conservativity of TM⁺ over TM is machine-refuted at `.Discrete` and refuted-in-source at `.Base`**; the reduction `tmComplete_iff_forward` (`Metalogic/Conservativity/TMCompletenessReduction.lean:125`) shows this is literally the same proposition as "TM is complete over task frames". The task's literal ask "prove L⁺ is a conservative extension of L" is therefore **false as a proof-theoretic statement about the paper's TM** and must be delivered as (a) **semantic** conservativity (`blValidIn_iff_validIn_tr`, already landed) and (b) conservativity over the **L-fragment logic** `TMᴸ fc φ := Derivable fc [] (tr φ)`, for which soundness/completeness/compactness transfer mechanically. A finite Hilbert axiomatization of `TMᴸ` is open research and is out of scope.
- **The stability modal is exactly** `M,τ,x ⊨ ⊡φ iff M,σ,x ⊨ φ for all σ ∈ ⟨τ⟩_x`, `⟨τ⟩_x := {σ ∈ H_F | σ(x) = τ(x)}` (paper line 1114, quoted verbatim in §1). The paper gives **no axiomatization** for it ("outside the scope of the present paper", line 1375). The only paper-stated facts: its monomodal logic is S5 (footnote, line 1118); `φ → ⊡φ` for non-temporal `φ` (line 1119); *Determined* `φ → ⊡φ` is valid over deterministic frames and refutable over non-deterministic ones (lines 1426, 4114, 4130).
- **Architecture decision: separate inductive `StarFormula` (7 constructors) plus a constructor-to-constructor embedding `ofFormula : Formula → StarFormula`**, mirroring the landed `BLFormula`/`tr` pattern. Adding a constructor to `Formula` would touch 414 pattern-match sites across 57 non-Boneyard files (measured) and force a rebuild of the 276k-line tree; a parameterized-signature refactor costs the same and buys nothing. A prototype of the 7-constructor type, its embedding, injectivity, `Denumerable`, the semantics with the `stab` clause, truth transfer along the embedding, and the S5+interaction validities **compiled against the live tree** via `lean_run_code` (Appendix A).
- **The hard direction of "TM⋆ is conservative over TM⁺" is cheap**: it needs only TM⋆ *soundness* plus the *existing* TM⁺ completeness engines (`completeness_base/dense/discrete/dedekind`, `StrongCompleteness.lean:879/987/1101/775`). The composition `forward_star_of_sound` type-checked against `BXCanonical.completeness` (Appendix A). It does **not** need TM⋆ completeness — which is the one genuinely open, research-grade item in this task and is scoped as a gated spike.
- **Online survey verdict: nothing directly reusable.** No Lean/Isabelle/Coq formalization of Since/Until completeness, Kamp's theorem, or tense-logic conservativity exists; the closest Lean 4 artifacts (FormalizedFormalLogic/Foundation, LeanLTL, LeanearTemporalLogic) cover Kripke modal logic or ℕ-indexed future-only LTL with no Hilbert completeness.

## Context & Scope

Three languages over the shared atom type `FormalSystem.Syntax.Atom`:

| Language | Primitives | Repo type | Status |
|---|---|---|---|
| L (paper `\BL`, `def:BL-language`, line 1180) | `p, ⊥, →, □, H, G` | `FormalSystem.BaseLanguage.BLFormula` (`BaseLanguage/Formula.lean:79`) | landed |
| L⁺ (paper `\BL^+`, `def:BLplus-language`, line 3729) | `p, ⊥, →, □, S, U` | `FormalSystem.Syntax.Formula` (`Syntax/Formula.lean:74`) | landed |
| L⋆ (this task) | L⁺ + `⊡` (Stability, line 1114) | none — to be created | new |

Note on the paper's own `\BL^\star` (line 1374): it adds `⊡` **and** the store/recall operators `\timeStore^i, \timeRecall^i, \worldStore^i, \worldRecall^i`. The task description scopes L⋆ to the stability modal only; this report follows the task. The hybrid store/recall operators change the point of evaluation (vectors `v⃗, μ⃗`) and would require a different truth-definition signature; they are out of scope.

Constraints in force: zero-debt (no `sorry`, no new axioms — invariant C3, `scripts/check-module-invariants.sh:11`), the `BaseLanguage/ → Semantics/` import direction invariant (`BaseLanguage/Formula.lean` docstring), no task-number citations under `FormalSystem/` (C9), and documented counts must match the tree (C14).

## Findings

### 1. Ground truth from the paper (Tier 1 source)

Verbatim, `possible_worlds.tex`:

- **Line 1108-1109** (definition of the intersection set): "given a world `τ ∈ H_F` and time `x ∈ D`, we may let `⟨τ⟩_x := {σ ∈ H_F | σ(x) = τ(x)}` be the set of possible worlds that intersect `τ` at `x`".
- **Line 1114** (the semantic clause): `($\Stability$) M,τ,x ⊨ ⊡φ iff M,σ,x ⊨ φ for all σ ∈ ⟨τ⟩_x.`
- **Line 1116**: "A sentence `⊡φ` is true in a world `τ` at a time `x` just in case `φ` is true at time `x` in every possible world that occupies the same world state as `τ` at `x`."
- **Lines 1118-1119** (footnote): "Since `⟨τ⟩_x` is an equivalence class under the relation `σ ∼_x τ := σ(x) = τ(x)`, the monomodal logic of `⊡` is also S5. However, for non-temporal `φ`, the truth-value of `φ` at `⟨M,τ,x⟩` depends only on `τ(x)`, so `φ → ⊡φ` is valid, collapsing `⊡` to the trivial modality on this fragment."
- **Line 1121**: dual `⟐φ := ¬⊡¬φ` (macro `\stability`).
- **Lines 1125-1129**: defined modals `Will := ⊡G`, `will := ⊡F`, `Could := ⟐G`, `could := ⟐F`.
- **Line 1171**: "I will omit further consideration of the restricted modals `⊡`, `▷`, `◁`, and `\Nomic`" — the logic section (`\S sub:Logic`, lines 1177-1258) axiomatizes **only** L, and the appendix (`def:TMplus`, line 4656) axiomatizes **only** L⁺.
- **Line 1375**: "extending TM to provide a logic for `\BL^\star` is outside the scope of the present paper."
- **Line 1426** (*Determined* schema): `φ → ⊡φ`; **line 4114** (`app:deterministic`): valid over every *Deterministic* frame; **line 4130** (`app:non-deterministic`): refuted over a two-state frame with `⇒_z` universal for `z > 0` (the same shape as `FormalSystem/Semantics/WorldHistory.lean`'s `universal` frame family, lines 216-253).
- **Lines 1150-1163**: `⟨τ⟩_x` is *definable*, so no primitive accessibility relation is needed; `R_×(τ,σ) := σ ∈ ⟨τ⟩_x` for fixed `x`.

Consequences for the formalization:

- The relation is on **total** histories at a **shared** time; in repo terms `σ.states t _ = τ.states t _` with `σ.IsTotal`. The domain-proof arguments are handled by quantifying over both proofs (`SameStateAt`, Appendix A), which is proof-irrelevant and lets the atom case close by `rw`.
- The valid principles that follow *directly from the definition* (all machine-checked in Appendix A): `⊡φ → φ` (T), `⊡φ → ⊡⊡φ` (4), `¬⊡φ → ⊡¬⊡φ` (5), `□φ → ⊡φ` (because `⟨τ⟩_x ⊆ H_F`), `p → ⊡p` for atoms. K and necessitation for `⊡` are immediate from the universal-quantifier shape. `⊡` commutes with time shift (`sameStateAt_timeShift`, Appendix A), which is what the MF/shift soundness case needs.
- There is **no** valid `⊡`/tense interaction in general (that is the whole point of `Will` vs `will`, lines 1125-1129), and `⊡φ → □⊡φ` is **not** valid (it would collapse `⊡` to `□`).

### 2. Current repository state (all paths opened; sorry status verified by grep)

Structural `sorry` count under `FormalSystem/` excluding `Boneyard/`: **0** (grep for `^\s*sorry\s*$|:= sorry|by sorry|exact sorry` returns only prose; matches invariant C3 and the `docs/README.md` count). Everything below is sorry-free unless stated.

**L (BaseLanguage) — landed**

| Declaration | Location | Statement (paraphrase) |
|---|---|---|
| `BLFormula` | `BaseLanguage/Formula.lean:79` | 6 constructors `atom, bot, imp, box, allPast, allFuture`; derives `DecidableEq, Countable` |
| `BLFormula.swapBL` | `Formula.lean` (after derived ops) | H/G interchange for TD |
| `BaseLanguage.Axiom` | `BaseLanguage/Axioms.lean:73` | CPL(4) + MK, MT, M5, MF, TK, T4, TB, TA, TL + DF/DN/CO, `Type`-valued |
| `Axiom.minFrameClass` | `Axioms.lean:143` | reuses `ProofSystem.FrameClass` |
| `BaseLanguage.DerivationTree fc Γ φ` | `BaseLanguage/Derivation.lean:68` | rules: axiom, assumption, MP, necessitation, temporal_necessitation, temporal_duality (TD), weakening |
| `BaseLanguage.Derivable` | `Derivation.lean:152` | `Nonempty (DerivationTree fc Γ φ)` |
| `tr : BLFormula → Formula` | `BaseLanguage/Translation.lean:57` | H ↦ `Formula.allPast`, G ↦ `Formula.allFuture`; `tr_swapBL`, `tr_ne_untl`, `tr_ne_snce`, `tr_injective` |
| `dischargeAxiom` | `BaseLanguage/AxiomDischarge.lean:359` | TM⁺ derivation of `tr` of every TM axiom; TB/TA/TL/DF/CO need the `¬G¬ψ ↔ Fψ` bridge (`notGNot_imp_F`, `:143`) |
| `BLTruthAt` | `Semantics/BLTruth.lean:98` | native 6-clause recursion; box quantifies over `σ.IsTotal` |
| `BLValidOn/BLValidOnFrames/BLValidIn/BLValid` | `Semantics/BLValidity.lean:96-123`; `BLValidDense/Discrete/DiscreteSucc/Dedekind` at `:204/216/233/268` | per-class validity |
| `truthAt_tr` | `Metalogic/Conservativity/BaseLanguageSoundness.lean:110` | `TruthAt M τ t (tr φ) ↔ BLTruthAt M τ t φ` |
| `blValidIn_iff_validIn_tr` | `BaseLanguageSoundness.lean:177` | `BLValidIn fc φ ↔ ValidIn fc (tr φ)` — **semantic conservativity of L⁺ over L, all classes** |
| `bl_soundness_in`, `bl_soundness{,_dense,_discrete,_dedekind}`, `_valid` forms | `BaseLanguageSoundness.lean:232-332` | TM soundness over `BLTruthAt`, by composing `translate` with TM⁺ soundness through `truthAt_tr` |
| `bl_soundness_discrete_succ` | `:429` | Archimedean-free discrete soundness, direct induction |
| `Conservativity.translate`, `derivable_translate` | `Metalogic/Conservativity/Backward.lean:64,88` | `TM ⊢ φ ⟹ TM⁺ ⊢ tr φ` (backward direction, generic in `fc`) |
| `ceb_backward, cef_backward, ced_backward, cec_backward` | `Backward.lean:104,116,126,147` | four paper rows |
| `TMComplete fc`, `Forward fc`, `tmComplete_iff_forward` | `Conservativity/TMCompletenessReduction.lean:94,102,125` | TM completeness over `fc` **is** forward conservativity at `fc` (given a `WeakCompleteness fc` engine) |
| `tmCompleteDiscrete_refuted` | `Conservativity/Z1Countermodel.lean:199` | `¬ TMCompleteDiscrete` via `not_bl_derivable_z1` (`:175`) over `ℚ ×ₗ ℤ` |
| `Sp`, `blValid_sp`, `sp_translate` | `Conservativity/SpWitness.lean:74,105,124` | the Base-row witness: `(Sp)` is BL-valid and TM⁺-derivable; its TM-underivability is **not machine-checkable within `TaskFrame`** (needs a two-fibre structure — `Conservativity.lean` docstring, "CEB" section) |

**L⁺ (TM⁺) — landed**

| Declaration | Location | Notes |
|---|---|---|
| `Formula` | `Syntax/Formula.lean:74` | 6 constructors; `allFuture φ := (someFuture φ.neg).neg`, `someFuture φ := untl top φ` (`:148-178`) |
| `ProofSystem.Axiom`, `FrameClass`, `minFrameClass` | `ProofSystem/Axioms.lean:111,529,599-607` | Burgess–Xu BX + S5 + MF; classes `Base < Dense ≤ Dedekind`, `Base < Discrete` |
| `TruthAt` | `Semantics/Truth.lean:223` | box: `∀ σ, σ.IsTotal → …`; untl/snce strict witness, open guard |
| `TruthCorr`, `truthAt_of_truthCorr` | `Truth.lean:604,634` | the single generic transport induction (time shift, iso, `IntTransfer`) |
| `ValidIn fc`, `Valid` | `Semantics/Validity.lean:376,416` | `Valid.of_forall_total` at `:427` |
| `soundness` | `Metalogic/Soundness.lean:1377` | Base; dense/discrete/dedekind siblings per `Metalogic.lean` docstring |
| `BXCanonical.completeness` | `Metalogic/BXCanonical/Completeness.lean:196` | `Valid φ → Derivable .Base [] φ` |
| `completeness_base/dense/discrete/dedekind : WeakCompleteness fc` | `Metalogic/StrongCompleteness.lean:879/987/1101/775` | the four engines |
| `WeakCompleteness`, `PointedModel`, `SatisfiableSet`, `ModelExistence`, `Compact`, `StrongCompleteness` | `Metalogic/SetConsequence.lean:234,153,178,186,197,207` | generic `FrameClass`-indexed vocabulary |
| `compactBase/Dense`, `strongCompletenessBase/Dense` | `Metalogic/Compactness.lean:183,186,196,203` | ultraproduct route (`Semantics/Ultraproduct/Los.lean:66,154`) |
| `notCompactDiscrete/Dedekind`, `notStrongCompleteness*` | `Metalogic/DiscreteNonCompactness.lean:268,287`; `DedekindNonCompactness.lean:456,473` | refutations |
| Decidability | `Metalogic/Decidability/Correctness.lean:64,112` (`decide_sound`, `isValid_sound`); `BiLasso/Assembly.lean:86,111` (`Decidable (ValidDiscrete φ)` **conditional on an `fmp` hypothesis**) | **`Decidable (⊨ φ)` is open for all four classes** (`README.md:200-215`; two earlier "decidability" theorems were retired as vacuous) |
| Kamp | `Metalogic/WeakCanonical/PriorExpressiveness.lean` header; `Metalogic.lean` docstring names `kampPriorExpressiveCompleteness` | `{U,S}` expressively complete over *Prior structures* only |

**Decisive negative facts already in the tree** (do not re-attempt): `Conservativity.lean` docstring section "THE FORWARD DIRECTION IS NOT OPEN WORK"; the `forward` shape `Derivable fc [] (tr φ) → BaseLanguage.Derivable fc [] φ` is refuted at `.Base` (source) and `.Discrete` (machine-checked) and must never be stated or `sorry`-ed.

**No stability-operator work exists** in the tree (grep for `stability|intersect|braket|SameState` under non-Boneyard `FormalSystem/` hits only the unrelated "box stability along the chain" bookkeeping in `BXCanonical/`).

### 3. Literature grounding (H3, Tier 1) — lemma-level mapping table

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|---|---|---|---|---|
| JPL paper | line 1114 `($\Stability$)` clause | `StarTruthAt … (.stab φ)` (proposed, `Semantics/StarTruth.lean`) | `∀ σ : WorldHistory F, σ.IsTotal → SameStateAt τ σ t → StarTruthAt M σ t φ` | prototype compiled (Appendix A) |
| JPL paper | line 1108 `⟨τ⟩_x` | `SameStateAt` (proposed) | `(τ σ : WorldHistory F) (t : F.Duration) : Prop := ∀ hτ hσ, τ.states t hτ = σ.states t hσ` | prototype compiled |
| JPL paper | footnote line 1118 "monomodal logic of ⊡ is S5" | `of_stab`, `stab_four`, `stab_five` (proposed `Semantics/StarTruth.lean`) | T/4/5 validities at total `τ` | prototype compiled |
| JPL paper | footnote line 1119 `φ → ⊡φ` non-temporal | `stab_atom_of_atom` (atoms); Boolean closure to follow | `StarTruthAt M τ t (.atom p) → StarTruthAt M τ t (.stab (.atom p))` | prototype compiled (atom case) |
| JPL paper | `⟨τ⟩_x ⊆ H_F` (implicit, line 1108) | `stab_of_box` | `StarTruthAt M τ t (.box φ) → StarTruthAt M τ t (.stab φ)` | prototype compiled |
| JPL paper | line 1426 *Determined*, 4114/4130 | (optional) `determined_valid_of_deterministic`, countermodel | frame-conditional; not part of the base logic | not started (optional) |
| JPL paper | `def:BL-language` line 1180; `\S sub:Logic` axioms 1187-1201 | `BLFormula`, `BaseLanguage.Axiom` | see §2 | landed |
| JPL paper | `def:BLplus-language/semantics` 3729-3752 | `Formula`, `TruthAt` | see §2 | landed |
| JPL paper | `cor:tm-completeness` 4668 | `completeness_base/dense/discrete/dedekind`, `strongCompletenessBase/Dense`, `notStrongCompletenessDiscrete/Dedekind` | see §2 | landed |
| Burgess 1982 (`burgess_1982_i`, §1.1 table, §1.3 A1a-A7a) | S/U primitives, G/H/F/P defined, axioms J₀ | `ProofSystem.Axiom.{right_mono_*, connect_*, enrichment_*, self_accum_*, absorb_*, linear_*}` | `ProofSystem/Axioms.lean:161-232` | landed (docstring cites Burgess 1982 §1.1) |
| Burgess 1984 (`sec08`, Prop. 4.3, Thm 4.5) | `G'` not G,H-definable over `(ℝ,<)`; `{U,S}` temporally complete over continuous orders (Kamp) | — (no repo target for the *separation* half; expressive completeness restricted to Prior structures: `kampPriorExpressiveCompleteness`) | — | separation NOT formalized; not needed for any statement in this task (see §5) |
| Venema 2001 (`venema_2001/sec03`) | Thm 4.1 (Kamp); "new operators really add expressive power"; Ockhamist semantics eq. (5); Peircean as fragment via translation `(·)^o` | conceptual model for L⋆: `⊡` plays the Ockhamist `□`-over-branches role relative to `⟨τ⟩_x` | — | grounding only |
| Venema 1993 (`venema_1993_since/sec01`) | §1 "completeness via expressive completeness"; §2.3 Stavi connectives; orthodox systems (MP, TG, SUB) | already reflected in `WeakCanonical/` (Stavi/Kamp chain) | — | landed (per `Metalogic.lean` docstring) |
| Reynolds 1992 (`reynolds_1992/sec01`) | weak completeness over ℝ, IRR-free; §10 integers | `completeness_dedekind` (`StrongCompleteness.lean:775`), `notCompactDedekind` | — | landed |
| Kamp 1968 via Burgess 1982 line 14 | "S,U-tense logics … axiomatizability announced, never published" | — | — | provenance only |

Reference-grounding notes: the Burgess 1982 chunk carries `provenance_fidelity: unverified_scan_source`; its axiom list agrees constructor-for-constructor with the repo's `ProofSystem.Axiom` docstrings, which independently cite it, so the cross-check passes. Chunk files for `burgess_1984 §1`, `venema_1993 §9.2-9.3`, `rabinovich_2014 §2.3`, and both `fine_2012` conservativity chunks are **missing on disk** (the index resolves to non-existent paths); the Fine "conservativity" hits from the literature briefing are about the logic of ground and are not relevant to modal-language conservativity — they were not used.

### 4. The three-way architecture question — decision with costs

Measured migration facts (non-Boneyard `FormalSystem/`): 276,217 lines of Lean; 414 pattern-match arms on `untl`/`snce` constructors across 57 files; 5,174 binder occurrences of `: Formula`.

| Option | How S/C/Cpt/Dec transfer | Conservativity statement shape | Migration cost vs. landed L⁺ code | Verdict |
|---|---|---|---|---|
| **(a) One `Formula` parameterized by a signature/level** (`Formula (sig : Sig)` or a `Lang` index with typeclass) | Every existing theorem must be restated at the L⁺ instance; the 414 match arms and every `induction φ` need an index discriminator or a `Sig`-dependent constructor set | `Derivable sig₁ … → Derivable sig₂ …` along an implicit inclusion | **Rewrite of the whole tree**: `Formula` appears in 5,174 binders; `TruthAt`, `TruthCorr`, the tableau (`Decidability/`, ~40 modules), and three canonical-model pipelines are all `Formula`-monomorphic | loses — cost is total, benefit is cosmetic |
| **(b) Separate inductives + explicit embeddings + transport lemmas** (the landed `BLFormula`/`tr` pattern) | Soundness: new induction on the new `DerivationTree` (small: 7 constructors, TM⁺ axioms embed exactly). Completeness (hard direction of conservativity): via existing engines through the truth-transfer lemma. Compactness: new Łoś case for `stab` (see §6). Decidability: not transferable — inherits the tree's open status | `∀ φ : Formula, Derivable⋆ fc [] (ofFormula φ) ↔ Derivable fc [] φ` | **Zero change to landed code**; ~5 new files; embedding is constructor-to-constructor (unlike `tr`, no `F/P` bridge is needed, because L⁺ ⊂ L⋆ is a syntactic inclusion, not a definitional one) | **wins** |
| **(c) Subtype/predicate carve-out over the largest language** (`Formula := {φ : StarFormula // stabFree φ}`) | Would replace the existing `Formula` by a subtype — every `match`/`induction` on `Formula` breaks (the subtype has no constructors) | trivial by construction | same as (a) in practice; also breaks `deriving Countable/DecidableEq` ergonomics and the `Formula`-indexed `Axiom : Formula → Type` family | loses |
| **(d) Typeclass abstraction over semantics with per-language instances** (`class HasTruth (Φ : Type) …`) | Adds an abstraction layer over `TruthAt` that no existing proof uses; the transports the task needs are *between* languages, which a per-language class does not express | statements become instance-relative and harder to read | moderate new code, no reuse gained; still needs (b)'s embeddings for the cross-language theorems | loses |

**Decision: (b).** It is the pattern the repository already validated for L⊂L⁺ (`BaseLanguage/` + `Conservativity/`), it leaves every sorry-free result untouched, and for L⁺⊂L⋆ it is *strictly easier* than for L⊂L⁺ because the embedding is constructor-to-constructor (the whole `AxiomDischarge.lean` bridge machinery is unnecessary; `dischargeAxiom` becomes `DerivationTree.axiom _ _ (Axiom⋆.ofPlus h) h_fc`). What *is* shared across the three languages is the semantic layer (`TaskFrame`, `TaskModel`, `WorldHistory`, `FrameClass`, `FrameClass.Sat`) and the generic `FrameClass`-indexed metatheory vocabulary (`WeakCompleteness`, `Compact`, `PointedModel`, …). The planner should expect L⋆'s files to be the L⁺ files' names with a `Star` prefix under a new `FormalSystem/StarLanguage/` directory (syntax, axioms, derivation, embedding) and `Semantics/StarTruth.lean`, `Semantics/StarValidity.lean`, `Metalogic/Conservativity/Star/` — the same shape as `BaseLanguage/`, so the two extension directions read as one story.

Mathlib machinery that helps (all verified, §6): `Infinite.of_injective` + `nonempty_denumerable` for `Denumerable StarFormula` (needed if any chronicle-style enumeration is attempted); `decidable_of_iff` for any future `Decidable` transfer; `Setoid.ker (fun σ => σ.states t _)` is the mathematical content of `⟨τ⟩_x` if a quotient is ever wanted, but the prototype shows a plain `Prop`-valued `SameStateAt` suffices and avoids `Quotient` friction.

### 5. Precise conservative-extension statements

Notation: `Derivable fc Γ φ` is `ProofSystem.Derivable` (L⁺); `BaseLanguage.Derivable` (L); `StarDerivable fc Γ φ` (L⋆, to be defined as `Nonempty (StarDerivationTree fc Γ φ)`).

**Pair L ⊂ L⁺ (via `tr`)**

- *Backward* (easy, landed): `derivable_translate : BaseLanguage.Derivable fc Γ φ → Derivable fc (trCtx Γ) (tr φ)`.
- *Forward = the hard direction = proof-theoretic conservativity*: `Forward fc := ∀ φ, Derivable fc [] (tr φ) → BaseLanguage.Derivable fc [] φ`. **Refuted** at `.Discrete` (`tmCompleteDiscrete_refuted`), refuted-in-source at `.Base`, **open** at `.Dense`, `.Dedekind`. By `tmComplete_iff_forward`, proving it at `.Dense`/`.Dedekind` is exactly proving TM_d/TM_dc complete — open research, not a phase of this task.
- *Semantic conservativity* (landed, all classes): `blValidIn_iff_validIn_tr fc φ : BLValidIn fc φ ↔ ValidIn fc (tr φ)`.
- **Deliverable this task can honestly add for L**: the *L-fragment logic* and its metatheory:
  - `def TMFrag (fc) (φ : BLFormula) : Prop := Derivable fc [] (tr φ)` (name to taste; "the H/G-fragment of TM⁺").
  - Soundness: `TMFrag fc φ → BLValidIn fc φ` — one line from `soundness_validIn` and `blValidIn_iff_validIn_tr`.
  - Completeness: `BLValidIn fc φ → TMFrag fc φ` — one line from the `WeakCompleteness fc` engine and `blValidIn_iff_validIn_tr`, for all four classes.
  - `TM ⊆ TMFrag` is `derivable_translate`; `TM ≠ TMFrag` at `.Discrete` is `not_bl_derivable_z1` + `z1_translate` (`Backward.lean:188`).
  - Compactness at `.Base`/`.Dense`: `BLSatisfiableSet fc Γ` (image under `tr`) — finitely satisfiable ⇒ satisfiable via `compactBase`/`compactDense` + `truthAt_tr`; non-compactness at `.Discrete`/`.Dedekind` transfers likewise (the witness sets `{F p} ∪ {¬Xⁿ p}` are H/G-expressible? **No** — `Formula.next` is `untl bot`, not in the range of `tr`; the Dedekind witness likewise uses `K⁺`. So BL non-compactness at those classes is **not** a transfer and is out of scope; state only the positive rows.)
  - Decidability: nothing to transfer (open for L⁺ itself).
- Kamp subtlety, stated precisely: L⁺ is strictly more expressive than L (Burgess 1984 Prop. 4.3, Venema 2001 §4). This is what makes `Forward` non-trivial, and it is *consistent with* `Forward` failing: the extra expressive power lets TM⁺ derive H/G-formulas (e.g. `Z1`, `Sp`) that TM cannot. No expressiveness-separation theorem is needed for any statement above, so none is proposed.

**Pair L⁺ ⊂ L⋆ (via `ofFormula`)**

- *Backward* (easy): `StarDerivationTree.ofPlus : DerivationTree fc Γ φ → StarDerivationTree fc (Γ.map ofFormula) (ofFormula φ)` by structural recursion; every TM⁺ axiom is a TM⋆ axiom under the embedding (design the `StarAxiom` inductive with a constructor `ofPlus : Axiom φ → StarAxiom (ofFormula φ)` carrying `minFrameClass` through, plus the new `⊡`-axioms), so the axiom case is one line. `swapTemporal` on L⋆ maps `stab` to `stab`; `ofFormula_swapTemporal` is `rfl`-by-induction.
- *Forward* (the hard direction, **provable now**): `∀ φ : Formula, StarDerivable fc [] (ofFormula φ) → Derivable fc [] φ`, by `StarSoundness` (new, small) + `starValidIn_ofFormula_iff : StarValidIn fc (ofFormula φ) ↔ ValidIn fc φ` (from `starTruthAt_ofFormula`) + the engine `completeness_{base,dense,discrete,dedekind}`. Prototype `forward_star_of_sound` compiled against `BXCanonical.completeness` with TM⋆ soundness as a hypothesis (Appendix A). So **proof-theoretic conservativity of TM⋆ over TM⁺ holds at all four classes and needs no TM⋆ completeness.**
- *Semantic conservativity*: `starValidIn_ofFormula_iff` (prototype at Base; the `fc`-generic form is the same proof with `ValidIn.of_forall_total`/`ValidIn.apply_total`, `Validity.lean:551,558`).
- Intended notion: **both** — proof-theoretic (both directions as above) and semantic (truth transfer). Which direction is hard: for L⁺⊂L⋆ neither is hard; for L⊂L⁺ the forward direction is the hard one and is false/open.

**Pair L ⊂ L⋆**: compose: `ofFormula ∘ tr`; backward direction composes `derivable_translate` with `ofPlus`; forward direction inherits exactly the L⊂L⁺ status (refuted at Base/Discrete) since `Forward⋆ ∘ (L⋆ forward) = Forward`. Nothing new to prove; one composed corollary per class for the backward direction.

### 6. Mathlib and repo grounding — verified names

| Name | Signature (as returned by tool) | Tool | Use |
|---|---|---|---|
| `decidable_of_iff` | `{b : Prop} (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b` (Init.PropLemmas) | `lean_loogle` | any future `Decidable` transfer along `ofFormula` |
| `Setoid.ker` | `{α β} (f : α → β) : Setoid α` (Mathlib.Data.Setoid.Basic) | `lean_loogle` | mathematical reading of `⟨τ⟩_x`; not needed by the prototype |
| `Infinite.of_injective` | `{α β} [Infinite β] (f : β → α) (hf : Injective f) : Infinite α` (Mathlib.Data.Fintype.EquivFin) | `lean_loogle` | `Infinite StarFormula` (compiled) |
| `nonempty_denumerable` | theorem in `Mathlib/Logic/Denumerable.lean` | `lean_local_search` | `Denumerable StarFormula` (compiled, mirrors `Syntax/Formula.lean:105`) |
| `FormalSystem.Syntax.Formula.swapTemporal` | def, `Syntax/Formula.lean:668` | `lean_local_search` | template for `StarFormula.swapTemporal` |
| `FormalSystem.Semantics.truthAt_tr` | theorem, `Conservativity/BaseLanguageSoundness.lean:110` | `lean_local_search` | template for `starTruthAt_ofFormula` |
| `FormalSystem.Metalogic.BXCanonical.completeness` | `(φ : Formula) : Valid φ → Derivable FrameClass.Base [] φ` | compiled use in Appendix A | forward conservativity engine (Base) |
| `Valid.of_forall_total`, `Valid.apply` | `Validity.lean:427,435` | compiled use | binder conversion |
| `WorldHistory.isTotal_iff` | `Semantics/WorldHistory.lean:372` | compiled use | `hτ t : τ.domain t` |
| `WorldHistory.timeShift` | `Semantics/WorldHistory.lean:295` (`states := fun z hz => σ.states (z + Δ) hz`) | compiled use | `sameStateAt_timeShift` is `Iff.rfl` |
| `Ultraproduct.los_truthAt` | `Semantics/Ultraproduct/Los.lean:154` | read | Łoś for `Formula`; a `StarFormula` twin needs a `stab` case (see Risks) |

UNVERIFIED (named in docstrings, not opened as declarations in this session): `kampPriorExpressiveCompleteness`, `uSExpressivelyCompleteOverPrior` (`WeakCanonical/PriorExpressiveness.lean` header names them; `^theorem` grep did not locate the declaration line). Neither is load-bearing for any proposed phase.

### 7. Online survey (user-requested)

- **FormalizedFormalLogic/Foundation** (Lean 4): standard modal logic with Kripke semantics, soundness/completeness, frame definability, Gödel–McKinsey–Tarski; **no** tense logic, no Since/Until, no conservativity/translation results between languages (WebFetch of the project book). Its `Formula` is a fixed inductive per logic family, not signature-parameterized — the same design as this repo.
- **LeanLTL** (ITP '25, arXiv 2507.01780): a unifying *semantic* framework for LTL flavours over finite/infinite linear time; no Hilbert system, no completeness/decidability, no past operators reported.
- **LeanearTemporalLogic** (GitHub, mrigankpawagi): ℕ-indexed LTL with `X`/`U` only, no past/Since, no axiomatization; tightly coupled to ℕ traces.
- **ANU "Mechanising Linear Temporal Properties in Lean"** (project page, Oct 2025): topology-flavoured linear-temporal properties; no code location, no Since/Until.
- **Kamp's theorem**: no formalization in Lean/Isabelle/Coq found; the standard reference proof is Rabinovich 2014 (LMCS), which this repo already follows for Prior structures.
- **Conservative extensions in proof assistants**: only the Lean 3 PAL·S5 formalization (Formalization-PAL) and the hybrid-logic `L(∀)` completeness (arXiv 2606.19761) came up; the latter has a "structural-freshness layer with conservativity certificates" for *language extension by fresh nominals*, which is a different mechanism from operator addition and is not transferable.
- **Closest mathematical relative of L⋆**: Ockhamist branching-time logic (Venema 2001 §4 eq. (5); Zanardo 1991 "A complete deductive system for Since–Until branching-time logic", JPL; Reynolds 2001 full CTL* axiomatization). In Ockhamist semantics `□` quantifies over branches through the current moment, exactly as `⊡` quantifies over `⟨τ⟩_x`; the difference is that task frames also carry the *global* `□` over all of `H_F` and the fixed duration group. Zanardo's Since/Until Ockhamist completeness uses Burgess–Gabbay-style rules (not orthodox), which is the most likely shape of a TM⋆ completeness proof. **Verdict: nothing directly reusable in Lean; the mathematics for a TM⋆ axiomatization exists in the Ockhamist literature (not in the corpus) and is research-grade.**

Sources: [Foundation book](https://formalizedformallogic.github.io/Book/), [FormalizedFormalLogic org](https://github.com/FormalizedFormalLogic), [Foundation on Reservoir](https://reservoir.lean-lang.org/@FormalizedFormalLogic/Foundation), [LeanLTL](https://arxiv.org/pdf/2507.01780), [LeanearTemporalLogic](https://github.com/mrigankpawagi/LeanearTemporalLogic), [ANU project](https://comp.anu.edu.au/study/projects/mechanising-linear-temporal-properties-in-lean/), [Rabinovich, A Proof of Kamp's Theorem](https://lmcs.episciences.org/730/pdf), [Hybrid logic L(∀) completeness in Lean 4](https://arxiv.org/abs/2606.19761), [Formalization-PAL](https://github.com/ljt12138/Formalization-PAL), [Extended Ockhamist temporal logic (Zanardo)](https://www2.philosophy.su.se/goranko/papers/JoLLI-An%20Extended%20Branching-Time%20Ockhamist%20Temporal%20Logic.pdf), [Ockhamist PDL decidability](https://link.springer.com/chapter/10.1007/978-3-319-48758-8_10).

### 8. What is and is not achievable sorry-free, per result

| Result | L (H/G) | L⋆ (with ⊡) |
|---|---|---|
| Syntax + embedding + injectivity + countability | landed | prototype compiled |
| Semantics (native recursion) | landed (`BLTruthAt`) | prototype compiled (`StarTruthAt`) |
| Truth transfer along embedding | landed (`truthAt_tr`) | prototype compiled (`starTruthAt_ofFormula`) |
| Semantic conservativity, all classes | landed | prototype at Base; generic form mechanical |
| Soundness | landed (`bl_soundness*`) | mechanical: new axioms are S5(⊡) + `□φ→⊡φ` + `p→⊡p`; TM⁺ axioms transfer through `starTruthAt_ofFormula` + `soundness`; shift/TD cases via `sameStateAt_timeShift` and a `stab ↦ stab` `swapTemporal` |
| Proof-theoretic conservativity, backward | landed (`derivable_translate`) | mechanical (`ofPlus` recursion) |
| Proof-theoretic conservativity, forward | refuted (Base, Discrete) / open (Dense, Dedekind) | **provable now** from soundness + existing engines |
| Completeness | refuted for TM; trivial for the fragment `TMFrag` | **open research**: needs a canonical model whose world states are `⊡`-classes of MCSs with genuine branching; no in-tree or literature-ready construction (closest: Zanardo 1991, unorthodox rules) |
| Compactness (Base, Dense) | mechanical transfer for `TMFrag` | needs a `stab` case in Łoś (`los_truthAt`): the ultraproduct history-carrier is an orbit/shift-set quotient, and `SameStateAt` must be shown to be "eventually" — moderate; **no** completeness dependency (compactness is semantic model-existence in this tree: `compact_of_modelExistence`) |
| Decidability | open for L⁺ itself; nothing to transfer | open; the verified tableau would need a `stab` rule family — out of scope |

## Decisions

1. **Architecture**: separate inductive `StarFormula` + `ofFormula` embedding (option (b)); no change to `Formula`, `BLFormula`, or any landed theorem.
2. **Scope of L⋆**: stability modal only (task text), not the paper's `\BL^\star` with store/recall.
3. **Scope of "conservative extension" for L⊂L⁺**: semantic (landed) + fragment-logic `TMFrag` (new, mechanical). The proof-theoretic forward direction is **not** a deliverable; the tree's standing prohibition stays in force.
4. **Scope of "completeness for L"**: completeness of `TMFrag` (mechanical); a native finite axiomatization of the H/G-fragment of TM⁺ is recorded as open and **not** planned.
5. **TM⋆ completeness**: planned as a **gated spike phase** with an explicit exit criterion (see Recommendations, Phase 7); if the spike does not produce a sorry-free construction, the phase closes `[COMPLETED WITH EXCLUSIONS]` and a follow-up task is spawned — never a `sorry`.
6. **TM⋆ decidability**: out of scope (L⁺ decidability is itself open; `README.md:200-215`).

## Recommendations (phase outline for the planner; each phase one agent run)

1. **Phase 1 — L-fragment metatheory (L side, ~150 lines)**: new `FormalSystem/Metalogic/Conservativity/Fragment.lean`: `TMFrag`, soundness and completeness of `TMFrag` for all four classes (one-liners from `blValidIn_iff_validIn_tr` + engines), `tm_le_tmFrag` (= `derivable_translate`), `tm_ne_tmFrag_discrete` (from `not_bl_derivable_z1`, `z1_translate`), BL compactness at Base/Dense via `tr`-image and `compactBase/Dense`. Update `Conservativity.lean` docstring and `Metalogic/README.md`; C14 counts.
2. **Phase 2 — L⋆ syntax (~200 lines)**: `FormalSystem/StarLanguage/Formula.lean`: `StarFormula`, derived operators (mirror `Formula`'s names, plus `stab`, `dualStab`, `will`, `Will`, `could`, `Could` per lines 1125-1129), `swapTemporal` (stab ↦ stab), involution, `ofFormula`, `ofFormula_injective`, `ofFormula_swapTemporal`, `ofFormula_ne_stab`, `Infinite`/`Denumerable`. Import invariant: `StarLanguage/ → Semantics/` forbidden (mirror `BaseLanguage/`).
3. **Phase 3 — L⋆ semantics (~250 lines)**: `Semantics/StarTruth.lean` (`SameStateAt`, `StarTruthAt`, characterization lemmas mirroring `BLTruth.*`), `Semantics/StarValidity.lean` (`StarValidIn fc`, `StarValid`, per-class abbreviations), `starTruthAt_ofFormula`, `starValidIn_ofFormula_iff` (generic in `fc`), the five definitional validities (T, 4, 5, `□→⊡`, atom stability) and `sameStateAt_timeShift`. Appendix A is the transcription source.
4. **Phase 4 — L⋆ proof system (~250 lines)**: `StarLanguage/Axioms.lean` (`StarAxiom` with `ofPlus` + `stab_k`, `stab_t`, `stab_4`, `stab_5`, `box_stab`, `atom_stab`; `minFrameClass` through `ofPlus`), `StarLanguage/Derivation.lean` (rules as `ProofSystem.DerivationTree` plus `stab_necessitation`), `StarDerivable`, `lift`, `ofPlus` recursion (backward conservativity), four row corollaries.
5. **Phase 5 — L⋆ soundness (~400 lines)**: `Metalogic/Conservativity/Star/StarSoundness.lean`: `star_soundness_in fc` by induction on `StarDerivationTree`; TM⁺ axiom case discharged by `soundness_validIn` + `starValidIn_ofFormula_iff`; `⊡` axioms by Phase 3 lemmas; TD case via `swapTemporal` anti-iso (extend the `TruthAntiIso` pattern, `Truth.lean:1092`, with a `stab` case) — or, cheaper, prove swap-validity proof-theoretically as task 495 did for BL (`bl_soundness_discrete_succ` design note).
6. **Phase 6 — L⋆ conservativity, forward + composed rows (~150 lines)**: `forward_star fc : ∀ φ, StarDerivable fc [] (ofFormula φ) → Derivable fc [] φ` for the four classes via the engines; the L⊂L⋆ composed backward corollaries; docstring in `Conservativity.lean` extended with a "Star" section stating precisely that `Forward⋆` holds everywhere while `Forward` does not.
7. **Phase 7 — TM⋆ completeness spike (gated)**: exit criterion: a sorry-free `star_completeness_base : StarValid φ → StarDerivable .Base [] φ` **or** a written postmortem identifying the exact obstruction (candidate construction: world states := `⊡`-equivalence classes of MCSs, task relation := "some pair of histories through the two classes", requiring the six `TaskFrame` axioms `nullity_identity, comp, converse, serial, limit, saturation` (`TaskFrame.lean:629-696`) to be re-verified). Budget one dispatch; on failure close `[COMPLETED WITH EXCLUSIONS]` and `/spawn` a follow-up.
8. **Phase 8 — L⋆ compactness (Base, Dense) (optional, ~300 lines)**: `stab` case for `los_truthAt`; then `modelExistence_of_satPreserved`-style instantiation. Only if Phase 7's outcome does not consume the budget; otherwise defer.
9. **Phase 9 — documentation and invariants**: `docs/`, `README.md` metatheory table rows for L and L⋆; run `scripts/check-module-invariants.sh` (C2/C3/C14 must stay green); no task numbers under `FormalSystem/`.

## Risks & Mitigations

- **Risk: the planner re-attempts forward conservativity for L⊂L⁺.** Mitigation: Decision 3; the `Conservativity.lean` prohibition; Phase 1 delivers the fragment logic instead.
- **Risk: TM⋆ completeness is attempted as a normal phase and stalls** (three-strikes/H5 territory). Mitigation: Phase 7 is a gated spike with a postmortem exit; the deliverable value of the task (soundness, both conservativity directions, semantic results) does not depend on it.
- **Risk: `stab` in the `□` position breaks `TruthCorr`-based transports** (`timeShift_preserves_truth`, `truthAt_of_truthCorr` are `Formula`-only). Mitigation: L⋆ needs only its own shift lemma (`sameStateAt_timeShift`, `Iff.rfl`) and a small `StarTruthCorr` if MF soundness is done semantically; alternatively discharge MF for L⋆ via `starValidIn_ofFormula_iff` since MF is a TM⁺ axiom — the embedded TM⁺ axioms need **no** new semantic work at all.
- **Risk: Łoś for `stab`.** The ultraproduct histories are orbit representatives (`ShiftSet.forward_repr`); showing "eventually same state" ↔ "same state in the ultraproduct" needs `omk_eq_omk` (`Ultraproduct/Carrier.lean:214`). Moderate; isolated to Phase 8, which is optional.
- **Risk: `SameStateAt` quantifying over domain proofs is awkward downstream.** Mitigation: on `F.HF` (total histories, `WorldHistory.lean:411`) it reduces to `τ.val.states t trivial = σ.val.states t trivial`; provide the `HF`-level characterization lemma in Phase 3.
- **Risk: documentation count checks (C14) fail** when new modules add axiom constructors or theorems. Mitigation: Phase 9; `StarAxiom` is a *new* inductive, so `ProofSystem.Axiom`'s documented constructor count (45) is unchanged.

## Adversarial Self-Verification

### Claim Verification Table

| Claim | Source/Counterexample | Verification Method | Confidence |
|---|---|---|---|
| Stability clause is line 1114 with `⟨τ⟩_x = {σ ∈ H_F | σ(x)=τ(x)}` | `possible_worlds.tex:1108,1114` read verbatim | file read (sed) | High |
| Paper gives no axiomatization of `⊡` | lines 1171, 1375 | file read | High |
| `\BL^\star` in the paper includes store/recall operators | line 1374 | file read | High |
| Zero structural `sorry` outside `Boneyard/` | grep pattern `^\s*sorry\s*$|:= sorry|by sorry|exact sorry` returns only prose; C3 pins the same | grep + `scripts/check-module-invariants.sh:11` | High |
| `Forward` refuted at `.Discrete`, open at `.Dense/.Dedekind` | `tmCompleteDiscrete_refuted` (`Z1Countermodel.lean:199`); `Conservativity.lean` docstring | file read | High |
| `Forward` refuted at `.Base` | source-level only (`Conservativity.lean` "CEB" section: TM half not machine-checkable in `TaskFrame`) | file read | Medium (not machine-checked, by the tree's own admission) |
| `tmComplete_iff_forward` needs a `WeakCompleteness fc` engine | `TMCompletenessReduction.lean:125` | file read | High |
| Four engines exist: `completeness_base/dense/discrete/dedekind : WeakCompleteness fc` | `StrongCompleteness.lean:879/987/1101/775` | grep with signature | High |
| `BXCanonical.completeness : Valid φ → Derivable .Base [] φ` | `BXCanonical/Completeness.lean:196`; used in compiled prototype | `lean_run_code` success | High |
| 7-constructor `StarFormula`, `ofFormula`, injectivity, `Denumerable`, `StarTruthAt`, `starTruthAt_ofFormula`, `starValid_ofFormula_iff`, `forward_star_of_sound`, T/4/5/`□→⊡`/atom validities, `sameStateAt_timeShift` all compile against the live tree | Appendix A | `lean_run_code`, three runs, `success: true` (warnings only: linter `unnecessarySeqFocus`, unused `hτ` in `stab_four`) | High |
| 414 match arms on `untl`/`snce` in 57 files; 276,217 non-Boneyard lines | grep/wc | Bash | High |
| `Decidable (⊨ φ)` open for all classes; `Decidable (ValidDiscrete φ)` only conditional on `fmp` | `README.md:200-215`; `BiLasso/Assembly.lean:86,111` | file read | High |
| Burgess 1982 axioms match `ProofSystem.Axiom` | chunk §1.3 vs `Axioms.lean` docstrings (which cite Burgess 1982 §1.1) | two-source cross-check; chunk is `unverified_scan_source` | Medium-High |
| Kamp: `{U,S}` complete over continuous orders; L⁺ strictly more expressive than L | Burgess 1984 sec08 Prop 4.3/Thm 4.5; Venema 2001 §4 | two chunks read | High |
| Ockhamist Since/Until completeness (Zanardo 1991) is the nearest relative | WebSearch summary only; not in corpus | web | Low-Medium (not load-bearing) |
| `decidable_of_iff`, `Setoid.ker`, `Infinite.of_injective`, `nonempty_denumerable` names/signatures | loogle / local search output | `lean_loogle`, `lean_local_search` | High |
| `kampPriorExpressiveCompleteness` exists as a declaration | named in two docstrings; declaration line not located | — | UNVERIFIED (not load-bearing) |
| BL non-compactness at Discrete/Dedekind does **not** transfer from L⁺ | witnesses use `Formula.next = untl bot`/`K⁺`, outside `range tr` by `tr_ne_untl` | reasoning over read definitions | High |

### Contradiction Log

- **Task text vs. tree**: the task asks to "prove conservative extension results relating L, L⁺" — the tree's own machine-checked `tmCompleteDiscrete_refuted` contradicts the proof-theoretic reading at `.Discrete`. Resolution by precedence: machine-checked theorem > task prose. Recorded as Decision 3; the report delivers the semantic and fragment readings and states the refutation up front.
- **Literature briefing vs. disk**: the briefing's "HIGH PRIORITY" Venema §9.2-9.3 chunk (`9f80f388f5225699`) and the Burgess 1984 §1 chunk resolve to files that do not exist; the same-document material was read from the `sources/` directories instead (`venema_2001/sec03`, `venema_1993_since/sec01`, `burgess_1984/sec08`). No claim rests on the missing chunks.
- **Fine 2012 "conservativity" hits**: ranked 1, 2, 7 by the resolver but concern the pure logic of ground; irrelevant. Ignored deliberately.

### Recommendations modified after verification

- Initially drafted "compactness for L transfers for all rows"; corrected to Base/Dense only after checking that the Discrete/Dedekind witnesses lie outside `range tr`.
- Initially drafted the CEB (Base) refutation as machine-checked; corrected to "source-level, TM half not machine-checkable within `TaskFrame`" after reading `Conservativity.lean`'s CEB section.
- The first injectivity proof for `ofFormula` failed (`simp_all` did not use the IHs); the fixed proof (per-constructor `cases ψ <;> simp [ofFormula] at h <;> rw [ih …]`) compiled and is the one in Appendix A.

## Literature Proof Structure

The only literature proof this task transcribes is semantic (the paper's definition-level validities), plus the two standard conservativity techniques:

1. **Backward direction (both pairs)**: structural recursion on derivation trees with an axiom-discharge table — Burgess 1982 §1.3 lists J₀'s axioms with "mirror images", which is why the repo's `swapTemporal`/TD rule needs `tr_swapBL` (landed) and will need `ofFormula_swapTemporal` (`rfl`-induction) for L⋆.
2. **Forward direction via semantics** ("completeness via completeness", Venema 1993 §1's slogan in a different guise): `⊢⋆ e(φ) ⇒ ⊨⋆ e(φ) ⇒ ⊨ φ ⇒ ⊢ φ`, using soundness of the extension, truth transfer along `e`, and completeness of the base. This works for L⁺⊂L⋆ (base complete) and fails for L⊂L⁺ (base TM incomplete), which is exactly the `tmComplete_iff_forward` reduction.
3. **Stability validities**: from the footnote at line 1118 — S5 because `∼_x` is an equivalence; the Lean proofs are the three symmetry/transitivity rewrites in Appendix A.

## Tactic Survey Results

`lean_run_code` (three runs, imports `FormalSystem.Semantics.Truth` / `FormalSystem.Metalogic.BXCanonical.Completeness`):

| Target | Tactic/term that closed it | Notes |
|---|---|---|
| `ofFormula_injective` | per-constructor `cases ψ <;> simp [ofFormula] at h <;> rw [ih₁ h.1, ih₂ h.2]` | `simp_all` alone fails to apply the IHs |
| `starTruthAt_ofFormula` | `induction φ` + `Iff.rfl`/`Iff.imp`/`forall_congr'`/`exists_congr`/`and_congr` | same shape as `truthAt_tr` |
| `starValid_ofFormula_iff` | `Valid.of_forall_total`, `Valid.apply` | binder conversion only |
| `forward_star_of_sound` | direct application of `BXCanonical.completeness` | engine composes on the nose |
| `of_stab` | `h τ hτ (fun _ _ => rfl)` | needs `τ.IsTotal` |
| `stab_four`, `stab_five` | `rw` with `hσsame (hτ t) hσ'` style instances | `hτ t : τ.domain t` via `IsTotal` unfolding (`isTotal_iff` is `Iff.rfl`) |
| `stab_atom_of_atom` | `obtain`, `rw [← hsame hτ (hσ t)]` | atom clause is a `∃` over the domain proof |
| `sameStateAt_timeShift` | `Iff.rfl` | `timeShift.states` is definitional |
| `ofFormula_ne_stab` | `cases φ <;> simp [ofFormula]` | mirrors `tr_ne_untl` |

## Context Extension Recommendations

- `.claude/context/repo/project-overview.md` is still the generic template; the metatheory map in `FormalSystem/Metalogic.lean`'s docstring is the de facto overview and should be linked from it.
- A short `docs/` note "How to add a language extension" distilled from `BaseLanguage/` + this task would prevent re-deriving the (b) pattern next time (open-future/open-past operators are the obvious next candidates).

## Appendix

### A. Compiled prototypes (verbatim, `lean_run_code`, all `success: true`)

Run 1/2 (import `FormalSystem.Semantics.Truth`):

```lean
namespace FormalSystem.Semantics
open FormalSystem.Syntax

inductive StarFormula : Type where
  | atom : Atom → StarFormula
  | bot : StarFormula
  | imp : StarFormula → StarFormula → StarFormula
  | box : StarFormula → StarFormula
  | untl : StarFormula → StarFormula → StarFormula
  | snce : StarFormula → StarFormula → StarFormula
  | stab : StarFormula → StarFormula
  deriving Repr, DecidableEq, Countable

def ofFormula : Formula → StarFormula
  | .atom a => .atom a
  | .bot => .bot
  | .imp φ ψ => .imp (ofFormula φ) (ofFormula ψ)
  | .box φ => .box (ofFormula φ)
  | .untl φ ψ => .untl (ofFormula φ) (ofFormula ψ)
  | .snce φ ψ => .snce (ofFormula φ) (ofFormula ψ)

theorem ofFormula_injective : Function.Injective ofFormula := by
  intro φ ψ h
  induction φ generalizing ψ with
  | atom a => cases ψ <;> simp_all [ofFormula]
  | bot => cases ψ <;> simp_all [ofFormula]
  | imp φ₁ φ₂ ih₁ ih₂ => cases ψ <;> simp [ofFormula] at h <;> rw [ih₁ h.1, ih₂ h.2]
  | box φ ih => cases ψ <;> simp [ofFormula] at h <;> rw [ih h]
  | untl φ₁ φ₂ ih₁ ih₂ => cases ψ <;> simp [ofFormula] at h <;> rw [ih₁ h.1, ih₂ h.2]
  | snce φ₁ φ₂ ih₁ ih₂ => cases ψ <;> simp [ofFormula] at h <;> rw [ih₁ h.1, ih₂ h.2]

instance : Infinite StarFormula :=
  Infinite.of_injective (fun a => StarFormula.atom a) (fun a b h => by cases h; rfl)
noncomputable instance : Denumerable StarFormula := Classical.choice (nonempty_denumerable _)

theorem ofFormula_ne_stab (φ : Formula) (ψ : StarFormula) : ofFormula φ ≠ StarFormula.stab ψ := by
  cases φ <;> simp [ofFormula]

variable {F : TaskFrame}

/-- `σ ∈ ⟨τ⟩_x` (paper line 1108): same world state at `t`. -/
def SameStateAt (τ σ : WorldHistory F) (t : F.Duration) : Prop :=
  ∀ (hτ : τ.domain t) (hσ : σ.domain t), τ.states t hτ = σ.states t hσ

def StarTruthAt (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) : StarFormula → Prop
  | .atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | .bot => False
  | .imp φ ψ => StarTruthAt M τ t φ → StarTruthAt M τ t ψ
  | .box φ => ∀ (σ : WorldHistory F), σ.IsTotal → StarTruthAt M σ t φ
  | .untl ψ φ => ∃ s : F.Duration, t < s ∧ StarTruthAt M τ s φ ∧
      ∀ r : F.Duration, t < r → r < s → StarTruthAt M τ r ψ
  | .snce ψ φ => ∃ s : F.Duration, s < t ∧ StarTruthAt M τ s φ ∧
      ∀ r : F.Duration, s < r → r < t → StarTruthAt M τ r ψ
  | .stab φ => ∀ (σ : WorldHistory F), σ.IsTotal → SameStateAt τ σ t → StarTruthAt M σ t φ

theorem starTruthAt_ofFormula (M : TaskModel F) (φ : Formula) :
    ∀ (τ : WorldHistory F) (t : F.Duration), StarTruthAt M τ t (ofFormula φ) ↔ TruthAt M τ t φ := by
  induction φ with
  | atom p => intro τ t; exact Iff.rfl
  | bot => intro τ t; exact Iff.rfl
  | imp φ ψ ihφ ihψ => intro τ t; exact Iff.imp (ihφ τ t) (ihψ τ t)
  | box φ ih => intro τ t; exact forall_congr' fun σ => imp_congr_right fun _ => ih σ t
  | untl ψ φ ihψ ihφ =>
    intro τ t
    exact exists_congr fun s => and_congr_right fun _ =>
      and_congr (ihφ τ s) (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ r)
  | snce ψ φ ihψ ihφ =>
    intro τ t
    exact exists_congr fun s => and_congr_right fun _ =>
      and_congr (ihφ τ s) (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ r)

theorem stab_of_box (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula)
    (h : StarTruthAt M τ t (.box φ)) : StarTruthAt M τ t (.stab φ) :=
  fun σ hσ _ => h σ hσ

theorem of_stab (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (φ : StarFormula) (h : StarTruthAt M τ t (.stab φ)) : StarTruthAt M τ t φ :=
  h τ hτ (fun _ _ => rfl)

theorem stab_four (M : TaskModel F) (τ : WorldHistory F) (_hτ : τ.IsTotal) (t : F.Duration)
    (φ : StarFormula) (h : StarTruthAt M τ t (.stab φ)) :
    StarTruthAt M τ t (.stab (.stab φ)) := by
  intro σ hσ hσsame ρ hρ hρsame
  exact h ρ hρ (fun hτ' hρ' => by rw [hσsame hτ' (hσ t), hρsame (hσ t) hρ'])

theorem stab_five (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (φ : StarFormula) (h : ¬ StarTruthAt M τ t (.stab φ)) :
    StarTruthAt M τ t (.stab (.imp (.stab φ) .bot)) := by
  intro σ hσ hσsame hstab
  apply h
  intro ρ hρ hρsame
  exact hstab ρ hρ (fun hσ' hρ' => by rw [← hσsame (hτ t) hσ', ← hρsame (hτ t) hρ'])

theorem stab_atom_of_atom (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (p : Atom)
    (h : StarTruthAt M τ t (.atom p)) : StarTruthAt M τ t (.stab (.atom p)) := by
  intro σ hσ hsame
  obtain ⟨hτ, hv⟩ := h
  exact ⟨hσ t, by rw [← hsame hτ (hσ t)]; exact hv⟩

theorem sameStateAt_timeShift (τ σ : WorldHistory F) (t Δ : F.Duration) :
    SameStateAt (τ.timeShift Δ) (σ.timeShift Δ) t ↔ SameStateAt τ σ (t + Δ) := Iff.rfl
end FormalSystem.Semantics
```

Run 3 (import `FormalSystem.Metalogic.BXCanonical.Completeness`; same definitions, plus):

```lean
def StarValid (φ : StarFormula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F), τ.IsTotal → ∀ t : F.Duration, StarTruthAt M τ t φ

theorem starValid_ofFormula_iff (φ : Formula) : StarValid (ofFormula φ) ↔ Valid φ := by
  constructor
  · intro h; exact Valid.of_forall_total fun F M τ hτ t => (starTruthAt_ofFormula M φ τ t).mp (h F M τ hτ t)
  · intro h F M τ hτ t; exact (starTruthAt_ofFormula M φ τ t).mpr (h.apply F M τ hτ t)

/-- The hard direction of "TM⋆ is conservative over TM⁺" needs only TM⋆ soundness
(a hypothesis here) and the existing TM⁺ completeness — never TM⋆ completeness. -/
theorem forward_star_of_sound
    (StarDerivable : StarFormula → Prop)
    (hsound : ∀ ψ, StarDerivable ψ → StarValid ψ)
    (φ : Formula) (h : StarDerivable (ofFormula φ)) : Derivable FrameClass.Base [] φ :=
  FormalSystem.Metalogic.BXCanonical.completeness φ ((starValid_ofFormula_iff φ).mp (hsound _ h))
```

### B. Web sources consulted

Listed inline in Findings §7.

### C. Literature files read on disk

- `~/Projects/Literature/sources/venema_2001/sec03_since-and-until.md` (Kamp Thm 4.1; Ockhamist clause (5); Peircean-to-Ockhamist translation)
- `~/Projects/Literature/sources/venema_1993_since/sec01_completeness-via-completeness-since-and.md` (§1-2.4)
- `~/Projects/Literature/sources/burgess_1982_i/Burgess_1982_Axioms_for_tense_logic_Since_and_Until.md` (lines 14, 20-65, 98, 254)
- `~/Projects/Literature/sources/burgess_1984/sec08_temporal-conjunctions-eliminability.md` (Props 4.3, 4.5, 4.8; axiomatizability remarks)
- `~/Projects/Literature/sources/reynolds_1992/sec01_an-axiomatization-for-until-and-since-ov.md` (§1-2)
