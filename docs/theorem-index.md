# Theorem Index

**This page is the single per-theorem status ledger for the repository.** Every other surface —
`README.md`, `FormalSystem/README.md`, `FormalSystem/Metalogic/README.md`,
`FormalSystem/Metalogic.lean`, `FormalSystem/Metalogic/Conservativity.lean`, the typst document —
carries a pointer here plus, at most, a five-row highlights table. If two of them disagree, this
page is right and the other is stale.

## How to read a row

| Column | Meaning |
|--------|---------|
| Paper label | The `\label{}` in ["The Construction of Possible Worlds"](https://benbrastmckie.com/publications/possible_worlds.pdf), pinned in [`specs/paper-definitions-of-record.md`](../specs/paper-definitions-of-record.md) and checked by C15. `—` means the result is the formalization's own, with no paper counterpart — compactness, non-compactness and consequence completeness are all in that category. |
| Statement | One line. The Lean statement itself is the authority. |
| Lean name | **Fully qualified, always.** A bare base identifier is not a row key: it can name declarations in more than one namespace, and the File column alone does not disambiguate them. `completeness_dense` and `completeness_ztime` used to do exactly that — the `BXCanonical` engines have since been renamed `derivable_of_validDense` / `derivable_of_validZTime`, but the convention stands for every row. |
| File | Path only. **No line numbers**: cite declaration names, never `file:line`. |
| Frame class | The `FrameClass` the result is stated at: `Base`, `Dense`, `ZTime`, `RTime`. `—` where the result is class-generic. |
| Axioms | `pcq` abbreviates exactly `[propext, Classical.choice, Quot.sound]`; anything else is written out literally. `pinned:C2` / `pinned:C14` names the check in `scripts/check-module-invariants.sh` that asserts the value on every build — the column is generated from those baselines, never typed. `claimed` would mean prose-only; no row currently reads that. |

Every declaration listed here is machine-pinned. To re-derive the whole column:

```bash
bash scripts/check-module-invariants.sh        # C2 and C14 assert every value below
```

## Notation and naming

The paper and the formalization use different vocabularies for the same objects. This table is
the mapping.

| Paper term | Lean identifier | Notes |
|------------|-----------------|-------|
| task frame | `FormalSystem.Semantics.TaskFrame` | `def:frame`; four axioms — Compositionality, Seriality, Limit, Saturation. Nullity is *derived*, not an axiom |
| world history / possible world | `FormalSystem.Semantics.WorldHistory` | `def:world-history`; a total history is a possible world |
| task relation `w ⇒ₓ v` | `TaskFrame.TaskRel` | `def:task-relation` |
| duration group `D` | `FormalSystem.Semantics.TemporalOrder` | `def:temporal-order`; a nontrivial totally ordered abelian group |
| TM⁺ | `FormalSystem.ProofSystem` over `FrameClass.Base` | `def:TMplus` |
| TM⁺_d (dense) | `FrameClass.Dense` | `def:BX-d` |
| TM⁺_z (ℤ-time) | `FrameClass.ZTime` | `def:BX-z`. The tree says `ZTime`, not `Discrete` |
| TM⁺_r (dense and Dedekind-complete) | `FrameClass.RTime` | `def:BX-r`. The tree says `RTime`, not `Dedekind` |
| BL (tense-primitive base language) | `FormalSystem.BaseLanguage` | `def:BL-semantics`; its truth relation is `Semantics.BLTruthAt`, a native six-clause recursion, **not** `TruthAt ∘ tr` |
| L⋆ / TM⋆ (stability modal `⊡`) | `FormalSystem.StarLanguage` | truth relation `Semantics.StarTruthAt` |
| `U(φ, ψ)` (until) | `Formula.untl ψ φ` | guard-first: `untl guard event` |
| `S(φ, ψ)` (since) | `Formula.snce ψ φ` | guard-first |
| `△φ` / `▽φ` | `Formula.always` / `Formula.sometimes` | derived, not primitive |
| `Xφ` / `Yφ` | `Formula.next` / `Formula.prev` | derived from `untl`/`snce` |
| validity on a frame class | `FrameClass.Sat` (`FormalSystem/Semantics/FrameClassValidity.lean`) | `def:frame-validity` |
| axiomatizability / Galois closure | `Semantics.Th` / `Semantics.Mod` | `Semantics/Correspondence/Galois.lean` |
| weak completeness | `WeakCompleteness fc` | one formula |
| finite-context consequence completeness | `consequence_completeness_*` | `Context = List Formula`; inter-derivable with the weak form through the deduction theorem. **Not** strong completeness |
| strong completeness | `StrongCompleteness fc` | consequence from a possibly-infinite `Γ : Set Formula` under `SetDerivable` |

## The ledger

### Soundness

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| `thm:TM-soundness` | TM⁺ is sound over all task frames | `FormalSystem.Metalogic.soundness` | `FormalSystem/Metalogic/Soundness.lean` | Base | pcq pinned:C14 |
| `thm:TM-soundness` | TM⁺_d is sound over the densely ordered task frames | `FormalSystem.Metalogic.soundness_dense` | `FormalSystem/Metalogic/Soundness.lean` | Dense | pcq pinned:C14 |
| `thm:TM-soundness` | TM⁺_z is sound over ℤ-time | `FormalSystem.Metalogic.soundness_ztime` | `FormalSystem/Metalogic/Soundness.lean` | ZTime | pcq pinned:C14 |
| `thm:TM-soundness` | TM⁺_r is sound over the dense Dedekind-complete task frames | `FormalSystem.Metalogic.soundness_rtime` | `FormalSystem/Metalogic/Soundness.lean` | RTime | pcq pinned:C14 |

### Weak completeness — the engines

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| `cor:tm-completeness` | Weak completeness over all task frames, by the chronicle construction | `FormalSystem.Metalogic.BXCanonical.completeness` | `FormalSystem/Metalogic/BXCanonical/Completeness.lean` | Base | pcq pinned:C2 |
| `cor:tm-completeness` | Weak completeness over the dense class, by the chronicle construction | `FormalSystem.Metalogic.BXCanonical.derivable_of_validDense` | `FormalSystem/Metalogic/BXCanonical/Completeness.lean` | Dense | pcq pinned:C2 |
| `cor:tm-completeness` | Weak completeness over ℤ-time, by the chronicle construction | `FormalSystem.Metalogic.BXCanonical.derivable_of_validZTime` | `FormalSystem/Metalogic/BXCanonical/Completeness.lean` | ZTime | pcq pinned:C2 |
| `cor:tm-completeness` | Weak completeness over the dense Dedekind-complete class, on the real line | `FormalSystem.Metalogic.BXCanonical.completeness_rtime_engine` | `FormalSystem/Metalogic/BXCanonical/CompletenessDedekind.lean` | RTime | pcq pinned:C14 |

### Weak completeness — the `WeakCompleteness` termini

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| `cor:tm-completeness` | `WeakCompleteness FrameClass.Base`, the corollary of consequence completeness | `FormalSystem.Metalogic.completeness_base` | `FormalSystem/Metalogic/StrongCompleteness.lean` | Base | pcq pinned:C14 |
| `cor:tm-completeness` | `WeakCompleteness FrameClass.Dense` | `FormalSystem.Metalogic.completeness_dense` | `FormalSystem/Metalogic/StrongCompleteness.lean` | Dense | pcq pinned:C14 |
| `cor:tm-completeness` | `WeakCompleteness FrameClass.ZTime` | `FormalSystem.Metalogic.completeness_ztime` | `FormalSystem/Metalogic/StrongCompleteness.lean` | ZTime | pcq pinned:C14 |
| `cor:tm-completeness` | `WeakCompleteness FrameClass.RTime` | `FormalSystem.Metalogic.completeness_rtime` | `FormalSystem/Metalogic/StrongCompleteness.lean` | RTime | pcq pinned:C14 |

### Finite-context consequence completeness

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | Finite-context consequence completeness against `SemanticConsequence` | `FormalSystem.Metalogic.consequence_completeness_base` | `FormalSystem/Metalogic/StrongCompleteness.lean` | Base | pcq pinned:C14 |
| — | Finite-context consequence completeness against `SemanticConsequenceDense` | `FormalSystem.Metalogic.consequence_completeness_dense` | `FormalSystem/Metalogic/StrongCompleteness.lean` | Dense | pcq pinned:C14 |
| — | Finite-context consequence completeness against `SemanticConsequenceZTime` | `FormalSystem.Metalogic.consequence_completeness_ztime` | `FormalSystem/Metalogic/StrongCompleteness.lean` | ZTime | pcq pinned:C14 |
| — | Finite-context consequence completeness against `SemanticConsequenceRTime` | `FormalSystem.Metalogic.consequence_completeness_rtime` | `FormalSystem/Metalogic/StrongCompleteness.lean` | RTime | pcq pinned:C14 |

### Compactness and strong completeness

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | `CompactBase`, by ultraproduct model existence over the finite sublists | `FormalSystem.Metalogic.compactBase` | `FormalSystem/Metalogic/Compactness.lean` | Base | pcq pinned:C14 |
| — | `CompactDense`, by ultraproduct model existence over the finite sublists | `FormalSystem.Metalogic.compactDense` | `FormalSystem/Metalogic/Compactness.lean` | Dense | pcq pinned:C14 |
| — | Strong completeness for `Γ : Set Formula` | `FormalSystem.Metalogic.strongCompletenessBase` | `FormalSystem/Metalogic/Compactness.lean` | Base | pcq pinned:C14 |
| — | Strong completeness for `Γ : Set Formula` | `FormalSystem.Metalogic.strongCompletenessDense` | `FormalSystem/Metalogic/Compactness.lean` | Dense | pcq pinned:C14 |

### Non-compactness — the two refutations

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | `¬ CompactZTime`: `{F p} ∪ {¬Xⁿ p}` is finitely satisfiable over ℤ, unsatisfiable on any Archimedean discrete carrier | `FormalSystem.Metalogic.notCompactZTime` | `FormalSystem/Metalogic/DiscreteNonCompactness.lean` | ZTime | pcq pinned:C14 |
| — | `¬ StrongCompletenessZTime`, the companion refutation | `FormalSystem.Metalogic.notStrongCompletenessZTime` | `FormalSystem/Metalogic/DiscreteNonCompactness.lean` | ZTime | pcq pinned:C14 |
| — | `¬ CompactRTime`: the `{G(⊤ S ¬q), F(G ¬q)} ∪ {Xqⁿ⊤}` witness, finitely satisfiable over ℝ | `FormalSystem.Metalogic.notCompactRTime` | `FormalSystem/Metalogic/DedekindNonCompactness.lean` | RTime | pcq pinned:C14 |
| — | `¬ StrongCompletenessRTime`, the companion refutation | `FormalSystem.Metalogic.notStrongCompletenessRTime` | `FormalSystem/Metalogic/DedekindNonCompactness.lean` | RTime | pcq pinned:C14 |

### Decidability

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | The tableau decision procedure | `FormalSystem.Metalogic.Decidability.decide` | `FormalSystem/Metalogic/Decidability/DecisionProcedure.lean` | Base | pcq pinned:C14 |
| — | Soundness of the decision procedure: a valid verdict yields validity | `FormalSystem.Metalogic.Decidability.sound_of_isValid` | `FormalSystem/Metalogic/Decidability/Correctness.lean` | Base | pcq pinned:C14 |

### Characterization and definability

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| `app:dense` | `Sat .Dense` is Galois-closed, via the `nextTop` indicator | `FormalSystem.Semantics.galoisClosed_sat_dense` | `FormalSystem/Semantics/Correspondence/Indicator.lean` | Dense | pcq pinned:C14 |
| `app:discrete` | `{F | F.IsDiscrete}` is Galois-closed, via the `nextTop` indicator | `FormalSystem.Semantics.galoisClosed_isDiscrete` | `FormalSystem/Semantics/Correspondence/Indicator.lean` | ZTime | pcq pinned:C14 |
| — | A frame class is axiomatizable iff it is Galois-closed under `Th`/`Mod` | `FormalSystem.Semantics.galoisClosed_mod` | `FormalSystem/Semantics/Correspondence/Galois.lean` | — | `[propext]` pinned:C14 |
| — | Closure from one indicator formula valid on precisely the class's members | `FormalSystem.Semantics.galoisClosed_of_indicator` | `FormalSystem/Semantics/Correspondence/Galois.lean` | — | pcq pinned:C14 |
| `app:complete` | `Sat .RTime ⊊ Mod (AxiomSet .RTime)` — the narrowing is not Galois-closed | `FormalSystem.Metalogic.Independence.sat_rtime_ssubset_mod_axiomSet` | `FormalSystem/Metalogic/Independence/RationalWitness.lean` | RTime | pcq pinned:C14 |
| `app:discrete` | `Sat .ZTime ⊊ Mod (AxiomSet .ZTime)` — the narrowing is not Galois-closed | `FormalSystem.Metalogic.Independence.sat_ztime_ssubset_mod_axiomSet` | `FormalSystem/Metalogic/Independence/LexIntWitness.lean` | ZTime | pcq pinned:C14 |
| `app:deterministic` | No set of `StarFormula`s defines `TaskFrame.Deterministic` | `FormalSystem.Metalogic.Independence.deterministic_not_starDefinable` | `FormalSystem/Metalogic/Independence/DeterminismUndefinable.lean` | — | pcq pinned:C14 |

### Conservativity — TM over BL, TM⁺ over TM, TM⋆ over TM⁺

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | `TM ⊢ φ ⟹ TM⁺ ⊢ tr φ`, the backward bridge | `FormalSystem.Metalogic.Conservativity.derivable_translate` | `FormalSystem/Metalogic/Conservativity/Backward.lean` | — | pcq pinned:C14 |
| — | CEB row corollary of the backward bridge | `FormalSystem.Metalogic.Conservativity.ceb_backward` | `FormalSystem/Metalogic/Conservativity/Backward.lean` | Base | pcq pinned:C14 |
| — | CEF row corollary of the backward bridge | `FormalSystem.Metalogic.Conservativity.cef_backward` | `FormalSystem/Metalogic/Conservativity/Backward.lean` | ZTime | pcq pinned:C14 |
| — | CED row corollary of the backward bridge | `FormalSystem.Metalogic.Conservativity.ced_backward` | `FormalSystem/Metalogic/Conservativity/Backward.lean` | Dense | pcq pinned:C14 |
| — | CEC row corollary of the backward bridge | `FormalSystem.Metalogic.Conservativity.cec_backward` | `FormalSystem/Metalogic/Conservativity/Backward.lean` | RTime | pcq pinned:C14 |
| — | Soundness of the H/G-fragment `TMFrag` | `FormalSystem.Metalogic.Conservativity.tmFrag_sound` | `FormalSystem/Metalogic/Conservativity/Fragment.lean` | — | pcq pinned:C14 |
| — | Completeness of `TMFrag` at all four frame classes | `FormalSystem.Metalogic.Conservativity.tmFrag_complete` | `FormalSystem/Metalogic/Conservativity/Fragment.lean` | — | pcq pinned:C14 |
| — | `TM ≤ TMFrag` everywhere | `FormalSystem.Metalogic.Conservativity.tm_le_tmFrag` | `FormalSystem/Metalogic/Conservativity/Fragment.lean` | — | pcq pinned:C14 |
| — | `TM ⊊ TMFrag` at ℤ-time | `FormalSystem.Metalogic.Conservativity.tm_lt_tmFrag_ztime` | `FormalSystem/Metalogic/Conservativity/Fragment.lean` | ZTime | pcq pinned:C14 |
| — | Proof-theoretic conservativity of TM⋆ over TM⁺, both directions, all four classes | `FormalSystem.Metalogic.Conservativity.starDerivable_ofFormula_iff` | `FormalSystem/Metalogic/Conservativity/Star/Forward.lean` | — | pcq pinned:C14 |
| — | Soundness of TM⋆ at every frame class | `FormalSystem.Metalogic.Conservativity.star_soundness_validIn` | `FormalSystem/Metalogic/Conservativity/Star/StarSoundness.lean` | — | pcq pinned:C14 |
| — | Semantic conservativity of L⋆ over L⁺ | `FormalSystem.Semantics.starValidIn_ofFormula_iff` | `FormalSystem/Semantics/StarValidity.lean` | — | `[propext]` pinned:C14 |

### Base-language soundness

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | Soundness of BL against the native `BLTruthAt` semantics | `FormalSystem.Metalogic.bl_soundness` | `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | Base | pcq pinned:C14 |
| — | BL soundness over the dense class | `FormalSystem.Metalogic.bl_soundness_dense` | `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | Dense | pcq pinned:C14 |
| — | BL soundness over ℤ-time | `FormalSystem.Metalogic.bl_soundness_ztime` | `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | ZTime | pcq pinned:C14 |
| — | BL soundness over the dense Dedekind-complete class | `FormalSystem.Metalogic.bl_soundness_rtime` | `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | RTime | pcq pinned:C14 |
| — | Consistency of BL: `⊬ ⊥` | `FormalSystem.Metalogic.bl_not_derivable_nil_bot` | `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` | Base | pcq pinned:C14 |

### Expressiveness

| Paper label | Statement | Lean name | File | Frame class | Axioms |
|-------------|-----------|-----------|------|-------------|--------|
| — | `{U, S}` is expressively complete for Prior structures relative to monadic FO | `FormalSystem.Metalogic.WeakCanonical.Kamp.kampPriorExpressiveCompleteness` | `FormalSystem/Metalogic/WeakCanonical/Kamp/KampPrior.lean` | — | pcq pinned:C14 |
| — | The load-bearing corollary consumed by the live completeness chain | `FormalSystem.Metalogic.WeakCanonical.uSExpressivelyCompleteOverPrior` | `FormalSystem/Metalogic/WeakCanonical/PriorExpressiveness.lean` | — | pcq pinned:C14 |

## Statuses that are refutations, not gaps

Three of the rows above are negative results, and they are easy to misread as unfinished work:

- **Strong completeness at `ZTime` and `RTime` is machine-refuted**, not open.
  `notStrongCompletenessZTime` and `notStrongCompletenessRTime` settle both negatively, which is
  why only the weak forms appear for those two classes.
- **Forward proof-theoretic conservativity of TM⁺ over TM is refuted at `Base` and `ZTime`** and
  open at `Dense` and `RTime`. `FormalSystem/Metalogic/Conservativity.lean` carries the standing
  prohibition on attempting or `sorry`-ing it; that record is the authority on the CEB/CEF/CED/CEC
  rows, this page on their per-theorem status.
- **The `Sat` narrowings are not Galois-closed** at `ZTime` and `RTime`
  (`sat_ztime_ssubset_mod_axiomSet`, `sat_rtime_ssubset_mod_axiomSet`). This is a statement about
  definability of the model class, a different property from strong completeness. Closed-form
  characterizations of `Mod (AxiomSet .ZTime)` and `Mod (AxiomSet .RTime)` remain open and are
  not promised.

## Related documentation

- [`README.md`](../README.md) — project overview and the `## Verifying the main theorems` recipe
- [`FormalSystem/Metalogic/README.md`](../FormalSystem/Metalogic/README.md) — the directory's
  generated inventory and the three completeness routes
- [`FormalSystem/Metalogic.lean`](../FormalSystem/Metalogic.lean) — the module docstring, whose
  every SORRY-FREE claim is pinned by C2 or C14
- [`specs/paper-definitions-of-record.md`](../specs/paper-definitions-of-record.md) — the pinned
  paper anchors C15 resolves against

## Tags

theorem-index · soundness · completeness · compactness · non-compactness · decidability · conservativity · correspondence · expressiveness
