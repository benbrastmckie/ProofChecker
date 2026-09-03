# PFilter Maximality Design Spike — Option (c) Verified in Lean

**Task**: 528 — Algebraic modernisation (propDecide + Mathlib filters)
- **Started**: 2026-09-03
- **Completed**: 2026-09-03
- **Effort**: Single research session (three scratch Lean files compiled against the pinned tree; see Appendix C)
- **Dependencies**: reports/01_algebraic-modernisation-verification.md; plans/01_algebraic-modernisation-propdecide-mathlib.md (Decision D1)
- **Sources/Inputs**: `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean`; pinned Mathlib `79d0395a` (`Order/PFilter.lean`, `Order/Ideal.lean`, `Order/PrimeIdeal.lean`, `Order/PrimeSeparator.lean`); upstream mathlib4 master fetched 2026-09-03
- **Artifacts**: this report (scratch files discarded; no repository source touched)
- **Standards**: `.claude/context/formats/report-format.md`
**Scope**: Decision D1 only. Resolve, empirically, whether the bespoke `structure Ultrafilter`
in `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean:44-59` should be replaced by an
`Order.PFilter`-based encoding, and what the highest-quality organisation of that layer is.
**Method**: three scratch files compiled with `lake env lean` against the pinned tree
(Lean `v4.33.0-rc1`, Mathlib `79d0395a`), then discarded. No file under `FormalSystem/` was
touched; `git status` shows no source change; `scripts/check-module-invariants.sh --no-build`
passes (ALL CHECKS PASSED); the C2 baseline is trivially unchanged because the tree was not
edited.
**Date**: 2026-09-03

---

## 1. Recommendation (for the planner)

**Adopt option (c).** Replace the bespoke seven-field `Ultrafilter` with Mathlib's
`Order.PFilter` plus its existing `Order.PFilter.IsPrime`, supplying the small missing
`IsProper`/`IsMaximal` layer in a Mathlib-shaped file. Every claim below was built and compiled;
nothing is on paper.

The headline findings, each with its evidence section:

| # | Claim | Result | Evidence |
|---|---|---|---|
| F1 | Mathlib's `Ultrafilter α` is a filter on `Set α`; `≃ Ultrafilter LindenbaumAlg` is the wrong target type | **Confirmed** | §2 |
| F2 | Two dualities (order-dual vs Boolean-complement) were conflated by the plan | **Confirmed**, and the order-dual one is `Iff.rfl` | §3 |
| F3 | All seven bespoke fields derive from `PFilter` + one predicate | **Confirmed — and stronger**: the one predicate is `IsPrime`, which *already exists*. `IsProper` is derivable from it (`IsPrime.toIsProper`). The gap the orchestrator named is smaller than stated. | §4 |
| Q3 | `Ideal.IsMaximal` transports across `ᵒᵈ` | **Yes**, cleanly; instance path is automatic | §5 |
| Q4 | The 1,071-line consumer ports mechanically | **Yes**: the hardest site (100-line `ultrafilterToSet_mcs`) ported by textual substitution with zero proof-step changes | §6 |
| Q5 | Cost vs (a)/(b) | (c) is **cheaper than (b)** and strictly cleaner: the bridge that (b) would write by hand is `IsPrime.toPrimePair`, already in Mathlib | §7 |
| Q7 | Upstream-contributable | **Yes**; upstream master (fetched 2026-09-03) still lacks all of it, including a `TODO` in `Order/PrimeSeparator.lean` that E3 closes in four lines | §9 |
| Q8 | Anything disqualifying | **None found.** Four small frictions, all handled; listed in §10 | §10 |

Three genuinely open choices are surfaced in §11 rather than settled here (file location,
bundled-type name, whether to define `IsMaximal` at all). Each has a recommendation and the
evidence for and against.

---

## 2. Finding 1 — `Ultrafilter LindenbaumAlg` is the wrong type (confirmed)

`.lake/packages/mathlib/Mathlib/Order/Filter/Ultrafilter/Defs.lean:41`:

```lean
structure Ultrafilter (α : Type*) extends Filter α where
  protected neBot' : NeBot toFilter
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g
```

with `instance : Membership (Set α) (Ultrafilter α)`. So `Ultrafilter LindenbaumAlg` is an
ultrafilter on the *powerset* `Set LindenbaumAlg`, whose members are sets of equivalence classes.
It is not an ultrafilter *of* the Boolean algebra `LindenbaumAlg`. The type
`{Γ // SetMaximalConsistent Γ} ≃ Ultrafilter LindenbaumAlg` in the task description, the plan
(Phase 4 line 443) and the prior report (Item 2) is therefore mathematically wrong — it would
only be reachable by shadowing, which is exactly the hazard the task exists to remove.

Mathlib has no general Boolean-algebra ultrafilter. `Order/Ideal.lean:29-30` says of
`Order.Ideal.IsMaximal`: "Dual to the notion of an ultrafilter", and supplies only the ideal.
`Order/PFilter.lean` (grep, full pinned checkout) defines `PFilter`, `IsPFilter`, `principal`,
`top_mem`, `inf_mem` and the `sInf` Galois connection — no `IsProper`, no `IsMaximal`.
`Order/PrimeIdeal.lean:194` supplies `PFilter.IsPrime` and nothing else on the filter side.

**Corrected target signature** (built and compiled in E2, §6):

```lean
noncomputable def SetMaximalConsistent.ultrafilterEquiv :
    {Γ : Set Formula // SetMaximalConsistent (fc := FrameClass.Base) Γ} ≃
      Order.PrimeFilter LindenbaumAlg
```

where `Order.PrimeFilter P := {F : Order.PFilter P // F.IsPrime}` (§4.3, name open in §11).

---

## 3. Finding 2 — two dualities, one of them free (confirmed)

`Order/PFilter.lean:45`: `structure PFilter (P) [Preorder P] where dual : Ideal Pᵒᵈ`, with
`mem_mk : x ∈ ⟨I⟩ ↔ toDual x ∈ I := Iff.rfl`. Measured in E1: **all four** of the following are
`Iff.rfl` on the pinned Mathlib:

```lean
theorem mem_dual_iff  : toDual x ∈ F.dual ↔ x ∈ F                                    := Iff.rfl
theorem le_iff_dual_le : F ≤ G ↔ F.dual ≤ G.dual                                    := Iff.rfl
theorem lt_iff_dual_lt : F < G ↔ F.dual < G.dual                                    := Iff.rfl
theorem coe_eq_univ_iff : (F : Set P) = Set.univ ↔ (F.dual : Set Pᵒᵈ) = Set.univ    := Iff.rfl
```

and on a Boolean algebra `(toDual x)ᶜ = toDual xᶜ` is `rfl` (`OrderDual.instBooleanAlgebra`,
`Order/BooleanAlgebra/Basic.lean:540`). This is the order dual: vocabulary is preserved
(`a ∈ U` stays "Γ accepts `a`"), and Mathlib's ideal theorems transport by `Iff.rfl`-level
plumbing.

Option (a)'s duality is the Boolean complement: `a ∈ U ↔ aᶜ ∈ I`. It is *not* free — it is the
content of `Order.Ideal.isPrime_iff_mem_or_compl_mem` and friends — and it inverts every
downstream statement. For the Jonsson–Tarski consumers the embedding is `η(a) = {U | a ∈ U}`
over filters; under (a) it becomes `{I | aᶜ ∈ I}`, and every accessibility relation on `Uf(A)`
(the Boneyard seed's `R_G`, `R_Box`, `R_H` at `UltrafilterFrame.lean:82-98` are all stated as
`∀ a, □a ∈ U → a ∈ V`) acquires a complement on both sides. Under (c) they port verbatim.

Note that (c) does not lose (a)'s ideal: for `U : PrimeFilter P`, `U.2.toPrimePair.I` is the
set-complement ideal (`Order/PrimeIdeal.lean:207`), which on a Boolean algebra is precisely
`{a | aᶜ ∈ U}`. The bridge (b) proposed to write by hand is a Mathlib projection.

---

## 4. Finding 3 — every bespoke field derives, and the primitive is `IsPrime`

### 4.1 The derivation table (all compiled, E1)

| Bespoke field (`UltrafilterMCS.lean:44-59`) | Source under (c) | Status |
|---|---|---|
| `carrier` | `SetLike (PFilter P) P` coercion, `x ∈ F` | Mathlib |
| `mem_of_le` | `Order.PFilter.mem_of_le` (`PFilter.lean:88`) | Mathlib |
| `inf_mem` | `Order.PFilter.inf_mem` (`PFilter.lean:141`, `[SemilatticeInf P]`) | Mathlib |
| `top_mem` | `Order.PFilter.top_mem` (`PFilter.lean:126`, `[OrderTop P]`) | Mathlib |
| `bot_not_mem` | `IsProper.bot_notMem`, and `IsProper` from `IsPrime.toIsProper` | **new, 3 lines** |
| `compl_or` | `IsPrime.mem_or_compl_mem` — `x ⊔ xᶜ = ⊤ ∈ F`, complement-ideal splits | **new, 6 lines** |
| `compl_not` | `IsPrime.compl_notMem_of_mem` via `IsProper.notMem_of_compl_mem` — `x ⊓ xᶜ = ⊥` | **new, 2 lines** |

None resisted. The only false start was a direct proof of `IsMaximal.isPrime`, which failed
because Mathlib gives `PFilter` no lattice (`failed to synthesize Max (PFilter P)`); routing
it through the dual (`Ideal.IsMaximal.isPrime` on `Pᵒᵈ`) made it a one-liner (§5).

### 4.2 The right primitive: `IsPrime`, not `IsMaximal`, not `IsProper + IsPrime`

The orchestrator hypothesised the gap is `IsProper`. Measured: **`Order.PFilter.IsPrime`
already implies proper**, because its single field `compl_ideal : IsIdeal (F : Set P)ᶜ` bundles
`IsIdeal.Nonempty` — a nonempty complement is a witness of non-universality:

```lean
instance (priority := 100) IsPrime.toIsProper [h : IsPrime F] : IsProper F :=
  let ⟨_, hp⟩ := h.compl_ideal.Nonempty
  isProper_of_notMem hp
```

So on a Boolean algebra, `{F : PFilter α // F.IsPrime}` *is* the ultrafilter type with no
predicate of ours in the type at all. The prior report's sentence "Mathlib defines `IsMaximal`
only for `Order.Ideal`, never for `Order.PFilter` (which has only `IsPrime`). The PFilter option
is dropped" drew the wrong conclusion from a correct fact: `IsPrime` was sufficient.

Comparison of the three candidate primitives:

| Primitive | Exists in Mathlib | On a BA equals ultrafilter | API quality | Verdict |
|---|---|---|---|---|
| `IsPrime` | yes (`PrimeIdeal.lean:194`) | yes (E1: `IsPrime.isMaximal`, `IsMaximal.isPrime`) | direct: `mem_or_compl_mem` is what every consumer uses; `toPrimePair` gives the ideal for free | **use as the type's predicate** |
| `IsProper ∧ IsPrime` | no / yes | yes | redundant — `IsProper` is implied | reject |
| `IsMaximal` | no | yes | needed only as the *transport target* of `Ideal.IsProper.exists_le_maximal` | **define it, but do not put it in the type** |
| `Ideal.PrimePair` | yes | yes | a *pair* (ideal, filter, `IsCompl`); heavier than needed as a carrier, but the right vehicle when both sides are wanted | use ad hoc via `IsPrime.toPrimePair`; not the carrier |

`IsMaximal` earns its place for two reasons: Lindenbaum's lemma on the filter side is
`IsProper.exists_le_maximal` transported from `Order/Ideal.lean:642`, and it is what a Mathlib
PR would have to contain to mirror the ideal file. On a Boolean algebra it is then *converted*
to `IsPrime` (`IsMaximal.isPrime`, valid already on any distributive lattice by transport).

### 4.3 The bundled type

Mathlib's precedent for "bundle an ideal with its primeness" is
`structure PrimeSpectrum R where asIdeal : Ideal R; isPrime : asIdeal.IsPrime` with a `SetLike`
instance. The subtype form is lighter and needs no `ext` boilerplate of its own:

```lean
abbrev Order.PrimeFilter (P : Type*) [Preorder P] := {F : PFilter P // F.IsPrime}

instance : SetLike (PrimeFilter P) P where
  coe U := U.1
  coe_injective := fun _ _ h => Subtype.ext (SetLike.coe_injective h)

instance (U : PrimeFilter P) : U.1.IsPrime := U.2
@[ext] theorem PrimeFilter.ext {U V : PrimeFilter P} (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V := SetLike.ext h
```

Downstream statements then read exactly as the Boneyard seed writes them
(`x ∈ U`, `PFilter.inf_mem hx hy`, `U.2.mem_or_compl_mem`), and
`def eta (a : P) : Set (PrimeFilter P) := {U | a ∈ U}` compiles as written.

---

## 5. Question 3 — dual transport of `Ideal.IsMaximal` (clean)

All three predicates transport, with the `IsProper` case reusing the ideal's own field
(E1, zero warnings):

```lean
theorem isProper_iff_dual  : F.IsProper  ↔ F.dual.IsProper  := ⟨fun h => ⟨h.ne_univ⟩, fun h => ⟨h.ne_univ⟩⟩
theorem isMaximal_iff_dual : F.IsMaximal ↔ F.dual.IsMaximal   -- 6 lines; `G ↦ G.dual`, `J ↦ ⟨J⟩`
theorem isPrime_iff_dual   : F.IsPrime   ↔ F.dual.IsPrime     -- 4 lines; `compl_ideal` ↔ `compl_filter` are the same term
```

**Instance path**: `Ideal.IsProper.exists_le_maximal` needs `[LE P] [OrderTop P]` on the ideal
side. For `F : PFilter P` with `[Preorder P] [OrderBot P]`, the dual `Pᵒᵈ` gets `LE` and
`OrderTop` from `Order/BoundedOrder/Basic.lean:238` automatically; no manual instance was
written anywhere:

```lean
theorem IsProper.exists_le_maximal [Preorder P] [OrderBot P] (hF : F.IsProper) :
    ∃ G, F ≤ G ∧ G.IsMaximal := by
  obtain ⟨J, hJ, hJm⟩ := (isProper_iff_dual.1 hF).exists_le_maximal
  exact ⟨⟨J⟩, hJ, isMaximal_iff_dual.2 hJm⟩

instance (priority := 100) IsMaximal.isPrime [DistribLattice P] [hF : IsMaximal F] : IsPrime F :=
  isPrime_iff_dual.2 (@Ideal.IsMaximal.isPrime Pᵒᵈ _ F.dual (isMaximal_iff_dual.1 hF))

theorem IsProper.exists_le_prime [BooleanAlgebra P] (hF : F.IsProper) : ∃ G, F ≤ G ∧ G.IsPrime
```

`#print axioms Order.PFilter.IsProper.exists_le_prime` → `[propext, Classical.choice, Quot.sound]`.

**On the "sorry in `Order/PrimeSeparator.lean:125`"**: it is not a compiled `sorry`. Lines
123-125 are a commented-out `-- TODO: Define prime filters in Mathlib so that the following
corollary can be stated and proved` followed by the statement and `:= by sorry` inside the
comment. E3 states and proves that exact corollary by dual transport (`Disjoint` flips with
`.symm`, the ideal `I` is read as `⟨I⟩ : PFilter αᵒᵈ` definitionally):

```lean
theorem DistribLattice.prime_filter_of_disjoint_filter_ideal [DistribLattice α]
    {F : PFilter α} {I : Ideal α} (hFI : Disjoint (F : Set α) (I : Set α)) :
    ∃ G : PFilter α, G.IsPrime ∧ F ≤ G ∧ Disjoint (G : Set α) I := by
  have h : Disjoint ((⟨I⟩ : PFilter αᵒᵈ) : Set αᵒᵈ) (F.dual : Set αᵒᵈ) := hFI.symm
  obtain ⟨J, hJ, hFJ, hJI⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal h
  exact ⟨⟨J⟩, PFilter.isPrime_iff_dual.2 hJ, hFJ, hJI.symm⟩
```

This is the Zorn-free prime-filter separator that the description of the ultrafilter-frame task
names as the intended hook for `Uf(A)`-nonemptiness. It is a four-line theorem once
`isPrime_iff_dual` exists.

---

## 6. Question 4 — does the consumer port mechanically? (yes, measured)

E2 imports the live `FormalSystem.Metalogic.Algebraic.UltrafilterMCS`, adds the generic layer,
and re-derives the sampled hard sites against `PrimeFilter LindenbaumAlg`. It compiles with
exit 0 and `#print axioms ultrafilterEquiv'` shows no `sorryAx`. Site by site:

| Site (current) | Lines now | Under (c) | Nature of change |
|---|---|---|---|
| `structure Ultrafilter` + `Membership` + `ext` + `empty_not_mem` (:44-81) | 38 | 0 | deleted; Mathlib supplies all four |
| `mcsToUltrafilter` six field proofs (:524-532) | 9 + the 5 field lemmas it cites | `IsPFilter.of_def` over 3 of the same lemmas (5 lines) + two `instance`s over the other 2 (4 lines) + `⟨_, inferInstance⟩` (1 line) | the five `mcsToSet_*` lemmas are **reused unchanged** as the filter/proper/prime witnesses |
| `mcsToUltrafilter_carrier`, `mem_mcsToUltrafilter_iff` (:538-556) | 19 | 1 (`Iff.rfl`) | membership is definitional through `IsPFilter.toPFilter` |
| `ultrafilterToSet_mcs` (:674-773) — the hardest site, uses all five fields | 100 | 98 | **textual substitution only**: `U.carrier` → `U` (x18), `U.top_mem` → `PFilter.top_mem`, `U.inf_mem` → `PFilter.inf_mem`, `U.mem_of_le` → `PFilter.mem_of_le`, `U.bot_not_mem` → `U.2.toIsProper.bot_notMem`, the `cases U.compl_or` block → `U.2.compl_mem_of_notMem hφ`; zero proof-step changes |
| `ultrafilter_correspondence` (:782-905) | 127 | 6 | becomes a corollary `⟨e, e.symm, e.left_inv, e.right_inv⟩` of the `Equiv` |
| `Ultrafilter.compl_xor`, `mem_iff_compl_not_mem`, `not_mem_iff_compl_mem` (:910-947) | 38 | 0 | these *are* `IsPrime.mem_iff_compl_notMem` / `compl_mem_iff_notMem` in the generic layer |
| `ultrafilter_neg_iff`, `ultrafilter_neg_iff'` (:950-966) | 17 | 6 | one-liners: `U.2.mem_iff_compl_notMem`, `U.2.compl_mem_iff_notMem (x := toQuot φ)` — `(toQuot φ)ᶜ = toQuot φ.neg` is `rfl` |
| `ultrafilter_mcs_round_trip` (:983-1053) | 72 | 0 | subsumed by `Equiv.left_inv` |
| `mcs_ultrafilter_round_trip` (:1056-1069) | 14 | 0 | subsumed by `Equiv.right_inv` |

**Real re-derivation needed: none.** Every one of the ~63 `Ultrafilter` and ~46 `carrier`
occurrences is either a type ascription (→ `PrimeFilter LindenbaumAlg`) or `x ∈ U.carrier`
(→ `x ∈ U`).

**A dedup that the same pass should take, independent of the encoding choice.** The
`LeftInverse` half of :782 and the whole of :983 both contain the same ~60-line block proving
`toQuot φ ∈ mcsToSet Γ → φ ∈ Γ` by hand (filtering `L`, deduction theorem, weakening, two
modus ponens). With the Core lemmas already imported it is three lines:

```lean
theorem toQuot_mem_mcsToSet_iff (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) Γ) (φ : Formula) :
    toQuot φ ∈ mcsToSet Γ ↔ φ ∈ Γ := by
  refine ⟨fun ⟨ψ, hψ, h_eq⟩ => ?_, mem_mcsToSet⟩
  obtain ⟨d_imp⟩ := (show toQuot ψ ≤ toQuot φ by rw [← h_eq] : Derives ψ φ)
  exact h_mcs.implication_property (theorem_in_mcs h_mcs d_imp) hψ
```

(`SetMaximalConsistent.implication_property` at `Core/MCSProperties.lean:160`, `theorem_in_mcs`
at `Core/MaximalConsistent.lean:462`.) `left_inv` is then
`Subtype.ext (Set.ext fun φ => toQuot_mem_mcsToSet_iff Γ.2 φ)`; `right_inv` is the 8-line
`RightInverse` half of :782 re-typed (one `show a = toQuot φ from h_eq` where the
`IsPFilter.toPFilter` route leaves an `ofDual (toDual a)` in a destructured hypothesis — the
only friction met in the whole port).

**Net size of `UltrafilterMCS.lean`**: 1,071 → roughly 780 lines, with the same theorem
content plus a named `Equiv`, and with `ultrafilter_correspondence` derived from it instead of
the reverse (which is what the task's acceptance criterion 3 asks for).

---

## 7. Question 5 — cost against (a) and (b)

Measured, not estimated, for the new code: the generic layer is **163 lines / 30 declarations**
(`gen_body`), the bundling **39 lines / 11 declarations**, the project port **160 lines**.
Written and green in three compile iterations each; total wall-clock of every `lake env lean`
run under 3 s (the oleans of the live modules are reused). The proof content the planner would
schedule is therefore *already written* — the implementation work is placing it and doing the
substitution pass of §6.

| | (a) Ideal-side replacement | (b) `BAUltrafilter` + bridge | (c) `PFilter` + `IsPrime` |
|---|---|---|---|
| New generic code | 0 | ~50-line bridge `Equiv` (complement flip, both directions, six axioms) | ~200 lines, Mathlib-shaped, **already compiled** (Appendix A) |
| Consumer rewrite | full re-derivation with complement in every statement; plan estimates "several agent runs" | rename ~63 sites | substitution pass ~110 sites, zero proof-step changes (§6) |
| Representations left in tree | 1 (ideal) | **2** (bespoke + Mathlib, joined by a lemma) | 1 (Mathlib) |
| Bridge lemmas | the flip is the bridge | 1 hand-written `Equiv` | **0** — the ideal is `IsPrime.toPrimePair`, the maximal-ideal Lindenbaum is `exists_le_maximal` by transport |
| `ultrafilterEquiv` target | `{I : Ideal LindenbaumAlg // I.IsMaximal}` (vocabulary inverted) | `BAUltrafilter LindenbaumAlg` (bespoke) | `PrimeFilter LindenbaumAlg` (Mathlib) |
| Downstream `η`, `R_G`, `R_Box`, `R_H` | complement on both sides | verbatim, but on a non-Mathlib type | verbatim, on a Mathlib type |
| Reaches `IsProper.exists_le_maximal` for tasks 497/125 | directly | via the bridge | directly, on the filter side, plus `exists_le_prime` and the PrimeSeparator corollary |
| Time (plan units) | +6 to +10 h over (b) per plan D1 | Phase 6 (1 h) + Phase 7 (2.5 h) = 3.5 h | **≈ 3.5 h**: place the generic file (0.5 h), substitution pass + dedup (2 h), README/overview (1 h). The proof-discovery cost that dominates Phase 7 is already spent. |

(c) is not "the expensive purist option". It lands at (b)'s budget with (a)'s single
representation and no bridge, because the piece (b) would hand-write already exists in Mathlib
as `IsPrime.toPrimePair`.

---

## 8. Question 6 — organisation

### 8.1 Where the generic layer lives

The layer is about arbitrary preorders, distributive lattices and Boolean algebras. Nothing in it
mentions formulas, derivations or `LindenbaumAlg`. Placing it under `Metalogic/Algebraic/`
would misdescribe it in the same way the bespoke structure did.

**Recommended**: a new top-level `FormalSystem/ForMathlib/` directory — the community
convention for code that is Mathlib-shaped and intended to be deleted on upstreaming:

```
FormalSystem/ForMathlib.lean                 -- aggregator (C8 requires a sibling for every
FormalSystem/ForMathlib/Order/PFilter.lean   --   immediate subdirectory of FormalSystem/)
```

- **Namespace**: `Order.PFilter` — exactly Mathlib's, so that when the layer is upstreamed the
  file is deleted and no consumer changes a name. Lemma names are the duals of their
  `Order/Ideal.lean` / `Order/PrimeIdeal.lean` counterparts, one for one (Appendix A lists the
  correspondence). Dual-transport lemmas follow the `*_iff_dual` pattern. Genuinely new names
  (no ideal analogue): `IsPrime.toIsProper`, `IsProper.exists_le_prime`,
  `DistribLattice.prime_filter_of_disjoint_filter_ideal` (the last is Mathlib's own commented
  name).
- **Imports**: only `Mathlib.Order.PrimeIdeal` (and `Mathlib.Order.PrimeSeparator` for E3).
  Both are light; `Mathlib.Order.Zorn` is already in the closure via
  `Core/MaximalConsistent.lean`.
- **Dependency rule** (state it in the file header and the README): nothing under
  `ForMathlib/` imports `FormalSystem.*`. Direction is strictly
  `Mathlib → ForMathlib → Metalogic/Algebraic/UltrafilterMCS → (tasks 497/125)`.
- **Wiring**: `FormalSystem.lean` gains `import FormalSystem.ForMathlib`; without it C6/C7 will
  count the module as unreachable. The root `CLAUDE.md` project-structure list and
  `.claude/context/repo/project-overview.md` need one line each.
- **Section discipline**: keep `[Preorder P]`, `[OrderBot P]`, `[DistribLattice P]`,
  `[BooleanAlgebra P]` in separate `section`s. Mixing `variable [Preorder P]` with a
  `[BooleanAlgebra P]` example trips the `overlappingInstances` linter and produces spurious
  unification failures (hit once in E1; fixed by sectioning).

**Alternative** (no new top-level directory): `FormalSystem/Metalogic/Algebraic/PrimeFilter.lean`
with the same `Order.PFilter` namespace. Cheaper on documentation, but it files a
Boolean-algebra fact under the logic's metatheory and keeps the "this is really a Mathlib
extension" signal implicit. Surfaced as decision D-A in §11.

### 8.2 What stays in `UltrafilterMCS.lean`

The module keeps its name (three Boneyard files import it; C11 checks import resolution) and
its `FormalSystem.Metalogic.Algebraic.UltrafilterMCS` namespace. It holds the
Lindenbaum-specific content only: `mcsToSet` and its five witnesses (unchanged),
`toQuot_mem_mcsToSet_iff` (new, §6), `mcsToPFilter` + its two instances, `mcsToUltrafilter`,
`ultrafilterToSet`, `ultrafilterToSet_mcs`, `SetMaximalConsistent.ultrafilterEquiv`,
`ultrafilter_correspondence` as its corollary, and the two formula-level `neg_iff` one-liners.
`fold_le_of_derives` is untouched by this decision (Phase 5 owns it).

### 8.3 What it buys the Jonsson–Tarski front

Concretely reachable without a bridge after this lands:
- `Order.PFilter.IsProper.exists_le_maximal` / `.exists_le_prime` — algebra-level Lindenbaum.
- `DistribLattice.prime_filter_of_disjoint_filter_ideal` — the separator for `Uf(A)` nonemptiness.
- `Order.Ideal.PrimePair` via `U.2.toPrimePair` whenever both the filter and its ideal are wanted.
- `η`, `R_G`, `R_Box`, `R_H` from the Boneyard seed, verbatim, over `PrimeFilter LindenbaumAlg`.

One thing it does **not** buy and the ultrafilter-frame task should know: Mathlib gives
`PFilter` no lattice (`Max (PFilter P)` does not exist; `Ideal` has one under
`[SemilatticeSup P] [IsCodirectedOrder P]`, `Order/Ideal.lean:390`). If that task needs
`F ⊔ principal x` it is a five-line transport `⟨F.dual ⊔ G.dual⟩`, not a blocker, but it is not
free today.

---

## 9. Question 7 — upstream contributability

Fetched from `leanprover-community/mathlib4` master on 2026-09-03: `Order/PFilter.lean` has no
declaration containing `IsProper`, `IsMaximal`, `IsPrime` or `Ultra`; `Order/PrimeIdeal.lean`'s
`namespace PFilter` still contains exactly `IsPrime`, `IsPrime.toPrimePair`,
`Ideal.PrimePair.F_isPrime`. The `TODO` in `PrimeSeparator.lean` is still open. So nothing
here has been superseded since the pin.

**PR shape** (matches what was written; costs this task nothing extra):
1. `Order/PFilter.lean`: `IsProper` (`@[mk_iff] class`, dual docstring), `isProper_of_notMem`,
   `IsProper.exists_notMem`, `isProper_iff_dual`, `isProper_iff_bot_notMem`,
   `IsProper.bot_notMem`; `IsMaximal` (`extends IsProper`), `isMaximal_iff_dual`,
   `IsProper.exists_le_maximal`. Plus the four `Iff.rfl` transport lemmas of §3 — reviewers will
   want them stated even though they are trivial, because they are what makes the rest read.
2. `Order/PrimeIdeal.lean`, `namespace PFilter`: `IsPrime.toIsProper` (instance),
   `isPrime_iff_dual`, and the Boolean section (`mem_or_compl_mem`, `compl_mem_of_notMem`,
   `compl_notMem_of_mem`, `mem_iff_compl_notMem`, `compl_mem_iff_notMem`,
   `isPrime_of_mem_or_compl_mem`, `isPrime_iff_mem_or_compl_mem`, `IsMaximal.isPrime`
   (DistribLattice), `IsPrime.isMaximal`, `IsProper.exists_le_prime`).
3. `Order/PrimeSeparator.lean`: replace the commented TODO with E3.

Expected review friction: (i) whether `PFilter.IsPrime` should be changed to
`extends IsProper` for symmetry with `Ideal.IsPrime` — a Mathlib-side choice; our `toIsProper`
instance is the compatible non-breaking form; (ii) whether the Boolean lemmas should be stated
on `Ideal.PrimePair` instead — the `toPrimePair` projection makes either derivable from the
other. Neither affects this task.

---

## 10. Question 8 — what could make (c) a bad idea

Looked for, not found. What was found, and its size:

1. **`ofDual (toDual a)` residue.** Filters built by `IsPFilter.toPFilter` expose
   `ofDual (toDual a) = ⟦φ⟧` after `rintro` in one spot. Fixed with one
   `show a = toQuot φ from h_eq`. Cosmetic.
2. **Implicit-argument pinning.** `U.2.compl_mem_iff_notMem` cannot infer `x` from
   `⟦φ.neg⟧ ∈ U` (the unifier will not invert `toQuot φ.neg` to `(toQuot φ)ᶜ`); pass
   `(x := toQuot φ)`. One site.
3. **No `Lattice (PFilter P)` in Mathlib.** Irrelevant to this task; noted for the frame task
   (§8.3).
4. **Type-target change is user-visible.** The task description, plan Phase 4, and acceptance
   criterion 3 all name `≃ Ultrafilter LindenbaumAlg`; the corrected target is
   `≃ PrimeFilter LindenbaumAlg`. That is a correction, not a cost, but the planner must
   restate the criterion.

The `PFilter.IsPrime` non-extension of `IsProper` (asymmetric with `Ideal.IsPrime`) was the
one place a real obstruction could have hidden; the `Nonempty` field closes it.

---

## 11. Decisions surfaced (with recommendations)

**D-A — Location of the generic layer.**
Recommend `FormalSystem/ForMathlib/Order/PFilter.lean` (+ `FormalSystem/ForMathlib.lean`
aggregator, `import FormalSystem.ForMathlib` in `FormalSystem.lean`, one line each in the root
`CLAUDE.md` structure list and `project-overview.md`). Alternative:
`Metalogic/Algebraic/PrimeFilter.lean`, same namespace, no new directory. Evidence: C8 accepts
either; the only cost of the first is documentation, the only cost of the second is a
misfiled abstraction.

**D-B — Name of the bundled type.**
Recommend `Order.PrimeFilter P := {F : PFilter P // F.IsPrime}`: honest on any preorder, equal
to the ultrafilters on a Boolean algebra (say so in the docstring), and it satisfies acceptance
criterion 2's first disjunct ("no declaration named `Ultrafilter` outside Mathlib in the live
tree") with nothing to document. Alternative: keep a project-namespaced `Ultrafilter` abbrev
for readability — this reintroduces the shadow the task exists to remove; not recommended.

**D-C — Define `IsMaximal` at all?**
Recommend yes. It is redundant *as the type's predicate* on a Boolean algebra, but it is the
transport target for `Ideal.IsProper.exists_le_maximal`, it is what a Mathlib PR must contain,
and it is 12 lines. Alternative: `IsProper` + `IsPrime` only, with `exists_le_prime` proved by
inlining the transport — saves 12 lines, loses the general-lattice statement.

None of the three changes the recommendation to adopt (c).

---

## 12. Phase-level organisation for the planner

Replaces plan Phases 6 and 7 (Decision D1's reversal point); Phases 1-3, 5 unaffected; Phase 4
is absorbed (the `Equiv` is built *on* the new type, so it should not be built first on the
old one and then re-typed).

- **Phase 6′ — Land the generic layer.** Create `ForMathlib/Order/PFilter.lean` from Appendix A
  (sections: Preorder / OrderBot / DistribLattice / BooleanAlgebra / bundling), aggregator,
  root import, docs lines. Verify: `lake build`, `check-module-invariants.sh` (C6/C7 must see
  the module as reachable; C8 green). Zero `sorry`; `#print axioms` on
  `IsProper.exists_le_prime` and `DistribLattice.prime_filter_of_disjoint_filter_ideal`
  show only `propext, Classical.choice, Quot.sound`. Commit.
- **Phase 7′ — Port `UltrafilterMCS.lean`.** In order: add `toQuot_mem_mcsToSet_iff`; add
  `mcsToPFilter` + two instances + `mcsToUltrafilter`; re-type `ultrafilterToSet` and
  `ultrafilterToSet_mcs` (substitution pass, §6); add `SetMaximalConsistent.ultrafilterEquiv`;
  restate `ultrafilter_correspondence` as its corollary; replace :910-966 by the two
  one-liners; delete :44-81, :538-556, :983-1069, the old `mcsToUltrafilter`. Verify
  `lake build`, C2 unchanged, C3 zero sorry, C11 green (module name unchanged). Commit
  per sub-step.
- **Phase 8′ — README.** `Algebraic/README.md`: module table row for `UltrafilterMCS.lean`
  (line count, "sorry-free", now consuming `ForMathlib/Order/PFilter.lean`), the dependency
  flowchart gains the `ForMathlib` node, a "Design decisions" subsection records D1 = option
  (c) with the two-dualities argument of §3 and the `IsPrime`-suffices fact of §4.2, and the
  "Last verified" stamp. C14 counts must be re-checked after the line changes.

Acceptance criteria as they should now read: (2) `grep -rn 'structure Ultrafilter\|def Ultrafilter' FormalSystem/ --include=*.lean | grep -v Boneyard` returns nothing — the first
disjunct, no documented exception needed; (3) `SetMaximalConsistent.ultrafilterEquiv :
{Γ // SetMaximalConsistent Γ} ≃ Order.PrimeFilter LindenbaumAlg` exists and
`ultrafilter_correspondence` is proved from it.

---

## 13. Open items

- **Tactic-level**: none. Every derivation in this spike closes with `exact`/`refine`/`rw`/
  `simpa`; no `aesop`/`omega`/`decide` was needed and none was tried, since there were no
  goals left to try them on.
- **Not measured**: full `lake build` time impact of the new Mathlib leaf imports. Expected
  negligible (`PrimeIdeal.lean` and `PrimeSeparator.lean` are ~250 and ~130 lines and import
  only `Order.Ideal`, `Order.PFilter`, `Order.Zorn`). Phase 6′ will observe it.
- **Not decided here**: D-A, D-B, D-C above.

---

## Appendix A — The generic layer as compiled (E1 body, 163 + 39 lines, zero warnings)

Imports: `Mathlib.Order.PrimeIdeal`. Name correspondence to Mathlib's ideal side is given in
the right margin where it exists.

```lean
open OrderDual

namespace Order.PFilter

variable {P : Type*}

section Preorder
variable [Preorder P] {F G : PFilter P} {x : P}

theorem mem_dual_iff : toDual x ∈ F.dual ↔ x ∈ F := Iff.rfl
theorem le_iff_dual_le : F ≤ G ↔ F.dual ≤ G.dual := Iff.rfl
theorem lt_iff_dual_lt : F < G ↔ F.dual < G.dual := Iff.rfl
theorem coe_eq_univ_iff : (F : Set P) = Set.univ ↔ (F.dual : Set Pᵒᵈ) = Set.univ := Iff.rfl

/-- A filter is proper if it is not the whole set. Dual of `Order.Ideal.IsProper`. -/
@[mk_iff]
class IsProper (F : PFilter P) : Prop where
  ne_univ : (F : Set P) ≠ Set.univ

theorem isProper_of_notMem {p : P} (notMem : p ∉ F) : IsProper F :=        -- Ideal.isProper_of_notMem
  ⟨fun hp ↦ by
    have := Set.mem_univ p
    rw [← hp] at this
    exact notMem this⟩

theorem IsProper.exists_notMem (hF : IsProper F) : ∃ p, p ∉ F :=
  Set.ne_univ_iff_exists_notMem _ |>.1 hF.ne_univ

theorem isProper_iff_dual : F.IsProper ↔ F.dual.IsProper :=
  ⟨fun h => ⟨h.ne_univ⟩, fun h => ⟨h.ne_univ⟩⟩

/-- A filter is maximal if it is maximal among proper filters. Dual of `Order.Ideal.IsMaximal`. -/
@[mk_iff]
class IsMaximal (F : PFilter P) : Prop extends IsProper F where
  maximal_proper : ∀ ⦃G : PFilter P⦄, F < G → (G : Set P) = Set.univ

theorem isMaximal_iff_dual : F.IsMaximal ↔ F.dual.IsMaximal := by
  constructor
  · intro h
    exact { ne_univ := h.ne_univ, maximal_proper := fun J hJ => h.maximal_proper (G := ⟨J⟩) hJ }
  · intro h
    exact { ne_univ := h.ne_univ, maximal_proper := fun G hG => h.maximal_proper (J := G.dual) hG }

/-- `IsPrime` already implies `IsProper`: the complement is a (nonempty) ideal. -/
instance (priority := 100) IsPrime.toIsProper [h : IsPrime F] : IsProper F :=   -- Ideal.IsPrime.toIsProper (there: a field)
  let ⟨_, hp⟩ := h.compl_ideal.Nonempty
  isProper_of_notMem hp

theorem isPrime_iff_dual : F.IsPrime ↔ F.dual.IsPrime := by
  constructor
  · intro h
    exact { ne_univ := h.toIsProper.ne_univ, compl_filter := h.compl_ideal }
  · intro h
    exact ⟨h.compl_filter⟩

end Preorder

section OrderBot
variable [Preorder P] [OrderBot P] {F : PFilter P}

theorem IsProper.bot_notMem (hF : IsProper F) : ⊥ ∉ F := fun h =>              -- Ideal.IsProper.top_notMem
  hF.ne_univ (Set.eq_univ_iff_forall.2 fun _ => mem_of_le bot_le h)

theorem isProper_iff_bot_notMem : IsProper F ↔ ⊥ ∉ F :=                        -- Ideal.isProper_iff_top_notMem
  ⟨IsProper.bot_notMem, isProper_of_notMem⟩

theorem IsProper.exists_le_maximal (hF : F.IsProper) : ∃ G, F ≤ G ∧ G.IsMaximal := by  -- Ideal.IsProper.exists_le_maximal
  obtain ⟨J, hJ, hJm⟩ := (isProper_iff_dual.1 hF).exists_le_maximal
  exact ⟨⟨J⟩, hJ, isMaximal_iff_dual.2 hJm⟩

end OrderBot

section DistribLattice
variable [DistribLattice P] {F : PFilter P}

instance (priority := 100) IsMaximal.isPrime [hF : IsMaximal F] : IsPrime F :=  -- Ideal.IsMaximal.isPrime
  isPrime_iff_dual.2 (@Ideal.IsMaximal.isPrime Pᵒᵈ _ F.dual (isMaximal_iff_dual.1 hF))

end DistribLattice

section BooleanAlgebra
variable [BooleanAlgebra P] {F : PFilter P} {x y : P}

theorem IsProper.notMem_of_compl_mem (hF : IsProper F) (hxc : xᶜ ∈ F) : x ∉ F := fun hx =>  -- Ideal.IsProper.notMem_of_compl_mem
  hF.bot_notMem (by simpa using inf_mem hx hxc)

theorem IsProper.notMem_or_compl_notMem (hF : IsProper F) : x ∉ F ∨ xᶜ ∉ F := by         -- Ideal.IsProper.notMem_or_compl_notMem
  by_cases hx : x ∈ F
  · exact Or.inr fun hxc => hF.notMem_of_compl_mem hxc hx
  · exact Or.inl hx

theorem IsPrime.mem_or_compl_mem (hF : IsPrime F) : x ∈ F ∨ xᶜ ∈ F := by                 -- Ideal.IsPrime.mem_or_compl_mem
  by_contra h
  push Not at h
  have : x ⊔ xᶜ ∈ hF.compl_ideal.toIdeal :=
    Ideal.sup_mem ((Ideal.mem_toIdeal _).2 h.1) ((Ideal.mem_toIdeal _).2 h.2)
  rw [Ideal.mem_toIdeal, sup_compl_eq_top] at this
  exact this top_mem

theorem IsPrime.compl_mem_of_notMem (hF : IsPrime F) (hx : x ∉ F) : xᶜ ∈ F :=            -- Ideal.IsPrime.compl_mem_of_notMem
  hF.mem_or_compl_mem.resolve_left hx

theorem IsPrime.compl_notMem_of_mem (hF : IsPrime F) (hx : x ∈ F) : xᶜ ∉ F :=
  fun hxc => hF.toIsProper.notMem_of_compl_mem hxc hx

theorem IsPrime.mem_iff_compl_notMem (hF : IsPrime F) : x ∈ F ↔ xᶜ ∉ F :=
  ⟨hF.compl_notMem_of_mem, fun h => hF.mem_or_compl_mem.resolve_right h⟩

theorem IsPrime.compl_mem_iff_notMem (hF : IsPrime F) : xᶜ ∈ F ↔ x ∉ F :=
  ⟨fun h hx => hF.compl_notMem_of_mem hx h, hF.compl_mem_of_notMem⟩

theorem isPrime_of_mem_or_compl_mem [hF : IsProper F] (h : ∀ {x : P}, x ∈ F ∨ xᶜ ∈ F) :   -- Ideal.isPrime_of_mem_or_compl_mem
    IsPrime F where
  compl_ideal :=
    { IsLowerSet := fun a b hab ha hb => ha (mem_of_le hab hb)
      Nonempty := ⟨⊥, hF.bot_notMem⟩
      Directed := fun a ha b hb =>
        ⟨a ⊔ b, fun hab => hF.notMem_of_compl_mem
            (by simpa [compl_sup] using inf_mem (h.resolve_left ha) (h.resolve_left hb)) hab,
          le_sup_left, le_sup_right⟩ }

theorem isPrime_iff_mem_or_compl_mem [IsProper F] : IsPrime F ↔ ∀ {x : P}, x ∈ F ∨ xᶜ ∈ F :=  -- Ideal.isPrime_iff_mem_or_compl_mem
  ⟨fun h _ => h.mem_or_compl_mem, isPrime_of_mem_or_compl_mem⟩

instance (priority := 100) IsPrime.isMaximal [hF : IsPrime F] : IsMaximal F where          -- Ideal.IsPrime.isMaximal
  ne_univ := hF.toIsProper.ne_univ
  maximal_proper := by
    intro G hFG
    obtain ⟨y, hyG, hyF⟩ := Set.exists_of_ssubset hFG
    refine Set.eq_univ_iff_forall.2 fun x => ?_
    have hyc : yᶜ ∈ G := hFG.le (hF.compl_mem_of_notMem hyF)
    have : y ⊓ yᶜ ∈ G := inf_mem hyG hyc
    rw [inf_compl_eq_bot] at this
    exact mem_of_le bot_le this

theorem IsProper.exists_le_prime (hF : F.IsProper) : ∃ G, F ≤ G ∧ G.IsPrime :=
  let ⟨G, hG, hGm⟩ := hF.exists_le_maximal
  ⟨G, hG, @IsMaximal.isPrime _ _ G hGm⟩

end BooleanAlgebra

end Order.PFilter

namespace Order

section Preorder
variable {P : Type*} [Preorder P]

/-- Prime filters, bundled. On a Boolean algebra these are precisely the ultrafilters. -/
abbrev PrimeFilter (P : Type*) [Preorder P] := {F : PFilter P // F.IsPrime}

instance : SetLike (PrimeFilter P) P where
  coe U := U.1
  coe_injective := fun _ _ h => Subtype.ext (SetLike.coe_injective h)

instance (U : PrimeFilter P) : U.1.IsPrime := U.2

theorem PrimeFilter.mem_iff {U : PrimeFilter P} {x : P} : x ∈ U ↔ x ∈ U.1 := Iff.rfl

@[ext] theorem PrimeFilter.ext {U V : PrimeFilter P} (h : ∀ x, x ∈ U ↔ x ∈ V) : U = V :=
  SetLike.ext h

end Preorder

end Order
```

Also compiled (E1 variants, kept as evidence that transport and direct proof agree):
`IsPrime.mem_or_compl_mem'` by pure transport of `Ideal.IsPrime.mem_or_compl_mem` with
`(x := toDual x)`, and `IsPrime.isMaximal'` by transport of `Ideal.IsPrime.isMaximal`. Either
style is acceptable; the direct Boolean proofs above are shorter to read and are what Appendix A
keeps.

## Appendix B — Project-side port as compiled (E2 excerpt)

```lean
theorem mcsToSet_isPFilter (h_mcs : SetMaximalConsistent (fc := FrameClass.Base) Γ) :
    IsPFilter (mcsToSet Γ) :=
  IsPFilter.of_def ⟨⊤, mcsToSet_top h_mcs⟩
    (fun a ha b hb => ⟨a ⊓ b, mcsToSet_inf_mem h_mcs ha hb, inf_le_left, inf_le_right⟩)
    (fun hle ha => mcsToSet_mem_of_le h_mcs ha hle)

def mcsToPFilter (Γ : {S : Set Formula // SetMaximalConsistent (fc := FrameClass.Base) S}) :
    PFilter LindenbaumAlg := (mcsToSet_isPFilter Γ.2).toPFilter

theorem mem_mcsToPFilter_iff (Γ) (a : LindenbaumAlg) : a ∈ mcsToPFilter Γ ↔ a ∈ mcsToSet Γ.1 := Iff.rfl

instance mcsToPFilter_isProper (Γ) : (mcsToPFilter Γ).IsProper :=
  PFilter.isProper_of_notMem (mcsToSet_bot_not_mem Γ.2)

instance mcsToPFilter_isPrime (Γ) : (mcsToPFilter Γ).IsPrime :=
  PFilter.isPrime_of_mem_or_compl_mem fun {a} => mcsToSet_compl_or Γ.2 a

def mcsToUltrafilter (Γ) : PrimeFilter LindenbaumAlg := ⟨mcsToPFilter Γ, inferInstance⟩

def ultrafilterToSet (U : PrimeFilter LindenbaumAlg) : Set Formula := { φ | toQuot φ ∈ U }

theorem ultrafilterToSet_mcs (U : PrimeFilter LindenbaumAlg) :
    SetMaximalConsistent (fc := FrameClass.Base) (ultrafilterToSet U)   -- :674 by substitution

noncomputable def SetMaximalConsistent.ultrafilterEquiv :
    {Γ : Set Formula // SetMaximalConsistent (fc := FrameClass.Base) Γ} ≃ PrimeFilter LindenbaumAlg where
  toFun := mcsToUltrafilter
  invFun U := ⟨ultrafilterToSet U, ultrafilterToSet_mcs U⟩
  left_inv Γ := Subtype.ext (Set.ext fun φ => toQuot_mem_mcsToSet_iff Γ.2 φ)
  right_inv U := by
    apply PrimeFilter.ext
    intro a
    constructor
    · rintro ⟨φ, h_phi_in, h_eq⟩
      rw [show a = toQuot φ from h_eq]
      exact h_phi_in
    · intro h_mem
      induction a using Quotient.ind with
      | _ φ => exact ⟨φ, h_mem, rfl⟩

theorem ultrafilter_correspondence : ∃ f g, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  ⟨ultrafilterEquiv, ultrafilterEquiv.symm, ultrafilterEquiv.left_inv, ultrafilterEquiv.right_inv⟩

theorem ultrafilter_neg_iff (U : PrimeFilter LindenbaumAlg) (φ : Formula) :
    toQuot φ ∈ U ↔ toQuot φ.neg ∉ U := U.2.mem_iff_compl_notMem
theorem ultrafilter_neg_iff' (U : PrimeFilter LindenbaumAlg) (φ : Formula) :
    toQuot φ.neg ∈ U ↔ toQuot φ ∉ U := U.2.compl_mem_iff_notMem (x := toQuot φ)
```

`#print axioms` on `ultrafilterEquiv`: `[propext, Classical.choice, Quot.sound]`.

## Appendix C — Evidence log

| Run | File | Imports | Result |
|---|---|---|---|
| E1 | generic layer + bundling (202 lines) | `Mathlib.Order.PrimeIdeal` | exit 0, 0 errors, 0 warnings |
| E2 | E1 + project port (160 lines) | `FormalSystem.Metalogic.Algebraic.UltrafilterMCS`, `Mathlib.Order.PrimeIdeal` | exit 0; axioms of `ultrafilterEquiv'` and `exists_le_prime` = `propext, Classical.choice, Quot.sound` |
| E3 | PrimeSeparator corollary (4-line proof) | `Mathlib.Order.PrimeSeparator` | exit 0 |
| — | `scripts/check-module-invariants.sh --no-build` | — | ALL CHECKS PASSED (C8, C11, C14 green) |
| — | `git status` | — | no change under `FormalSystem/`, `Tests/`, `docs/`, `scripts/` |
| — | upstream `mathlib4` master `Order/PFilter.lean`, `Order/PrimeIdeal.lean` (2026-09-03) | — | no `PFilter.IsProper`/`IsMaximal`; `namespace PFilter` unchanged from the pin |

Scratch files lived only in the session scratchpad and were never inside the repository.
