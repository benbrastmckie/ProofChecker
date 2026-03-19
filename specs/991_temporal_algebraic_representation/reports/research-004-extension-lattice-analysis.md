# Research Report 004: Extension Lattice and Weakest Base Logic Analysis

**Date**: 2026-03-18
**Status**: Complete
**Scope**: Extensions, weakenings, and characterization theorems for the bimodal system

---

## Executive Summary

This report identifies the **weakest natural base logic** with irreflexive semantics that preserves the parametric representation theorem, and maps the full **lattice of extensions** with characterization theorems for each node. Three findings are central and should guide the refactoring:

> **Finding 1 — Minimal interaction**: The minimal representation-preserving logic is **S5 + K_t.Lin.Irr + MF** — a single interaction axiom (time-shift closure) suffices. The axiom TF (`□φ → G(□φ)`) is **derivable** from MF + S5 via a three-step proof (§2.3) and should be removed as an axiom and re-proved as a theorem.

> **Finding 2 — Universal automatic completeness**: Every interaction axiom in the system (MF, TF, Barcan variants, commutativity axioms) is **Sahlqvist** because each expresses a relation composition containment (e.g., MF: `R;< ⊆ R`). By Sahlqvist's theorem, every node in the extension lattice (§3-4) has **automatic Kripke completeness** — no ad-hoc completeness proofs are needed at any level. This is the single most important simplification for the formalization.

> **Finding 3 — Irreflexivity is semantics-only**: Venema's insight that "connectedness and irreflexivity do not yield new validities" means the proof system needs no changes for irreflexivity — only the semantic interpretation changes (§6.2).

---

## 1. Current System Inventory

### 1.1 Axiom Catalog

The system (`Theories/Bimodal/ProofSystem/Axioms.lean`) has 21 axiom schemas organized into Base (18), Dense (1), and Discrete (3):

**Propositional (4)**:

| # | Axiom | Schema | Notes |
|---|-------|--------|-------|
| 1 | `prop_k` | (φ→(ψ→χ)) → ((φ→ψ)→(φ→χ)) | Distribution |
| 2 | `prop_s` | φ → (ψ → φ) | Weakening |
| 3 | `ex_falso` | ⊥ → φ | Explosion |
| 4 | `peirce` | ((φ→ψ)→φ) → φ | Classical reasoning |

**Modal S5 (5)**:

| # | Axiom | Schema | Frame property |
|---|-------|--------|----------------|
| 5 | `modal_t` (MT) | □φ → φ | Reflexivity of R |
| 6 | `modal_4` (M4) | □φ → □□φ | Transitivity of R |
| 7 | `modal_b` (MB) | φ → □◇φ | Symmetry of R |
| 8 | `modal_5_collapse` | ◇□φ → □φ | S5 collapse |
| 9 | `modal_k_dist` (MK) | □(φ→ψ) → (□φ→□ψ) | Distribution |

**Temporal (9)**:

| # | Axiom | Schema | Frame property |
|---|-------|--------|----------------|
| 10 | `temp_k_dist` (TK) | G(φ→ψ) → (Gφ→Gψ) | Distribution |
| 11 | `temp_4` (T4) | Gφ → GGφ | Transitivity of < |
| 12 | `temp_t_future` (TT-F) | Gφ → φ | **Reflexivity of ≤** |
| 13 | `temp_t_past` (TT-P) | Hφ → φ | **Reflexivity of ≤** |
| 14 | `temp_a` (TA) | φ → G(Pφ) | Temporal connectedness |
| 15 | `temp_l` (TL) | △φ → G(Hφ) | Temporal introspection |
| 16 | `temp_linearity` | F(φ)∧F(ψ) → F(φ∧ψ)∨F(φ∧Fψ)∨F(Fφ∧ψ) | Linearity (Task 922) |

**Bimodal Interaction (2)**:

| # | Axiom | Schema | Semantic property |
|---|-------|--------|-------------------|
| 17 | `modal_future` (MF) | □φ → □(Gφ) | Time-shift closure forward |
| 18 | `temp_future` (TF) | □φ → G(□φ) | Temporal persistence of □ |

**Dense Extension (1)**:

| # | Axiom | Schema | Frame condition |
|---|-------|--------|-----------------|
| 19 | `density` (DN) | Fφ → FFφ | DenselyOrdered |

**Discrete Extension (3)**:

| # | Axiom | Schema | Frame condition |
|---|-------|--------|-----------------|
| 20 | `discreteness_forward` (DF) | (F⊤∧φ∧Hφ) → F(Hφ) | SuccOrder |
| 21 | `seriality_future` | F(¬⊥) | NoMaxOrder |
| 22 | `seriality_past` | P(¬⊥) | NoMinOrder |

### 1.2 Inference Rules

From `Derivation.lean` — 7 rules:
1. **axiom**: Any axiom instance is derivable
2. **assumption**: Context formulas are derivable
3. **modus_ponens**: Γ ⊢ φ→ψ, Γ ⊢ φ ⟹ Γ ⊢ ψ
4. **necessitation**: ⊢φ ⟹ ⊢□φ
5. **temporal_necessitation**: ⊢φ ⟹ ⊢Gφ
6. **temporal_duality**: ⊢φ ⟹ ⊢swap_past_future(φ)
7. **weakening**: Γ ⊢ φ, Γ ⊆ Δ ⟹ Δ ⊢ φ

### 1.3 Reflexivity Dependencies

Axioms whose **soundness** depends on reflexive (≤) temporal semantics:

| Axiom | Uses `le_refl` | Status Under Strict (<) |
|-------|---------------|------------------------|
| `temp_t_future` (Gφ→φ) | Yes | **INVALID** — drops entirely |
| `temp_t_past` (Hφ→φ) | Yes | **INVALID** — drops entirely |
| `seriality_future` (F⊤) | Yes (trivializes) | Becomes genuine constraint (needs NoMaxOrder) |
| `seriality_past` (P⊤) | Yes (trivializes) | Becomes genuine constraint (needs NoMinOrder) |
| `density` (Fφ→FFφ) | Yes (trivializes) | Becomes genuine constraint (needs DenselyOrdered) |
| `modal_future` (MF) | Yes (proof uses it) | Statement valid with different proof |
| `temp_l` (△φ→G(Hφ)) | Yes | Needs reformulation |

Axioms **independent** of reflexivity:
- All propositional axioms (`prop_k`, `prop_s`, `ex_falso`, `peirce`)
- Modal axioms (`modal_t`, `modal_4`, `modal_b`, `modal_5_collapse`, `modal_k_dist`)
- Temporal distribution (`temp_k_dist`) and transitivity (`temp_4`)
- `temp_future` / TF (statement valid under both, proof may differ)
- `temp_a` (temporal connectedness)
- `temp_linearity` (linearity)

---

## 2. The Weakest Base Logic

### 2.1 Design Principles

The goal is to find the weakest logic satisfying:
1. **Irreflexive temporal semantics** (strict <)
2. **Parametric representation**: □φ ↔ □△φ where △φ = Hφ ∧ φ ∧ Gφ
3. **Decidability** and **finite model property**
4. **Completeness** with respect to a natural frame class
5. **Widest range of independent extensions**

### 2.2 The Minimal System: S5 + K_t.Lin.Irr + MF

**Modal component**: S5 = K + T + 5
- K: □(φ→ψ) → (□φ→□ψ)
- T: □φ → φ (modal reflexivity — NOT temporal reflexivity)
- 5: ◇φ → □◇φ (Euclidean)
- Frames: equivalence relations

**Temporal component**: K_t.Lin.Irr
- K_G: G(φ→ψ) → (Gφ→Gψ)
- K_H: H(φ→ψ) → (Hφ→Hψ)
- Tense duality: φ → GPφ, φ → HFφ
- Temporal 4: Gφ → GGφ (transitivity of <)
- Linearity axioms: future/past connectedness
- IRR rule (Gabbay): for irreflexivity (not axiomatizable)
- Frames: strict linear orders

**Interaction**: MF only
- MF: □φ → □(Gφ) (time-shift closure forward)
- Mirror-MF: □φ → □(Hφ) (obtained via temporal swap rule)

### 2.3 Key Theorem: TF is Derivable from MF + S5

**Claim**: In S5 + MF, the axiom `temp_future` / TF (□φ → G(□φ)) is a theorem.

**Proof**:
1. □φ → □□φ (by `modal_4`)
2. □□φ → □(G(□φ)) (by `modal_future` / MF applied to □φ)
3. □(G(□φ)) → G(□φ) (by `modal_t` / MT applied to G(□φ))
4. Chain: □φ → G(□φ) ∎

**Consequence**: `temp_future` is NOT an independent axiom in the S5 setting. The system needs only `modal_future` (MF) as its interaction axiom.

### 2.4 Perpetuity Principles from MF Alone

All six perpetuity principles are derivable from S5 + K_t.Lin.Irr + MF.

**Critical finding**: Code analysis confirms that **none of the perpetuity proofs in the codebase use `temp_t_future` or `temp_t_past`**. The actual Lean derivation trees survive the irreflexive refactoring without modification.

P5 uses TF (`temp_future`: □φ → G(□φ)) in its persistence lemma, but TF is derivable from MF + S5 (see §2.3), so MF remains the sole independent interaction axiom needed.

| Principle | Statement | Key axioms used |
|-----------|-----------|-----------------|
| P1 | □φ → △φ | MF, MT, temporal duality |
| P2 | ♢φ → ◇φ | Contrapositive of P1 |
| P3 | □φ → □△φ | MF, MK, temporal duality |
| P4 | ◇♢φ → ◇φ | Contrapositive of P3 |
| P5 | ◇♢φ → △◇φ | MF, TF (derivable), MB, M4, MT, MK, TK |
| P6 | ♢□φ → □△φ | All of P5's + classical propositional |

### 2.5 What Gets Dropped from the Current System

Moving to the irreflexive base, we **remove**:
- `temp_t_future` (Gφ→φ) — invalid under strict <
- `temp_t_past` (Hφ→φ) — invalid under strict <
- `temp_future` / TF — derivable from MF + S5 (see §2.3)
- `temp_l` (△φ→G(Hφ)) — needs reformulation for strict semantics

We **keep but reclassify**:
- `density` — now a genuine frame condition (not trivially true)
- `seriality_future/past` — now genuine frame conditions
- All modal axioms unchanged
- MF with updated soundness proof

---

## 3. The Extension Lattice

### 3.1 Three Dimensions of Extension

Extensions form a lattice along three orthogonal dimensions:

```
MODAL DIMENSION          TEMPORAL DIMENSION        INTERACTION DIMENSION
     S5                 K_t.Lin.Dense.NoEnd.Irr      Full Commutativity
      |                         |                          |
    S4.3                  K_t.Lin.Dense.Irr          MF + Barcan + Conv-Barcan
      |                         |                          |
    S4.2                    K_t.Lin.Irr                  MF + TF
      |                         |                          |
     S4                     K_t.Lin                       MF
      |                         |                          |
    KD45                    K_t.Trans                  (no interaction)
      |                         |
     KT                     K_t.Irr
      |                         |
     KD                       K_t
      |
      K
```

### 3.2 Modal Extensions

| Logic | Axioms over K | Frame Condition | Sahlqvist? | FMP? |
|-------|--------------|-----------------|------------|------|
| K | — | Arbitrary | — | Yes |
| KD | D: □φ→◇φ | Serial | Yes | Yes |
| KT | T: □φ→φ | Reflexive | Yes | Yes |
| KB | B: φ→□◇φ | Symmetric | Yes | Yes |
| K4 | 4: □φ→□□φ | Transitive | Yes | Yes |
| K5 | 5: ◇φ→□◇φ | Euclidean | Yes | Yes |
| KD45 | D+4+5 | Serial+Trans+Eucl | Yes | Yes |
| S4 = KT4 | T+4 | Preorder | Yes | Yes |
| S4.2 | T+4+.2 | Preorder+Convergent | Yes | Yes |
| S4.3 | T+4+.3 | Preorder+Connected | Yes | Yes |
| **S5 = KT5** | **T+5** | **Equivalence** | **Yes** | **Yes** |
| GL | L: □(□φ→φ)→□φ | Trans+conv. well-founded | No! | Yes |

**For the base system**: S5 is the natural choice (equivalence-class accessibility for histories through a moment). Weakening to S4 allows distinguishing "necessarily possible" from "possible" — useful for epistemic variants.

### 3.3 Temporal Extensions (over K_t, strict semantics)

| Extension | Axiom | Frame Condition | Sahlqvist? | Genuine? |
|-----------|-------|-----------------|------------|----------|
| Transitivity | Gφ→GGφ | t<s∧s<u → t<u | Yes | Yes |
| Linearity-F | complex | Future-connected | Yes | Yes |
| Linearity-P | complex | Past-connected | Yes | Yes |
| **Density** | **Fφ→FFφ** | **t<s → ∃u. t<u<s** | **Yes** | **Genuine under strict <** |
| **Seriality-F** | **F⊤** | **∀t∃s. t<s** | **Yes** | **Genuine under strict <** |
| **Seriality-P** | **P⊤** | **∀t∃s. s<t** | **Yes** | **Genuine under strict <** |
| Discreteness-F | Next operator | Discrete successor | — | Yes |
| Discreteness-P | Prev operator | Discrete predecessor | — | Yes |
| Well-foundedness | G(Gφ→φ)→Gφ | No infinite ascending | No! | Yes |
| Dedekind complete | Not fin. axiom. | Every bounded set has sup | — | Yes |

**Key insight**: Under strict semantics, density and seriality become **genuine, independent frame conditions** rather than trivial consequences of reflexivity. This is a feature: more independent extension points.

### 3.4 Interaction Extensions (over fusion S5 ⊗ K_t)

#### Herzig's Classification of Bimodal Interactions

Bimodal interaction axioms fall into four families (Herzig):

| Family | Schema | Frame Condition |
|--------|--------|-----------------|
| **Incl(□,G)** | □φ → Gφ | R_G ⊆ R_□ |
| **Perm(□,G)** | □Gφ → G□φ | R_G ∘ R_□ ⊆ R_□ ∘ R_G |
| **Confl(□,G)** | ◇Gφ → G◇φ | R_□⁻¹ ∘ R_G ⊆ R_G ∘ R_□⁻¹ (Church-Rosser) |
| **Scott-Lemmon** | ◇ʰ□ⁱφ → □ʲ◇ᵏφ | Parameterized confluence G(h,i,j,k) |

The Scott-Lemmon scheme `G(h,i,j,k)` = `◇ʰ□ⁱφ → □ʲ◇ᵏφ` unifies axioms 4, 5, B, .2, and many interaction axioms. Frame condition: `wR^h v ∧ wR^j u → ∃x. vR^i x ∧ uR^k x`.

#### Specific Interaction Axioms

| Extension | Axiom | Frame Condition | Independent? |
|-----------|-------|-----------------|-------------|
| **MF** | □φ→□(Gφ) | Time-shift closure forward | **Yes** (MINIMAL for representation) |
| MF-past | □φ→□(Hφ) | Time-shift closure backward | Derivable via temporal swap |
| TF | □φ→G(□φ) | R preserved forward | **Derivable** from MF+S5 |
| Barcan-F | G□φ→□Gφ | Expanding domains forward | Yes |
| Conv-Barcan-F | □Gφ→G□φ | Contracting domains forward | Yes |
| Barcan-P | H□φ→□Hφ | Expanding domains backward | Yes |
| Conv-Barcan-P | □Hφ→H□φ | Contracting domains backward | Yes |
| Com₁ | ◇Gφ→G◇φ | Church-Rosser (□/G) | Yes |
| Com₂ | F□φ→□Fφ | Church-Rosser (G/□) | Yes |
| Full commutativity | □Gφ↔G□φ | Product frame | Implies all above |

**Implication chain**:
```
Full Commutativity (□G↔G□, □H↔H□)
         ⇓
Barcan + Conv-Barcan (both directions)
         ⇓
MF + TF + Com₁ + Com₂
         ⇓
MF (+ TF derivable in S5)
         ⇓
No interaction (fusion)
```

---

## 4. Characterization Theorems

### 4.1 Level 0: Pure Fusion (No Representation)

**Logic**: S5 ⊗ K_t.Lin.Irr

**Frame class**: F₀ = {(W, T, R, <) : R is equivalence on W, < is strict linear order on T, no constraints between R and <}

**Characterization Theorem**: S5 ⊗ K_t.Lin.Irr is sound and complete w.r.t. F₀.
- FMP: Yes (fusion preserves FMP)
- Decidable: Yes, PSPACE
- Representation: **None** — □ and G/H are independent

### 4.2 Level 1: Minimal Representation (THE KEY LEVEL)

**Logic**: S5 ⊗ K_t.Lin.Irr + MF

**Frame class**: F₁ = F₀ ∩ {time-shift closure: if wRv at time t, then the temporal structure of v preserves R-accessibility at all times s > t}

**Characterization Theorem**: S5 + K_t.Lin.Irr + MF is sound and complete w.r.t. F₁.
- **Representation**: □φ ↔ □△φ (P5) — YES
- **Perpetuity**: P1-P6 all hold
- FMP: Conjectured yes
- Decidable: Conjectured yes

**This is the weakest logic with the representation theorem.**

### 4.3 Level 2: Dense Irreflexive

**Logic**: S5 ⊗ K_t.Lin.Dense.Irr + MF

**Frame class**: F₂ = F₁ ∩ {< is dense: t<s → ∃u. t<u<s}

**Characterization Theorem**: Additional axiom Fφ→FFφ characterizes density.
- Strictly stronger than Level 1
- Relevant for continuous-time models (ℚ, ℝ)

### 4.4 Level 3: Dense Unbounded Irreflexive (Irreflexive Current System)

**Logic**: S5 ⊗ K_t.Lin.Dense.NoEnd.Irr + MF

**Frame class**: F₃ = F₂ ∩ {no endpoints: ∀t∃s>t, ∀t∃s<t}

**Characterization Theorem**: Additional axioms F⊤, P⊤ characterize no-endpoints.
- This is the **irreflexive version of the current ProofChecker** (minus temporal T-axioms, which are now invalid, and minus TF which is derivable)
- FMP: Yes (established in codebase modulo reflexivity adjustment)
- Decidable: Yes

### 4.5 Level 4: Full Product

**Logic**: S5 × K_t.Lin.Dense.NoEnd.Irr

**Frame class**: F₄ = product frames W × T

**Characterization Theorem**: Full commutativity □G↔G□ characterizes product structure.
- Strictly stronger than Level 3
- □ and G commute perfectly
- Decidable: Yes (≤ NEXPTIME)

---

## 5. Natural Extensions and Their Independence

### 5.1 Extensions of the Minimal Base (Level 1)

From the minimal base S5 + K_t.Lin.Irr + MF, we can independently add:

```
                    S5 + K_t.Lin.Irr + MF (MINIMAL BASE)
                    ┌──────────┼──────────┐
                    │          │          │
              + Density   + Seriality  + Barcan
              (Fφ→FFφ)   (F⊤, P⊤)    (G□φ→□Gφ)
                    │          │          │
                    └──────┬───┘          │
                           │              │
                + Dense + Unbounded    + Conv-Barcan
                           │              │
                           └──────┬───────┘
                                  │
                    + Full Commutativity (Product)
```

### 5.2 Modal Weakenings

Weakening the modal base below S5:

| Modal Base | Effect on Representation | Notes |
|------------|-------------------------|-------|
| S5 | Full representation; TF derivable from MF | Current system |
| S4 | TF NOT derivable; need both MF and TF | More expressive |
| KD45 | Similar to S5 but without modal T | Lose □φ→φ, so lose P1's "present" part |
| K | No modal T — cannot derive □φ→φ | Representation breaks down |

**Important**: Weakening the modal base below KT loses □φ→φ (modal T), which is essential for the "present" component of P1 (□φ → φ). Without it, P1 becomes □φ → □(Hφ ∧ Gφ) — necessity implies necessary-always-else, missing the present.

### 5.3 The Diodorean Connection (Bull 1965)

When □ is *defined as* omnitemporal truth (single-operator, no separate G):

| Time Structure | Diodorean □ | Modal Logic Validated |
|---------------|-------------|----------------------|
| Continuous (ℝ, ≤) | □φ ≡ φ ∧ Gφ | **S4.3** (KT4 + .3) |
| Continuous (ℝ, <) | □φ ≡ Gφ | **K4.3** (K4 + .3) |
| Discrete (ℕ, ≤) | □φ ≡ φ ∧ Gφ | **S4.3.1** (S4.3 + Dum) |

The .3 axiom □(□φ→ψ) ∨ □(□ψ→φ) corresponds to linearity/connectedness of the temporal order. This shows the single-operator representation captures the linear structure but collapses the distinction between modal and temporal necessity.

The two-operator system (□ independent of G, connected by MF) is strictly more expressive: it preserves the distinction while establishing the bridge via P1-P6.

### 5.4 Independence Table

| Extension | Independent of base? | Independent of each other? | Frame characterization |
|-----------|---------------------|---------------------------|----------------------|
| Density | Yes | Yes (vs. seriality) | ∀ts. t<s → ∃u. t<u<s |
| Seriality-F | Yes | Yes (vs. density) | ∀t∃s. t<s |
| Seriality-P | Yes | Yes (vs. seriality-F) | ∀t∃s. s<t |
| Barcan-F | Yes | Yes (vs. Conv-Barcan) | Expanding temporal domains |
| Conv-Barcan-F | Yes | Yes (vs. Barcan) | Contracting temporal domains |
| Discreteness | Yes | **Incompatible** with density | Discrete successor exists |
| Well-foundedness | Yes | Yes | No infinite ascending chains |

### 5.5 Incompatible Extensions

Some extensions are **mutually exclusive**:
- Density + Discreteness: dense orders have no immediate successors
- Well-foundedness + No-first-moment: well-founded linear orders have a minimum

---

## 6. Correspondence Theory

### 6.1 Sahlqvist Status of All Axioms

| Axiom | Sahlqvist? | Canonical? | Automatic Completeness? |
|-------|-----------|-----------|------------------------|
| All propositional | N/A | Yes | Yes |
| Modal K, T, 4, B, 5 | Yes | Yes | Yes |
| Temporal K_G, K_H | N/A | Yes | Yes |
| Temporal 4 (Gφ→GGφ) | Yes | Yes | Yes |
| Density (Fφ→FFφ) | Yes | Yes | Yes |
| Seriality (F⊤, P⊤) | Yes | Yes | Yes |
| MF (□φ→□Gφ) | **Yes** | **Yes** | **Yes** |
| TF (□φ→G□φ) | **Yes** | **Yes** | **Yes** |
| Barcan/Conv-Barcan | Yes | Yes | Yes |
| Linearity axioms | Yes | Yes | Yes |
| IRR rule | N/A (rule) | N/A | Special treatment |
| McKinsey (□◇φ→◇□φ) | **No** | **No** | No (but derivable in S5) |
| Löb (□(□φ→φ)→□φ) | **No** | Yes (special) | Special |

### 6.1.1 Why All Interaction Axioms Are Sahlqvist

All natural interaction axioms express **relation composition containments** on two-sorted frames (W, R_□, <):

| Axiom | Composition Condition | Sahlqvist? |
|-------|----------------------|-----------|
| MF: □φ→□Gφ | R_□ ; < ⊆ R_□ (R_□ is forward-closed) | Yes (boxed atom → positive) |
| TF: □φ→G□φ | < ; R_□ ⊆ R_□ (R_□ absorbs temporal past) | Yes |
| Gφ→□Gφ | R_□ ; < ⊆ < (modal successors' futures ⊆ own futures) | Yes |
| □Gφ→G□φ | R_□ ; < ⊆ < ; R_□ (forward commutativity) | Yes |
| ◇Gφ→G◇φ | R_□⁻¹ ; < ⊆ < ; R_□⁻¹ (Church-Rosser) | Yes |
| □φ→Gφ | < ⊆ R_□ (temporal implies modal) | Yes |

Any formula of the form `□ᵢ₁...□ᵢₙ p → □ⱼ₁...□ⱼₘ p` is Sahlqvist (boxed atom antecedent, positive consequent), with correspondent `Rⱼ₁;...;Rⱼₘ ⊆ Rᵢ₁;...;Rᵢₙ`.

**Consequence**: The entire extension lattice (§3-4) has **automatic Kripke completeness** at every node, since all axioms at every level are Sahlqvist. No ad-hoc completeness proofs needed — Sahlqvist's theorem gives them for free.

### 6.2 The Irreflexivity Problem

**Irreflexivity is NOT modally definable** (Goldblatt-Thomason: fails closure under surjective bounded morphisms; van Benthem 1983: `¬Rxx` is not bisimulation-invariant).

**Key insight (Venema)**: "Connectedness and irreflexivity do not yield any new validities." The set of valid formulas is the same whether or not we enforce irreflexivity on frames. This means the extension lattice structure is preserved — irreflexivity is a semantic constraint, not a proof-theoretic one.

**Approaches for handling irreflexivity**:

1. **Gabbay's IRR rule** (1981): From `(p ∧ H(¬p)) → φ` where p is fresh, infer φ. Standard approach; used by Burgess (1980) for branching-time logic.
2. **Difference operator** (de Rijke 1992): Add Dφ = "φ at some w ≠ current w". Captures irreflexivity axiomatically. Decidable (coNP-complete, like S5).
3. **IRR-free axiomatization** (Reynolds 1992): Over (ℝ, <), orthodox temporal rules suffice without IRR. Also Di Maio & Zanardo (1998) for T×W frames.
4. **Infinite axiom schema** (Zanardo 1990): Replace IRR rule with infinitely many axioms.
5. **Semantic restriction**: Simply restrict validity to irreflexive frames (no proof-theoretic change needed if Venema's observation applies).

For the ProofChecker, approach (5) may be simplest: since irreflexivity adds no new validities, the proof system can remain unchanged while the semantics restricts to strict orders.

### 6.3 Frame Definability Summary

| Property | Definable by axioms? | Definable by rules? |
|----------|---------------------|-------------------|
| Reflexivity | Yes (T axiom) | — |
| Irreflexivity | **No** | Yes (IRR rule) |
| Transitivity | Yes (4 axiom) | — |
| Density | Yes (Fφ→FFφ) | — |
| Seriality | Yes (D/F⊤) | — |
| Linearity | Yes (complex) | — |
| Well-foundedness | **No** | Yes (Löb-like rule) |
| Dedekind completeness | **No** | **No** (second-order) |

---

## 7. Complexity and Decidability

| Logic | Complexity | Notes |
|-------|-----------|-------|
| S5 alone | coNP-complete | |
| K_t.Lin alone | PSPACE-complete | coNP for finitely axiom. tense logics |
| S5 ⊗ K_t.Lin (fusion) | PSPACE-complete | Fusion preserves decidability |
| S5 + K_t.Lin + MF | ≤ EXPTIME (conj.) | Single interaction axiom |
| S5 + K_t.Lin.Dense + MF | ≤ EXPTIME (conj.) | Same + density |
| S5 × K_t.Lin (product) | ≤ EXPSPACE | Full commutativity |
| K × K (product) | Decidable | FMP holds |
| S5 × S5 (product) | NEXPTIME | Decidable |
| K4 × K4 (product) | **Undecidable** | Gabelaia et al. 2005 |
| S4 × S4 (product) | **Undecidable** | GKWZ 2003 |
| S5 × S5 × S5 (product) | **Undecidable** | 3+ dimensions |

**Warning**: Products of transitive logics are generally undecidable. The choice to use MF (a single interaction axiom, weaker than full commutativity) avoids this trap.

**Warning**: Adding interaction axioms can jump complexity dramatically. The product K4 × K4 is undecidable. This means the choice of which interaction axioms to add is not just logical but also computational.

---

## 8. Refactoring Plan: Two Central Simplifications

The following two results should be the **primary drivers** of the refactoring. Every architectural decision flows from them.

### 8.1 Simplification A: Remove TF as Axiom, Derive It

**Current state**: `temp_future` (TF: □φ → G(□φ)) is listed as an independent axiom (#18 in §1.1).

**Target state**: TF is a **derived theorem**, proved once from MF + M4 + MT.

**Proof** (three steps, each a single axiom application):
```
1. □φ → □□φ              (M4: modal_4)
2. □□φ → □(G(□φ))        (MF: modal_future, applied to □φ)
3. □(G(□φ)) → G(□φ)      (MT: modal_t, applied to G(□φ))
∴  □φ → G(□φ)            (chain 1-2-3)
```

**Refactoring steps**:
1. Remove `temp_future` from the axiom enum in `Axioms.lean`
2. Add `theorem tf_from_mf` in the proof system deriving TF from MF + M4 + MT
3. Update all downstream uses of `temp_future` to reference the theorem instead
4. P5's proof (which uses TF via a persistence lemma) should import the derived theorem

**Impact**: Reduces the axiom count by 1 and clarifies the logical dependency structure — MF is the **sole** bridge between the modal and temporal components.

### 8.2 Simplification B: Sahlqvist Completeness at Every Level

**Current state**: Completeness proofs are proved ad-hoc for specific frame classes.

**Target state**: **No ad-hoc completeness proofs** at any level of the extension lattice.

**Why this works**: Every interaction axiom in the system expresses a **relation composition containment** on two-sorted frames:

| Axiom | Composition Containment | Sahlqvist Form |
|-------|------------------------|----------------|
| MF: □φ→□Gφ | R ; < ⊆ R | Boxed atom → positive |
| TF: □φ→G□φ | < ; R ⊆ R | Boxed atom → positive |
| Barcan: G□φ→□Gφ | R ; < ⊆ < ; R | Boxed atom → positive |
| Conv-Barcan: □Gφ→G□φ | < ; R ⊆ R ; < | Boxed atom → positive |
| Com₁: ◇Gφ→G◇φ | R⁻¹ ; < ⊆ < ; R⁻¹ | Church-Rosser |

All are instances of the general pattern `□ᵢ₁...□ᵢₙ p → □ⱼ₁...□ⱼₘ p` (Sahlqvist: boxed atom antecedent, positive consequent), with frame correspondent `Rⱼ₁;...;Rⱼₘ ⊆ Rᵢ₁;...;Rᵢₙ`.

**Consequence**: By Sahlqvist's theorem:
- Every axiom has an automatically computable first-order frame correspondent
- The canonical frame validates every axiom (canonicity for free)
- Kripke completeness holds at every node in the extension lattice

**Refactoring steps**:
1. Factor completeness proofs to use a single Sahlqvist machinery module
2. Each extension level (§4) should invoke Sahlqvist completeness rather than proving completeness independently
3. When adding new interaction axioms, verify they fit the `□...p → □...p` pattern (guaranteeing Sahlqvist status) rather than constructing a bespoke completeness proof
4. Document the composition containment for each axiom as its "semantic certificate"

**Impact**: Eliminates the most labor-intensive part of the formalization (completeness proofs) and makes the system trivially extensible — adding a new interaction axiom at any level requires only stating it and verifying it's Sahlqvist.

---

## 9. Recommended Architecture

### 9.1 The Layered System

```
Layer 4: Frame Specializations
  ┌──────────┬────────────┬─────────────┐
  │ + Dense  │ + Discrete │ + Unbounded │  (choose time structure)
  │ (Fφ→FFφ) │ (next/prev)│ (F⊤, P⊤)   │
  └──────────┴─────┬──────┴─────────────┘
                   │
Layer 3: Interaction Strengthening (optional)
  ┌──────────────┬─┴──────────────┐
  │ + Barcan     │ + Conv-Barcan  │  (domain conditions)
  │ (G□φ→□Gφ)   │ (□Gφ→G□φ)     │
  └──────────┬───┴────────────────┘
             │
Layer 2: MINIMAL REPRESENTATION BASE ← recommended base
  S5 + K_t.Lin.Irr + MF
  (P1-P6 all hold; □φ ↔ □△φ; TF derivable)
             │
Layer 1: Pure Fusion (no representation)
  S5 ⊗ K_t.Lin.Irr
             │
Layer 0: Weakest Components
  K ⊗ K_t
```

### 9.2 Implementation Strategy

For the ProofChecker refactoring to irreflexive semantics, guided by the two central simplifications (§8):

**Phase 1: TF derivability (§8.1)**
1. Remove `temp_future` from the axiom enum in `Axioms.lean`
2. Add `theorem tf_from_mf` deriving TF from MF + M4 + MT (three-step chain)
3. Update all downstream uses of `temp_future` to reference the derived theorem
4. Verify P5's persistence lemma still works via the derived TF

**Phase 2: Establish the irreflexive base**
1. Change Truth.lean: `≤` → `<` in temporal quantifiers
2. Remove `temp_t_future` and `temp_t_past` axioms (invalid under strict <)
3. Add IRR rule to the derivation system (or restrict semantics per Venema's insight, §6.2)
4. Update MF soundness proof (no longer uses `le_refl`)

**Phase 3: Reclassify frame axioms**
1. Mark density as a genuine extension (not trivially true)
2. Mark seriality as a genuine extension
3. Reformulate `temp_l` for strict semantics
4. Add `[DenselyOrdered D]` and `[Nontrivial D]` where needed in soundness proofs

**Phase 4: Verify perpetuity**
1. Prove P1-P6 from MF alone (no TF needed as axiom — it's now a theorem)
2. Verify P5 (representation theorem) holds
3. Update Bridge.lean derivations

**Phase 5: Sahlqvist completeness infrastructure (§8.2)**
1. Factor completeness proofs to use a single Sahlqvist machinery module
2. Each extension level (§4) invokes Sahlqvist completeness, not bespoke proofs
3. Document the composition containment (`R;< ⊆ R` etc.) for each axiom
4. When adding new axioms, verify `□...p → □...p` Sahlqvist form as the completeness certificate

**Phase 6: Build extension modules**
1. Create modular extension files for each layer
2. Each extension adds axioms + Sahlqvist certificate + frame characterization
3. Independence proofs via countermodels

---

## 10. Key Theorems to Prove in Lean

### 10.1 Core (Minimal Base)

```
-- TF is derivable from MF + S5 (see §2.3)
theorem tf_from_mf : ⊢ φ.box.imp φ.box.all_future  -- using MF + M4 + MT

-- P1 from MF alone
theorem perpetuity_1_irrefl : ⊢ φ.box.imp φ.always  -- using MF + T

-- P5 (representation) from MF alone
theorem representation : ⊢ φ.always.box.iff φ.box  -- P3 + projection
```

### 10.2 Extensions

```
-- Density characterization
theorem density_characterizes :
  valid_on_dense_frames φ ↔ ⊢[base + density] φ

-- Seriality characterization
theorem seriality_characterizes :
  valid_on_unbounded_frames φ ↔ ⊢[base + seriality] φ

-- Barcan characterization
theorem barcan_characterizes :
  valid_on_expanding_frames φ ↔ ⊢[base + barcan] φ
```

---

## 11. References

1. **Gabbay (1981)**: Irreflexivity lemma and IRR rule
2. **Thomason (1984)**: Combinations of tense and modality
3. **Finger & Gabbay (1992)**: Adding a temporal dimension to a logic system
4. **Sahlqvist (1975)**: Completeness and correspondence
5. **Goldblatt & Thomason (1975)**: Frame definability
6. **Marx (1999)**: Complexity of products of modal logics
7. **Wolter (2000)**: Fusions of modal logics revisited
8. **GKWZ (2003)**: Many-Dimensional Modal Logics (Gabbay, Kurucz, Wolter, Zakharyaschev)
9. **Reynolds (1992)**: An axiomatization for until and since over the reals without the IRR rule
10. **Reynolds (2003)**: Axiomatization of temporal logics on the real line
11. **Zanardo (1990)**: IRR-free axiomatization via infinite axiom schemas
12. **Zanardo (1996)**: Branching-time logic with quantification over branches
13. **van Benthem (1983)**: The Logic of Time
14. **Blackburn, de Rijke, Venema (2001)**: Modal Logic (Cambridge)
15. **Blackburn, van Benthem, Wolter (2007)**: Handbook of Modal Logic
16. **de Rijke (1992)**: The modal logic of inequality (difference operator)
17. **Di Maio & Zanardo (1998)**: A Gabbay-rule free axiomatization of T×W validity
18. **Kracht & Wolter (1991)**: Properties of independently axiomatizable bimodal logics (fusion transfer theorems)
19. **Venema**: Temporal Logic (chapter) — "connectedness and irreflexivity do not yield new validities"
20. **Burgess (1980)**: Peircean branching-time temporal logic (used IRR)
21. **Nalon, Marcos & Dixon (2014)**: Parameterized confluence axioms for modal logics
