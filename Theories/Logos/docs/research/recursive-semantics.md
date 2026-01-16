# Recursive Semantics for Logos

**Related Documents**:
- [layer-extensions.md](layer-extensions.md) - Extension architecture overview
- [METHODOLOGY.md](../user-guide/METHODOLOGY.md) - Philosophical methodology
- [GLOSSARY.md](../reference/GLOSSARY.md) - Term definitions

---

## Introduction

A semantic frame provides the primitive structures used to interpret a formal language. Extending the expressive power of a language requires strategic extensions to the primitive semantic resources provided by the frame, including precisely the resources needed and nothing more. This ensures that language and frame remain in perfect step with each other.

This document provides the recursive semantics for Logos. The semantics proceeds through increasingly expressive extensions, each extending the frame and evaluation mechanisms of the previous:

### Extension Dependencies

The following diagram shows the dependency structure among extensions:

```
┌─────────────────────────────────────────────────┐
│           Constitutive Foundation               │
│         (hyperintensional base layer)           │
└───────────────────────┬─────────────────────────┘
                        │ required
                        ▼
┌─────────────────────────────────────────────────┐
│              Dynamical Foundation              │
│    (modal, temporal, counterfactual, causal)    │
└───────────────────────┬─────────────────────────┘
                        │
       ┌────────────────┼────────────────┐
       │ optional       │ optional       │ optional
       ▼                ▼                ▼
┌──────────────┐ ┌──────────────┐ ┌──────────────┐
│  Epistemic   │ │  Normative   │ │   Spatial    │
│  Extension   │ │  Extension   │ │  Extension   │
│ (belief,     │ │ (obligation, │ │ (location,   │
│  knowledge,  │ │  permission, │ │  spatial     │
│  probability)│ │  preference) │ │  relations)  │
└──────┬───────┘ └──────┬───────┘ └──────┬───────┘
       │                │                │
       └────────────────┼────────────────┘
                        │ at least one required
                        ▼
┌─────────────────────────────────────────────────┐
│             Agential Extension                  │
│           (multi-agent reasoning)               │
└───────────────────────┬─────────────────────────┘
                        │ inherits from Epistemic
                        ▼
┌─────────────────────────────────────────────────┐
│            Reflection Extension                 │
│    (metacognition, self-modeling, I operator)   │
└─────────────────────────────────────────────────┘
```

The Constitutive Foundation and Dynamical Foundation form the required base. The Epistemic, Normative, and Spatial Extensions are modular plugins that can be combined in any subset. The Agential Extension requires at least one middle extension to be loaded.

1. **Constitutive Foundation**: Hyperintensional semantics over a mereological state space
2. **Dynamical Foundation**: Hyperintensional and intensional semantics over a task space
3. **Epistemic Extension**: Extensions for belief, knowledge, and probability [DETAILS]
4. **Normative Extension**: Extensions for obligation, permission, and value [DETAILS]
5. **Spatial Extension**: Extensions for spatial reasoning [DETAILS]
6. **Agential Extension**: Extensions for multi-agent reasoning [DETAILS]
7. **Reflection Extension**: Extensions for metacognition and self-modeling [DETAILS]

The Constitutive Foundation provides the foundational mereological structure with bilateral propositions (verifier/falsifier pairs). The Dynamical Foundation extends this foundation with temporal structure (a totally ordered abelian group) and a task relation constraining possible state transitions, enabling evaluation of truth relative to world-histories and times.

---

## Constitutive Foundation: Hyperintensional Semantics

The Constitutive Foundation provides the foundational semantic structure based on exact truthmaker semantics. Evaluation is hyperintensional, distinguishing propositions that agree on truth-value across all possible worlds but differ in their exact verification and falsification conditions.

### Syntactic Primitives

The Constitutive Foundation interprets the following syntactic primitives:
- **Variables**: x, y, z, ... (ranging over states)
- **Individual constants**: a, b, c, ... (0-place function symbols)
- **n-place function symbols**: f, g, h, ...
- **n-place predicates**: F, G, H, ...
- **Sentence letters**: p, q, r, ... (0-place predicates)
- **Lambda abstraction**: λx.A (binding variable x in formula A)
- **Logical connectives**: ¬, ∧, ∨, ⊤, ⊥, ≡

### Constitutive Frame

A *constitutive frame* is a structure **F** = ⟨S, ⊑⟩ where:

| Component | Description |
|-----------|-------------|
| **State Space** | A nonempty set S of states |
| **Parthood** | A partial order ⊑ on S making ⟨S, ⊑⟩ a complete lattice |

The constitutive frame is non-modal: possibility and compatibility cannot be defined at this level since they require the task relation introduced in the Dynamical Foundation.

The lattice structure provides:
- **Null state** (□): The bottom element (fusion of the empty set)
- **Full state** (■): The top element (fusion of all states)
- **Fusion** (s.t): The least upper bound of s and t

### Constitutive Model

A *constitutive model* is a structure **M** = ⟨S, ⊑, I⟩ where:

| Component | Description |
|-----------|-------------|
| **Frame** | ⟨S, ⊑⟩ is a constitutive frame |
| **Interpretation** | I assigns meanings to non-logical vocabulary |

The interpretation function I assigns:
- **n-place function symbols** f → I(f) : Sⁿ → S (0-place = individual constants mapping to states)
- **n-place predicates** F → ordered pairs ⟨v_F, f_F⟩ where:
  - v_F : set of functions Sⁿ → S (verifier functions)
  - f_F : set of functions Sⁿ → S (falsifier functions)
- **Sentence letters** (0-place predicates) p → ordered pairs ⟨v_p, f_p⟩ of verifier and falsifier state sets

**Containment constraint**: For any function f in v_F or f_F and any n states a₁, ..., aₙ, these states are all parts of f(a₁,...,aₙ). However, f(a₁,...,aₙ) may have additional parts beyond the input states.

**Predicate intuition**: For 1-place predicates, the functions in v_F and f_F take an object (which is itself a state) as input and return that object instantiating a verifying or falsifying property instance for the property in question.

### Variable Assignment

A *variable assignment* σ is a function from variables to states: σ : Var → S

Greek letters (τ, α, β, ...) are reserved for world-histories. The letter σ (with subscripts σ₁, σ₂, ...) denotes variable assignments, chosen for compatibility across LaTeX, markdown, and Lean notation.

The **extension** of a term relative to model M and assignment σ:
- **Variable** x: ⟦x⟧^σ_M = σ(x)
- **Function application** f(t₁,...,tₙ): ⟦f(t₁,...,tₙ)⟧^σ_M = I(f)(⟦t₁⟧^σ_M, ..., ⟦tₙ⟧^σ_M)

### Verification and Falsification Clauses

A state s **verifies** (⊩⁺) or **falsifies** (⊩⁻) a formula A relative to model M and assignment σ:

#### Atomic Formulas

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ F(t₁,...,tₙ) | iff there is some f ∈ v_F where s = f(⟦t₁⟧^σ_M, ..., ⟦tₙ⟧^σ_M) |
| M, σ, s ⊩⁻ F(t₁,...,tₙ) | iff there is some f ∈ f_F where s = f(⟦t₁⟧^σ_M, ..., ⟦tₙ⟧^σ_M) |

#### Lambda Abstraction (λ)

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ (λx.A)(t) | iff M, σ[⟦t⟧^σ_M/x], s ⊩⁺ A |
| M, σ, s ⊩⁻ (λx.A)(t) | iff M, σ[⟦t⟧^σ_M/x], s ⊩⁻ A |

Where σ[v/x] is the assignment that maps x to v and agrees with σ on all other variables.

#### Negation (¬)

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ ¬A | iff M, σ, s ⊩⁻ A |
| M, σ, s ⊩⁻ ¬A | iff M, σ, s ⊩⁺ A |

#### Conjunction (∧)

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ A ∧ B | iff s = t.u for some t, u where M, σ, t ⊩⁺ A and M, σ, u ⊩⁺ B |
| M, σ, s ⊩⁻ A ∧ B | iff M, σ, s ⊩⁻ A, or M, σ, s ⊩⁻ B, or s = t.u for some t, u where M, σ, t ⊩⁻ A and M, σ, u ⊩⁻ B |

#### Disjunction (∨)

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ A ∨ B | iff M, σ, s ⊩⁺ A, or M, σ, s ⊩⁺ B, or s = t.u for some t, u where M, σ, t ⊩⁺ A and M, σ, u ⊩⁺ B |
| M, σ, s ⊩⁻ A ∨ B | iff s = t.u for some t, u where M, σ, t ⊩⁻ A and M, σ, u ⊩⁻ B |

#### Top (⊤) and Bottom (⊥)

| | Verification | Falsification |
|---|-------------|---------------|
| ⊤ | M, σ, s ⊩⁺ ⊤ for all s ∈ S | M, σ, s ⊩⁻ ⊤ iff s = ■ (full state) |
| ⊥ | Never: M, σ, s ⊮⁺ ⊥ for all s | M, σ, s ⊩⁻ ⊥ iff s = □ (null state) |

#### Propositional Identity (≡)

| | Condition |
|---|-----------|
| M, σ, s ⊩⁺ A ≡ B | iff s = □ and {t : M, σ, t ⊩⁺ A} = {t : M, σ, t ⊩⁺ B} and {t : M, σ, t ⊩⁻ A} = {t : M, σ, t ⊩⁻ B} |
| M, σ, s ⊩⁻ A ≡ B | iff s = □ and ({t : M, σ, t ⊩⁺ A} ≠ {t : M, σ, t ⊩⁺ B} or {t : M, σ, t ⊩⁻ A} ≠ {t : M, σ, t ⊩⁻ B}) |

#### Essence and Ground

These constitutive relations can be defined via propositional identity:

| Relation | Definition | Reading |
|----------|------------|---------|
| **Essence** | A ⊑ B := A ∧ B ≡ B | "A is essential to B" (A is a conjunctive part of B) |
| **Ground** | A ≤ B := A ∨ B ≡ B | "A grounds B" (A is a disjunctive part of B) |

**Negation distribution**: These relations are interrelated through negation:
- A ⊑ B iff ¬A ≤ ¬B
- A ≤ B iff ¬A ⊑ ¬B

**Bilattice structure**: The space of bilateral propositions forms a non-interlaced bilattice (Ginsberg 1988, Fitting 1989-2002) where:
- ⟨P, ⊑⟩ and ⟨P, ≤⟩ are complete lattices
- Negation exchanges the two orderings: X ≤ Y iff ¬X ⊑ ¬Y
- Conjunction and disjunction are the least upper bounds with respect to ⊑ and ≤ respectively

### Bilateral Propositions

A *bilateral proposition* is an ordered pair ⟨V, F⟩ where:
- V and F are subsets of S closed under fusion
- ⟨V, F⟩ is **exclusive**: states in V are incompatible with states in F
- ⟨V, F⟩ is **exhaustive**: every possible state is compatible with some state in V or F

**Propositional Operations**:

| Operation | Definition |
|-----------|------------|
| **Product** | X ⊗ Y := {s.t : s ∈ X, t ∈ Y} |
| **Sum** | X ⊕ Y := X ∪ Y ∪ (X ⊗ Y) |
| **Conjunction** | ⟨V,F⟩ ∧ ⟨V',F'⟩ := ⟨V ⊗ V', F ⊕ F'⟩ |
| **Disjunction** | ⟨V,F⟩ ∨ ⟨V',F'⟩ := ⟨V ⊕ V', F ⊗ F'⟩ |
| **Negation** | ¬⟨V,F⟩ := ⟨F, V⟩ |

### Logical Consequence (Constitutive Foundation)

Logical consequence at the Constitutive Foundation is restricted to propositional identity sentences:

> Γ ⊨ A iff for any model M and assignment σ: if M, σ, □ ⊩⁺ B for all B ∈ Γ, then M, σ, □ ⊩⁺ A

That is, A is a consequence of Γ iff the null state verifies A in any model where it verifies all premises.

**Identity Sentences and Evaluation Overlap**: Identity sentences are formed from extensional (non-identity) sentences: A ≡ B where A and B are atomic sentences or built from ¬, ∧, ∨. The logical consequences holding between identity sentences are preserved by further extensions. However, the Constitutive Foundation lacks the semantic resources to evaluate non-identity sentences, which depend on contingent states of affairs rather than purely structural relations in state space. The Constitutive Foundation is nevertheless important for defining a logic of propositional identity. The same theorems valid at this level remain valid in the Dynamical Foundation, though the Dynamical Foundation's definition of logical consequence differs, quantifying over world-histories and times in addition to models and variable assignments.

---

## Dynamical Foundation: Intensional Semantics

The Dynamical Foundation extends the Constitutive Foundation with temporal structure and a task relation, enabling evaluation of truth relative to world-histories and times. While the hyperintensional foundation remains (distinguishing propositions by their exact verifiers and falsifiers), this foundation adds intensional evaluation relative to contextual parameters (world-history, time, variable assignment) to determine truth-values for all Dynamical Foundation sentences.

### Syntactic Primitives

The Dynamical Foundation interprets the following additional syntactic primitives beyond those of the Constitutive Foundation:
- **Modal operators**: □ (necessity), ◇ (possibility)
- **Temporal operators**: H (always past), G (always future), P (some past), F (some future)
- **Extended temporal operators**: ◁ (since), ▷ (until)
- **Counterfactual conditional**: □→ (would-counterfactual)
- **Store/recall operators**: ↑ⁱ (store), ↓ⁱ (recall)

A well-formed sentence at this extension includes all Constitutive Foundation sentences plus those built using these operators according to their arities.

### Core Frame

A *core frame* is a structure **F** = ⟨S, ⊑, D, ⇒⟩ where:

| Component | Description |
|-----------|-------------|
| **State Space** | ⟨S, ⊑⟩ is a constitutive frame |
| **Temporal Order** | D = ⟨D, +, ≤⟩ is a totally ordered abelian group |
| **Task Relation** | ⇒ is a ternary relation on S × D × S satisfying constraints below |

The task relation s ⇒_d t (read: "there is a task from s to t of duration d") satisfies constraints formulated in terms of state modality.

### State Modality Definitions

| Term | Definition |
|------|------------|
| **Possible state** | s ∈ P iff s ⇒_0 s (state has a trivial task to itself) |
| **Impossible state** | s ∉ P iff ¬(s ⇒_0 s) |
| **Connected** | s ~ t iff s ⇒_d t or t ⇒_d s for some d |
| **Compatible states** | s ∘ t iff s.t ∈ P |
| **Maximal t-compatible part** | s ∈ r_t iff s ⊑ r, s ∘ t, and s' ⊑ s for all s' where s ⊑ s' ⊑ r and s' ∘ t |
| **Maximal state** | s is maximal iff t ⊑ s for every compatible state t ∘ s |
| **World-state** | w ∈ W iff w is a maximal possible state |
| **Necessary state** | s ∈ N iff s ~ t implies s = t |

### Task Relation Constraints

| Constraint | Formulation |
|------------|-------------|
| **Compositionality** | If s ⇒_x t and t ⇒_y u, then s ⇒_{x+y} u |
| **Parthood (Left)** | If d ⊑ s and s ⇒_x t, then d ⇒_x r for some r ⊑ t |
| **Parthood (Right)** | If r ⊑ t and s ⇒_x t, then d ⇒_x r for some d ⊑ s |
| **Containment (L)** | If s ∈ P, d ⊑ s, and d ⇒_x r, then s ⇒_x t.r for some t ∈ S |
| **Containment (R)** | If t ∈ P, r ⊑ t, and d ⇒_x r, then s.d ⇒_x t for some s ∈ S |
| **Maximality** | If s ∈ S and t ∈ P, there is a maximal t-compatible part r ∈ s_t |

The Containment constraints ensure that tasks between parts of possible states can be extended to tasks between the states themselves. The Maximality constraint ensures that for any state and possible state, there exists a maximal part compatible with that possible state.

### World-History

A *world-history* over a causal frame F is a function τ : X → W where:
- X ⊆ D is a convex subset of the temporal order
- τ(x) ⇒_{y-x} τ(y) for all times x, y ∈ X where x ≤ y

The set of all world-histories over F is denoted H_F.

World-histories assign world-states to times in a way that respects the task relation. The constraint ensures that consecutive world-states are connected by appropriate tasks. The set of maximal possible evolutions M_Z equals the set of world-histories H_Z (proven in Brast-McKie, "Counterfactual Worlds"), showing that world-histories can be characterized as maximal elements among possible evolutions under the pointwise parthood ordering.

### Core Model

A *core model* is a structure **M** = ⟨S, ⊑, D, ⇒, I⟩ where:
- ⟨S, ⊑, D, ⇒⟩ is a core frame
- I is an interpretation as in the Constitutive Foundation

### Truth Conditions

Truth is evaluated relative to a model M, world-history τ, time x ∈ D, variable assignment σ, and temporal index i⃗ = ⟨i₁, i₂, ...⟩:

#### Atomic Sentences

| | Condition |
|---|-----------|
| M, τ, x, σ, i⃗ ⊨ F(t₁,...,tₙ) | iff there is some f ∈ v_F where f(⟦t₁⟧^σ_M, ..., ⟦tₙ⟧^σ_M) ⊑ τ(x) |
| M, τ, x, σ, i⃗ ⊭ F(t₁,...,tₙ) | iff there is some f ∈ f_F where f(⟦t₁⟧^σ_M, ..., ⟦tₙ⟧^σ_M) ⊑ τ(x) |

It is derivable that M, τ, x, σ, i⃗ ⊨ A iff it is not the case that M, τ, x, σ, i⃗ ⊭ A. This justifies using ⊨ alone for truth and ⊭ for falsehood.

#### Lambda Abstraction

| Operator | Truth Condition |
|----------|-----------------|
| **(λx.A)(t)** | M, τ, x, σ, i⃗ ⊨ (λx.A)(t) iff M, τ, x, σ[⟦t⟧^σ_M/x], i⃗ ⊨ A |

#### Universal Quantifier

| Operator | Truth Condition |
|----------|-----------------|
| **∀y.A** | M, τ, x, σ, i⃗ ⊨ ∀y.A iff M, τ, x, σ[s/y], i⃗ ⊨ A for all s ∈ S |

#### Actuality Predicate

| Operator | Truth Condition |
|----------|-----------------|
| **Act(t)** | M, τ, x, σ, i⃗ ⊨ Act(t) iff ⟦t⟧^σ_M ⊑ τ(x) |

The actuality predicate checks whether a state is part of the current world-state. Combined with the universal quantifier, this enables restricting quantification to actually existing objects:

| Restricted Quantifier | Truth Condition |
|----------------------|-----------------|
| **∀y(Act(y) → A)** | True iff A holds for all states that are parts of τ(x) |

**Barcan formulas**: The unrestricted universal quantifier validates the Barcan formulas (∀x□A → □∀xA and its converse), while the actuality-restricted quantifier does not. This allows modeling domains that vary across possible worlds.

#### Extensional Connectives

| Operator | Truth Condition |
|----------|-----------------|
| **¬A** | M, τ, x, σ, i⃗ ⊨ ¬A iff M, τ, x, σ, i⃗ ⊭ A |
| **A ∧ B** | M, τ, x, σ, i⃗ ⊨ A ∧ B iff M, τ, x, σ, i⃗ ⊨ A and M, τ, x, σ, i⃗ ⊨ B |
| **A ∨ B** | M, τ, x, σ, i⃗ ⊨ A ∨ B iff M, τ, x, σ, i⃗ ⊨ A or M, τ, x, σ, i⃗ ⊨ B |
| **A → B** | M, τ, x, σ, i⃗ ⊨ A → B iff M, τ, x, σ, i⃗ ⊭ A or M, τ, x, σ, i⃗ ⊨ B |

#### Modal Operators

| Operator | Truth Condition | Reading |
|----------|-----------------|---------|
| **□A** | M, τ, x, σ, i⃗ ⊨ □A iff M, α, x, σ, i⃗ ⊨ A for all α ∈ H_F | "Necessarily A" |
| **◇A** | M, τ, x, σ, i⃗ ⊨ ◇A iff M, α, x, σ, i⃗ ⊨ A for some α ∈ H_F | "Possibly A" |

**Equivalence**: ◇A ≡ ¬□¬A

Metaphysical necessity can also be defined via counterfactuals: □A := ⊤ □→ A. This yields an S5 modal logic.

#### Core Tense Operators

| Operator | Truth Condition | Reading |
|----------|-----------------|---------|
| **HA** | M, τ, x, σ, i⃗ ⊨ HA iff M, τ, y, σ, i⃗ ⊨ A for all y ∈ D where y < x | "It has always been that A" |
| **GA** | M, τ, x, σ, i⃗ ⊨ GA iff M, τ, y, σ, i⃗ ⊨ A for all y ∈ D where y > x | "It will always be that A" |
| **PA** | M, τ, x, σ, i⃗ ⊨ PA iff M, τ, y, σ, i⃗ ⊨ A for some y ∈ D where y < x | "It was the case that A" |
| **FA** | M, τ, x, σ, i⃗ ⊨ FA iff M, τ, y, σ, i⃗ ⊨ A for some y ∈ D where y > x | "It will be the case that A" |

**Equivalences**:
- PA ≡ ¬H¬A
- FA ≡ ¬G¬A

**Derived Operators**:
- **△A** := HA ∧ A ∧ GA ("Always A" - at all times)
- **▽A** := PA ∨ A ∨ FA ("Sometimes A" - at some time)

#### Extended Tense Operators: Since and Until

| Operator | Truth Condition |
|----------|-----------------|
| **A ◁ B** (Since) | M, τ, x, σ, i⃗ ⊨ A ◁ B iff there exists z < x where M, τ, z, σ, i⃗ ⊨ B and M, τ, y, σ, i⃗ ⊨ A for all y where z < y < x |
| **A ▷ B** (Until) | M, τ, x, σ, i⃗ ⊨ A ▷ B iff there exists z > x where M, τ, z, σ, i⃗ ⊨ B and M, τ, y, σ, i⃗ ⊨ A for all y where x < y < z |

**Reading**:
- "A since B" means B was true at some past time, and A has been true ever since
- "A until B" means B will be true at some future time, and A is true until then

#### Counterfactual Conditional (□→)

**Mereological formulation**:

> M, τ, x, σ, i⃗ ⊨ φ □→ C iff for all t ∈ v_φ and β ∈ H_F: if s.t ⊑ β(x) for some maximal t-compatible part s ∈ τ(x)_t, then M, β, x, σ, i⃗ ⊨ C

Where:
- v_φ is the set of exact verifiers for φ
- τ(x)_t is the set of maximal t-compatible parts of τ(x)
- s ∈ τ(x)_t is maximal iff s ⊑ τ(x), s ∘ t, and for all s' where s ⊑ s' ⊑ τ(x) and s' ∘ t, we have s' ⊑ s

**Intuitive reading**: A counterfactual "if φ were the case, then C" is true at world τ and time x iff the consequent C is true in any world β at x where β(x) is the result of minimally changing τ(x) to make the antecedent φ true.

**Imposition**: We write t →_w w' ("imposing t on w yields w'") iff there exists maximal t-compatible part s ∈ w_t where s.t ⊑ w'.

#### Store and Recall Operators (↑, ↓)

For cross-temporal reference within counterfactual evaluation, the context includes a temporal index i⃗ = ⟨i₁, i₂, ...⟩ of stored times:

| Operator | Truth Condition | Effect |
|----------|-----------------|--------|
| **↑ⁱA** | M, τ, x, σ, i⃗ ⊨ ↑ⁱA iff M, τ, x, σ, i⃗[x/iₖ] ⊨ A | Store: replaces iₖ with current time x |
| **↓ⁱA** | M, τ, x, σ, i⃗ ⊨ ↓ⁱA iff M, τ, iₖ, σ, i⃗ ⊨ A | Recall: shifts evaluation to stored time iₖ |

**Example** (tensed counterfactuals):
- ↓¹(B □→ FH) - "If B had occurred at the stored time, then H would have occurred at some future time"
- ↑²↓¹(B □→ ↓²H) - "Store now, recall past time, if B then H at the stored present"

### Bimodal Interaction Principles

The task semantics validates these perpetuity principles connecting modal and temporal operators:

| Principle | Formula | Reading |
|-----------|---------|---------|
| **P1** | □φ → △φ | Necessary implies always |
| **P2** | ▽φ → ◇φ | Sometimes implies possible |
| **P3** | □△φ ↔ △□φ | Necessary-always commutativity |
| **P4** | ◇▽φ ↔ ▽◇φ | Possible-sometimes commutativity |
| **P5** | □φ → □△φ | Necessary implies necessary-always |
| **P6** | ▽◇φ → ◇φ | Sometimes-possible implies possible |

### Temporal Frame Constraints

Different temporal structures yield different valid principles. The framework does not assume discrete time:

| Constraint | Description | Corresponding Axiom |
|------------|-------------|---------------------|
| **Dense** | Between any two times there is another | GGφ → Gφ |
| **Complete** | Every bounded set has a least upper bound | △(Hφ → FHφ) → (Hφ → Gφ) |
| **Unbounded Past** | No earliest time | P⊤ |
| **Unbounded Future** | No latest time | F⊤ |

### Logical Consequence (Dynamical Foundation)

> Γ ⊨ A iff for any model M, world-history τ ∈ H_F, time x ∈ D, assignment σ, and temporal index i⃗: if M, τ, x, σ, i⃗ ⊨ B for all B ∈ Γ, then M, τ, x, σ, i⃗ ⊨ A

### Counterfactual Logic Axiom Schemata

**Core Rules**:

| Axiom | Schema | Name |
|-------|--------|------|
| **R1** | If Γ ⊢ C, then φ □→ Γ ⊢ φ □→ C | Closure under deduction |
| **C1** | φ □→ φ | Identity |
| **C2** | φ, φ □→ A ⊢ A | Counterfactual Modus Ponens |
| **C3** | φ □→ ψ, φ ∧ ψ □→ A ⊢ φ □→ A | Weakened Transitivity |
| **C4** | φ ∨ ψ □→ A ⊢ φ ∧ ψ □→ A | Disjunction-Conjunction |
| **C5** | φ ∨ ψ □→ A ⊢ φ □→ A | Simplification (Left) |
| **C6** | φ ∨ ψ □→ A ⊢ ψ □→ A | Simplification (Right) |
| **C7** | φ □→ A, ψ □→ A, φ ∧ ψ □→ A ⊢ φ ∨ ψ □→ A | Disjunction Introduction |

**Modal Axioms**:

| Axiom | Schema |
|-------|--------|
| **M1** | ⊤ |
| **M2** | ¬⊥ |
| **M3** | A → □◇A |
| **M4** | □A → □□A |
| **M5** | □(φ → A) ⊢ φ □→ A |

---

## Epistemic Extension

[DETAILS]

The Epistemic Extension extends the Dynamical Foundation with structures for belief, knowledge, and probability.

### Frame Extension

[DETAILS]

The epistemic frame extends the core frame with a credence function assigning probabilities to state transitions.

[QUESTION: What is the exact structure of the credence function? Does it assign probabilities to individual state transitions or to sets of transitions?]

### Operators

| Operator | Intended Reading |
|----------|------------------|
| **B_a φ** | Agent a believes that φ |
| **K_a φ** | Agent a knows that φ |
| **Pr(φ) ≥ r** | The probability of φ is at least r |

[DETAILS: Full semantic clauses for epistemic operators pending specification]

### Indicative Conditionals

[DETAILS]

[QUESTION: How do indicative conditionals relate to counterfactual conditionals in the semantic framework?]

---

## Normative Extension

[DETAILS]

The Normative Extension extends the Dynamical Foundation with structures for obligation, permission, and value.

### Frame Extension

[DETAILS]

The normative frame extends the core frame with value orderings over states.

[QUESTION: How are value orderings structured? Are they complete orderings or partial orderings? Are they agent-relative?]

### Operators

| Operator | Intended Reading |
|----------|------------------|
| **O φ** | It ought to be that φ |
| **P φ** | It is permitted that φ |
| **φ ≻ ψ** | φ is preferred to ψ |

[DETAILS: Full semantic clauses for normative operators pending specification]

### Normative Explanation

[DETAILS]

[QUESTION: How does normative explanation relate to causal explanation?]

---

## Spatial Extension

[DETAILS]

The Spatial Extension extends the Dynamical Foundation with structures for spatial reasoning and location.

### Frame Extension

[DETAILS]

The spatial frame extends the core frame with:
- **Location space** L = set of spatial locations
- **Spatial relations**: adjacency, containment, distance

[QUESTION: What spatial primitives are required? Should locations be mereological (with parts) or set-theoretic?]

### Operators

| Operator | Intended Reading |
|----------|------------------|
| **Here(A)** | A holds at the current location |
| **Somewhere(A)** | A holds at some location |
| **Everywhere(A)** | A holds at all locations |
| **Near(A)** | A holds at an adjacent location |

[DETAILS: Full semantic clauses for spatial operators pending specification]

---

## Agential Extension

The Agential Extension requires at least one of the Epistemic, Normative, or Spatial Extensions to be loaded. It provides structures for ability and free choice reasoning, capturing what agents can bring about through their own capacities.

### Frame Extension

The agential frame extends the core frame with:

| Component | Type | Description |
|-----------|------|-------------|
| **Agent set** | A | Set of agents capable of action |
| **Choice function** | C : A x T -> Partition(H) | Partitions histories into choice cells |
| **Capacity assignment** | K : A -> P(Prop) | Agent-intrinsic capacities |
| **Dependence relation** | D : A x W -> P(W) | Dependence domain for each agent at each world |

The choice function C(a, x) partitions all histories passing through time x into cells. Histories in the same cell are "choice-equivalent" for agent a at x: the agent has made the same choice in both.

### Ability Operators

#### Truth Conditions for Ability (Can_a)

[DETAILS: Precise formalization pending]

**Informal semantics**:

> M, tau, x, sigma |- Can_a(p) iff
> there exists a choice c in C(a, x) containing tau such that:
>   (1) for some history h in c: M, h, x, sigma |- p
>   (2) for all worlds w in D(a, tau(x)): if agent a makes choice c at w, then p holds at w

Condition (1) ensures there is a choice leading to p. Condition (2) ensures robustness across the agent's dependence domain - the ability persists regardless of what others do.

#### Truth Conditions for Generic Ability (Able_a)

> M, tau, x, sigma |- Able_a(p) iff
> for most worlds w in the agent's capacity set K(a):
>   M, w, x, sigma |- Can_a(p)

Generic ability is a dispositional notion: the agent reliably has the specific ability across a range of circumstances.

#### Truth Conditions for Inability (Cannot_a)

> M, tau, x, sigma |- Cannot_a(p) iff
> not (M, tau, x, sigma |- Can_a(p))

Inability is simply the negation of ability.

### Free Choice Operators

#### Truth Conditions for Free Permission (FP)

[DETAILS: Precise formalization pending]

**Hyperintensional semantics** (leveraging Constitutive Foundation):

> M, tau, x, sigma |- FP(A or B) iff
> there exists a state s such that:
>   (1) s is a permitted state (all permitted worlds contain s as a part)
>   (2) s = s_A . s_B where s_A verifies A and s_B verifies B

This captures free choice: permission for a disjunction entails permission for each disjunct because the permitted state decomposes mereologically.

**Alternative modal semantics**:

> M, tau, x, sigma |- FP(p) iff
> there exists a permitted world w where p holds AND
> the choice to bring about p is available to the relevant agent

#### Truth Conditions for Free Prohibition (FF)

> M, tau, x, sigma |- FF(p) iff
> not (M, tau, x, sigma |- FP(p))

#### Truth Conditions for Choice Set (Ch)

> M, tau, x, sigma |- Ch(p, q, ...) iff
> M, tau, x, sigma |- FP(p) and M, tau, x, sigma |- FP(q) and ...

The choice set operator confirms that all listed alternatives are freely permitted.

### Open Questions

1. **STIT integration**: Should the choice function use full STIT branching-time semantics with moments and histories, or can a simpler approximation suffice?

2. **Dependence domain specification**: How exactly is D(a, w) determined? By the agent's intrinsic properties? By counterfactual analysis?

3. **Interaction with deontic operators**: What axioms govern the relationship between Can_a and P (deontic permission)?
   - Does `Can_a(p) and P(p)` imply the agent should do p?
   - How does `Can_a(p) and O(not p)` (akrasia) work semantically?

4. **Multi-agent extension**: How do joint abilities work?
   - `Can_{a,b}(p)` - agents a and b together can bring about p
   - Requires coordination mechanism in frame

[DETAILS: Full formal semantics pending specification]

---

## Reflection Extension

The Reflection Extension enables first-person metacognitive reasoning through the 'I' operator.
Where the Agential Extension projects epistemic operators onto other agents, the Reflection Extension projects them onto the self, enabling perspectival distance from one's own beliefs, abilities, and goal-states.

### Core Insight

The 'I' operator transforms direct modal expressions into self-aware epistemic stances.
Consider the difference between:

| Expression | Reading | Epistemic Subject |
|------------|---------|-------------------|
| Mu(raining) | "It must be raining" | Implicit/absent |
| I(raining) | "I believe it is raining" | Explicit (self) |

The direct expression commits the speaker without self-awareness; the self-aware expression registers the speaker as the epistemic subject.
This distinction follows Kaplan's character/content framework and Lewis's centered-worlds semantics.

### Frame Extension

The Reflection frame extends the Agential frame with:

| Component | Description |
|-----------|-------------|
| **Self-Index** | Distinguished agent index `self` in the agent set A |
| **Self-Accessibility** | Reflexive accessibility relation R_self for self-knowledge |
| **Self-Model** | Function SM: W -> SelfState mapping world-states to self-representations |
| **Commitment Register** | Set CR(w) of propositions explicitly self-ascribed at world w |

The self-accessibility relation R_self satisfies:
- **Seriality (D)**: For all w, there exists w' such that (w, w') in R_self
- **Transitivity (4)**: Positive introspection: I(phi) -> I(I(phi))
- **Euclidean (5)**: Negative introspection: -I(phi) -> I(-I(phi))

### Operators

#### Self-Knowledge and Self-Belief

| Operator | Symbol | Reading |
|----------|--------|---------|
| **Metacognitive I** | I(phi) | "I judge/believe that phi" |
| **Self-Knowledge** | I_K(phi) | "I know that phi" |
| **Self-Belief** | I_B(phi) | "I believe that phi" |
| **Self-Uncertainty** | I_?(phi) | "I am uncertain whether phi" |

#### Ability Introspection

| Operator | Symbol | Reading |
|----------|--------|---------|
| **Self-Ability** | I_Can(phi) | "I can bring about phi" |
| **Ability-Knowledge** | K_self(Can_self(phi)) | "I know I can bring about phi" |
| **Limitation-Knowledge** | K_self(-Can_self(phi)) | "I know I cannot bring about phi" |

#### Goal-Distance

| Operator | Symbol | Reading |
|----------|--------|---------|
| **Goal-Distance** | Dist(G, n) | "Goal G is n steps away" |
| **Goal-Progress** | Closer(G) | "I am getting closer to goal G" |
| **Goal-Achievable** | Achievable(G) | "Goal G is achievable" |

#### Attributed Belief (How Others Perceive Self)

| Operator | Symbol | Reading |
|----------|--------|---------|
| **Other's Belief About Self** | B_j(I(phi)) | "Agent j believes that I believe phi" |
| **Other's Belief About Self-Ability** | B_j(I_Can(phi)) | "Agent j believes I can do phi" |

### Truth Conditions

Given evaluation context (M, tau, x, sigma, i-vector):

**Primary 'I' Operator**:

M, tau, x, sigma |- I(phi) iff:
1. For all w' accessible via R_self from tau(x): M, tau[w'/x], x, sigma |- phi
2. phi is in the Commitment Register CR(tau(x))

The second condition distinguishes explicit self-attribution from mere truth across epistemic alternatives.

**Derived Operators**:

| Operator | Definition |
|----------|------------|
| I_K(phi) | I(K(phi)) where K is factive |
| I_B(phi) | I(B(phi)) |
| I_?(phi) | I(-B(phi) & -B(-phi)) |
| I_Can(phi) | There exists action-sequence a achievable by self leading to phi |

**Temporal Interaction**:

| Formula | Reading |
|---------|---------|
| P(I(phi)) | "I previously believed phi" |
| I(P(phi)) | "I believe phi was the case" |
| F(I(phi)) | "I will believe phi" |
| I(F(phi)) | "I believe phi will be the case" |

These are not equivalent, demonstrating the interaction between temporal and metacognitive perspectives.

### Key Axioms

| Axiom | Name | Schema |
|-------|------|--------|
| **I-T** | Veridicality of self-knowledge | I_K(phi) -> phi |
| **I-4** | Positive introspection | I(phi) -> I(I(phi)) |
| **I-5** | Negative introspection | -I(phi) -> I(-I(phi)) |
| **I-D** | Consistency | -I(false) |
| **I-Commit** | Commitment closure | I(phi) -> Register(phi) |

### Relationship to Agential Extension

The Reflection Extension inherits from the Epistemic Extension in parallel with the Agential Extension:

```
                Epistemic Extension
                (B_a, K_a, Pr, Mi, Mu)
                       |
          +------------+------------+
          |                         |
          v                         v
  Agential Extension         Reflection Extension
  (modeling others)          (modeling self)
          |                         |
 B_j(phi): "j believes phi"  I(phi): "I believe phi"
 K_j(phi): "j knows phi"     I_K(phi): "I know I know phi"
```

Both extensions apply the epistemic apparatus in different directions:
- **Agential**: Outward projection onto other agents
- **Reflection**: Inward projection onto self

[DETAILS]

---

## References

### Academic Sources
- Fine, K. (2017). "Truthmaker Semantics" - Foundation for hyperintensional propositions
- Brast-McKie, B. "Possible Worlds" (JPL) - Task semantics, bimodal logic
- Brast-McKie, B. "Counterfactual Worlds" (JPL) - Counterfactual conditional semantics

### Related Documentation
- [layer-extensions.md](layer-extensions.md) - Extension architecture overview
- [GLOSSARY.md](../reference/GLOSSARY.md) - Term definitions
- [METHODOLOGY.md](../user-guide/METHODOLOGY.md) - Philosophical methodology
