/-!
# Logos.Reflection - Layer 7 (Reflection Extension)

This layer extends the Epistemic and Agential Extensions with self-modeling operators:
- Metacognitive operator (`I`)
- Self-knowledge operators (`I_K`, `I_B`)
- Ability introspection operators (`I_Can`)
- Goal-distance operators (`Dist`, `Closer`, `Achievable`)
- Attributed belief operators (`B_j(I(phi))`)

## Core Insight

The 'I' operator transforms direct modal expressions into self-aware epistemic stances:
- Direct: "It must be raining" (Mu(raining)) - epistemic necessity without self-reference
- Self-aware: "I believe it is raining" (I(raining)) - explicit first-person epistemic stance

This follows Kaplan's character/content framework and Lewis's centered-worlds semantics.

## Frame Extension

The Reflection frame extends the Agential frame with:
- **Self-Index**: Distinguished agent index `self` in agent set A
- **Self-Accessibility**: Reflexive accessibility relation R_self for self-knowledge
- **Self-Model**: Function SM : W -> SelfState mapping world-states to self-representations
- **Commitment Register**: Set CR(w) of propositions explicitly self-ascribed at world w

The self-accessibility relation R_self satisfies:
- Seriality (D): For all w, exists w' such that (w, w') in R_self
- Transitivity (4): Positive introspection: I(phi) -> I(I(phi))
- Euclidean (5): Negative introspection: -I(phi) -> I(-I(phi))

## Operators

| Operator | Reading |
|----------|---------|
| `I(A)` | I judge/believe that A |
| `I_K(A)` | I know that A |
| `I_B(A)` | I believe that A |
| `I_?(A)` | I am uncertain whether A |
| `I_Can(A)` | I can bring about A |
| `Dist(G, n)` | Goal G is n steps away |
| `Closer(G)` | I am getting closer to G |
| `Achievable(G)` | Goal G is achievable |
| `B_j(I(A))` | Agent j believes I believe A |

## Key Axioms

- Veridicality: `I_K(A) -> A`
- Positive Introspection: `I(A) -> I(I(A))`
- Negative Introspection: `-I(A) -> I(-I(A))`
- Consistency: `-I(false)`
- Commitment Closure: `I(A) -> Register(A)`

## Relationship to Agential Extension

The Reflection Extension inherits from the Epistemic Extension in parallel with the Agential Extension:
- Agential: B_j(phi) projects epistemic operators onto other agents
- Reflection: I(phi) projects epistemic operators onto self

**Status**: Planned for future development
**Prerequisites**: Agential Extension completion
**Estimated Timeline**: Post-Agential completion

See: docs/research/layer-extensions.md (Reflection Extension section)
-/

namespace Logos.SubTheories.Reflection
  -- Layer 7 implementation to be added
  -- Extension point: Formula type will extend Agential.Syntax.Formula
  -- Extension point: Semantics will use SelfModel, ReflexiveAccessibility, CommitmentRegister
  -- Extension point: Frame will add self-index, self-accessibility relation, commitment register
end Logos.SubTheories.Reflection
