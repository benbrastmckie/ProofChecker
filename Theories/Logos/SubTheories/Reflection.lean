import Logos.SubTheories.Reflection.Reflection

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

**Status**: Planned for future development
**Prerequisites**: Agential Extension completion

See: docs/research/layer-extensions.md (Reflection Extension section)
-/
