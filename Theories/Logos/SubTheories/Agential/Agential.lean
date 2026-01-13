/-!
# Logos.Agential - Agential Extension

This layer extends the Logos framework with agential operators for ability
and free choice reasoning. The Agential Extension occupies a position in
the extension hierarchy that requires at least one middle extension
(Epistemic, Normative, or Spatial) to be loaded.

## Ability Operators

Ability modals express what an agent can bring about through their own
capacities, distinct from circumstantial possibility:

| Operator | Notation | Reading |
|----------|----------|---------|
| **Ability** | `Can_a(p)` | "Agent a can bring about p" |
| **Generic Ability** | `Able_a(p)` | "Agent a has the general ability to p" |
| **Inability** | `Cannot_a(p)` | "Agent a cannot bring about p" |

Ability modals involve "dependence domains" that track counterfactual agency,
keeping facts about the agent fixed while varying facts about circumstances.

## Free Choice Operators

Free choice modals address the inference from disjunctive permission to
individual permissions (the Free Choice Permission paradox):

| Operator | Notation | Reading |
|----------|----------|---------|
| **Free Permission** | `FP(p)` | "p is freely permitted (choice available)" |
| **Free Prohibition** | `FF(p)` | "p is freely forbidden" |
| **Choice Set** | `Ch(p,q,...)` | "Choice among alternatives p, q, ..." |

The hyperintensional approach (using truthmaker semantics) resolves free
choice puzzles naturally within Logos's mereological state space.

## Frame Extension

The agential frame extends the core frame with:

| Component | Description |
|-----------|-------------|
| **Agent set** A | Set of agents |
| **Choice function** C : A -> T -> Partition(H) | Agent choices partition histories |
| **Capacity assignment** K : A -> Set(Prop) | Agent-intrinsic capacities |
| **Dependence relation** D : A -> World -> Set(World) | Worlds in agent's dependence domain |

The choice function follows STIT (Sees To It That) semantics, partitioning
possible histories into choice cells for each agent at each time.

## Key Axioms (Tentative)

| Schema | Name | Reading |
|--------|------|---------|
| `Can_a(p) -> diamond(p)` | Ability-Possibility | Ability implies possibility |
| `Can_a(p or q) -> Can_a(p) or Can_a(q)` | Ability-FreeChoice | Ability distributes over disjunction |
| `FP(p or q) -> FP(p) and FP(q)` | Permission-FreeChoice | Free permission validates free choice |
| `Cannot_a(p) <-> not Can_a(p)` | Inability-Dual | Inability is dual of ability |

## Semantic Approach

### Ability Truth Conditions

> M, tau, x, sigma |- Can_a(p) iff
> there exists history h in Choices(a, x)(tau) such that M, h, x, sigma |- p
> AND for all worlds w in the dependence domain D_a(tau, x):
>   if the same choice is made, p holds in w

### Free Choice Truth Conditions

> FP(A or B) holds iff
> there is a state s verifying (A or B) in all permitted ways,
> AND this state decomposes into parts verifying A and verifying B separately

This leverages the mereological state space from the Constitutive Foundation.

## Design Decisions

### Open Questions

1. **STIT vs simpler semantics**: Should ability require full STIT-style
   branching time, or can it be captured with simpler possible-worlds semantics?
   Initial approach: Simpler semantics first, extend to STIT later if needed.

2. **Interaction with deontic operators**: How do ability and permission interact?
   `Can_a(p) and P(p)` vs `Can_a(p) and O(not p)` (can but ought not)

3. **Multi-agent coordination**: How do individual and collective agency interact?
   Joint abilities `Can_{a,b}(p)` for group agency.

**Status**: Planned for future development
**Prerequisites**: Explanatory Extension, at least one middle extension (Epistemic/Normative/Spatial)
**Estimated Timeline**: TBD (dependent on middle extension completion)

See: docs/research/layer-extensions.md Section 6
See: docs/research/recursive-semantics.md Agential Extension section
-/

namespace Logos.SubTheories.Agential
  -- Agential Extension implementation to be added

  -- Extension point: Formula type will extend Core.Syntax.Formula with ability and free choice operators
  -- Extension point: Semantics will use Agent set, Choice function, and Dependence relation
  -- Extension point: Frame will add agent-indexed accessibility for ability modals

  -- Future: Consider STIT branching-time semantics if simpler approach proves insufficient
  -- Future: Multi-agent abilities (group STIT operators)
  -- Future: Interaction axioms between ability and deontic operators
end Logos.SubTheories.Agential
