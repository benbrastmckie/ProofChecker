// ============================================================================
// 01-syntax.typ
// Syntax chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *

= Syntax

== Formulas

Formulas are defined inductively with six primitive constructors.

#definition("Formula")[
  The type `Formula` is defined by:
  $ phi.alt, psi ::= p | bot | phi.alt arrow.r psi | square.stroked phi.alt | H phi.alt | G phi.alt $
  where $p$ ranges over sentence letters (type `String`).
]

#figure(
  table(
    columns: 4,
    stroke: none,
    table.hline(),
    table.header(
      [*Symbol*], [*Name*], [*Lean*], [*Reading*],
    ),
    table.hline(),
    [$p, q, r$], [Atom], [`atom s`], [sentence letter],
    [$bot$], [Bottom], [`bot`], [falsity],
    [$phi.alt arrow.r psi$], [Implication], [`imp`], ["if $phi.alt$, then $psi$"],
    [$square.stroked phi.alt$], [Necessity], [`box`], ["necessarily $phi.alt$"],
    [$H phi.alt$], [Always past], [`all_past`], ["it has always been that $phi.alt$"],
    [$G phi.alt$], [Always future], [`all_future`], ["it is always going to be that $phi.alt$"],
    table.hline(),
  ),
  caption: none,
)

== Derived Operators

The following operators are defined in terms of the primitives.

#definition("Propositional")[
  $
    not phi.alt &:= phi.alt arrow.r bot \
    phi.alt and psi &:= not (phi.alt arrow.r not psi) \
    phi.alt or psi &:= not phi.alt arrow.r psi
  $
]

#figure(
  table(
    columns: 4,
    stroke: none,
    table.hline(),
    table.header(
      [*Symbol*], [*Name*], [*Lean*], [*Reading*],
    ),
    table.hline(),
    [$not phi.alt$], [Negation], [`neg`], ["it is not the case that $phi.alt$"],
    [$phi.alt and psi$], [Conjunction], [`and`], ["$phi.alt$ and $psi$"],
    [$phi.alt or psi$], [Disjunction], [`or`], ["$phi.alt$ or $psi$"],
    table.hline(),
  ),
  caption: none,
)

#definition("Modal")[
  $
    diamond.stroked phi.alt &:= not square.stroked not phi.alt
  $
]

#figure(
  table(
    columns: 4,
    stroke: none,
    table.hline(),
    table.header(
      [*Symbol*], [*Name*], [*Lean*], [*Reading*],
    ),
    table.hline(),
    [$diamond.stroked phi.alt$], [Possibility], [`pos`], ["possibly $phi.alt$"],
    table.hline(),
  ),
  caption: none,
)

#definition("Temporal")[
  $
    P phi.alt &:= not H not phi.alt \
    F phi.alt &:= not G not phi.alt \
    triangle.stroked.t phi.alt &:= H phi.alt and phi.alt and G phi.alt \
    triangle.stroked.b phi.alt &:= P phi.alt or phi.alt or F phi.alt
  $
]

#figure(
  table(
    columns: 4,
    stroke: none,
    table.hline(),
    table.header(
      [*Symbol*], [*Name*], [*Lean*], [*Reading*],
    ),
    table.hline(),
    [$P phi.alt$], [Sometime past], [`some_past`], ["it has been that $phi.alt$"],
    [$F phi.alt$], [Sometime future], [`some_future`], ["it is going to be that $phi.alt$"],
    [$triangle.stroked.t phi.alt$], [Always], [`always`], ["always $phi.alt$"],
    [$triangle.stroked.b phi.alt$], [Sometimes], [`sometimes`], ["sometimes $phi.alt$"],
    table.hline(),
  ),
  caption: none,
)

== Temporal Duality

The `swap_temporal` function exchanges past and future operators.

#definition("Temporal Swap")[
  The function $chevron.l S chevron.r : "Formula" arrow.r "Formula"$ is defined by induction on the complexity of formulas:
  $
    chevron.l S chevron.r p &= p \
    chevron.l S chevron.r bot &= bot \
    chevron.l S chevron.r (phi.alt arrow.r psi) &= (chevron.l S chevron.r phi.alt arrow.r chevron.l S chevron.r psi) \
    chevron.l S chevron.r square.stroked phi.alt &= square.stroked chevron.l S chevron.r phi.alt \
    chevron.l S chevron.r H phi.alt &= G chevron.l S chevron.r phi.alt \
    chevron.l S chevron.r G phi.alt &= H chevron.l S chevron.r phi.alt
  $
]

#theorem("Involution")[
  $chevron.l S chevron.r chevron.l S chevron.r phi.alt = phi.alt$
]
