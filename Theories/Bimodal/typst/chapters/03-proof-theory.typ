// ============================================================================
// 03-proof-theory.typ
// Proof Theory chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *

= Proof Theory

== Axiom Schemata

The TM proof system has 14 axiom schemata.

=== Propositional Axioms

#axiom("K - Distribution")[
  $(phi.alt arrow.r (psi arrow.r chi)) arrow.r ((phi.alt arrow.r psi) arrow.r (phi.alt arrow.r chi))$
]

#axiom("S - Weakening")[
  $phi.alt arrow.r (psi arrow.r phi.alt)$
]

#axiom("EFQ - Ex Falso Quodlibet")[
  $bot arrow.r phi.alt$
]

#axiom("Peirce")[
  $((phi.alt arrow.r psi) arrow.r phi.alt) arrow.r phi.alt$
]

=== Modal Axioms (S5)

#axiom("MT - Modal T")[
  $square.stroked phi.alt arrow.r phi.alt$
]

#axiom("M4 - Modal 4")[
  $square.stroked phi.alt arrow.r square.stroked square.stroked phi.alt$
]

#axiom("MB - Modal B")[
  $phi.alt arrow.r square.stroked diamond.stroked phi.alt$
]

#axiom("M5 - Modal 5 Collapse")[
  $diamond.stroked square.stroked phi.alt arrow.r square.stroked phi.alt$
]

#axiom("MK - Modal Distribution")[
  $square.stroked (phi.alt arrow.r psi) arrow.r (square.stroked phi.alt arrow.r square.stroked psi)$
]

=== Temporal Axioms

#axiom("TK - Temporal Distribution")[
  $G(phi.alt arrow.r psi) arrow.r (G phi.alt arrow.r G psi)$
]

#axiom("T4 - Temporal 4")[
  $G phi.alt arrow.r G G phi.alt$
]

#axiom("TA - Temporal A")[
  $phi.alt arrow.r G P phi.alt$
]

#axiom("TL - Temporal L")[
  $triangle.stroked.t phi.alt arrow.r G H phi.alt$
]

=== Modal-Temporal Interaction

#axiom("MF - Modal-Future")[
  $square.stroked phi.alt arrow.r square.stroked G phi.alt$
]

#axiom("TF - Temporal-Future")[
  $square.stroked phi.alt arrow.r G square.stroked phi.alt$
]

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Axiom*], [*Lean Constructor*], [*Pattern*],
    ),
    table.hline(),
    [K], [`Axiom.prop_k`], [Distribution],
    [S], [`Axiom.prop_s`], [Weakening],
    [EFQ], [`Axiom.ex_falso`], [Explosion],
    [Peirce], [`Axiom.peirce`], [Classical],
    [MT], [`Axiom.modal_t`], [Reflexivity],
    [M4], [`Axiom.modal_4`], [Transitivity],
    [MB], [`Axiom.modal_b`], [Symmetry],
    [M5], [`Axiom.modal_5_collapse`], [S5 collapse],
    [MK], [`Axiom.modal_k_dist`], [Modal distribution],
    [TK], [`Axiom.temp_k_dist`], [Temporal distribution],
    [T4], [`Axiom.temp_4`], [Temporal transitivity],
    [TA], [`Axiom.temp_a`], [Connectedness],
    [TL], [`Axiom.temp_l`], [Introspection],
    [MF], [`Axiom.modal_future`], [Modal-future],
    [TF], [`Axiom.temp_future`], [Temporal-modal],
    table.hline(),
  ),
  caption: none,
)

== Inference Rules

The proof system has 7 inference rules.

#definition("Axiom Rule")[
  If $phi.alt$ matches an axiom schema, then $Gamma tack.r phi.alt$.
]

#definition("Assumption Rule")[
  If $phi.alt in Gamma$, then $Gamma tack.r phi.alt$.
]

#definition("Modus Ponens")[
  $
    (Gamma tack.r phi.alt arrow.r psi quad quad Gamma tack.r phi.alt) / (Gamma tack.r psi)
  $
]

#definition("Necessitation")[
  $
    (tack.r phi.alt) / (tack.r square.stroked phi.alt)
  $
  Applies only to theorems (empty context).
]

#definition("Temporal Necessitation")[
  $
    (tack.r phi.alt) / (tack.r G phi.alt)
  $
  Applies only to theorems (empty context).
]

#definition("Temporal Duality")[
  $
    (tack.r phi.alt) / (tack.r chevron.l S chevron.r phi.alt)
  $
  Applies only to theorems (empty context).
]

#definition("Weakening")[
  $
    (Gamma tack.r phi.alt quad quad Gamma subset.eq Delta) / (Delta tack.r phi.alt)
  $
]

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Rule*], [*Lean Constructor*], [*Context Requirement*],
    ),
    table.hline(),
    [Axiom], [`DerivationTree.axiom`], [Any],
    [Assumption], [`DerivationTree.assumption`], [Any],
    [Modus Ponens], [`DerivationTree.modus_ponens`], [Any],
    [Necessitation], [`DerivationTree.necessitation`], [Empty only],
    [Temp. Necessitation], [`DerivationTree.temporal_necessitation`], [Empty only],
    [Temporal Duality], [`DerivationTree.temporal_duality`], [Empty only],
    [Weakening], [`DerivationTree.weakening`], [Any],
    table.hline(),
  ),
  caption: none,
)

== Derivation Trees

Derivations are represented as inductive trees.

#definition("Derivation Tree")[
  `DerivationTree Gamma phi` (written $Gamma tack.r phi.alt$) is an inductive type
  representing a derivation of $phi.alt$ from context $Gamma$.
]

#definition("Height")[
  The height of a derivation tree:
  - Base cases (axiom, assumption): height 0
  - Unary rules: height of subderivation + 1
  - Modus ponens: max of both subderivations + 1
]

The height measure enables well-founded recursion in metalogical proofs.

== Notation

#figure(
  table(
    columns: 2,
    stroke: none,
    table.hline(),
    table.header(
      [*Notation*], [*Lean*],
    ),
    table.hline(),
    [$Gamma tack.r phi.alt$], [`DerivationTree Gamma phi`],
    [$tack.r phi.alt$], [`DerivationTree [] phi`],
    table.hline(),
  ),
  caption: none,
)
