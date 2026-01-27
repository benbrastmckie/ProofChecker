// ============================================================================
// 00-introduction.typ
// Introduction chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *
#import "@preview/cetz:0.3.4"

= Introduction

The bimodal logic *TM* combines S5 historical modal operators for necessity ($square.stroked$) and possibility ($diamond.stroked$) with linear temporal operators for past ($H$) and future ($G$).
Implementing *TM* in Lean 4 provides a positive RL signal for training AI systems to conduct verified reasoning about past and future contingency in an interpreted formal language.

The semantics is based on _task frames_, which extend Kripke frames with temporal structure.
A task frame consists of world states connected by a _task relation_ indexed by temporal durations.
World histories are temporal slices through a task frame, representing the possible evolution of a system.

#align(center)[
  #cetz.canvas({
    import cetz.draw: *

    // Define the marked point P at the bottom of the S-curve
    let P = (0.5, -0.2)

    // Past light cone (blue, opens left)
    line(P, (-0.7, 1.0), stroke: gray.lighten(40%))
    line(P, (-0.7, -1.2), stroke: gray.lighten(40%))
    line((-0.7, 1.0), (-0.7, -1.2), stroke: none, fill: blue.transparentize(85%))

    // Future light cone (orange, opens right)
    line(P, (1.7, 1.0), stroke: gray.lighten(40%))
    line(P, (1.7, -1.2), stroke: gray.lighten(40%))
    line((1.7, 1.0), (1.7, -1.2), stroke: none, fill: orange.transparentize(85%))

    // Fill the past cone
    line(P, (-0.7, 1.0), (-0.7, -1.2), close: true, stroke: none, fill: blue.transparentize(85%))

    // Fill the future cone
    line(P, (1.7, 1.0), (1.7, -1.2), close: true, stroke: none, fill: orange.transparentize(85%))

    // Counterfactual paths (dotted gray)
    // Past paths
    line(P, (-0.5, 0.6), stroke: (paint: gray.lighten(50%), thickness: 1pt, dash: "dotted"))
    line(P, (-0.4, -0.8), stroke: (paint: gray.lighten(50%), thickness: 1pt, dash: "dotted"))

    // Future paths
    line(P, (1.4, 0.5), stroke: (paint: gray.lighten(50%), thickness: 1pt, dash: "dotted"))
    line(P, (1.3, -0.8), stroke: (paint: gray.lighten(50%), thickness: 1pt, dash: "dotted"))

    // Draw the S-shaped main worldline (actual history)
    bezier(
      (-3.5, -1.5),
      (-1.5, -0.6),
      P,
      (1.0, 0.0),
      stroke: (paint: blue.darken(40%), thickness: 2pt),
    )
    bezier(
      P,
      (1.0, 0.0),
      (2.0, 0.4),
      (3.5, 1.5),
      stroke: (paint: blue.darken(40%), thickness: 2pt),
      mark: (end: ">", fill: blue.darken(40%)),
    )

    // Label tau above the worldline
    content((-2.8, -0.4), text(fill: blue.darken(40%), size: 10pt)[$tau$])

    // Draw the marked point P
    circle(P, radius: 0.08, fill: blue.darken(40%), stroke: none)
    content((P.at(0), P.at(1) - 0.25), text(size: 10pt)[$x$])
  })
]

The diagram above illustrates the conceptual structure underlying TM logic.
The solid curve $tau$ represents a single world history---a temporal sequence of states.
From any point $x$ along a history, the past and future light cones contain all states that are modally accessible.
The necessity operator $square.stroked$ quantifies over all possible histories, though we may often restrict to those histories that pass through the world state $tau(x)$.
The temporal operators $H$ and $G$ quantify over past and future times which, given a particular history, determines the range of past and future world states that history occupies relative to a given time.
These primitive operators may then be used to define a host of combined operators of interest.

== Project Structure

The Lean 4 implementation is in the `Bimodal/` directory:
- `Syntax/` -- Defines the formula language with 6 primitive constructors and derived operators.
  *Complete.*
- `ProofSystem/` -- Axioms (14 schemata) and inference rules (7 rules) forming a Hilbert-style proof system.
  *Complete.*
- `Semantics/` -- Task frames model possible worlds; world histories model time; truth conditions define meaning.
  *Complete.*
- `Metalogic/` -- Soundness theorem (proven: all axioms valid, rules preserve validity), deduction theorem (proven: enables assumption introduction), completeness via the semantic canonical model (Lindenbaum lemma proven, truth lemma proven, weak completeness proven), and decidability via tableau-based decision procedure (soundness and completeness proven).
  *Complete.*
- `Theorems/` -- Perpetuity principles and modal theorems derived from the axiom system.
  *Partial.*
