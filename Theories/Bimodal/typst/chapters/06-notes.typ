// ============================================================================
// 06-notes.typ
// Notes chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *

= Notes

== Implementation Status

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Component*], [*Status*], [*Notes*],
    ),
    table.hline(),
    [Syntax], [Complete], [6 primitives, derived operators],
    [Semantics], [Complete], [Task frames, world histories, truth],
    [Proof System], [Complete], [14 axioms, 7 inference rules],
    [Soundness], [Proven], [All 14 axioms valid, 7 rules sound],
    [Deduction Theorem], [Proven], [Well-founded recursion on height],
    [Completeness], [Proven (Semantic)], [Lindenbaum, truth lemma, weak completeness],
    [Decidability], [Soundness Proven], [Tableau-based, FMP for full completeness],
    [Perpetuity Principles], [Proven], [P1-P6 all proven],
    table.hline(),
  ),
  caption: none,
)

== Discrepancy Notes

This section documents differences between the paper "The Construction of Possible Worlds" and the Lean implementation.

=== Terminology

- The paper uses "perpetuity principles" for P1-P6; the Lean code uses the same terminology.
- The paper's notation $triangle.stroked.t$ and $triangle.stroked.b$ for "always" and "sometimes"
  is preserved in the Lean implementation as `always` and `sometimes`.

=== Axiom Naming

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Paper Name*], [*Lean Name*], [*Notes*],
    ),
    table.hline(),
    [MT (Modal T)], [`Axiom.modal_t`], [$square.stroked phi.alt arrow.r phi.alt$],
    [M4 (Modal 4)], [`Axiom.modal_4`], [$square.stroked phi.alt arrow.r square.stroked square.stroked phi.alt$],
    [MB (Modal B)], [`Axiom.modal_b`], [$phi.alt arrow.r square.stroked diamond.stroked phi.alt$],
    [MK], [`Axiom.modal_k_dist`], [K distribution],
    [TK], [`Axiom.temp_k_dist`], [Temporal K distribution],
    [T4], [`Axiom.temp_4`], [Temporal transitivity],
    [TA], [`Axiom.temp_a`], [Temporal connectedness],
    [TL], [`Axiom.temp_l`], [Temporal introspection],
    [MF], [`Axiom.modal_future`], [Modal-future interaction],
    [TF], [`Axiom.temp_future`], [Temporal-future interaction],
    table.hline(),
  ),
  caption: none,
)

=== M5 Collapse Axiom

The implementation includes an explicit M5 collapse axiom (`Axiom.modal_5_collapse`):
$ diamond.stroked square.stroked phi.alt arrow.r square.stroked phi.alt $
This is derivable from the other S5 axioms (MB + M4) but is included as a primitive
for proof convenience in the S5 collapse theorem.

=== Completeness Status

The paper proves completeness via canonical model construction.
The Lean implementation establishes completeness via the semantic canonical model approach.
The key results are:
- `set_lindenbaum`: Every consistent set extends to a maximal consistent set
- `semantic_truth_lemma_v2`: Membership corresponds to truth in the semantic model
- `semantic_weak_completeness`: Validity implies derivability
- `main_provable_iff_valid`: Derivability and validity coincide

The semantic approach defines world states as equivalence classes of history-time pairs, making the truth lemma straightforward by construction.
Bridge sorries remain for connecting general validity to frame validity in strong completeness.

=== Decidability Implementation

The implementation includes a tableau-based decision procedure for validity that provides an alternative to the canonical model approach.
The decidability module establishes that validity is decidable via constructive tableau expansion and branch closure.
Soundness is proven: if the procedure returns "valid", the formula is semantically valid.
Completeness requires the Finite Model Property (FMP), which is stated but not yet fully formalized.
The FMP states that if a formula is satisfiable, it is satisfiable in a finite model.
Full formalization of the FMP completes decidability.

== Design Choices <sec:design-choices>

The implementation of TM logic involves foundational choices that affect the proof theory and metatheoretic properties.
This section documents these choices and their rationale.

=== Strict vs Reflexive Temporal Semantics

The temporal operators $G$ (future) and $H$ (past) can be interpreted with either *strict* or *reflexive* quantification over times.
This choice has significant consequences for axiom validity, frame definability, and completeness proof structure.

#definition("Strict Temporal Semantics")[
  Under *strict semantics*, temporal quantification excludes the present moment:
  $
    cal(M), tau, x tack.r.double G phi.alt &<=> cal(M), tau, y tack.r.double phi.alt "for all" y : D "where" x < y \
    cal(M), tau, x tack.r.double H phi.alt &<=> cal(M), tau, y tack.r.double phi.alt "for all" y : D "where" y < x
  $
  Under strict semantics, the T-axioms $G phi.alt arrow.r phi.alt$ are *invalid*: the present moment is not included in "always future."
]

#definition("Reflexive Temporal Semantics (Current)")[
  Under *reflexive semantics*, temporal quantification includes the present moment:
  $
    cal(M), tau, x tack.r.double G phi.alt &<=> cal(M), tau, y tack.r.double phi.alt "for all" y : D "where" x lt.eq y \
    cal(M), tau, x tack.r.double H phi.alt &<=> cal(M), tau, y tack.r.double phi.alt "for all" y : D "where" y lt.eq x
  $
  The temporal T-axioms $G phi.alt arrow.r phi.alt$ and $H phi.alt arrow.r phi.alt$ are definitionally valid.
  This matches the truth conditions in @sec:truth.
]

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Property*], [*Reflexive ($lt.eq$) — Current*], [*Strict ($<$)*],
    ),
    table.hline(),
    [T-axiom: $G phi.alt arrow.r phi.alt$], [Definitionally valid], [Invalid],
    [Seriality: $G phi.alt arrow.r F phi.alt$], [Trivially valid (T-axiom)], [Requires NoMaxOrder],
    [Density: $G G phi.alt arrow.r G phi.alt$], [Trivially valid], [Requires DenselyOrdered],
    [Discreteness: DF axiom], [Trivially valid], [Requires SuccOrder],
    [Frame class separation], [Collapsed to single logic], [Three distinct logics],
    [Canonical model reflexivity], [Holds by T-axiom], [Requires Gabbay IRR rule],
    table.hline(),
  ),
  caption: [Comparison of reflexive and strict temporal semantics. TM uses reflexive semantics.],
)

=== Algebraic Classification

The choice between reflexive and strict semantics has a clean algebraic characterization: under reflexive semantics, the temporal operators $G$ and $H$ are *interior operators* on the Lindenbaum algebra.

#definition("Interior Operator")[
  An *interior operator* $I$ on a partial order satisfies:
  + *Deflationary*: $I(a) lt.eq a$ (corresponds to T-axiom: $G phi.alt arrow.r phi.alt$)
  + *Monotone*: $a lt.eq b arrow.r I(a) lt.eq I(b)$ (corresponds to K-distribution)
  + *Idempotent*: $I(I(a)) = I(a)$ (corresponds to 4-axiom + T-axiom)
]

#remark("Operators Under Reflexive Semantics")[
  Under reflexive semantics, all three modal-like operators are interior operators:
  - $square.stroked$ (box): Interior operator via `modal_t` ($square.stroked phi.alt arrow.r phi.alt$), `modal_k_dist`, and `modal_4`
  - $G$ (future): Interior operator via `temp_t_future` ($G phi.alt arrow.r phi.alt$), `temp_k_dist`, and `temp_4`
  - $H$ (past): Interior operator via `temp_t_past` ($H phi.alt arrow.r phi.alt$), `temp_k_dist`, and `temp_4`

  The dual operators ($diamond.stroked$, $F$, $P$) are correspondingly *closure operators* (inflationary, monotone, idempotent).
]

#remark("McKinsey-Tarski Connection")[
  The McKinsey-Tarski theorem (1944) establishes that *S4 is sound and complete for the class of all topological spaces*, where $square.stroked phi.alt$ is interpreted as the topological interior.
  Under reflexive semantics, TM's temporal fragment forms a *bimodal interior algebra* (tense algebra), giving it a richer algebraic structure than mere normal modal operators.
]

#remark("Jonsson-Tarski Representation")[
  The Jonsson-Tarski representation theorem (1952) provides the key correspondence:

  #align(center)[
    *Frame reflexivity* $arrow.l.r.double$ *Operator deflationarity*
  ]

  The choice of reflexive semantics is algebraically equivalent to choosing that $G$ and $H$ are interior operators.
  Under strict semantics, $G$ and $H$ retain only monotonicity --- they degrade to normal modal operators without the S4 structure.
]

=== Expressive Power and Frame Definability

Strict semantics is provably *more expressive* for distinguishing frame classes.
The fundamental obstacle is that *irreflexivity is not modally definable* (Blackburn, de Rijke, Venema): no temporal formula holds in exactly those frames where the accessibility relation is irreflexive.

#figure(
  table(
    columns: 4,
    stroke: none,
    table.hline(),
    table.header(
      [*Axiom*], [*Frame Property*], [*Strict Semantics*], [*Reflexive Semantics*],
    ),
    table.hline(),
    [DN: $G G phi.alt arrow.r G phi.alt$], [Density], [Valid iff DenselyOrdered], [Trivially valid ($r = t$ works)],
    [SF: $G phi.alt arrow.r F phi.alt$], [Seriality (future)], [Valid iff NoMaxOrder], [Trivially valid (T-axiom)],
    [SP: $H phi.alt arrow.r P phi.alt$], [Seriality (past)], [Valid iff NoMinOrder], [Trivially valid (T-axiom)],
    [DF: $(F top and phi.alt and H phi.alt) arrow.r F(H phi.alt)$], [Discreteness], [Valid iff SuccOrder], [Trivially valid ($s = t$ works)],
    table.hline(),
  ),
  caption: [Frame class axioms under each semantics. Under reflexive semantics, all four collapse to trivial validity.],
)

#remark("Frame Class Collapse")[
  Under reflexive semantics, the following distinctions become invisible to the logic:
  - *Dense vs. Discrete*: Both satisfy all four axioms
  - *Bounded vs. Unbounded*: Seriality holds even on bounded orders (T-axiom provides the witness)
  - *Base vs. Extensions*: A single completeness theorem suffices

  This is a *feature for proof engineering* (simpler proofs) but a *loss for frame taxonomy* (cannot axiomatically distinguish $bb(Q)$ from $bb(Z)$).
]

#remark("Inter-Definability")[
  The reflexive operator $G'$ is definable from strict $G$: $G' phi.alt equiv phi.alt and G phi.alt$.
  However, strict $G$ is *not* recoverable from reflexive $G'$ alone --- excluding the present requires hybrid logic or an additional irreflexivity axiom.
  This asymmetry explains why the strict-to-reflexive transition is "safe": every reflexive-valid formula is strict-valid (when T-axioms are not assumed).
]

#remark("S4.3.1 Alignment")[
  Under reflexive semantics, TM aligns with *S4.3.1*: reflexive + transitive + linear + antisymmetric frames.
  Completeness for S4.3.1 was established by Bull (1965) and Segerberg (1970).
  Under strict semantics, the relevant comparison is *K4.3* (transitive + linear, no T-axiom), which requires the Gabbay IRR rule for completeness.
]

=== Representation Theorem Challenges

The canonical model construction differs fundamentally between the two semantics, with significant implications for proof complexity.

#definition("Canonical Accessibility Relation")[
  The canonical accessibility relation for temporal operators is:
  $
    "CanonicalR" M N := g_"content"(M) subset.eq N
  $
  where $g_"content"(M) = {phi.alt | G(phi.alt) in M}$.
]

#remark("Canonical Model Under Strict Semantics")[
  Under strict semantics, $"CanonicalR" M M$ is *semantically false* (the present is excluded from $G$'s quantification) but *not derivable from axioms* (no modal formula characterizes irreflexivity).
  This creates a proof gap requiring:
  - The *Gabbay IRR rule*: If $tack (p and H(not p)) arrow.r A$ where $p in.not "atoms"(A)$, then $tack A$
  - A *fresh atom* $p$ not appearing in any formula of $g_"content"(M)$
  - Three separate completeness theorems for Base/Dense/Discrete frame classes
]

#remark("Canonical Model Under Reflexive Semantics")[
  Under reflexive semantics, $"CanonicalR" M M$ *holds by the T-axiom*:
  - If $G(phi.alt) in M$, then $phi.alt in M$ by MCS closure with $G phi.alt arrow.r phi.alt$
  - This gives $g_"content"(M) subset.eq M$, so $"CanonicalR" M M$
  - The canonical model is *definitionally reflexive*

  Instead of proving irreflexivity (impossible), we establish *antisymmetry*:
  $
    "CanonicalR" M N and "CanonicalR" N M arrow.r M = N
  $
]

#remark("Completeness Architecture Collapse")[
  Under strict semantics, three completeness theorems are needed:
  + *BaseCompleteness*: all linear orders (via CanonicalFMCS)
  + *DenseCompleteness*: densely ordered frames (via DovetailedBuild)
  + *DiscreteCompleteness*: discrete successor orders (via StagedExecution)

  Under reflexive semantics, these collapse to a *single theorem*: the density and discreteness axioms are trivially valid, so the base completeness proof covers all cases.
]

=== Historical Context

#remark("Prior's Tradition (1957--1968)")[
  Arthur Prior established tense logic using *strict semantics*:
  - F ("it will be the case") quantifies over strictly future times
  - P ("it was the case") quantifies over strictly past times
  - Frame correspondence theory: temporal axioms genuinely characterize frame properties (density, discreteness, seriality)

  This tradition continued through Goldblatt, van Benthem, and Blackburn-de Rijke-Venema.
  Strict semantics remains the foundation of the standard temporal logic literature.
]

#remark("Computer Science Shift")[
  Model checking and verification applications often use *reflexive semantics*:
  - CTL: "AG $phi.alt$" means "$phi.alt$ at all states including the current one"
  - LTL: Both strict ($X$) and weak ($X_w$) variants exist
  - Finite state systems: Reflexive simplifies boundary conditions

  The trade-off is loss of frame-theoretic expressiveness for proof-engineering simplicity.
]

#remark("TM Project History")[
  The TM implementation switched between semantics multiple times:
  #figure(
    table(
      columns: 3,
      stroke: none,
      table.hline(),
      table.header(
        [*Task*], [*Direction*], [*Motivation*],
      ),
      table.hline(),
      [Initial], [Reflexive ($lt.eq$)], [Project inception],
      [Task 658], [Confirmed reflexive], [Indexed family coherence: *mathematically impossible* under strict],
      [Task 991], [Strict ($<$)], [Frame class separation concern],
      [Task 29], [Reflexive ($lt.eq$)], [IRR proof broken under strict; theoretical analysis],
      table.hline(),
    ),
    caption: none,
  )

  The decisive finding (Task 658): independent Lindenbaum extensions cannot be proven coherent without the T-axiom. This is not a proof difficulty --- it is a *mathematical impossibility*.
]

=== Design Rationale for TM

#remark("Why Reflexive Semantics")[
  TM uses *reflexive semantics* for the following reasons:

  *Mathematical Necessity*:
  - The indexed family construction requires $G phi.alt arrow.r phi.alt$ for forward coherence
  - Without T-axioms, independent Lindenbaum extensions have no provable coherence
  - This is a mathematical impossibility, not a proof inconvenience

  *Algebraic Elegance*:
  - $G$, $H$, and $square.stroked$ are all interior operators on the Lindenbaum algebra
  - The logic forms a bimodal tense algebra with rich algebraic structure
  - Stone-type representation theorems apply cleanly

  *Proof Architecture*:
  - Single completeness theorem replaces three
  - No Gabbay IRR rule or fresh atom machinery needed
  - Canonical model is definitionally reflexive
]

#remark("Trade-offs Accepted")[
  The choice of reflexive semantics accepts:
  + *Frame class collapse*: Cannot axiomatically distinguish dense from discrete orders
  + *Departure from tradition*: Does not follow Prior's strict tense logic
  + *Seriality as theorem*: $G phi.alt arrow.r F phi.alt$ holds trivially, not as a frame constraint

  These are acceptable because:
  - TM reasons about a *fixed* linear time domain, not classifying frames
  - Frame distinctions remain semantic ($bb(Q)$ is still dense, $bb(Z)$ still discrete)
  - The S5 modal structure provides sufficient expressiveness for bimodal reasoning
]
