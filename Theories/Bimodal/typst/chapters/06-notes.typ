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
