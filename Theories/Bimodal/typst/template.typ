// ============================================================================
// template.typ
// Shared template with theorem environments for all chapters
// ============================================================================

#import "@preview/great-theorems:0.1.2": *
#import "notation/bimodal-notation.typ": *

// ============================================================================
// Theorem Environments
// ============================================================================

#let great-theorems-show = great-theorems-init

#let definition = mathblock(
  blocktitle: "Definition",
  counter: counter("definition"),
  numbering: num => numbering("1.1", counter(heading).get().first(), num),
)

#let theorem = mathblock(
  blocktitle: "Theorem",
  counter: counter("theorem"),
  numbering: num => numbering("1.1", counter(heading).get().first(), num),
)

#let lemma = mathblock(
  blocktitle: "Lemma",
  counter: counter("lemma"),
  numbering: num => numbering("1.1", counter(heading).get().first(), num),
)

#let axiom = mathblock(
  blocktitle: "Axiom",
  counter: counter("axiom"),
  numbering: num => numbering("1.1", counter(heading).get().first(), num),
)

#let remark = mathblock(
  blocktitle: "Remark",
  counter: counter("remark"),
  numbering: num => numbering("1.1", counter(heading).get().first(), num),
)

#let proof = proofblock()
