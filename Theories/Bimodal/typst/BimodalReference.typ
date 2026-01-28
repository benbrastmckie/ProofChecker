// ============================================================================
// BimodalReference.typ
// Bimodal TM Logic: A Reference Manual
//
// This document provides the formal specification of the Bimodal TM logic,
// a bimodal logic combining S5 metaphysical modality with linear temporal
// operators, as implemented in the Bimodal/ directory.
// ============================================================================

// ============================================================================
// Package Imports
// ============================================================================

#import "@preview/cetz:0.3.4"

// Local notation and template (includes thmbox theorem environments)
#import "notation/bimodal-notation.typ": *
#import "template.typ": thmbox-show, URLblue, definition, theorem, lemma, axiom, remark, proof

// ============================================================================
// Document Configuration
// ============================================================================

#set document(
  title: "Bimodal Reference Manual",
  author: "Benjamin Brast-McKie",
)

// Typography settings - LaTeX-like appearance
#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set par(
  justify: true,
  leading: 0.55em,        // Tight line spacing like LaTeX
  spacing: 0.55em,        // Paragraph spacing
  first-line-indent: 1.8em,  // First-line indent like LaTeX
)

// Page layout with LaTeX-like margins
#set page(
  numbering: "1",
  number-align: center,
  margin: 1.75in,  // Match LaTeX 11pt article class defaults
)

// Heading spacing
#show heading: set block(above: 1.4em, below: 1em)

// Automatically bold "TM" throughout the document
#show "TM": strong

// ============================================================================
// Theorem Environment Initialization
// ============================================================================

#show: thmbox-show

// Style hyperlinks in URLblue color
#show link: set text(fill: URLblue)

// Allow theorem boxes to break across pages
#show figure.where(kind: "thmbox"): set block(breakable: true)

// ============================================================================
// Custom Commands
// ============================================================================

// Horizontal rule
#let HRule = line(length: 100%, stroke: 0.5pt)

// ============================================================================
// Title Page
// ============================================================================

#page(numbering: none)[
  #v(2cm)
  #align(center)[
    #HRule
    #v(0.4cm)
    #text(size: 24pt, weight: "bold")[Bimodal Reference Manual]
    #v(0.2cm)
    #HRule
    #v(.5cm)

    #text(size: 18pt, style: "italic")[A Logic for Tense and Modality]
    #v(1cm)

    #text(size: 12pt, style: "italic")[Benjamin Brast-McKie]
    #v(0.0cm)
    #link("https://www.benbrastmckie.com")[#raw("www.benbrastmckie.com")]
    #v(0.0cm)
    --- #datetime.today().display("[month repr:long] [day], [year]") ---
    #v(1cm)

    #v(1fr)

    #text(size: 11pt, weight: "bold")[Primary Reference:]
    #v(0.3cm)
    #link("https://www.benbrastmckie.com/wp-content/uploads/2025/11/possible_worlds.pdf")[_"The Construction of Possible Worlds"_], Brast-McKie, (under review), 2025.
    #v(1cm)
  ]
]

// ============================================================================
// Abstract
// ============================================================================

#page(numbering: none)[
  #v(1em)
  #align(center)[
    #text(size: 14pt, weight: "bold")[Abstract]
  ]
  #v(1em)

  This reference manual provides the formal specification of the Bimodal logic *TM* for tense and modality as implemented in the #proofchecker project.
  *TM* is a bimodal logic combining an S5 historical necessity operator with linear temporal operators for the past and future tenses.
  Soundness and the deduction theorem are established.
  Completeness is proven via the semantic canonical model approach: the Lindenbaum lemma, truth lemma, and weak completeness theorem are all proven.
  The key result `semantic_weak_completeness` demonstrates that validity implies derivability.

  #v(1cm)

  // Styled Contents header
  #align(center)[
    #text(size: 14pt, weight: "bold")[Contents]
  ]
  #v(1em)

  // Bold chapter entries (level 1), normal weight for sections/subsections
  #show outline.entry.where(level: 1): it => {
    v(0.5em)
    strong(it)
  }
  #outline(title: none, indent: auto)
]

#pagebreak()

// ============================================================================
// Content
// ============================================================================

#include "chapters/00-introduction.typ"
#include "chapters/01-syntax.typ"
#include "chapters/02-semantics.typ"
#include "chapters/03-proof-theory.typ"
#include "chapters/04-metalogic.typ"
#include "chapters/05-theorems.typ"
#include "chapters/06-notes.typ"
