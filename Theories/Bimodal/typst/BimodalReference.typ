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

// FIX: make the margins match those in /home/benjamin/Projects/ProofChecker/Theories/Logos/latex/LogosReference.tex

// FIX: the hyperlinks and clickable reference links should be in light blue

#import "@preview/great-theorems:0.1.2": *
#import "@preview/cetz:0.3.4"

// Local notation and template
#import "notation/bimodal-notation.typ": *
#import "template.typ": definition, theorem, lemma, axiom, remark, proof

// ============================================================================
// Document Configuration
// ============================================================================

#set document(
  title: "Bimodal Reference Manual",
  author: "Benjamin Brast-McKie",
)

#set text(font: "New Computer Modern", size: 11pt)
#set heading(numbering: "1.1")
#set par(justify: true)
#set page(numbering: "1", number-align: center)

// ============================================================================
// Theorem Environment Initialization
// ============================================================================

#show: great-theorems-init

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
    #v(1cm)

    #text(size: 18pt, style: "italic")[A Logic for Tense and Modality]
    #v(1cm)

    #text(size: 12pt, style: "italic")[Benjamin Brast-McKie]
    #v(0.15cm)
    #link("https://www.benbrastmckie.com")[www.benbrastmckie.com]
    #v(0.15cm)
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
  #heading(outlined: false, numbering: none)[Abstract]

  This reference manual provides the formal specification of the Bimodal logic *TM* for tense and modality as implemented in the #proofchecker project.
  *TM* is a bimodal logic combining an S5 historical necessity operator with linear temporal operators for the past and future tenses.
  Soundness and the deduction theorem are established.
  Completeness is proven via the semantic canonical model approach: the Lindenbaum lemma, truth lemma, and weak completeness theorem are all proven.
  The key result `semantic_weak_completeness` demonstrates that validity implies derivability.

  #v(1cm)
  #outline(title: "Contents", indent: auto)
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
