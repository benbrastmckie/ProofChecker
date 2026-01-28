// ============================================================================
// template.typ
// Shared template with theorem environments for all chapters
// ============================================================================

#import "@preview/thmbox:0.3.0" as thmbox
#import "notation/bimodal-notation.typ": *

// ============================================================================
// Color Definitions
// ============================================================================

// URLblue color for hyperlinks (matches LogosReference.tex)
#let URLblue = rgb(0, 0, 150)

// ============================================================================
// thmbox initialization function
// ============================================================================

// thmbox-init sets up the theorem environment system
#let thmbox-show = thmbox.thmbox-init()

// ============================================================================
// Custom Theorem Environment Styling
// ============================================================================

// Professional styling for math environments - subtle background tints
#let theorem-style = (
  fill: rgb("#f8f8ff"),  // Very light blue-gray
)

#let definition-style = (
  fill: rgb("#f0fff0"),  // Very light green (mint)
)

#let axiom-style = (
  fill: rgb("#fff8f0"),  // Very light orange
)

#let remark-style = (
  fill: rgb("#f8f8f8"),  // Light gray
)

// ============================================================================
// Theorem Environments (using thmbox predefined environments with custom styling)
// ============================================================================

// Re-export thmbox environments with custom styling
// Chapters use: definition, theorem, lemma, axiom, remark, proof
#let definition = thmbox.definition.with(..definition-style)
#let theorem = thmbox.theorem.with(..theorem-style)
#let lemma = thmbox.lemma.with(..theorem-style)
#let axiom = thmbox.axiom.with(..axiom-style)
#let remark = thmbox.remark.with(..remark-style)
#let proof = thmbox.proof
