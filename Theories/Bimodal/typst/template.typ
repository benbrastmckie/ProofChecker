// ============================================================================
// template.typ
// Shared template with theorem environments for all chapters
//
// Styling follows the AMS/journal aesthetic: austere, black-only body text,
// no background colors on theorem environments. Link colors (URLblue) are
// preserved for digital usability.
//
// Uses ctheorems package with thmplain for AMS-style plain environments.
// ============================================================================

#import "@preview/ctheorems:1.1.3": thmplain, thmproof, thmrules
#import "notation/bimodal-notation.typ": *

// ============================================================================
// Color Definitions
// ============================================================================

// URLblue color for hyperlinks (matches LogosReference.tex)
#let URLblue = rgb(30, 144, 255)  // Light blue (Dodger Blue)

// ============================================================================
// AMS-Style Theorem Environments (using ctheorems thmplain)
// ============================================================================

// AMS convention:
// - Theorems/lemmas: bold label, italic body (plain style)
// - Definitions: bold label, upright body (definition style)
// - Axioms: bold label, italic body (follows theorem style)
// - Remarks: italic label, upright body, unnumbered (remark style)

// AMS "plain" style: bold label, italic body
#let theorem = thmplain(
  "theorem",
  "Theorem",
  titlefmt: strong,
  bodyfmt: body => emph(body),
)

#let lemma = thmplain(
  "lemma",
  "Lemma",
  base: "theorem",
  titlefmt: strong,
  bodyfmt: body => emph(body),
)

// AMS "definition" style: bold label, upright body
#let definition = thmplain(
  "definition",
  "Definition",
  titlefmt: strong,
)

// Axiom follows theorem style (bold label, italic body)
#let axiom = thmplain(
  "axiom",
  "Axiom",
  titlefmt: strong,
  bodyfmt: body => emph(body),
)

// AMS "remark" style: italic label, upright body, unnumbered
#let remark = thmplain(
  "remark",
  "Remark",
  titlefmt: emph,
  numbering: none,
)

// Proof environment with QED symbol
#let proof = thmproof("proof", "Proof")

// ============================================================================
// Show Rule Export for Chapters
// ============================================================================

// Export thmrules for chapters to apply
// Chapters should use: #show: thmrules.with(qed-symbol: $square$)
