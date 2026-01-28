# Bimodal Reference Manual (Typst)

This directory contains the Typst port of the Bimodal TM Logic Reference Manual.

## Building

### Development (with live preview)

```bash
cd Theories/Bimodal/typst
typst watch BimodalReference.typ build/BimodalReference.pdf
```

### Production build

```bash
cd Theories/Bimodal/typst
typst compile BimodalReference.typ build/BimodalReference.pdf
```

## Directory Structure

```
typst/
├── BimodalReference.typ      # Main document
├── template.typ              # Shared theorem environments
├── notation/
│   ├── shared-notation.typ   # Shared notation (mirrors notation-standards.sty)
│   └── bimodal-notation.typ  # Bimodal-specific notation
├── chapters/
│   ├── 00-introduction.typ   # Introduction with light cone diagram
│   ├── 01-syntax.typ         # Formula syntax
│   ├── 02-semantics.typ      # Task frames and truth conditions
│   ├── 03-proof-theory.typ   # Axioms and inference rules
│   ├── 04-metalogic.typ      # Completeness and decidability
│   ├── 05-theorems.typ       # Perpetuity principles
│   └── 06-notes.typ          # Implementation status
└── build/                    # Output directory (PDF)
```

## Package Dependencies

- `@preview/great-theorems:0.1.2` - Theorem environments
- `@preview/cetz:0.3.4` - Diagrams (light cones, dependency graphs)

Packages are downloaded automatically on first compile.

## Relationship to LaTeX Version

This is a parallel port of `Theories/Bimodal/latex/`. The LaTeX source remains
unchanged and can be used as a reference. Both versions should produce visually
similar output with identical mathematical content.

## Font Requirements

The document uses "New Computer Modern" font. If not available, Typst will fall
back to similar fonts.
