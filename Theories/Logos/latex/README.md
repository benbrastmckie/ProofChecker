# Logos Reference Manual - LaTeX Build System

This directory contains the LaTeX source for the Logos Reference Manual, a comprehensive specification of the Logos logic system.

## Quick Start

### Regular Compilation
```bash
cd Theories/Logos/latex
latexmk -pdf LogosReference.tex
```

### Fix Common Issues (Recommended if errors occur)
```bash
cd Theories/Logos/latex
./latex-fix.sh rebuild
```

### Check Document Health
```bash
cd Theories/Logos/latex
./latex-fix.sh check
```

## Document Structure

- **`LogosReference.tex`** - Main document file
- **`subfiles/`** - Individual chapter files
- **`assets/logos-notation.sty`** - Custom LaTeX package for Logos notation
- **`bibliography/LogosReferences.bib`** - Bibliography database
- **`latex-fix.sh`** - Automated troubleshooting script
- **`latexmkrc`** - Build configuration (loads shared config)

## Build System Features

- **XeLaTeX** for Unicode and modern font support
- **Biber** for modern bibliography processing
- **Isolated build directory** (`build/`) keeps source clean
- **Automatic package discovery** for custom style files
- **Continuous compilation** support with `latexmk -pvc`

## Common Issues & Solutions

### "Runaway argument" or "File ended while scanning" errors
These occur when auxiliary files get corrupted during interrupted compilation.

**Solution**: Use the automated fix script:
```bash
./latex-fix.sh rebuild
```

### "Package not found" errors
The build system automatically handles package discovery. Ensure custom `.sty` files are in the `assets/` directory.

### Undefined references
Run a complete compilation cycle:
```bash
latexmk -f -pdf LogosReference.tex
```

## Development Workflow

1. **Make changes** to `.tex` files
2. **Compile automatically**:
   ```bash
   latexmk -pvc -pdf LogosReference.tex
   ```
3. **Check for issues** periodically:
   ```bash
   ./latex-fix.sh check
   ```
4. **Clean rebuild** when switching between major changes:
   ```bash
   ./latex-fix.sh rebuild
   ```

## Output Files

The compiled PDF and all auxiliary files are generated in the `build/` directory:
- `build/LogosReference.pdf` - Main output document
- `build/LogosReference.aux` - Auxiliary file with cross-references
- `build/LogosReference.log` - Compilation log (check for errors)
- `build/LogosReference.toc` - Table of contents

## Dependencies

- XeLaTeX (TeX Live 2025+)
- latexmk
- biber
- Required LaTeX packages (automatically installed by TeX Live)

## Troubleshooting

For detailed troubleshooting steps and common error solutions, see `LATEX_TROUBLESHOOTING.md`.

## Integration with Lean 4

Each definition in this reference manual has a corresponding Lean 4 implementation, referenced using the `\leansrc{}{}` command. The implementation can be found in:
```
Theories/Logos/    # Lean 4 source files
```