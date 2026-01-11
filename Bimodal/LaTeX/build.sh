#!/bin/bash
# Build script for Bimodal TM Logic Reference Manual
#
# Usage: ./build.sh [--clean]
#   --clean: Remove all build artifacts before building

set -e

# Change to the LaTeX directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

# Handle clean flag
if [[ "$1" == "--clean" ]]; then
    echo "Cleaning build artifacts..."
    rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk *.synctex.gz
    rm -f subfiles/*.aux
    rm -rf build/
    echo "Clean complete."
fi

# Create build directory if it doesn't exist
mkdir -p build

# Build the main document
echo "Building BimodalReference.tex..."
pdflatex -interaction=nonstopmode -output-directory=build BimodalReference.tex

# Run twice for table of contents
echo "Second pass for TOC..."
pdflatex -interaction=nonstopmode -output-directory=build BimodalReference.tex

echo ""
echo "Build complete: build/BimodalReference.pdf"
