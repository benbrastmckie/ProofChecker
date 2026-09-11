"""Shared Boneyard-excluding traversal for the module-invariant harness.

Every filesystem traversal in `scripts/check-module-invariants.sh` filters the
archive by the ``Boneyard`` *directory name*, never by a path prefix: B0 asserts
that exactly one such directory exists anywhere under ``FormalSystem/``, so a
second archive reappearing fails the gate instead of silently splitting the
counts.  This module is the single implementation of that walk.  It is imported
by the C4/C5/C6/C7/C8/C11 graph checks and by the ``--emit-inventory``
generator, so the inventory tables and the C7 rollup can never disagree about
what "live" means.
"""

import os

BONEYARD_DIR_NAME = "Boneyard"


def live_files(base, ext):
    """Every file under `base` ending in `ext`, with the archive excluded."""
    out = []
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != BONEYARD_DIR_NAME]
        for f in files:
            if f.endswith(ext):
                out.append(os.path.join(root, f))
    return sorted(out)


def live_loose_files(base, ext):
    """Files directly in `base` (no recursion) ending in `ext`.

    The archive is excluded here too: a `Boneyard/` entry is a directory, so it
    can only be reached through `live_subdirs`, which drops it by name.
    """
    if not os.path.isdir(base):
        return []
    out = [
        os.path.join(base, f)
        for f in os.listdir(base)
        if f.endswith(ext) and os.path.isfile(os.path.join(base, f))
    ]
    return sorted(out)


def live_subdirs(base):
    """Immediate subdirectories of `base`, with the archive excluded."""
    if not os.path.isdir(base):
        return []
    out = [
        os.path.join(base, d)
        for d in os.listdir(base)
        if d != BONEYARD_DIR_NAME and os.path.isdir(os.path.join(base, d))
    ]
    return sorted(out)


def line_count(path):
    """Line count of `path`, counted the way `wc -l` counts it."""
    with open(path, "rb") as fh:
        return fh.read().count(b"\n")


def classify_lines(path):
    """Return (code_lines, comment_lines) for a Lean source file.

    A line counts as a comment line iff every non-blank character on it falls
    inside a `--` line comment or a (possibly nested) `/- ... -/` block
    comment; a line carrying any code at all -- including code followed by a
    trailing `--` note -- counts as code. Blank lines are counted as neither,
    matching cloc's three-way blank/comment/code split closely enough for an
    approximate inventory metric.
    """
    code = comment = 0
    depth = 0
    with open(path, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.rstrip("\n")
            if not line.strip() and depth == 0:
                continue
            has_code = has_comment = False
            i, n = 0, len(line)
            while i < n:
                if depth > 0:
                    if line[i:i + 2] == "-/":
                        depth -= 1
                        i += 2
                    elif line[i:i + 2] == "/-":
                        depth += 1
                        i += 2
                    else:
                        i += 1
                    has_comment = True
                    continue
                if line[i:i + 2] == "--":
                    if line[i:].strip():
                        has_comment = True
                    break
                if line[i:i + 2] == "/-":
                    depth += 1
                    i += 2
                    has_comment = True
                    continue
                if not line[i].isspace():
                    has_code = True
                i += 1
            if has_code:
                code += 1
            elif has_comment:
                comment += 1
    return code, comment
