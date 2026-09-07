#!/usr/bin/env bash
# check-module-invariants.sh
#
# Phase-gate harness for the Lean source tree. Turns "the reorganization did not
# break anything" into a single command with a non-zero exit on any failure.
#
# Checks:
#   B0  Boneyard exclusion self-test (the single archive must be found and excluded)
#   C1  `lake build` exits 0
#   C2  `#print axioms` for the four flagship theorems matches the recorded baseline
#   C3  ZERO structural `sorry`, asserted BY CONTENT (never by line number)
#   C4  Every `import FormalSystem.*` / `import BimodalTest.*` resolves to a real file
#   C5  Every module-shaped `FormalSystem.*` path in non-specs markdown resolves
#   C6  Known-unreachable live modules still compile (rot guard)
#   C7  Live inventory (informational, never asserted)
#   C8  Aggregator convention: sibling `X.lean` beside `X/`, no `X/X.lean`
#   C9  Zero task-number citations under FormalSystem/, lakefile.lean, README.md,
#       and scripts/
#   C10 Zero references to the pre-relocation docs/latex/typst paths
#   C11 Every import inside FormalSystem/Boneyard/ resolves, or is waived
#   C12 Every slash-shaped source path in docs/ + README.md resolves
#   C13 Every relative markdown link in docs/ + README.md resolves
#   C14 Documented axiom/sorry counts match the tree -- in docs/, README.md AND
#       FormalSystem/**/*.lean docstrings; and the axiom set of every declaration
#       C2 does not cover matches its baseline, including every subject of a
#       SORRY-FREE claim in FormalSystem/Metalogic.lean
#   C15 Every paper-anchor citation in live scope resolves against the pinned
#       record (manifest row, or an explicit KNOWN-ANCHORS row)
#   C16 Batteries env_linter batch (simpNF, docBlame, unusedArguments, ...) has no
#       finding beyond scripts/nolints.json's grandfathered baseline; dupNamespace
#       reported via a live textual (namespace-nesting) approximation, never gated
#   C17 Dead-declaration scan: base identifiers with zero occurrences outside their
#       own declaring line, across FormalSystem/ + Tests/ + repo-wide markdown
#       (REPORTED, not gated)
#   C18 Duplicated paragraphs across README.md, FormalSystem/README.md,
#       FormalSystem/Metalogic/README.md and FormalSystem/Metalogic.lean
#       (REPORTED, not gated)
#   C19 Docstring-coverage floor (90%), G-12 heuristic refined with a /-!
#       section-comment credit (REPORTED, not gated; 90% floor, never fails)
#   C9D Task-number citations under docs/ (computed always, soft by default)
#   INV Every `<!-- BEGIN GENERATED: inventory -->` block in the tree is current
#
# Every filesystem traversal excludes the archive via `-not -path '*/Boneyard/*'`.
# The archive was consolidated into a single tree at `FormalSystem/Boneyard/`; the
# former second archive at `Metalogic/WeakCanonical/Kamp/Boneyard/` (63 files /
# 29,256 lines) now lives at `Boneyard/Kamp/KampWeakCanonical/`. B0 asserts the
# directory count is exactly 1, so a second archive reappearing anywhere under
# `FormalSystem/` fails the gate instead of silently splitting the counts again --
# which is what happened before, and is why the name glob (not a path prefix) is
# what the traversals filter on.
#
# Usage:
#   bash scripts/check-module-invariants.sh            # all checks
#   bash scripts/check-module-invariants.sh --no-build # skip C1/C2/C6/C16 (fast structural pass)
#   bash scripts/check-module-invariants.sh --emit-inventory          # rewrite generated inventory blocks
#   bash scripts/check-module-invariants.sh --emit-inventory --check  # fail if a rewrite would change a byte
#
# Companion files:
#   scripts/module-invariants-manifest.txt   known-unreachable live modules (C6)
#   scripts/module-invariants-allowlist.txt  pre-existing unresolved md paths (C5)
#   scripts/boneyard-import-waivers.txt    unrepairable archived imports (C11)
#   scripts/markdown-slash-path-allowlist.txt  hypothetical slash paths (C12)
#   scripts/markdown-link-allowlist.txt        link-syntax-illustration files (C13)
#   specs/paper-definitions-of-record.md       pinned paper anchors + known-anchor rows (C15)
#   scripts/nolints.json                       grandfathered env_linter findings (C16)

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 1

MANIFEST="scripts/module-invariants-manifest.txt"
ALLOWLIST="scripts/module-invariants-allowlist.txt"
WAIVERS="scripts/boneyard-import-waivers.txt"
SLASH_ALLOWLIST="scripts/markdown-slash-path-allowlist.txt"
LINK_ALLOWLIST="scripts/markdown-link-allowlist.txt"

# scripts/lib/ is on sys.path for the python passes below; keep the tree clean.
export PYTHONDONTWRITEBYTECODE=1

RUN_BUILD=1
[ "${1:-}" = "--no-build" ] && RUN_BUILD=0

# ---------------------------------------------------------------------------
# --emit-inventory: the generated-count owner
#
# Hand-maintained module inventory tables drift the moment a file is added,
# split or renamed, and nothing in the tree noticed: 40 of 72 per-file line
# counts were wrong when this mode was written, and one README listed five files
# that had moved to another directory. Counts are therefore machine-owned. A
# markdown file opts in by wrapping its table in
#
#     <!-- BEGIN GENERATED: inventory dir=FormalSystem/Automation -->
#     ... table ...
#     <!-- END GENERATED -->
#
# and this mode rewrites every column except the hand-written trailing one.
#
# Marker options (all optional except dir=):
#   dir=<path>              directory the inventory covers, repo-relative
#   rows=loose|subdirs|both|totals
#                           which rows to emit (default both); `totals` emits the
#                           live/archived file and line rollup for dir= instead
#                           of a per-file listing
#   filter=all|aggregators|non-aggregators
#                           restrict the loose rows; an aggregator is a loose
#                           `X.lean` with a sibling directory `X/` (default all)
#   cols=lines|files-lines  one numeric column (lines) or two (file count then
#                           line count, for directory-shaped tables)
#   desc=yes|no             emit the trailing hand-written column (default yes)
#   link=yes|no             render a subdirectory row as a link to its README
#                           when one exists (default no)
#   sort=name|lines-desc    row order (default name)
#
# The trailing column is HAND-WRITTEN and survives regeneration: rows are keyed
# on the file or directory name, so an existing description is carried across
# verbatim. A newly-appeared file gets `<!-- TODO: add description -->`; a row
# whose file no longer exists is dropped. A row naming a file outside the
# scanned directory (`../FormalSystem.lean`) is kept as a pinned row with its
# numbers refreshed, as long as the path still resolves.
#
# A table that is deliberately NOT generated -- one ordered by the layering rather
# than alphabetically, or carrying no counts at all -- registers itself instead with
#
#     <!-- INVENTORY: hand-maintained (dir=FormalSystem/Semantics) -->
#
# placed immediately above it. Registration buys exemption from generation, never
# from being checked: this mode still asserts that such a table has a row for every
# live file and subdirectory and no row for anything else.
#
# Two modes:
#   --emit-inventory           rewrite every registered block in place
#   --emit-inventory --check   exit non-zero if a rewrite would change a byte
#
# Only --check belongs in CI. The writer is a developer command.
if [ "${1:-}" = "--emit-inventory" ]; then
  EMIT_CHECK=0
  if [ "${2:-}" = "--check" ]; then EMIT_CHECK=1; fi
  export EMIT_CHECK
  python3 - <<'PYEOF'
import os, re, sys

sys.path.insert(0, os.path.join("scripts", "lib"))
from live_walk import live_loose_files, live_subdirs, live_files, line_count

CHECK = os.environ.get("EMIT_CHECK") == "1"

BEGIN_RE = re.compile(r'^<!--\s*BEGIN GENERATED:\s*inventory\s*(?P<opts>[^>]*?)\s*-->\s*$')
END_RE = re.compile(r'^<!--\s*END GENERATED\s*-->\s*$')
HAND_RE = re.compile(r'^<!--\s*INVENTORY:\s*hand-maintained\s*\(dir=(?P<dir>[^)\s]+)\)')
SEP_CELL_RE = re.compile(r'^:?-{2,}:?$')
LINK_RE = re.compile(r'^\[(?P<label>.*)\]\((?P<href>[^)]*)\)$')
TODO_DESC = "<!-- TODO: add description -->"


def markdown_targets():
    out = []
    for root, dirs, files in os.walk("."):
        dirs[:] = [d for d in dirs
                   if d not in (".git", "specs", ".claude", ".lake", "node_modules", "Boneyard")]
        for f in files:
            if f.endswith(".md"):
                out.append(os.path.normpath(os.path.join(root, f)))
    return sorted(out)


def parse_opts(raw):
    opts = {}
    for tok in raw.split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            opts[k] = v
    return opts


def split_row(line):
    body = line.strip()
    if not body.startswith("|"):
        return None
    body = body[1:]
    if body.endswith("|"):
        body = body[:-1]
    return [c.strip() for c in body.split("|")]


def row_key(cell):
    cell = cell.strip()
    m = LINK_RE.match(cell)
    if m:
        cell = m.group("label").strip()
    return cell.strip("`").strip()


def is_separator(cells):
    return bool(cells) and all(SEP_CELL_RE.match(c.replace(" ", "")) for c in cells if c != "")


def scan(directory, opts):
    """Return [(key, [numeric cells...], link_target_or_None)] for `directory`."""
    rows = opts.get("rows", "both")
    filt = opts.get("filter", "all")
    cols = opts.get("cols", "lines")
    want_link = opts.get("link", "no") == "yes"

    subdir_names = {os.path.basename(p) for p in live_subdirs(directory)}
    out = []
    if rows == "totals":
        live = live_files(directory, ".lean")
        archived = [f for f in
                    (os.path.join(r, n)
                     for r, _d, ns in os.walk(directory) for n in ns)
                    if f.endswith(".lean") and (os.sep + "Boneyard" + os.sep) in f]
        out.append(("Live `.lean` files", ["{:,}".format(len(live))], "literal"))
        out.append(("Live lines", ["{:,}".format(sum(line_count(f) for f in live))], "literal"))
        if archived:
            out.append(("Archived `.lean` files", ["{:,}".format(len(archived))], "literal"))
            out.append(("Archived lines",
                        ["{:,}".format(sum(line_count(f) for f in archived))], "literal"))
        return out
    if rows in ("loose", "both"):
        for path in live_loose_files(directory, ".lean"):
            name = os.path.basename(path)
            stem = name[:-len(".lean")]
            is_agg = stem in subdir_names
            if filt == "aggregators" and not is_agg:
                continue
            if filt == "non-aggregators" and is_agg:
                continue
            nums = ["{:,}".format(line_count(path))]
            if cols == "files-lines":
                nums = ["1"] + nums
            out.append((name, nums, None))
    if rows in ("subdirs", "both"):
        for sub in live_subdirs(directory):
            members = live_files(sub, ".lean")
            if not members:
                continue
            key = os.path.basename(sub) + "/"
            total = sum(line_count(m) for m in members)
            if cols == "files-lines":
                nums = [str(len(members)), "{:,}".format(total)]
            else:
                nums = ["—"]
            link = None
            if want_link and os.path.isfile(os.path.join(sub, "README.md")):
                link = os.path.basename(sub) + "/README.md"
            out.append((key, nums, link))
    return out


def render_block(opts, existing_lines):
    directory = opts.get("dir")
    if not directory:
        raise SystemExit("emit-inventory: BEGIN marker has no dir= option")
    if not os.path.isdir(directory):
        raise SystemExit("emit-inventory: dir=%s does not exist" % directory)
    cols = opts.get("cols", "lines")
    want_desc = opts.get("desc", "yes") != "no"
    ncols = (2 if cols == "files-lines" else 1) + 1 + (1 if want_desc else 0)

    header = None
    sep = None
    descriptions = {}
    order = []
    for ln in existing_lines:
        cells = split_row(ln)
        if cells is None or len(cells) < 2:
            continue
        if is_separator(cells):
            sep = ln.rstrip()
            continue
        if header is None and not order:
            header = ln.rstrip()
            continue
        key = row_key(cells[0])
        if want_desc:
            descriptions[key] = cells[-1].strip() if len(cells) >= ncols else TODO_DESC
        order.append(key)
    if header is None:
        header = "| File | Lines |" + (" Description |" if want_desc else "")
    if sep is None:
        sep = "|------|------:|" + ("-------------|" if want_desc else "")

    scanned = scan(directory, opts)
    scan_keys = {k for k, _, _ in scanned}

    # Pinned rows: an existing row naming a path outside the scan that still
    # resolves (e.g. `../FormalSystem.lean`) is kept, with its numbers refreshed.
    pinned = []
    for key in order:
        if key in scan_keys or key.endswith("/"):
            continue
        resolved = os.path.normpath(os.path.join(directory, key))
        if os.path.isfile(resolved):
            nums = ["{:,}".format(line_count(resolved))]
            if cols == "files-lines":
                nums = ["1"] + nums
            pinned.append((key, nums, None))

    rows = pinned + scanned
    if opts.get("sort") == "lines-desc":
        def size_of(r):
            raw = r[1][-1].replace(",", "")
            return int(raw) if raw.isdigit() else -1
        rows = sorted(rows, key=lambda r: (-size_of(r), r[0]))

    out = [header, sep]
    for key, nums, link in rows:
        if link == "literal":
            # A rollup row: the first cell is a metric name, not a path.
            label = key
        elif link:
            label = "[`%s`](%s)" % (key, link)
        else:
            label = "`%s`" % key
        cells = [label] + nums
        if want_desc:
            cells.append(descriptions.get(key, TODO_DESC))
        out.append("| " + " | ".join(cells) + " |")
    return out


def audit_hand_maintained(target, lines):
    """A table registered as hand-maintained must still be exhaustive.

    Registration buys exemption from *generation* (a deliberate reading order, no
    line counts), never from being checked: the failure mode a hand table has left
    is a file that appeared or moved and never made it into the list.
    """
    problems = []
    for i, ln in enumerate(lines):
        m = HAND_RE.match(ln.strip())
        if not m:
            continue
        directory = m.group("dir")
        j = i
        while j < len(lines) and not lines[j].strip().startswith("|"):
            j += 1
        have = set()
        while j < len(lines) and lines[j].strip().startswith("|"):
            cells = split_row(lines[j])
            if cells and not is_separator(cells):
                have.add(row_key(cells[0]))
            j += 1
        want = {os.path.basename(f) for f in live_loose_files(directory, ".lean")}
        want |= {os.path.basename(d) + "/" for d in live_subdirs(directory)
                 if live_files(d, ".lean")}
        for missing in sorted(want - have):
            problems.append("%s: %s is live but has no row" % (target, missing))
        for phantom in sorted(k for k in have - want if k.endswith((".lean", "/"))):
            problems.append("%s: row `%s` names nothing live" % (target, phantom))
    return problems


changed = []
hand_problems = []
for target in markdown_targets():
    with open(target, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    hand_problems.extend(audit_hand_maintained(target, lines))
    out = []
    i = 0
    touched = False
    in_fence = False
    while i < len(lines):
        if lines[i].lstrip().startswith("```"):
            in_fence = not in_fence
        m = None if in_fence else BEGIN_RE.match(lines[i])
        if not m:
            out.append(lines[i]); i += 1; continue
        begin = lines[i]
        j = i + 1
        body = []
        while j < len(lines) and not END_RE.match(lines[j]):
            body.append(lines[j]); j += 1
        if j >= len(lines):
            raise SystemExit("emit-inventory: %s has an unterminated BEGIN GENERATED block" % target)
        new_body = render_block(parse_opts(m.group("opts")), body)
        out.append(begin)
        out.extend(new_body)
        out.append(lines[j])
        if new_body != body:
            touched = True
        i = j + 1
    if not touched:
        continue
    changed.append(target)
    if not CHECK:
        with open(target, "w", encoding="utf-8") as fh:
            fh.write("\n".join(out))

if CHECK:
    if hand_problems:
        print("FAIL  INV  %d hand-maintained inventory row problem(s)" % len(hand_problems))
        for m in hand_problems:
            print("            %s" % m)
        if not changed:
            sys.exit(1)
    if changed:
        print("FAIL  INV  %d file(s) carry a stale generated inventory block" % len(changed))
        for t in changed:
            print("            %s" % t)
        print("            run: bash scripts/check-module-invariants.sh --emit-inventory")
        sys.exit(1)
    print("PASS  INV  every generated inventory block is current, "
          "every hand-maintained one is exhaustive")
    sys.exit(0)

if changed:
    print("rewrote %d file(s):" % len(changed))
    for t in changed:
        print("  %s" % t)
else:
    print("no generated inventory block needed a rewrite")
sys.exit(0)
PYEOF
  exit $?
fi


# Enforcement flags. C8/C9/C10 describe end-state invariants that the tree does
# not satisfy until the corresponding reorganization work lands. Each is computed
# and reported from the outset -- so progress is visible at every gate -- but only
# becomes exit-code-affecting once its flag flips to 1. Never flip a flag to 0 to
# make a gate pass; that is what the flag exists to prevent.
ENFORCE_C8=${ENFORCE_C8:-1}   # aggregator convention (enforced)
ENFORCE_C9=${ENFORCE_C9:-1}   # no task-number citations under FormalSystem/ (enforced)
ENFORCE_C10=${ENFORCE_C10:-1} # no stale docs/latex/typst paths (enforced)
# C9D is the C9 rule applied to docs/, which does not yet satisfy it. Computed and
# reported from the outset; flip to 1 once docs/development/PHASED_IMPLEMENTATION.md
# and the smaller residue are cleared.
ENFORCE_C9_DOCS=${ENFORCE_C9_DOCS:-0} # no task-number citations under docs/ (NOT yet enforced)
# C16 gates the Batteries env_linter batch (defsWithUnderscore, docBlame, simpNF,
# structureInType, tacticDocs, unusedArguments -- everything `lake exe runLinter`/the
# configured `lintDriver` checks). scripts/nolints.json grandfathers the 307 findings
# that existed when it was generated, so a clean run here means "no NEW finding", not
# "the tree has zero findings" -- exactly CI's own `lake lint` gate. Enforced from the
# outset because nolints.json makes it genuinely green today, unlike C8/C9/C10 above.
ENFORCE_C16=${ENFORCE_C16:-1} # env_linter batch has no un-nolisted finding (enforced)

FAILURES=0
pass() { printf 'PASS  %-4s %s\n' "$1" "$2"; }
fail() { printf 'FAIL  %-4s %s\n' "$1" "$2"; FAILURES=$((FAILURES + 1)); }
info() { printf 'INFO  %-4s %s\n' "$1" "$2"; }
note() { printf '            %s\n' "$1"; }
# Report a not-yet-enforced check: visible, but does not affect the exit code.
soft() { printf 'TODO  %-4s %s\n' "$1" "$2"; }

# Shared find filter. The archive is excluded by the `*/Boneyard/*` name glob;
# B0 asserts that this pattern matches exactly one directory.
live_lean() {
  find "$@" -name '*.lean' -not -path '*/Boneyard/*'
}

echo "=== Module invariants: $(git rev-parse --short HEAD 2>/dev/null || echo 'no-git') ==="
echo

# ---------------------------------------------------------------------------
# B0: Boneyard exclusion self-test
# ---------------------------------------------------------------------------
mapfile -t BONEYARDS < <(find FormalSystem -type d -name Boneyard | sort)
if [ "${#BONEYARDS[@]}" -eq 1 ]; then
  pass B0 "Boneyard exclusion covers exactly 1 directory"
  for b in "${BONEYARDS[@]}"; do note "$b"; done
else
  fail B0 "expected 1 Boneyard directory, found ${#BONEYARDS[@]}"
  for b in "${BONEYARDS[@]}"; do note "$b"; done
fi
# Prove the exclusion is load-bearing: archived files must not be in the live set.
ALL_LEAN=$(find FormalSystem -name '*.lean' | wc -l)
LIVE_LEAN=$(live_lean FormalSystem | wc -l)
if [ "$ALL_LEAN" -gt "$LIVE_LEAN" ]; then
  note "excluded $((ALL_LEAN - LIVE_LEAN)) archived .lean files ($ALL_LEAN total -> $LIVE_LEAN live)"
else
  fail B0 "exclusion filter removed nothing; archived files are leaking into live counts"
fi
echo

# ---------------------------------------------------------------------------
# C1: build
# ---------------------------------------------------------------------------
if [ "$RUN_BUILD" -eq 1 ]; then
  BUILD_LOG=$(mktemp)
  if lake build >"$BUILD_LOG" 2>&1; then
    pass C1 "lake build exits 0"
  else
    fail C1 "lake build failed"
    tail -40 "$BUILD_LOG" | while IFS= read -r l; do note "$l"; done
  fi
  if lake build BimodalTest >>"$BUILD_LOG" 2>&1; then
    pass C1 "lake build BimodalTest exits 0"
  else
    fail C1 "lake build BimodalTest failed"
    tail -40 "$BUILD_LOG" | while IFS= read -r l; do note "$l"; done
  fi
  rm -f "$BUILD_LOG"
else
  info C1 "skipped (--no-build)"
fi
echo

# ---------------------------------------------------------------------------
# C2: axiom sets for the four flagship theorems
#
# Do NOT scrape `lake build` stdout for these -- an incremental build may not
# re-emit them. A dedicated scratch file is compiled against the built library.
# ---------------------------------------------------------------------------
read -r -d '' AXIOM_BASELINE <<'BASELINE'
'FormalSystem.Metalogic.BXCanonical.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.BXCanonical.completeness_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.BXCanonical.completeness_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.BXCanonical.Chronicle.countermodel_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
BASELINE

if [ "$RUN_BUILD" -eq 1 ]; then
  AX_SRC=$(mktemp --suffix=.lean)
  cat >"$AX_SRC" <<'LEAN'
import FormalSystem
#print axioms FormalSystem.Metalogic.BXCanonical.completeness
#print axioms FormalSystem.Metalogic.BXCanonical.completeness_dense
#print axioms FormalSystem.Metalogic.BXCanonical.completeness_ztime
#print axioms FormalSystem.Metalogic.BXCanonical.Chronicle.countermodel_dense
LEAN
  # The pretty-printer wraps at a fixed width, and `FormalSystem.` is longer than the
  # namespace it replaced, so a long axiom record now spills onto continuation lines that
  # begin with a space. Rejoin those before grepping, or the record is silently truncated
  # and C2 reports a divergence that is purely cosmetic.
  AX_OUT=$(lake env lean "$AX_SRC" 2>&1 \
    | sed -e ':a' -e '$!N' -e 's/\n / /' -e 'ta' -e 'P' -e 'D' \
    | grep 'depends on axioms')
  rm -f "$AX_SRC"
  if [ "$AX_OUT" = "$AXIOM_BASELINE" ]; then
    pass C2 "all four flagship axiom sets match baseline"
    while IFS= read -r l; do note "$l"; done <<<"$AX_OUT"
  else
    fail C2 "axiom sets diverged from baseline -- this is a HARD STOP, not a new baseline"
    note "--- expected ---"
    while IFS= read -r l; do note "$l"; done <<<"$AXIOM_BASELINE"
    note "--- actual ---"
    while IFS= read -r l; do note "$l"; done <<<"$AX_OUT"
  fi
else
  info C2 "skipped (--no-build)"
fi
echo

# ---------------------------------------------------------------------------
# C3: the structural sorry inventory, asserted BY CONTENT
#
# The inventory is ZERO. `FormalSystem/` (excluding `Boneyard/`) contains no
# structural `sorry` at all: the last one, `countermodel_discrete`, was closed
# when the theorem moved from `WeakCanonical/Transfer.lean` to
# `WeakCanonical/GroupModel/CountermodelBase.lean` and was proved there at the
# `Q x_l Z` carrier off `companionChronicle`.
#
# Never assert a line number, and never relax this back to a nonzero count to
# accommodate a new sorry: a new structural sorry is a regression, and this
# check is the gate that says so.
# ---------------------------------------------------------------------------
SORRY_HITS=$(grep -rnE --include='*.lean' \
  '(^[[:space:]]*sorry[[:space:]]*$)|(:=[[:space:]]*sorry[[:space:]]*$)|(\bexact sorry\b)|(<;> sorry)' \
  FormalSystem | grep -v '/Boneyard/')
SORRY_COUNT=$(printf '%s' "$SORRY_HITS" | grep -c . || true)

if [ "$SORRY_COUNT" -ne 0 ]; then
  fail C3 "expected zero structural sorries, found $SORRY_COUNT"
  while IFS= read -r l; do note "$l"; done <<<"$SORRY_HITS"
else
  pass C3 "structural sorry inventory is ZERO across FormalSystem/ (Boneyard/ excluded)"
fi
echo

# ---------------------------------------------------------------------------
# C4/C5/C6/C7/C8/C11: graph, markdown, reachability, archive and structure checks
# ---------------------------------------------------------------------------
[ "$RUN_BUILD" -eq 0 ] && export SKIP_BUILD=1
export ENFORCE_C8
python3 - "$MANIFEST" "$ALLOWLIST" "$WAIVERS" <<'PYEOF'
import os, re, sys, subprocess

manifest_path, allowlist_path, waivers_path = sys.argv[1], sys.argv[2], sys.argv[3]
failures = 0
def pas(c, m): print(f"PASS  {c:<4} {m}")
def bad(c, m):
    global failures
    failures += 1
    print(f"FAIL  {c:<4} {m}")
def inf(c, m): print(f"INFO  {c:<4} {m}")
def note(m):   print(f"            {m}")

BONEYARD = os.sep + "Boneyard"

# The Boneyard-excluding walk lives in scripts/lib/live_walk.py and is shared
# with the --emit-inventory generator, so the inventory tables and C7's rollup
# can never disagree about what "live" means.
sys.path.insert(0, os.path.join("scripts", "lib"))
from live_walk import live_files  # noqa: E402

def mod_to_path(m):
    base = "Tests" if m.split(".")[0] == "BimodalTest" else "."
    return os.path.normpath(os.path.join(base, *m.split("."))) + ".lean"

def path_to_mod(p):
    for base in ("Tests/", ""):
        if p.startswith(base):
            return p[len(base):-len(".lean")].replace(os.sep, ".")
    return None

lean_files = (live_files("FormalSystem", ".lean") + live_files("Tests", ".lean")
              + (["FormalSystem.lean"]
                 if os.path.isfile("FormalSystem.lean") else []))
imp_re = re.compile(r"^import\s+((?:FormalSystem|BimodalTest)(?:\.[A-Za-z0-9_]+)*)\s*$", re.M)

graph, texts = {}, {}
for p in lean_files:
    txt = open(p, encoding="utf-8", errors="replace").read()
    texts[p] = txt
    graph[path_to_mod(p)] = imp_re.findall(txt)

# --- C4: dangling imports ---------------------------------------------------
dangling = []
for p in lean_files:
    for i, line in enumerate(texts[p].splitlines(), 1):
        m = imp_re.match(line + "\n")
        if not m:
            continue
        tgt = m.group(1)
        if not os.path.isfile(mod_to_path(tgt)):
            dangling.append((p, i, tgt))
total_imports = sum(len(v) for v in graph.values())
if dangling:
    bad("C4", f"{len(dangling)} dangling import(s) across {total_imports} import lines")
    for p, i, t in dangling:
        note(f"{p}:{i}: import {t}  ->  {mod_to_path(t)} (missing)")
else:
    pas("C4", f"all {total_imports} FormalSystem/BimodalTest import lines resolve")

# --- C5: markdown module paths ---------------------------------------------
allow = set()
if os.path.isfile(allowlist_path):
    for line in open(allowlist_path, encoding="utf-8"):
        line = line.split("#")[0].strip()
        if line:
            allow.add(line)

md_files = []
for root, dirs, files in os.walk("."):
    dirs[:] = [d for d in dirs
               if d not in (".git", ".lake", "specs", "Boneyard", "build", "__pycache__")]
    for f in files:
        if f.endswith(".md"):
            md_files.append(os.path.relpath(os.path.join(root, f), "."))

mod_re = re.compile(r"\b(?:FormalSystem|BimodalTest)(?:\.[A-Z][A-Za-z0-9_]*)+")

def resolves(m):
    base = "Tests" if m.split(".")[0] == "BimodalTest" else "."
    p = os.path.normpath(os.path.join(base, *m.split(".")))
    return os.path.isfile(p + ".lean") or os.path.isdir(p)

unresolved, used_allow = [], set()
for p in sorted(md_files):
    for i, line in enumerate(open(p, encoding="utf-8", errors="replace"), 1):
        for m in mod_re.findall(line):
            if resolves(m):
                continue
            if m in allow:
                used_allow.add(m)
                continue
            unresolved.append((p, i, m))
if unresolved:
    bad("C5", f"{len(unresolved)} unresolved module path(s) in non-specs markdown")
    for p, i, m in unresolved:
        note(f"{p}:{i}: {m}")
else:
    pas("C5", f"all module-shaped paths in {len(md_files)} markdown files resolve"
              + (f" ({len(used_allow)} allowlisted)" if used_allow else ""))
stale_allow = allow - used_allow
if stale_allow:
    inf("C5", f"{len(stale_allow)} allowlist entr(y/ies) no longer occur; prune them")
    for m in sorted(stale_allow):
        note(m)

# --- reachability (feeds C6 and C7) ----------------------------------------
roots = ["FormalSystem", "BimodalTest"]
try:
    lf = open("lakefile.lean", encoding="utf-8").read()
    roots += re.findall(r"root\s*:=\s*`([A-Za-z0-9_.]+)", lf)
except OSError:
    pass
seen, stack = set(), list(roots)
while stack:
    m = stack.pop()
    if m in seen or m not in graph:
        continue
    seen.add(m)
    stack.extend(graph[m])
unreachable = sorted(set(graph) - seen)

# --- C6: unreachable-module rot guard --------------------------------------
# Manifest entries may carry a `broken:` prefix, meaning the module is known not
# to compile. Those are still tracked (so they cannot be forgotten) but are not
# compile-checked -- the rot already happened and is recorded, not re-discovered
# on every run. Removing the prefix is how a repaired module re-enters the gate.
manifest, manifest_broken = [], []
if os.path.isfile(manifest_path):
    for line in open(manifest_path, encoding="utf-8"):
        line = line.split("#")[0].strip()
        if not line:
            continue
        if line.startswith("broken:"):
            manifest_broken.append(line[len("broken:"):].strip())
        else:
            manifest.append(line)
manifest_set = set(manifest) | set(manifest_broken)
unmanifested = [m for m in unreachable if m not in manifest_set]
if unmanifested:
    bad("C6", f"{len(unmanifested)} unreachable live module(s) absent from {manifest_path}")
    for m in unmanifested:
        note(f"{m}  ->  {mod_to_path(m)}")
else:
    pas("C6", f"all {len(unreachable)} unreachable live module(s) are manifested")

phantom = [m for m in manifest_set if m not in graph]
if phantom:
    bad("C6", f"{len(phantom)} manifest entr(y/ies) name a module that does not exist")
    for m in sorted(phantom):
        note(m)

stale_manifest = sorted(m for m in manifest_set if m in seen)
if stale_manifest:
    bad("C6", f"{len(stale_manifest)} manifest entr(y/ies) name a REACHABLE module; "
              f"`lake build` already guards these -- delete the lines")
    for m in stale_manifest:
        note(m)

if manifest_broken:
    inf("C6", f"{len(manifest_broken)} module(s) manifested as known-broken (not compile-checked)")
    for m in manifest_broken:
        note(m)

if os.environ.get("SKIP_BUILD") != "1":
    broken = []
    for m in manifest:
        if m not in graph:
            continue
        # `lake build <module>` (not `lake env lean <path>`) is the authoritative
        # check: it builds the module's transitive dependencies first, so a
        # missing .olean for an unbuilt sibling is not mistaken for rot.
        r = subprocess.run(["lake", "build", m], capture_output=True, text=True)
        if r.returncode != 0:
            errs = [l for l in (r.stdout + r.stderr).splitlines() if "error:" in l]
            broken.append((m, errs[:4]))
    if broken:
        bad("C6", f"{len(broken)} manifested module(s) no longer compile")
        for m, lines in broken:
            note(m)
            for l in lines:
                note("  " + l)
    else:
        pas("C6", f"all {len(manifest)} manifested module(s) still compile in isolation")
else:
    inf("C6", "compile-check skipped (--no-build)")

# --- C7: live inventory (informational) -------------------------------------
inf("C7", f"{len(lean_files)} live .lean files "
          f"({len(live_files('FormalSystem', '.lean'))} FormalSystem / "
          f"{len(live_files('Tests', '.lean'))} Tests); "
          f"{len(seen)} reachable, {len(unreachable)} unreachable")
counts = {}
for p in live_files("FormalSystem", ".lean"):
    top = os.path.relpath(p, "FormalSystem").split(os.sep)[0]
    if top.endswith(".lean"):
        top = "(loose)"
    counts[top] = counts.get(top, 0) + 1
for k in sorted(counts):
    note(f"{k:<20} {counts[k]:>4}")

# --- C8: aggregator convention ----------------------------------------------
# Convention: a directory `X/` has exactly one sibling aggregator `X.lean`.
# Allowlisted exception: `FormalSystem.lean` + `FormalSystem/FormalSystem.lean`.
# That pair is the Lake `lean_lib FormalSystem` root (`srcDir := "."`,
# `roots := #[`FormalSystem]`), so the self-named indirection is load-bearing, not a
# convention violation.
C8_ALLOW_SELFNAMED = {"FormalSystem/FormalSystem.lean"}
c8_problems = []
for parent in ("FormalSystem", "FormalSystem/Metalogic"):
    for d in sorted(os.listdir(parent)):
        full = os.path.join(parent, d)
        if not os.path.isdir(full) or d == "Boneyard":
            continue
        # Only Lean-bearing directories participate in the aggregator convention.
        # Asset directories (docs/, latex/, typst/) have no module to aggregate.
        if not live_files(full, ".lean"):
            continue
        sibling = full + ".lean"
        selfnamed = os.path.join(full, d + ".lean")
        if not os.path.isfile(sibling):
            c8_problems.append(f"{full}/ has no sibling aggregator {sibling}")
        if os.path.isfile(selfnamed) and selfnamed not in C8_ALLOW_SELFNAMED:
            c8_problems.append(f"{selfnamed} is a self-named aggregator (use the sibling form)")
if c8_problems:
    if os.environ.get("ENFORCE_C8") == "1":
        bad("C8", f"{len(c8_problems)} aggregator convention violation(s)")
    else:
        print(f"TODO  {'C8':<4} {len(c8_problems)} aggregator convention violation(s) (not yet enforced)")
    for m in c8_problems:
        note(m)
else:
    pas("C8", "every FormalSystem/ and Metalogic/ subdirectory has exactly one sibling aggregator")

# --- C11: archive import resolution ----------------------------------------
# The Boneyard is uncompiled, so `lake build` cannot notice when an archived
# file's import goes stale. Without this check the archive rots silently:
# 65 archived import lines were already dangling when the two archives were
# consolidated into one. C11 makes the invariant enforceable -- every archived
# import must resolve to a file on disk, or be named in the waiver file with a
# recorded reason. Shipped enforced from day one, deliberately without an
# ENFORCE_C11 flag: the flags above exist for end-state invariants the tree does
# not yet satisfy, and this one is satisfied at the moment it lands.
#
# The regex is C4's, verbatim. Do NOT widen it to a bare `^import`: archived
# files carry block-comment continuation lines and fenced code blocks that begin
# with the word `import`, which inflate a naive count by 31 lines and would
# produce that many false failures.
def archive_files(base):
    out = []
    for root, dirs, files in os.walk(base):
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return sorted(out)

archive_roots = []
for root, dirs, files in os.walk("FormalSystem"):
    if os.path.basename(root) == "Boneyard":
        archive_roots.append(root)
        dirs[:] = []
archive_lean = []
for r in sorted(archive_roots):
    archive_lean.extend(archive_files(r))

waived, waiver_reasons = set(), {}
if os.path.isfile(waivers_path):
    for line in open(waivers_path, encoding="utf-8"):
        raw = line.rstrip("\n")
        mod = raw.split("#")[0].strip()
        if mod:
            waived.add(mod)
            waiver_reasons[mod] = raw.split("#", 1)[1].strip() if "#" in raw else ""

arch_dangling, used_waiver, arch_imports = [], set(), 0
for p in archive_lean:
    txt = open(p, encoding="utf-8", errors="replace").read()
    for i, line in enumerate(txt.splitlines(), 1):
        m = imp_re.match(line + "\n")
        if not m:
            continue
        arch_imports += 1
        tgt = m.group(1)
        if os.path.isfile(mod_to_path(tgt)):
            continue
        if tgt in waived:
            used_waiver.add(tgt)
            continue
        arch_dangling.append((p, i, tgt))

if arch_dangling:
    bad("C11", f"{len(arch_dangling)} unwaived dangling import(s) across "
               f"{arch_imports} archived import lines in {len(archive_lean)} archived file(s)")
    for p, i, t in arch_dangling:
        note(f"{p}:{i}: import {t}  ->  {mod_to_path(t)} (missing, not waived)")
    note(f"repair the import, or add `{arch_dangling[0][2]}` to {waivers_path} with a reason")
else:
    pas("C11", f"all {arch_imports} archived import lines in {len(archive_lean)} archived "
               f"file(s) resolve ({len(used_waiver)} waived)")

stale_waivers = waived - used_waiver
if stale_waivers:
    inf("C11", f"{len(stale_waivers)} waiver entr(y/ies) no longer occur; prune them")
    for m in sorted(stale_waivers):
        note(m)

sys.exit(1 if failures else 0)
PYEOF
PY_STATUS=$?
[ "$PY_STATUS" -ne 0 ] && FAILURES=$((FAILURES + 1))
echo

# ---------------------------------------------------------------------------
# INV: generated inventory blocks are current
#
# The CI path runs the --check sub-mode only, never the writer: a stale block is
# a failure a developer resolves with `--emit-inventory`, not something a gate
# silently rewrites underneath them.
# ---------------------------------------------------------------------------
INV_OUT=$(bash "$0" --emit-inventory --check 2>&1)
INV_STATUS=$?
printf '%s\n' "$INV_OUT"
[ "$INV_STATUS" -ne 0 ] && FAILURES=$((FAILURES + 1))
echo


# ---------------------------------------------------------------------------
# C9: no task-number citations under FormalSystem/, lakefile.lean, README.md,
# or scripts/
#
# `.claude/rules/no-task-references-in-deliverables.md` forbids ephemeral
# task-management identifiers in deliverable files. Task numbers are renumbered
# by vault operations and mean nothing to a future reader of a README. Scope
# widened beyond FormalSystem/ to catch the same defect in the other places it
# was slipping past this check: lakefile.lean's lean_exe docstrings and
# scripts/*.sh's own comments. specs/** stays excluded -- it is the rule's own
# documented exemption -- and this script's own path is excluded (self-match:
# widening the scan to scripts/ would otherwise catch this file's own header
# examples the moment one is added, the same reason C10 self-excludes below).
# ---------------------------------------------------------------------------
TASK_REFS=$(grep -rniE --include='*.lean' --include='*.md' --include='*.sh' \
  '\b(tasks?[[:space:]]+#?[0-9]+|task-[0-9]+)\b' \
  FormalSystem lakefile.lean README.md scripts 2>/dev/null \
  | grep -v '/Boneyard/' | grep -v '^scripts/check-module-invariants\.sh:')
TASK_REF_COUNT=$(printf '%s' "$TASK_REFS" | grep -c . || true)
if [ "$TASK_REF_COUNT" -eq 0 ]; then
  pass C9 "zero task-number citations under FormalSystem/, lakefile.lean, README.md, scripts/"
else
  MSG="$TASK_REF_COUNT task-number citation(s) under FormalSystem/, lakefile.lean, README.md, scripts/ (use a durable anchor instead)"
  if [ "$ENFORCE_C9" -eq 1 ]; then fail C9 "$MSG"; else soft C9 "$MSG (not yet enforced)"; fi
  printf '%s\n' "$TASK_REFS" | head -20 | while IFS= read -r l; do note "$l"; done
  [ "$TASK_REF_COUNT" -gt 20 ] && note "... and $((TASK_REF_COUNT - 20)) more"
fi
echo

# ---------------------------------------------------------------------------
# C10: no references to the pre-relocation asset paths
#
# docs/, latex/ and typst/ live at the project root. `specs/**` legitimately
# records the historical paths and is excluded.
# ---------------------------------------------------------------------------
STALE_PATHS=$(grep -rnE 'FormalSystem/(docs|latex|typst)\b' . \
  --exclude-dir=.git --exclude-dir=.lake --exclude-dir=specs \
  --exclude-dir=build --exclude-dir=__pycache__ 2>/dev/null \
  | grep -v '/Boneyard/' \
  | grep -v '^\./scripts/check-module-invariants\.sh:')
STALE_COUNT=$(printf '%s' "$STALE_PATHS" | grep -c . || true)
if [ "$STALE_COUNT" -eq 0 ]; then
  pass C10 "zero references to FormalSystem/{docs,latex,typst} outside specs/"
else
  MSG="$STALE_COUNT stale reference(s) to FormalSystem/{docs,latex,typst}"
  if [ "$ENFORCE_C10" -eq 1 ]; then fail C10 "$MSG"; else soft C10 "$MSG (not yet enforced)"; fi
  printf '%s\n' "$STALE_PATHS" | head -20 | while IFS= read -r l; do note "$l"; done
  [ "$STALE_COUNT" -gt 20 ] && note "... and $((STALE_COUNT - 20)) more"
fi
echo

# ---------------------------------------------------------------------------
# C12/C13: markdown path and link resolution across docs/ + README.md
#
# C5 matches only DOTTED module names (`FormalSystem.Metalogic.Foo`) via
# `\b(?:FormalSystem|BimodalTest)(?:\.[A-Z][A-Za-z0-9_]*)+`, so the SLASH form
# (`FormalSystem/Metalogic/Foo.lean`) is invisible to it. That blind spot is why a
# source-file table naming six files, four of which did not exist, survived a green
# gate for as long as it did. C12 closes it.
#
# C5's regex is deliberately NOT extended to cover this: adding `Bimodal` to it
# would turn the gate red on occurrences in `FormalSystem/**/README.md` that are a
# separate piece of work. C12 is a distinct check over a distinct path shape.
#
# Both are scoped to `docs/` + `README.md`, and both take a companion allowlist
# FILE rather than hardcoded exclusions, so a future surprise is recorded rather
# than forcing an unrelated edit.
# ---------------------------------------------------------------------------
python3 - "$SLASH_ALLOWLIST" "$LINK_ALLOWLIST" <<'MDPYEOF'
import os, re, sys

slash_allow_path, link_allow_path = sys.argv[1], sys.argv[2]
failures = 0
def pas(c, m): print(f"PASS  {c:<4} {m}")
def bad(c, m):
    global failures
    failures += 1
    print(f"FAIL  {c:<4} {m}")
def inf(c, m): print(f"INFO  {c:<4} {m}")
def note(m):   print(f"            {m}")

def read_allowlist(path):
    out = set()
    if os.path.isfile(path):
        for line in open(path, encoding="utf-8"):
            line = line.split("#")[0].strip()
            if line:
                out.add(line)
    return out

# The scope: every markdown file under docs/, plus the front page.
md_files = []
for root, dirs, files in os.walk("docs"):
    dirs[:] = [d for d in dirs if d not in (".git", "__pycache__")]
    for f in files:
        if f.endswith(".md"):
            md_files.append(os.path.normpath(os.path.join(root, f)))
if os.path.isfile("README.md"):
    md_files.append("README.md")
md_files.sort()

# --- C12: slash-shaped source paths ----------------------------------------
# `Logos/` and `Bimodal/` are the two pre-merge tree roots. Neither resolves to
# anything today, so any occurrence is by construction a defect -- which is exactly
# why they are in the pattern.
slash_re = re.compile(r"\b(?:FormalSystem|Tests|Logos|Bimodal)/[A-Za-z0-9_./-]+")

def slash_resolves(p):
    return (os.path.exists(p) or os.path.isfile(p + ".lean")
            or os.path.isfile(p + ".md") or os.path.isdir(p))

slash_allow = read_allowlist(slash_allow_path)
unresolved, used_slash_allow = [], set()
for f in md_files:
    for i, line in enumerate(open(f, encoding="utf-8", errors="replace"), 1):
        for m in slash_re.findall(line):
            m = m.rstrip("./,:;)")
            if not m or slash_resolves(m):
                continue
            if m in slash_allow:
                used_slash_allow.add(m)
                continue
            unresolved.append((f, i, m))

if unresolved:
    bad("C12", f"{len(unresolved)} unresolved slash-shaped source path(s) in docs/ + README.md")
    for f, i, m in unresolved[:20]:
        note(f"{f}:{i}: {m}")
    if len(unresolved) > 20:
        note(f"... and {len(unresolved) - 20} more")
else:
    pas("C12", f"all slash-shaped source paths in {len(md_files)} markdown files resolve"
               + (f" ({len(used_slash_allow)} allowlisted)" if used_slash_allow else ""))
stale = slash_allow - used_slash_allow
if stale:
    inf("C12", f"{len(stale)} allowlist entr(y/ies) no longer occur; prune them")
    for m in sorted(stale):
        note(m)

# --- C13: relative markdown links ------------------------------------------
link_re = re.compile(r"\[[^\]]*\]\(([^)]+)\)")
link_allow = read_allowlist(link_allow_path)
used_link_allow = set()
broken = []
for f in md_files:
    if f in link_allow:
        used_link_allow.add(f)
        continue
    d = os.path.dirname(f) or "."
    for i, line in enumerate(open(f, encoding="utf-8", errors="replace"), 1):
        for link in link_re.findall(line):
            if link.startswith(("http://", "https://", "mailto:", "#")):
                continue
            target = link.split("#")[0]
            if not target:
                continue
            full = target if target.startswith("/") else os.path.join(d, target)
            if not os.path.exists(full):
                broken.append((f, i, link))

if broken:
    bad("C13", f"{len(broken)} unresolved relative markdown link(s) in docs/ + README.md")
    for f, i, link in broken[:20]:
        note(f"{f}:{i}: -> {link}")
    if len(broken) > 20:
        note(f"... and {len(broken) - 20} more")
else:
    pas("C13", f"all relative markdown links in {len(md_files) - len(used_link_allow)} "
               f"markdown files resolve"
               + (f" ({len(used_link_allow)} file(s) allowlisted)" if used_link_allow else ""))
stale_links = link_allow - used_link_allow
if stale_links:
    inf("C13", f"{len(stale_links)} link-allowlist entr(y/ies) match no file; prune them")
    for m in sorted(stale_links):
        note(m)

sys.exit(1 if failures else 0)
MDPYEOF
MD_STATUS=$?
[ "$MD_STATUS" -ne 0 ] && FAILURES=$((FAILURES + 1))
echo

# ---------------------------------------------------------------------------
# C14: status-claim tripwires
#
# This is the check that closes the loop the rest of this script leaves open.
# C2 and C3 assert facts about the TREE; nothing asserted that `docs/` agrees
# with them. It has two halves:
#
#   (i)  a content scan for STALE literals -- an axiom count that is not 45, or a
#        table row documenting a non-zero sorry count. This half is cheap and
#        always runs. Its scope is docs/ + README.md + FormalSystem/**/*.lean:
#        the .lean half was added because C14's markdown-only scope is exactly
#        why SIX "42 axiom constructors" claims survived a 42 -> 45 change
#        untouched -- every one of them lived in a Lean docstring, where C14
#        could not see it. Lean doc comments are documentation and are in scope.
#   (ii) `#print axioms` for the two headline theorems that C2's four do not
#        cover, so that the decidability soundness bridge and RTime
#        completeness are pinned by the BUILD rather than by prose. This half
#        reuses C2's scratch-file + `lake env lean` machinery, including the
#        continuation-line rejoin, and skips under --no-build exactly as C2 does.
#
# The stale-literal patterns are deliberately narrow. A broad `[1-9]` scan over
# any line containing "sorry" produces false positives on prose that says the
# count is zero; the table-row shape is what actually carries a documented count.
# ---------------------------------------------------------------------------
C14_FAIL=0

# (i) stale axiom counts. 45 is the constructor count of `inductive Axiom`, per
# `Axiom.minFrameClass`. 42 is the figure in the stale `Axioms.lean` docstring,
# which omits the RTime (Dedekind-complete) layer; 21, 14 and 44 are older figures still.
# Scope note: `FormalSystem` is scanned for `*.lean` only, and Boneyard/ is excluded --
# archived modules are not documentation and are allowed to carry historical figures.
#
# WIDENING (both branches, kept identical so they cannot drift apart): the terminal
# word set gains `schema` (matches `schemata` too, since the pattern has no trailing
# `\b`) alongside `axiom`/`constructor`, and an optional single interposed word (e.g.
# "21 TM axiom schemas") is now tolerated between the count and the terminal word.
STALE_AXIOMS=$(grep -rniE --include='*.md' \
  '\b(14|21|42|44)[[:space:]]+([A-Za-z⁺+]+[[:space:]]+)?(axiom|constructor|schema)' \
  docs README.md 2>/dev/null || true)
# The trailing `grep -i axiom` is a PRECISION guard, not a weakening: `.lean` sources
# carry constructor counts for types other than `Axiom` (e.g. `EnrichedFormula`'s 21
# constructors in Automation/Normalization.lean), and a bare "21 constructors" in such
# a docstring is a correct statement about a different type. Requiring the word "axiom"
# somewhere on the line keeps the tripwire aimed at axiom-count claims. The markdown
# half above is deliberately left exactly as it was -- this is a widening of C14's
# scope, not a rewrite of its existing behavior.
#
# A second PRECISION guard (`grep -v -i covers`) was added alongside the first when
# widening exposed a genuine false positive: `Automation/ProofSearch/Core.lean`
# documents that its matcher "covers" 42 of the tree's 45 axiom constructors --
# a correct SUBSET claim, not a stale TOTAL claim, and the word "covers" is what
# distinguishes the two in every case checked at widening time (verified: neither
# guard removes either of this phase's two genuine stale-count fixes).
STALE_AXIOMS_LEAN=$(grep -rniE --include='*.lean' \
  '\b(14|21|42|44)[[:space:]]+([A-Za-z⁺+]+[[:space:]]+)?(axiom|constructor|schema)' \
  FormalSystem 2>/dev/null \
  | grep -v '/Boneyard/' | grep -i 'axiom' | grep -v -i 'covers' || true)
STALE_AXIOMS=$(printf '%s\n%s' "$STALE_AXIOMS" "$STALE_AXIOMS_LEAN" | grep -c . >/dev/null \
  && printf '%s\n%s' "$STALE_AXIOMS" "$STALE_AXIOMS_LEAN" | grep . || true)
STALE_AXIOM_COUNT=$(printf '%s' "$STALE_AXIOMS" | grep -c . || true)

# (i) documented non-zero sorry counts, in table-row shape (`... sorries | 7`).
# C3 asserts the real inventory is zero, so any such row is stale by construction.
STALE_SORRIES=$(grep -rniE --include='*.md' \
  'sorr(y|ies)[^|]*\|[[:space:]]*[1-9]' docs README.md 2>/dev/null || true)
STALE_SORRY_COUNT=$(printf '%s' "$STALE_SORRIES" | grep -c . || true)

if [ "$STALE_AXIOM_COUNT" -eq 0 ] && [ "$STALE_SORRY_COUNT" -eq 0 ]; then
  pass C14 "no stale axiom or sorry counts documented in docs/ + README.md + FormalSystem/*.lean"
else
  C14_FAIL=1
  fail C14 "$STALE_AXIOM_COUNT stale axiom count(s), $STALE_SORRY_COUNT documented non-zero sorry count(s)"
  [ "$STALE_AXIOM_COUNT" -gt 0 ] && printf '%s\n' "$STALE_AXIOMS" | head -10 \
    | while IFS= read -r l; do note "$l"; done
  [ "$STALE_SORRY_COUNT" -gt 0 ] && printf '%s\n' "$STALE_SORRIES" | head -10 \
    | while IFS= read -r l; do note "$l"; done
  note "the tree is the authority: C3 asserts zero sorries, Axiom.minFrameClass gives 45 axioms"
fi

# (ii) #print axioms for the theorems C2 does not cover.
# The C14BASE and C14LEAN heredocs below are compared by exact string equality, so they must
# list the same declarations in the same order. Edit them together, appending to both.
#
# The list is long by design. It is the consolidated axiom manifest for the
# consequence / compactness / strong-completeness stack: every declaration in
# Metalogic/{StrongCompleteness,Compactness,DiscreteNonCompactness,DedekindNonCompactness}.lean
# and Metalogic/Conservativity/TMCompletenessReduction.lean that used to carry its own in-file
# `#print axioms` directive now lives here instead. Exactly five in-file directives remain, on
# the five termini: strongCompletenessBase, strongCompletenessDense, notCompactZTime,
# notCompactRTime, consequence_completeness_rtime.
#
# Seven entries carry a STRICT SUBSET of [propext, Classical.choice, Quot.sound], recorded
# literally rather than rounded up: setConsequence_of_not_satisfiable, satisfiableSet_iff_
# finitelySatisfiable, modelExistence_iff_finitelySatisfiable, Conservativity.TMFrag,
# Semantics.starValidIn_ofFormula_iff and Semantics.galoisClosed_mod are [propext], and
# qDepth_qAlpha is [propext, Quot.sound]. A smaller dependency is not a regression.
#
# The second block below (soundness onward) is the SORRY-FREE claim set of
# FormalSystem/Metalogic.lean's module docstring. Every declaration that docstring calls
# SORRY-FREE is pinned here or by C2, so no such claim is prose-only: the docstring asserts
# it and this baseline proves it. Adding a SORRY-FREE bullet to Metalogic.lean without
# adding its subject here reintroduces exactly the drift this block exists to prevent.
read -r -d '' C14_BASELINE <<'C14BASE'
'FormalSystem.Metalogic.Decidability.sound_of_isValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.completeness_rtime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.strongCompletenessBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.strongCompletenessDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.semantic_deduction_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_setConsequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.strongCompleteness_of_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.setConsequence_of_not_satisfiable' depends on axioms: [propext]
'FormalSystem.Metalogic.compact_of_strongCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.strongCompleteness_iff_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.not_compact_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.not_strongCompleteness_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.compact_of_modelExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.modelExistence_of_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.compact_iff_modelExistence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.consequence_completeness_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.completeness_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_base_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.consequence_completeness_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.completeness_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_dense_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.consequence_completeness_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.completeness_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_ztime_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.sat_ofModel_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.modelExistence_of_satPreserved' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.modelExistenceBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.modelExistenceDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.compactBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.compactDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.truthAt_next_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.truthAt_next_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.archWitness_finitely_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.archWitness_not_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.notStrongCompletenessZTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.qDepth_qAlpha' depends on axioms: [propext, Quot.sound]
'FormalSystem.Metalogic.dedWitness_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.dedWitness_not_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.dedWitness_finitely_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.notStrongCompletenessRTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.modelExistenceRTime_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.tmComplete_iff_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.tmCompleteBase_iff_forwardBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.tmCompleteZTime_iff_forwardZTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.tmCompleteDense_iff_forwardDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.tmCompleteRTime_iff_forwardRTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.qAlpha_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.exists_strictMono_qPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.setConsequence_iff_not_satisfiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.satisfiableSet_iff_finitelySatisfiable' depends on axioms: [propext]
'FormalSystem.Metalogic.modelExistence_iff_finitelySatisfiable' depends on axioms: [propext]
'FormalSystem.Metalogic.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.soundness_rtime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.WeakCanonical.countermodel_discrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.notCompactZTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.notCompactRTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.truthAt_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_soundness_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_soundness_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_soundness_rtime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_not_derivable_nil_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.bl_not_derivable_nil_bot_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.derivable_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.ceb_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.cef_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.ced_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.cec_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.TMFrag' depends on axioms: [propext]
'FormalSystem.Metalogic.Conservativity.tmFrag_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tmFrag_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tmFrag_complete_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tmFrag_complete_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tmFrag_complete_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tmFrag_complete_rtime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tm_le_tmFrag' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.tm_lt_tmFrag_ztime' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.blCompactBase' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.blCompactDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.star_soundness_validIn' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Conservativity.starDerivable_ofFormula_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.starValidIn_ofFormula_iff' depends on axioms: [propext]
'FormalSystem.Metalogic.Decidability.decide' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.galoisClosed_mod' depends on axioms: [propext]
'FormalSystem.Semantics.galoisClosed_of_indicator' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.galoisClosed_sat_dense' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.galoisClosed_isDiscrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.validOn_nextTop_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Semantics.validOn_nextTop_iff_isDiscrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Independence.sat_rtime_ssubset_mod_axiomSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Independence.sat_ztime_ssubset_mod_axiomSet' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.Independence.deterministic_not_starDefinable' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.WeakCanonical.Kamp.kampPriorExpressiveCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.WeakCanonical.uSExpressivelyCompleteOverPrior' depends on axioms: [propext, Classical.choice, Quot.sound]
'FormalSystem.Metalogic.consequence_completeness_rtime' depends on axioms: [propext, Classical.choice, Quot.sound]
C14BASE

if [ "$RUN_BUILD" -eq 1 ]; then
  C14_SRC=$(mktemp --suffix=.lean)
  cat >"$C14_SRC" <<'C14LEAN'
import FormalSystem
#print axioms FormalSystem.Metalogic.Decidability.sound_of_isValid
#print axioms FormalSystem.Metalogic.completeness_rtime
#print axioms FormalSystem.Metalogic.strongCompletenessBase
#print axioms FormalSystem.Metalogic.strongCompletenessDense
#print axioms FormalSystem.Metalogic.semantic_deduction_in
#print axioms FormalSystem.Metalogic.soundness_consequence
#print axioms FormalSystem.Metalogic.soundness_setConsequence
#print axioms FormalSystem.Metalogic.strongCompleteness_of_compact
#print axioms FormalSystem.Metalogic.setConsequence_of_not_satisfiable
#print axioms FormalSystem.Metalogic.compact_of_strongCompleteness
#print axioms FormalSystem.Metalogic.strongCompleteness_iff_compact
#print axioms FormalSystem.Metalogic.not_compact_of_witness
#print axioms FormalSystem.Metalogic.not_strongCompleteness_of_witness
#print axioms FormalSystem.Metalogic.compact_of_modelExistence
#print axioms FormalSystem.Metalogic.modelExistence_of_compact
#print axioms FormalSystem.Metalogic.compact_iff_modelExistence
#print axioms FormalSystem.Metalogic.consequence_completeness_base
#print axioms FormalSystem.Metalogic.completeness_base
#print axioms FormalSystem.Metalogic.soundness_base_consequence
#print axioms FormalSystem.Metalogic.consequence_completeness_dense
#print axioms FormalSystem.Metalogic.completeness_dense
#print axioms FormalSystem.Metalogic.soundness_dense_consequence
#print axioms FormalSystem.Metalogic.consequence_completeness_ztime
#print axioms FormalSystem.Metalogic.completeness_ztime
#print axioms FormalSystem.Metalogic.soundness_ztime_consequence
#print axioms FormalSystem.Metalogic.sat_ofModel_frame
#print axioms FormalSystem.Metalogic.modelExistence_of_satPreserved
#print axioms FormalSystem.Metalogic.modelExistenceBase
#print axioms FormalSystem.Metalogic.modelExistenceDense
#print axioms FormalSystem.Metalogic.compactBase
#print axioms FormalSystem.Metalogic.compactDense
#print axioms FormalSystem.Metalogic.truthAt_next_iff
#print axioms FormalSystem.Metalogic.truthAt_next_iterate
#print axioms FormalSystem.Metalogic.archWitness_finitely_satisfiable
#print axioms FormalSystem.Metalogic.archWitness_not_satisfiable
#print axioms FormalSystem.Metalogic.notStrongCompletenessZTime
#print axioms FormalSystem.Metalogic.qDepth_qAlpha
#print axioms FormalSystem.Metalogic.dedWitness_core
#print axioms FormalSystem.Metalogic.dedWitness_not_satisfiable
#print axioms FormalSystem.Metalogic.dedWitness_finitely_satisfiable
#print axioms FormalSystem.Metalogic.notStrongCompletenessRTime
#print axioms FormalSystem.Metalogic.modelExistenceRTime_refuted
#print axioms FormalSystem.Metalogic.tmComplete_iff_forward
#print axioms FormalSystem.Metalogic.tmCompleteBase_iff_forwardBase
#print axioms FormalSystem.Metalogic.tmCompleteZTime_iff_forwardZTime
#print axioms FormalSystem.Metalogic.tmCompleteDense_iff_forwardDense
#print axioms FormalSystem.Metalogic.tmCompleteRTime_iff_forwardRTime
#print axioms FormalSystem.Metalogic.qAlpha_step
#print axioms FormalSystem.Metalogic.exists_strictMono_qPoints
#print axioms FormalSystem.Metalogic.setConsequence_iff_not_satisfiable
#print axioms FormalSystem.Metalogic.satisfiableSet_iff_finitelySatisfiable
#print axioms FormalSystem.Metalogic.modelExistence_iff_finitelySatisfiable
#print axioms FormalSystem.Metalogic.soundness
#print axioms FormalSystem.Metalogic.soundness_dense
#print axioms FormalSystem.Metalogic.soundness_ztime
#print axioms FormalSystem.Metalogic.soundness_rtime
#print axioms FormalSystem.Metalogic.WeakCanonical.countermodel_discrete
#print axioms FormalSystem.Metalogic.notCompactZTime
#print axioms FormalSystem.Metalogic.notCompactRTime
#print axioms FormalSystem.Semantics.truthAt_tr
#print axioms FormalSystem.Metalogic.bl_soundness
#print axioms FormalSystem.Metalogic.bl_soundness_dense
#print axioms FormalSystem.Metalogic.bl_soundness_ztime
#print axioms FormalSystem.Metalogic.bl_soundness_rtime
#print axioms FormalSystem.Metalogic.bl_not_derivable_nil_bot
#print axioms FormalSystem.Metalogic.bl_not_derivable_nil_bot_ztime
#print axioms FormalSystem.Metalogic.Conservativity.translate
#print axioms FormalSystem.Metalogic.Conservativity.derivable_translate
#print axioms FormalSystem.Metalogic.Conservativity.ceb_backward
#print axioms FormalSystem.Metalogic.Conservativity.cef_backward
#print axioms FormalSystem.Metalogic.Conservativity.ced_backward
#print axioms FormalSystem.Metalogic.Conservativity.cec_backward
#print axioms FormalSystem.Metalogic.Conservativity.TMFrag
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_sound
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_complete
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_complete_base
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_complete_dense
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_complete_ztime
#print axioms FormalSystem.Metalogic.Conservativity.tmFrag_complete_rtime
#print axioms FormalSystem.Metalogic.Conservativity.tm_le_tmFrag
#print axioms FormalSystem.Metalogic.Conservativity.tm_lt_tmFrag_ztime
#print axioms FormalSystem.Metalogic.Conservativity.blCompactBase
#print axioms FormalSystem.Metalogic.Conservativity.blCompactDense
#print axioms FormalSystem.Metalogic.Conservativity.star_soundness_validIn
#print axioms FormalSystem.Metalogic.Conservativity.starDerivable_ofFormula_iff
#print axioms FormalSystem.Semantics.starValidIn_ofFormula_iff
#print axioms FormalSystem.Metalogic.Decidability.decide
#print axioms FormalSystem.Semantics.galoisClosed_mod
#print axioms FormalSystem.Semantics.galoisClosed_of_indicator
#print axioms FormalSystem.Semantics.galoisClosed_sat_dense
#print axioms FormalSystem.Semantics.galoisClosed_isDiscrete
#print axioms FormalSystem.Semantics.validOn_nextTop_iff
#print axioms FormalSystem.Semantics.validOn_nextTop_iff_isDiscrete
#print axioms FormalSystem.Metalogic.Independence.sat_rtime_ssubset_mod_axiomSet
#print axioms FormalSystem.Metalogic.Independence.sat_ztime_ssubset_mod_axiomSet
#print axioms FormalSystem.Metalogic.Independence.deterministic_not_starDefinable
#print axioms FormalSystem.Metalogic.WeakCanonical.Kamp.kampPriorExpressiveCompleteness
#print axioms FormalSystem.Metalogic.WeakCanonical.uSExpressivelyCompleteOverPrior
#print axioms FormalSystem.Metalogic.consequence_completeness_rtime
C14LEAN
  C14_OUT=$(lake env lean "$C14_SRC" 2>&1 \
    | sed -e ':a' -e '$!N' -e 's/\n / /' -e 'ta' -e 'P' -e 'D' \
    | grep 'depends on axioms')
  rm -f "$C14_SRC"
  if [ "$C14_OUT" = "$C14_BASELINE" ]; then
    pass C14 "every pinned declaration matches its axiom baseline (the consequence/compactness stack plus every SORRY-FREE claim in Metalogic.lean)"
    while IFS= read -r l; do note "$l"; done <<<"$C14_OUT"
  else
    C14_FAIL=1
    fail C14 "axiom sets diverged from baseline -- this is a HARD STOP, not a new baseline"
    note "--- expected ---"
    while IFS= read -r l; do note "$l"; done <<<"$C14_BASELINE"
    note "--- actual ---"
    while IFS= read -r l; do note "$l"; done <<<"$C14_OUT"
  fi
else
  info C14 "#print axioms half skipped (--no-build); the content scan above still ran"
fi
echo

# ---------------------------------------------------------------------------
# C15: paper-anchor integrity
#
# WHY THIS EXISTS: 30 dangling paper-anchor citations accumulated in this tree
# across six paper editing waves, and not one of them was caught at write time.
# `lem:fibers` alone was cited 17 times after the paper deleted its `\label`.
# Nothing in this script asserted that a `def:`/`thm:`/`lem:`/`cor:`/`app:`/`rmk:`
# citation names an anchor that actually exists.
#
# RESOLUTION SOURCE IS THE RECORD, NOT THE PAPER. specs/paper-definitions-of-record.md
# is this repository's citation source of record (that is the record's own charter),
# and the paper lives in a different repository this one cannot see from CI. Resolving
# against the live .tex would make this check go red whenever the author edits the
# paper -- an event this repository does not control and cannot fix by editing itself.
# So a citation resolves if EITHER:
#
#   (a) it has a row in the record's machine-readable MANIFEST (a pinned anchor), or
#   (b) it has a row in the record's KNOWN-ANCHORS block, whose status is either
#       LIVE-UNPINNED (live in the paper, deliberately not pinned) or DANGLING
#       (retired, commented out, or never existed).
#
# Every anchor is therefore a RECORDED DECISION. An anchor with no row is either a
# typo or an undocumented citation, and both are defects.
#
# SCOPE is deliberate: specs/** is excluded (task artifacts routinely quote anchors
# that were live when they were written, and rewriting history is not the goal), and
# FormalSystem/Boneyard/ is excluded (archived modules are frozen). What remains is
# live, load-bearing scope: FormalSystem/ (non-Boneyard), Tests/, typst/, docs/,
# and README.md.
# ---------------------------------------------------------------------------
C15_RECORD="specs/paper-definitions-of-record.md"
if [ ! -f "$C15_RECORD" ]; then
  fail C15 "record not found: $C15_RECORD (C15 cannot resolve any anchor without it)"
else
  C15_KNOWN=$(mktemp)
  # (a) manifest rows: anchor_id is field 1; strip the `#SubAnchor` suffix so that
  # `def:frame#Saturation` registers its parent `def:frame` too.
  sed -n '/<!-- MANIFEST:BEGIN -->/,/<!-- MANIFEST:END -->/p' "$C15_RECORD" \
    | grep -v '<!--' | grep -v '^```' | grep -v '^#' | grep -v '^[[:space:]]*$' \
    | cut -d'|' -f1 | sed 's/#.*//' >> "$C15_KNOWN"
  # (b) known-anchor rows
  sed -n '/<!-- KNOWN-ANCHORS:BEGIN -->/,/<!-- KNOWN-ANCHORS:END -->/p' "$C15_RECORD" \
    | grep -v '<!--' | grep -v '^```' | grep -v '^#' | grep -v '^[[:space:]]*$' \
    | cut -d'|' -f1 >> "$C15_KNOWN"
  sort -u -o "$C15_KNOWN" "$C15_KNOWN"

  C15_CITED=$(mktemp)
  # `--include` restricts the walk to documentation-bearing file types; `--exclude-dir`
  # drops the archive. Both are needed: `-h -o` discards the path, so a post-hoc path
  # filter is not available on this pipeline.
  grep -rhoE '\b(def|thm|lem|cor|app|rmk):[A-Za-z0-9][A-Za-z0-9_-]*' \
    --include='*.lean' --include='*.md' --include='*.typ' --exclude-dir=Boneyard \
    FormalSystem Tests typst docs README.md 2>/dev/null \
    | sort -u > "$C15_CITED" || true

  C15_UNKNOWN=$(comm -23 "$C15_CITED" "$C15_KNOWN")
  C15_UNKNOWN_COUNT=$(printf '%s' "$C15_UNKNOWN" | grep -c . || true)
  if [ "$C15_UNKNOWN_COUNT" -eq 0 ]; then
    C15_TOTAL=$(grep -c . "$C15_CITED" || true)
    pass C15 "all $C15_TOTAL paper-anchor citation(s) resolve against $C15_RECORD"
  else
    fail C15 "$C15_UNKNOWN_COUNT paper-anchor citation(s) resolve to nothing in $C15_RECORD"
    printf '%s\n' "$C15_UNKNOWN" | head -15 | while IFS= read -r a; do
      [ -z "$a" ] && continue
      loc=$(grep -rlF "$a" --include='*.lean' --include='*.md' --include='*.typ' \
              FormalSystem Tests typst docs README.md 2>/dev/null \
              | grep -v '/Boneyard/' | head -2 | tr '\n' ' ')
      note "$a  <- $loc"
    done
    note "fix the citation, or record the anchor in the record's KNOWN-ANCHORS block"
    note "(status LIVE-UNPINNED if it resolves in the paper, DANGLING if it does not)"
  fi
  rm -f "$C15_KNOWN" "$C15_CITED"
fi
echo

# ---------------------------------------------------------------------------
# C16: environment linters (defsWithUnderscore, docBlame, simpNF, structureInType,
# tacticDocs, unusedArguments, ...) via the configured lintDriver
#
# `lake exe runLinter FormalSystem` runs Batteries' full env_linter suite -- the same
# one `lintDriver := "batteries/runLinter"` wires into `lake lint`/CI -- and reads
# scripts/nolints.json unconditionally, filtering out every declaration recorded
# there before deciding pass/fail. nolints.json grandfathers the 307 findings that
# existed when it was generated (`lake exe runLinter --update FormalSystem`), so a
# clean run here means "no NEW finding since the grandfather baseline", mirroring
# CI's own `lake lint` gate exactly -- this is the local equivalent of that check.
# Never regenerate nolints.json to make a genuine regression disappear; confirm
# every new finding is intentional (or itself grandfather-worthy) before running
# `--update` again.
#
# `dupNamespace` is deliberately NOT part of this batch (it is a separate Lean-core
# text linter, not a Batteries @[env_linter], and never appears in runLinter's
# output regardless of its true count). Isolating it via the REAL linter requires
# `lake lint --builtin-only --lint-only .dupNamespace`, which forces Lake to
# rebuild the ENTIRE default target under different linter options on every
# single invocation (confirmed during this check's own development: roughly ten
# minutes, and OOM-killed once) -- unsustainable for a routinely-run script.
#
# Instead, dupNamespace's condition is checked TEXTUALLY below, reporting-only:
# it fires when a declaration's own name repeats a component of its enclosing
# `namespace`, so a plain scan tracking `namespace`/`section`/`end` nesting and
# flagging any `structure`/`inductive`/`def`/`abbrev`/`theorem`/`instance`/`class`
# whose name (plus, for a `structure`/`class`, its auto-generated field
# projections and `.mk` constructor) repeats an open segment reproduces the real
# linter's verdict closely, in milliseconds, with no build. This is intentionally
# an approximation (it will miss `to_additive`-style generated names, and
# multi-line/attribute-heavy declarations are best-effort) -- acceptable because
# this half is reporting-only. Validated against ChronicleTypes.lean: finds
# exactly the same 14 declarations `lake lint --builtin-only --lint-only
# .dupNamespace` reports, at the same lines. A HARDCODED count was deliberately
# rejected here: this script exists in part to catch hand-typed numbers drifting
# from the tree (see C14, and the two documents Phase 6 of this task corrects),
# so freezing dupNamespace's count would be the same defect class in miniature.
# ---------------------------------------------------------------------------
if [ "$RUN_BUILD" -eq 1 ]; then
  C16_LOG=$(mktemp)
  if lake exe runLinter FormalSystem >"$C16_LOG" 2>&1; then
    pass C16 "env_linter batch (defsWithUnderscore, docBlame, simpNF, structureInType, tacticDocs, unusedArguments) has no un-nolisted finding"
  else
    MSG="env_linter batch reports new finding(s) beyond scripts/nolints.json's grandfathered baseline"
    if [ "$ENFORCE_C16" -eq 1 ]; then fail C16 "$MSG"; else soft C16 "$MSG (not yet enforced)"; fi
    grep -m1 '^-- Found ' "$C16_LOG" | while IFS= read -r l; do note "$l"; done
    tail -20 "$C16_LOG" | while IFS= read -r l; do note "$l"; done
    note "run 'lake exe runLinter --update FormalSystem' only after confirming every new finding is intentional -- --update grandfathers everything currently reported, including a genuine regression"
  fi
  rm -f "$C16_LOG"
else
  info C16 "env_linter batch skipped (--no-build)"
fi
# dupNamespace: live textual check, runs regardless of --no-build (no build needed).
python3 - <<'PYEOF'
import os, re

def live_lean_files(base):
    out = []
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != "Boneyard"]
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return sorted(out)

ns_open_re = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
section_re = re.compile(r"^section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
end_re = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?\s*$")
decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|mutual\s+)*"
    r"(structure|inductive|def|abbrev|theorem|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
field_re = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*\s*:")

findings = []
for path in live_lean_files("FormalSystem"):
    stack, frames = [], []
    try:
        lines = open(path, encoding="utf-8", errors="replace").readlines()
    except OSError:
        continue
    n_lines = len(lines)
    i = 0
    while i < n_lines:
        raw = lines[i]
        line = raw.strip()
        m = ns_open_re.match(line)
        if m:
            segs = m.group(1).split(".")
            stack.extend(segs)
            frames.append(len(segs))
            i += 1
            continue
        if section_re.match(line):
            frames.append(0)
            i += 1
            continue
        if end_re.match(line):
            if frames:
                n = frames.pop()
                if n:
                    stack = stack[:-n] if n <= len(stack) else []
            i += 1
            continue
        m = decl_re.match(line)
        if m and stack:
            kind, ident = m.group(1), m.group(2)
            if ident.startswith("_root_."):
                combined = ident[len("_root_."):].split(".")
            else:
                combined = stack + ident.split(".")
            seen, dup = set(), None
            for s in combined:
                if s in seen:
                    dup = s
                    break
                seen.add(s)
            if dup:
                findings.append((path, i + 1, ident, dup))
                if kind in ("structure", "class") and ident == dup:
                    j, field_count, in_doc = i + 1, 0, False
                    while j < n_lines:
                        body_raw = lines[j]
                        stripped_body = body_raw.strip()
                        if stripped_body == "":
                            j += 1; continue
                        if not body_raw[:1].isspace():
                            break
                        if in_doc:
                            if "-/" in stripped_body:
                                in_doc = False
                            j += 1; continue
                        if stripped_body.startswith("/--"):
                            if "-/" not in stripped_body[3:]:
                                in_doc = True
                            j += 1; continue
                        if field_re.match(stripped_body):
                            field_count += 1
                        j += 1
                    findings.append((path, i + 1, f"{ident}.mk", dup))
                    for _ in range(field_count):
                        findings.append((path, i + 1, f"{ident}.<field>", dup))
        i += 1

if not findings:
    print("PASS  C16  dupNamespace: zero declaration(s) with a repeated namespace component (live textual check)")
else:
    print(f"INFO  C16  dupNamespace: {len(findings)} declaration(s) with a repeated namespace component (live textual check, approximate; never affects FAILURES)")
    for p, l, ident, dup in findings[:20]:
        print(f"            {p}:{l}: {ident} (duplicated component: {dup})")
    if len(findings) > 20:
        print(f"            ... and {len(findings) - 20} more")
PYEOF
echo

# ---------------------------------------------------------------------------
# C17: dead-declaration scan (reporting-only)
#
# Numbering note: the review's own text calls this check "C16", which collides
# with this file's C16 (the environment-linter batch above). The delegation's
# mapping supersedes the review's label: C17 = D-16 (this check), C18 = E-13
# (paragraph duplication, below).
#
# For each declaration in non-Boneyard FormalSystem/**/*.lean, the BASE
# identifier (the last dot-segment of its name -- e.g. `c0` for `Chronicle.c0`,
# matching how dot notation and an `open` namespace actually reference it) is
# tokenised and counted across every `.lean` file in FormalSystem/ and Tests/
# plus every `.md` file in the repo (excluding .git/.lake/specs/Boneyard/
# build/__pycache__, the same scope C5 already uses for markdown). A
# declaration whose base identifier occurs nowhere else -- not even on another
# line of its own file -- is reported as a candidate dead declaration.
#
# This is reporting-only and deliberately approximate, same spirit as C16's
# dupNamespace check: it is blind to attribute/simp-set-driven indirect usage
# (a theorem tagged `@[formula_unfold]` and consumed only via `simp only
# [formula_unfold]` elsewhere is textually "dead" by this scan but is not
# actually unused), to `to_additive`-generated names, and to same-named
# declarations in different namespaces (a shared base name like `mk` or
# `toString` will never register as dead, which is the safe direction of
# error for a census that must never gate). No ENFORCE_C17 flag -- reporting-
# only per the delegation, and an unused enforcement flag invites a later
# unreviewed flip.
# ---------------------------------------------------------------------------
python3 - <<'PYEOF'
import os, re

def live_lean_files(base):
    out = []
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != "Boneyard"]
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return sorted(out)

def prose_files():
    out = []
    for root, dirs, files in os.walk("."):
        dirs[:] = [d for d in dirs
                   if d not in (".git", ".lake", "specs", "Boneyard", "build", "__pycache__")]
        for f in files:
            if f.endswith(".md"):
                out.append(os.path.relpath(os.path.join(root, f), "."))
    return sorted(out)

decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|mutual\s+)*"
    r"(structure|inductive|def|abbrev|theorem|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
token_re = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

lean_files = live_lean_files("FormalSystem")
declarations = []
for path in lean_files:
    try:
        lines = open(path, encoding="utf-8", errors="replace").readlines()
    except OSError:
        continue
    for i, raw in enumerate(lines, 1):
        m = decl_re.match(raw.strip())
        if m:
            declarations.append((m.group(2).split(".")[-1], path, i))

# Tests/ is not part of C17's declaration scope but IS a legitimate reference
# site (tests routinely call library declarations by name), so it is included
# in the occurrence corpus -- excluding it would misreport every
# test-only-referenced declaration as dead.
occurrence_files = list(lean_files) + prose_files()
for root, dirs, files in os.walk("Tests"):
    for f in files:
        if f.endswith(".lean"):
            occurrence_files.append(os.path.join(root, f))

occurrences = {}
for path in occurrence_files:
    try:
        lines = open(path, encoding="utf-8", errors="replace").readlines()
    except OSError:
        continue
    for i, line in enumerate(lines, 1):
        for tok in set(token_re.findall(line)):
            occurrences.setdefault(tok, set()).add((path, i))

dead = []
for base, decl_file, decl_line in declarations:
    other = occurrences.get(base, set()) - {(decl_file, decl_line)}
    if not other:
        dead.append((base, decl_file, decl_line))

if not dead:
    print("PASS  C17  zero dead declaration(s) (base-identifier token scan)")
else:
    print(f"INFO  C17  {len(dead)} declaration(s) with zero other occurrences (dead-declaration scan, approximate; never affects FAILURES)")
    for base, f, l in dead[:20]:
        print(f"            {f}:{l}: {base}")
    if len(dead) > 20:
        print(f"            ... and {len(dead) - 20} more")
PYEOF
echo

# ---------------------------------------------------------------------------
# C18: paragraph duplication across the top-level READMEs (reporting-only)
#
# D-16/E-13's "C16" label collision note above applies to this check too --
# C18 is the delegation's mapping for E-13.
#
# Scope (confirmed to exist at implementation time, per the Scope Hypothesis):
# README.md, FormalSystem/README.md, FormalSystem/Metalogic/README.md, and
# FormalSystem/Metalogic.lean (an aggregator whose presence C8 governs).
# Paragraphs (blank-line-delimited blocks) are whitespace-normalised (all
# runs of whitespace, including newlines, collapsed to a single space) and
# pooled across all four files; any normalised paragraph appearing more than
# once -- within one file or across files -- is reported. Markdown headers
# and horizontal rules are excluded (they are structure, not prose), and
# paragraphs under 40 normalised characters are excluded to keep the census
# aimed at substantial copy-paste duplication rather than short, legitimately
# repeated phrases. No ENFORCE_C18 flag -- reporting-only per the delegation.
# ---------------------------------------------------------------------------
python3 - <<'PYEOF'
import re

FILES = [
    "README.md",
    "FormalSystem/README.md",
    "FormalSystem/Metalogic/README.md",
    "FormalSystem/Metalogic.lean",
]

def paragraphs(path):
    try:
        text = open(path, encoding="utf-8", errors="replace").read()
    except OSError:
        return []
    paras, cur, start = [], [], None
    for i, line in enumerate(text.split("\n"), 1):
        if line.strip() == "":
            if cur:
                paras.append((start, "\n".join(cur)))
                cur, start = [], None
        else:
            if start is None:
                start = i
            cur.append(line)
    if cur:
        paras.append((start, "\n".join(cur)))
    return paras

def normalize(p):
    return re.sub(r"\s+", " ", p).strip()

occ = {}
for path in FILES:
    for lineno, raw in paragraphs(path):
        norm = normalize(raw)
        if len(norm) < 40:
            continue
        if re.match(r"^#{1,6}\s", norm) or re.match(r"^[-*_]{3,}$", norm):
            continue
        occ.setdefault(norm, []).append((path, lineno))

dups = [(norm, locs) for norm, locs in occ.items() if len(locs) > 1]
if not dups:
    print("PASS  C18  zero duplicated paragraph(s) across the four top-level READMEs")
else:
    print(f"INFO  C18  {len(dups)} duplicated paragraph(s) across the four top-level READMEs (never affects FAILURES)")
    for norm, locs in dups[:20]:
        loc_str = ", ".join(f"{f}:{l}" for f, l in locs)
        print(f"            {loc_str}: {norm[:80]!r}")
    if len(dups) > 20:
        print(f"            ... and {len(dups) - 20} more")
PYEOF
echo

# ---------------------------------------------------------------------------
# C19: docstring-coverage floor (reporting-only)
#
# Declaration-shaped lines (theorem|lemma|def|structure|inductive|class|abbrev|
# instance) in non-Boneyard FormalSystem/**/*.lean. `lemma` is G-12's one
# deliberate addition to the review's own keyword list. The baseline is G-12's
# heuristic, not D-15's 91.8% "core scope" figure -- G-12's is the only one with
# a named, re-runnable method (see this task's plan Overview for the full
# rationale); D-15's baseline is explicitly NOT used here.
#
# TWO figures are computed and both are reported, so a future reader can see
# that the number moved because the definition of "documented" was widened, not
# because coverage itself changed:
#
#   (i)  UNREFINED (G-12 exactly as specified): a declaration counts as
#        documented iff a `/-- ... -/` doc comment ends within the three lines
#        immediately above it. Measured 89.37% (10427 total, 1108 undocumented)
#        -- under the 90% floor.
#   (ii) REFINED (this check's reported figure): (i), OR the declaration falls
#        within the scope of the nearest preceding `/-! ... -/` section
#        comment. That scope begins immediately after the section comment's
#        own closing `-/` and ends at the EARLIEST of: another `/-!` comment
#        opening, a `namespace`/`section`/`end` command, a declaration that is
#        itself (i)-documented (the author explicitly labelled a new unit, so
#        the ambient section's credit ends there), or end of file. Measured
#        92.32% (9626 documented) -- clears the floor.
#
# The refinement was authorized (not assumed) after the unrefined figure was
# found under 90%: this blind spot was already documented as a KNOWN, ANTICIPATED
# limitation of G-12's heuristic ("under-reports coverage for declarations
# documented by an enclosing /-! -/ section comment") before this check existed,
# not a new discovery invented to clear the floor. It was applied ONCE as a
# single, precisely-specified rule and measured once -- not iterated toward a
# target. Verified in both directions before adoption: (a) manually inspecting 8
# of the ORIGINAL undocumented hits confirmed they were genuinely covered by an
# enclosing section, not actually undocumented; (b) manually inspecting several
# NEWLY-credited hits after a first draft of the rule found real over-crediting
# (a section header 664 lines away crediting an unrelated theorem deep in an
# 11000-line file with no intervening boundary) -- the "ends at the next
# (i)-documented declaration too" clause was added specifically to close that
# gap, and the largest remaining credited gap (241 lines, in
# WeakCanonical/GroupModel/MonoDiscrete.lean) was re-checked and found genuine:
# the section header explicitly names every theorem in the batch it covers.
#
# Per-keyword rates worth carrying into a documentation follow-up task
# regardless of the aggregate clearing the floor: class 16.3%, instance 57.6%,
# lemma 55.6% (all measured against the unrefined figures; these three
# categories are real, small-sample documentation gaps, not artifacts of either
# heuristic).
#
# Reporting-only: never increments FAILURES, no ENFORCE_C19 flag. No build
# invocation; runs under --no-build like C17/C18.
# ---------------------------------------------------------------------------
python3 - <<'PYEOF'
import os, re

def live_lean_files(base):
    out = []
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != "Boneyard"]
        for f in files:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return sorted(out)

decl_re = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+|mutual\s+)*"
    r"(theorem|lemma|def|structure|inductive|class|abbrev|instance)\s+[A-Za-z_]"
)
boundary_re = re.compile(r"^(namespace|section|end)\b")

total = 0
documented_unrefined = 0
documented_refined = 0

for path in live_lean_files("FormalSystem"):
    text = open(path, encoding="utf-8", errors="replace").read()
    lines = text.split("\n")
    n = len(lines)

    doc_ends = set()
    for m in re.finditer(r"/--.*?-/", text, re.DOTALL):
        doc_ends.add(text.count("\n", 0, m.end()) + 1)

    section_end_lines = set()
    for m in re.finditer(r"/-!.*?-/", text, re.DOTALL):
        section_end_lines.add(text.count("\n", 0, m.end()) + 1)

    decl_lines = {}
    for i, raw in enumerate(lines, 1):
        if decl_re.match(raw.strip()):
            decl_lines[i] = any((i - k) in doc_ends for k in (1, 2, 3))

    active = False
    for i in range(1, n + 1):
        line = lines[i - 1].strip()
        if i in section_end_lines:
            active = True
            continue
        if boundary_re.match(line):
            active = False
        if i in decl_lines:
            total += 1
            if decl_lines[i]:
                documented_unrefined += 1
                documented_refined += 1
                active = False
            elif active:
                documented_refined += 1

pct_unrefined = 100.0 * documented_unrefined / total if total else 0.0
pct_refined = 100.0 * documented_refined / total if total else 0.0
FLOOR = 90.0

print(f"INFO  C19  docstring coverage (unrefined G-12): {documented_unrefined}/{total} = {pct_unrefined:.2f}%")
if pct_refined >= FLOOR:
    print(f"PASS  C19  docstring coverage (refined, /-! section credit): {documented_refined}/{total} = {pct_refined:.2f}% (floor: {FLOOR:.0f}%)")
else:
    print(f"TODO  C19  docstring coverage (refined, /-! section credit): {documented_refined}/{total} = {pct_refined:.2f}% -- below the {FLOOR:.0f}% floor (never affects FAILURES)")
PYEOF
echo

# ---------------------------------------------------------------------------
# C9-DOCS: task-number citations under docs/
#
# `.claude/rules/no-task-references-in-deliverables.md` binds docs/ exactly as it
# binds FormalSystem/, but docs/ does not yet satisfy it. Following this script's
# own documented pattern for an end-state invariant the tree has not reached, the
# computation runs from the outset and is REPORTED at every gate, while only the
# flag controls whether it affects the exit code.
#
# Do not silently omit this check to keep the gate quiet, and do not flip the flag
# to 0 once it is 1. Clear the citations instead.
# ---------------------------------------------------------------------------
DOCS_TASK_REFS=$(grep -rniE --include='*.md' \
  '\b(tasks?[[:space:]]+#?[0-9]+|task-[0-9]+)\b' docs 2>/dev/null || true)
DOCS_TASK_REF_COUNT=$(printf '%s' "$DOCS_TASK_REFS" | grep -c . || true)
if [ "$DOCS_TASK_REF_COUNT" -eq 0 ]; then
  pass C9D "zero task-number citations under docs/"
else
  MSG="$DOCS_TASK_REF_COUNT task-number citation(s) under docs/ (use a durable anchor instead)"
  if [ "$ENFORCE_C9_DOCS" -eq 1 ]; then fail C9D "$MSG"; else soft C9D "$MSG (not yet enforced)"; fi
  printf '%s\n' "$DOCS_TASK_REFS" | cut -d: -f1 | sort | uniq -c | sort -rn | head -5 \
    | while IFS= read -r l; do note "$l"; done
  note "set ENFORCE_C9_DOCS=1 to make this exit-code-affecting once the citations are cleared"
fi
echo

# ---------------------------------------------------------------------------
echo "==========================================================="
if [ "$FAILURES" -eq 0 ]; then
  echo "ALL CHECKS PASSED"
  exit 0
else
  echo "$FAILURES CHECK GROUP(S) FAILED"
  exit 1
fi
