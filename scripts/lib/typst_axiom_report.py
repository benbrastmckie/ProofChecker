"""Render `#print axioms` output as a typst `axiom-report-table` binding.

Reads the raw `'Name' depends on axioms: [...]` lines from the AX_OUT
environment variable and the display module labels from
`scripts/typst-axiom-report-modules.txt`. Emits the `#let` binding on stdout.

Kept out of `typst-status-counts.sh` as a file rather than a heredoc because the
script already nests three levels of heredoc and a fourth is unreadable.
"""

import os
import re
import sys

MODULES_FILE = os.environ.get(
    "TYPST_AXIOM_MODULES",
    os.path.join("scripts", "typst-axiom-report-modules.txt"),
)

modules = {}
with open(MODULES_FILE, encoding="utf-8") as fh:
    for line in fh:
        line = line.split("#")[0].strip()
        if line:
            name, module = line.split("|", 1)
            modules[name.strip()] = module.strip()

rows = []
for line in os.environ.get("AX_OUT", "").split("\n"):
    m = re.match(r"'([^']+)' depends on axioms: \[(.*)\]", line.strip())
    if not m:
        continue
    name, axioms = m.group(1), m.group(2)
    rows.append((name, modules.get(name, "?"), axioms,
                 "yes" if "sorryAx" in axioms else "no"))

if not rows:
    sys.exit("typst_axiom_report.py: no axiom records parsed from AX_OUT")

print("#let axiom-report-table = (")
for name, module, axioms, sorryax in rows:
    print('  ("%s", "%s", "%s", "%s"),' % (name, module, axioms, sorryax))
print(")")
