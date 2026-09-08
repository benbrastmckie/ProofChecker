#!/usr/bin/env python3
"""Split `IsTotal` occurrences into code lines and docstring/comment lines.

Evidence script for task 553, report section 6.1. Run from the repository root:

    python3 specs/553_decide_convex_history_layer_collapse/probes/scan-istotal-code-vs-doc.py

Also reports the dependent-`.states` application count, partitioned by whether the file
mentions `ConvexHistory` (convex layer, in scope for a retarget) or does not
(`PartialHistory`-only, out of scope by the task's own constraint).
"""
import glob, re

code = doc = 0
code_files = set()
conv = part = 0
per_file = []

for f in sorted(glob.glob('FormalSystem/**/*.lean', recursive=True)):
    if '/Boneyard/' in f:
        continue
    src = open(f).read()

    in_doc = False
    for line in src.split('\n'):
        st = line.strip()
        if st.startswith('/-'):
            in_doc = True
        if 'IsTotal' in line:
            if in_doc or st.startswith('--'):
                doc += 1
            else:
                code += 1
                code_files.add(f)
        if '-/' in line:
            in_doc = False

    n = len(re.findall(r"\.states [A-Za-z0-9_']+ [A-Za-z0-9_']+", src))
    if n:
        if 'ConvexHistory' in src:
            conv += n
        else:
            part += n
        per_file.append((n, f, 'ConvexHistory' in src))

print(f"IsTotal in code:        {code} lines across {len(code_files)} files")
print(f"IsTotal in docs/comments: {doc} lines")
print()
print(f"dependent .states applications, convex layer:        {conv}")
print(f"dependent .states applications, PartialHistory only: {part}")
print(f"dependent .states applications, total:               {conv + part}")
print()
for n, f, is_conv in sorted(per_file, reverse=True)[:14]:
    print(f"  {n:4d}  {'CONV' if is_conv else 'PART'}  {f}")
