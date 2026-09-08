#!/usr/bin/env python3
"""Count declarations binding a `ConvexHistory` with no `IsTotal` guard.

Evidence script for task 553, report section 2.4. Run from the repository root:

    python3 specs/553_decide_convex_history_layer_collapse/probes/scan-ungated-convex-binders.py

Prints the total and a per-directory breakdown. Excludes FormalSystem/Boneyard/.
A declaration counts when its signature (through the first `:=`) binds a name at type
`ConvexHistory ...`, the declaration body mentions no `IsTotal`, and the signature
mentions no `.HF` (which would be the bundled total form).
"""
import re, glob, collections

res = []
for f in sorted(glob.glob('FormalSystem/**/*.lean', recursive=True)):
    if '/Boneyard/' in f:
        continue
    lines = open(f).read().split('\n')
    decl_start, buf = None, []

    def flush():
        if decl_start is None:
            return
        body = '\n'.join(buf)
        sig = []
        for l in buf:
            sig.append(l)
            if ':=' in l:
                break
        sigtxt = '\n'.join(sig)
        if (re.search(r'[({]\s*\w+\s*:\s*ConvexHistory', sigtxt)
                and 'IsTotal' not in body and '.HF' not in sigtxt):
            res.append((f, decl_start + 1, buf[0].strip()[:100]))

    for i, l in enumerate(lines):
        if re.match(r'^(private |protected |noncomputable |@\[[^\]]*\]\s*)*'
                    r'(theorem|lemma|def|abbrev|instance)\s', l):
            flush(); decl_start, buf = i, [l]
        elif decl_start is not None:
            buf.append(l)
    flush()

print("TOTAL:", len(res))
for k, v in sorted(collections.Counter(f.rsplit('/', 1)[0] for f, _, _ in res).items(),
                   key=lambda x: -x[1]):
    print(f"  {v:4d}  {k}")
