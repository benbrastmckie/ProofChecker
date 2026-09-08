# Phase 2 handoff (task 548)

- Done: all 15 drifted entries re-quoted + re-hashed (fence, sha line, manifest row), every hash
  re-derived via `--resolve`. Live hashes matched the research report's for all 15.
- `cor:saturation-finite`: prose entry still carried the pre-rename `cor:spherical-finite`
  *Spherical* text; refreshed, heading re-keyed, and the `Cthm` -> `Lthm` environment change
  recorded. Manifest `kind` stays `env` (resolver reads the env off the \label line).
- `def:frame`: commentary extended with the two in-block changes (def:directed folded inline,
  ball-space footnote softened "strictly stronger" -> "at least as strong as").
- State: `check-paper-definitions.sh` = case-(b) notice pass, exit 0, sentinels untouched.
- Discovered scope for Phase 5 (beyond the plan's list): in-tree prose citing the newly-DANGLING
  anchors must say so at the citation site (record convention) — `def:directed` in
  `Semantics/TaskFrame.lean`, plus the BL^+ cluster and `TMP-CO`; and `README.md:81` +
  `TaskFrame.lean:402` assert *strictly stronger* where the paper now says *at least as strong*.
- Next: Phase 3 — re-pin FILE_CHECKSUM/PINNED_COMMIT/LINE_COUNT, write the wave narrative.
