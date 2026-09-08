# Phase 1 handoff (task 548)

- Done: 9 dangling manifest rows retired (prose entries retained + marked DANGLING), 9 DANGLING
  rows added to KNOWN-ANCHORS, 3 new prose entries + manifest rows for `def:BX-z/-d/-r` with
  freshly `--resolve`d hashes (385f73e8…, 555db844…, b35751c7… — identical to the report's).
- State: `check-paper-definitions.sh` reports 0 dangling, 15 drifted (expected), exit 1.
- Next: Phase 2 — re-quote and re-hash the 15 drifted entries; do NOT touch the sentinels.
- Deviations: none.
