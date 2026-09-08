# Phase 5 Handoff — Task 541

- **Next action**: Phase 6 — the mandated negative test. Remove the
  `import FormalSystem.Init` line from `FormalSystem/Automation/NormalizationAttr.lean`,
  rebuild, observe `FAIL C24` + non-zero script exit, restore, rebuild, observe `PASS C24`.
- **State**: C24 wired at all four sites (header `# Checks:` row, `--no-build` usage line,
  `ENFORCE_C24=${ENFORCE_C24:-1}` beside `ENFORCE_C23`, and the `RUN_BUILD`-guarded block on the
  C16 template, placed between C22 and C9D so the identifiers stay ascending).
  `docs/development/MODULE_INVARIANTS.md` carries the C24 row and a paragraph recording the
  negative-test mandate beside C15's. `--no-build` -> `INFO C24 … skipped`, ALL CHECKS PASSED.
  Build mode -> `PASS C24`, ALL CHECKS PASSED, exit 0.
- **Key decisions**: `grep -c C24` returned 0 before authoring, so C24 was confirmed free.
- **Deviations**: `scripts/module-invariants-manifest.txt` needed its `FormalSystem.Init` line
  deleted — the root is no longer unreachable, and C6 fails on a manifest entry naming a
  reachable module. The manifest's own comment had pre-authorised exactly that deletion.
