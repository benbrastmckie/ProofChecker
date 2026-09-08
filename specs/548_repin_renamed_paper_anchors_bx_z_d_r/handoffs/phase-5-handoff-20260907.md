# Phase 5 handoff (task 548)

- Hölder attribution corrected at 7 sites (6 Lean/md + README.md:275); the narrowing is now
  attributed to def:BX-z citing prop:archimedean, with the Hölder step described as the paper's
  earlier route where the parenthetical explains the predicate's name.
- prop:archimedean LIVE-UNPINNED row added to the record (recorded as pen-and-paper, not verified).
- Verbatim old-text quotation found in typst/FormalFoundations.typ (not FrameClassValidity.lean):
  refreshed + naming-provenance remark added. Document-wide f/d/c -> z/d/r rename NOT done
  (~57 sites) -> follow-up.
- Dangling-citation honesty pass done for def:directed, the BL^+ cluster, and TMP-CO.
- "strictly stronger" ball-space claim corrected (README.md:81, TaskFrame.lean).
- docs/theorem-index.md naming rows refreshed (TM/BL without superscripts; BL name collision).
- Verified: full `lake build` clean (2596 jobs, 0 errors); C15 reproduction empty (known=75,
  cited=63); typst-sync-check unchanged at 4 pre-existing violations; FormalFoundations.typ
  compiles.
- NOTE: the paper moved on disk again (c3846c1e -> c485a615); check-paper-definitions.sh is now a
  case-(b) notice pass (exit 0, all 43 definitions unchanged) rather than the quiet case-(a).
  Per the record's own convention a case-(b) touch is NOT re-pinned.
- Next: Phase 6 full-gate verification (check-module-invariants.sh, >15 min, backgrounded).
