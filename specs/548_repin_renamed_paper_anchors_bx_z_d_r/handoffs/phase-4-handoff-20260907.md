# Phase 4 handoff (task 548)

- Re-labelled def:TMplus-f/-d/-c -> def:BX-z/-d/-r at every live site: 32 lines across 18 files.
- `Conservativity.lean:32-34`'s "the record's re-pin is separate work" sentence rewritten: it now
  states the new labels as pinned and names the old ones as DANGLING.
- `typst/sync-check-whitelist.txt`: two stale entries retired (nothing cites them);
  typst-sync-check Check 1 unchanged at 4 pre-existing unrelated violations.
- Verified: `grep -rn 'def:TMplus-[fdc]'` returns nothing outside specs/; full `lake build`
  completed successfully (2592 jobs); standalone C15 reproduction reports no unresolved anchor
  (known=74, cited=63).
- Next: Phase 5 prose corrections. Sites identified:
  * "def:BX-z's Hölder narrowing to ℤ-time" (6): LexIntWitness.lean:20, Semantics.lean:68,
    Indicator.lean:52, Correspondence/README.md:22, Validity.lean:603, BLValidity.lean:215-216;
    plus README.md:275 "Hölder-to-ℤ class", FrameProperty.lean:28/42/58/131/133/159,
    FrameClassValidity.lean:34/94.
  * Already-correct sites (leave alone): FrameProperty.lean:136, Conservativity.lean:164-176,
    Z1Countermodel.lean:31-34 already say the Hölder route is an earlier revision.
  * Dangling-citation honesty: TaskFrame.lean cites def:directed as live; typst cites
    def:BLplus-semantics / def:directed / thm:BLplus-PastFuture; Formula.lean cites TMP-CO.
  * "strictly stronger" ball-space claim now overstates the paper: README.md:81,
    TaskFrame.lean:402.
