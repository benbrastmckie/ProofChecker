# The 547/548 boundary, and what 547 deliberately left alone

## What 547 did

- Renamed the historical system names in **prose only** — comments, docstrings, READMEs, docs and
  the typst sync map. `TM⁺_f → TM⁺_z`, `TM⁺_c` and `TM⁺_dc → TM⁺_r`, `TM_f → TM_z`, `TM_c` and
  `TM_dc → TM_r`, `BX_f → BX_z`, `BX_c → BX_r`. No Lean identifier changed.
- **De-quoted four sites** that quoted the paper's deleted "successor-Archimedean discrete class"
  sentence: `Metalogic/Conservativity.lean`, `Semantics/FrameClassValidity.lean`, and *two* in
  `Semantics/FrameProperty.lean` (the module header and the `TaskFrame.IsZTime` docstring — the
  second was missed by the census grep because its markdown emphasis splits the token as
  ``**BX**`_f```).
- Retired the claims the live paper has resolved: the "`TM⁺_c` gap" argument, the "the paper bases
  its complete-order extension on the single axiom CO" note, the "correcting the paper means
  switching the basis" C4 note, and the "open question" about density axioms in `BX_c`.
- Wrote the canonical two-families mapping into `FormalSystem/Metalogic/Conservativity.lean`'s
  module docstring and a prose-adapted version into `docs/README.md`, with a one-line pointer at
  `FormalSystem/BaseLanguage/Axioms.lean`'s system table.

## What 547 deliberately left for the anchor re-pinning follow-up

**Every anchor label, and every row of `specs/paper-definitions-of-record.md`.** The record still
pins `def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c`; the paper has relabelled these to `def:BX-z`,
`def:BX-d`, `def:BX-r`. C15 resolves citations against the *record*, not the paper, so citing the
paper's live labels before the record is re-pinned would turn C15 red. 547's new prose therefore
cites the record's labels and says so inline. The follow-up owns:

1. Re-pinning the record's manifest rows to the paper's `def:BX-*` labels and content hashes.
2. Retargeting the label citations in live scope once the record accepts them.

**Do not re-litigate `FrameClassValidity.lean`.** Both tasks name that file. 547 owns the *system
names* and the de-quotation there; the follow-up owns the *anchor label*. The edits do not overlap.

**`typst/FormalFoundations.typ`** still carries `$"BX"_f$` and `$op("TM")^+_f$` at lines 508-509
and a Hölder sentence at 558. It is a verbatim transcription of the paper environment the record
pins, so renaming it independently would desynchronize it from the record. It belongs with the
re-pin, not with 547's prose sweep. (It is also invisible to the completeness grep, whose regex
does not match typst subscript syntax.)

## Task-546 residue recorded but not fixed

`FrameClass.Dedekind` / `FrameClass.Discrete` still appear at seven sites outside the paragraphs
547 rewrote:

- `FormalSystem/README.md:174`
- `FormalSystem/README.md:182`
- `FormalSystem/ProofSystem/README.md:49`
- `FormalSystem/Theorems/README.md:17`
- `FormalSystem/Semantics/Correspondence/README.md:20`
- `FormalSystem/Metalogic/Decidability/BiLasso/README.md:161`
- `docs/development/NAMING_CONVENTION_DEVIATION.md:232`

The plan anticipated five; `FormalSystem/README.md:174` and `:182` are the two it did not list.
The three co-located sites inside the rewritten `FormalSystem/README.md` paragraph were fixed.

## The divergence from the task description, and how it was resolved

The task description asserts a live footnote in the Logic subsection stating the Past/Future axiom
set and its incompleteness results. **That footnote is not live.** `possible_worlds.tex:1331-1341`
is commented out in full, with the author's own editorial note that it stays commented "until the
BimodalLogic repository establishes that the Past/Future language admits no complete
axiomatization".

The plan surfaced this as a non-blocking `user_decision` and recommended: say the BaseLanguage
systems have no paper name today, plus one sentence noting the commented-out footnote. That is
what was written. If the author un-comments the footnote, the mapping paragraph's second bullet
should be revised to cite it.

## Build-gate finding for any follow-up in this tree

`lake build FormalSystem` is **not** sufficient before `scripts/check-module-invariants.sh`.
`FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound` lies outside that target's
closure, so the scoped build reports success while `MintBound.olean` is absent, and C1, C2, C14
and C16 then all fail on the missing object file rather than on anything substantive. Run a full
`lake build` before the invariants gate.
