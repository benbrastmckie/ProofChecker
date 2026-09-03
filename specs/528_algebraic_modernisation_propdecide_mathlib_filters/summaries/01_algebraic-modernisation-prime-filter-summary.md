# Implementation Summary: Algebraic/ Modernisation (propDecide, Mathlib Prime Filters)

- **Task**: 528
- **Status**: TBD
- **Started**: TBD
- **Completed**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Plan**: `plans/03_algebraic-modernisation-prime-filter.md` (v3), all 7 phases executed
- **Session**: sess_1788465505_51370d
- **Date**: 2026-09-03
- **Outcome**: implemented — 6 phases `[COMPLETED]`, Phase 2 `[COMPLETED WITH EXCLUSIONS]`
  (Decision D2 accept bar met, stretch bar not met; see below)

## What changed

| Phase | Files | Result |
|-------|-------|--------|
| 1 | `FormalSystem/Metalogic/Algebraic/BooleanStructure.lean` | `import FormalSystem.Automation.Tactics.PropDecide` (no cycle; full build green in isolation); the 10 closed-tautology `*_quot` lemmas rewritten to `induction … using Quotient.ind with \| _ φ =>` / `change Derives …` / `unfold Derives` / `propDecide`. The 110-line `le_sup_inf_quot` is now 8 lines. Metric 286 → 139. |
| 2 | same | `sup_le_quot` (39 → 8) and `le_inf_quot` (13 → 8) via a `propDecide`-closed tautology + `Combinators.pairing` + `DerivationTree.modus_ponens`; `le_trans_quot` left as is (already minimal). Metric 139 → **105**. |
| 3 | `Tests/BimodalTest/Metalogic/PropDecideTest.lean` | Wrong "out of scope" De Morgan docstring replaced; De Morgan and distributivity `example`s added (both close). |
| 4 | `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` | `fold_le_of_derives` restated over `((L.map toQuot : List _) : Multiset _).inf`; `fold_from_x` gone; single call site's helper `h_meet_in_U` restated over `Multiset.inf` (double induction → single). One atomic commit. |
| 5 | `FormalSystem/ForMathlib/Order/PFilter.lean` (new, 250 lines), `FormalSystem/ForMathlib.lean` (new), `FormalSystem/FormalSystem.lean`, `FormalSystem/README.md`, `CLAUDE.md` | Report 02 Appendix A transcribed verbatim in namespace `Order.PFilter` (`IsProper`, `IsMaximal`, `*_iff_dual`, Boolean section, `Order.PrimeFilter`), plus the optional `DistribLattice.prime_filter_of_disjoint_filter_ideal` (import cost measured as nil; upstream TODO confirmed still open on master). Root import added to `FormalSystem/FormalSystem.lean`; C8 sibling aggregator created; four doc enumerations gained a row. |
| 6 | `FormalSystem/Metalogic/Algebraic/UltrafilterMCS.lean` | Ported onto `Order.PrimeFilter LindenbaumAlg`: `toQuot_mem_mcsToSet_iff` (3-line dedup), `mcsToSet_isPFilter` / `mcsToPFilter` / `IsProper` + `IsPrime` instances / `mcsToUltrafilter`, `ultrafilterToSet(_mcs)` by textual substitution, **`SetMaximalConsistent.ultrafilterEquiv`** at the corrected type, `ultrafilter_correspondence` as its corollary, `ultrafilter_neg_iff(')` one-liners; bespoke `structure Ultrafilter` and its 6 satellite declarations plus both round-trip theorems deleted. File 1,071 → **801** lines. |
| 7 | `FormalSystem/Metalogic/Algebraic/README.md` | Counts, API sketch, `ForMathlib` flowchart node, new "Design decisions" subsection (D1 rationale, two dualities, `IsPrime` suffices, no bridge lemma, `abbrev` trade-off, Chagrov–Zakharyaschev §8.2 Thm 8.14 citation, Mathlib-coverage note with re-verified anchors, `propDecide` layering, documented `PFilter` lattice gap), `*Last verified: 2026-09-03*`. `Algebraic.lean` needed no edit (names only the module). |

32 commits on `main` from `f0a75a3f0` (phase 1.1) through the Phase 7 close, each taken on a green build.

## Acceptance criteria

1. **`*_quot` line total**: `lemmas: 15 total_body_lines: 105` (baseline 286). D2: accept bar
   (≤ 115) met; stretch (< 100) not met. Note for the D2 ruling: the plan's command counts the one
   blank line following each lemma; the plan's prose definition ("declaration line through last proof
   line") gives 90. Recorded as 105 because the plan names the command as the metric.
2. **No `Ultrafilter` shadow**: both greps empty; first disjunct satisfied outright.
3. **`ultrafilterEquiv`**: `#check` gives `{Γ // SetMaximalConsistent Γ} ≃ Order.PrimeFilter LindenbaumAlg`;
   `#print axioms` = `[propext, Classical.choice, Quot.sound]`; `ultrafilter_correspondence` is
   `⟨e, e.symm, e.left_inv, e.right_inv⟩`.
4. **`fold_le_of_derives`** over `Multiset.inf`; `grep -c fold_from_x` = 0.
5. **`lake build` green**; `scripts/check-module-invariants.sh` all-pass at every phase boundary
   (8 full runs: baseline, after Phases 1–7); C2 baseline unchanged every time. C6: `ForMathlib` reachable
   (476 reachable modules, not in the manifest); C8 green with the sibling aggregator; C11 green.
6. **Zero new sorries**: C3 green; `lean-sorry-census.sh` on the touched trees: `sorry_count: 0`.
7. **`UltrafilterMCS.lean` shrinks**: 1,071 → 801 (report 02 projected ~780; the surplus is docstrings
   on the new declarations).

Live `axiom` declarations: 7 before, 7 after. The vacuous-pattern grep reports one pre-existing hit
(`Examples/TemporalStructures.lean:496`, present in the pre-task baseline, untouched).

## Plan Deviations

- Phase 5, optional `.claude/context/repo/project-overview.md` courtesy edit: **skipped** —
  `.claude/rules/source-store-deploy-boundary.md` forbids hand-authoring under `.claude/**`; the plan
  itself marks the edit non-tracked and optional. Annotated inline on the plan checklist.
- Phase 6, commit granularity: the plan's finer split (Equiv / corollary / `:910-966` as separate
  green commits) is not realisable because `mcsToUltrafilter` keeps its name, so the type change is
  one connected component; it landed as one green commit (6.4) with the deletions in 6.5. No content
  deviation. Recorded in the plan's Phase 6 completion note.
- Phase 6, one statement change recorded (not silent): `ultrafilter_correspondence`'s binder types
  `Ultrafilter LindenbaumAlg` → `PrimeFilter LindenbaumAlg`; leaving the old spelling would have
  silently retargeted Mathlib's `_root_.Ultrafilter` (a filter on `Set LindenbaumAlg`), the exact
  hazard report 02 §2 identified. The existential form is otherwise byte-identical.
- Phase 6, substitution pass: one argument-order swap (`U.mem_of_le h_meet h_le_bot` →
  `PFilter.mem_of_le h_le_bot h_meet`, Mathlib's signature), recorded as a signature-shape
  difference; no tactic added, removed or reordered.

## Findings worth keeping

- `propDecide` needs the goal syntactically `Derivable …`; on the quotient order this is
  `change Derives …; unfold Derives`. A trial also showed `obtain ⟨φ⟩ := a` (rcases quotient
  induction) and `show Derivable _ [] _` work and are one line shorter each — not used, to keep the
  plan's named tactic sequence.
- Report 02's Appendix A/B compiled unchanged against the live tree; the only frictions were the two
  pre-loaded ones.
- `Mathlib.Order.PrimeSeparator`'s import cost is unmeasurable at this scale (1.2–1.3 s either way for
  a one-line file with cached oleans).
