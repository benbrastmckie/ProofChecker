---
next_project_number: 554
---

# TODO

## Task Order

*Updated 2026-09-07. Generated from state.json dependency graph.*

**Dependency Waves**:
| Wave | Tasks | Blocked by | Topics |
|------|-------|------------|--------|
| 1 | 127,128,193,257,298,464,476,481,502,504,506,534,535,540,541,542,544,545,547,549,551 | -- | algebraic-representation, automation, dataset-enhancement, ... |
| 2 | 178,231,282,296,465,497,537,548,550 | 193,298,464,502,535,547,549 | algebraic-representation, dataset-enhancement, decidability, ... |
| 3 | 219,428,498,499,500,552 | 231,465,497,548 | algebraic-representation, dataset-enhancement, decidability, paper-refactor |
| 4 | 125,429,543,553 | 428,498,499,500,552 | algebraic-representation, decidability, metalogic, paper-refactor |
| 5 | 410,501 | 125,429 | algebraic-representation, decidability |
| 6 | 411 | 410 | decidability |
| 7 | 430 | 411 | decidability |
| 8 | 177,412 | 193,430 | decidability, formula-refactor |
| 9 | 482 | 412 | decidability |

**Grouped by Topic** (indented = depends on parent):

### Algebraic Representation

502 [NOT STARTED] — RESEARCH TASK. Ground the algebraic representation front in the l
  └─ 497 [NOT STARTED] — Bring the Shift-closed Tense S5 Algebra class into live code and 
    └─ 498 [NOT STARTED] — Phase 1 of the Jonsson-Tarski representation: the complex algebra
      └─ 125 [NOT STARTED] — CAPSTONE of the algebraic representation front. Prove the Jonsson
        └─ 501 [NOT STARTED] — Phase 4 of the Jonsson-Tarski representation: extend STSA with th
    └─ 499 [NOT STARTED] — HARD. Phase 2 of the Jonsson-Tarski representation: the ultrafilt
      └─ 125 [NOT STARTED] — CAPSTONE of the algebraic representation front. Prove the Jonsson (see above)
    └─ 500 [NOT STARTED] — RESEARCH TASK. Prevent two parallel representation theorems from 

### Automation

193 [NOT STARTED] — Apply validity-intro and truth-simp macros to the soundness layer

### Dataset Enhancement

257 [BLOCKED] — Complete the Hugging Face Hub migration for large dataset storage
298 [PARTIAL] — Fix c7 labeling bug at formula ~13750 that causes unbounded memor
  └─ 231 [NOT STARTED] — Build comprehensive automation so that every dataset regeneration
    └─ 219 [RESEARCHED] — Run bmlogic-bench through multiple LLMs to establish baseline dif
  └─ 282 [PARTIAL] — Flip complexity-9 dataset generation from stratified to exhaustiv
  └─ 296 [PARTIAL] — Re-add the 6 derived binary temporal operators (release, weak_unt

### Decidability

464 [NOT STARTED] — Design and land `gapPotential`, the density coordinate of the ter
  └─ 465 [NOT STARTED] — Complete the terminus restatement family at the repaired residual
    └─ 428 [BLOCKED] — Engine totality at a quantified branch budget. Owns obstruction O
      └─ 429 [NOT STARTED] — Repair the truth-lemma side conditions. Owns obstructions O2 and 
        └─ 410 [PLANNED] — Track B part 1 for the TM tableau decidability program (parent: t
          └─ 411 [NOT STARTED] — Track B part 2 for the TM tableau decidability program (parent: t
            └─ 430 [NOT STARTED] — The semantic lift and the Track A assembly. Owns obstruction O4 o
              └─ 412 [NOT STARTED] — Track B finish for the TM tableau decidability program (parent: t
                └─ 482 [NOT STARTED] — CLASSIFICATION: OPEN MATHEMATICS, multi-month. This MUST NOT be r
476 [NOT STARTED] — THE BOX-FAITHFUL SMALL-MODEL THEOREM.
481 [BLOCKED] — CLASSIFICATION: genuinely open -- the predicate is refuted as sta
549 [IMPLEMENTING] — Trace whether `FormalSystem.Metalogic.Decidability.decide` depend

### Formula Refactor

177 [NOT STARTED] — Update README.md, docs/, and FormalSystem/ module-level docstring
178 [NOT STARTED] — Expand Examples/ with publication-quality demonstrations of the f

### Frame Extensions

127 [NOT STARTED] — Add time addition operator (+) to the bimodal logic TM. φ + ψ is 
128 [NOT STARTED] — Add topological open set (interior) operator for dense and contin

### Literature

504 [NOT STARTED] — Retry acquisition of the standard modal-representation sources th

### Metalogic

535 [RESEARCHED] — RESEARCH TASK -- report and probe files only; no changes to Forma
  └─ 537 [NOT STARTED] — Implement in Lean the honest TM⋆ metatheory that research task 53
543 [NOT STARTED] — Machine-check the principal new results from the MF frame-corresp

### Paper Refactor

547 [NOT STARTED] — Replace the historical extension names TM⁺_f, TM⁺_c, TM⁺_dc, TM_f
  └─ 548 [NOT STARTED] — Re-pin the paper anchors changed by the paper's z/d/r refactor an
    └─ 552 [NOT STARTED] — Rename this repository's semantic history layer so that its
      └─ 553 [NOT STARTED] — RESEARCH TASK, verdict-first --- report and probe files only

### Publication Quality

506 [NOT STARTED] — Fix all outstanding display/layout defects in the compiled typst 
550 [NOT STARTED] — Decompose `MintBound.lean` for publication legibility -- 15,759 l

### Repo Hygiene

551 [NOT STARTED] — Decide the disposition of `FormalSystem/Boneyard/` -- 91,539 line

### Documentation

540 [NOT STARTED] — Close the three declaration categories that sit far below the rep

### Incompleteness

534 [NOT STARTED] — Research and, where feasible, establish in Lean whether the H/G-f
544 [RESEARCHED] — Machine-check the failing half of CEB: no instance of the boxed d
545 [RESEARCHED] — Decide, with machine-checked proof, whether the two H/G-language 

### Infrastructure

541 [NOT STARTED] — Make the Init.lean import invariant enforceable by adopting Forma
542 [NOT STARTED] — Triage the dead-declaration census that C17 produces, separating 

## Tasks

### 553. Decide convex history layer collapse
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: paper-refactor
- **Dependencies**: Task 552

**Description**: RESEARCH TASK, verdict-first --- report and probe files only; no change to `FormalSystem/` beyond probes. Decide whether the convex-history layer should exist in this repository at all, and, if it should not, specify how to collapse it. Deliver a reasoned recommendation with the evidence needed to act on it. Implementation, if the recommendation is accepted, is a follow-up task.

THE QUESTION. Once the history-vocabulary rename has landed, `ConvexHistory` is the evaluation index of `TruthAt` and `IsTotal` is carried as a side hypothesis at every validity, soundness, completeness and decidability site. The paper evaluates sentences only at world histories --- only at total ones. The alternative is to make the evaluation index total by construction, `structure WorldHistory (F : TaskFrame) where states : F.Duration -> F.WorldState ; respects_task : forall s t, F.TaskRel (states s) (t - s) (states t)`, so that `WorldHistory F` and `F.HF` coincide definitionally exactly as they do in the paper, with `ConvexHistory` surviving only for material that genuinely needs a bounded domain. That would make the repository's central type mean the paper's central notion with no side condition and no bridging apparatus. It would also foreclose things. Decide which way it goes.

EVIDENCE ALREADY GATHERED --- verify it, do not re-derive it from scratch, and report any of it that turns out to be wrong.
1. The convex layer looks vestigial. Every concrete construction with a non-total domain in the repository lives at the `PartialHistory` layer: `Semantics/Extension/Extension.lean:227` (`point`), `Semantics/Extension/Admissible.lean:239` (`adjoinDomain`), `Semantics/PartialHistoryOrder.lean:126` and `:193`. The only convex-layer constructions whose `domain` field is anything other than `fun _ => True` are the two generic transports --- `timeShift` (`Semantics/WorldHistory.lean:305`) and the two directions of `Semantics/IntTransfer.lean` (`:199`, `:255`) --- and those merely carry through whatever domain they were handed. Every CONCRETE convex-layer value built anywhere in the tree is total.
2. The `convex` field is discharged 22 times and consumed essentially never. A grep for `.convex` applied to a history value returns only those transports and their re-establishment lemmas; the remaining hits belong to unrelated `convex` fields in `Metalogic/WeakCanonical/DenseModelSurgery/` and `Metalogic/WeakCanonical/RealModel/`.
3. The generality has a real price. `IsTotal` occurs on 322 lines. `TruthAt`'s atom clause carries `exists (ht : tau.domain t)` (`Semantics/Truth.lean:234`), and there are roughly 85 dependent `.states t ht` applications; `.domain` occurs on 198 lines. The bundled/predicate split exists only to manage the same thing: `TaskFrame.HF.val`/`.property`, `SemanticConsequence.of_forall`/`.apply`, `SemanticConsequenceIn.of_forall_total`/`.apply_total`, `Valid.of_forall_total`/`.apply`, and `validOn_iff_total` are all bridges between the two spellings of one notion.
4. Nothing in the repository formalizes the paper's presheaf appendix --- the behavior presheaf Beh(F), the interval site, the gluing lemma, the path-category correspondence. "presheaf" occurs 0 times in `FormalSystem/`. That appendix is the paper's principal consumer of bounded convex histories, so the strongest argument for keeping the layer is prospective rather than actual, and its weight depends on whether that appendix is ever going to be formalized here.

WHAT THIS TASK MUST SETTLE.
(a) Is the vestigial finding correct AND complete? Hunt specifically for any site that needs a convex, non-total, non-partial history: check `Semantics/StarPasting.lean`, `Semantics/ShiftSet.lean`, `Semantics/Ultraproduct/`, `Metalogic/Decidability/BiLasso/`, `Metalogic/WeakCanonical/`, and any `Boneyard/` subtree that a live task might revive. One genuine consumer changes the answer.
(b) What actually happens to `TruthAt` at a total index? The atom clause loses its `exists ht`; the box clause loses its `sigma.IsTotal ->` guard; the `untl` and `snce` clauses already quantify over all of `D` with no domain guard (`Semantics/Truth.lean:238-241`) rather than over `tau.domain`. Establish what those tense clauses currently MEAN at a non-total index --- an atom outside the domain is false rather than ill-formed, so the clauses are well-defined, but that is not the paper's footnoted alternative semantics either. If the current reading at a bounded index is degenerate rather than intended, say so plainly: that is an argument for collapsing on correctness grounds and not merely on tidiness, and it should be weighed as such.
(c) Cost the change honestly, by file and by obligation class, separating mechanical rewrites (`tau.states t ht` -> `tau.states t`, dropped `IsTotal` binders) from proofs that must genuinely be rethought. Compare against the counterfactual of doing nothing. Note that the change is expected to REMOVE code rather than add it, so volume rather than depth is the likely difficulty --- confirm or refute that expectation with measurements.
(d) Weigh what is lost. Collapsing forecloses evaluating at a bounded convex history, which is the alternative semantics the paper floats in a footnote --- box quantifying over the convex histories whose domain contains the time, the tense operators restricted to that domain, and logical consequence relativised from D to the domain --- and it forecloses formalizing the presheaf appendix without first reintroducing a layer. Assess whether retaining `ConvexHistory` as a structure that the semantics simply no longer uses preserves those options at acceptable cost. That middle answer is the likeliest one and deserves to be costed as carefully as the two extremes rather than adopted by default.
(e) Recommend exactly one of: COLLAPSE, with a phased plan sized so that each phase is one agent run and leaves `lake build FormalSystem` green; KEEP, with the reason recorded once in the `ConvexHistory` module docstring so the question is not silently reopened a third time; or COLLAPSE-PARTIALLY, retaining `ConvexHistory` as a definition while retargeting the semantics to a total index. State the reasoning, not just the verdict, and state it well enough that a follow-up task can execute without re-deriving it.

CONSTRAINTS. Do not begin the refactor as part of this research; probe files under this task's directory are fine, edits to the live tree are not. The history-vocabulary rename must land first --- costing this against a tree in which `WorldHistory` still names the convex layer would produce a plan that reads as its own opposite. Any plan this task proposes must leave `PartialHistory` and the Extension Theorem untouched: the Extension Theorem's conclusion is stated at the partial layer and is unaffected either way. `lake build FormalSystem` must be green with no new `sorry` at the end of every phase of any plan proposed here.

---

### 552. Align history vocabulary with paper
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: paper-refactor
- **Dependencies**: Task 548

**Description**: Rename this repository's semantic history layer so that its names mean what the paper's mean: the paper's `def:world-history` layers *partial history* -> *convex history* -> *world history* (equivalently *possible world*, the set being H_F), and this repository's `WorldHistory` denotes the paper's CONVEX history, not its world history. Rename `WorldHistory` to `ConvexHistory` throughout, keep `IsTotal` and `TaskFrame.HF` as they are, and re-pin the drifted `def:world-history` record entry. This is a name-and-prose sweep with no change to any proof term.

PAPER CONVENTION (current text of `def:world-history` in /home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex): a *partial history* over a task frame is a function tau : X -> W on a nonempty X subset of D with tau(x) => _{y-x} tau(y) for all times x, y in X, with no convexity requirement; a *convex history* is any partial history whose domain X is convex; a *world history* --- equivalently a *possible world* --- is any convex history whose domain is total, so that X = D; *history* is the generic term for all three wherever the distinction is immaterial; H_F is the set of all world histories over F. The paper's body reinforces the layering rather than merely stipulating it: a finite game of chess is a bounded convex history, and the paper argues that a bounded convex history is NOT a possibility in which time begins or ends, which is exactly why it must not be called a world history. The paper also defines W_F as the set of time-shift equivalence classes [tau]_F and then states that, since those classes play no further role, it will also refer to H_F as the set of possible worlds --- so H_F = possible worlds is the paper's own identification, and this repository's lack of a W_F quotient is a licensed omission rather than a divergence. Record that fact once; do not build a quotient.

THE MISMATCH IS A SHIFT-BY-ONE, not a scatter of small divergences. `PartialHistory` is already correct and must not be touched. `WorldHistory` denotes the convex layer, i.e. the paper's convex history, which makes it a false friend: `forall sigma : WorldHistory F, ...` without an `IsTotal` guard quantifies over strictly MORE than H_F. Correspondingly the paper's middle tier has no Lean name at all --- the string "convex history" occurs zero times in this repository. The origin is recorded and benign: `specs/paper-definitions-of-record.md` (the `def:world-history` entry, lines 577-593) still quotes the SUPERSEDED wording, "A world history is any partial history whose domain X is convex... A world history is total --- equivalently, a possible world --- just in case X = D". The Lean naming was a faithful transcription of the draft it was made from; the paper has since renamed the middle tier and given the top tier the name.

MEASURED STATE. Identifier `WorldHistory`: 629 lines under `FormalSystem/` across 78 `.lean` files, of which 7 files are under `Boneyard/`; 6 lines in `Tests/`; 43 in `docs/`; 4 in `typst/`; 5 in `latex/`. `specs/` carries 2505 further occurrences which are ARCHIVAL task history and must not be rewritten. Case variants beyond the bare name: `toWorldHistory` (6), `worldHistory_ext` (4), `isTotal_toWorldHistory` (2), `toWorldHistory_toPartialHistory` (1), and `Boneyard/ChainCompleteness/Bundle/SuccChainWorldHistory.lean` (2, Boneyard). Heaviest live files: `Semantics/Truth.lean` 64, `Metalogic/Decidability/Verified/Decidable.lean` 57, `Semantics/IntTransfer.lean` 33, `Semantics/WorldHistory.lean` 32, `Semantics/Validity.lean` 31, `Semantics/StarTruth.lean` 30, `Semantics/StarPasting.lean` 22, `Metalogic/WeakCanonical/IntegerModel/ReynoldsBridge.lean` 18, `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean` 16, `Metalogic/Independence/StaticFrame.lean` 14. `import FormalSystem.Semantics.WorldHistory` occurs on 8 lines. There are NO string literals, JSON fixtures or benchmark data naming the type --- `data/`, `scripts/` and `FormalSystem/Automation/` were checked and carry none --- so unlike the FrameClass rename there is no fixture tail. `ConvexHistory` currently occurs 0 times anywhere in the tree, so the target name is free. Prose occurrences of "world histor*" outside `specs/`: 100 lines in `FormalSystem/`, 35 in `docs/`, 30 in `typst/`, 17 in `latex/`, 1 in `Tests/`. Most of those say "world history" while MEANING the convex notion, and they are the real editorial work of this task; the identifier sweep is the easy half.

WORK.
(a) Rename the file `FormalSystem/Semantics/WorldHistory.lean` to `FormalSystem/Semantics/ConvexHistory.lean` and fix the 8 import lines plus the `FormalSystem/Semantics.lean` aggregator, which names it at lines 21, 107, 169, 185, 234 and 242.
(b) Rename the structure and its namespace `WorldHistory` -> `ConvexHistory` and every derived identifier with it: `toWorldHistory` -> `toConvexHistory`, `worldHistory_ext` -> `convexHistory_ext`, `isTotal_toWorldHistory` -> `isTotal_toConvexHistory`, `toWorldHistory_toPartialHistory` -> `toConvexHistory_toPartialHistory`. `PartialHistory`, `IsTotal`, `ofTotal`, `timeShift` and `TaskFrame.HF` all keep their names.
(c) `TaskFrame.HF` becomes the sole Lean name for the paper's world histories. Rewrite its docstring (currently `Semantics/WorldHistory.lean:405-420`) so it says that an element of `F.HF` is a world history, equivalently a possible world, and that `IsTotal` is the predicate form of the same notion. Do NOT introduce an `abbrev WorldHistory F := F.HF`: it would make dot-notation such as `tau.states` fail on a subtype and would reintroduce exactly the ambiguity this task removes. If a structure-level Lean name for the paper's top tier is wanted beyond `HF`, that is the collapse question, not this task's business.
(d) Rewrite the prose. Every docstring, README and documentation line that says "world history" while meaning the convex notion becomes "convex history"; every line that means the total notion becomes "world history (possible world)". The module docstrings of `PartialHistory.lean` and of the renamed `ConvexHistory.lean` both restate the paper's layering verbatim and must be RE-QUOTED from the current paper text rather than adjusted in place. `FormalSystem/Semantics.lean:185`'s table row --- "World History | tau : X -> W convex | WorldHistory F with convex proof" --- is precisely the wrong row and should become two rows, one per tier.
(e) Re-pin `def:world-history` in `specs/paper-definitions-of-record.md` following that file's own "How to extend this record" procedure, together with `thm:extension` and `cor:occurrence`, whose statements now read "world history" where the record has "total world history": `thm:extension` is now "Every partial history tau : X -> W over a task frame F is extended by some world history sigma in H_F", and `cor:occurrence` is now "there is a world history tau in H_F where tau(x) = w, and so H_F is nonempty". The new `def:world-history` also carries a footnote citing THIS repository for the `WorldHistory`/`IsTotal` naming; that footnote becomes false the moment this task lands. The paper is read-only input here, so record the fact for the paper author rather than editing the paper.
(f) `bash scripts/check-paper-definitions.sh` currently reports 15 drifted anchors and 9 unresolved. Only `def:world-history`, `thm:extension` and `cor:occurrence` belong to this task; the z/d/r anchors belong to the separate re-pin task and the remainder to neither. Do not conflate them. Leave the whole-file checksum sentinels to whichever of the two paper-refactor re-pins lands second.

VERIFY. `lake build FormalSystem` green with no new `sorry`; `scripts/check-module-invariants.sh` no regression; a final grep confirming that no live-tree file outside `Boneyard/` and `specs/` contains the identifier `WorldHistory`, and that no live docstring uses the phrase "world history" for a merely-convex domain. This is alpha-renaming plus prose: if any proof term needs to change, something has gone wrong --- stop and record it rather than adapting the proof around it.

SCOPE BOUNDARY. Do not collapse, weaken or delete the convex layer; do not touch the `exists (ht : tau.domain t)` guard in `TruthAt`'s atom clause; do not remove any `IsTotal` hypothesis. Whether the convex layer should exist at all is a separate research task and must not be pre-empted here. Landing this rename first is precisely what makes that question answerable on its own merits, since costing a collapse against a tree whose names still mislead would produce a plan nobody can follow.

DEPENDENCY NOTE. The dependency on the paper-anchor re-pin task is for file serialisation only: both tasks edit `specs/paper-definitions-of-record.md` and both re-run the same checker, and interleaving them would produce conflicting checksum sentinels. The subject matter is independent, so the dependency may be dropped if this task is run first instead.

---

### 551. Boneyard disposition for publication
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: repo-hygiene
- **Dependencies**: None

**Description**: Decide the disposition of `FormalSystem/Boneyard/` -- 91,539 lines, roughly a quarter of the repository, carrying every `sorry` in the tree.

MEASURED, not estimated. `FormalSystem/Boneyard/` is 168 Lean files totalling 91,539 lines, against 373,234 lines for `FormalSystem/` as a whole. It is genuinely excluded from the build, not merely nominally: a full `lake build` produces ZERO Boneyard `.olean` files. A sorry census over the live tree (`Metalogic`, `Syntax`, `Semantics`, `ProofSystem`, `Theorems`, `Automation`) reports `sorry_count: 0`, while 39 Boneyard files contain sorries in proof position. The quarantine works exactly as designed.

THE DECISION, and it is a judgement call rather than a cleanup. Boneyard doubles the apparent size of what a reviewer must navigate and contains the only unfinished proofs in the repository, yet retired-attempt provenance has real scholarly value -- it is evidence of what was tried and why it failed, which is often the most useful part of a formalization for a subsequent researcher. Both keeping and cutting are defensible; what is not defensible is shipping it undecided and unexplained.

DELIVER A REASONED RECOMMENDATION, with the evidence to act on it:
1. Characterize what is actually in there. The two Boneyard trees are already distinguished in `FormalSystem/FormalSystem.lean` and `Boneyard/README.md` (there is a documented "two-Boneyard counting caveat") -- start from those rather than re-deriving. Which subtrees are genuinely superseded, which record refuted approaches still cited elsewhere, and which are merely unfinished?
2. Check for live references before proposing any removal. `scripts/audit-deletion-references.sh` exists for this; a subtree cited by live documentation or by a C9-style register is not free to delete even though nothing imports it.
3. Recommend one of: KEEP AS-IS with a clearer top-level framing of what the tree is and why it ships; SPLIT, retaining the subtrees with provenance value and cutting the rest; or CUT ENTIRELY, with the history preserved in git and a pointer recorded. State the reasoning, not just the verdict.
4. Only if the recommendation is to cut, and only after it is accepted: execute, and verify a full green `lake build` plus an unchanged live-tree sorry census of 0.

CONSTRAINTS. Do not delete anything in the characterization or recommendation stages -- steps 1 through 3 are read-only, and step 4 is gated on acceptance of the recommendation rather than following automatically from it. Removal must go through git history preservation, never an untracked deletion. The live tree's sorry-free status is a headline property of this repository and must be preserved and re-verified by census, not assumed.

---

### 550. Decompose mintbound for publication legibility
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: publication-quality
- **Dependencies**: Task 549

**Description**: Decompose `MintBound.lean` for publication legibility -- 15,759 lines, 2.5x the next-largest live file in the repository.

MEASURED, not estimated: `FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean` is 15,759 lines. The next-largest file under `FormalSystem/` that is actually built is `GapDetection.lean` at 5,090; the only larger file anywhere in the tree is retired Boneyard code. The file also carries the C9 register (entries through 25), a running record of refuted approaches interleaved with the live development.

WHY THIS MATTERS FOR PUBLICATION. This is a legibility problem, not a correctness one -- the file builds green, is sorry-free and axiom-free. But a single file of this size is effectively unreviewable, and the interleaving of live results with a register of refuted attempts means a reader cannot tell, locally, which of the two they are reading. The concrete failure mode is already on record: the six `_run` theorems are vacuous, and the only statement of that fact sits roughly 12,700 lines into the file, far from the declarations it invalidates.

SCOPE:
1. Characterize the file's actual composition before proposing any split -- live definitions and theorems, the C9 register, probe/measurement blocks, and long-form prose notes. Report the line budget of each. A split proposed without this measurement is guesswork.
2. Propose a decomposition into modules with a stated organizing principle (by development layer, by frame class, or register-vs-live -- pick one and justify it against the alternatives). The C9 register is the strongest candidate for extraction: it is documentation of what did not work and need not sit inside the module carrying what did.
3. Execute the split additively and verifiably: the public interface must be preserved exactly, every downstream importer must build unchanged, and the full `lake build` must stay green. Sorry-free, axiom-free.

CONSTRAINTS. Preserve every existing declaration name -- this is a decomposition, not a rename or a cull; removing declarations is a separate decision and belongs to the disposition task. Do not weaken or drop C9 register content while relocating it; the register's value is that it prevents re-attempting refuted approaches, and a lossy move destroys exactly that. Expect expensive builds: this module has cost 5-25 minutes per pass under concurrent load, so batch verification rather than rebuilding per edit.

Dependencies: 549. If its disposition recommendation is to retire the six vacuous `_run` theorems, that removes a section of this file, and decomposing before knowing so is wasted work.

---

### 549. Trace decide dependency on vacuous run theorems
- **Status**: [IMPLEMENTING]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 463
- **Research**: [549_trace_decide_dependency_on_vacuous_run_theorems/reports/01_trace-decide-dependency-vacuous-run.md]
- **Plan**: [549_trace_decide_dependency_on_vacuous_run_theorems/plans/01_decide-dependency-verdict-disposition.md]

**Description**: Trace whether `FormalSystem.Metalogic.Decidability.decide` depends on the six now-vacuous `_run` theorems, and correct the affected status claims if it does.

WHY THIS EXISTS. Task 463 machine-checked a FALSE verdict: `PostBlockingSettlesRun fc fuel` is refutable at every `fuel >= 1`, hence at the terminus's own `mintAwareFuelAt` figure for all parameter values. The consequence is that `buildTableauAt_isSome_of_budget_fixed_run` (MintBound.lean:12199) and its five `_run` siblings are VACUOUS at `.Base`, `.Dense` and `.RTime` -- they carry a false hypothesis. Vacuous here means unusable as premises, not merely unproved: they establish nothing, so anything resting on them for a load-bearing step has no support.

THE OPEN QUESTION, stated as a question and not a claim. `docs/theorem-index.md:113` carries a status row for the tableau decision procedure `FormalSystem.Metalogic.Decidability.decide` (`DecisionProcedure.lean`, Base, `pcq pinned:C14`). That row does NOT cite the `_run` theorems by name, so it is not wrong on its face. But if `decide`'s totality or correctness argument routes through any of the six vacuous results, the row's status claim is indirectly overstated. Nobody has traced it. Do not assume either answer.

SCOPE -- a dependency trace, then a conditional correction:
1. Enumerate the six vacuous `_run` results precisely (the terminus `buildTableauAt_isSome_of_budget_fixed_run` and its five siblings; task 463's report and its C9 register entry name them).
2. Trace, mechanically rather than by reading prose, whether `decide`'s totality/correctness argument reaches any of them -- `#print axioms`, transitive import/use analysis, or `lean_references` on each of the six. A mechanical trace is the deliverable; a prose argument that it "probably doesn't" is not.
3. BINARY VERDICT, both outcomes first-class:
   - NO DEPENDENCY: record that `decide` routes around them, name the evidence, and leave `docs/theorem-index.md:113` untouched. This is a real result, not a null one -- it retires an open question.
   - DEPENDS: name every load-bearing step that rests on a vacuous premise, state precisely what `decide`'s row may still claim and what it may not, and correct the row.

CONTEXT ALREADY ESTABLISHED -- consume, do not re-derive. A concurrent search of `docs/` and `README.md` for all 13 `_run`-suffixed declarations in `FormalSystem/` returned zero hits, so no documentation cites the six by name; the exposure, if any, is indirect through `decide` alone. A weak prior, explicitly NOT clearance: the six sit in the termination/fuel-bound layer (`Termination/MintBound.lean`) while the index row points at `DecisionProcedure.lean`, so a termination-side vacuity is likelier to break a fuel-bound argument than a correctness argument -- but MintBound is a termination file and totality is exactly the kind of claim that could route through it.

CONSTRAINTS. Read-only with respect to `FormalSystem/**` -- this task traces, it does not repair; if the trace finds a real break, the repair is a separate task and must be named, not attempted here. The only file this task may edit is `docs/theorem-index.md`, and only on the DEPENDS branch. Do not edit `MintBound.lean` (task 463 owns it and both tasks would collide on the same file). No `sorry`, no axiom additions, full `lake build` green.

Dependencies: 463, both mathematically (its verdict is this task's premise) and as a file_scope serialization edge on MintBound.lean.
ADDED DELIVERABLE -- disposition recommendation (publication-driven). Beyond the trace verdict above, this task MUST also deliver a recommended DISPOSITION for the six vacuous `_run` theorems, because it will hold exactly the evidence the decision needs and no other task will. This remains READ-ONLY: recommend and justify, do not execute. The three dispositions are mutually exclusive and the trace result selects among them:
- NO DEPENDENCY anywhere -> recommend RETIRING the six. They read as headline results ("the tableau construction succeeds") while establishing nothing, which is worse than absent in a publication-facing library: a reader meeting `buildTableauAt_isSome_of_budget_fixed_run` at its declaration site gets no local signal that its hypothesis is unsatisfiable, the refutation being recorded ~12,700 lines away in C9 entry 25. Name what else would have to move with them.
- DEPENDS, at `.Base`/`.Dense`/`.RTime` -> recommend marking vacuity AT THE DECLARATION SITE (not only in the register), and name the dependent that needs repair as its own task.
- DEPENDS, at `.ZTime` -> the fourth frame class is load-bearing after all; recommend completing it. The mechanical recipe is already recorded in MintBound.lean's scoped note: add the `priorUZ`/`priorSZ` conclusions to the witness at `<0,0>`, `<0,1>`, `<1,0>`, `<1,1>`, then re-run the same three `rfl` obligations at `.ZTime`.

WHY THIS IS ONE TASK AND NOT TWO. The `.ZTime` strengthening is worth doing in exactly one of these three outcomes. Deciding it before the trace is a coin-flip on expensive build time, and in the RETIRE branch it would mean polishing code that is then deleted. State the recommendation plainly enough that a follow-up task can execute it without re-deriving the reasoning.

---

### 548. Repin renamed paper anchors bx z d r
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: paper-refactor
- **Dependencies**: Task 547

**Description**: Re-pin the paper anchors changed by the paper's z/d/r refactor and its removal of the Past/Future fragment, and update every citing docstring and the definitions-of-record so that scripts/check-module-invariants.sh C15 resolves them. RENAMED LABELS: def:TMplus-f, def:TMplus-d, def:TMplus-c are now def:BX-z, def:BX-d, def:BX-r; def:TMplus is unchanged and still names TM. CHANGED TEXT UNDER UNCHANGED LABELS: cor:tm-completeness now lists TM strongly complete over all task frames, TM_d strongly over the dense task frames, TM_z weakly over Z-time, and TM_r weakly over R-time; def:derivability and def:soundness are now stated for TM and the full language BL rather than for the fragment system; thm:TM-soundness now speaks of TM and its extensions, adds a sentence that the since/until/next/previous schemata are valid by their clauses as verified in this repository, and its footnote cites this repository for TM rather than for the fragment system; lem:temporal-duality and thm:TD-valid are now stated for the since/until interchange with new inductive cases for U and S. DELETED ANCHORS: prop:fragment and rmk:fragment no longer exist (no Lean file cites either, and neither is pinned -- verify). MEASURED STATE: specs/paper-definitions-of-record.md pins `def:TMplus-f`, `def:TMplus-d`, `def:TMplus-c` with content hashes in the machine-readable manifest (rows near line 1431) and carries their full-text entries at lines 993, 1014, 1032, alongside `def:TMplus` (line 1056) and `cor:tm-completeness` (line 1175); `thm:TM-soundness` is cited by 2 Lean files and appears on 4 record lines; `def:soundness` and `def:derivability` each appear on 1 record line; `def:TMplus` is cited in 20 lines across 13 Lean files and `cor:tm-completeness` in 9 files; C15 resolves anchors against the record, not the paper. The paper's new text is at /home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex: def:BX-z (Discrete Burgess-Xu logic BX_z, axioms UZ and Z1, Z-time footnote), def:BX-d (dense logic BX_d, axioms DN and NN), def:BX-r (Dense and Complete Burgess-Xu logic BX_r, the extension of BX_d by PU and SP, CO derived), def:TMplus (TM_z, TM_d, TM_r as the extensions of TM by the axioms distinguishing BX_z, BX_d, BX_r). The Semantics/FrameClassValidity.lean docstring quotes the closing sentence of the old def:TMplus-f verbatim ('the successor-Archimedean discrete class to which BX_f and TM⁺_f are sound and complete is exactly Z-time'); it now reads BX_z and TM_z and the quotation must be refreshed. The Logic-subsection footnote that replaced the fragment proposition cites this repository for the Z1 result (`not_bl_derivable_z1` in Metalogic/Conservativity/Z1Countermodel.lean); its Kripke countermodel for the base class is a pen-and-paper claim that this repository does not check -- record it as such, do not pin it as verified. WORK: follow the record's own 'How to extend this record' procedure to retire the three old anchors, pin the three renamed ones, and re-hash every changed entry named above; update every citing docstring to the new label names; re-run scripts/check-module-invariants.sh until C15 reports no unresolved anchor from this refactor. The three unrelated unresolved anchors (app:drift, cor:no-characterization, lem:deterministic-singleton) belong to a separate open task and must not be conflated with this one.

---

### 547. Replace historical system names in docstrings
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: paper-refactor
- **Dependencies**: Task 546

**Description**: Replace the historical extension names TM⁺_f, TM⁺_c, TM⁺_dc, TM_f, TM_c, TM_dc, BX_f, BX_c in docstrings, comments, docs and scripts with the paper's current z/d/r subscripts, and record in one place the mapping between this repository's two base systems and the paper's. PAPER CONVENTION (implemented in /home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex): the since/until logic of BL is called TM; its extensions are named by the class over which each is complete -- TM_z (Z-time), TM_d (dense task frames), TM_r (R-time, the dense and complete orders) -- with the same subscripts on the Burgess-Xu cores BX_z, BX_d, BX_r. BX_r is the extension of BX_d by PU and SP, with CO derived, matching this repository's Dedekind-class derivations. THE PAPER NO LONGER NAMES A PAST/FUTURE FRAGMENT: the former fragment language BL⁻ and the systems TM⁻, TM⁻_f, TM⁻_d, TM⁻_dc, the Fragment proposition and the fragment remark are all deleted. What remains is one footnote in the Logic subsection stating the Past/Future axiom set (S5 schemata, MF, TK, T4, TB, TA, TL, TD with P and F interchanged), its incompleteness over all task frames by a two-line Kripke countermodel to the dichotomy of a boxed DF instance and a boxed DN instance, the Z-time incompleteness of its extension by DF via Z1 (citing this repository), and the open dense and R-time cases. MAPPING: this repository's `TM` (BaseLanguage, H/G primitive) is that footnote's Past/Future system, and its `TM⁺` is the paper's TM; the repository's `TM_f`, `TM_d`, `TM_dc` (BaseLanguage plus DF, DN, DN and CO) correspond to no named paper system. DO NOT drop the ⁺ superscript and do not rename bare `TM`: the earlier plan to do so is withdrawn, because bare TM is not greppable and the TM/TM⁺ distinction is load-bearing throughout Conservativity/. WORK, a comment-and-docstring-only sweep with no identifier changes beyond those the FrameClass rename task already made: (a) TM⁺_f → TM⁺_z, TM⁺_c and TM⁺_dc → TM⁺_r, BX_f → BX_z, BX_c → BX_r; (b) for the BaseLanguage extensions use the parallel Lean-only names TM_z, TM_d, TM_r (replacing TM_f, TM_c, TM_dc) and say once that these have no paper name; (c) add the mapping paragraph above to the module docstring of FormalSystem/Metalogic/Conservativity.lean and to docs/README.md, and reword the `TMFrag` docstring in Metalogic/Conservativity/Fragment.lean so it describes the H/G-fragment of TM⁺ as the set of Past/Future theorems of the paper's TM rather than as a fragment of a named paper system; (d) rewrite the per-constructor anchors in Semantics/FrameClassValidity.lean in the new vocabulary. MEASURED STATE under FormalSystem/: `TM⁺` 124 lines in 21 files (stays); `TM_f` 29 lines in 8 files; `TM_dc` 8 lines in 4 files; `TM_c` 7 lines in 3 files; `BX_c` 3 lines in 2 files; `BX_f` 2 lines in 2 files; 12 further lines across docs/, scripts/ and the definitions-of-record. TM⋆ (Metalogic/Conservativity/Star/) is a different system and must not be touched. Verify with a final grep that no f, c or dc subscript remains outside Boneyard/ and the archive, and that lake build FormalSystem stays green.

---

### 546. Rename frameclass tags to ztime rtime
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: semantics
- **Dependencies**: None
- **Research**: [546_rename_frameclass_tags_to_ztime_rtime/reports/01_frameclass-ztime-rtime-rename.md]
- **Plan**: [546_rename_frameclass_tags_to_ztime_rtime/plans/01_ztime-rtime-rename-plan.md]
- **Summary**: [546_rename_frameclass_tags_to_ztime_rtime/summaries/01_ztime-rtime-rename-summary.md]

**Description**: Rename FrameClass.Discrete and FrameClass.Dedekind to FrameClass.ZTime and FrameClass.RTime, with the frame predicates IsSuccArchDiscrete and IsDedekind renamed IsZTime and IsRTime, so that the Lean class tags say what they mean and match the paper's new system naming. PAPER CONVENTION (now implemented in /home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex, Extensions subsection and Appendix): each extension of TM is named by the class over which it is complete -- TM (all task frames), TM_z (Z-time, weakly complete), TM_d (dense task frames, strongly complete), TM_r (R-time, weakly complete), with the same subscripts on the Burgess-Xu cores BX_z, BX_d, BX_r and on the Past/Future fragments. R-time is defined there as the dense and complete temporal orders, which by Holder are exactly R; the complete temporal orders are exactly Z and R up to isomorphism. The frame CONDITIONS keep their names Discrete, Dense, Complete with correspondents DF, DN, CO. MEASURED STATE: `inductive FrameClass | Base | Dense | Discrete | Dedekind` at FormalSystem/ProofSystem/Axioms.lean:529 with the partial order Dense <= Dedekind at :536-543; `FrameClass.Sat` at FormalSystem/Semantics/FrameClassValidity.lean interprets `.Discrete` as `TaskFrame.IsSuccArchDiscrete` and `.Dedekind` as `TaskFrame.IsDedekind`, and its docstring records in bold that neither tag means the bare condition its name suggests -- that is the confusion this rename removes. Occurrence counts under FormalSystem/: `.Discrete` 494 lines in 70 files, `.Dedekind` 345 lines in 54 files, `IsSuccArchDiscrete` 32 lines in 9 files, `IsDedekind` 29 lines in 8 files; derived names `soundness_discrete` 58 lines in 18 files, `soundness_dedekind` 44 lines in 9 files, `ValidDiscrete` 135 lines in 26 files, `ValidDedekind` 103 lines in 24 files, plus `TMCompleteDiscrete` in Metalogic/Conservativity/TMCompletenessReduction.lean and the string literals in Automation/ProofStepExport.lean and Automation/BenchmarkAnchors.lean that name classes (`fc := .Discrete`). WORK: rename the two constructors and two predicates; rename the derived identifiers consistently (soundness_ztime, soundness_rtime, ValidZTime, ValidRTime, TMCompleteZTime, and so on -- pick one scheme and apply it everywhere, recording it in the naming-convention docs); leave `TaskFrame.IsDiscrete` and `TaskFrame.IsComplete` as the bare conditions; update the FrameClass.Sat docstring so the naming-deviation paragraphs become plain statements of what each tag denotes; update every string literal and any JSON or benchmark fixture that names a class. Do not change any semantics or proof content. lake build FormalSystem must stay green with no new sorry, and scripts/check-module-invariants.sh must not regress. This is the first of three tasks pressing the paper's z/d/r convention into this repository; the docstring system-name replacement and the paper-anchor re-pinning are separate follow-on tasks.

---

### 545. Hg completeness dense and dedekind verdicts
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Topic**: incompleteness
- **Dependencies**: None
- **Research**: [545_hg_completeness_dense_and_dedekind_verdicts/reports/01_hg-completeness-dense-dedekind.md]

**Description**: Decide, with machine-checked proof, whether the two H/G-language (Past/Future) systems that the paper leaves open are weakly complete: TM_d := TM + DN over the Dense frame class, and TM_dc := TM + DN + CO over the Dedekind (dense-and-complete, i.e. R-time) class, where TM is the BaseLanguage proof system (the paper's TM^-). These are the two remaining open rows of the paper's rmk:fragment; the Base row is the CEB task (Sp underivability) and the Discrete row is closed (tmCompleteDiscrete_refuted). A negative verdict with a machine-checked separating H/G-validity, or a positive verdict with a completeness proof, are both complete outcomes; an honest OPEN verdict must name the precise obstruction. EXPECTED VERDICT (to be tested, not assumed): both complete. Reasoning: unlike Base and Discrete, neither class splits into two H/G-definable subclasses, so no (Sp)/Z1-style dichotomy witness is available; every dense unbounded chain has the H/G logic of Q by downward Lowenheim-Skolem, and R is a single frame up to isomorphism. SUGGESTED ROUTE FOR DENSE: (1) Kripke-style completeness of TM + DN over frames whose Box-classes are R-closed unions of dense unbounded chains, via the Sahlqvist/canonical-model argument for the fusion S5 (x) Kt4.3 + seriality + density with the MF interaction (MF and its TD-mirror force each Box-class to be closed under R-successors and R-predecessors; the TM-completeness-status report section 5(i) records this as the Kripke-level answer, unformalized); bulldoze clusters into dense chains; (2) replace each chain by a countable elementary substructure, order-isomorphic to Q by Mathlib's Order.iso_of_countable_dense; (3) transform into a Dense task frame: world states := chain points, durations := Q, task relation := translation along each chain (a disjoint union of translation task frames, each satisfying Compositionality, Seriality, Limit, Saturation with singleton fibres), histories := all translates; show BL truth is preserved since Box over H_F at a time equals truth at every point of the class under translation closure. SUGGESTED ROUTE FOR DEDEKIND: the temporal part of TM_dc is Bull 1968 / Goldblatt's axiomatization of the H/G logic of R (CO is exactly the Dedekind axiom of that literature), so the target is Bull's completeness theorem for R plus the same product/translation transfer; NOTE that CO is not Sahlqvist, so the canonical-model route of the Dense case does not apply and a Bull/Burgess-style step-by-step or Dedekind-completion construction is required, making this the substantially harder half. EXISTING ASSETS: BL-side semantics and soundness (Semantics/BLTruth.lean, BLValidity.lean, Metalogic/Conservativity/BaseLanguageSoundness.lean), the Fragment theorem (Conservativity/Fragment.lean), the reduction tmComplete_iff_forward and its Dense/Dedekind rows (Conservativity/TMCompletenessReduction.lean), the BX-side canonical model and completeness_dense / completeness_dedekind (Metalogic/BXCanonical/), and LexCarrier.lean. RELATION TO OTHER TASKS: settling these two rows settles the Sigma_fc = empty case of the Hg-fragment finite-axiomatizability task at Dense and Dedekind, and is independent of the CEB task at Base. HARD CONSTRAINT inherited from Conservativity.lean: never state a completeness or forward-conservativity theorem and discharge it with sorry.

---

### 544. Machine check sp underivable native bl soundness
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Topic**: incompleteness
- **Dependencies**: None
- **Research**: [544_machine_check_sp_underivable_native_bl_soundness/reports/01_sp-underivable-native-bl-soundness.md]

**Description**: Machine-check the failing half of CEB: no instance of the boxed dichotomy (Sp) := Box(DF phi) or Box(DN psi) is a theorem of TM, the BaseLanguage Past/Future proof system (the paper's TM^-). SpWitness.lean already records (Sp) as BL-valid (blValid_sp) and TM+-derivable (sp_translate); its TM-underivability is the one claim in the paper's fragment-system discussion (possible_worlds.tex, sub:Logic, second footnote of the TM^- paragraph) that is stated as NOT verified, and the paper wants to cite this repository for it. WHY IT IS UNAVAILABLE TODAY: (Sp) is valid on every task frame, so no TaskFrame-bound refutation exists; a countermodel must be a structure OUTSIDE the task-frame class on which every TM schema remains sound but whose temporal order is neither discrete nor dense (e.g. the lexicographic sum Z + Q, or the two-fibre structure named in Metalogic/Conservativity.lean). SCOPE, following the follow-up proposed but not created by the TM-completeness-status task: (1) a native BL frame notion not bound to TaskFrame; (2) a native BL truth definition over it; (3) a native BL soundness theorem verifying all TM axiom schemata directly (MK, MT, M5, MF, TD, TK, T4, TB, TA, TL) plus MP, MN, and temporal necessitation, via swap-strengthened induction for TD; (4) the concrete countermodel instance and the evaluation of some (Sp) instance as false there; (5) the theorem not_derivable_sp and its corollary tmCompleteBase_refuted : not TMCompleteBase, mirroring Z1Countermodel.tmCompleteDiscrete_refuted. HARD CONSTRAINT inherited from Conservativity.lean: never state a forward-conservativity theorem and discharge it with sorry; it is refuted, not open. OUT OF SCOPE: whether TM^-_d and TM^-_dc are complete over the dense and dense-and-complete classes remains a separate open question.

---

### 543. Formalize mf correspondence rigidity
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: metalogic
- **Dependencies**: Task 500

**Description**: Machine-check the principal new results from the MF frame-correspondence research conducted in the PossibleWorlds paper repository. SOURCE MATERIAL (read before starting; six reports, all outside this repository): /home/benjamin/Philosophy/Papers/PossibleWorlds/specs/136_rewrite_mf_paragraph_frame_correspondence/reports/02_mf-substrate-weakening-definability.md (Theorem A), /home/benjamin/Philosophy/Papers/PossibleWorlds/specs/136_rewrite_mf_paragraph_frame_correspondence/reports/03_worlds-topological-categorical-characterization.md (rigidity, T1 converse), /home/benjamin/Philosophy/Papers/PossibleWorlds/specs/136_rewrite_mf_paragraph_frame_correspondence/reports/04_dense-correspondent-and-rigidity.md (Theorems B and C, scope limits), and /home/benjamin/Philosophy/Papers/PossibleWorlds/specs/136_rewrite_mf_paragraph_frame_correspondence/reports/05_lean-verification-and-formalization-program.md (THE ROADMAP -- effort estimates, elaborated statements, and Mathlib dependencies, all checked against this tree). VERIFIED BASELINE, established by that round-3 work against this repository: lake build FormalSystem green (2591 jobs); 20 lean_verify calls returning standard axioms with no sorryAx; and the claim that modal_future_valid discharges no frame field now verified at the proof-term level by a transitive constant-closure walk (696 of 703 constants, imported bodies loaded via findAsync?) finding no FrameOver or TaskFrame field projection and no hF_nonempty. TARGETS, in roadmap priority order. R1: the result that deterministic task frames determine the same BL-logic as all task frames. It is NOT the pure composition of reverse_repr and forward_repr that the originating report claimed -- it needs a third fact, S.frame.Deterministic, absent from this tree; with a one-line helper it typechecks in about 25 lines, reproduced in report 05 Appendix A.1 (elaborated in scratch only; nothing was written into this repository). R2 -- BEST EFFORT-TO-VALUE IN THE SET: the rigidity theorem (report 03 section 4.3.6): over a dense Archimedean temporal order a task frame is static iff it has a uniform dwell time, hence every task frame over such an order with finitely many world states is static. Approximately 100 lines, and the finite-W half ALREADY EXISTS here as exists_uniform_radius_of_finite. The proof uses only Limit and Compositionality; Mathlib supplies Archimedean and DenselyOrdered. The claim is surprising enough that machine-checking it before it enters the paper is the point. Note report 04's refinement: for time-indexed frames the boundary is Dedekind completeness rather than the Archimedean property. R3: the T1-converse witness (report 03 section 4.2.3), a 4-state structure refuting the converse of the paper's Limit-implies-T1 result. BLOCKER TO RESOLVE FIRST: this witness cannot currently even be STATED here, because WorldHistory requires a TaskFrame and the witness violates that structure's limit field; a structural workaround is needed, and this would introduce the first topology into the repository. R4: Theorem A (MF valid iff the task relation is stationary) over Z-time, medium-large; the TimeIndexed structure and the statement are elaborated in report 05. CRITICAL SCOPE CONSTRAINT from report 04 Theorem C: Theorem A's scope is EXACTLY D isomorphic to Z -- for every discrete D not isomorphic to Z (including Z x_lex Z) and every countable or divisible dense D, a non-affine order-automorphism yields a deterministic non-stationary MF-valid frame. Do not state it more generally. Also worth formalizing: Theorem B (report 04) -- MF valid iff its past mirror MP valid iff every box-sentence is globally constant in every model -- which is exact and uniform over every D and is flagged in report 04 as reachable via box_const. NOT RECOMMENDED: Theorem A-prime; report 05 judges the formalization cost unjustified and the paper statement fine unformalized. DEPENDENCY RATIONALE: this task depends on the ShiftSet representation-theorem reconciliation research task because Theorems A and B both touch FormalSystem/Semantics/ShiftSet.lean, and that task exists precisely to prevent two parallel representation theorems from being developed and having to be reconciled afterwards. Settle that question before landing R4. Land real proofs; no sorry. This repository already carries a task-relation correspondent the paper lacks, density_schema_iff_fwdRec over Z, which is a useful model for how to state these.

---

### 542. Dead declaration triage c17 findings
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: infrastructure
- **Dependencies**: Task 529

**Description**: Triage the dead-declaration census that C17 produces, separating genuine dead code from the scan's known blind spot. MEASURED STATE: C17 in scripts/check-module-invariants.sh is a reporting-only token census: for each declared name it takes the last dot-segment as a base identifier and counts occurrences across FormalSystem/**/*.lean, Tests/**/*.lean, and repo-wide *.md. It currently flags 989 of 10346 declarations as having zero occurrences outside their own declaration site, in roughly 2 seconds. The census has a documented structural blind spot: it cannot see indirect usage through attributes. A spot-check of one flagged declaration, `release_unfold`, confirmed it has genuinely zero textual references yet is live via the `@[formula_unfold]` attribute and its simp-set mechanism -- exactly the pattern the scan cannot detect. So 989 is an upper bound on dead code, not a count of it, and the false-positive rate is unknown. WORK: (1) quantify the blind spot first -- enumerate the attribute and simp-set mechanisms in use (`@[formula_unfold]`, `@[simp]` sets, aesop rule sets, instance registration) and determine how many of the 989 are reachable only through one of them. This is the step that makes the rest of the triage meaningful; skipping it risks deleting live code. (2) Of the genuine remainder, delete what is dead or move it to Boneyard/ per the repository's existing convention. (3) Where a declaration is intentionally part of a public surface but currently unused internally, note that rather than deleting it. (4) If the attribute-reachability analysis is mechanizable, fold it into C17 so the reported number means something closer to actual dead code. ACCEPTANCE: C17's flagged count is materially reduced with every removal justified; no declaration removed that is reachable via an attribute or simp-set mechanism; `lake build` green and the test suite passing after removals; if C17 gained an attribute-awareness refinement, its new counting rule is documented in the script header the way the existing blind spot already is.

---

### 541. Formalsystem init transitive import adoption
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: infrastructure
- **Dependencies**: Task 529

**Description**: Make the Init.lean import invariant enforceable by adopting FormalSystem.Init across the module tree. MEASURED STATE: FormalSystem/Init.lean and a CSLib-style CheckInitImports executable exist (ported from leanprover/cslib's Cslib/Init.lean + scripts/CheckInitImports.lean, using the ImportGraph transitive-closure API, which is already an inherited transitive dependency via Mathlib so no new `require` was needed). The check currently runs reporting-only: 434 modules do not yet transitively import FormalSystem.Init. This was an explicit, recorded deferral -- the CI/linter-gates task landed the mechanism and excluded the tree-wide import rewrite as out of scope. The purpose of the Init root is to give every module a single place from which repository-wide linter options and syntax settings are inherited; until adoption is universal, that guarantee does not hold and the check cannot gate. WORK: add the FormalSystem.Init import to the 434 modules that lack it transitively, working bottom-up through the import graph so most files inherit it via an existing dependency rather than each acquiring a direct import -- the goal is transitive reachability, not 434 new import lines. Confirm no import cycle is introduced (Init.lean must stay above the rest of the tree). Then flip CheckInitImports from reporting-only to gating, and wire it into scripts/check-module-invariants.sh alongside the existing checks. Note FormalSystem/Automation/AxiomNames.lean currently has zero imports and will need explicit treatment. ACCEPTANCE: CheckInitImports reports zero modules missing FormalSystem.Init transitively; the check gates rather than reports; `lake build` green; `bash scripts/check-module-invariants.sh` still reports ALL CHECKS PASSED.

---

### 540. Docstring coverage class instance lemma
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: documentation
- **Dependencies**: Task 529

**Description**: Close the three declaration categories that sit far below the repository's docstring-coverage floor. MEASURED STATE: C19 in scripts/check-module-invariants.sh reports 92.34% aggregate coverage over non-Boneyard FormalSystem/**/*.lean, against a 90% reporting floor, using a heuristic that counts a declaration documented if a `/-- -/` doc comment ends within the 3 lines above it OR it falls within an enclosing `/-! -/` section comment's scope. The aggregate passes, but it hides three categories that do not: class 16.3%, lemma 55.6%, instance 57.6%. For comparison the healthy categories are def 97.1%, abbrev 96.3%, inductive 96.3%, theorem 86.8%, structure 82.5%. `class` in particular is the worst-covered category in the tree and also the most consequential to a reader, since a typeclass's docstring is where its intended instances and laws are stated. Note also that the aggregate is dominated by theorem, which is 6429 of 10427 declarations, so category-level gaps do not move the headline number much. WORK: raise class, instance, and lemma coverage to at least the 90% floor by writing real docstrings -- what the declaration IS, present tense, with caller traps where they exist, per the repository's three-register docstring convention. Do not close the gap by widening C19's heuristic further; the heuristic was already deliberately refined once (to credit `/-!` sections) under explicit authorization, and a second widening to make a category pass would be fitting the measure to the data. Where a `lemma` is genuinely an internal step not worth documenting, consider whether it should be `private` rather than undocumented. ACCEPTANCE: C19 reports at least 90% for each of class, instance, and lemma individually, not merely in aggregate; the aggregate does not regress below its current 92.34%; no change to C19's counting rule.

---

### 539. Linter debt burndown nolints dupnamespace
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: infrastructure
- **Dependencies**: Task 529
- **Research**: [539_linter_debt_burndown_nolints_dupnamespace/reports/01_linter-debt-burndown.md]
- **Plan**: [539_linter_debt_burndown_nolints_dupnamespace/plans/01_linter-debt-burndown.md]
- **Summary**: [539_linter_debt_burndown_nolints_dupnamespace/summaries/01_linter-debt-burndown-summary.md]

**Description**: Draw down the linter debt that the CI/linter-gates work recorded rather than fixed. MEASURED STATE: `lint: true` is live in CI via scripts/nolints.json, Batteries' standard grandfathering mechanism -- the full env_linter batch runs and fails only on NEW findings, while 307 pre-existing findings are suppressed by that checked-in file. The 307 break down as unusedArguments=217, docBlame=51, defsWithUnderscore=33, tacticDocs=4, simpNF=1, structureInType=1. Separately, dupNamespace (a Lean-core syntax linter, architecturally distinct from the Batteries env_linter family and unreachable by the driver, so nolints.json cannot cover it) reports 14 findings, all in FormalSystem/Metalogic/BXCanonical/Chronicle/ChronicleTypes.lean, where `structure Chronicle` is declared inside `namespace ...Chronicle` so every field projection and the `.mk` constructor double-namespaces (Chronicle.Chronicle.dom, .f, .g, .c0..c5', etc.). C16 in check-module-invariants.sh reports the dupNamespace count via a live textual scan and does not gate on it. WORK: (1) fix the single simpNF finding, `length_range_map` in FormalSystem/Metalogic/Decidability/BiLasso/Extraction.lean (a 'simp can prove this' duplicate-lemma notice). (2) Fix the 14 dupNamespace findings by renaming the Chronicle structure out of its same-named namespace, updating every projection site. (3) Decide and record a policy for the remaining nolints.json entries: either burn down whole linter categories (docBlame's 51 and defsWithUnderscore's 33 are the tractable ones; unusedArguments' 217 is the bulk and may be largely legitimate for instance-argument-heavy signatures), or document explicitly which categories are permanently grandfathered and why. After any fix, regenerate nolints.json with `lake exe runLinter --update FormalSystem` -- but only after confirming every remaining entry is intentional, since --update grandfathers everything currently reported including a genuine regression. ACCEPTANCE: simpNF and dupNamespace both report zero findings; scripts/nolints.json shrinks by at least the categories the recorded policy commits to; plain `lake lint` still exits 0; C16 reports zero dupNamespace findings via its textual scan.

---

### 537. Tm star completeness stab nondefinability
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: metalogic
- **Dependencies**: Task 533, Task 535, Task 536

**Description**: Implement in Lean the honest TM⋆ metatheory that research task 535 found achievable, plus the non-definability of the stability modal ⊡, over the L⋆ infrastructure built by task 533 (StarFormula, StarTruthAt, StarValidIn, closed-inductive StarAxiom with the ⊡-axioms {SK, ST, S4, S5, MS, AS, PS, US}, StarDerivable, star soundness, both-direction conservativity over TM⁺). GROUND TRUTH: specs/535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md and probes/01_stab-axiom-probes.lean (60 sorry-free declarations) -- read both first. RESCOPED 2026-09-03 on 535's verdict: general TM⋆ completeness over task frames is BLOCKED as research at all four classes. Every existing completeness engine's canonical model is a deterministic disjoint-lines frame (FlowFrame.lean:145-160, ReynoldsBridge.lean:464) on which ⊡ = id, so no engine can be reused; the ⊡-class canonical model needs a Lifting Lemma (task-respecting class sequences carry tense-coherent MCS labellings) that the pasting axioms only approximate for pure formulas, the literal construction fails TaskFrame.comp's composition direction, and Limit is at risk on dense classes; the paper's all-histories semantics is the complete-tree Ockhamist case, which in the literature needed IRR + ANF rules and a trans-countable construction for F/P alone (Reynolds 2003), while Zanardo 1991 covers only bundled semantics and Reynolds 1992's IRR-free route rests on Doets' theorem over linear orders and does not transfer. Do NOT attempt general TM⋆ completeness as a normal phase, and NEVER state it and discharge it with sorry. DELIVERABLES: (1) DETERMINISTIC COMPLETENESS (mechanical): TM⋆ + Determined (φ → ⊡φ) is sound and complete over the Deterministic task frames at each class, obtained from the existing engines completeness_{base,dense,discrete,dedekind} via the collapse ⊡ = id on deterministic frames (every ⟨τ⟩_x a singleton) and the atomization lever (⊡φ depends on the world state alone; 535 probes E1/E2); coordinate with task 536, which owns the collapse lemma Deterministic F → StarValidIn F (⊡φ ↔ φ) -- consume it, do not duplicate it. (2) NON-DEFINABILITY (mechanical, models supplied): stab_not_definable -- no Formula is equivalent to the StarFormula ⊡Fp over all task models -- transcribing 535's two concrete models (a permissive 2-state frame and a 3-state frame in which state u has a unique history) that are TruthCorr-related at (const u, 0) yet differ on ⊡Fp, with □Fp false in both; the invariance notion is the tree's own TruthCorr, no new bisimulation machinery. Without this theorem someone can reasonably ask why L⋆ is a separate language at all. (3) UNDERIVABILITY OF PASTING (small): machine-check that PS/US are not derivable from the naive set {SK, ST, S4, S5, MS, AS} + TM⁺, transcribing 535's E-model argument, so the axiom set's non-redundancy is on record. (4) CONSERVATIVITY COROLLARIES that ⊡ permits: composed rows of TM⋆ over TMFrag and over TM at each class; the logic of the defined modals Will/will/Could/could as derived theorems; the deterministic-completeness transfer back to the L⁺ level, if any. (5) GATED LIFTING-LEMMA SPIKE (one dispatch, ℤ only): attempt the Lifting Lemma for the ⊡-class canonical model over ℤ-time with the exit criterion of a sorry-free star_completeness_discrete OR a written obstruction postmortem naming the exact failing TaskFrame axiom and the formula class where lifting breaks; on failure close [COMPLETED WITH EXCLUSIONS] and /spawn a follow-up research task -- the general problem is recorded as open. (6) OPTIONAL, only if (5) does not consume the budget: compactness of TM⋆ at Base and Dense via a stab case in the Łoś lemma los_truthAt (ultraproduct histories are orbit representatives; SameStateAt must be shown eventually-agreeing via omk_eq_omk). Decidability of TM⋆ is OUT OF SCOPE: 535 shows it is open and no easier than TM⁺'s open decidability problem (via forward conservativity) with no undecidability following (⊡ is not an independent third dimension; GKWZ's 3-D theorems do not apply). Update Metalogic/Conservativity.lean's Star section and README metatheory rows; keep C2/C3/C14 invariants green; no task numbers under FormalSystem/.

---

### 535. Axiomatize stability modal tm star
- **Status**: [RESEARCHED]
- **Task Type**: lean4
- **Topic**: metalogic
- **Dependencies**: None
- **Research**: [535_axiomatize_stability_modal_tm_star/reports/01_stability-modal-axiomatization.md]
- **Probes**: [535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean]

**Description**: RESEARCH TASK -- report and probe files only; no changes to FormalSystem/ or Tests/. Determine the axiomatization of the stability modal ⊡ and the completeness strategy for the resulting TM⋆, so that task 533 builds the L⋆ proof system around the right axiom set (or an explicitly extensible design) the first time. Task 533 DEPENDS ON this task; the Lean implementation of TM⋆ completeness and the non-definability theorem is task 537. THE REAL DEFINITION (possible_worlds.tex line 1114): M,τ,x ⊨ ⊡φ iff M,σ,x ⊨ φ for all σ ∈ ⟨τ⟩_x, where ⟨τ⟩_x := {σ ∈ H_F | σ(x) = τ(x)} (line 1108). The paper gives no axiomatization (line 1375). Known-valid (machine-checked in task 533's research prototypes): K and necessitation for ⊡; T, 4, 5 (⊡ is S5 on the equivalence ⟨τ⟩_x); □φ → ⊡φ (⟨τ⟩_x ⊆ H_F); p → ⊡p for atoms (atoms are valued on world states); commutation with time shift. NOT valid: ⊡φ → □⊡φ (would collapse ⊡ into □) and any ⊡/tense interaction in general (the point of Will := ⊡G vs will := ⊡F, lines 1125-1129). Nearest literature: Ockhamist branching-time logic, where □ quantifies over branches through the current moment exactly as ⊡ quantifies over ⟨τ⟩_x -- Zanardo 1991 (complete deductive system for Since-Until Ockhamist logic, Burgess/Gabbay-style irreflexivity rules), Reynolds, Venema 2001 §4 -- with the differences that task frames also carry the global □ over all of H_F, the MF interaction axiom, and a fixed duration group. DELIVERABLES: (1) the candidate axiom set for TM⋆ over task frames and per frame class, each candidate validated or refuted against the real semantics by lean_run_code probes (a sorry-free probes file under this task's directory, in the manner of specs/511_*/02_probes.lean, is the evidence of record); (2) the completeness strategy: canonical-model design (candidate: world states := ⊡-equivalence classes of maximal consistent sets, task relation := some pair of histories through the two classes; the six TaskFrame axioms nullity_identity, comp, converse, serial, limit, saturation must be re-verified), which literature technique carries over, and an honest per-class feasibility verdict -- research-grade obstructions named precisely, never assumed away; (3) the non-definability argument for ⊡ in L⁺ on paper, ready for transcription: the bisimulation notion appropriate to task models (histories, shared world states, the global □) and two models or two evaluation points that agree on every L⁺-formula but differ on a ⊡-formula (p → ⊡p is valid for atoms, so the separating formula must be temporal, e.g. ⊡Fp versus □Fp on histories that share a world state at x but diverge afterwards, alongside a history that does not intersect them); (4) which conservative-extension results the addition of ⊡ permits beyond the both-direction TM⋆/TM⁺ result task 533 delivers: composed rows over TMFrag and TM, anything TM⋆ completeness would transfer back to the L⁺ level, and the logic of the defined modals Will/will/Could/could and of Determined φ → ⊡φ over deterministic frames; (5) an engineering recommendation binding on task 533's plan: whether StarAxiom should be parameterized over the ⊡-axiom set or closed with a one-lemma-per-new-constructor soundness discipline, and whether the TD/swap soundness case should be discharged semantically (a stab case in the TruthAntiIso pattern) or proof-theoretically. Consult the Literature/ corpus via --lit (venema_2001, venema_1993_since_until, burgess_1982*, burgess_1984) and survey online sources for Ockhamist Since/Until axiomatizations and any formalized branching-time completeness.

---

### 534. Hg fragment finite axiomatizability
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: incompleteness
- **Dependencies**: Task 533

**Description**: Research and, where feasible, establish in Lean whether the H/G-fragment of TM⁺ is finitely axiomatizable natively in the tense-only language L (primitive tense operators H and G) -- Kamp/Burgess territory. THE OBJECT: TMFrag fc φ := TM⁺ ⊢_fc tr φ, the H/G-fragment of TM⁺ delivered by task 533 (Metalogic/Conservativity/Fragment.lean), which by the fragment completeness theorem is exactly Log_{H,G}(fc), the set of H/G-sentences valid over the frame class fc, for each of Base, Dense, Discrete, Dedekind. KNOWN: TM ⊊ TMFrag at Discrete (witness Z1, machine-checked: not_bl_derivable_z1, z1_translate) and at Base (witness the splitting schema (DD), formerly (Sp), refuted in source); by tmComplete_iff_forward these gaps are exactly TM's semantic incompleteness. THE QUESTION: for each class fc, is there a FINITE set Σ_fc of H/G-schemas (or at least a recursive set) with TM + Σ_fc = TMFrag_fc? Candidates: (DD); Z1-type backward-induction schemas; the classical H/G axiomatizations of linear discrete/dense/complete flows of time (Burgess 1982 Axioms for tense logic I and II; Burgess 1984 handbook chapter; Kamp 1968; Gabbay-Hodkinson-Reynolds 1994; Prior), adapted to the bimodal setting where □ ranges over all world histories of a single task frame with the MF interaction axiom and every history shares one temporal order (so Log(all task frames) = Log(Discrete) ∩ Log(Dense) and (DD) is a split validity -- see the Halldén analysis in PossibleWorlds tasks 72 and 82, which record that completeness of TM + (DD) turns on whether TM_f and TM_d axiomatize their classes, both open). Consult the Literature/ corpus (burgess_1982, burgess_1982_ii, burgess_1982b, burgess_1984, venema_1993_since_until, venema_2001) via --lit and survey online sources. DELIVERABLES: a per-class verdict (finitely axiomatizable / recursively axiomatizable / open with the precise obstruction named), a candidate axiom set Σ_fc, and the machine-checked partial results that are honestly obtainable: soundness of TM + Σ_fc relative to TMFrag_fc (i.e. TM + Σ_fc ⊆ TMFrag_fc) and either a completeness proof (canonical model or filtration in the H/G language) or a separating H/G-validity showing TM + Σ_fc ⊊ TMFrag_fc. A negative or open verdict with evidence is a complete outcome. HARD CONSTRAINT: never state a completeness or conservativity theorem and discharge it with sorry. PAPER DEPENDENCY: the paper (PossibleWorlds, possible_worlds.tex, sub:Logic, the footnote following "TM owes its strength to since and until", currently commented out) waits on this task. The paper wants to assert that the Past/Future language admits no complete finite axiomatization of the fragment, and the footnote stays commented out until a negative verdict is established here. Note the claim must be non-FINITE-axiomatizability: the fragment is r.e. via TM+, so a recursive axiomatization exists trivially. A positive or open verdict must also be reported back so the footnote can be reworded to match.

---

### 531. Docgen publication and automation suite triage
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: metalogic
- **Dependencies**: Task 529, Task 530
- **Research**: [531_docgen_publication_and_automation_suite_triage/reports/01_docgen-publication-automation-triage.md]
- **Plan**: [531_docgen_publication_and_automation_suite_triage/plans/01_docgen-publication-automation-triage.md]
- **Summary**: [531_docgen_publication_and_automation_suite_triage/summaries/01_docgen-publication-automation-triage-summary.md]

**Description**: WAVE 5 (publication infrastructure). Publish the API documentation, adopt the repository furniture mature Lean libraries carry, and triage the bespoke automation suite by evidence. Findings E-08, G-09, G-10, G-11, G-14, G-16, D-02, D-17 in specs/reviews/2026-09-01-lean-engineering/{E-docs,G-ecosystem,D-tactics}.md; High H8/H9 and the 'Ecosystem alignment' section of the review (G-ecosystem section 8 is the seven-step packaging recipe). MEASURED STATE: docs/README.md:271-279 documents `lake build :docs` for doc-gen4 output, but lakefile.lean has no doc-gen4 requirement and lake-manifest.json has zero matches -- the 90%-documented core scope is published nowhere; no references.bib (Reynolds, Blackburn-de Rijke-Venema, Kamp, Prior are cited in prose, e.g. ProofSystem/Axioms.lean's sep docstring quotes a printed page), no ORGANISATION.md/NOTATION.md (compare leanprover/cslib), no MainResults page -- though DiscreteNonCompactness.lean:292-312 and DedekindNonCompactness.lean:473-490 already demonstrate the pattern (headline theorems followed by #print axioms with the verbatim output recorded); leanprover-community/docgen-action builds doc-gen4 + a Jekyll homepage and deploys to GitHub Pages in ~10 lines of YAML (teorth/pfr is the reference layout). The bespoke tactic suite (Automation/Tactics/ 2,260 lines + Normalization.lean 1,336 + AesopRules.lean 285) is invoked at most 4 times by the library it was written for (FormalSystem.lean:64, Examples/BimodalProofs.lean:219,223,231, all modal_search); 14 of 26 declared tactics have zero library AND test uses; the only production custom tactics are the six EF-game ones in WeakCanonical/EFGameTactics.lean (68 sites); Helpers.lean (1,210 lines) mixes user tactics (:109-515), reusable MetaM plumbing (:516-1000, the only part PropDecide/Deduction reuse) and a search engine (:545-1210) that is ProofSearch/'s business. Naming: 98 non-namespaced Uppercase_x theorem names (CanonicalTask_backward_comp → CanonicalTask.backward_comp, Fib_eq_singleton, Succ_implies_CanonicalR, …) and 141 `lemma` against 7,031 `theorem`. WORK: (1) `require «doc-gen4»` matching lean-toolchain, or the docgen-action workflow (permissions contents:read / id-token:write / pages:write; `api-docs: true`, `references: references.bib`, `blueprint: false`); Pages source = GitHub Actions; link the generated docs from README.md above 'Documentation'; delete or fix the broken docs/README.md recipe. (2) references.bib at the root; convert prose citations in ## References sections to keys. (3) FormalSystem/MainResults.lean restating soundness, the four weak completeness theorems, consequence completeness, strongCompletenessBase/Dense, compactBase/Dense, the two non-compactness refutations, the Galois closure results, kampPriorExpressiveCompleteness and decidability's sound_of_isValid, each followed by #print axioms with output recorded, and wired into C2 so drift fails the build; this is also the artefact task 178's examples should cite -- hand it to 178. (4) ORGANISATION.md (the Syntax/ProofSystem/Semantics/Metalogic/Automation layering and the one documented Semantics→ProofSystem edge) and NOTATION.md; consider per-logic judgement notation tags `TM[...]` since the repo carries four ⊨-shaped relations (G-16). (5) Automation-suite triage (D-02): promote propDecide (done by 528) and deduction/undischarge (trial the tactic form on Core/DeductionTheorem.lean's hot spots); keep modal_search as the pedagogical entry point and say so; retire temporal_search, propositional_search, tm_auto, modal_4_tactic, modal_b_tactic, modalNormAt, modalNormAll, modalFold and the SearchConfig weight machinery to Boneyard/ unless a benchmark justifies them; split Helpers.lean into Tactics/{UserTactics,Meta,Search}.lean; regenerate Automation/README.md and Tactics/README.md from the surviving inventory (D-14). (6) Mechanical rename of the 98 Uppercase_x names to dot-namespaced form and the 141 lemma → theorem (do after tasks 519/520 so the dead ones are gone), guarded by a new invariant check. (7) NAMING: nested-namespace shadowing (added 2026-09-04 from a survey run during the CI/linter-gates work). A repo-wide scan of live scope (Boneyard excluded) found ~16 genuine cases where a BARE declaration in an outer namespace shadows a same-named bare declaration in a nested inner namespace, so the outer one silently wins at any site that opens the inner namespace. DO NOT treat ordinary structure-member namesakes as part of this: `Syntax.Atom.beq_refl` vs `Syntax.Formula.beq_refl`, and the `toJson`/`display`/`empty`/`size`/`insert`/`mono`/`lift` families, are idiomatic Lean dot-notation on distinct types and must be left alone -- roughly half the raw scan hits are of that benign kind. The genuine cases, grouped by the idiom that produced them: (a) INNER RESULT RE-EXPOSED AT AN OUTER NAMESPACE UNDER THE SAME NAME -- `FormalSystem.Metalogic.completeness_dense` (StrongCompleteness.lean:987, type `WeakCompleteness FrameClass.Dense`) shadows `FormalSystem.Metalogic.BXCanonical.completeness_dense` (BXCanonical/Completeness.lean:255, type `(phi : Formula) : ValidDense phi -> Derivable FrameClass.Dense [] phi`), and identically for `completeness_discrete` (StrongCompleteness.lean:1101 vs BXCanonical/Completeness.lean:296); the same idiom recurs for `F_until_equiv_valid`, `P_since_equiv_valid`, `temp_linearity_valid` and `temp_linearity_past_valid` (all `FormalSystem.Metalogic` in Soundness.lean shadowing `FormalSystem.Metalogic.SoundnessLemmas` in SoundnessLemmas/FrameClassVariants.lean), and for `temporal_truth_and`/`temporal_truth_neg` (`WeakCanonical` in StaviConnectives.lean shadowing `WeakCanonical.Kamp` in Kamp/Translation.lean). Note `WeakCompleteness fc` unfolds to `forall psi, ValidIn fc psi -> Derivable fc [] psi` (SetConsequence.lean:234), so the shadowing and shadowed forms really are the same claim in bundled and unbundled form -- which is precisely why they warrant DISTINGUISHING names rather than a shared one. RECOMMENDED FIX for this group: rename the inner, unbundled members to Mathlib's `conclusion_of_hypothesis` convention, which is both collision-free and more self-describing -- `BXCanonical.completeness_dense` -> `BXCanonical.derivable_of_validDense`, `BXCanonical.completeness_discrete` -> `BXCanonical.derivable_of_validDiscrete`, and analogously for the SoundnessLemmas and Kamp pairs. Do NOT rename the outer `completeness_base`/`_dense`/`_discrete`/`_dedekind` family: its four-member uniformity is the more valuable pattern and renaming two of four to dodge a collision would damage it. Where the intent is genuinely pure re-exposure rather than restatement at a different type, prefer Lean's `export` mechanism over a second declaration. (b) UNRELATED BARE COLLISIONS, each needing a judgement call rather than a mechanical rule: `insertEnv` (WeakCanonical/MonadicFO.lean:360 vs WeakCanonical.Kamp in Kamp/NfDepth0Generalized.lean:48), `realOrder` (Metalogic in DedekindNonCompactness.lean:318 vs Metalogic.Independence in Independence/RealTranslationFrame.lean:99), `pastKDist` (Theorems in GeneralizedNecessitation.lean:114 vs Theorems.Perpetuity in Perpetuity/Principles.lean:664), `allAxiomNames` (Automation in AxiomNames.lean:33 vs Automation.ProofStepExport in ProofStepExport.lean:1526), and `hasBox`/`isNeg`/`isTop` (Automation in FormulaEnumerator.lean vs Automation.FormulaMutator / Automation.InterestingnessMetrics). (c) A SEPARATE AND MORE SERIOUS FINDING worth checking first: `mem_knownTimes_of_mem` appears TWICE under the SAME fully-qualified namespace `FormalSystem.Metalogic.Decidability`, from two different files (CountermodelExtraction.lean:415 and Verified/Termination/MintBound.lean:1344), with a third at `Decidability.Verified.Bridge` (Bridge/BoxSaturation.lean:261); `mem_knownWorlds_of_mem` has the same shape (MintBound.lean:2469 vs Bridge/BoxSaturation.lean:255). Two live declarations sharing one fully-qualified name is a different and stronger problem than shadowing -- determine whether one is private/sectioned or whether the two files are simply never imported together, and resolve accordingly. GUARD: extend the invariant check this item already introduces for the Uppercase_x and lemma renames to also flag NEW nested-namespace shadowing of bare (non-structure-member) declarations, so the class does not regrow; it must not flag structure-member namesakes, which are legitimate. CONTEXT: this shadowing already degrades tooling -- C17's dead-declaration census in scripts/check-module-invariants.sh keys on the last dot-segment, so any two declarations sharing a base name mask each other's occurrences and neither can ever be reported dead; and docs/theorem-index.md must use fully-qualified names throughout precisely because `completeness_dense` alone does not identify a row. ACCEPTANCE: a public doc-gen4 site linked from README.md; MainResults.lean compiles with every #print axioms matching C2; references.bib consumed by the docs build; zero declared tactics with zero library-and-test uses outside Boneyard/; lemma count 0; lake build green.

---

### 530. Documentation single source of truth theorem index
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: metalogic
- **Dependencies**: Task 518, Task 524
- **Research**: [530_documentation_single_source_of_truth_theorem_index/reports/01_documentation-single-source-of-truth.md]
- **Plan**: [530_documentation_single_source_of_truth_theorem_index/plans/01_documentation-single-source-of-truth.md]
- **Summary**: [530_documentation_single_source_of_truth_theorem_index/summaries/01_documentation-single-source-of-truth-summary.md]

**Description**: WAVE 5 (publication infrastructure). Make status and counts machine-owned, create the theorem index a paper reader needs, and purge history/process prose from publication-facing docstrings. THIS TASK IS A DEPENDENCY OF TASK 177 (the gated post-decidability docs polish); it is the un-gated metalogic half. Findings E-04..E-22, B-14..B-17, A-10, A-11, A-18, D-14, F-21, G-07, G-09 in specs/reviews/2026-09-01-lean-engineering/{E-docs,B-completeness,A-soundness,D-tactics,F-canonical,G-ecosystem}.md; High H8 (documentation half) and the 'Documentation architecture' section of the review, whose policy table is the specification. MEASURED STATE: Metalogic.lean asserts SORRY-FREE for 37 declarations of which C2+C14 machine-pin 8 (33 prose-only claims, restated in 1-3 further places each -- the mechanism by which README.md:167 and typst/FormalFoundations.typ went stale); the four-row status ledger exists in six drifting copies (Metalogic.lean:45-47 says 'the two countermodels remain outstanding' while Conservativity.lean:159-166 says CEF landed; Metalogic.lean:110-113 is a dangling edit fragment); ~40 numeric claims are stale across README.md, FormalSystem/README.md, Metalogic/README.md and Metalogic.lean:224-256 (Decidability 19 vs 62 files, WeakCanonical 135 vs 179, 'Ten loose files' above an eleven-row table, 'two Boneyards' vs the one B0 asserts); four multi-sentence paragraphs are duplicated verbatim between README.md and Metalogic.lean; 45 lines of refactor archaeology sit in StrongCompleteness.lean/SetConsequence.lean docstrings ('before this collapse there were four byte-identical definitions', 'pre-collapse binder shape'; StrongCompleteness is 69% prose, Conservativity 80%); 19 change-log phrasings on live README surfaces; 6 of 16 file.lean:NNN citations in the five main metalogic files point at the wrong line; Soundness.lean:76 and SoundnessLemmas/Core.lean:40 assert TruthAt takes a Set.univ argument it lacks; Semantics.lean's truth-clause table shows a five-argument TruthAt with H/G clauses and lists Nullity as a frame axiom that README.md:82 calls derived; Automation/README.md's line counts are wrong by 2-5x with 13 of 27 modules missing and 26 stale `Bimodal.*` references survive in 14 READMEs; three source files (BLSchemaValidity.lean:40-41,15; BLValidity.lean:260; BaseLanguageSoundness.lean:310) cite an ephemeral specs/NNN report path against the repo's own rule; the twelve flagship completeness/compactness theorems carry no paper anchor at the declaration site though the Semantics/Correspondence layers do this well; no docs/theorem-index.md, no CITATION.cff (and the README's BibTeX has year 2025 vs 2026 in the article entry), no docs/ARCHITECTURE.md layer diagram; README.md:150-152 says `cd ProofChecker` after cloning BimodalLogic; Independence/README.md:30 cites `co_not_derives_prior_U`, which does not exist. WORK: (1) POLICY (E-14, review section 'Documentation architecture'): axiom sets owned by C2/C14 -- extend the baseline from 8 to every flagship declaration; counts owned by a new `check-module-invariants.sh --emit-inventory` writing `<!-- BEGIN GENERATED -->` blocks into Metalogic/README.md and the other inventories; per-theorem status owned by ONE ledger, docs/theorem-index.md (schema: paper label · statement · Lean name · file (no line numbers) · frame class · axioms-generated), seeded from the 16 rows + continuation list in E-docs section 5.2, with a Notation-and-naming table (E-20) mapping paper term → Lean identifier; every other surface carries a pointer and a ≤5-row highlights table. Delete Metalogic.lean:224-256 outright (E-04). (2) Add a one-line `Paper: <anchor>` to the doc comment of each flagship declaration in StrongCompleteness/Compactness/DiscreteNonCompactness/DedekindNonCompactness using the anchors pinned in specs/paper-definitions-of-record.md, and extend C15 to assert every theorem-index row carries one (E-22). (3) Three-register docstring cleanup across the core scope (A-18/B-16): doc comments state what IS, present tense, with paper anchor and caller traps; rejected alternatives and layering rationale move to docs/decisions/*.md ADRs (Metalogic/README.md's 'Why There Is No Physical Regroup', the archive-consolidation narrative, the validity_decidable retirement told in four places); 'formerly a sorry' / 'before this delta' / 'earlier revisions of this docstring' prose is deleted (git log is the history). Target: halve prose in Validity.lean, FrameClassValidity.lean, StrongCompleteness.lean, SetConsequence.lean, Conservativity.lean without losing a mathematical claim. (4) Standing convention: cite declaration names, never file:line, in docstrings and READMEs; fix the 16 existing citations in the five main files and the stale ones in docs/reference/API_REFERENCE.md. (5) Fix every verifiable mismatch listed above (A-10, A-11 durable anchors, B-17, E-11, E-17, E-18, E-19, D-14's Bimodal.* sweep and Automation READMEs regenerated from readme-inventory.sh, E-07/C-20 contents tables, E-06 stamps, E-10 typst sorry-table label). (6) CITATION.cff (reconcile the year); docs/ARCHITECTURE.md with one layer diagram naming both upward edges (Semantics→ProofSystem via FrameClassValidity; Decidability→Automation); a `## Verifying the main theorems` section in README.md with the #print axioms snippet and the invariant-script one-liner; `## Tags` lines in the ~30 files a reader would search (G-07). (7) Generate typst's per-declaration axiom table from typst-status-counts.sh rather than by hand. ACCEPTANCE: zero hand-typed file/line counts on the four status surfaces; every SORRY-FREE claim in Metalogic.lean machine-pinned; docs/theorem-index.md exists with every flagship result and resolves under the C17 name-resolution check (task 529); C14/C15 pass with the extended baselines; readme-lint.sh reports zero stale stamps; grep for 'before the collapse|formerly a strategic sorry|earlier revisions of this docstring|used to live' returns zero hits on live surfaces.

---

### 506. Fix typst display defects via playwright visual loop
- **Status**: [NOT STARTED]
- **Task Type**: typst
- **Topic**: publication-quality
- **Dependencies**: None

**Description**: Fix all outstanding display/layout defects in the compiled typst documents (typst/FormalFoundations.typ and typst/BimodalReference.typ) using a Playwright-driven visual check loop. Known defect: in <sec:representation> Definition 5.1 (TM+-algebra), the display equation listing the derived operators (F a := 1 ▷ a, G a := ¬F(¬a), P a := 1 ◁ a, H a := ¬P(¬a), Next a := 0 ▷ a, △a := H a ∧ a ∧ G a) is set as one unbreakable math line and overflows both the definition box and the page margins; it must be broken across lines (e.g. an aligned block or a two-row layout) so it fits within the text block. Approach: compile each document to PDF (and/or SVG/PNG pages via `typst compile --format png`), serve the output to a headless browser via the Playwright MCP tools, screenshot every page, and systematically inspect for overflowing display math, content escaping theorem/definition boxes, text running past margins, clipped tables, orphaned headings, broken cross-references or citation placeholders, and any other visual defect. Catalogue every finding with page number and source line, then plan and implement fixes in the .typ sources (line-breaking long equations, resizing tables, adjusting box widths, etc.), recompiling and re-screenshotting after each fix and repeating the full sweep until no display issues remain. Both documents must compile cleanly and scripts/typst-sync-check.sh must pass at the end. Do not change mathematical content — layout only

---

### 504. Retry acquisition of missing representation sources
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: literature
- **Dependencies**: None

**Description**: Retry acquisition of the standard modal-representation sources that the representation-section literature research could not obtain because Semantic Scholar (literature-discover.sh Tier 3) was rate-limited (HTTP 429) for the whole session: Sambin & Vaccaro 1988 "Topology and duality in modal logic"; S. K. Thomason 1972 "Semantic analysis of tense logics" and 1975 "Categories of frames for modal logic"; Goldblatt 1976 "Metamathematics of modal logic" I-II; Fine 1975 "Some connections between elementary and modal logic"; Gehrke & Jonsson 2004 "Bounded distributive lattice expansions" (mscand.dk URLs 404; proxy gehrke_vosmaer_2011 already ingested); Gabbay & Shehtman "Products of modal logics I"; Marx & Venema 1997 "Multi-dimensional modal logic" (Zotero metadata only, no PDF). Use /literature "<title>" or literature-discover.sh once Tier 3 recovers (or after the S2_API_KEY / multi-provider fallback lands in the literature extension), ingest what is open-access or in Zotero, record paywalled items honestly as not acquired, and register every acquired doc in specs/literature-index.json with reason and citation_rule fields following the existing entries. Evidence and the full standard-sources checklist are in specs/503_revise_representation_section_with_literature/reports/01_representation-literature-research.md sections 2.2-2.3

---

### 502. Ground algebraic representation in goldblatt and brv
- **Effort**: 12-20 hours
- **Status**: [NOT STARTED]
- **Task Type**: formal
- **Topic**: algebraic-representation
- **Dependencies**: Task 461

**Description**: RESEARCH TASK. Ground the algebraic representation front in the literature BEFORE the STSA axiom set is fixed and before Uf(A) is constructed. Gates the STSA port; the complex-algebra and ultrafilter-frame tasks inherit the gate transitively.

WHY THIS RUNS EARLY. Goldblatt 1989 is largely about which varieties of Boolean algebras with operators are complex algebras, and about canonicity. Those are design questions for the STSA axiomatization and for the Uf(A) construction, not questions the eta-embedding capstone can act on. On the pre-existing graph this paper was ingested in wave 1 and not opened until wave 4, by which point three tasks would have committed to designs it should have informed.

PRIMARY SOURCE, WITH A HARD READING CONSTRAINT. Goldblatt, R. "Varieties of complex algebras", Annals of Pure and Applied Logic 44 (1989) 173-242, doi 10.1016/0168-0072(89)90032-8. The acquired PDF is an Acrobat 3.0 Capture scan (70 pages) whose OCR text layer is UNRELIABLE ON MATHEMATICS: symbols mangle, lines drop and reorder, and even the title page renders New Zealand as "New 2Miand". READ THE PAGE IMAGES via the Read tool's pages parameter. Do NOT grep the text layer for definitions or theorem statements, and do NOT accept a pdftotext- or /literature --convert-derived markdown as a faithful source for any axiom or equation. The text layer is usable only as a rough locator.

PAGINATION. Journal page 173 is PDF page 1, so PDF page = journal page - 172. The paper's own table of contents is partly OCR-garbled in its page-number column; verify each section start against the actual page image rather than trusting the offsets below.

SECTIONS IN SCOPE (do not read the whole paper):
- 2.2 The dual space of a lattice (journal ~185) and 2.3 Bounded morphisms (~192) -- the duality machinery the eta embedding rests on.
- 3.1 Canonical structures (~198) -- the canonical extension / Uf(A) construction. Bears directly on the ultrafilter-frame task.
- 3.5 Canonical varieties (~208) -- IS THE STSA VARIETY CANONICAL? This is the single most load-bearing question for the STSA port, which must restate three Boneyard sorries against the current 45-constructor axiom set and should not do so blind.
- 3.6 The elementary case (~210) and 3.8 First-order definability -- bears on whether the Spherical frame condition is first-order definable and preserved, which is the ultrafilter-frame task's dominant and explicitly unattempted obligation, and one the paper's finite-W discharge pattern does not cover.
- 4.2 Preservation by bounded morphisms and inner substructures (~229) -- whether the TaskFrame axioms transfer along the constructions.
EXPLICITLY OUT OF SCOPE: 2.4 Heyting algebras (intuitionistic, not this signature).

CROSS-FRONT NOTE, RECORD BUT DO NOT PURSUE HERE: section 4.3 covers preservation by DISJOINT UNIONS, which may bear on the two-fibre structure named in Metalogic/Conservativity.lean as the CEB countermodel shape. That belongs to the TM-completeness research task on the metalogic front; if 4.3 looks relevant, record a pointer for that task rather than expanding this one.

SECONDARY SOURCE: Blackburn/de Rijke/Venema 2002 Chapter 5 (corpus entry blackburn_2002, born-digital, full text) is the standard Jonsson-Tarski reference and should be read alongside. CAVEAT: the corpus warns this entry is 365,868 tokens and exceeds a single context budget -- create a chapter-scoped sub-entry before an agent consumes it.

DELIVERABLE: a grounding report answering, with citations to specific pages read as images: (1) does the STSA axiom set as seeded in Boneyard/UltrafilterFrame/TenseS5Algebra.lean match the standard BAO presentation, and where does it diverge; (2) is the variety canonical, and what does that buy or cost the representation; (3) what the literature says about discharging a Spherical-style frame condition on an ultrafilter frame; (4) a concrete recommendation on how the three removed-axiom sorries (temp_a, temp_l) should be restated against the current axiom set. A finding that the literature does NOT settle one of these is a complete and valid answer for that item -- record it as unsettled rather than manufacturing a verdict.

---

### 501. Extend stsa with until since operators
- **Effort**: 20-32 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: algebraic-representation
- **Dependencies**: Task 125

**Description**: Phase 4 of the Jonsson-Tarski representation: extend STSA with the binary Until and Since operators. The STSA class as seeded in Boneyard/UltrafilterFrame/TenseS5Algebra.lean carries only the unary box, G, H and sigma. The live object language's primitives are untl and snce (Formula, Syntax/Formula.lean), with allFuture and allPast DERIVED from them (:167, :177) -- so an STSA over the unary fragment alone does not represent the actual logic, and the representation theorem is incomplete without this. SCOPE: add binary operators to the STSA signature with their algebraic laws, extend the complex algebra Cm(F) to interpret them from the frame relations, extend the ultrafilter frame Uf(A) correspondingly, and re-prove the eta embedding at the extended signature. SEQUENCING: this deliberately follows the unary capstone rather than being folded into it -- the unary representation is a standalone result worth landing first, and folding the binary case in would make a single task that cannot complete in one dispatch. LITERATURE: Blackburn/de Rijke/Venema 2002 Chapter 5 (in the corpus as blackburn_2002, full text) is the standard reference for Jonsson-Tarski and its extensions to n-ary operators. Note the corpus warns blackburn_2002 exceeds a single context budget at 365,868 tokens -- a chapter-scoped sub-entry should be created before an agent consumes it.

---

### 500. Reconcile shiftset representation with stsa route
- **Effort**: 10-16 hours
- **Status**: [NOT STARTED]
- **Task Type**: formal
- **Topic**: algebraic-representation
- **Dependencies**: Task 492, Task 497

**Description**: RESEARCH TASK. Prevent two parallel representation theorems from being developed and having to be reconciled after the fact. THE OBSERVATION: FormalSystem/Semantics/ShiftSet.lean -- landed by task 424 for the COMPACTNESS route -- is already a representation theorem. forward_repr (:263) and reverse_repr (:362) represent task models as shift sets, both directions, sorry-free. Separately, the STSA design report (specs/archive/992_shift_closed_tense_s5_algebra/reports/01_stsa-algebraic-analysis.md) identifies its key structural claim as: box a <= box(G a) meet G(box a) says the box-fixed points form a G-invariant subalgebra, which is the algebraic encoding of OMEGA BEING SHIFT-CLOSED. That is the same shift structure ShiftSet.lean makes explicit. These look like two views of one representation. SCOPE: determine whether they are, and if so, specify the shared infrastructure so the algebraic route consumes ShiftSet rather than duplicating it. Concretely: (a) is Cm(F) expressible as an algebra of shift-invariant subsets of a ShiftSet carrier? (b) does ShiftSet's sep hypothesis correspond to an STSA axiom, and if so which? (c) can the eta embedding be factored through reverse_repr? DELIVERABLE: a report with a verdict and, if affirmative, a concrete refactor specification. A NEGATIVE VERDICT IS A COMPLETE OUTCOME -- if the two representations are genuinely different objects, say so with evidence and record it so the question is not reopened. TIMING: run this after the Los-lemma work and the STSA port have both landed, so both sides are concrete rather than projected.

---

### 499. Build ultrafilter frame and prove task frame axioms
- **Effort**: 24-40 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: algebraic-representation
- **Dependencies**: Task 497

**Description**: HARD. Phase 2 of the Jonsson-Tarski representation: the ultrafilter frame Uf(A), and the proof that it is a TaskFrame. THE SEED: Boneyard/UltrafilterFrame/UltrafilterFrame.lean (1189 lines, behind #exit, 4 sorry hits) already has R_G (:82), R_Box (:90), R_H (:98) and a substantial body of proved structure -- R_Box_refl (:111), R_Box_euclidean (:127), R_Box_symm (:154), R_Box_trans (:164), R_G_R_H_converse (:179), the preimage and upward-closure lemmas (:229-251), R_G_trans (:281), R_H_trans (:304), and the F/P resolution lemmas (:515, :750). Port and revive rather than rebuild. THE GENUINELY NEW OBLIGATION, flagged in task 125's own FOUR-AXIOM EXPOSURE NOTE (2026-08-10): proving SPHERICAL for an ultrafilter frame is nontrivial and unattempted, and the paper's finite-W discharge pattern EXPLICITLY DOES NOT APPLY. Budget this as the dominant cost of the task; Compositionality, Seriality and Limit are expected to be far cheaper. MATHLIB HOOKS: Order/PrimeSeparator.lean:44 (DistribLattice.prime_ideal_of_disjoint_filter_ideal -- the Boolean prime ideal theorem in distributive-lattice form) is what a Zorn-free Uf(A)-nonemptiness argument should use; Order/Ideal.lean and Order/PrimeIdeal.lean (:156, :171) give the ultrafilter-as-prime-filter characterization. NOTE: Mathlib has NO Ultrafilter on an abstract Boolean algebra -- its Ultrafilter is Filter-on-Set-based. UltrafilterMCS.lean:44 rolls its own structure for exactly this reason, and its MCS-to-ultrafilter bijection (ultrafilter_correspondence :782) is available, though stated existentially rather than as a named Equiv. SHADOWING HAZARD: if Mathlib's Ultrafilter is opened in that namespace it collides with the bespoke one; keep them explicitly qualified.

---

### 498. Build complex algebra for task frames
- **Effort**: 16-24 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: algebraic-representation
- **Dependencies**: Task 497

**Description**: Phase 1 of the Jonsson-Tarski representation: the complex algebra Cm(F). Construct the powerset STSA over a TaskFrame -- carrier the powerset of the world-history space, with box, G, H and sigma defined from the frame relations -- and prove it satisfies every STSA axiom. GREENFIELD WARNING: Mathlib has NO Boolean algebras with operators, no complex algebras, no canonical extensions, and no modal-algebra machinery of any kind; a survey of the pinned v4.33.0-rc1 tree found nothing reusable for this. What Mathlib DOES supply and should be used: Order/BooleanAlgebra/ (already consumed by BooleanStructure.lean:421) and Order/CompleteBooleanAlgebra.lean:711 (CompleteAtomicBooleanAlgebra). CONSTRAINT FROM THE FOUR-AXIOM WORK (task 420, completed): TaskFrame (Semantics/TaskFrame.lean:474-577) now carries SEVEN fields, not five -- biconditional Compositionality, Seriality, Limit and Spherical plus a Nonempty WorldState field and [Nontrivial D]. The complex algebra must be built against the live seven-field structure, not the five-field shape the older design documents assume. ACCEPTANCE: Cm(F) defined, instance STSA (Cm F) proved, sorry-free, lake build green.

---

### 497. Port stsa class and add g operator
- **Effort**: 16-24 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: algebraic-representation
- **Dependencies**: Task 496, Task 502, Task 528

**Description**: Bring the Shift-closed Tense S5 Algebra class into live code and close the G-operator gap. Phase 1 groundwork for the Jonsson-Tarski representation. THE SEED: Boneyard/UltrafilterFrame/TenseS5Algebra.lean (361 lines, behind #exit) already contains the full class STSA extending BooleanAlgebra with fields box, G, H, sigma and axioms box_deflationary, box_monotone, box_idempotent, box_s5, G_monotone, H_monotone, sigma_involution, sigma_neg, sigma_sup, sigma_G, sigma_H, sigma_box, MF, TF, TA, TL. This is the exact algebraic signature the representation needs. IT CARRIES 3 SORRIES, AND THEY MUST NOT BE PROVED AS-IS: they are for temp_a and temp_l, axioms that have since been REMOVED or restructured; restate them against the current 45-constructor ProofSystem.Axiom set (Axioms.lean:115-464) rather than reviving the old shapes. THE G GAP: LindenbaumQuotient.lean supplies boxQuot (:305-ish), hQuot, and sigmaQuot (:346) with its four laws (sigma_quot_involution :353, sigma_quot_neg :362, sigma_quot_sup :373, sigma_quot_box :385) -- but there is NO gQuot. G on the Lindenbaum quotient must be constructed and its congruence proved before LindenbaumAlg can be an STSA instance. Boneyard/SorriedDeclExcisions/AlgebraicGQuotChain.lean is the excised prior attempt and should be consulted, not trusted. DESIGN REFERENCE: specs/archive/992_shift_closed_tense_s5_algebra/reports/01_stsa-algebraic-analysis.md (538 lines) gives the full axiom-to-equation translation table and the key structural claim that box a <= box(G a) meet G(box a) says the box-fixed points form a G-invariant subalgebra -- the algebraic encoding of Omega being shift-closed. It is stale on file names (references deleted AlgebraicRepresentation.lean and ParametricRepresentation.lean) but sound on the mathematics. ACCEPTANCE: STSA class live and sorry-free, gQuot constructed with congruence, instance STSA LindenbaumAlg, lake build green.

=== DEPENDENCY ADDED 2026-09-01 ===
Task 528 (Algebraic/ modernisation: propDecide in BooleanStructure.lean, SetMaximalConsistent.ultrafilterEquiv as a named Equiv, the bespoke `Ultrafilter` structure reconciled with Mathlib Order.PFilter/Ideal.IsPrime, Multiset.inf; from specs/reviews/review-2026-09-01-lean-engineering.md findings D-08, F-11, F-12, F-13) must land first so this task builds on the modernised algebra rather than inheriting a shadowed Ultrafilter name and ~430 lines of hand-built Boolean algebra.

---

### 482. Discharge proof extraction completeness
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 412

**Description**: CLASSIFICATION: OPEN MATHEMATICS, multi-month. This MUST NOT be re-described as engineering, and must not be scheduled or budgeted as a routine task.

TARGET: eliminate `.extractionFailed` as a live outcome of `decide` on a genuinely closed tableau. Currently `verifyProof` is `fun _ _ => true` (`FormalSystem/Metalogic/Decidability/ProofExtraction.lean:345`, honestly commented, misleadingly named) and no theorem establishes that a closed tableau ALWAYS yields an extractable Hilbert-system derivation. `ProofExtraction.lean` has zero theorems today (re-confirmed at task 468 realignment time, 2026-08-25).

WHAT THIS REQUIRES: the missing refutation induction (`allClosed → Derivable`, the content that would live under `FormalSystem/Metalogic/Decidability/Verified/Refutation/` -- this directory does not exist today, zero files, re-confirmed 2026-08-25) is a PREREQUISITE owned by task 412, which already targets exactly this induction (`allClosed_derivable`). This task is sequenced AFTER 412 rather than folded into 412's acceptance criteria as an additional corollary, precisely so the research problem is not hidden behind 412's engineering-shaped description -- see the planner's decision recorded in task 468's implementation plan (`specs/468_realign_task_programme_from_proof_state_audit/plans/01_programme-realignment-execution.md`, "Planner decisions taken here" item 1). Task 412's own description carries a one-line REVISE naming this task as the owner of `.extractionFailed` elimination.

DEPENDENCIES: `[412]`.

FILE SCOPE: `FormalSystem/Metalogic/Decidability/ProofExtraction.lean`,
`FormalSystem/Metalogic/Decidability/Verified/Refutation/` (does not yet exist -- this task or a predecessor may need to create it).

DO NOT schedule this as an independent parallel effort that would redundantly re-derive the refutation induction 412 already targets -- consume 412's `allClosed_derivable` once it lands.

ACCEPTANCE: `.extractionFailed` is unreachable on a genuinely closed tableau (stated and proved as a corollary of `allClosed_derivable` or equivalent); `lake build` green; no regression to any currently-passing check-module-invariants.sh check; `verifyProof` either proved correct against the new theorem or replaced by an implementation whose correctness the new theorem certifies.

PROVENANCE: specced by task 468's realignment (report `specs/468_realign_task_programme_from_proof_state_audit/reports/02_stage1-verification-and-programme-realignment.md` §5, new-task-spec-2), itself descended from `specs/reviews/review-2026-08-24.md` amendment 10b's surviving ADD-list item, per R4.

---

### 481. Discharge or replace unorderedsuccessorlabelclosed residual
- **Effort**: large
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 434, Task 483
- **Research**:
  - [481_discharge_or_replace_unorderedsuccessorlabelclosed_residual/reports/01_unorderedsuccessorlabelclosed-verdict.md]
  - [481_discharge_or_replace_unorderedsuccessorlabelclosed_residual/reports/02_spawn-analysis.md]
- **Plan**: [481_discharge_or_replace_unorderedsuccessorlabelclosed_residual/plans/01_sharpen-replace-labelclosed-residual.md]
- **Summary**: [481_discharge_or_replace_unorderedsuccessorlabelclosed_residual/summaries/01_sharpen-replace-labelclosed-residual-summary.md]

**Description**: CLASSIFICATION: genuinely open -- the predicate is refuted as stated, so this is a repair-or-replace problem, not routine discharge. This is the FIFTH termination residual; the four-residual framing used elsewhere in this programme (`UniverseClosed`, `DifficultyBounded`/`StepLengthBounded`, `MintPaysForTime`, `PostBlockingSettles`) is WRONG and must be corrected wherever it recurs.

TARGET: `UnorderedSuccessorLabelClosed` (`FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean:6199`) is carried as a live hypothesis by `buildTableauAt_isSome_at_seed_lengthBudget_signedUniverse` (`:6215`) and has an in-tree refutation at `:6238` (`¬ UnorderedSuccessorLabelClosed fc freshWorldLabels`) -- the same shape of problem `DifficultyBounded` presented before `StepLengthBounded` replaced it.

WHAT TO DO -- determine which of three outcomes applies:
(a) the predicate can be discharged at the frame classes/settings the surviving terminus theorems actually need (distinct from the setting `:6238` refutes it in -- check precisely which); or
(b) it needs a `StepLengthBounded`-style weaker replacement, analogous to the `DifficultyBounded` -> `StepLengthBounded` repair pattern already in this file; or
(c) it is unclosable as stated and needs a C9 register entry (the file already has 24 such entries; this would be the 25th) plus an explicit statement of which theorem still carries it and at which frame classes.

A C9 REGISTER ENTRY IS A VALID, COMPLETE DELIVERABLE for this task -- do not treat "prove it" as the only acceptable outcome.

SEQUENCING NOTE (direct from `specs/reviews/review-2026-08-24.md` amendment 10e, re-affirmed by task 468's realignment): task 462 targets `MintPaysForTimeFixed` discharge at a NONEMPTY UNIVERSE, which is the same setting `:6238`'s refutation applies in. If this task and 462 are not sequenced, 462 risks either duplicating the discovery of the refutation or, worse, building on an implicit assumption that this residual is harmless. This task should run BEFORE OR ALONGSIDE 462.

DEPENDENCIES: `[434]` (established the residual set this belongs to). Do NOT fold into 465 (the mechanical restatement-family task) -- 465 is explicitly scoped as "a one-line application of its family root" for SETTLED residuals; this residual is not settled, so folding it in would either force 465 to do research work outside its charter or produce a restatement of an unsettled predicate, which is exactly the kind of premature-closure risk this whole realignment exists to prevent.

VERIFIED at task-468 realignment time (2026-08-25): none of tasks 462, 463, 464, 465 mentions the symbol `UnorderedSuccessorLabelClosed` in its live description.

ACCEPTANCE: one of outcomes (a)/(b)/(c) above is reached and recorded; `lake build` green; no regression to any currently-passing check-module-invariants.sh check.

PROVENANCE: specced by task 468's realignment (report `specs/468_realign_task_programme_from_proof_state_audit/reports/02_stage1-verification-and-programme-realignment.md` §5, new-task-spec-3), itself descended from `specs/reviews/review-2026-08-24.md` amendment 10e.

---

### 476. Box faithful small model theorem
- **Effort**: large
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 475

**Description**: THE BOX-FAITHFUL SMALL-MODEL THEOREM.

CLASSIFICATION: OPEN MATHEMATICS. MULTI-MONTH. This is a genuine research problem in the same
category as the audit's R4 "semantic FMP" entry. IT MAY NOT BE RE-DESCRIBED AS ENGINEERING, AND IT
MAY NOT BE MERGED INTO THE BILASSO WIRING TASK OR THE CARRIER-NORMALIZATION TASK. Merging is
precisely how a research problem gets hidden behind an engineering description, and this task
exists partly to prevent that.

DO NOT BEGIN before the BiLasso wiring task and the carrier-normalization task (task 475) are
landed. Those two have standalone value; this one does not, and its cost is dominated by a problem
a two-day literature check might refute outright.

=== LITERATURE GATE -- RUN FIRST, AND IT IS EMPOWERED TO STOP THE TASK ===

Acquire Gabbay, Kurucz, Wolter, Zakharyaschev, *Many-Dimensional Modal Logics* (2003) and read its
temporal-products chapter. IF the two-dimensional `Until`/`Since` case is recorded there as
undecidable or as lacking the finite model property, THIS TASK IS REFUTED and must be REPORTED AS
SUCH rather than attempted. A negative result here is as valuable as a positive one and would
redirect the whole decidability front.

What is already firm from a prior search: products of THREE OR MORE modal logics are undecidable,
with no logic between K x K x K and S5 x S5 x S5 decidable, and S5 x S5 x S5 lacks the finite model
property. What is NOT settled: the two-dimensional case with `Until`/`Since`, which is what this
logic is closest to. Note that TM is in any case NOT a full product -- its second dimension is the
path space of a graph, not an arbitrary set of runs -- so a product-logic result would be evidence,
not a decision.

=== THE TARGET ===

Build `cands : Formula -> List IntPresentation` and prove

    not (ValidDiscrete phi) -> exists P in cands phi, exists w, SatAtState P w phi.neg

This is the SINGLE remaining obligation for decidability of `ValidDiscrete`. Everything else is
already compiled: given this hypothesis, `check`-over-`cands` is equivalent to `ValidDiscrete phi`
and `decidable_of_iff` reads the `Decidable` instance off it. There is no bridge theorem, no
transfer lemma, no enumeration over `Atom`, and no `Fin n`-from-`Finite` extraction anywhere in the
assembly; `check_correct` is the FINAL step.

=== THE CONSTRUCTION (the tractable part) ===

Build `cands phi` from the CLOSURE-TYPE SPACE: subsets of `subformulaClosure phi` satisfying the
local Hintikka conditions, with `step` given by `LocalCoherent`'s `untl`/`snce` unfolding clauses
(`BiLasso/Annotation.lean` already states them, and they relate the label at `t` to the label at
`t` plus-or-minus one only -- i.e. they ARE an adjacency relation), and the valuation read off the
state by deciding atom membership. Every ingredient is `Finset`/`Bool` data with `DecidableEq`.
Two real obligations, neither research-grade:

  1. `fwd`/`bwd` SERIALITY OF THE TYPE GRAPH. Not free: a Hintikka type may have no locally
     coherent successor, forcing an ITERATED PRUNING to a maximal serial subgraph. Standard,
     bounded, fiddly.
  2. INDEXING. `IntPresentation` demands `Fin card` specifically, so the type `Finset` must be
     listed and indexed. Mechanical.

Estimate for this part alone: two to four weeks.

DO NOT instead try "bound `card` by some `presentationBound phi`, then enumerate the presentations
up to that bound". That does not typecheck as stated: `IntPresentation.val : Atom -> Fin card ->
Bool` is a function on the `Infinite` type `Atom`, so presentations of a given `card` are not a
finite collection. Closing that would need a valuation-restriction lemma that is not in the tree.
The formula-indexed candidate list sidesteps the problem rather than solving it.

=== THE CRUX: BOX-FAITHFULNESS (the research part) ===

The `box` clause of `TruthAt` quantifies universally over ALL total histories. Two landed facts
make this a GLOBAL modality rather than a local one:

  - `Truth.box_const` (`Semantics/Truth.lean`): box truth is independent of both the history and
    the time. Its own docstring: "a model has one finite set of box facts, computed once."
  - `Extension.occurrence` (`cor:occurrence`): every state occurs at every time in some total
    history.

That collapse is why `BoxOracleSound P bx` types `bx` as `Formula -> Bool` -- one `Bool` per
formula, per model. It is also the obstruction:

  The box facts of the SOURCE model M and of the TARGET presentation P are each global constants
  of their own model, and they need not agree. P admits every path of its graph. The subgraph of
  types realized in M still generates paths that M does not realize, and along such a path a
  `box chi` true in M can fail. When it fails, the type-map image is no longer a `LocalCoherent`
  annotation, and the transfer breaks.

Restricting `cands phi` to realized-type subgraphs does NOT by itself close this: the subshift
generated by the realized edges properly contains the realized paths. So the residue is a genuine
BOX-FAITHFUL small-model theorem -- in effect a bounded-model property for LTL(Until, Since) over
bi-infinite paths of a graph, PLUS a universal path quantifier over the whole structure.

Is it true? Almost certainly -- the shape is the classical automata-theoretic bounded-model
setting, and the analogous results (CTL*-style satisfiability, LTL with a universal modality) are
decidable with finite/bounded model properties. Is it in reach? Not routinely. Neither Mathlib nor
this tree carries omega-automata, Buchi complementation, or any language-inclusion machinery, so a
Lean proof must be hand-rolled.

=== WHAT TO REUSE ===

`BiLasso/GoodCycle.lean`'s good-cycle argument, `cycleBound`, and `exists_annot_of_truth` are
exactly the fulfilment machinery a hand-rolled proof would reuse. Be clear-eyed that they operate
INSIDE a presentation, not across the model boundary, which is the whole difficulty.

=== DO NOT PROMISE A CHOICE-FREE RESULT ===

`wlem_of_spherical` (`Tests/BimodalTest/Semantics/SphericalFiniteAxiomTest.lean`) derives weak
excluded middle from `Spherical R` at the finite carrier `Bool` over `D = ZZ`, from
`[propext, Quot.sound]` alone. So NO finite-carrier frame with an arbitrarily shaped relation can
be choice-free, on any route. The cost is already paid by `IntPresentation.toTaskFrame`. Any spec
promising choice-freedom here is promising something proved impossible. Note the separate
distinction: `instDecidableSatAtState` COMPUTES (kernel-evaluated `#guard`s prove it) while
measuring `[propext, Classical.choice, Quot.sound]`. Computability and choice-freedom are different
properties.

---

### 465. Complete terminus restatement family
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 462, Task 463, Task 464

**Description**: Complete the terminus restatement family at the repaired residuals. Task 433's Phase 6 landed EIGHT of the twenty-two restatements -- the four family roots and their four caller-facing seed forms -- and recorded the remaining FOURTEEN as a Reasoned Exclusion with the recipe written down: each is a `_lengthBudget` / `signedUniverse` substitution, "a one-line application of its family root".

This is deliberately MECHANICAL work with the recipe already recorded. Its value is uniformity: a caller reaching for a `_lengthBudget` or `signedUniverse` form of a repaired terminus should find it landed rather than having to re-derive it, and a half-populated family is a trap for a future reader who assumes an absent member is absent for a reason.

SCOPE: read Phase 6's Reasoned Exclusions section in specs/433_discharge_postblockingsettles_residual/plans/01_postblockingsettles-refute-or-prove.md for the enumerated list and the recipe. The family roots and existing members are the `buildTableauAt_isSome_*` declarations in MintBound.lean (the `_at`, `_selfGuarded`, `_fixed` and `_run` families, roughly :6308-:12240). Land the fourteen missing members following the naming convention the file already uses; do not invent a new convention.

WHY THIS RUNS LAST: it restates termini at the repaired residuals, so it must run after the residuals themselves are settled. If 462, 463 or 464 changes a predicate's shape or sheds a hypothesis, the restatements must reflect the settled form -- doing this work earlier would mean doing it twice. Before starting, RE-DERIVE the list of missing members from the file as it then stands rather than trusting the count of fourteen recorded here: earlier tasks may have landed some, or added new family roots.

PROHIBITED: no `sorry`; additive only; do not alter any previously-landed declaration; do not edit Fuel.lean, Saturation.lean or Tableau.lean; axioms within {propext, Classical.choice, Quot.sound}; full `lake build` green. If any of the fourteen turns out NOT to be a one-line application -- i.e. the recipe does not actually apply -- STOP on that member, record why, and do not force it; a member that needs real mathematics belongs in its own task, not smuggled in here.

Dependencies: 462, 463, 464 -- all three, so that the restatements are made against a settled set of residuals rather than a moving one.

---

### 464. Gappotential density measure component
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 462, Task 463

**Description**: Design and land `gapPotential`, the density coordinate of the termination measure. This is the one genuinely OPEN MATHEMATICAL question remaining on the totality terminus; it is research, not plumbing, and should be run with --lit.

THE PROBLEM, stated exactly. `densityRule` mints a fresh time while lying OUTSIDE BOTH `freshLabelRules` AND `selfGuardRules`. Consequently no disjunct of the current measure moves at a `densityRule` step, FOR ANY sigma WHATSOEVER. This has been open since C9 register entry 17 named it, and task 434's Phase 8 records the current state bluntly: `gapPotential` "remains implemented nowhere and assumed by nothing". Because `densityRule` is `denseRules`-gated, this blocks a nonempty `MintPaysForTimeFixed` discharge at `.Dense` and `.Dedekind` frame classes specifically; every frame class needs `gapPotential` for a fully general result.

SHAPE SUGGESTED BY PRIOR WORK (a starting point, NOT a specification to follow blindly): task 434 records the expectation that `gapPotential` is indexed by `U x U` and `denseRules`-gated. Validate or refute that shape as part of the research; if a different indexing is correct, say so and justify it.

HARD REQUIREMENT -- PRESERVATION ACROSS THE IDENTIFICATION ARM. Any candidate component must be preserved across `TimeOrdering.identifyTime`, which can LOWER `ord.timeCount`. This is the same maxTime-lowering mechanism that refuted earlier candidates; see `nextTime_reissues_retired_time` and `reuse_driven_through_engine`, and task 436's oriented-arm re-gate (`orientedGate*` family, :8592-8788) for how the analogous obstacle was handled for the self-guard component. A component that pays at `densityRule` steps but is destroyed by the identification arm is not a solution.

REFUTED ROUTES -- C9 register entries 14, 17, 18, 19, 20, 24. Read them ALL in full before designing anything. In particular entry 14 forbids BOTH (1) re-indexing `mintPotential` on `freshTimeRules` instead of `freshLabelRules` -- refuted by `witnessPresent_eq_false_of_not_freshLabel`, whose match has exactly eight arms so the three added columns are permanently false -- and (2) dropping disjunct 1's cardinality conjunct in favour of the ordering-rank conjunct alone -- refuted by `splitOrderedRank_lt_of_knownTimes_lt` plus `mintPaysForTime_rank_repair_false`. Neither may be re-attempted.

LITERATURE. Run with --lit against the sub-index curated for this line of work, drawing specifically on: venema_2001 section 5 (interval-based temporal logic) for the density/gap-guarded component itself; caleiro_2013 sections 6-7 (mosaic-method decidability for combined tense-and-modal logics) as a structural analogue for a combined-logic termination measure; gerth_1995 and baier_katoen_2008 (closure-set LTL tableau termination) as a model for a measure over an evolving, non-monotonically-changing time set; and massacci_2000 for rule-bounding technique.

DONE MEANS EITHER: (a) `gapPotential` defined, its payment at `densityRule` steps proved, its preservation across `identifyTime` proved, integrated into the measure, and a nonempty `MintPaysForTimeFixed` discharge extended to `.Dense` and `.Dedekind`; OR (b) a machine-checked impossibility result showing no such component exists at the current measure's shape, with the obstruction identified precisely and a C9 entry recording it. Outcome (b) is a genuine and valuable result, NOT a failure -- this repo's practice is that a proved refutation ranks with a proof, and several of this measure's real advances came from refutations.

PROHIBITED: no `sorry`, no vacuous or false predicate, no weakening presented as a repair (a direction lemma is a GATE, not a nicety -- C9 entry 7 exists because that mistake was made once); do not edit Fuel.lean, Saturation.lean or Tableau.lean (md5-pinned frozen); additive only in MintBound.lean; axioms within {propext, Classical.choice, Quot.sound}; full `lake build` green.

Dependencies: 462 is a REAL SEMANTIC dependency -- the engine-level assembly is what makes a per-rule payment usable at the successor, and `gapPotential`'s payment needs the same threading. 463 is a file_scope SERIALIZATION edge only (both edit MintBound.lean), with no mathematical content.

---

### 463. Postblockingsettlesrun verdict at terminus fuel
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 462, Task 433
- **Research**: [463_postblockingsettlesrun_verdict_at_terminus_fuel/reports/01_postblockingsettlesrun-verdict-terminus-fuel.md]
- **Plan**: [463_postblockingsettlesrun_verdict_at_terminus_fuel/plans/01_postblockingsettlesrun-verdict-terminus-fuel.md]
- **Summary**: [463_postblockingsettlesrun_verdict_at_terminus_fuel/summaries/01_postblockingsettlesrun-verdict-terminus-fuel-summary.md]

**Description**: Decide `PostBlockingSettlesRun fc (mintAwareFuelAt U.card Tmax mintBudget D beta)` -- the narrowed settlement residual task 433 landed -- at the terminus's OWN fuel figure. Nothing currently decides it in either direction, and task 433's C9 register entry 24 exists precisely so the narrowing is not mistaken for a proof.

WHY THIS MATTERS. `PostBlockingSettlesRun` (MintBound.lean:11961) is CARRIED as a hypothesis by the fully-repaired terminus `buildTableauAt_isSome_of_budget_fixed_run` (:12199), exactly as `ArmSettlement` is. Until it is decided, the repaired terminus rests on an unknown. Task 433 established the surrounding facts but deliberately stopped short of this verdict.

WHAT IS ALREADY DECIDED -- consume, do not repeat:
- `PostBlockingSettles fc` (the unnarrowed form, :5181) is REFUTED: `postBlockingSettles_fuel_zero_false` (false at the `fuel = 0` arm at every frame class) and `postBlockingSettles_fuel_gap_false` / `postBlockingSettles_gap_at_every_fuel` (fuel does not close the gap, at ANY fuel). The witness is `freshWorldBranch = [F(box p)@<0,0>]`: `.boxNeg` mints a fresh world, so `expandOnceNoFresh` skips it and reports `.saturated` while `findUnexpandedUnblockedWith` reports it.
- `PostBlockingSettlesAt fc` (:11539) holds OUTRIGHT for every `fc` (`postBlockingSettlesAt_holds`, :11721) -- but the bridge from `saturateBlocked ... = some (.inr (satBr, satOrd))` to its antecedents does NOT go through, because at `fuel = 0` that equation holds at every branch while carrying no saturation information (`labelFreeSaturatedExit_not_of_saturateBlocked_inr`).
- Task 433 PROVED that the only bridge shape that typechecks carries a hypothesis that is itself refutable (it composes with the settlement lemma to give the refuted `PostBlockingSettles fc`). Do NOT re-attempt that bridge; it is a weakening dressed as a repair.

STRUCTURE THIS AS A REFUTE-FIRST GATE with a BINARY verdict, in the style tasks 432, 433 and 436 used successfully. Both outcomes are first-class deliverables:
- TRUE: `PostBlockingSettlesRun` holds at the terminus's own fuel figure -- discharge it, and the repaired terminus sheds a hypothesis.
- FALSE: it is refutable at that figure -- land the machine-checked refutation with its witness, record a C9 entry, and name the minimal further narrowing as the next step. A proved refutation here is as valuable as a proof and MUST NOT be treated as failure.

EMPIRICAL WARNING FROM TASK 433. Across fourteen formula shapes, four frame classes and three fuel figures, `buildTableauAt`'s own guard NEVER fired -- the threaded tracker and the recomputed `armTracker` agreed everywhere -- so no probed run exercised the post-blocking arm at all. That is a fact about the probe's reach, not about the residual, but it means this path is essentially untested empirically. Do not treat "no counterexample found by probing" as evidence of truth; the verdict must be proved either way, and if the honest answer is "undecided by the means available", say so explicitly with evidence rather than guessing.

PROHIBITED: do not discharge via `ArmSettlement` (proved strictly too weak: `resolveOpenArm` tests `findClosure satBr` before its saturation test, `buildTableauAt` does not); do not edit Saturation.lean, Tableau.lean or Fuel.lean (md5-pinned frozen) -- use only their existing public interface; do not re-attempt anything in the C9 register; no `sorry`, no vacuous discharge. Sorry-free, axiom-free, additive only, full `lake build` green.

Dependencies: 462, as a file_scope SERIALIZATION edge only (both tasks edit MintBound.lean). There is no mathematical dependency on 462 -- this task's content is independent of the minting measure and may be reasoned about immediately.

---

### 461. Acquire Goldblatt 1989 'Varieties of complex algebras' (Annals of Pure and Applied Logic)
- **Status**: [COMPLETED]
- **Task Type**: general
- **Topic**: literature
- **Dependencies**: Task 460
- **Research**: [461_acquire_goldblatt_1989_varieties_of_complex_algebras/reports/01_acquisition-verified-corpus-status.md]
- **Plan**: [461_acquire_goldblatt_1989_varieties_of_complex_algebras/plans/01_goldblatt-1989-zotero-closeout.md]
- **Summary**: [461_acquire_goldblatt_1989_varieties_of_complex_algebras/summaries/01_goldblatt-1989-zotero-closeout-summary.md]

**Description**: SCOPE 8 acquisition gap identified by task 457's research and re-confirmed at implementation time: this paper is absent from both the ~/Projects/Literature corpus and the Zotero library, and is named as a prerequisite by other tasks in this repo working on the Jonsson-Tarski representation theorem. Note: goldblatt_2003 already present in the corpus is a DIFFERENT paper (Erdos Graphs Resolve Fine's Canonicity Problem) -- do not conflate the two. Needed: locate and acquire a copy of Goldblatt 1989 (Annals of Pure and Applied Logic 44, pp. 173-242), add it to Zotero, then run a normal /literature ingest.

---

### 433. Discharge postblockingsettles residual
- **Effort**: 6-10 hours
- **Status**: [COMPLETED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 432, Task 434
- **Research**:
  - [428_engine_totality_at_a_quantified_branch_budget/reports/05_spawn-analysis.md]
  - [433_discharge_postblockingsettles_residual/reports/01_spawn-inherited-research.md]
- **Plan**: [433_discharge_postblockingsettles_residual/plans/01_postblockingsettles-refute-or-prove.md]
- **Summary**: [433_discharge_postblockingsettles_residual/summaries/01_postblockingsettles-summary.md]

**Description**: Discharge `PostBlockingSettles fc`, defined at FormalSystem/Metalogic/Decidability/Verified/Termination/MintBound.lean:4344, one of the four residual hypotheses on the totality terminus `buildTableauAt_isSome_of_budget` (MintBound.lean:4416). It states that the post-blocking pass leaves a branch the blocking-aware saturation test certifies -- i.e. `findUnexpandedUnblockedWith satBr satOrd fc (blockedTimes satBr satOrd fc (armTracker satBr)) = none` whenever `saturateBlocked ob fuel oOrd fc = some (.inr (satBr, satOrd))`. It subsumes `resolveOpenArm`'s own `none` arm via `armSettlement_of_postBlockingSettles` (MintBound.lean:4354) -- `ArmSettlement` alone is proved strictly too weak (`resolveOpenArm` tests `findClosure satBr` before its saturation test; `buildTableauAt` does not), so do not attempt to discharge via `ArmSettlement` instead. The relevant definitions are frozen (md5-pinned) in Saturation.lean (`saturateBlocked`, :431) and Tableau.lean (`blockedTimes`, :2104; `findUnexpandedUnblockedWith`, :2115) -- do not edit either file; the residual's own docstring states the gap ('whether the fuel-vs-condition gap can be closed by fuel alone') is exactly what Saturation.lean leaves open using only its existing public interface. Done means: either (a) a proof of `PostBlockingSettles fc` for the frame classes the terminus is meant to be used at, using only the public interface of the frozen files, landed sorry-free and axiom-free with `lake build` green; or (b), if (a) turns out to be genuinely impossible without touching the frozen files, a return to [BLOCKED] with the specific counterexample or obstruction found, analogous to the parent task's own refutation-driven repairs (e.g. `ordTimes_identifyTime_arm3_false`, MintBound.lean:1217) -- do not paper over with a vacuous definition (`lean4.md`'s Vacuous Definitions prohibition applies). This task's own residual work -- deciding PostBlockingSettlesRun at the terminus's own fuel figure, and completing the terminus restatement family -- has moved downstream to tasks 463 and 465 respectively; do not re-attempt those here.

---

### 430. Semantic lift and track a assembly valid iff allclosed
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 428, Task 429, Task 411

**Description**: The semantic lift and the Track A assembly. Owns obstruction O4 of the Phase 7.3 deadlock, then delivers what Phase 7.3 of task 165 was for. Grounding: specs/165_establish_semantic_finite_model_property/reports/09_phase7-deadlock-blocker-research.md.

THIS TASK CARRIES THE WORK MOVED OUT OF TASK 165's PHASE 7.3. Task 165 terminated with Phase 7 scoped to what it delivered (the truth lemma and Track A's conditional results); 7.3 -- `valid_iff_allClosed` and the `Decidable` instances -- was moved here rather than closed, because it is blocked on prerequisites no task owned.

O4 HAS TWO DISTINCT PIECES, per Verified/Decidable.lean:3062-3067: "It is not yet `valid_iff_allClosed` (7.3), which additionally needs the fuel/termination side and the truth-lemma gate, and it says nothing about the two rules scheduled outside `allRulesForFC` -- `serialityRule` and `timeLinearity` run as stages 2 and 3 of `expandOnce` and need their own obligations at the point where `expandOnce`, rather than `applyRule`, is the object."

(a) Two more `RuleSound`-analogues at the `expandOnce` level, for `serialityRule` and `timeLinearity`. These are deliberately outside `allRulesForFC`, so `ruleSound_of_mem_allRulesForFC` (landed, 34/34) does NOT cover them.
(b) THE SEMANTIC LIFT: the induction lifting single-step satisfiability preservation to the whole recursion, so that `.allClosed` yields a contradiction. This is the LARGER of the two and is comparable in weight to a landed sub-phase, not to a wrapper. Naming it inside "the two outside rules" understates it.

THEN, and only after (a), (b) and both predecessors: `valid_iff_allClosed` plus the four `Decidable` instances for validity over Base, Dense, Discrete and Dedekind.

WHAT IS ALREADY LANDED (do not re-prove): the rule half is done -- `ruleSound_of_mem_allRulesForFC` is a single landed induction over `mem_allRulesForFC_iff`, ledger complete at 34/34, from task 165 Phase 7.2.

PLAN AGAINST SIX ROWS, NOT EIGHT: the truth-lemma gate hypothesis hTW is discharged on SIX accepted TemporalWitnessProbe rows (A, B, C, D, E, F), not the historical eight -- rows I and K left when the PASSIVE arms of untlNeg/snceNeg were retired. See the banner at the head of Tests/BimodalTest/TemporalWitnessProbe.lean.

DO NOT write a conditional `valid_iff_allClosed` carrying hTW as an explicit hypothesis. Correctness.lean:98-105 refuses exactly this shape, and the O4(b) hypothesis would BE the conclusion's forward direction, making the theorem vacuous. Four vacuous theorems were deleted in 165's Phase 8; do not land a fifth.

DONE WHEN: `valid_iff_allClosed` and the four `Decidable` validity instances are landed unconditionally, sorry-free and axiom-clean outside Boneyard, lake build green.

---

### 429. Repair truth lemma side conditions boxanchored and temporalwitness
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 428

**Description**: Repair the truth-lemma side conditions. Owns obstructions O2 and O3 of the Phase 7.3 deadlock recorded in specs/165_establish_semantic_finite_model_property/reports/09_phase7-deadlock-blocker-research.md. THIS IS THE TASK WITH GENUINE OPEN MATHEMATICS IN IT and should be budgeted accordingly.

READ FIRST: specs/418_*/artifacts/boxanchored-finding.md -- it carries the measurement, the full carrier list, and the repair options. Then TruthLemma.lean:399-404 and BoxSaturation.lean:430-435, :574-580.

O2 -- `hBA` (`boxAnchoredCheck`) is no longer dischargeable on multi-world branches. BoxSaturation.lean:430-435: the two copy blocks "have since been removed as unsound ... They were the ONLY route by which T(G phi)/T(H phi) could reach a freshly minted world ... `boxAnchoredCheck` is therefore expected to compute `false` on multi-world branches now." :574-580: "a caller can no longer expect to discharge that hypothesis from a real run." TruthLemma.lean:399-404 names the repair as "an open design decision with its own soundness obligations" and lists THREE candidate routes: (a) propagate T(box phi) itself; (b) copy T(G phi)/T(H phi) only when box-derived; (c) restructure the `box` case to need no anchor.

CRITICAL CONSTRAINT: this was caused by task 418 (completed) removing a GENUINE UNSOUNDNESS. It is the cost of a correct fix, not a regression to revert. TruthLemma.lean:404 says "Do NOT reinstate the removed copies." Any repair must re-establish the anchor WITHOUT reinstating them.

O3 -- `hTW` (`temporalWitnessCheck`) is no longer dischargeable on any branch carrying a negative until with a known future time. TemporalWitnessProbe.lean:66-73: `untlNegFuture` demands F(event) at every known future time of every negative until; the PASSIVE arm's branch 1 was the ONLY producer of `not event` at an EXISTING time; that arm was retired as unsound (user-authorized rank 2), so the producer is gone. Measured cost: fourteen probe rows moved check=true -> check=false; the accepted set went from EIGHT rows to SIX (rows A, B, C, D, E, F; I and K left). :86-88: "it was already `false` on the branches the engine actually builds. What it removes is the last set of hand-built branches on which the hypothesis was discharged."

DO NOT REOPEN (settled by 165): guardWitnessed in any variant; restoring sat_untl_neg / sat_snce_neg (they are FALSE against the current engine, not merely unproved); reinstating the retired PASSIVE arms or the removed box copy blocks.

GOAL: choose among the three documented BoxAnchored repair routes and land it with its soundness obligations discharged; and re-establish a producer for `not event` at existing future times. Both must hold on branches the engine ACTUALLY builds, measured by the probes, not on hand-built branches.

DONE WHEN: `boxAnchoredCheck` and `temporalWitnessCheck` are dischargeable on real engine output for the relevant branch classes, evidenced by probe rows moving back to check=true; no unsound copy block or retired arm is reinstated; lake build green.
REALIGNMENT ADDENDUM (task 468, 2026-08-25) -- RECOMMENDED ROUTE, NAMED UP FRONT: of the three O2
repair routes listed above, route (a) -- propagate T(box phi) itself to the fresh world -- is the
RECOMMENDED route (per specs/reviews/review-2026-08-24.md amendment 10a and the box-anchor
artifact's own §5), so a dispatch need not re-derive the recommendation from
boxanchored-finding.md each time. It follows the S5 axiom-4/5 pattern, carries its own RuleSound
obligation, and has named fuel/termination consequences that Fuel.lean's bounds and the
subformula property must absorb -- all as already detailed in that artifact. Route (b) remains
available but reduces to route (a)'s obligation once branch provenance is tracked, per the
artifact. Route (c) stays recorded as CLOSED AS FORMULATED (boxGridCheck fails for the same
structural reason the anchor does, so weakening only the anchor buys nothing) -- do not
re-attempt it. This addendum names a recommendation; it does not narrow the task's own account of
all three routes and their obligations above, which stands as written.

---

### 428. Engine totality at a quantified branch budget
- **Status**: [BLOCKED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 432, Task 433, Task 434, Task 465
- **Plan**:
  - [428_engine_totality_at_a_quantified_branch_budget/plans/02_lexicographic-splitordered-measure.md]
  - [428_engine_totality_at_a_quantified_branch_budget/plans/03_mint-bound-irreflexivity-totality.md]
  - [428_engine_totality_at_a_quantified_branch_budget/plans/04_ordtimesknown-strengthening-totality.md]
  - [428_engine_totality_at_a_quantified_branch_budget/plans/01_budget-totality-engine-repair.md]
- **Summary**:
  - [428_engine_totality_at_a_quantified_branch_budget/summaries/02_lexicographic-splitordered-measure-summary.md]
  - [428_engine_totality_at_a_quantified_branch_budget/summaries/01_budget-totality-engine-repair-summary.md]
  - [428_engine_totality_at_a_quantified_branch_budget/summaries/04_ordtimesknown-strengthening-totality-summary.md]
- **Research**:
  - [428_engine_totality_at_a_quantified_branch_budget/reports/03_phase11-potential-obstruction.md]
  - [428_engine_totality_at_a_quantified_branch_budget/reports/04_witness-preservation-machine-checked.md]
  - [428_engine_totality_at_a_quantified_branch_budget/reports/01_budget-totality-refuted-and-repair.md]
  - [428_engine_totality_at_a_quantified_branch_budget/reports/02_splitordered-measure-blocker.md]
  - [428_engine_totality_at_a_quantified_branch_budget/reports/05_spawn-analysis.md]

**Description**: Engine totality at a quantified branch budget. Owns obstruction O1 of the Phase 7.3 deadlock recorded in specs/165_establish_semantic_finite_model_property/reports/09_phase7-deadlock-blocker-research.md section "The four obstructions" (read it first; do not re-derive the refutation).

THE REFUTED THEOREM, SETTLED: `buildTableau_isSome` in unconditional form is FALSE, not merely unproved, and is on a do-not-re-attempt register (165's plan 01_tableau-decidability-two-track.md:1405-1420, :1489-1493). The refutation is a property of the engine SIGNATURE, not a proof difficulty: `buildTableau` (Saturation.lean:928-951) calls `expandBranchWithFuel` at the default `maxBranches := 50000` (Saturation.lean:590), whose first line is `if branchesUsed >= maxBranches then none` (:594). A formula exploring more than 50000 branches returns `none` at ANY fuel whatsoever. Independently, `buildTableau`'s last arm returns `none` on a still-unsaturated branch (:950). Neither is fuel exhaustion, so no fuel figure rules them out. DO NOT attempt the unconditional form.

WHAT LANDED INSTEAD, and why it is unusable as-is: Verified/Termination/Fuel.lean:1587-1598 carries two hypotheses -- `(hP : NoSplit P fc)` and `(hbud : branchesUsed + fuel <= maxBranches)`. `NoSplit` excludes impPos, orPos, untlPos, untlNeg, sncePos, snceNeg, orderTrichotomy and every frame-class-gated splitting rule, i.e. it holds only on non-branching runs. 165's plan:1467-1468 records "Residual 2 (branching arms) -- isolated, not discharged."

GOAL: add a `maxBranches`-parameterised entry point ALONGSIDE `buildTableau` -- an ADDITION, never an edit to the existing default, because `maxBranches = 50000` is a deliberate runtime guard -- and prove totality against a quantified budget. Target shape:

  theorem buildTableau_isSome_of_budget (phi : Formula) (fc : FrameClass)
      (maxBranches : Nat) (hmb : <bound in phi> <= maxBranches) :
      (buildTableauAt phi (soundFuel' phi) fc maxBranches).isSome = true

THREE SUB-OBLIGATIONS:
1. Discharge the branching-arm residual that `NoSplit` currently hypothesises (Fuel.lean:1587, Saturation.lean:661-664, :686-689).
2. Supply the missing WORLD-COUNT dimension. 165's plan:1484-1488: "T1 bounds formulas and T2 bounds times; neither bounds worlds ... as defined, `soundFuel' = 2*n*2^(2n)` has no world factor at all." A branch bound that ignores worlds cannot bound branches.
3. Establish the `<bound in phi> <= maxBranches` side condition in a form callers can actually discharge.

COORDINATION: overlaps task 426's hypothesis (b) on the same file (Fuel.lean). Sequence with 426 or merge; do not both edit Fuel.lean concurrently. Task 412 consumes this theorem in place of the refuted `buildTableau_isSome`.

DONE WHEN: the budget-parameterised totality theorem is landed sorry-free with no `NoSplit` hypothesis, lake build green, and the world dimension is either supplied or its absence is proved harmless.

RETARGET DECISION (user-approved, post-research): the specified unconditional target shape is refuted (see reports/01_budget-totality-refuted-and-repair.md). Task WIDENED to own the validated certificate repair: swap findUnexpanded -> findUnexpandedUnblocked at resolveOpenArm's two decision points, discharge the accompanying soundness obligation on what .hasOpen certifies (shared with O2/O3), lift the proved saturateBlocked_isSome asset, close the world dimension via worldFuel'/WorldWitness, and land the budget-parameterised totality theorem against the repaired engine. The per-path budget finding (maxBranches >= 3*fuel linear invariant) supplies the side condition.

SECOND RETARGET DECISION (user-approved, post-research 03). The per-step framing of Phase 11 cannot be closed: reports/03_phase11-potential-obstruction.md section 4 is a proof about the SHAPE of the argument, not a report of a failed attempt. Route (a) (a lower bound on branch cardinality after identification) is DEAD by definition -- `Branch.identifyTime = (b.map relabel).eraseDups`, so all shrinkage comes from eraseDups and is bounded only by |U|. Route (b) (an independent mint bound) is the APPROVED path.

THE CHEAPER ALTERNATIVE IS EXPLICITLY REJECTED BY THE USER: do NOT carry the mint bound as a hypothesis in the shape `hT` has, and do NOT push the discharge obligation onto task 412. Do it the right way.

APPROVED WORK (route (b), ~6-7 phases, comparable in size to everything landed so far):
1. WITNESS PRESERVATION (~3 phases): the eight-rule case analysis of report 03 section 3 step 4, resting on the three lemmas already machine-checked in that report's section 1 (`mem_futureOf_of_mem_constraints`, `mem_pastOf_of_mem_constraints`, `identifyTime_no_collapse`).
2. RESTATEMENT (~1 phase): give `expandBranchWithFuel_isSome_of_budget` an explicit MINT-BUDGET PARAMETER, in the shape `branchesUsed`/`maxBranches` already establishes. This is what converts route (b)'s amortized bound into something the induction can carry; a per-step potential over (b, ord) provably cannot express it (report 03 section 4), and `maxTime` was checked and is not a usable proxy (arm 3 can lower it).
3. AMORTIZED INDUCTION (~2-3 phases): #mints <= 8*|U|; #identifications <= |knownTimes|_0 + #mints; total shrinkage <= #identifications * |U|; #extensions <= |U| + total shrinkage; then the terminus `buildTableauAt_isSome_of_budget`.

RESEARCH GATE -- MACHINE-CHECK BEFORE PLANNING. Report 03 marks two load-bearing claims UNCERTAIN, and the whole mint bound rests on both:
  (i) section 3 step 4, witness preservation across `.splitOrdered` arm 3 -- ARGUED, NOT MACHINE-CHECKED. The two modal rules are trivial (their witness sits at the same time as `sf`, so identification moves both together); THE SIX TEMPORAL ONES NEED THE REACHABILITY TRANSPORT and were not verified.
  (ii) section 3 step 3, "formulas are never deleted" -- read off the rule shapes, consistent with the landed `expandOnceUnblocked_card_lt` / `expandOnceUnblocked_split_card_lt`, but NOT PROVED.
Machine-check BOTH before any plan is written. This task has twice had a plan rest on an unverified lemma that later turned out FALSE (the unconditional `buildTableau_isSome`; then the `.splitOrdered` cardinality twin). A third occurrence is not acceptable. If witness preservation fails for any temporal rule, ROUTE (b) IS DEAD and that is a THIRD retarget decision requiring human approval -- report it plainly, do not work around it and do not substitute a weaker statement.

PRESERVED, DO NOT RE-PROVE: phases 1-10 of plans/02_lexicographic-splitordered-measure.md are landed, sorry-free, axiom-free, and green repo-wide. Consume those declarations. `buildTableau`, its `fuel := 1000` default, and `expandBranchWithFuel`'s `maxBranches := 50000` default stay BYTE-IDENTICAL. No `NoSplit` reintroduction; no admitted `WorldWitness` or `hT`; no `sorry`; no narrowing a statement into vacuity. The refuted unconditional `buildTableau_isSome` and the refuted `.splitOrdered` cardinality twin stay on the do-not-re-attempt register. `resolveOpenArmCancellable` in CancellableExpansion.lean remains a DECLARED, deliberately-unrepaired out-of-scope divergence. Task 412 must not be planned against `buildTableauAt_isSome_of_budget` until it lands; the Phase 3 assets (`BudgetedTableau`, `buildTableauAt`, `BudgetedTableau.upgrade`) are available and sorry-free meanwhile.

RESUME SEQUENCE: `/research 428` first (discharge the two uncertain claims above), then `/orchestrate 428`. The stale loop guard from the prior invocation has been removed so a restart gets a fresh cycle budget.
REALIGNMENT ADDENDUM (task 468, 2026-08-25) -- ASSESS-AND-C9-REGISTER ESCAPE CLAUSE FOR THE
SPLIT-ARM FUEL SCALING PROBLEM: the opening "THE REFUTED THEOREM, SETTLED" paragraph above is
unaffected by this addendum and gets a CURRENT verdict on that point -- do NOT touch it.

`Fuel.lean:1595-1610` documents that fuel adequate for a split run scales like
`beta ^ depth * worldFuel'`, and depth is not bounded by anything proved in that file -- this is,
in its own words, "a real property of a deliberate engine policy, not a gap in a proof," of the
same class as the already-settled `buildTableau_isSome` refutation. If, in the course of this
task's approved route (b) work, the split-arm fuel-adequacy question proves genuinely unclosable
as specified -- i.e. no depth bound can be established or supplied without weakening the engine's
own proportional-fuel policy -- the correct deliverable is an explicit ASSESS-and-C9-register
outcome: name the specific obstruction, add a C9 register entry (in
`Verified/Termination/MintBound.lean`, alongside its other entries) stating precisely which
theorem still carries the split-arm scaling exposure and under what hypothesis, and stop there.
This is a VALID, COMPLETE outcome for this sub-question -- do not treat "close it" as the only
acceptable result, and do not force a proof past this obstruction by weakening `NoSplit`,
reintroducing a hypothesis this task's own do-not-re-attempt register forbids, or narrowing a
statement into vacuity.

---

### 412. Prove refutation core and decidability of provability with completeness corollaries
- **Effort**: 10-15 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 165, Task 410, Task 411, Task 428, Task 430

**Description**: Track B finish for the TM tableau decidability program (parent: task 165; grounding: reports/02_tableau-decidability-hard-research.md sections 3.1, 8.3, 8.5). Create Verified/Refutation/Core.lean proving allClosed_derivable as ONE induction over allRulesForFC fc, discharging each rule by its admissibility lemma (predecessor tasks) and its ruleFrameClass r <= fc hypothesis via the RuleSpec GATE lemmas — Dense/Discrete/Dedekind instantiate the generic theorem, they do not re-prove it. Then Verified/Provable.lean: Decidable (Derivable fc [] phi) combining allClosed_derivable with Track A's buildTableau_isSome and not_valid_of_hasOpen; the completeness corollaries ValidFor fc phi -> Derivable fc [] phi; supply the Dedekind engine consumed by completeness_dedekind_of_engine (StrongCompleteness.lean:308, target ValidDedekindDense). Acceptance: zero sorries repo-wide outside Boneyard; lake build green; update typst/latex decidability chapters to record headline result 2.
RE-SCOPING ADDENDUM (2026-07-29, supersedes the buildTableau_isSome reference above): the scope text above depends on "Track A's buildTableau_isSome", which task 165 proved FALSE and placed on a do-not-re-attempt register (165's plan 01_tableau-decidability-two-track.md:1405-1420, :1489-1493). The refutation is a property of the engine signature, not a proof difficulty: buildTableau returns none whenever a formula explores more than maxBranches := 50000, at ANY fuel. Consequently this task's acceptance criterion "zero sorries repo-wide outside Boneyard" was UNREACHABLE AS SCOPED, independently of task 165's own status.

CORRECTED DEPENDENCE: consume the budget-parameterised totality theorem from task 428 (engine_totality_at_a_quantified_branch_budget) -- shape `buildTableau_isSome_of_budget phi fc maxBranches (hmb : <bound in phi> <= maxBranches)` -- in place of the unconditional buildTableau_isSome. Task 428 has been added as a predecessor. Do NOT attempt the unconditional form yourself.

ALSO NOTE: this task inherits obstructions O2 and O3 (the boxAnchoredCheck and temporalWitnessCheck truth-lemma side conditions) from Phase 7.3 of task 165 by way of not_valid_of_hasOpen. Those are owned by task 429. If your induction reaches a point where a truth-lemma gate hypothesis must be discharged on real engine output, that is 429's work, not this task's -- record it and coordinate rather than re-deriving it. Grounding for all of this: specs/165_establish_semantic_finite_model_property/reports/09_phase7-deadlock-blocker-research.md.

REALIGNMENT CORRECTION (task 468, 2026-08-25): the struck clause above ("discharge the
pre-existing sorry countermodel_discrete at Transfer.lean:1242") is STALE. That sorry no longer
exists -- countermodel_discrete is CLOSED, via tasks 477/478/479's k-equivalence/groupable-
companion route, and now lives sorry-free in
FormalSystem/Metalogic/WeakCanonical/GroupModel/CountermodelBase.lean, not Transfer.lean. Verified
fresh by scripts/check-module-invariants.sh C2/C3 at realignment time: C3 reports zero live
structural sorries tree-wide; C2 reports BXCanonical.completeness axiom-clean
([propext, Classical.choice, Quot.sound]). This task's remaining scope (allClosed_derivable, the
Decidable (Derivable fc [] phi) instance, the completeness corollaries, the Dedekind engine) is
UNCHANGED and still open.

New task 482 (discharge_proof_extraction_completeness, dependencies: [412]) is the owner of
eliminating .extractionFailed as a live outcome on a genuinely closed tableau -- it is gated on
this task's allClosed_derivable induction as a prerequisite and consumes it once landed. This
task's own acceptance criteria are unchanged by 482's existence; 482 is a downstream consumer,
not an addition to this task's scope.

---

### 411. Prove hard admissibility lemmas for until since trichotomy discrete and dedekind rules
- **Effort**: 15-20 hours
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 165, Task 410

**Description**: Track B part 2 for the TM tableau decidability program (parent: task 165; grounding: reports/02_tableau-decidability-hard-research.md sections 3.2-3.3 and 10). First run a /literature acquisition pass for Reynolds 1992 and Reynolds 2003 (the untlNeg co-decomposition and the Dedekind gap axioms; report 02 section 10 flags in-repo literature as thin). Then prove the hard admissibility block in Verified/Refutation/Rules/{UntilSince,Trichotomy,Discrete,Dense,Dedekind}.lean: untlPos (branch 1 via until_F, branch 2 via self_accum_until — follow the axiom literally), untlNeg (Reynolds co-decomposition via absorb_until + left_mono_until_G; the single largest lemma — budget it its own dispatch), sncePos/snceNeg duals, orderTrichotomy (one-liner if Phase 2.2 kept branches syntactically equal to temp_linearity disjuncts — verify, do not assume), z1Rule (two-premise instance of z1 + two modus ponens, relies on same-label internalization from the predecessor task), densityRule/denseIndicatorClosure via density/dense_indicator, and the Dedekind rules via prior_U_gap/prior_S_gap/sep. Acceptance: all admissibility lemmas sorry-free; lake build green.

---

### 410. Internalize tableau branches and prove routine rule admissibility
- **Effort**: 12-18 hours
- **Status**: [PLANNED]
- **Task Type**: lean4
- **Topic**: decidability
- **Dependencies**: Task 165, Task 429
- **Research**: [410_internalize_tableau_branches_and_prove_routine_rule_admissibility/reports/01_internalize-routine-admissibility.md]
- **Plan**: [410_internalize_tableau_branches_and_prove_routine_rule_admissibility/plans/01_internalize-routine-admissibility.md]

**Description**: Track B part 1 for the TM tableau decidability program (parent: task 165, plan plans/01_tableau-decidability-two-track.md, research reports/02_tableau-decidability-hard-research.md sections 3.1-3.4). Create FormalSystem/Metalogic/Decidability/Verified/Internalize.lean defining Branch.internalize (world labels via box/diamond nesting, time labels via U/S guards realizing the branch TimeOrdering; SETTLED constraints: internalization design over substitution — no cut or uniform-substitution admissibility exists in the tree — and z1Rule's two premises must stay at the same label). Then prove the routine admissibility lemmas in Verified/Refutation/Rules/{Propositional,Modal,Temporal}.lean (~21 lemmas: 8 propositional, 4 S5 modal, 1 boxTemporal, 8 temporal universal/existential), each stated as rule_admissible per report 02 section 3.1 with hypothesis ruleFrameClass r <= fc, reusing Combinators.lean, ModalS5.lean, TemporalDerived.lean, GeneralizedNecessitation.lean, and DeductionTheorem.lean via DerivationTree.lift. Acceptance: all lemmas sorry-free, lake build green, RuleSpec GATE lemmas still green.

---

### 298. Fix c7 labeling bug and regenerate dataset
- **Status**: [PARTIAL]
- **Task Type**: lean4
- **Topic**: dataset-enhancement
- **Dependencies**: Task 297, Task 343
- **Research**: [298_fix_c7_labeling_bug_and_regenerate_dataset/reports/01_c7-labeling-bug.md]
- **Plan**: [298_fix_c7_labeling_bug_and_regenerate_dataset/plans/01_c7-labeling-bug.md]
- **Summary**:
  - [298_fix_c7_labeling_bug_and_regenerate_dataset/summaries/01_c7-labeling-bug-summary.md]
  - [298_fix_c7_labeling_bug_and_regenerate_dataset/summaries/01_c7-labeling-bug-summary.md]

**Description**: Fix c7 labeling bug at formula ~13750 that causes unbounded memory growth in the decision procedure's timeout handling, then regenerate the full c7 dataset. During task 297 dataset regeneration, all 3 attempts to generate c7 stalled at exactly record 13,749 with RSS growing ~40MB/6s. The labeling function enters an apparent infinite loop or unbounded search for formula #13,750 in the sorted enumeration order. The timeout mechanism either does not fire or cannot interrupt the stuck state. Steps: (1) Identify the specific formula at position ~13,750 in the c7 enumeration. (2) Reproduce the hang in isolation with that formula. (3) Diagnose whether the decision procedure's timeout is failing to fire or the procedure is in an uninterruptible state. (4) Fix the timeout handling so it reliably terminates. (5) Regenerate the full c7 dataset (target: 77,272 records)

---

### 296. Re add derived binary operators with dedup fix
- **Status**: [PARTIAL]
- **Task Type**: lean4
- **Topic**: dataset-enhancement
- **Dependencies**: Task 295, Task 298
- **Research**: [296_re_add_derived_binary_operators_with_dedup_fix/reports/01_derived-binary-operators.md]
- **Plan**: [296_re_add_derived_binary_operators_with_dedup_fix/plans/01_derived-binary-operators-plan.md]
- **Summary**: [296_re_add_derived_binary_operators_with_dedup_fix/summaries/01_derived-binary-operators-summary.md]

**Description**: Re-add the 6 derived binary temporal operators (release, weak_until, trigger, weak_since, strong_release, strong_trigger) to the formula enumerator, adjusting canonicalization and/or the passesFilter gate so they survive deduplication and appear in the unique pipeline output. These operators were removed in task 295 because they inflated the enumeration space by ~40-60% without contributing unique formulas — their canonical representations collapsed with primitives. Potential approaches: (1) skip canonicalization for formulas containing derived binary operators, (2) canonicalize to the derived form instead of the primitive form, (3) lower or remove the passesFilter complexity gate for these operators, (4) add a fold-aware dedup stage that treats release(p,q) as distinct from neg(untl(neg p, neg q)). The goal is to have all 13 derived operators represented in the final dataset.

---

### 282. Exhaustive enumeration by default
- **Status**: [PARTIAL]
- **Task Type**: lean4
- **Topic**: dataset-enhancement
- **Dependencies**: Task 274, Task 298
- **Plan**: [282_exhaustive_enumeration_by_default/plans/01_exhaustive-enumeration-plan.md]
- **Research**: [282_exhaustive_enumeration_by_default/reports/01_exhaustive-enumeration-default.md]
- **Summary**: [282_exhaustive_enumeration_by_default/summaries/01_exhaustive-enumeration-summary.md]

**Description**: Flip complexity-9 dataset generation from stratified to exhaustive-by-default once feasibility is confirmed. Prior work (see plans/01_exhaustive-enumeration-plan.md, handoffs/phase-1-6-handoff-20260714.md) verified the 0-sentinel/.take-guard machinery is already correct and unlimited-capable, and corrected stale infeasibility claims in data/README.md and scripts/run_dataset_generation.sh. The next action is the deferred c9 feasibility probe (Plan Phase 2), followed -- pending a GO verdict and explicit user approval for the multi-hour compute -- by c8/c9 exhaustive regeneration and HF Hub republication (Phases 3, 4(rest), 5, 6(rest), 7).

---

### 257. Large data storage huggingface
- **Status**: [BLOCKED]
- **Task Type**: general
- **Topic**: dataset-enhancement
- **Dependencies**: None
- **Research**: [257_large_data_storage_huggingface/reports/01_large-data-storage.md]
- **Plan**: [257_large_data_storage_huggingface/plans/01_implementation-plan.md]
- **Summary**: [257_large_data_storage_huggingface/summaries/01_execution-summary.md]

**Description**: Complete the Hugging Face Hub migration for large dataset storage. Prior work (see plans/01_implementation-plan.md, summaries/01_execution-summary.md) removed Git LFS tracking from .gitattributes and rewrote data/README.md to point at HF Hub (logos-labs/bmlogic-bench) as the canonical source, but Phase 1 -- the actual upload to HF Hub via the existing data/hf-dataset/upload.py pipeline -- was never executed because it requires user HF authentication. This task is blocked on that credential; once supplied, run the upload, validate, and confirm data/hf-dataset/PUBLISHING.md's 'Migration Status' header reflects completion.

---

### 231. Dataset regeneration automation
- **Status**: [NOT STARTED]
- **Task Type**: general
- **Topic**: dataset-enhancement
- **Dependencies**: Task 230, Task 298

**Description**: Build comprehensive automation so that every dataset regeneration automatically updates all downstream artifacts and documentation fields. Supersedes task 227 scope. (1) Create data/scripts/sync-all.py master sync script that: (a) Scans all JSONL files and recomputes metadata JSON files (record counts, rule distributions, schema field lists, valid/invalid ratios, tier distributions, step statistics). (b) Updates specific fields in data/README.md: file inventory table (Records, Size columns), training record schema table (field count), proof steps statistics (records, theorems, rule distribution, steps per theorem), cross-logic split table (records, valid rates), NL paraphrase statistics. (c) Updates specific fields in data/dataset-card.md: overview table, all record counts, proof steps section, competitive position 'primary gaps' paragraph. (d) Recomputes SHA-256 hashes and contentSize for all distributions in croissant.json. (e) Regenerates bmlogic-bench-splits.json. (f) Validates all JSONL records against declared schemas (checks field presence, types, null patterns). (g) Checks train/benchmark formula overlap and reports contamination percentage. (h) Validates metadata key consistency (total_records not total_count). (2) Idempotent and safe to run after any regeneration command (lake exe dataset_generator, lake exe proof_extractor, lake exe benchmark_oracle, finalize_benchmark.py). (3) --dry-run mode that reports what would change. (4) --commit mode that creates structured git commit. (5) CI-friendly exit codes (0=clean, 1=staleness detected, 2=validation error). (6) Update data/README.md with pipeline documentation. (7) Integrate into agent context (.claude/context/project/dataset/) so /implement for dataset tasks runs sync-all as post-implementation step. Note: supersedes task 227 (dataset_pipeline_automation_croissant_sync) with broader scope covering README/dataset-card field updates and schema validation.
=== ITEM (7) TARGETS A DISPOSABLE DEPLOY ARTIFACT -- CORRECTED 2026-08-24 ===

Item (7) above says "Integrate into agent context (.claude/context/project/dataset/)". DO NOT WRITE
THERE. Verified 2026-08-24: `.claude/` in this repository is fully gitignored (`.gitignore:81`) with
zero tracked files, and is regenerated wholesale from a source store that is NOT in this repository
-- it lives at /home/benjamin/.config/nvim/agent-system/, a separate git repo. A file written to
`.claude/context/project/dataset/` will be silently destroyed on the user's next agent-system
reload.

Item (7) therefore CANNOT be completed from inside this repository. Two acceptable dispositions,
both of which require asking the user first:

  (a) DROP item (7) from this task's scope and record why. The other seven sub-targets of this task
      are ordinary repository work (`data/scripts/sync-all.py`, `data/README.md`,
      `data/dataset-card.md`, `croissant.json`, the splits file, schema validation, contamination
      check) and are unaffected. This is the recommended default -- it keeps the task in one repo.
  (b) Split item (7) into a task filed in the nvim repository's own tracker
      (/home/benjamin/.config/nvim/specs/state.json), targeting
      agent-system/extensions/<appropriate-extension>/context/, and committed there.

Do not silently satisfy item (7) by writing into `.claude/`.
=== ITEM (7) DROPPED FROM SCOPE -- 2026-08-24, user decision ===

Item (7) ("Integrate into agent context (.claude/context/project/dataset/) so /implement for
dataset tasks runs sync-all as post-implementation step") is REMOVED from this task's scope. It is
not a defect and not deferred -- it is out of scope here, permanently, and no successor task owns
it in this repository.

WHY. The disposition options recorded above were put to the user on 2026-08-24 and option (a) was
chosen. Three considerations decided it:

  1. `.claude/` here is gitignored (`.gitignore:81`, zero tracked files) and regenerated wholesale
     from /home/benjamin/.config/nvim/agent-system/, a separate git repo. A file written to
     `.claude/context/project/dataset/` is destroyed on the next agent-system reload.
  2. Filing it in the nvim tracker instead was considered and declined. There is no `dataset`
     extension in that source store (verified 2026-08-24: core, cslib, email, epidemiology,
     filetypes, formal, founder, latex, lean, literature, memory, nix, nvim, present, python,
     slidev, typst, web, z3), and a BimodalLogic-specific post-implementation hook placed in the
     shared global agent-system would deploy to every repository that loads it. It would have to be
     generalized into a repo-local hook mechanism first -- a different and larger piece of work
     than this task.
  3. The `.syncprotect` escape hatch (project root; honored by deploy-headless.sh and the picker's
     sync path) would survive a reload, but leaves the file untracked and unbacked-up in a repo
     where everything else is version-controlled.

WHAT REMAINS IN SCOPE. Items (1) through (6) and (8), unchanged and unaffected -- they are ordinary
repository work under `data/`: `data/scripts/sync-all.py`, `data/README.md`,
`data/dataset-card.md`, `croissant.json`, `bmlogic-bench-splits.json`, schema validation, the
train/benchmark contamination check, and the metadata-key consistency check. Do not treat the
removal of item (7) as reducing any of them.

IF THE HOOK IS WANTED LATER. `sync-all.py` is a plain script with CI-friendly exit codes (item 5).
Wire it from repository CI or run it manually after a regeneration. That reaches the same outcome
without depending on agent-system context at all.

---

### 219. Llm baseline difficulty calibration
- **Status**: [RESEARCHED]
- **Task Type**: general
- **Topic**: dataset-enhancement
- **Dependencies**: Task 231
- **Research**: [219_llm_baseline_difficulty_calibration/reports/01_llm-baseline-research.md]

**Description**: Run bmlogic-bench through multiple LLMs to establish baseline difficulty calibration. Evaluate at least 3 models (GPT-4o, Claude Sonnet, a 7B open model). Report zero-shot accuracy per difficulty tier (easy/medium/hard/very_hard), chain-of-thought vs direct label accuracy, error rate correlation with modal/temporal depth. Include random baseline (50% for balanced benchmark). Publish results in data/baselines/README.md with methodology. Both symbolic formula input and NL paraphrase input (if available from R1).

---

### 193. Codebase tactic refactor
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: automation
- **Dependencies**: Task 165, Task 402, Task 448, Task 470, Task 508, Task 519, Task 521, Task 522
- **Research**: [193_codebase_tactic_refactor/reports/01_codebase-refactor-seed.md]

**Description**: Apply validity-intro and truth-simp macros to the soundness layer.

RE-SCOPED 2026-07-26 by the codebase tactic survey (now archived at specs/archive/196_codebase_tactic_survey/reports/02_automation-survey.md section 6.3). The original charter targeted Theorems/ using tm_prove. Theorems/ is 7,017 lines - 3.8% of the tree, half the relative share the 2026-05 research assumed - and is sorry-free and stable; tm_prove (task 192) is abandoned; and the search-family tactics it would have fallen back on have zero adoption. The task keeps its kind (an application pass that reduces existing proof text) and replaces its target and its instrument.

Define a small family of syntactic macros and apply them mechanically to the three files that concentrate the codebase two highest-frequency verbatim proof repetitions. This is an APPLICATION task: the deliverable is measured reduction in existing proof text at named files, not the existence of a macro.

Macros to define (single-line `macro ... : tactic` declarations - no elaboration, no goal inspection):
  - intros_validity           for `intro F M Omega _h_sc τ _h_mem t`
  - intros_validity_framed    for the frame-condition-prefixed variant
  - simp_truth                for the recurring `simp only [TruthAt, Truth.future_iff, Truth.past_iff, Truth.some_future_iff, Truth.some_past_iff]` bundle
  - unfold_validity           composing intros_validity with simp_truth, for sites where the two appear consecutively

NAMING NOTE (2026-07-27): the simp head symbol is `TruthAt`, not the pre-upgrade `truth_at` -- the systematic Mathlib naming upgrade renamed it. The `Truth.*_iff` names above are unchanged (declared in FormalSystem/Semantics/Truth.lean at :220 some_future_iff, :239 some_past_iff, :258 future_iff, :278 past_iff).

Measured target sites (re-verified 2026-07-27 against the working tree, Boneyard/ excluded; counts unchanged from the 2026-07-26 measurement, only the paths and the simp head symbol were restated):
  - FormalSystem/Metalogic/SoundnessLemmas/DenseValidity.lean      - 92 `intro F M Omega`, 54 `simp only [TruthAt`
  - FormalSystem/Metalogic/SoundnessLemmas/FrameClassVariants.lean - 56 `intro F M Omega`, 30 `simp only [TruthAt`
  - FormalSystem/Metalogic/Soundness.lean                          -  0 `intro F M Omega`, 47 `simp only [TruthAt`

DO BOTH MACRO GROUPS AS ONE PASS over the same files, not two. Splitting them edits the same two files twice and forfeits the unfold_validity collapse.

COMPLETION CRITERION: `intro F M Omega` occurrences in the two SoundnessLemmas/ files reach zero; `simp only [TruthAt` occurrences across the three files fall by at least 80%; lake build green; executable sorry count unchanged at 1, located BY CONTENT in FormalSystem/Metalogic/WeakCanonical/Transfer.lean, never by line number. A task that ends with working macros and unchanged proof text has FAILED.

EXPLICITLY OUT OF SCOPE: Theorems/ refactoring, tm_prove, modal_search and every other search-family tactic, and any new elaborated tactic. See the survey report section 5 for the measured evidence (38 real proof-site invocations across ~5,800 lines of proof automation, all 38 in one file).

DEPENDENCY ON THE SYSTEMATIC MATHLIB NAMING UPGRADE -- NOW DISCHARGED (2026-07-27): this task rewrites proof bodies at roughly 330 sites, and the naming-upgrade task rewrote the same reference graph at 24,364 sites while moving every file from Theories/Bimodal/ to FormalSystem/. A mass proof rewrite must not race a mass rename, so this task was held until that rename landed. It HAS landed -- the naming-upgrade task is status `completed` -- so the precondition is satisfied and this task is NOT blocked. Every path in this description, and every entry in file_scope, is now stated in its post-rename FormalSystem/ form; `Theories/Bimodal/` appears above only as the historical source of that move, never as a path to open.

Inventory groups drawn on: survey report section 4.2 groups 2 (intros_validity, score 153) and 3 (simp_truth, score 72.7).

=== RE-SCOPED 2026-09-01 by specs/reviews/review-2026-09-01-lean-engineering.md (findings A-13, D-06, D-10, D-20) ===
DROP the intros_validity / intros_validity_framed / unfold_validity macros: the tactics review (D-20) recommends AGAINST a binder macro (macro hygiene makes F/M/τ/t inaccessible at the call site, so it is strictly worse than `intro`); the 231 intro-chains are instead normalised to one spelling by task 522. KEEP the simp_truth half, but retarget it: task 521 DEFINES the truth simp-normal form (`Truth.and_iff` etc. as @[simp], `register_simp_attr truth_norm`, `macro truth_simp`) and rewrites the ten worst soundness proofs as its proof of concept; THIS task is the mechanical application pass of `truth_simp`/`swap_norm` across the REST of Metalogic/Soundness.lean and Metalogic/SoundnessLemmas/FrameClassVariants.lean. The original target DenseValidity.lean (92 intros / 54 simps) is DELETED by task 519, so do not touch it. DEPENDS ON 519 (deletion first, or 600 lines are rewritten and then removed) and 521 (the set must exist). COMPLETION CRITERION, restated: `simp only [TruthAt` occurrences across Soundness.lean and FrameClassVariants.lean fall by at least 80%; lake build green; C2 baseline unchanged.

---

### 178. Publication examples and demo
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: formula-refactor
- **Dependencies**: Task 131, Task 193, Task 402

**Description**: Expand Examples/ with publication-quality demonstrations of the full verified pipeline. Complete worked example showing soundness and completeness on a concrete formula, plus decidability of the propositional fragment (genuinely complete today, per the soundness/completeness metatheory's axiom-clean status). Examples exercising each frame class with FrameClass-parameterized DerivationTree. Examples of the expressive completeness result. Update BimodalProofs.lean and TemporalStructures.lean. All examples sorry-free.

REALIGNMENT CORRECTION (task 468, 2026-08-25, carried from specs/reviews/review-2026-08-24.md
amendment M-7, independently re-confirmed at realignment time): the struck original acceptance
criterion above ("Complete worked example showing soundness-completeness-decidability on a
concrete formula") is RESCOPED. Decidability of TM (the full bimodal logic) is still open --
re-confirmed fresh this dispatch: grep -rn "isValid" FormalSystem/Metalogic/Decidability/ shows no
declaration takes DecisionProcedure.isValid as its subject, and ruleSound_of_mem_allRulesForFC is
not lifted to any allClosed -> valid theorem. `truthAt_of_isValid`
(Verified/Decidable.lean:2412) is NOT evidence of decidability -- it concerns a different,
semantic-side `SoundnessLemmas.IsValid`, not the decision procedure's `DecisionProcedure.isValid`.
Do not cite it as such. This task's decidability example is therefore rescoped to the
propositional-fragment case (genuinely decidable today) rather than the full logic; a full-logic
decidability example remains gated on the decidability/tableau front (410-465,
480-482) landing.

---

### 177. Update readme and module docstrings
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: formula-refactor
- **Dependencies**: Task 131, Task 193, Task 402, Task 426, Task 428, Task 429, Task 430, Task 432, Task 433, Task 434, Task 440, Task 441, Task 448, Task 494, Task 510, Task 513, Task 524, Task 526, Task 530, Task 533

**Description**: Update README.md, docs/, and FormalSystem/ module-level docstrings to their final post-refactor state, once the decidability chain (426, 428, 429, 430, 432, 433, 434) lands. This is the final polish pass, distinct from and run after task 472's already-completed immediate correction pass. Explicitly excludes: every item task 472 already corrected (the Decidability.lean Status block, Verified/README.md, FMP/README.md, DecisionProcedure.lean's decideAuto docstring, Verified/Decidable.lean's Status docstring, WeakCanonical.lean, RealModel/ShuffleReal.lean, Soundness.lean, PriorExpressivenessDense.lean) and the two Kamp files task 473 already swept (Kamp/EANegationClosure.lean, NfMultiAnchorBridge/NavigatedSpine.lean). This task's residual content is: re-auditing all touched documentation for drift accumulated during the decidability chain's landing (472/473 audited a snapshot; the chain's remaining tasks will touch further files after 472/473 ran), and the Axiom Reference update the charter names as part of 177's original scope.

REALIGNMENT NOTE (task 468, 2026-08-25, verdict per specs/468_realign_task_programme_from_proof_state_audit/reports/02_stage1-verification-and-programme-realignment.md §6): DIVIDE, already half-executed exactly as specs/reviews/review-2026-08-24.md amendment 10f states -- tasks 472 (documentation correction pass) and 473 (Kamp vacuity deletion) already ran the ungated half; the description above is the remaining, gated half's text. `file_scope` (README.md, specs/ROADMAP.md, FormalSystem/, docs/) was already repaired by task 470 item (G) and is confirmed resolvable, no duplicate -- left unchanged here.

=== DEPENDENCY ADDED 2026-09-01 ===
Task 530 (documentation single source of truth + theorem index, from specs/reviews/review-2026-09-01-lean-engineering.md) is the UN-GATED metalogic half of this charter and is now a dependency; this task remains the gated post-decidability-chain pass and its residual shrinks to re-auditing drift the decidability chain introduces plus the Axiom Reference update.

---

### 128. Open set operator dense continuous
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: frame-extensions
- **Dependencies**: None

**Description**: Add topological open set (interior) operator for dense and continuous temporal frames. On discrete ℤ the interior is trivial (discrete topology), but on dense ℚ and continuous ℝ it captures neighborhood-stable truth: Int(φ) true at t iff φ holds in an open neighborhood of t. Related to Dynamic Topological Logic (Kremer-Mints 2005), McKinsey-Tarski topological semantics for S4, and Fernandez-Duque intuitionistic temporal logic. Phase 1: add TopologicalSpace instance to TaskFrame for dense/continuous cases. Phase 2: add interior constructor to Formula with truth clause. Phase 3: axioms (S4-like: Int(φ)→φ, Int(φ)→Int(Int(φ))). Phase 4: interaction with temporal operators and S5 □. Note: DTL is not finitely axiomatizable (Fernandez-Duque 2014) — completeness may require non-standard techniques.

---

### 127. Time addition operator
- **Status**: [NOT STARTED]
- **Task Type**: lean4
- **Topic**: frame-extensions
- **Dependencies**: None

**Description**: Add time addition operator (+) to the bimodal logic TM. φ + ψ is true at (τ, x) iff ∃ y,z with x = y+z, φ true at (τ,y), ψ true at (τ,z). This internalizes the AddCommGroup structure of D into the object language, extending expressive power from FO[<] to FO[<,+] (Presburger arithmetic). Related to arrow logic (Venema), relevant logic (Routley-Meyer ternary frames), and separation logic (BI). Phase 1: add tadd/tsub constructors to Formula, truth clause in semantics. Phase 2: basic axioms (associativity, commutativity, identity, inverse). Phase 3: soundness proofs. Phase 4: interaction with G/H/U/S/□. Completeness (ternary canonical model) and decidability are open research problems — defer to later phases.

---

### 125. Jonsson tarski representation bimodal sus
- **Status**: [NOT STARTED]
- **Task Type**: formal
- **Topic**: algebraic-representation
- **Dependencies**: Task 420, Task 439, Task 461, Task 498, Task 499, Task 528

**Description**: CAPSTONE of the algebraic representation front. Prove the Jonsson-Tarski representation theorem for the bimodal logic: the embedding eta(a) = {U | a in U} is an injective STSA homomorphism A -> Cm(Uf(A)).

RE-SCOPED. This task's original four phases are now distributed: Phase 1 (complex algebra Cm(F)) and Phase 2 (ultrafilter frame Uf(A), including the Spherical obligation) are separately tasked and are this task's dependencies; Phase 4 (binary untl/snce operators) is separately tasked and depends on this one. What remains here is Phase 3 -- the embedding itself and its injectivity -- stated at the unary signature (box, G, H, sigma).

PREREQUISITE STATE, RE-VERIFIED 2026-08-26: the STSA class and the R_G/R_H/R_Box ultrafilter frame exist as Boneyard seeds behind #exit and are ported by the dependency tasks. The MCS-to-ultrafilter bijection is live at Algebraic/UltrafilterMCS.lean:782 (ultrafilter_correspondence), though stated existentially rather than as a named Equiv -- converting it to an Equiv may be worth doing here. The BooleanAlgebra LindenbaumAlg instance is at BooleanStructure.lean:421.

THE PRIOR PREREQUISITE LIST IN THIS DESCRIPTION IS STALE and is superseded: it named 'resolve 6 algebraic sorries in TenseS5Algebra/InteriorOperators/LindenbaumQuotient'. InteriorOperators.lean and LindenbaumQuotient.lean are sorry-free today; the remaining sorries are the 3 in the Boneyard TenseS5Algebra seed, and they are for REMOVED axioms (temp_a, temp_l) that must be restated against the current 45-constructor axiom set rather than proved as-is. That is the STSA port task's business, not this one's.

LITERATURE: Goldblatt 1989 'Varieties of complex algebras' (APAL 44, 173-242, doi 10.1016/0168-0072(89)90032-8) has been acquired. CAVEAT THAT MUST BE HONORED: the acquired PDF is an Acrobat 3.0 Capture scan with a badly degraded OCR text layer -- math-heavy pages yield mangled symbols, dropped and reordered lines. READ THE PAGE IMAGES DIRECTLY (the Read tool's pages parameter); do NOT rely on a pdftotext-derived conversion for any axiom statement or equation. Blackburn/de Rijke/Venema 2002 Chapter 5 (corpus entry blackburn_2002) is the primary reference and is born-digital.

MATHLIB HOOK: Order/Atoms.lean:710 (toSetOfIsAtom : alpha <-> Set {a // IsAtom a} for CompleteAtomicBooleanAlgebra) is the atom-structure half of Stone/Jonsson-Tarski for the complete atomic case and is the single most relevant Mathlib lemma here; supporting lemma eq_setOf_le_sSup_and_isAtom at :695. Mathlib has NO Stone duality for Boolean algebras and no BAO machinery -- the rest is greenfield.

SEE ALSO the reconciliation task on whether this embedding can be factored through ShiftSet.lean's reverse_repr rather than built independently; if it can, that supersedes part of this task's construction and this description should be revised again before implementation starts.

=== DEPENDENCY ADDED 2026-09-01 ===
Task 528 (Algebraic/ modernisation: propDecide in BooleanStructure.lean, SetMaximalConsistent.ultrafilterEquiv as a named Equiv, the bespoke `Ultrafilter` structure reconciled with Mathlib Order.PFilter/Ideal.IsPrime, Multiset.inf; from specs/reviews/review-2026-09-01-lean-engineering.md findings D-08, F-11, F-12, F-13) must land first so this task builds on the modernised algebra rather than inheriting a shadowed Ultrafilter name and ~430 lines of hand-built Boolean algebra.
