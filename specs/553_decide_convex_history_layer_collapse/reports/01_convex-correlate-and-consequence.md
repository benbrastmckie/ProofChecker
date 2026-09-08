# The Convex-History Layer: Categorical Correlate and Alternative Consequence Relations

- **Task**: 553
- **Plan**: `specs/553_decide_convex_history_layer_collapse/plans/01_convex-correlate-and-consequence-study.md`
- **Type**: study (research-only; no edit to `FormalSystem/`)
- **Paper of record**: `/home/benjamin/Philosophy/Papers/PossibleWorlds/JPL/possible_worlds.tex`

## §0. Scope and method

This study answers the task's questions (a)–(e) and the two questions the dispatch's User focus
adds: what the alternative consequence relations are and what logics they give, and what the
paper's categorical appendix `app:Structure` and this repository have to teach each other.

**Method.** Every quantitative claim below is accompanied by the command that produced it, run
from the repository root against the working tree at the time of writing. Every logical claim
that a probe can settle is settled by a probe under
`specs/553_decide_convex_history_layer_collapse/probes/`, compiled with `lake env lean <path>`;
probes are never added to the library or to any import graph. Claims that were *not* machine-
checked are marked as arguments, and §7.4 lists what remains open.

**Anchors used.** Paper anchors are cited by `\label`, never by line number, except where the
line number is the only address a commented-out sentence has. The two paper locations that carry
this study are `app:Structure` (the topological/categorical appendix, `\label{app:Structure}`,
carrying a `% TODO: review in full` marker in the source) and the alternative-semantics footnote
attached to the chess example in the body (source line 1102 of the `.tex`).

**Vocabulary.** Following the completed history-vocabulary alignment, `PartialHistory F` is the
paper's *partial history*, `ConvexHistory F` its *convex history*, and `TaskFrame.HF F` (the
`IsTotal` subtype of `ConvexHistory F`) its *possible world*. There is deliberately no
`PossibleWorld` abbreviation; where this report writes "a total index" it means the `HF` tier.

---

## §1. Evidence audit

The task description supplies four evidence claims under "EVIDENCE ALREADY GATHERED", with the
standing instruction to verify rather than re-derive, and to report whatever turns out to be
wrong. Each is given a verdict below.

### §1.0 Measurements, and the metric problem

The description's numbers and this study's numbers are not measuring the same thing. The
description reports *lines*; several of its figures are reproducible only as *occurrences*. Both
are recorded here.

| Quantity | Command | Lines | Occurrences |
|---|---|---:|---:|
| `IsTotal` | `grep -rn "IsTotal" FormalSystem/ --include=*.lean \| wc -l` / `grep -ro` | 305 | 326 |
| `.domain` | `grep -rn "\.domain" FormalSystem/ --include=*.lean \| wc -l` / `grep -ro` | 228 | 295 |
| `ConvexHistory` | `grep -rn "ConvexHistory" FormalSystem/ --include=*.lean \| wc -l` / `grep -ro` | 593 | 626 |
| `.convex` (all fields) | `grep -rn "\.convex" FormalSystem/ --include=*.lean \| wc -l` | 21 | — |
| `convex :=` (all structures) | `grep -rn "convex :=" FormalSystem/ --include=*.lean \| wc -l` | 22 | — |
| `presheaf` (case-insensitive) | `grep -rin "presheaf" FormalSystem/ --include=*.lean \| wc -l` | 0 | — |
| files mentioning `IsTotal` | `grep -rl "IsTotal" FormalSystem/ --include=*.lean \| wc -l` | 58 | — |

### §1.1 Claim 1 — "the convex layer looks vestigial" — **CONFIRMED, and strengthened**

The claim is that every concrete construction with a non-total domain lives at the
`PartialHistory` layer, and that the only convex-layer constructions whose `domain` is not
`fun _ => True` are the generic transports.

*Method*: `grep -rn "convex :=" FormalSystem/ --include=*.lean` enumerates every discharge of a
field literally named `convex`; each site was then read and classified by the structure it
belongs to and by the `domain` it carries.

Of the 22 `convex :=` sites, **four belong to other structures entirely** — they discharge
`IsContempEquivDense.convex` and the `isBad`/`hbi` convexity fields in the dense-model-surgery and
real-model machinery, not `ConvexHistory.convex`:

- `Metalogic/WeakCanonical/DenseModelSurgery/TruthTransfer.lean:719`
- `Metalogic/WeakCanonical/DenseModelSurgery/Defs.lean:435`, `:673`
- `Metalogic/WeakCanonical/DenseModelSurgery/Dual.lean:510`

That leaves **18 genuine `ConvexHistory` constructions**, which classify as follows.

| Class | Count | Sites |
|---|---:|---|
| Total by construction (`domain := fun _ => True`, or an `IsTotal` hypothesis) | 15 | `Semantics/ConvexHistory.lean:184` (`ofTotal`); `Semantics/Extension/Extension.lean:153` (`toConvexHistory`, which *takes* `τ.IsTotal`); `Semantics/Correspondence/DurationFrames.lean:126`, `:200`; `Metalogic/DiscreteNonCompactness.lean:167`; `Metalogic/Independence/ClockFrame.lean:228`; `Metalogic/Independence/CoNotPriorU.lean:393`; `Metalogic/Algebraic/FlowFrame.lean:183`; `Metalogic/WeakCanonical/IntegerModel/ReynoldsBridge.lean:528`, `:814`; `Metalogic/Decidability/Verified/Bridge/RegionFrame.lean:322`; `Examples/TemporalStructures.lean:315`, `:433`; `Boneyard/ChainCompleteness/Bundle/SuccChainWorldHistory.lean:149`; `Boneyard/StrictSemanticsLegacy/Bundle/CanonicalConstruction.lean:299` |
| Generic transport (carries through whatever domain it is handed) | 3 | `Semantics/ConvexHistory.lean:336` (`timeShift`); `Semantics/IntTransfer.lean:209`, `:268` |
| Genuinely bounded (a concrete non-total convex domain) | **0** | — |

The description named `timeShift` and the two `IntTransfer` directions as the only non-`fun _ =>
True` sites; that is exactly right. The audit **strengthens** the claim in one place the
description did not reach: `PartialHistory.toConvexHistory`
(`Semantics/Extension/Extension.lean:151`) is the tree's *only* promotion from the partial layer
to the convex layer, and it is gated on `τ.IsTotal` and discharges `convex` by `total_isConvex`.
There is therefore no route in the library by which a bounded partial history becomes a
`ConvexHistory` at all — the Extension Theorem's own promotion step goes straight from partial to
*total*, skipping the bounded convex tier entirely. The middle tier is not merely unused; it is
unreachable by construction from the one place a bounded history could have entered it.

The description's own concrete non-total sites at the partial layer were re-checked and hold:
`Semantics/Extension/Extension.lean:227` (`point`, `domain := fun t => t = x`),
`Semantics/Extension/Admissible.lean:239` (`adjoinDomain`),
`Semantics/PartialHistoryOrder.lean:126`, `:193`.

**Completeness of the hunt** (the plan's stated risk). Constructions were sought by three
independent routes, not one: (i) `grep "convex :="`, which catches every record-syntax and
structure-instance site; (ii) `grep "ConvexHistory.mk"`, which catches explicit constructor
applications — all six hits are `change`-target spellings inside `timeShift` re-establishment
proofs in `FlowFrame.lean` and `ReynoldsBridge.lean`, not constructions; (iii) `grep "ofTotal"`
and `grep "toConvexHistory"`, which catch every use of the two named smart constructors. The
three routes agree, and no site escapes all three, because `ConvexHistory` has exactly one
constructor and any value of the type must arise through it — directly, or through `ofTotal` /
`toConvexHistory` / `timeShift` / the `IntTransfer` pair.

### §1.2 Claim 2 — "`convex` is discharged 22 times and consumed essentially never" — **CORRECTED (in the repository's favour)**

*Discharge count*: 22 is right as a count of `convex :=` lines, but 4 of those belong to other
structures (§1.1), so the `ConvexHistory.convex` field is discharged **18** times, of which 2 are
in `Boneyard/`. The live count is **16**.

*Consumption*: `grep -rn "\.convex" FormalSystem/ --include=*.lean` returns 21 lines. Of these,
**exactly three** are the projection applied to a history value:

- `Semantics/ConvexHistory.lean:343` — inside `timeShift`, re-establishing convexity of the shifted domain
- `Semantics/IntTransfer.lean:211`, `:270` — the two transfer directions, likewise

The remaining 18 are `hε.convex`, `hS.isBad.convex`, `h.convex` and `hbi.convex` in
`DenseModelSurgery/` and `RealModel/DoetsTheorem.lean` — unrelated fields, as the description
said. So the description's "consumed essentially never" is not merely essentially true: the
convexity field is consumed **only** to reprove itself under the two generic transports. No
theorem in the tree uses convexity to prove anything else. The description undersold this.

### §1.3 Claim 3 — "the generality has a real price" — **CONFIRMED, with the numbers restated as occurrences**

`IsTotal`: 305 lines / 326 occurrences across 58 files (description: "322 lines"; the figure is
reproducible today as an occurrence count, not a line count, and both have moved with the tree).
`.domain`: 228 lines / 295 occurrences (description: "198 lines"). `.states` with an explicit
second (domain-proof) argument: 249 sites, by
`grep -rno "\.states [a-zA-Z0-9_']* [a-zA-Z0-9_']*" FormalSystem/ --include=*.lean | wc -l`
(description: "roughly 85"). That last divergence is large and in the direction that makes the
description's case *stronger*, not weaker; the description's figure appears to predate the
history-vocabulary rename.

The atom clause does carry the domain existential, as claimed
(`Semantics/Truth.lean`, `TruthAt`'s `Formula.atom` case:
`∃ (ht : τ.domain t), M.valuation (τ.states t ht) p`), and its own docstring already records this
as "Decision A, accepted gap" — the paper's `def:BL-semantics` atom clause has no domain
conjunct.

The bundled/predicate bridge inventory is confirmed and is slightly larger than the description
listed. In `Semantics/Validity.lean` alone:

| Bridge | Line |
|---|---:|
| `SemanticConsequence.of_forall` / `.apply` | 136 / 143 |
| `SemanticConsequenceIn.of_forall_total` / `.apply_total` | 158 / 167 |
| `TaskFrame.validOn_iff_total` | 290 |
| `Valid.of_forall_total` / `Valid.apply` | 419 / 427 |
| `ValidOnFrames.of_forall_total` / `.apply_total` | 527 / 534 |
| `ValidIn.of_forall_total` / `.apply_total` | 540 / 547 |

Twelve declarations, six matched pairs, each existing for no reason but to convert between
`(τ : ConvexHistory F) (hτ : τ.IsTotal)` and `(τ : F.HF)` — two spellings of the paper's one
notion. `TaskFrame.HF` is itself defined as `{τ : ConvexHistory F // τ.IsTotal}`
(`Semantics/ConvexHistory.lean:450`), and its own docstring states the split as policy: the
subtype "is used **only** where `H_F` appears as an object in its own right", the predicate form
everywhere totality is a hypothesis.

### §1.4 Claim 4 — "nothing formalizes the presheaf appendix" — **CONFIRMED as stated, REFUTED as an inference**

`grep -rin "presheaf" FormalSystem/ --include=*.lean` returns 0. The claim, read literally, is
true.

The *inference* the description draws from it — that the strongest argument for keeping the
convex layer is "prospective rather than actual" — does not survive contact with the appendix.
`app:Structure`'s analytic content is substantially present in the tree under non-categorical
names:

| `app:Structure` item | Present in the tree as | Status |
|---|---|---|
| `Tr p` (translation morphism of `Int(D)`) | `ConvexHistory.timeShift` (`Semantics/ConvexHistory.lean:330`) | present, domain-generic |
| `app:gluing` (two-piece gluing at a shared time) | `StarPasting.paste` (`Semantics/StarPasting.lean:109`) | present, **total-only** |
| *Totality* and *Directed Gluing* clauses' analytic input (`thm:extension`) | `Semantics/Extension/` | present, proved |
| *Possible Worlds* clause's `H_F` | `TaskFrame.HF` (`Semantics/ConvexHistory.lean:450`) | present |
| *Germs* clause (`Beh(F)(0) ≅ W`, via `lem:nullity`) | `FrameOver.nullity_identity`, used in `Extension.point` | present |
| *Determinism* clause | `Semantics/StarDeterminism.lean` (modal-formula treatment) | present in a different idiom |
| `def:task-topology`, `app:topology-t1`, `app:topology-r0` | — | absent |
| `def:interval-site`, `def:behavior-presheaf`, `def:twisted-arrow`, `lem:interval-twisted-arrow` | — | absent |
| `def:conduche`, `def:path-category`, `fact:conduche-equivalence` | — | absent |
| `cor:path-fibration` (the `D = ℤ` free-category clause) | `Metalogic/Decidability/BiLasso/` — see §5.2 | present as an effective/computational analogue |

A zero-hit grep for a *vocabulary* is evidence about naming, not about content. Using it to
license "the layer is prospective-only" inverts the actual finding: the layer's prospective
consumer is closer to hand than the description assumes, because most of its analytic input is
already proved. This is a first-order argument against COLLAPSE and is carried into §6.

### §1.5 The consumer hunt

The task names specific surfaces to hunt for a genuine convex, non-total, non-partial consumer.
Result: **none found.** Every surface below was searched with
`grep -rn "ConvexHistory\|IsTotal" <surface> --include=*.lean` and every hit read.

| Surface | `ConvexHistory` lines | Finding |
|---|---:|---|
| `Semantics/StarPasting.lean` | 22 | Every declaration taking a `ConvexHistory` also takes `IsTotal` — including `paste` itself, which is built by `ConvexHistory.ofTotal` and is therefore total. `AgreeFrom`/`AgreeUpTo` (`:120`, `:124`) are the only domain-free ones, and they are pointwise predicates that say nothing about domains. **No bounded consumer.** |
| `Semantics/ShiftSet.lean` | 13 | `hist` is `ofTotal` (`:206`); `total_eq_orbit` (`:232`) is totality-gated. `wh_ext` (`:140`), `ts_zero` (`:299`) and `ts_add` (`:306`) are domain-generic transport lemmas about `timeShift`. **No bounded consumer**, though these three are the closest thing in the tree to presheaf functoriality (see §5). |
| `Semantics/Ultraproduct/` | 0 | The subtree does not mention `ConvexHistory` at all. |
| `Metalogic/Decidability/BiLasso/` | 29 | Every semantic statement is totality-gated (`GoodCycle.lean:176`, `:465`, `:494`; `Check.lean:151`; `Annotation.lean:358`; `BoxOracle.lean:209`, `:219`, `:258`; `SmallModel.lean:120`, `:226`, `:230`; `Realized.lean:156`, `:184`; `Extraction.lean:355`). `TruthLemma.hist` (`:68`) is `A.lasso.toHF.val`, total by construction. Four declarations take an ungated `ConvexHistory` — `SmallModel.typeAt` (`:100`), `typeAt_subset` (`:109`), `typeAt_fulfillingSeq` (`:192`), and `BoxOracle.truth_neg_iff` (`:159`) — but all four are applied only at total arguments; see §2.4. **No bounded consumer.** |
| `Metalogic/WeakCanonical/` | 19 | `ReynoldsBridge.lean`'s two histories are `domain := fun _ => True`; `zHistoryV2_total_eq` (`:639`) and its `multiFam` twin (`:847`) take `(htot : ∀ t, σ.domain t)` — an inlined `IsTotal`. The remaining hits are totality-gated countermodel statements. **No bounded consumer.** |
| `Semantics/IntTransfer.lean` | 33 | This is the largest domain-generic surface in the tree, and it is the one place where a non-total domain is transported rather than assumed away. But it *transports*: no `IntTransfer` declaration constructs or consumes a specific bounded domain. **No bounded consumer.** |
| `FormalSystem/Boneyard/` | 1 (plus 2 construction sites) | The only `ConvexHistory` mention is an import in `ChainCompleteness/Bundle/SuccChainWorldHistory.lean`; both Boneyard constructions carry `domain := fun _ => True`. Three live tasks (497, 499, 501) name a Boneyard revival, but all three target `Boneyard/UltrafilterFrame/` — the algebraic-representation front — not either convex-history-bearing subtree. **No bounded consumer.** |

### §1.6 Verdicts

| Claim | Verdict |
|---|---|
| 1. The convex layer looks vestigial | **CONFIRMED**, and strengthened: the bounded convex tier is not merely unused but unreachable, since the tree's one partial→convex promotion (`toConvexHistory`) requires `IsTotal`. |
| 2. `convex` discharged 22×, consumed never | **CORRECTED**: discharged 18× at the `ConvexHistory` layer (16 live, 2 in `Boneyard/`); consumed at exactly 3 sites, all of which are convexity re-establishment inside the two generic transports. Stronger than claimed. |
| 3. The generality has a real price | **CONFIRMED**, with figures restated: `IsTotal` 305 lines / 326 occurrences / 58 files; `.domain` 228 lines / 295 occurrences; dependent `.states` applications 249 (not ~85); 12 bridge declarations in six matched pairs in `Validity.lean` alone. |
| 4. Nothing formalizes the presheaf appendix | **CONFIRMED as a fact, REFUTED as an inference**: `presheaf` occurs 0 times, but `timeShift`, `StarPasting.paste`, the Extension Theorem, `TaskFrame.HF` and the determinism material already supply most of `app:presheaf-dictionary`'s analytic input under non-categorical names. |

**Question (a) is therefore settled in the negative**: there is no site in the repository that
needs a convex, non-total, non-partial history. The evidence that would have changed the answer
does not exist. But §1.4 shows the correct conclusion is not the one the description anticipated
— the layer is unused *today* while its intended consumer is closer than assumed.
