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

---

## §2. What `TruthAt` means at a bounded index

**Question (b).** Machine-checked evidence:
`specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean`,
compiled sorry-free with

```
lake env lean specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean
```

The probe works on the permissive frame `natFrame` over `ℤ` (world states `ℕ`, task relation
`d ≠ 0 ∨ w = u`), the model `TaskModel.allTrue`, and one bounded index `bdd` whose domain is the
closed interval `[0, 0]`. `bdd_not_isTotal` proves it is genuinely bounded.

### §2.1 The clauses, as written

`TruthAt` (`Semantics/Truth.lean`) is five clauses. Read at an index `τ` and a time `t`:

| Clause | Text | Domain sensitivity |
|---|---|---|
| `atom p` | `∃ (ht : τ.domain t), M.valuation (τ.states t ht) p` | **the only** domain-sensitive clause |
| `bot` | `False` | none |
| `imp φ ψ` | `TruthAt M τ t φ → TruthAt M τ t ψ` | inherited |
| `box φ` | `∀ (σ : ConvexHistory F), σ.IsTotal → TruthAt M σ t φ` | **re-indexes to total histories** |
| `untl ψ φ` | `∃ s, t < s ∧ TruthAt M τ s φ ∧ ∀ r, t < r → r < s → TruthAt M τ r ψ` | none — quantifies over all of `D` |
| `snce ψ φ` | dual | none — quantifies over all of `D` |

The task description's summary of (b) is confirmed: the atom clause carries the domain
existential, the box clause re-indexes to `IsTotal` histories, and `untl`/`snce` quantify over
all of `D` with no domain guard.

### §2.2 The three findings

**(i) An atom outside the domain is false, not ill-formed** (`atom_false_outside_domain`). The
clause is a perfectly good `Prop`; it is simply refuted, because its leading existential asks for
a domain proof that does not exist. The same atom is true at `0`, inside the domain
(`atom_true_inside_domain`). So `TruthAt` is *total as a function* on bounded indices — nothing
is undefined — but the value it returns off the domain is "false", not "undefined" and not
"restricted away".

**(ii) The tense clauses see outside the domain** (`tense_sees_outside_domain`). At `(bdd, 0)`,
in the model where every atom is true at every world state, `F ¬p` is TRUE — witnessed at
`s = 1`, a time the index does not settle, where `¬p` holds *only because* the atom clause
failed for want of a domain proof. This is the sharpest available demonstration that the tense
operators do not respect the index's domain: they range over all of `D` and read "outside the
domain" as "the atom is false there".

`someFuture_top_true_at_bounded` records the corollary: `F⊤` — the semantic content of TM's
seriality axiom TS — is true at the bounded index at *every* time. The boundedness of the index
is invisible to the tense operators, which is exactly why the current bounded-index reading is
not the paper's footnoted alternative.

**(iii) The T-schema fails at a bounded index off the domain**
(`refute_modal_t_at_bounded_index`). `□p → p` is REFUTED at `(bdd, 1)`. The antecedent holds
because the box clause re-indexes to the total histories, where `p`'s domain obligation is
discharged for free (`box_atom_true`); the consequent fails because the atom clause is evaluated
at `bdd`, where it is not. The formula's modal part and its atomic part are evaluated against
**two different domains**, and the schema separates them.

`modal_t` is an axiom of TM (`ProofSystem/Axioms.lean`). So the bounded-index reading does not
merely give a weaker logic — it invalidates an axiom of the logic the repository proves sound.

**(iv) …and holds at the same index inside the domain** (`modal_t_holds_in_domain`). At `0`,
which is in `bdd`'s domain, the same instance holds. The degeneracy is therefore exactly
co-extensive with evaluating at `x ∉ dom τ`.

### §2.3 The plain answer: is the current bounded-index reading degenerate?

**Yes, and in a specific, locatable way.** It is degenerate off the domain and coherent on it.

The current clause set, read at a bounded index, is **none of the three candidate readings**:

- It is **not** `def:BL-semantics`. That definition evaluates only at possible worlds; at a total
  index the two agree (the atom clause's existential is vacuously satisfiable), which is the
  "Decision A, accepted gap" already recorded in `Truth.lean`'s own docstring.
- It is **not** the paper's line-1102 alternative. That alternative requires `x ∈ dom τ`,
  restricts `Past`/`Future` to `dom τ`, and quantifies `□` over the convex histories whose domain
  contains `x`. The current clauses do none of these three things: `x` is unrestricted, the
  tenses are unrestricted, and `□` still quantifies over `H_F`.
- It is a **third, unintended reading**: a hybrid in which the atom clause is domain-relative,
  the box clause is `H_F`-relative, the tense clauses are `D`-relative, and the evaluation time
  is unrestricted. Its incoherence is not a matter of taste; the T-schema refutation is a proof
  that the three relativisations do not cohere.

This is the correctness-grounds argument the task asked to have weighed
(question (b), final sentence). It is a genuine one, and it should be weighed as such: the
repository currently carries an evaluation index at which a theorem of its own proof system is
semantically false. Nothing is *unsound*, because every validity and consequence statement in the
tree carries the `IsTotal` guard (§1.5) and so never reaches the degenerate region. But the
guard is load-bearing at 305 lines across 58 files, and what it is guarding against is this.

### §2.4 Lemmas stated at an arbitrary index whose intended content is the total one

**97 declarations** in the live tree (excluding `Boneyard/`) explicitly bind a
`(τ : ConvexHistory F)` with no `IsTotal` anywhere in the declaration and no `.HF` in the
signature. Command:

```
python3 specs/553_decide_convex_history_layer_collapse/probes/scan-ungated-convex-binders.py
```

Distribution: `Semantics/` 50, `Metalogic/Decidability/Verified/` 17 (+3 in its `Bridge/`),
`Metalogic/` 9, `Decidability/BiLasso/` 5, `WeakCanonical/IntegerModel/` 4,
`Conservativity/` 3, `Algebraic/` 2, `Automation/` 2, `Independence/` 1, `BXCanonical/` 1.

Three classes, and only the third is a problem:

1. **Genuinely domain-generic transport and clause-unfolding lemmas.** `Truth.lean`'s
   `bot_false`, `imp_iff`, `some_future_iff`, `some_past_iff` etc.; `ShiftSet.wh_ext`,
   `ts_zero`, `ts_add`; `StarPasting.AgreeFrom` / `AgreeUpTo`. These say exactly what they
   should at any index. No action.
2. **Lemmas applied only at total arguments, correctly.** `BiLasso/SmallModel.typeAt`,
   `typeAt_subset`, `typeAt_fulfillingSeq`, `BoxOracle.truth_neg_iff`. Every call site supplies
   a total history (`GoodCycle.lean:477`, `:506` inside `exists_good_fwd_cycle`, which takes
   `hτ : τ.IsTotal`; `BoxOracle.lean:239`, `:254`). The extra generality is harmless and
   occasionally convenient.
3. **Lemmas whose *name* promises the total content and whose *statement* delivers the hybrid
   one.** The tense-characterization block in `Metalogic/Decidability/Verified/Decidable.lean`
   (`truthAt_of_allFuture`, `not_truthAt_of_someFuture`, `exists_gt_truthAt_of_untl`, …, 17
   declarations) and `Metalogic/DedekindNonCompactness.lean`'s `truthAt_qNext_iff`,
   `truthAt_qGap`, `truthAt_qBound` are stated at an arbitrary index. They are *true* as stated —
   they are consequences of the unrestricted tense clauses, which do not consult the domain — but
   what they assert at a bounded index is a fact about the hybrid reading, not about the paper's
   semantics. A reader who takes them as statements about possible worlds is reading in a
   hypothesis they do not carry.

Class 3 is not a soundness defect and it is not, on its own, an argument for collapsing the
layer. It is an argument that the generality is *unpaid-for*: 97 declarations carry an index
they never use, and at the one place where the difference is observable the semantics is
degenerate.

---

## §3. The candidate consequence relations, defined and separated

This section is the core of the User focus: the logic that results from letting consequence range
over convex histories, and the logic that results from additionally restricting the temporal
quantifiers to the domain of the convex world.

Machine-checked evidence:
`specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean`,
compiled sorry-free with

```
lake env lean specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean
```

Each of C2, C3 and C4 is an actual Lean definition in that probe, not only prose; C3's semantics
is a local recursion `TruthAtConvex` written beside the library's `TruthAt`, never a modification
of it.

### §3.1 The four relations, side by side

| | index | `□` ranges over | tenses range over | evaluation time `x` |
|---|---|---|---|---|
| **C1** (current / paper) | `τ` with `τ.IsTotal` | `{σ : σ.IsTotal}` = `H_F` | all of `D` | all of `D` |
| **C2** (convex index, unrestricted tense) | any `τ : ConvexHistory F` | `{σ : σ.IsTotal}` = `H_F` | all of `D` | all of `D` |
| **C3** (the paper's line-1102 alternative) | any `τ` with `x ∈ dom τ` | `{σ : x ∈ dom σ}` | `dom τ` | `dom τ` |
| **C4** (interval-indexed) | interval `τ` with `x ∈ dom τ` | `{σ : x ∈ dom σ}` | `dom τ` | `dom τ` |

C1 is the repository's `ConsequenceOnFrames` (`Semantics/Validity.lean:78`) and the paper's
`def:logical-consequence`. C2 is not a design: it is what the tree's own `TruthAt` already
computes when the `IsTotal` binder is dropped. C4 restricts C3's index to the closed bounded
interval domains `[a, b]` — the domain shape of `Beh(F)(ℓ)`'s sections, up to translation — via
the probe's `IsInterval` predicate.

**The four do not collapse.** C1 ≠ C2 (§3.4), C1 ≠ C3 (§3.2), C3 ≠ C4 in *definition* though the
containment `ValidC3 → ValidC4` is proved (`validC3_imp_validC4`) and no separating formula was
found — §7.4 records that as open. The plan's instruction was to reduce the count rather than
manufacture a distinction; the honest position is that C4 is C3's restriction to the presheaf's
own index class, which matters for §5's categorical reading even where the two validity sets may
coincide.

### §3.2 The separating pair: `F⊤`

- `valid_C1_someFuture_top` — `F⊤` is C1-valid. Its proof uses nothing about the index: C1's
  `untl` clause quantifies over all of `D`, so the witness `t + 1` is always available. The
  general statement over every frame is the library's `serial_future_axiom_valid`
  (`Metalogic/Soundness.lean:261`); the probe proves the one-frame instance so the separating
  pair is self-contained.
- `refute_C3_someFuture_top` — `F⊤` is **not** C3-valid, refuted at the right endpoint of the
  closed interval `[0, 0]`. C3's `untl` clause requires its witness to lie in `dom τ`, and there
  is no time strictly after the right endpoint in that domain.
- `refute_C3_somePast_top` — the past dual `P⊤` fails at the left endpoint, symmetrically.
- `refute_C4_someFuture_top` — the same refutation lands for C4, since `bdd` is an interval
  index (`bdd_isInterval`).

This is exactly what the paper's own commented-out sentence at line 1102 predicts, now
machine-checked rather than cited: "At the final move of a finished game there is no later time
in that history's domain, and so `F⊤` — the seriality axiom TS of the logic TM presented below —
and its past dual both fail, making `F⊥` satisfiable and the unboundedness of time contingent."

### §3.3 The structural observations, checked

**(1) C3's `□` does not depend on the index.** `truthC3_box_indep` proves
`TruthAtConvex M τ x (□φ) = TruthAtConvex M τ' x (□φ)` by `rfl`: the clause reads its
quantifier range off `x` alone. So C3 does not turn `□` into a relative modality; it keeps it
universal and changes its *range*, from `H_F` to the convex histories through `x`.

**(2) The range is strictly larger, and that is what breaks things.** For every world state `w`,
the point history `{⟨x, w⟩}` is a convex history (`pointHist`), is a legal C3 index at its own
point (`pointHist_domain_self`), is an *interval* history — a germ, `[x, x]`
(`pointHist_isInterval`) — and is not total (`pointHist_not_isTotal`). So C3's box quantifies
over indices that C1's does not, including maximally degenerate ones.

**(3) Consequently `□F⊤` is C3-UNSATISFIABLE** (`c3_box_someFuture_top_unsat`), at every model,
every convex index, and every time, over an arbitrary task frame. The proof is one line of
mathematics: the germ at `x` is always in the box's range, and no germ has a later time in its
own domain.

This is the answer to "what that does to formulas mixing `□` with tense", and it is much stronger
than the loss of TS. TM is closed under necessitation, so `⊢ F⊤` yields `⊢ □F⊤`. A semantics on
which `□F⊤` is unsatisfiable cannot be repaired by deleting the seriality axiom: the necessitation
rule itself would have to go, or the box's range would have to be cut back to exclude the germs.
**C3 is a genuinely different logic, not TM minus seriality.** The same argument refutes `□ψ` for
every `ψ` whose principal content is tense — every such `ψ` fails at germs, so its box is false
everywhere.

This is the most important single finding of §3, and it is the one the paper's footnote does not
state. The footnote observes that TS fails; it does not observe that necessitation and the germ
indices are jointly inconsistent with any tense theorem at all.

**(4) The S5 modal core nevertheless survives C3**, for an arbitrary task frame:
`c3_modal_t` (`□φ → φ`), `c3_modal_4` (`□φ → □□φ`), `c3_modal_b` (`φ → □◇φ`),
`c3_modal_5_collapse` (`◇□φ → □φ`). All four are proved from (1) plus the C3 side condition
`x ∈ dom τ`, which puts the index itself in the box's range. T needs exactly that side
condition — it is the one place where C3's insistence on `x ∈ dom τ` earns its keep, and it is
precisely the condition C2 omits (§3.4).

So the picture for C3 is sharp: **the modal half is intact and the temporal half is broken**, and
the breakage is not local to a couple of axioms.

### §3.4 C2, diagnostically

`valid_C1_modal_t` proves `□p → p` C1-valid; `refute_C2_modal_t` refutes it under C2, at the
bounded index at the out-of-domain time `1`. This is probe 01's finding restated in this
section's vocabulary, and it identifies the culprit precisely: C2 keeps C1's unrestricted
evaluation time while weakening the index, so the atom clause and the box clause are evaluated
against different domains (§2.2).

C2 is therefore an **artifact to be eliminated, not an alternative to be developed**. It is not a
design anyone chose; it is the reading the current clause set falls into when the `IsTotal` guard
is removed, and it invalidates an axiom of the logic the repository proves sound. The one thing
it is good for is the argument in §6: it is the concrete cost of carrying an evaluation index
that is more general than the semantics can actually interpret.

---

## §4. Axiom survival under C3

Machine-checked evidence:
`specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean`, compiled
sorry-free with

```
lake env lean specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean
```

**Constructor count, re-derived.** `FormalSystem/ProofSystem/Axioms.lean`'s `inductive Axiom`
has **45** constructors, by
`awk '/^inductive Axiom/,0' FormalSystem/ProofSystem/Axioms.lean | grep -c "^  | "` (58) minus
the 4 `FrameClass` constructors and the 9 `axiomFrameClass` match arms that the same pattern
picks up. The file's own module docstring states 45 and lists the nine layers; the two agree.

Legend: **P** = machine-checked in probe 03; **A** = audited by argument.

### §4.1 The table

| # | Constructor | Layer | Verdict | Evidence |
|---:|---|---|---|---|
| 1 | `prop_k` | Propositional | SURVIVES | **A** — `imp`/`bot` clauses unchanged; C3 truth at a fixed `(τ, x)` is a classical valuation of the propositional skeleton |
| 2 | `prop_s` | Propositional | SURVIVES | **A** — as above |
| 3 | `ex_falso` | Propositional | SURVIVES | **A** — as above |
| 4 | `peirce` | Propositional | SURVIVES | **A** — as above (classical) |
| 5 | `modal_t` | S5 | SURVIVES | **P** `c3_modal_t` |
| 6 | `modal_4` | S5 | SURVIVES | **P** `c3_modal_4` |
| 7 | `modal_b` | S5 | SURVIVES | **P** `c3_modal_b` |
| 8 | `modal_5_collapse` | S5 | SURVIVES | **P** `c3_modal_5_collapse` |
| 9 | `modal_k_dist` | S5 | SURVIVES | **P** `c3_modal_k_dist` |
| 10 | `serial_future` | BX temporal | **FAILS** | **P** `refute_C3_serial_future` — no later domain time at the right endpoint |
| 11 | `serial_past` | BX temporal | **FAILS** | **P** `refute_C3_serial_past` — dual, at the left endpoint |
| 12 | `left_mono_until_G` | BX temporal | SURVIVES | **A** — `G` restricted to `dom τ` still covers every `r` the `untl` guard consults, since those `r` are in `dom τ` by C3's own clause |
| 13 | `left_mono_since_H` | BX temporal | SURVIVES | **A** — dual |
| 14 | `right_mono_until` | BX temporal | SURVIVES | **A** — the witness `s` is in `dom τ`, so restricted `G` reaches it |
| 15 | `right_mono_since` | BX temporal | SURVIVES | **A** — dual |
| 16 | `connect_future` | BX temporal | SURVIVES | **P** `c3_connect_future` — uses the C3 side condition `x ∈ dom τ` |
| 17 | `connect_past` | BX temporal | SURVIVES | **P** `c3_connect_past` |
| 18 | `enrichment_until` | BX temporal | SURVIVES | **A** — the `S`-witness is `x` itself, available because `x ∈ dom τ`; the guard interval `(x, s) ∩ dom τ` is the same set on both sides |
| 19 | `enrichment_since` | BX temporal | SURVIVES | **A** — dual |
| 20 | `self_accum_until` | BX temporal | SURVIVES | **A** — same witness `s`; at any guard time `r`, `(r, s) ∩ dom τ ⊆ (x, s) ∩ dom τ` |
| 21 | `self_accum_since` | BX temporal | SURVIVES | **A** — dual |
| 22 | `absorb_until` | BX temporal | SURVIVES | **A** — order argument entirely inside `dom τ` |
| 23 | `absorb_since` | BX temporal | SURVIVES | **A** — dual |
| 24 | `linear_until` | BX temporal | SURVIVES | **A** — trichotomy on two witnesses, both in `dom τ`, which inherits `D`'s linear order |
| 25 | `linear_since` | BX temporal | SURVIVES | **A** — dual |
| 26 | `until_F` | BX temporal | SURVIVES | **P** `c3_until_F` |
| 27 | `since_P` | BX temporal | SURVIVES | **P** `c3_since_P` |
| 28 | `temp_linearity` | BX temporal | SURVIVES | **A** — trichotomy, as for `linear_until` |
| 29 | `temp_linearity_past` | BX temporal | SURVIVES | **A** — dual |
| 30 | `F_until_equiv` | BX temporal | SURVIVES | **P** `c3_F_until_equiv` (definitional) |
| 31 | `P_since_equiv` | BX temporal | SURVIVES | **P** `c3_P_since_equiv` (definitional) |
| 32 | `modal_future` | Interaction | SURVIVES | **P** `c3_modal_future`, via `truthC3_timeShift` and `c3_box_time_uniform` |
| 33 | `discrete_symm_fwd` | Uniformity | **FAILS** | **P** `refute_C3_discrete_symm_fwd` — forward gap at the left endpoint, no backward gap possible |
| 34 | `discrete_symm_bwd` | Uniformity | **FAILS** | **P** `refute_C3_discrete_symm_bwd` — dual, at the right endpoint |
| 35 | `discrete_propagate_fwd` | Uniformity | **FAILS** | **P** `refute_C3_discrete_propagate_fwd` — `G` now reaches the right endpoint, where the gap does not exist |
| 36 | `discrete_propagate_bwd` | Uniformity | CONDITIONAL | **A** — survives on `ℤ`-interval indices (`H` reaches only non-right-endpoint times, each of which keeps its successor gap); unresolved for an arbitrary convex domain over an arbitrary `D` |
| 37 | `discrete_box_necessity` | Uniformity | **FAILS** | **P** `refute_C3_discrete_box_necessity` — its consequent boxes a `U`-formula, hence is C3-unsatisfiable |
| 38 | `prior_UZ` | Prior (ZTime) | SURVIVES | **A** — `{s ∈ dom τ : s > x, φ}` is bounded below by `x`; well-ordering on a discrete order gives the least element |
| 39 | `prior_SZ` | Prior (ZTime) | SURVIVES | **A** — dual |
| 40 | `z1` | Z1 (ZTime) | CONDITIONAL | **A** — the backward induction runs inside `dom τ` and `G` is vacuous at the right endpoint, which is favourable; not verified |
| 41 | `density` | Density | SURVIVES | **A** — convexity of `dom τ` puts the interpolated time back in the domain, so the usual argument goes through unchanged |
| 42 | `dense_indicator` | Density | SURVIVES | **A** — at the right endpoint `U(⊤,⊥)` is false for want of any later domain time; elsewhere density + convexity interpolate |
| 43 | `prior_U_gap` | Reynolds (RTime) | UNRESOLVED | **A** — plausible on closed real intervals (which are order-complete), but `K⁺` is itself a restricted `U`-formula and its endpoint behaviour was not checked |
| 44 | `prior_S_gap` | Reynolds (RTime) | UNRESOLVED | **A** — dual |
| 45 | `sep` | Reynolds (RTime) | UNRESOLVED | **A** — same, compounded by `sep`'s nesting of `K⁺`/`K⁻` |

**Totals**: 36 SURVIVES (12 machine-checked), 6 FAILS (all 6 machine-checked), 2 CONDITIONAL,
3 UNRESOLVED (the RTime layer, whose analysis is real work and belongs to a follow-on task).

### §4.2 What logic C3 actually is

The failures are not scattered. Every one of them is an **existence assertion about the temporal
order**, and boundedness is exactly what makes existence assertions fail:

- `serial_future` / `serial_past` — assert a later / earlier time. Fail at the endpoints.
- `discrete_symm_fwd` / `_bwd` — assert that a gap on one side implies a gap on the other. Fail
  at the endpoints, where one side has no times at all.
- `discrete_propagate_fwd` — asserts the gap propagates forward. Fails because `G` now reaches
  the right endpoint.
- `discrete_box_necessity` — asserts a boxed gap. Fails for the germ reason (§3.3).

Nothing in the S5 layer fails, nothing in the propositional layer fails, and — the finding that
was genuinely unclear in advance — **the modal/temporal interaction axiom `modal_future`
survives**. It survives because C3 is *time-uniform*: `truthC3_timeShift` proves that C3 truth is
invariant under translating the index, which is the C3 analogue of the paper's
`app:auto_existence` (closure of `H_F` under translation). That lemma was the phase's one real
piece of work and it is what makes the verdict on row 32 a proof rather than a guess.

So: **C3 is TM's S5 modal layer over a bounded-interval tense logic.** Precisely,

> C3 ⊇ (classical propositional) + (S5 for `□`) + (the whole Burgess–Xu monotonicity,
> enrichment, accumulation, absorption and linearity block) + `modal_future`,
> and C3 ⊉ seriality and the uniformity layer.

Whether the remainder is a *known* system: it is close to Burgess–Xu on a linear order **without
the unboundedness assumption** — the logic of `U`/`S` over an arbitrary linear order, which is
the setting Burgess 1982 and Xu 1988 actually axiomatize before unboundedness is added. What is
*not* established here, and should not be claimed, is that C3 equals BX-without-seriality plus
S5: that is a completeness question, and it is out of scope. §7.3 proposes it as a task.

### §4.3 The germ constraint, which is the real obstacle

Two probe lemmas together give the governing structural constraint:

- `c3_nec` — C3 **is** closed under necessitation, semantically.
- `c3_valid_imp_germ_valid` — every C3-validity holds at every germ `{⟨x, w⟩}`.
- `c3_box_untl_unsat` / `c3_box_snce_unsat` — `□(φ U ψ)` and `□(φ S ψ)` are C3-**unsatisfiable**
  for every `φ`, `ψ`.

So the C3 logic must have every theorem germ-valid, and no boxed binary-tense formula can ever be
a theorem. This is more than the loss of TS: it constrains what any axiomatization of C3 could
look like. Row 37 (`discrete_box_necessity`) is the one place in TM's actual axiom set where this
bites directly, but it would bite any future axiom of the same shape.

A reader wanting to *develop* C3 rather than merely diagnose it has a design choice here that the
paper's footnote does not raise: whether to let `□` range over all convex histories through `x`
(as the footnote says, and as C3 does — germs included) or to cut the range back, e.g. to the
interval histories of some minimum length, or to those whose domain contains `dom τ`. The germ
result is the argument that the choice matters. §7.3 proposes it as a task.

### §4.4 C2, briefly

C2's status is diagnostic, not logical. §2 and §3.4 show it invalidates `modal_t` — an axiom that
survives even C3. C2 is therefore **strictly worse than both** C1 and C3: it is not a weakening
of TM in a principled direction, it is the accidental reading that results from removing a guard
without replacing it. It should be eliminated, not developed. That is a direct argument for
either retargeting the index to a total one (removing the possibility of C2 arising) or adding
C3's side condition (making the bounded case coherent) — and §6 costs both.
