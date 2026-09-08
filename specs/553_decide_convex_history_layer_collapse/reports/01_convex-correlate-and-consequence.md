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
second (domain-proof) argument: **133** sites over the live tree, by

```
grep -rnoE "\.states [a-zA-Z0-9_']+ [a-zA-Z0-9_']+" FormalSystem/ --include=*.lean | grep -v Boneyard | wc -l
```

(description: "roughly 85"). *A loose variant of the same grep, with `*` in place of `+`, returns
247 because it admits empty tokens; 133 is the correct figure and §6 uses it.* The divergence
from the description's 85 is real but modest, and §6.1 shows that only 64 of the 133 sit in files
that mention `ConvexHistory` at all — the rest are at the `PartialHistory` layer, which the
task's own constraint puts out of scope.

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
| 3. The generality has a real price | **CONFIRMED**, with figures restated: `IsTotal` 305 lines / 326 occurrences / 58 files; `.domain` 228 lines / 295 occurrences; dependent `.states` applications 133 (not ~85), of which only 64 are at the convex layer; 12 bridge declarations in six matched pairs in `Validity.lean` alone. |
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

---

## §5. The categorical correlate, both directions

Machine-checked evidence:
`specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean`, compiled
sorry-free with

```
lake env lean specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean
```

The paper's `app:Structure` runs from `def:task-topology` to `cor:path-fibration` and carries a
`% TODO: review in full` marker in the LaTeX source. **Anything proposed here tracks material the
author has not finished reviewing**, and any follow-on task should be flagged accordingly.

### §5.1 The dictionary: `app:Structure` → the tree

One row per named item of `app:Structure`, in the paper's order.

| Paper item | Repository correlate | Status |
|---|---|---|
| `def:task-topology` (basic opens `(w)_x`, `T_F`, closure, T1, R0) | — | **absent**. Nothing in `FormalSystem/` builds a topology on `WorldState`. The *Limit* frame field (`TaskFrame`'s `limit`) is the analytic input its T1 proof uses, and it is present. |
| `app:topology-t1` | — | **absent** (its input `lem:nullity` = `F.nullity_identity` and `limit` are present) |
| `app:topology-r0` | — | **absent** (immediate from T1) |
| `app:gluing` (two-piece gluing at a shared time, arbitrary convex domains) | `StarPasting.paste` (`Semantics/StarPasting.lean:109`) and its seam argument `paste_rel_le_lt` (`:83`) | **present, total-only**. `paste` glues two TOTAL histories at a time; `app:gluing` glues two arbitrary convex histories on a nonempty overlap. The mathematics is the same *Compositionality* step. Probe 04's `glue_seam` re-derives it at the interval site to measure the gap. |
| `def:interval-site`: *Duration Monoid* `BD⁺` | — | **absent** |
| `def:interval-site`: *Interval* `[p, q]` | probe 04's `Beh`'s domain predicate; nothing in the library | **absent** as a named notion |
| `def:interval-site`: *Interval Category* `Int(D)`, translations `Tr p` | `ConvexHistory.timeShift` (`Semantics/ConvexHistory.lean:330`) is the ACTION of `Tr p` on histories; `ShiftSet.ts_zero` (`:299`) and `ts_add` (`:306`) are its functoriality laws | **present in action, absent as a category**. `ts_zero`/`ts_add` are literally `Tr 0 = id` and `Tr p ∘ Tr p' = Tr (p+p')`, proved, on arbitrary convex histories. |
| `def:interval-site`: *Presheaf*, *Johnstone Coverage*, *Sheaf* | — | **absent** |
| `def:behavior-presheaf`: `Beh(F)(ℓ)` and its restrictions | probe 04's `Beh` + `restrict` + `restrict_id` + `restrict_comp` | **absent from the library; established in this task's probe.** |
| `def:behavior-presheaf`: *Reflection* `τ^r`, *Converse Frame* `F⁻`, *Reflection Automorphism* | the converse convention is a frame field (`FrameOver.converse`); the past/future duality metarule TD is `Metalogic/`'s `thm:TD-valid` correlate | **present as a duality, absent as a natural isomorphism** |
| `def:twisted-arrow`, `lem:interval-twisted-arrow` | — | **absent** |
| `app:presheaf-dictionary`: *Germs* `Beh(F)(0) ≅ W` | probe 04's `germ` / `ofGerm` / `germ_ofGerm` / `ofGerm_germ` | **absent from the library; PROVED in this task's probe**, using `F.nullity_identity` exactly as the paper's proof does |
| `app:presheaf-dictionary`: *Sheaf* | `glue_seam` (probe 04) is its composition step; the assembly is not done | **composition step proved; clause open** |
| `app:presheaf-dictionary`: *Directed Gluing* | `Semantics/Extension/` (`thm:extension`) is the analytic input the paper's proof cites, and it is fully proved | **input present, clause absent** |
| `app:presheaf-dictionary`: *Totality* (restrictions are surjective) | same — the paper's proof is "extend by `thm:extension`, restrict" | **input present, clause absent** |
| `app:presheaf-dictionary`: *Possible Worlds* `H_F ≅ lim Beh(F)(2x)` | `TaskFrame.HF` (`Semantics/ConvexHistory.lean:450`); over `ℤ`, `FrameOver.mem_HF_iff_adjacent` (`Semantics/IntNormalForm.lean:337`) identifies `H_F` with the bi-infinite step paths | **`H_F` present; the limit presentation absent** |
| `app:presheaf-dictionary`: *Determinism* (⟺ injectivity of every restriction) | `Semantics/StarDeterminism.lean` — `states_eq_of_deterministic` (the singleton bridge), `stab_iff_of_deterministic`, `determined_of_deterministic` | **present in a different idiom.** `states_eq_of_deterministic` — "two total histories agreeing at one time agree everywhere" — is *exactly* injectivity of restriction, stated for total histories instead of sections. |
| `app:presheaf-dictionary`: *Reflection* (natural isomorphism) | — | **absent** |
| `def:conduche`, `fact:conduche-equivalence` | — | **absent** |
| `def:path-category` `Path(F)` | — | **absent** as a category |
| `cor:path-fibration`, `D = ℤ` clause (sections = paths; `Path(F)` free) | `FrameOver.mem_HF_iff_adjacent`; the whole of `Metalogic/Decidability/BiLasso/` | **present as an effective analogue**, see §5.2.2 |

**The headline of the dictionary.** Of the appendix's seven `app:presheaf-dictionary` clauses,
two (*Germs*, and the composition step of *Sheaf*) are now machine-checked in this task's probe;
two more (*Directed Gluing*, *Totality*) have their entire analytic input already proved in the
tree as `thm:extension`; one (*Determinism*) exists in a different idiom; and two (*Possible
Worlds*, *Reflection*) have their objects present but not their categorical presentation. The
site itself — `Int(D)`, `BD⁺`, the twisted-arrow category, the Johnstone coverage — is genuinely
absent, but it is also the cheapest part: `ts_zero` and `ts_add` are already the functoriality
laws, proved.

This directly corrects §1.4's inference. A `presheaf`-grep of 0 is a fact about *naming*.

### §5.2 The other direction: what this repository teaches about the categorical structure

The User focus asks for this half explicitly, and the paper does not supply it. Three
connections, each with what is established and what is conjectural stated separately.

#### §5.2.1 Determinism ⟺ injectivity, and a modal-formula characterization of separatedness

**Established (paper side).** `app:presheaf-dictionary`'s *Determinism* clause: `F` is
`Deterministic` iff every restriction map of `Beh(F)` is injective.

**Established (repository side).** `Semantics/StarDeterminism.lean`'s
`states_eq_of_deterministic` is the singleton bridge: two total histories of a deterministic
frame that agree on their world state at one time agree at *every* time. Read presheaf-side, that
is precisely "restriction to a germ is injective on the sections through it". The module also
proves `determined_of_deterministic` — the object-language schema *Determined* (`φ → ⊡φ`, with
`⊡` the stability modal) is frame-valid on every deterministic frame — and it records, with
citations, that the converse fails: the drift frame `F°` validates *Determined* without being
deterministic (`Metalogic/Independence/`).

**The connection, and it is new.** Composing the two gives a *modal-formula* statement about a
*categorical* property: on frames where the object-language schema *Determined* is valid, the
behavior presheaf is separated. And the repository's own independence result says the converse
fails, so:

> **`Beh(F)` separated is strictly stronger than the validity of *Determined* on `F`.** The
> object language can express a sufficient condition for the presheaf's separatedness but not a
> necessary and sufficient one, and the repository already carries the countermodel that
> establishes the gap.

That is a fact about the *category theory* that came out of the proof theory, not the other way
round, and it is exactly the kind of thing the User focus asks for. **Conjectural**: whether some
*other* formula of `BL⋆` characterizes separatedness exactly. `StarDeterminism.lean`'s own
"choice-dependence tracks a direction" note is the relevant obstruction: the genuine converse of
the bridge needs `thm:extension` and hence Zorn, which suggests separatedness is not
first-order-in-the-object-language definable. **A follow-on task would have to prove or refute
that**; nothing here settles it.

#### §5.2.2 BiLasso as the effective content of `cor:path-fibration`

**Established (paper side).** `cor:path-fibration`: when `D = ℤ`, the sections of `Beh(F)` over
`ℓ` are the paths of length `ℓ` in the graph `⟨W, ⇒₁⟩`, gluing is concatenation, and `Path(F)` is
the free category on that graph. The paper's line-1773 footnote adds the effective half: when `W`
is finite, every bounded convex history extends to a possible world that is *eventually periodic
in both directions* — a finite prefix plus a finite cycle each way — "licensing a finite
certificate that a given bounded history is a fragment of a possible world".

**Established (repository side).** `FrameOver.mem_HF_iff_adjacent`
(`Semantics/IntNormalForm.lean:337`) proves `H_F` over `ℤ` is exactly the bi-infinite step paths
— the `H_F` half of the correspondence, machine-checked. `Metalogic/Decidability/BiLasso/Basic.lean`
defines a `BiLasso` as three lists `back`/`mid`/`fwd` decoded to a bi-infinite path: a finite
cycle backward, a finite window, a finite cycle forward. `BiLasso/Agreement.lean`'s
`extends_of_agrees` (`:112`) proves that a placed bi-lasso agreeing with a bounded partial history
on that history's own domain **extends** it in the paper's sense.

**The connection.** `extends_of_agrees` **is** the paper's line-1773 footnote, formalized: the
bi-lasso is the finite certificate, and the theorem is that the certificate is sound. The paper
states the fact and cites Lind and Marcus; the repository proves it and ships a decision
procedure over it.

**What that teaches about the categorical statement.** `cor:path-fibration` says `Path(F)` is the
free category on `⟨W, ⇒₁⟩`, whose morphisms are the finite paths. `H_F` is the limit of the
sections (the *Possible Worlds* clause). The BiLasso layer says something the categorical
statement does not: over a *finite* `W`, the limit is computed by *finitely presentable* elements
— every point of `lim Beh(F)(2x)` is reachable as a bi-lasso, and membership of a section in the
image of the limit projection is decidable. In shift-of-finite-type language (which the paper's
line 1770 uses): `H_F` is a shift of finite type, and its points of interest are the eventually
periodic ones.

**Where it breaks, stated honestly.** The correspondence is about *paths*, not about *truth*.
`BiLasso/Annotation.lean` records a machine-checked refutation: formula truth along a bi-lasso is
**not** a function of the state at a time and is **not** periodic in the time, even though the
state sequence is — the witness family is `prevⁿ p`, whose truth set along a fixed short lasso is
`[n, ∞)`. So the free-category presentation of `Path(F)` gives the *syntax* of the model for free
and gives *nothing* about the semantics of the tense language over it; that is why the BiLasso
layer needs annotations at all, and why `Assembly.lean`'s finite-model hypothesis `fmp` is still
open. **This is the sharpest thing this repository has to say back to `cor:path-fibration`**: the
categorical presentation is a statement about the underlying graph, and the logic does not
factor through it.

#### §5.2.3 A restriction-invariance fragment (conjecture, with the two easy directions settled)

**The conjecture.** Under C4 — evaluation at interval sections — truth at a point of a section
is preserved under restriction to smaller subintervals containing that point, for some syntactic
fragment of `BL` and not for others.

**Settled here, in the negative direction.** Probe 03's germ theorems already decide the two
extremes, and they decide them more sharply than the conjecture anticipated:

- **Atoms are restriction-invariant.** The atom clause reads `τ.states t ht`, and restriction
  does not change the value at a retained time. Immediate.
- **`□` is restriction-invariant** — indeed *index-independent* (`truthC3_box_indep`, probe 02).
  So it is trivially invariant, but for a reason stronger than locality: it does not consult the
  index at all.
- **`F` and `P` are NOT even co-monotone in the way the conjecture guessed.** The conjecture said
  they should be "co-monotone" (preserved under *enlarging* the domain). That is right for `F`/`P`
  read existentially — a witness in a subinterval survives in a superinterval — but probe 03's
  `germ_untl_false` shows the failure is total in the other direction: restricting to the germ
  makes *every* binary tense formula false, so no `U`/`S` formula whatever is
  restriction-invariant downward.
- **`G` and `H` are anti-monotone**, dually: they are vacuously true at the germ and can only
  lose truth as the domain grows.

**So the fragment is exactly the `□`-and-atoms fragment plus Boolean combinations**, i.e. the
tense-free fragment. That is a *complete* answer to the conjecture rather than a partial one, and
it is a negative one: there is no interesting locality result to be had at C4, because the germ
is a legal restriction and it kills the entire tense language.

**What that teaches about the sheaf.** The interesting reformulation is not "which formulas are
local" but **"which formulas are germ-determined"** — determined by the section's germs alone.
Atoms and `□` are; nothing else is. Read sheaf-theoretically, `BL`'s tense fragment is precisely
the part of the language that is *not* a section of a sheaf of truth values over the interval
site, and the failure is detected at the coverage's germ objects. That is a clean statement, it is
the paper's own *Sheaf* clause read backwards through the logic, and it is a genuine contribution
from this side to that one. **It is stated here as a formulation, not proved as a theorem**;
§7.3 proposes it.

---

## §6. Costing the structural options

Every figure below is followed by the command that produced it. Nothing is carried over from the
task description without re-measurement; §1.3 and §6.1 record two places where re-measurement
changed the number.

### §6.1 The retarget, by obligation class

The change costed here is: replace the evaluation index of `TruthAt` (and hence of `Valid`,
`ValidIn`, `ValidOnFrames`, `ConsequenceOnFrames`, `SetConsequenceOnFrames`, `TaskFrame.ValidOn`
and the satisfiability definitions) by a total-by-construction type — the paper's `PossibleWorld`
— leaving `PartialHistory` and the Extension Theorem untouched, as the task's constraints
require.

**Class (i): mechanical rewrites.**

| Item | Measure | Command |
|---|---:|---|
| `IsTotal` occurrences in *code* (not docstrings) | 239 lines across 55 files | `python3 specs/553_decide_convex_history_layer_collapse/probes/scan-istotal-code-vs-doc.py` |
| `IsTotal` occurrences in docstrings/comments | 66 lines | same script |
| dependent `.states t ht` applications, whole tree | 133 | `grep -rnoE "\.states [A-Za-z0-9_']+ [A-Za-z0-9_']+" FormalSystem/ --include=*.lean \| grep -v Boneyard \| wc -l` |
| …of which are in files that mention `ConvexHistory` | **64** | same script |
| …of which are in `PartialHistory`-only files (OUT OF SCOPE) | 69 | same script |
| `.domain` occurrences | 228 lines, 35 files | `grep -rn "\.domain" … \| wc -l`; `grep -rl … \| wc -l` |
| `convex :=` discharges at the convex layer, live | 16 | §1.1's classification |
| bridge declarations to delete | 12, in `Semantics/Validity.lean` | §1.3's table |
| **bridge CALL SITES to rewrite** | **~280** (`of_forall_total` 201, `apply_total` 78, `Valid.apply` 7, `SemanticConsequence.of_forall` 8, `.apply` 1, `validOn_iff_total` 3), across **26 files** | `grep -rn "<name>" FormalSystem/ --include=*.lean \| grep -v Boneyard \| wc -l` per name; file span by `grep -rln` on the disjunction |
| files touching `IsTotal` ∪ `.domain` ∪ `.states` | 75 | `grep -rl "IsTotal\|\.domain\|\.states" … \| grep -v Boneyard \| wc -l` |
| live tree size, for scale | 283,541 lines | `find FormalSystem -name '*.lean' -not -path '*/Boneyard/*' \| xargs wc -l \| tail -1` |

**Two corrections to the description's cost picture, both material.**

1. The description's "roughly 85 dependent `.states t ht` applications" is 133 by a strict grep
   (the loose variant that returns 247 admits empty tokens and should not be used). But **only 64
   of the 133 are at the convex layer at all** — the other 69 are in `Extension/Constraint.lean`
   (33), `Extension/PeriodicExtension.lean` (13), `FrameAxioms.lean` (11),
   `PartialHistoryOrder.lean` (4), `Extension/Admissible.lean` (4) and friends, which are
   `PartialHistory`-layer files the task's constraints put out of scope. The mechanical
   `.states` cost of the retarget is therefore **less than half** what the raw grep suggests.

2. Conversely, the description does not count the **bridge call sites**, and they dominate.
   `of_forall_total` alone is applied 201 times. Deleting the 12 bridge declarations means
   rewriting roughly 280 call sites across 26 files. That is the single largest mechanical item
   in the change and the description's costing omits it entirely.

**Class (ii): proofs that must genuinely be rethought.** Short list, and it is short:

- **The `Extension/` interface.** `thm:extension` concludes at the partial layer and produces a
  totality proof; `PartialHistory.toConvexHistory` promotes across it. Under a total index that
  promotion becomes `PartialHistory → PossibleWorld` with the totality proof as its input — the
  same theorem with a different target type. `Extension.lean:213` is the one call site. **One
  interface, mechanical, but it must be got right because it is the only route into the index
  type.**
- **`Semantics/IntTransfer.lean`.** This is the tree's only genuinely domain-generic transport,
  and `Truth.lean:593-597` records that its `alignedCorr` "states its relation on arbitrary
  `ConvexHistory`s, which is what lets `TimeShift.timeShift_preserves_truth` and
  `IntTransfer.truthAt_map` keep their" generality. Retargeting the index makes those statements
  total-only. Whether the ℤ-transfer machinery (`validZTime_iff_validInt`, consumed by
  `DurationClassification.lean` and the decidability branch) still goes through at the narrower
  type is **the one real question in the whole change**, and it is not answerable by grep.
- **`ConvexHistory.timeShift` and its convexity re-establishment** (`ConvexHistory.lean:336-343`)
  become unnecessary — a total index's shift is total by `isTotal_timeShift` and there is no
  domain to reshape. This is a *simplification*, not a rethink.

Everything else in the 55 code files is binder deletion and proof-term forwarding.

**Net lines.** The description expected the change to remove code. That is **confirmed but
smaller than implied**: deleting the 12 bridge declarations with their docstrings removes on the
order of 120–160 lines from `Validity.lean` (which is 950 lines); deleting the 16 live `convex :=`
discharges removes 16; dropping 239 in-code `IsTotal` occurrences mostly shortens existing lines
rather than deleting them; the 64 domain-proof arguments likewise. Against that, a
`structure PossibleWorld` with its API costs perhaps 40–80 lines. **Estimated net: −150 to −250
lines out of 283,541**, i.e. under 0.1% of the tree. The description's expectation that "volume
rather than depth is the likely difficulty" is **confirmed**: roughly 600 individual touch points
in 55–75 files, almost none of them hard, and one genuinely open question (`IntTransfer`).

### §6.2 The four options, costed on the same basis

| Option | Cost | What it forecloses |
|---|---|---|
| **COLLAPSE** — retarget the semantics to a total index and delete `ConvexHistory` | The §6.1 change, **plus** deleting `ConvexHistory` itself and rehoming `timeShift` (used by `BiLasso/BoxOracle.lean:252`, `ShiftSet`, `ReynoldsBridge`) and `IntTransfer` onto the new type or onto `PartialHistory`. Adds perhaps 20% to §6.1's touch count. | **The presheaf appendix outright.** `Beh(F)(ℓ)`'s sections are convex histories with bounded domain; with no convex layer there is no type for them. Probe 04 would not typecheck. Also forecloses C3/C4 as anything but a from-scratch redefinition. |
| **KEEP** — change nothing, record the reason in the module docstring | ~10 lines of docstring, once. | Nothing structurally. But it keeps C2 reachable: 97 declarations continue to bind an index at which `modal_t` is false (§2, §3.4), and the 305-line `IsTotal` tax continues to be paid at every validity, soundness, completeness and decidability site. |
| **COLLAPSE-PARTIALLY** — retarget the semantics; retain `ConvexHistory` as an unused definition | Exactly §6.1, no more: `ConvexHistory` stays as a type, `timeShift`/`IntTransfer` stay on it, and the semantics moves off it. ~600 touch points, −150 to −250 lines. | Nothing that matters. `Beh(F)` still has a home. C3/C4 can still be defined on it. |
| **DEVELOP-AND-RETARGET** — §6.1, and *also* grow the convex layer into the interval-site/presheaf apparatus and add C3/C4 as named definitions | §6.1 **plus** new work, all of it additive and none of it blocking: the site + presheaf + Germs is ~150 lines (probe 04 is 200 including docstrings and it proves functoriality and Germs already); the *Sheaf* clause is ~120 more on top of `glue_seam`; *Totality* and *Directed Gluing* are wrappers on `thm:extension`; C3/C4 as library definitions with the §4 survival theorems is ~400 lines (probe 03 is ~460 including docstrings). | Nothing. It is the union of COLLAPSE-PARTIALLY's foreclosures (none) with strictly more capability. |

**The counterfactual — the cost of not deciding.** Measured, not asserted:

- 239 in-code `IsTotal` occurrences across 55 files, each one a binder that must be written,
  threaded and discharged at every new validity/soundness/completeness statement. The heaviest
  file is `Semantics/Validity.lean` at 35.
- ~280 bridge applications across 26 files, each existing only to convert between two spellings
  of one notion.
- 97 declarations binding an index whose semantics is degenerate (§2.4, class 3), a number that
  grows monotonically with the tree.
- The `presheaf`-grep-0 misreading of §1.4, which nearly produced the wrong verdict, is itself a
  cost of the layer's namelessness: the apparatus is there but nothing points at it.

The status quo is not free, and its cost is proportional to future work rather than fixed.

### §6.3 The constraint any COLLAPSE-shaped plan must meet

Recorded here so §7.3's proposals inherit it:

- Each phase is one agent run — on §6.1's numbers, that is roughly "one module cluster per
  phase", not "one obligation class per phase": the 26 bridge-call-site files alone are two or
  three phases.
- `lake build FormalSystem` green with no new `sorry` at the end of **every** phase. This is the
  binding constraint on phase decomposition, and it rules out the obvious slicing (change the
  index type first, fix call sites after): the type change is not green until its call sites
  are. A compatibility `abbrev` plus a deprecation sweep is the shape that satisfies it.
- `PartialHistory` and the Extension Theorem untouched. §6.1 shows this is compatible with the
  change and in fact removes 69 of the 133 `.states` sites from scope.

---

## §7. Verdict, proposed description revision, and follow-on tasks

### §7.1 The verdict: DEVELOP-AND-RETARGET

Exactly one option, with its reasoning.

> **Retarget the primary semantics to a total-by-construction index — the paper's
> `PossibleWorld` — while simultaneously growing the convex layer into the interval-site /
> behavior-presheaf apparatus and adding the alternative consequence relations C3 and C4 as
> explicitly named second definitions.**

The reasoning, in the order the evidence forces it:

**1. The bounded convex index is not merely unused; the semantics at it is incoherent.** §1.1
shows the tier is unreachable (the tree's one partial→convex promotion requires `IsTotal`) and
that no concrete bounded convex history exists anywhere. §2 shows *why that is fortunate*: at a
bounded index off the domain, `modal_t` — an axiom of TM — is **false**
(`refute_modal_t_at_bounded_index`), because the atom clause is domain-relative while the box
clause re-indexes to `H_F`. The repository is not unsound, because the `IsTotal` guard is present
at every validity and consequence site; but the guard is load-bearing at 239 in-code occurrences
across 55 files, and what it guards against is a semantics nobody designed. **This is a
correctness argument, not a tidiness argument**, and it is the decisive one for retargeting.

**2. Retargeting costs about 600 mechanical touch points and removes code.** §6.1: ~600 edits
across 55–75 files, net −150 to −250 lines out of 283,541, with exactly one genuinely open
question (whether `IntTransfer`'s domain-generic transports survive a narrower index). The
description's expectation — volume rather than depth — is confirmed, with two corrections: the
`.states` cost is less than half what the raw grep suggests (64 of 133 are at the convex layer),
and the ~280 bridge call sites, which the description omits, dominate.

**3. But COLLAPSE is wrong, and §1.4's inference was the near-miss.** A `presheaf` grep of 0 is a
fact about naming. §5.1 shows that `timeShift` + `ts_zero` + `ts_add` *are* `Tr p` and its
functoriality laws, `StarPasting.paste_rel_le_lt` *is* `app:gluing`'s composition step,
`thm:extension` *is* the whole analytic input to the *Totality* and *Directed Gluing* clauses, and
`StarDeterminism.states_eq_of_deterministic` *is* injectivity of restriction. Probe 04 proves
presheaf functoriality and the *Germs* clause in ~200 lines against the live tree. Deleting
`ConvexHistory` would delete the type in which `Beh(F)(ℓ)`'s sections live, and probe 04 would
stop typechecking. **The layer's intended consumer is much closer to hand than the description
assumed.**

**4. And KEEP is wrong for the same reason in reverse.** Keeping the layer *as the evaluation
index* keeps C2 reachable and keeps the tax growing: 97 declarations already bind an index at
which the semantics is degenerate, and the number grows monotonically with the tree.

**5. What separates DEVELOP-AND-RETARGET from COLLAPSE-PARTIALLY is that the study found real
work for the layer to do, not merely a reason to preserve the option.** §3 and §4 give C3 a
determinate character: its S5 core is intact, `modal_future` survives (via the newly-proved
`truthC3_timeShift`), and every failure is an existence assertion about the temporal order — but
`□(φ U ψ)` is outright unsatisfiable, so C3 is a genuinely different logic rather than TM minus
seriality. §5.2 turns up three connections that run *from* this repository *to* the category
theory, including one — separatedness of `Beh(F)` is strictly stronger than the validity of
*Determined*, witnessed by the repository's own drift-frame countermodel — that is a new fact
about the categorical structure. A layer with that much determinate content ahead of it is being
developed, not preserved.

**The two moves are independent and must be phased separately.** Retargeting the semantics does
not touch `Beh(F)`; growing `Beh(F)` does not touch the semantics. That independence is what
makes the combination coherent rather than contradictory, and it is what lets each phase leave
`lake build FormalSystem` green.

**What would have changed the verdict.** A single genuine consumer of a convex, non-total,
non-partial history would have forced KEEP. §1.5 hunted every surface the task named and found
none. If one is found later, the retarget half of this verdict is void and the develop half is
unaffected.

### §7.2 Proposed revised description for task 553

**This is a proposal. `specs/state.json` was NOT edited by this task**, nor were `specs/TODO.md`
or `specs/ROADMAP.md` — the plan's Non-Goals forbid it. Paste-ready:

```
ANALYSIS SURFACE (read-only; NOT a write scope): FormalSystem/Semantics/{ConvexHistory,PartialHistory,Truth,Validity,StarPasting,ShiftSet,IntTransfer,StarDeterminism}.lean, FormalSystem/Semantics/Extension, FormalSystem/Metalogic/Decidability/BiLasso, FormalSystem/Metalogic/WeakCanonical, FormalSystem/Metalogic/Soundness.lean, FormalSystem/ProofSystem/Axioms.lean. These are a READING surface. This task declares no file_scope: the batch orchestrator treats file_scope as write ownership, and over-declaring a reading surface would collide with any concurrent task editing those trees. Every other research-only task in this repository declares no file_scope; this one matches.

RESEARCH TASK --- report and probe files only; no change to FormalSystem/ beyond probes under this task's directory.

THE AIM, as reframed. Develop the categorical correlate of convex histories rather than suppress it, in both directions: draw on the paper's app:Structure (the task topology, the interval site Int(D), the behavior presheaf Beh(F), the twisted-arrow and path categories) for insight into the logic, AND draw on this repository's proof theory, semantics and decidability results for insight into that categorical structure. Alongside that, study the alternative consequence relations the paper floats: one ranging over convex histories, and one additionally restricting the temporal quantifiers to the domain of the convex world. What is wanted are the most natural definitions and the best insights about them.

PAPER ANCHORS. app:Structure (def:task-topology, app:topology-t1, app:topology-r0, app:gluing, def:interval-site, def:behavior-presheaf, def:twisted-arrow, lem:interval-twisted-arrow, app:presheaf-dictionary with its seven clauses Germs/Sheaf/Directed Gluing/Totality/Possible Worlds/Determinism/Reflection, def:conduche, def:path-category, fact:conduche-equivalence, cor:path-fibration). NOTE: app:Structure carries a "% TODO: review in full" marker in the LaTeX source, so anything proposed against it tracks material the author has not finished reviewing. The alternative semantics is the footnote at possible_worlds.tex line 1102; its own commented-out sentence predicts that F-top and its past dual fail, making F-bot satisfiable.

WHAT THIS TASK MUST SETTLE.
(a) Is the convex layer vestigial, and is the finding complete? Hunt for any site needing a convex, non-total, non-partial history.
(b) What does TruthAt MEAN at a bounded index? Establish it with machine-checked probes and say plainly whether the reading is degenerate.
(c) Cost the retarget honestly, by file and by obligation class, separating mechanical rewrites from proofs that must be rethought, against the counterfactual of doing nothing.
(d) Weigh what each option forecloses --- including the presheaf appendix and the alternative semantics.
(e) Recommend exactly one of: COLLAPSE; KEEP (with the reason recorded once in the ConvexHistory module docstring); COLLAPSE-PARTIALLY (retain ConvexHistory as a definition, retarget the semantics); or DEVELOP-AND-RETARGET (retarget the semantics AND grow the convex layer into the presheaf apparatus, adding the alternative consequence relations as named second definitions). State the reasoning well enough that a follow-up task can execute without re-deriving it.

CONSTRAINTS. Do not begin the refactor here; probe files under this task's directory are fine, edits to the live tree are not. Any plan proposed must leave PartialHistory and the Extension Theorem untouched --- the Extension Theorem's conclusion is stated at the partial layer and is unaffected either way. lake build FormalSystem must be green with no new sorry at the end of every phase of any plan proposed here.
```

### §7.3 Follow-on task specifications

**Task creation was not performed.** This dispatch runs in orchestrator mode, and the plan's
Non-Goals forbid editing `specs/state.json`; creating tasks requires exactly that. The
specifications below are the deliverable.

The planning-time candidate list has been pruned and re-ordered against what the study actually
established. Two of the seven candidates are dropped or merged; three are new.

| # | Title | Type | Size | Depends on |
|---:|---|---|---|---|
| A | Formalize the interval site `Int(D)` and the behavior presheaf `Beh(F)` | lean4 | M (2–3 phases) | — |
| B | The *Sheaf* clause: two-piece gluing at the interval site | lean4 | M (2 phases) | A |
| C | *Totality* and *Directed Gluing* from `thm:extension` | lean4 | S (1–2 phases) | A |
| D | `H_F ≅ lim Beh(F)(2x)` — the *Possible Worlds* clause | lean4 | M | A, C |
| E | *Determinism* ⟺ injectivity of restriction, joined to the repository's modal treatment | lean4 | M | A |
| F | C3/C4 as named library definitions, with the §4 survival theorems | lean4 | L (4–5 phases) | — |
| G | Retarget the semantics to a total-by-construction `PossibleWorld` index | lean4 | L (5–7 phases) | — |
| H | Is the C3 logic complete for BX-without-seriality plus S5? | formal/logic | L | F |

**A — Formalize `Int(D)` and `Beh(F)`.** Promote probe 04 into the library. Deliver: the section
type (`Beh F l`, the convex histories with domain exactly `[0, l]`), restriction along `Tr p`,
presheaf functoriality (`restrict_id`, `restrict_comp`), and the *Germs* clause
`Beh(F)(0) ≅ W`. All four are already proved in
`specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean`; the work is
finding the right home (a new `Semantics/Presheaf/` cluster, below `Truth.lean` in the layering so
that `assert_not_exists` on the proof system still holds), naming, and docstrings against
`def:interval-site` and `def:behavior-presheaf`. Optionally add `BD⁺` and the twisted-arrow
category with `lem:interval-twisted-arrow`; that lemma is pure order algebra and needs no frame.
*Flag in the module docstring that `app:Structure` carries a `% TODO: review in full` marker.*

**B — The *Sheaf* clause.** `app:gluing` for two interval sections whose germs agree at the seam,
plus the two restriction identities and uniqueness. The composition step is already proved as
probe 04's `glue_seam`; the remainder is assembling the glued section by cases and applying
`ShiftSet.wh_ext`. **Generalize `StarPasting.paste` off its totality hypothesis as part of this**
— `paste_rel_le_lt` is the same argument and should not exist twice.

**C — *Totality* and *Directed Gluing*.** Both are wrappers on `thm:extension`, which is fully
proved: translate a section to its subinterval, extend to a possible world, restrict. Small, and
it is the task that demonstrates the Extension Theorem was the presheaf's analytic content all
along. Records which clauses are choice-free (*Sheaf* is; *Directed Gluing* is not).

**D — The *Possible Worlds* clause.** `H_F ≅ lim Beh(F)(2x)` along the central restrictions.
Over `ℤ` this connects to `FrameOver.mem_HF_iff_adjacent`, already proved.

**E — Determinism and separatedness.** Prove `app:presheaf-dictionary`'s *Determinism* clause
(deterministic ⟺ every restriction injective) and connect it to
`StarDeterminism.states_eq_of_deterministic`. **The deliverable that makes this worth doing is
§5.2.1's asymmetry**: `Beh(F)` separated is strictly stronger than the validity of *Determined*
on `F`, witnessed by the drift frame `F°` already in `Metalogic/Independence/`. State that as a
theorem pair, and pose the open question of whether any `BL⋆` formula characterizes separatedness
exactly.

**F — C3/C4 as library definitions.** Promote probes 02 and 03. Deliver `TruthAtConvex`,
`ValidC3`, `ValidC4`, the germ theorems (`germ_untl_false`, `c3_box_untl_unsat`,
`c3_valid_imp_germ_valid`, `c3_nec`), the shift-invariance lemma `truthC3_timeShift`, and the
§4.1 survival table as theorems — including the six machine-checked failures. **Close the four
gaps §4.1 leaves**: `discrete_propagate_bwd` (CONDITIONAL), `z1` (CONDITIONAL), and the three
RTime axioms (UNRESOLVED). This is the task the User focus most directly asks for.

**G — The retarget.** §6.1's change and §6.3's constraint. Suggested phase decomposition, each
one agent run and each leaving `lake build FormalSystem` green: (1) introduce
`structure PossibleWorld` with an `abbrev` bridge and prove the round trip against
`TaskFrame.HF`; (2) retarget `TruthAt` and `Truth.lean`'s lemma block; (3) retarget
`Validity.lean` and delete the 12 bridges, keeping deprecated aliases; (4–6) sweep the ~280 bridge
call sites, one module cluster per phase, `Metalogic/Soundness.lean` and
`Metalogic/Decidability/` last; (7) delete the deprecated aliases and the `assert_not_exists`
audit. **Gate G on resolving the `IntTransfer` question first** — §6.1's one genuine unknown —
which is a one-phase spike, not a task of its own.

**H — Is C3's logic BX-without-seriality plus S5?** §4.2 states the containment and explicitly
declines the completeness claim. This is the natural sequel and it is genuinely open. The germ
constraint (§4.3) is the first thing any canonical-model construction for C3 will have to
accommodate, and the box-range design choice (§7.4) has to be settled before it is worth starting.

**Dropped from the planning-time list.** The candidate "formalize `app:gluing` at the
`ConvexHistory` layer, generalizing `StarPasting.paste`" is folded into B rather than run
separately — the study showed the general-convex and interval-site versions share one proof and
should not be written twice. The candidate "the `D = ℤ` path-category corollary and its relation
to BiLasso" is **not** proposed as a formalization task: §5.2.2 establishes that the interesting
content is already proved (`mem_HF_iff_adjacent`, `Agreement.extends_of_agrees`) and that the
categorical presentation *does not* transfer to the logic (`Annotation.lean`'s refutation), so
formalizing `Path(F)` as a category would add vocabulary and no theorem. Recording that finding
is the deliverable; a task is not.

**A roadmap note, not a roadmap edit.** `specs/ROADMAP.md` currently has no front for the
categorical/presheaf material and was not modified by this task. Tasks A–E constitute a coherent
new front; proposing one is a decision for whoever owns the roadmap.

### §7.4 What was NOT settled

Stated plainly so the boundaries of the study are not mistaken for its conclusions.

1. **Whether C3 and C4 have the same validities.** `validC3_imp_validC4` proves one containment;
   no separating formula was found and none is claimed. The four-way split C1/C2/C3/C4 is
   justified by *definition*, and by C1 ≠ C2 and C1 ≠ C3 as proved separations — not by four
   distinct validity sets.
2. **Four of the 45 axiom verdicts.** `discrete_propagate_bwd` and `z1` are CONDITIONAL;
   `prior_U_gap`, `prior_S_gap` and `sep` are UNRESOLVED. The RTime layer's analysis is real work
   — `K⁺`/`K⁺` are themselves restricted `U`/`S` formulas whose endpoint behaviour was not
   checked — and it belongs to task F.
3. **Whether C3's logic is a known system.** §4.2 states a containment and explicitly declines
   the completeness claim. Task H.
4. **A design choice C3 forces that the paper's footnote does not raise.** The footnote lets `□`
   quantify over *all* convex histories through `x`, germs included. §3.3 and §4.3 show that
   choice is what makes `□(φ U ψ)` unsatisfiable and `discrete_box_necessity` fail. Cutting the
   range back — to interval sections of some minimum length, or to those whose domain contains
   `dom τ` — would give a different and possibly more natural logic. **This is surfaced as a
   user decision**, non-blocking; the study's recommendation is to keep the footnote's own reading
   as the primary C3 and add the restricted variant as a named alternative, because the footnote
   is the definition of record and the germ result is more interesting stated than avoided.
5. **The `IntTransfer` question.** Whether the ℤ-transfer machinery survives a narrower index
   (§6.1, class (ii)) is the one item in the retarget that grep cannot answer. It gates task G.
6. **Whether any `BL⋆` formula characterizes separatedness of `Beh(F)` exactly.** §5.2.1 proves
   one direction and cites the repository's own countermodel for the failure of the converse for
   *Determined*; whether some other formula does better is open, and `StarDeterminism.lean`'s
   choice-dependence note suggests it does not.
7. **The paper's own review status.** `app:Structure` carries `% TODO: review in full`. Every
   §5.1 dictionary row and every task A–E tracks material the author has not finished reviewing,
   and could move under him.
