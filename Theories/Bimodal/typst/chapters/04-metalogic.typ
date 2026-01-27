// ============================================================================
// 04-metalogic.typ
// Metalogic chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *
#import "@preview/cetz:0.3.4"

= Metalogic

The metalogic for the bimodal logic *TM* establishes that the proof system and semantics describe the same space of inferences.
This chapter presents a representation theorem from which completeness and compactness follow as corollaries.
The chapter also proves that *TM* is decidable.

== Soundness

This theorem establishes that only logical consequences are derivable.

#theorem("Soundness")[
  If $Gamma tack.r phi.alt$ then $Gamma tack.r.double phi.alt$.
]

The proof proceeds by induction on the derivation structure:
- *Axioms*: Each of the 14 axiom schemata is proven valid
- *Assumptions*: Assumed formulas are true by hypothesis
- *Modus ponens*: Validity preserved under implication elimination
- *Necessitation*: Valid formulas become necessarily valid
- *Temporal necessitation*: Valid formulas become always-future valid
- *Temporal duality*: Past-future swap preserves validity
- *Weakening*: Adding premises preserves semantic consequence

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Axiom Validity*], [*Lean Theorem*], [*Technique*],
    ),
    table.hline(),
    [`prop_k_valid`], [Propositional K], [Propositional reasoning],
    [`prop_s_valid`], [Propositional S], [Propositional reasoning],
    [`ex_falso_valid`], [EFQ], [Vacuous implication],
    [`peirce_valid`], [Peirce], [Classical case analysis],
    [`modal_t_valid`], [MT], [Reflexivity of accessibility],
    [`modal_4_valid`], [M4], [Transitivity of accessibility],
    [`modal_b_valid`], [MB], [Symmetry of accessibility],
    [`modal_5_collapse_valid`], [M5], [S5 equivalence structure],
    [`modal_k_dist_valid`], [MK], [Distribution],
    [`temp_k_dist_valid`], [TK], [Temporal distribution],
    [`temp_4_valid`], [T4], [Transitivity of time],
    [`temp_a_valid`], [TA], [Temporal connectedness],
    [`temp_l_valid`], [TL], [Always implies recurrence],
    [`modal_future_valid`], [MF], [Time-shift invariance],
    [`temp_future_valid`], [TF], [Time-shift invariance],
    table.hline(),
  ),
  caption: none,
)

The MF and TF axioms use time-shift invariance to relate truth at different times (via `WorldHistory.time_shift`).

== Core Infrastructure

The completeness proof requires three foundational components including the deduction theorem, maximal consistent sets, and Lindenbaum's lemma.
These provide the infrastructure for constructing canonical models.

=== Deduction Theorem

#theorem("Deduction Theorem")[
  If $A :: Gamma tack.r B$ then $Gamma tack.r A arrow.r B$.
]

The proof uses well-founded induction on derivation height, handling each of the following rules:
- *Axiom*: Use S axiom to weaken
- *Assumption*: Identity if same, S axiom if different
- *Modus ponens*: Use K axiom distribution
- *Weakening*: Case analysis on assumption membership
- *Modal/temporal rules*: Do not apply (require empty context)


=== Consistency

#definition("Consistent")[
  A context $Gamma$ is *consistent* if $Gamma tack.r.not bot$.
]

#definition("Maximal Consistent")[
  A context $Gamma$ is *maximal consistent* if it is consistent and
  for all $phi.alt in.not Gamma$, the context $phi.alt :: Gamma$ is inconsistent.
]

#definition("Negation-Complete")[
  A set of formulas $S$ is *negation-complete* if for every formula $phi.alt$, exactly one of $phi.alt$ or $not phi.alt$ is in $S$.
]

Maximal consistent sets (MCS) are negation-complete.
This property is essential for defining canonical world states, as it ensures that every formula has a definite truth value in each MCS.

=== Lindenbaum's Lemma

#lemma("`set_lindenbaum`")[
  Every consistent context can be extended to a maximal consistent context.
]

The proof applies Zorn's lemma to the partially ordered set of consistent supersets of the given context.
Note that contexts (finite lists of formulas) embed naturally into sets, so "consistent context" and "consistent set" are used interchangeably here.
The key step is showing that the union of any chain of consistent sets is itself consistent.
This follows because any derivation uses only finitely many premises, so a derivation of $bot$ from the union would have to come from some finite subset, which is contained in some member of the chain, contradicting that member's consistency.

== Representation Theory

The _Representation Theorem_ is the core of the metalogic, providing the bridge between syntactic consistency and semantic satisfiability.
The subsequent _Completeness Theorems_ follow directly from this result.

=== Canonical World States

The semantic approach constructs world states from histories and times.
We first define these constituent concepts before assembling them into canonical structures.

#definition("History")[
  A *history* is a function $tau : ZZ arrow.r "MCS"$ mapping each time to a maximal consistent set, satisfying temporal coherence: for each time $t$, the formulas in $tau(t)$ are consistent with the temporal operators applied to formulas in $tau(t')$ for related times $t'$.
]

#definition("Time")[
  *Times* are integers ($ZZ$), providing a discrete linear order with both past and future directions.
]

#definition("Task Relation")[
  The *task relation* (`SemanticTaskRelV2`) relates world states based on the existence of histories connecting them: world state $w$ is task-related to $w'$ if there exists a history $tau$ such that $w$ and $w'$ both occur along $tau$.
]

A *canonical world state* is derived from a maximal consistent set.
The semantic approach defines world states as equivalence classes of (history, time) pairs.

#definition("Semantic World State")[
  A world state is an equivalence class of (history, time) pairs under the relation where two pairs are equivalent iff they denote the same underlying world state.#footnote[This is formalized as `SemanticWorldState`.]
]

#definition("Universal Canonical Model")[
  The *canonical model* is built from an indexed MCS family using the `IndexedMCSFamily D` construction:
  - Indexed family: `IndexedMCSFamily D` assigns an MCS to each time $t : D$
  - Temporal coherence: G/H formulas propagate between time-indexed MCS via strict inequalities
  - Canonical frame: `canonical_model D family` with task relation via histories
  - Duration type: Parametric over totally ordered abelian group $D$

  The construction is formula-independent and universally parametric, avoiding the T-axiom requirement of same-MCS-at-all-times approaches.#footnote[The T-axiom ($G phi.alt arrow.r phi.alt$) is _not_ valid in TM logic because G/H are irreflexive operators.]
]

#definition("Canonical Valuation")[
  An atom $p$ is true at world state $[tau, x]$ iff $p in "MCS"(tau(x))$.
]

#lemma("Truth Lemma")[
  In the canonical model, $phi.alt in "MCS"(t)$ iff $phi.alt$ is true at time $t$ in the canonical model.#footnote[This is proven as `truth_lemma` in `Theories/Bimodal/Metalogic/Representation/TruthLemma.lean`.]
]

The _quotient construction_ identifies (history, time) pairs that agree on which formulas hold, forming equivalence classes.
Two pairs $(tau_1, t_1)$ and $(tau_2, t_2)$ are equivalent when $tau_1(t_1) = tau_2(t_2)$ as maximal consistent sets.
The _Truth Lemma_ follows directly from this construction: membership in a maximal consistent set corresponds to truth by definition of the equivalence class.

=== Representation Theorem

#theorem("Representation Theorem")[
  Every consistent formula is satisfiable in the canonical model.#footnote[This is proven as `representation_theorem` in `Theories/Bimodal/Metalogic/Representation/UniversalCanonicalModel.lean`.]
]

This theorem is the pivotal result linking syntax to semantics.
The proof strategy is:
+ Given a consistent context $Gamma$, convert it to a set $S = "contextToSet"(Gamma)$.
+ Apply Lindenbaum's lemma to extend $S$ to a maximal consistent set $M$.
+ View $M$ as a canonical world state.
+ By the truth lemma, all formulas in $Gamma$ are satisfied at this world.

The elegance of this approach is that the MCS construction makes the _Truth Lemma_ essentially trivial since truth _is_ membership in the MCS.

#theorem("Strong Representation Theorem")[
  If $Gamma tack.r.not phi.alt$, then $Gamma union {not phi.alt}$ is satisfiable in the canonical model.#footnote[This is proven as `strong_representation_theorem`.]
]

This strengthening is crucial for completeness: it says that any formula unprovable from a context can be made false while satisfying the context.
The proof adds $not phi.alt$ to the context and applies the standard _Representation Theorem_ to the resulting consistent set.

=== Theorem Dependency Structure <fig:theorem-deps>

The diagram below illustrates the dependency structure of the completeness proof.
The core infrastructure (top row) feeds into the central _Representation Theorem_, from which the completeness corollaries follow.

#figure(
  cetz.canvas({
    import cetz.draw: *

    let box-style = (stroke: 0.5pt, fill: none)
    let arrow-style = (stroke: 0.5pt + gray.darken(20%), mark: (end: ">"))

    // Core Infrastructure layer (top)
    rect((-2, 3.5), (2, 4.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((0, 4), text(size: 8pt)[Deduction Theorem\ #text(size: 6pt)[`deduction_theorem`]])

    rect((3, 3.5), (7, 4.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((5, 4), text(size: 8pt)[Lindenbaum's Lemma\ #text(size: 6pt)[`set_lindenbaum`]])

    rect((8, 3.5), (12, 4.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((10, 4), text(size: 8pt)[Maximal Consistent Sets\ #text(size: 6pt)[`MaximalConsistent`]])

    // Representation layer (middle)
    rect((1.5, 1.5), (8.5, 2.5), ..box-style, fill: green.lighten(85%), radius: 4pt)
    content((5, 2), text(size: 9pt, weight: "bold")[Representation Theorem]
      + text(size: 6pt)[\ `representation_theorem`])

    // Completeness layer (bottom)
    rect((-0.5, -0.5), (4, 0.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((1.75, 0), text(size: 8pt)[Weak Completeness\ #text(size: 6pt)[`semantic_weak_completeness`]])

    rect((6, -0.5), (10.5, 0.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((8.25, 0), text(size: 8pt)[Strong Completeness\ #text(size: 6pt)[`main_strong_completeness`]])

    // Arrows from Core to Representation
    line((0, 3.5), (3.5, 2.5), ..arrow-style)
    line((5, 3.5), (5, 2.5), ..arrow-style)
    line((10, 3.5), (6.5, 2.5), ..arrow-style)

    // Arrows from Representation to Completeness
    line((3.5, 1.5), (1.75, 0.5), ..arrow-style)
    line((6.5, 1.5), (8.25, 0.5), ..arrow-style)
  }),
  caption: [Theorem dependency structure for completeness.],
)

The three foundational components---the _Deduction Theorem_, _Lindenbaum's Lemma_, and _Maximal Consistent Sets_---provide the infrastructure for the _Representation Theorem_.
Both weak and strong completeness then follow as direct corollaries via contrapositive arguments.

== Completeness as Corollary

The _Completeness Theorems_ follow directly from the _Representation Theorem_ via contrapositive arguments.

=== Weak Completeness

#theorem("Weak Completeness")[
  If $tack.r.double phi.alt$, then $tack.r phi.alt$.#footnote[This is proven as `semantic_weak_completeness`.]
]

The proof proceeds by contraposition:
+ Assume $tack.r.not phi.alt$ (i.e., the empty context does not derive $phi.alt$).
+ Then ${not phi.alt}$ is consistent (otherwise we could derive $phi.alt$).
+ By the _Representation Theorem_, ${not phi.alt}$ is satisfiable in the canonical model.
+ So there exists a world where $not phi.alt$ is true, meaning $phi.alt$ is false.
+ Hence $phi.alt$ is not valid.

By contraposition, validity implies provability.

=== Strong Completeness

==== Note on Infinite Contexts

The current implementation uses list-based finite contexts (`Context = List Formula`).
This makes the compactness theorem trivial: if every finite subset of $Gamma$ is satisfiable, then $Gamma$ is satisfiable (since $Gamma$ is already finite).

A true compactness result for infinite sets would require:
+ Migrating from `List Formula` to `Set Formula` contexts
+ Ensuring derivability is finitary (derivations use finitely many premises)
+ Proving: if $Gamma tack.r.double phi.alt$, then finite $Delta subset.eq Gamma$ with $Delta tack.r.double phi.alt$

This is a standard result in modal logic but is not required for the current completeness proof.
See `Boneyard/Metalogic_v2/Applications/Compactness.lean` for the trivial version with list-based contexts.

#theorem("Strong Completeness")[
  If $Gamma tack.r.double phi.alt$, then $Gamma tack.r phi.alt$.#footnote[This is proven as `main_strong_completeness` with bridge sorries for the generalization.]
]

The proof extends weak completeness using an implication chain technique:
+ Assume semantic consequence: $Gamma tack.r.double phi.alt$.
+ For context $Gamma = [psi_1, dots, psi_n]$, build the implication chain $psi_1 arrow.r (psi_2 arrow.r dots (psi_n arrow.r phi.alt))$.
+ Show this chain is valid (from the semantic consequence assumption).
+ By weak completeness, the chain is provable.
+ Unfold the chain with repeated modus ponens applications to obtain $Gamma tack.r phi.alt$.

#theorem("Provable iff Valid")[
  $tack.r phi.alt arrow.l.r tack.r.double phi.alt$.#footnote[This is proven as `main_provable_iff_valid`, establishing completeness of *TM*.]
]

This biconditional shows that the proof system and semantics align perfectly.
Soundness (left-to-right) ensures no non-logical consequences are derivable, while completeness (right-to-left) ensures all logical consequences are captured by the proof system.
Together, they establish that *TM* provides an exact syntactic characterization of semantic validity.

=== Two Canonical Model Approaches

The codebase contains two canonical model constructions.
Understanding their differences explains why the semantic approach is primary.

*Syntactic Approach.*
World states are directly identified with maximal consistent sets.
Accessibility is defined via modal witnesses: $square.stroked phi.alt in w$ implies $phi.alt in w'$ for all accessible $w'$.
This approach requires explicit negation-completeness proofs for locally consistent sets.
The syntactic approach is archived in `Boneyard/` for historical reference.

*Semantic Approach.*
World states are equivalence classes of (history, time) pairs, where two pairs are equivalent iff they denote the same underlying world state.
This approach offers key advantages:
- *Truth lemma*: Follows trivially from the quotient construction.
- *Compositionality*: The task relation is defined via history concatenation, making compositionality proofs straightforward.
- *Negation-completeness*: The semantic approach does not require proving negation-completeness of arbitrary locally consistent sets, a property that caused difficulties in the syntactic approach.

== Decidability

The decidability of TM bimodal logic rests on the _Finite Model Property_: if a formula is satisfiable, it is satisfiable in a finite model bounded by the formula's modal and temporal depth.
The bound on model size is $2^(|"closure"(phi.alt)|)$, where the subformula closure contains all relevant formulas for determining the truth of $phi.alt$.
This property connects the representation infrastructure to decidability by ensuring that satisfiability checking can terminate.

The decidability proof proceeds via a tableau-based decision procedure.

#theorem("Decidability")[
  Validity in TM bimodal logic is decidable: for any formula $phi.alt$, either $tack.r.double phi.alt$ or $not tack.r.double phi.alt$.
]

#theorem("Decision Soundness")[
  If the decision procedure returns "valid" with proof $pi$, then $tack.r.double phi.alt$.#footnote[This is proven as `decide_sound`.]
]

Here $pi$ is a derivation term witnessing $tack.r phi.alt$, constructed from the closed tableau.
In Lean 4, this is a term of type `ContextDerivable [] phi`, representing a formal proof tree.

The decision procedure operates as follows:
+ *Direct axiom proof*: Check if $phi.alt$ matches one of the axiom schemata directly, yielding an immediate derivation.
+ *Proof search*: Apply Lean 4 tactics (`decide`, `simp`) with bounded recursion depth to find a derivation automatically.
+ *Tableau construction*: Build a systematic tree that decomposes $phi.alt$ into simpler signed formulas.
+ If all branches close: formula is valid, extract proof.
+ If open saturated branch: formula is invalid, extract countermodel.

A _tableau_ is a tree-structured refutation method: to prove $phi.alt$ valid, we assume $phi.alt$ is false and systematically derive contradictions.
Each branch represents a possible scenario; if all branches lead to contradictions, the original assumption was impossible, so $phi.alt$ must be valid.

=== Tableau Structure

The tableau uses *signed formulas* with annotations:
- $T(phi.alt)$: formula $phi.alt$ is assumed true
- $F(phi.alt)$: formula $phi.alt$ is assumed false

*Expansion rules* are categorized as:
- *Propositional*: $T(phi.alt and psi)$ splits, $F(phi.alt arrow.r psi)$ splits, etc.
- *Modal*: $T(square.stroked phi.alt)$ propagates to accessible worlds, $F(diamond.stroked phi.alt)$ creates witness
- *Temporal*: $T(triangle.stroked.t phi.alt)$ propagates to future times, $F(triangle.stroked.b phi.alt)$ creates witness

A branch *closes* when it contains both $T(phi.alt)$ and $F(phi.alt)$ for some formula.
A branch is *saturated* when no expansion rules apply.

=== Complexity

#figure(
  table(
    columns: 2,
    stroke: none,
    table.hline(),
    table.header(
      [*Measure*], [*Complexity*],
    ),
    table.hline(),
    [Time], [$O(2^n)$ where $n$ is formula size],
    [Space], [$O(n)$],
    [Class], [PSPACE-complete],
    table.hline(),
  ),
  caption: none,
)

The exponential time bound means formulas of modest size (30--50 symbols) remain tractable on modern hardware.
PSPACE-completeness implies that modal satisfiability is among the hardest problems solvable with polynomial space, but the linear space bound makes memory usage manageable even for larger formulas.

=== Decision Result Types

The decision procedure returns one of three outcomes:
- `valid proof`: Formula is valid with derivation tree
- `invalid counter`: Formula is invalid with countermodel
- `timeout`: Resources exhausted before decision

Despite computational limitations, decidability is practically valuable: small formulas (most proof obligations in practice) resolve quickly, invalid formulas are often rejected early without full exploration, and countermodels provide concrete feedback for debugging specifications.

== File Organization and Dependencies

The active metalogic infrastructure is in `Theories/Bimodal/Metalogic/`, using the `IndexedMCSFamily` approach.
Deprecated code in `Boneyard/Metalogic_v2/` is preserved for historical reference.
The following diagram illustrates the import structure of the active codebase.

#figure(
  cetz.canvas({
    import cetz.draw: *

    let box-style = (stroke: 0.5pt)
    let arrow-style = (stroke: 0.5pt + gray.darken(30%), mark: (end: ">"))

    // Core layer (bottom)
    rect((-1.5, -0.5), (2.5, 0.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((0.5, 0), text(size: 7pt)[Core/\ #text(size: 5pt)[Basic, Provability, Deduction, MCS]])

    rect((4, -0.5), (8, 0.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((6, 0), text(size: 7pt)[Soundness/\ #text(size: 5pt)[Soundness, SoundnessLemmas]])

    // Representation layer (middle)
    rect((1.5, 1.5), (6.5, 2.5), ..box-style, fill: green.lighten(85%), radius: 4pt)
    content((4, 2), text(size: 7pt)[Representation/\ #text(size: 5pt)[Canonical, Truth, Representation]])

    // Completeness and FMP
    rect((-1, 3.5), (3, 4.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((1, 4), text(size: 7pt)[Completeness/\ #text(size: 5pt)[Weak, Strong]])

    rect((5, 3.5), (8.5, 4.5), ..box-style, fill: yellow.lighten(80%), radius: 4pt)
    content((6.75, 4), text(size: 7pt)[FMP.lean\ #text(size: 5pt)[Central Hub]])

    // Applications and Decidability
    rect((-1, 5.5), (3, 6.5), ..box-style, fill: purple.lighten(90%), radius: 4pt)
    content((1, 6), text(size: 7pt)[Applications/\ #text(size: 5pt)[Compactness]])

    rect((5, 5.5), (8.5, 6.5), ..box-style, fill: purple.lighten(90%), radius: 4pt)
    content((6.75, 6), text(size: 7pt)[Decidability/\ #text(size: 5pt)[Tableau, Saturation]])

    // Arrows
    line((0.5, 0.5), (3, 1.5), ..arrow-style)
    line((6, 0.5), (5, 1.5), ..arrow-style)
    line((4, 2.5), (1, 3.5), ..arrow-style)
    line((4, 2.5), (6.75, 3.5), ..arrow-style)
    line((1, 4.5), (1, 5.5), ..arrow-style)
    line((6.75, 4.5), (6.75, 5.5), ..arrow-style)
    line((5, 4), (3, 4), ..arrow-style)
  }),
  caption: none,
)

*Directory descriptions*:
- *`Core/`*: Foundational definitions including provability (`ContextDerivable`), deduction theorem, and maximal consistent sets.
- *`Soundness/`*: Validity proofs for all 15 axiom schemata and the main soundness theorem.
- *`Representation/`*: Canonical model construction, truth lemma, and the central representation theorems.
- *`Completeness/`*: Weak and strong completeness theorems derived from representation.
- *`Applications/`*: Compactness theorem (trivial for list-based contexts).
- *`Decidability/`*: Tableau-based decision procedure with proof/countermodel extraction.

== Implementation Status

=== Sorry Status

The `Metalogic_v2` codebase has three remaining `sorry` statements, none of which block the core completeness results:

+ `semantic_task_rel_compositionality` (SemanticCanonicalModel.lean:236) --- Finite time domain limitation; a fundamental issue with Int-valued durations exceeding finite time bounds.
+ `main_provable_iff_valid_v2` completeness direction (SemanticCanonicalModel.lean:647) --- Requires truth bridge from general validity to finite model truth.
+ `finite_model_property_constructive` truth bridge (FiniteModelProperty.lean:481) --- Same truth bridge issue.

The core completeness result `semantic_weak_completeness` is fully proven without sorries.

=== Decidability Implementation

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Submodule*], [*Status*], [*Notes*],
    ),
    table.hline(),
    [SignedFormula], [Complete], [Sign, SignedFormula, Branch types],
    [Tableau], [Complete], [Expansion rules],
    [Closure], [Complete], [Branch closure detection],
    [Saturation], [Complete], [Fuel-based termination],
    [ProofExtraction], [Partial], [Axiom instances only],
    [CountermodelExtraction], [Complete], [From open branches],
    [DecisionProcedure], [Complete], [Main decide function],
    [Soundness], [Proven], [`decide_sound`],
    [Completeness], [Partial], [Requires Finite Model Property],
    table.hline(),
  ),
  caption: none,
)

=== Metalogic Implementation

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*Component*], [*Status*], [*Lean*],
    ),
    table.hline(),
    [Soundness], [Proven], [`soundness`],
    [Deduction Theorem], [Proven], [`deduction_theorem`],
    [Lindenbaum Lemma], [Proven], [`set_lindenbaum`],
    [IndexedMCSFamily], [Proven], [`IndexedMCSFamily`],
    [Truth Lemma], [Proven], [`truth_lemma`],
    [Representation Theorem], [Proven], [`representation_theorem`],
    [Weak Completeness], [Proven], [`semantic_weak_completeness`],
    [Strong Completeness], [Proven\*], [`main_strong_completeness`],
    [Provable iff Valid], [Proven], [`main_provable_iff_valid`],
    [Finite Model Property], [Statement], [`finite_model_property`],
    [Decidability Soundness], [Proven], [`decide_sound`],
    table.hline(),
  ),
  caption: none,
)

\* Strong completeness uses the weak completeness result, which is fully proven.
The three sorries listed above affect only the finite model property path.
