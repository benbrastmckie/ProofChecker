// ============================================================================
// 04-metalogic.typ
// Metalogic chapter for Bimodal TM Logic Reference Manual
// ============================================================================

#import "../template.typ": *
#import "@preview/cetz:0.3.4"

= Metalogic

The metalogic for the bimodal logic *TM* establishes that the proof system and semantics describe the same space of inferences.
This chapter presents two approaches to completeness: the _representation theorem_, which provides canonical model infrastructure, and the _contrapositive approach_ via `semantic_weak_completeness`, which is the primary sorry-free completeness theorem.
Both approaches rely on the same foundational infrastructure---the deduction theorem, maximal consistent sets, and Lindenbaum's lemma---but the contrapositive approach avoids the truth bridge gap that creates architectural limitations in the representation theorem path.
The chapter also proves that *TM* is decidable.

== Soundness

This theorem establishes that only logical consequences are derivable.

#theorem("Soundness")[
  If $Gamma tack.r phi.alt$ then $Gamma tack.r.double phi.alt$.
]

The proof proceeds by induction on the derivation structure:
- *Axioms*: Each of the 15 axiom schemata is proven valid
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
The axiom validity proofs are located in `Metalogic/Soundness/Soundness.lean`, with supporting lemmas in `SoundnessLemmas.lean`.

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

The _Representation Theorem_ provides the bridge between syntactic consistency and semantic satisfiability via canonical model construction.
While the representation theorem and truth lemma are mathematically elegant, the Lean formalization contains architectural limitations.

*Architectural Note*: The `Representation/` subdirectory contains deprecated code with sorries.
The truth lemma has an S5-style Box semantics limitation: the modal Box quantifies over _all_ histories in the canonical frame, whereas TM logic requires quantification over histories sharing the current time point.
This creates a "truth bridge gap" that is intentionally left as sorry.
For a sorry-free completeness proof, the contrapositive approach via `semantic_weak_completeness` (documented in the next section) is recommended.

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
  A sentence letter $p$ is true at world state $[tau, x]$ iff $p in "MCS"(tau(x))$.
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

This theorem links syntax to semantics via the canonical model construction.
While the representation theorem depends on the truth lemma (which has architectural sorries), the infrastructure it develops is reused by the sorry-free contrapositive approach.
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

The diagram below illustrates the dependency structure of the completeness proof, showing both the deprecated representation theorem path and the primary contrapositive path.
The core infrastructure (top row) feeds into both approaches, but only the contrapositive path (green, right side) is sorry-free.

#figure(
  cetz.canvas({
    import cetz.draw: *

    let box-style = (stroke: 0.5pt, fill: none)
    let arrow-style = (stroke: 0.5pt + gray.darken(20%), mark: (end: ">"))
    let deprecated-arrow = (stroke: 0.5pt + gray.lighten(40%), mark: (end: ">"))

    // Core Infrastructure layer (top)
    rect((-2, 4.5), (2, 5.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((0, 5), text(size: 8pt)[Deduction Theorem\ #text(size: 6pt)[`deduction_theorem`]])

    rect((3.5, 4.5), (7.5, 5.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((5.5, 5), text(size: 8pt)[Lindenbaum's Lemma\ #text(size: 6pt)[`set_lindenbaum`]])

    rect((9, 4.5), (13, 5.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((11, 5), text(size: 8pt)[Maximal Consistent Sets\ #text(size: 6pt)[`MaximalConsistent`]])

    // Middle layer - two paths diverge
    // Representation path (deprecated - left side)
    rect((-1, 2.5), (4, 3.5), ..box-style, fill: yellow.lighten(80%), radius: 4pt)
    content((1.5, 3), text(size: 8pt)[Representation Theorem\ #text(size: 6pt, fill: gray)[`representation_theorem` (deprecated)]])

    // Contrapositive path (primary - right side)
    rect((7, 2.5), (13, 3.5), ..box-style, fill: green.lighten(80%), radius: 4pt)
    content((10, 3), text(size: 8pt, weight: "bold")[Contrapositive Approach\ #text(size: 6pt)[`semantic_weak_completeness` (primary)]])

    // Completeness layer (bottom)
    rect((3, 0.5), (8, 1.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((5.5, 1), text(size: 8pt)[Weak Completeness\ #text(size: 6pt)[sorry-free]])

    rect((9.5, 0.5), (13.5, 1.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((11.5, 1), text(size: 8pt)[Strong Completeness\ #text(size: 6pt)[`main_strong_completeness`]])

    // Arrows from Core to middle layer
    line((0, 4.5), (1.5, 3.5), ..deprecated-arrow)
    line((5.5, 4.5), (2.5, 3.5), ..deprecated-arrow)
    line((5.5, 4.5), (8.5, 3.5), ..arrow-style)
    line((11, 4.5), (11, 3.5), ..arrow-style)

    // Arrows from middle to completeness
    line((1.5, 2.5), (4.5, 1.5), ..deprecated-arrow)
    line((10, 2.5), (6.5, 1.5), ..arrow-style)
    line((11, 2.5), (11.5, 1.5), ..arrow-style)
  }),
  caption: [Theorem dependency structure. Green path (contrapositive) is sorry-free; yellow path (representation) is deprecated.],
)

The three foundational components---the _Deduction Theorem_, _Lindenbaum's Lemma_, and _Maximal Consistent Sets_---provide infrastructure for both approaches.
The contrapositive path via `semantic_weak_completeness` is the primary sorry-free completeness theorem.
The representation theorem path remains in the codebase for its infrastructure contributions but has architectural sorries in the truth lemma.

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

=== The Contrapositive Approach (Primary)

The `semantic_weak_completeness` theorem in `FMP/SemanticCanonicalModel.lean` provides the canonical sorry-free completeness proof.
Unlike the representation theorem path (which depends on the truth lemma with architectural sorries), this approach works via contrapositive and avoids the truth bridge gap entirely.

#theorem("Contrapositive Weak Completeness")[
  If $tack.r.double phi.alt$, then $tack.r phi.alt$.#footnote[This is `semantic_weak_completeness` in `FMP/SemanticCanonicalModel.lean`---the primary sorry-free completeness theorem.]
]

The proof strategy proceeds as follows:
+ *Contrapositive*: Transform `valid phi -> provable phi` into `not provable phi -> not valid phi`.
+ *Consistency*: If $phi.alt$ is not provable, then ${not phi.alt}$ is consistent (otherwise we could derive $phi.alt$ from the empty context).
+ *Lindenbaum extension*: By Lindenbaum's lemma, extend ${not phi.alt}$ to a maximal consistent set $M$.
+ *Closure projection*: Project $M$ to a closure MCS containing the relevant subformulas.
+ *Finite world state construction*: Build a `FiniteWorldState` from closure MCS membership.
+ *Countermodel*: By construction, $not phi.alt$ is true at this world state.
+ *Invalidity*: The world state provides a countermodel, so $phi.alt$ is not valid.

*Why this avoids the truth bridge gap*: The contrapositive approach does not require proving that _every_ formula in the MCS is true at the constructed world state (the truth lemma).
Instead, it only needs to show that the specific formula $not phi.alt$ is true, which follows directly from the construction: the assignment _is_ the MCS membership function.
This targeted approach sidesteps the Box semantics limitation where S5-style universal quantification over all histories conflicts with TM's time-indexed modal accessibility.

The theorem `sorry_free_weak_completeness` provides an explicit alias documenting this as the preferred completeness path.

=== Two Canonical Model Approaches

The codebase contains two canonical model constructions.
Understanding their differences explains why the contrapositive approach supersedes the representation theorem path.

*Representation Theorem Path (Deprecated).*
The representation theorem uses canonical model construction where world states are identified with maximal consistent sets.
This approach requires the truth lemma, which has architectural sorries due to the Box semantics limitation: the S5-style Box quantifies over _all_ histories, not just those sharing the current time point.
The `Representation/` subdirectory contains this code, preserved for its infrastructure contributions to the contrapositive approach.

*Contrapositive Path (Primary).*
The `semantic_weak_completeness` theorem in `FMP/SemanticCanonicalModel.lean` works via contrapositive.
This approach reuses the MCS infrastructure from the representation path but avoids the truth bridge gap by constructing a targeted countermodel for the specific formula being proven invalid.
This is the recommended completeness theorem for all downstream applications.

*Historical Note*: An older syntactic approach (world states as MCS directly, with modal witness accessibility) is archived in `Boneyard/` for historical reference.

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
The primary completeness theorem `semantic_weak_completeness` is in `FMP/SemanticCanonicalModel.lean`.
The following diagram illustrates the import structure of the active codebase.

#figure(
  cetz.canvas({
    import cetz.draw: *

    let box-style = (stroke: 0.5pt)
    let arrow-style = (stroke: 0.5pt + gray.darken(30%), mark: (end: ">"))
    let deprecated-style = (stroke: 0.5pt + gray.lighten(30%), mark: (end: ">"))

    // Core layer (bottom)
    rect((-1.5, -0.5), (2.5, 0.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((0.5, 0), text(size: 7pt)[Core/\ #text(size: 5pt)[Basic, Provability, Deduction, MCS]])

    rect((4, -0.5), (8, 0.5), ..box-style, fill: blue.lighten(90%), radius: 4pt)
    content((6, 0), text(size: 7pt)[Soundness/\ #text(size: 5pt)[15 axioms, soundness theorem]])

    // Middle layer - Representation (deprecated) and FMP (primary)
    rect((-1.5, 1.5), (3.5, 2.5), ..box-style, fill: yellow.lighten(85%), radius: 4pt)
    content((1, 2), text(size: 7pt, fill: gray)[Representation/\ #text(size: 5pt)[Canonical model (deprecated)]])

    rect((5.5, 1.5), (11.5, 2.5), ..box-style, fill: green.lighten(80%), radius: 4pt)
    content((8.5, 2), text(size: 7pt, weight: "bold")[FMP/\ #text(size: 5pt)[`semantic_weak_completeness` (primary)]])

    // Completeness and Algebraic
    rect((-1.5, 3.5), (3.5, 4.5), ..box-style, fill: orange.lighten(85%), radius: 4pt)
    content((1, 4), text(size: 7pt)[Completeness/\ #text(size: 5pt)[Weak, Strong completeness]])

    rect((5.5, 3.5), (11.5, 4.5), ..box-style, fill: green.lighten(85%), radius: 4pt)
    content((8.5, 4), text(size: 7pt)[Algebraic/\ #text(size: 5pt)[Alternative sorry-free approach]])

    // Applications and Decidability
    rect((-1.5, 5.5), (3.5, 6.5), ..box-style, fill: purple.lighten(90%), radius: 4pt)
    content((1, 6), text(size: 7pt)[Compactness/\ #text(size: 5pt)[List-based compactness]])

    rect((5.5, 5.5), (11.5, 6.5), ..box-style, fill: purple.lighten(90%), radius: 4pt)
    content((8.5, 6), text(size: 7pt)[Decidability/\ #text(size: 5pt)[Tableau procedure]])

    // Arrows from Core/Soundness to middle layer
    line((0.5, 0.5), (1, 1.5), ..deprecated-style)
    line((6, 0.5), (7, 1.5), ..arrow-style)

    // Arrows from middle to completeness
    line((1, 2.5), (1, 3.5), ..deprecated-style)
    line((8.5, 2.5), (8.5, 3.5), ..arrow-style)

    // Arrows to top layer
    line((1, 4.5), (1, 5.5), ..arrow-style)
    line((8.5, 4.5), (8.5, 5.5), ..arrow-style)
  }),
  caption: [Directory structure. Green boxes contain sorry-free code; yellow box is deprecated.],
)

*Directory descriptions*:
- *`Core/`*: Foundational definitions including provability (`ContextDerivable`), deduction theorem, and maximal consistent sets.
- *`Soundness/`*: Validity proofs for all 15 axiom schemata and the main soundness theorem.
- *`Representation/`*: Canonical model construction, truth lemma, and representation theorems. _Deprecated_: contains architectural sorries.
- *`FMP/`*: Finite Model Property. Contains the primary sorry-free completeness theorem `semantic_weak_completeness`.
- *`Completeness/`*: Weak and strong completeness theorems using both representation and FMP paths.
- *`Algebraic/`*: Alternative sorry-free completeness via Lindenbaum quotient and Boolean structure.
- *`Compactness/`*: Compactness theorem (trivial for list-based contexts).
- *`Decidability/`*: Tableau-based decision procedure with proof/countermodel extraction.

== Implementation Status

=== Sorry Status

The `Metalogic/` codebase contains 20 `sorry` statements, _all of which are deprecated with sorry-free alternatives_.
The primary completeness theorem `semantic_weak_completeness` is fully proven without sorries.

#figure(
  table(
    columns: 3,
    stroke: none,
    table.hline(),
    table.header(
      [*File*], [*Count*], [*Cause*],
    ),
    table.hline(),
    [`TruthLemma.lean`], [4], [Box/temporal backward directions],
    [`TaskRelation.lean`], [5], [Cross-sign duration composition],
    [`CoherentConstruction.lean`], [8], [Cross-origin coherence],
    [`SemanticCanonicalModel.lean`], [2], [Frame compositionality, truth bridge],
    [`FiniteModelProperty.lean`], [1], [FMP truth bridge],
    table.hline(),
    [*Total*], [*20*], [All deprecated---use `semantic_weak_completeness`],
    table.hline(),
  ),
  caption: none,
)

*Architectural Note*: These sorries are _not_ incomplete work.
They represent fundamental limitations in the representation theorem approach: the S5-style Box semantics quantifies over all histories, whereas TM logic requires quantification over histories sharing the current time point.
The contrapositive approach via `semantic_weak_completeness` avoids these limitations entirely and is recommended for all downstream applications.

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
    [Truth Lemma], [Deprecated], [`truth_lemma` (has sorries)],
    [Representation Theorem], [Deprecated], [`representation_theorem` (has sorries)],
    [*Weak Completeness*], [*Proven*], [*`semantic_weak_completeness`* (sorry-free)],
    [Strong Completeness], [Proven], [`main_strong_completeness`],
    [Provable iff Valid], [Proven], [`main_provable_iff_valid`],
    [Algebraic Completeness], [Proven], [`AlgebraicRepresentation` (sorry-free)],
    [Finite Model Property], [Statement], [`finite_model_property` (has sorries)],
    [Decidability Soundness], [Proven], [`decide_sound`],
    table.hline(),
  ),
  caption: none,
)

*Status Key*:
- *Proven*: No sorries, fully verified.
- *Deprecated*: Contains architectural sorries; use sorry-free alternative.
- *Statement*: Theorem stated but proof has sorries.

The sorry-free completeness path via `semantic_weak_completeness` is the recommended approach for all applications requiring verified completeness.
