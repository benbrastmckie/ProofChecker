# Metalogic/Conservativity/Star

The register extension L⋆ = L⁺ plus the manuscript's time registers `↑ⁱ` / `↓ⁱ`
(`def:BLstar-semantics`), and its logic **TM⋆**.

TM⋆ is formalization-native: the manuscript supplies no proof system for `\BL^\star`, and every
earlier L⋆ deliverable in this tree was semantic. It is built to the shape of
`PlusAxiom`/`PlusDerivationTree` (`FormalSystem/StarLanguage/`) precisely so that the two systems
are structurally comparable and the L⁺ ⊂ L⋆ questions can be *stated* — which, before it existed,
they could not be.

Its axiom set is **one `ofBase` constructor** carrying every TM⁺ schema at its `ofPlus`
instances, plus sixteen register schemata. The TM block is embedded rather than re-declared
because `modal_future` (`□φ → □Gφ`) is *refuted* over `StarFormula` (`refute_modal_future`,
`Semantics/StarNonValidities.lean`): MF is the only schema in that block whose soundness proof
consumes time-shift homogeneity, and the L⋆ time-shift lemma shifts the stored-time vector along
with the history. The recorded cost is that TM⋆'s inherited temporal schemata are available only
at register-free instances. The return is that soundness for the whole TM block is a two-line
transport, and that the embedding of TM⁺ derivations is a one-line `axiom` case.

## Modules

<!-- BEGIN GENERATED: inventory dir=FormalSystem/Metalogic/Conservativity/Star -->
| File | Lines | Description |
|------|------:|-------------|
| `Forward.lean` | 195 | Conservativity: `forward_star` and `starDerivable_ofFormula_iff` over TM, unconditional in both directions at all four classes; the conditional pair `starConservative_of_plusComplete` / `plusIncomplete_of_starNonconservative` over TM⁺. |
| `StarAxiomValidity.lean` | 322 | The two dispatch lemmas, one arm per `StarAxiom` constructor and no wildcard, plus the sixteen named register-schema validities they dispatch to. |
| `StarSoundness.lean` | 202 | Soundness of TM⋆ at every frame class, by the companion recursion carrying validity and swap-validity, plus the four rows and consistency at `.Base`. |
<!-- END GENERATED -->

## Key Results

- `starAxiom_validIn_min` / `starAxiom_swap_validIn_min` — every schema and every temporal dual is
  valid at its own minimum frame class. The `ofBase` arm transports
  `plusAxiom_validIn_min` / `plusAxiom_swap_validIn_min` along `starValidOnFrames_ofPlus`; **no
  L⋆ atomization is used, and none can exist** (neither `↓ⁱχ` nor `↑ⁱχ` is state-determined, so
  `stab_state_only` has no L⋆ analogue).
- `star_soundness_validIn` — soundness of TM⋆ at every frame class, TD discharged semantically.
- `starDerivable_ofFormula_iff` — **TM⋆ is a conservative extension of TM**, both directions, at
  all four classes, unconditionally.
- `starConservative_of_plusComplete` with `plusIncomplete_of_starNonconservative` — the L⁺ ⊂ L⋆
  row, as a proved conditional pair.

## Metatheory rows

| Row | Status | Where |
|-----|--------|-------|
| TM⋆ soundness, all four classes | **landed** | `StarSoundness.lean` |
| TM⋆ consistent at `.Base` | **landed** | `StarSoundness.lean`, `star_not_derivable_nil_bot` |
| every TM⁺ theorem is a TM⋆ theorem at its embedding | **landed** | `StarLanguage/Embedding.lean` |
| TM⋆ conservative over TM, both directions, all four classes | **landed** | `Forward.lean` |
| TM⋆ conservative over TM⁺ | **CONDITIONAL on general TM⁺ completeness**, with an unconditional contrapositive | `Forward.lean` |
| **TM⋆ completeness, any class** | **OPEN** — never stated, never sorried; two obstructions named below | — |

## Why the TM⁺ row is conditional, and why that is a result

The forward direction over TM runs *TM⋆ soundness → truth transfer → **TM** completeness engine*,
and TM has engines at all four classes. One level up the same composition needs **TM⁺**
completeness, which is open at every class (`../Plus/README.md`). Given TM⋆ soundness the two
questions are the same question: a separating witness for non-conservativity is an L⁺ formula
whose embedding is a TM⋆ theorem — hence, by soundness, `PlusValidIn fc` — while the formula
itself is not a TM⁺ theorem, which is exactly a witness of TM⁺ incompleteness. That is
`plusIncomplete_of_starNonconservative`, and it is unconditional.

So the L⁺ ⊂ L⋆ question cannot be settled either way without settling TM⁺ completeness. Stating
it as a conditional pair records that fact; asserting or denying conservativity would not.

**Both syntactic routes are closed, by machine-checked refutations.** Naive register erasure
sends the `StarValid` formula `↑¹G↓¹p → p` (`storeG_recall_valid`) to `Gp → p`, refuted over `NF`
(`refute_erasure`) — both in `Semantics/StarNonValidities.lean`. Register collapse (identifying
every register with the time of evaluation) sends the rigidity schema `↓ⁱφ → G↓ⁱφ` to `φ → Gφ`,
which is not even valid. There is therefore no translation-based route to the L⁺ row.

## TM⋆ completeness is OPEN, under two named obstructions

Not attempted, not sorried, not stubbed. The two obstructions are recorded so that the entry is
not a bare "open".

**(a) The engine obstruction.** The countermodels produced by all four TM completeness engines
are *deterministic*. Every deterministic frame validates `sent:det`
(`sentDet_of_deterministic`, `Semantics/StarDeterminism.lean`), and `sent:det` is **not**
`StarValid` (`refute_sentDet` / `not_starValid_sentDet`,
`Semantics/StarNonValidities.lean`). So no existing engine can build a countermodel for
`¬ sentDet p`, and none of them transfers to L⋆ as it stands.

This is *strictly worse* than the L⁺ situation. There, the same fact about the engines is what
makes the **deterministic** row available — on deterministic frames `⊡` is the identity, so
narrowing to that class recovers completeness for TM⁺ + *Determined*
(`Metalogic/Deterministic/`). The registers do **not** collapse on deterministic frames: `↓ⁱ`
still moves the point of evaluation to another time, which is precisely the discrimination the
registers were added for. So the "narrow to the deterministic class" escape has no L⋆ analogue.

**(b) The literature obstruction.** The standard completeness route for a language with a
`↓`-style binder is the hybrid one: pure axioms plus the PASTE/BG rules, which yields
completeness for `H(@, ↓)` and its relatives. That machinery is stated for languages containing
**nominals**, and L⋆ has none — the registers store *times*, and there is no formula that names
one. The route is therefore unavailable rather than merely unattempted. The nearest results in
the surrounding literature are the standard hybrid-logic completeness and undecidability
treatments (Blackburn, de Rijke and Venema, *Modal Logic*, §7.3; Goranko 1996 on hierarchies of
modal and temporal logics with reference pointers; the *Stanford Encyclopedia of Philosophy*
entry on Temporal Logic, §7.1 on hybrid logic), together with Reynolds (2003) on until/since
completeness over the reals and Zanardo (1991) on branching-time logics under an Ockhamist
reading. None of them settles this system: the first family needs nominals, and the last two are
about the register-free base.

A further caution from the same literature: adding a `↓`-binder to a temporal logic frequently
costs decidability outright. Nothing here claims TM⋆ is decidable, and TM⁺ decidability is itself
open.

## Related Documentation

- [`../Plus/README.md`](../Plus/README.md) — TM⁺, the system TM⋆ extends, and the open-problem
  record the conditional row points at
- [`../../../StarLanguage/README.md`](../../../StarLanguage/README.md) — the language L⋆, the
  proof system's declarations, and the paper-label correspondence table
- [`../README.md`](../README.md) — the conservativity directory as a whole
