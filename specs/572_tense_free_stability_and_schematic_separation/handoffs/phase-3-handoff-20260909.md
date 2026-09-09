# Phase 1-3 handoff (task 572)

## Immediate next action

Phase 4: retire `fn_sentDet_atom` in
`FormalSystem/Metalogic/Independence/ForwardDeterministicFrame.lean`, replacing it with
`fn_sentDet_stateLocal`, strengthening `fn_separates`, and adding `fn_sentDet_bounds`.

## State

`FormalSystem/Semantics/StarStateLocal.lean` exists and builds green (zero sorry). It carries:

- `StarFormula.StateLocal` (namespace `FormalSystem.StarLanguage`) — the nine-clause syntactic
  fragment, with `@[simp]` clause lemmas and the `neg`/`and`/`or` closure lemmas
- `IsStateLocal` (namespace `FormalSystem.Semantics`) — the semantic property
- `isStateLocal_box`, `isStateLocal_stab` — both proved for an **arbitrary** argument
- `isStateLocal_of_stateLocal` — the soundness induction, all nine cases
- `not_isStateLocal_someFuture`, `not_isStateLocal_somePast`, `not_isStateLocal_timeRecall` —
  the three exclusion witnesses, all on `NF`/`natModel`
- `stateLocal_stab_iff`, `stateLocal_starValid_iff_stab` — the headline `φ ↔ ⊡φ`

`FormalSystem/Semantics.lean` gained the `import` line (after `StarNonValidities`).

## Gate verdict

Phase 1's gate PASSED, unconditionally: no rung of the fallback ladder was needed. The open
question the task posed about `box` is settled positively and more strongly than anticipated —
`□φ` is state-local for arbitrary `φ`, by `Iff.rfl`.

## Measured axiom sets

| Declaration | `#print axioms` |
|---|---|
| `StarFormula.StateLocal` | (none) |
| `isStateLocal_box`, `isStateLocal_stab`, `isStateLocal_of_stateLocal`, `stateLocal_stab_iff` | `[propext]` |
| `not_isStateLocal_someFuture`, `not_isStateLocal_somePast`, `not_isStateLocal_timeRecall`, `stateLocal_starValid_iff_stab` | `[propext, Classical.choice, Quot.sound]` |

## Deviations so far

- `StarFormula.StateLocal` declared in `FormalSystem.StarLanguage`, not `FormalSystem.Semantics`
  (dot-notation resolution; see the plan's inline annotation)
- `stateLocal_starValid_iff_stab` uses `StarValid.of_forall_total`, not
  `TaskFrame.StarValidOn.of_forall_total`
- Phases 1-3 landed in one commit: all three phases edit the single new file and were verified
  together by one `lake env lean` run
