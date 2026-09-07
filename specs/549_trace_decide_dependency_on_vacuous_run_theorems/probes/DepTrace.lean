import FormalSystem.Metalogic.Decidability

/-! Mechanical dependency trace: does any target constant reach any of the nine `_run`
    theorems in `Verified/Termination/MintBound.lean`?  Environment-level transitive
    constant closure over value + type of every declaration. -/

open Lean

namespace DepTrace

partial def collect (env : Environment) (visited : Std.HashSet Name) (n : Name) :
    Std.HashSet Name :=
  if visited.contains n then visited
  else
    let visited := visited.insert n
    match env.find? n with
    | none => visited
    | some ci =>
      let deps := (ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[])
      deps.foldl (fun acc d => collect env acc d) visited

def targets : List Name :=
  [ `FormalSystem.Metalogic.Decidability.decide
  , `FormalSystem.Metalogic.Decidability.decideAuto
  , `FormalSystem.Metalogic.Decidability.decideBlocking
  , `FormalSystem.Metalogic.Decidability.isValid
  , `FormalSystem.Metalogic.Decidability.isSatisfiable
  , `FormalSystem.Metalogic.Decidability.sound_of_isValid ]

def suspects : List Name :=
  [ `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_of_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_at_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_at_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_selfGuarded_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_selfGuarded_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_fixed_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_fixed_run
  , `FormalSystem.Metalogic.Decidability.PostBlockingSettlesRun
  , `FormalSystem.Metalogic.Decidability.PostBlockingSettles
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_settlesRun ]

end DepTrace

open DepTrace in
run_cmd do
  let env ← Lean.getEnv
  -- existence check first: a typo would silently produce a clean bill of health
  for s in suspects do
    if (env.find? s).isNone then
      logError m!"SUSPECT NOT FOUND IN ENV: {s}"
  for t in targets do
    if (env.find? t).isNone then
      logError m!"TARGET NOT FOUND IN ENV: {t}"
    else
      let cl := collect env {} t
      let hits := suspects.filter (fun s => cl.contains s)
      logInfo m!"{t}: closure = {cl.size} consts; hits = {hits}"
