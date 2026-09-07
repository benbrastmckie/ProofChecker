import FormalSystem
open Lean
namespace RevDep
def suspects : List Name :=
  [ `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_of_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_at_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_at_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_selfGuarded_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_selfGuarded_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_fixed_run
  , `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_at_seed_fixed_run ]
end RevDep

open RevDep in
run_cmd do
  let env ← Lean.getEnv
  let sset := suspects.foldl (fun (s : Std.HashSet Name) n => s.insert n) {}
  let mut hits : Array (Name × Name) := #[]
  for (n, ci) in env.constants.toList do
    if sset.contains n then continue
    if n.isInternal then continue
    let deps := (ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[])
    for d in deps do
      if sset.contains d then hits := hits.push (n, d)
  logInfo m!"direct reverse-dependents across the whole FormalSystem env: {hits.size}"
  for h in hits do logInfo m!"  {h.1}  ->  {h.2}"
