import FormalSystem.Metalogic.Decidability

open Lean
namespace DepTrace2

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

end DepTrace2

open DepTrace2 in
run_cmd do
  let env ← Lean.getEnv
  let cl := collect env {} `FormalSystem.Metalogic.Decidability.decide
  -- which engine functions does `decide` actually reach?
  let engine : List Name :=
    [ `FormalSystem.Metalogic.Decidability.buildTableauAt
    , `FormalSystem.Metalogic.Decidability.buildTableau
    , `FormalSystem.Metalogic.Decidability.expandBranchWithFuel
    , `FormalSystem.Metalogic.Decidability.saturateBlocked
    , `FormalSystem.Metalogic.Decidability.mintAwareFuelAt
    , `FormalSystem.Metalogic.Decidability.mintAwareFuel ]
  for e in engine do
    logInfo m!"decide reaches {e}? {cl.contains e}  (exists: {(env.find? e).isSome})"
  -- how many MintBound-module constants does decide reach at all?
  let mb := env.header.moduleNames.findIdx?
    (· == `FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound)
  match mb with
  | none => logInfo "MintBound module not in header"
  | some i =>
    let inMB := cl.toList.filter (fun n =>
      match env.getModuleIdxFor? n with
      | some j => j.toNat == i
      | none => false)
    logInfo m!"constants from MintBound reached by decide: {inMB.length}"
    let dp := env.header.moduleNames.findIdx?
      (· == `FormalSystem.Metalogic.Decidability.DecisionProcedure)
    logInfo m!"DecisionProcedure module idx: {dp}, MintBound idx: {i}"
