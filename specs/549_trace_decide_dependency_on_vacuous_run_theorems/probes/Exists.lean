import FormalSystem
open Lean
run_cmd do
  let env ← Lean.getEnv
  for n in [`FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_fixed_run,
            `FormalSystem.Metalogic.Decidability.buildTableauAt_isSome_of_budget_run,
            `FormalSystem.Metalogic.Decidability.decide] do
    logInfo m!"{n} exists under `import FormalSystem`: {(env.find? n).isSome}"
