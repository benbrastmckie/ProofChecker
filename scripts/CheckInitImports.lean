/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Lean
import Mathlib.Lean.CoreM
import Batteries.Data.List.Basic
import ImportGraph

open Lean Core Elab Command

/-!
# Check Init Imports

Near-verbatim port of CSLib's `scripts/CheckInitImports.lean` (`Cslib` -> `FormalSystem`, and a
one-entry exceptions list rather than CSLib's two, since this repo has no local lint/tactic-
attribute module analogous to `Cslib.Foundations.Lint.Basic` needing its own circular-dependency
exception -- `FormalSystem.Init`'s own two imports, `Mathlib.Init` and `Mathlib.Tactic.Common`,
are rooted at `Mathlib`, not `FormalSystem`, so the `name.getRoot = `FormalSystem`` filter below
already excludes them without needing an explicit exception).

This script checks that all `FormalSystem` modules (transitively) import `FormalSystem.Init`.
Reporting-only: not wired into `check-module-invariants.sh`, and the ~430-file import rewrite
that would make this check clean is an explicit follow-up, not this task's Non-Goal-excluded
scope. Run with `lake exe checkInitImports`.
-/

/-- Modules with technical constraints preventing a `FormalSystem.Init` import. -/
def exceptions : List Name := [
  -- `FormalSystem.Init` does not (and cannot) import itself.
  `FormalSystem.Init,
]

def main : IO UInt32 := do
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  CoreM.withImportModules #[`FormalSystem] (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    let graph := env.importGraph.transitiveClosure
    let noInitGraph :=
      graph.filter (fun name imports => name.getRoot = `FormalSystem ∧ !imports.contains `FormalSystem.Init)
    let diff := noInitGraph.keys.diff exceptions
    if diff.length > 0 then
      IO.eprintln s!"error: {diff.length} module(s) do not (transitively) import `FormalSystem.Init`:"
      for name in diff do
        IO.eprintln s!"  {name}"
    return diff.length.toUInt32
