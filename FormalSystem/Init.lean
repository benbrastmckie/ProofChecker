/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import Mathlib.Init
import Mathlib.Tactic.Common

/-!
# FormalSystem Initialization

This is the intended root file for `FormalSystem`, modeled on CSLib's `Cslib/Init.lean` (in turn
modeled on `Mathlib.Init`): a file every module in the library is meant to import, carrying the
linters and common tactics that should be active by default throughout. Unlike CSLib, this repo
has no local lint/tactic-attribute module to pin alongside `Mathlib.Init`, so this file imports
only the two Mathlib roots.

`scripts/CheckInitImports.lean` reports which `FormalSystem` modules do not (yet) transitively
import this file; see that script and G-08 in the task that introduced it. Rewriting the tree so
every module actually imports `FormalSystem.Init` is an explicit follow-up, not done here.
-/
