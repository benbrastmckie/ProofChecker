/-
Probe: restate determinism in the tree's own `Fib`-subsingleton idiom, and check that
`translationFrame` supplies F¹ for free — including the reducibility trap.
-/
import FormalSystem.Semantics.Frames.Standard
import Mathlib.Data.Real.Basic
import FormalSystem.Semantics.StarTruth
import FormalSystem.Semantics.StarValidity

namespace Probe536C

open FormalSystem.Semantics
open FormalSystem.StarLanguage

/-- The tree's own idiom: every fibre of the two-sided task relation is a subsingleton.
`d` ranges over ALL of `F.Duration`, which is the bidirectional reading. -/
def TaskFrame.Deterministic (F : TaskFrame) : Prop :=
  ∀ (w : F.WorldState) (d : F.Duration), (TaskFrame.Fib F.TaskRel w d).Subsingleton

/-- The `Fib` form and the pointwise form agree. -/
theorem deterministic_iff (F : TaskFrame) :
    TaskFrame.Deterministic F ↔
      ∀ (w u v : F.WorldState) (x : F.Duration), F.TaskRel w x u → F.TaskRel w x v → u = v :=
  ⟨fun h w _ _ x hu hv => h w x hu hv, fun h w x _ hu _ hv => h w _ _ x hu hv⟩

/-- Free consequence, via the tree's existing Helper D: a deterministic relation saturates. -/
theorem saturation_of_deterministic {D : TemporalOrder} (F : FrameOver D)
    (h : ∀ w d, (TaskFrame.Fib F.TaskRel w d).Subsingleton) :
    TaskFrame.Saturation F.TaskRel :=
  TaskFrame.saturation_of_fib_subsingleton h

/-! ## The bridge lemma, restated against the `Fib` form -/

variable {F : TaskFrame}

theorem states_eq_of_deterministic (hD : TaskFrame.Deterministic F)
    {τ σ : WorldHistory F} (hτ : τ.IsTotal) (hσ : σ.IsTotal) {t : F.Duration}
    (h : SameStateAt τ σ t) (s : F.Duration) :
    τ.states s (hτ s) = σ.states s (hσ s) := by
  have hτr := τ.respects_task t s (hτ t) (hτ s)
  have hσr := σ.respects_task t s (hσ t) (hσ s)
  rw [h (hτ t) (hσ t)] at hτr
  exact hD (σ.states t (hσ t)) (s - t) hτr hσr

theorem stab_iff_of_deterministic (hD : TaskFrame.Deterministic F) (M : TaskModel F)
    {τ : WorldHistory F} (hτ : τ.IsTotal) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (.stab φ) ↔ StarTruthAt M τ t φ := by
  constructor
  · intro h; exact of_stab M τ hτ t φ h
  · intro h σ hσ hsame
    refine (truth_congr_ext M φ τ σ t (fun s => by simp [hτ s, hσ s]) ?_).mp h
    intro s _ _
    exact states_eq_of_deterministic hD hτ hσ hsame s

theorem determined_of_deterministic (hD : TaskFrame.Deterministic F) (φ : StarFormula) :
    F.StarValidOn (.imp φ (.stab φ)) :=
  fun M τ t h => (stab_iff_of_deterministic hD M τ.prop t φ).mpr h

/-! ## F¹ from `translationFrame` — three lines, no new axiom obligations -/

@[reducible] noncomputable def rOrd : TemporalOrder := ⟨ℝ⟩

noncomputable def F1 : FrameOver rOrd := translationFrame rOrd

-- REDUCIBILITY TRAP (reproduced): `translationFrame` is a plain `def`, not `@[reducible]`, so
-- `F1.WorldState` does NOT reduce to `ℝ` at synthesis transparency. This FAILS:
--   example (w x u : ℝ) : F1.TaskRel w x u ↔ u = w + x := Iff.rfl
-- with "w has type ℝ but is expected to have type F1.WorldState" and
-- "failed to synthesize HAdd ℝ ℝ ?m".
-- WORKING WORKAROUND: type the variables at the temporal order's coercion, not at `ℝ`.
-- `rOrd` is `@[reducible]`, so `↑rOrd` does reduce.
example (w x u : ↑rOrd) : F1.TaskRel w x u ↔ u = w + x := Iff.rfl

-- SECOND TRAP INSTANCE — and this one the `↑rOrd` workaround does NOT fix. The history
-- characterization ("total histories are exactly the translations") FAILS:
--   example (τ : WorldHistory F1.toTaskFrame) (hτ : τ.IsTotal) (r : ↑rOrd) :
--       τ.states r (hτ r) = τ.states 0 (hτ 0) + r := by
--     have h := τ.respects_task 0 r (hτ 0) (hτ r); simpa using h
-- with "failed to synthesize HAdd F1.toTaskFrame.WorldState rOrd.carrier ?m", because
-- `τ.states` returns `F1.toTaskFrame.WorldState`, which does not reduce. The barrier is inside
-- `translationFrame` (a plain `def`), so neither a type ascription nor a `@[reducible]` alias
-- reaches it. Route (i) — build F¹ through `ShiftSet` instead, whose `fibre`/`frame` ARE
-- `@[reducible]` — is therefore the recommendation, and it also hands over `total_eq_orbit`,
-- which IS this characterization, already proved generically.

theorem f1_deterministic : TaskFrame.Deterministic F1.toTaskFrame :=
  fun w d => translationRel_fib_subsingleton (D := rOrd) w d

/-- Deliverable (a) instantiated at F¹, with no bespoke frame construction. -/
theorem f1_determined (φ : StarFormula) :
    F1.toTaskFrame.StarValidOn (.imp φ (.stab φ)) :=
  determined_of_deterministic f1_deterministic φ

end Probe536C
