/-
Probes for the deterministic collapse of the stability modal.
Research-only file; not part of the FormalSystem library.
-/
import FormalSystem.Semantics.StarTruth
import FormalSystem.Semantics.StarValidity

namespace Probe536

open FormalSystem.Syntax
open FormalSystem.Semantics
open FormalSystem.StarLanguage
open FormalSystem.StarLanguage.StarFormula

/-! ## A1: the two-sided determinism predicate -/

/-- `def:deterministic`: every fibre of the (two-sided) task relation is a subsingleton. -/
def TaskFrame.IsDeterministic (F : TaskFrame) : Prop :=
  ∀ (w u v : F.WorldState) (x : F.Duration), F.TaskRel w x u → F.TaskRel w x v → u = v

variable {F : TaskFrame}

/-! ## A2: the singleton bridge — `⟨τ⟩_x = {τ}` on a deterministic frame -/

/-- On a deterministic frame two total histories agreeing at one time agree everywhere. -/
theorem states_eq_of_deterministic (hD : TaskFrame.IsDeterministic F)
    {τ σ : WorldHistory F} (hτ : τ.IsTotal) (hσ : σ.IsTotal) {t : F.Duration}
    (h : SameStateAt τ σ t) (s : F.Duration) :
    τ.states s (hτ s) = σ.states s (hσ s) := by
  have hτr := τ.respects_task t s (hτ t) (hτ s)
  have hσr := σ.respects_task t s (hσ t) (hσ s)
  rw [h (hτ t) (hσ t)] at hτr
  exact hD (σ.states t (hσ t)) _ _ (s - t) hτr hσr

/-! ## A3: the collapse `⊡φ ↔ φ` -/

theorem stab_iff_of_deterministic (hD : TaskFrame.IsDeterministic F) (M : TaskModel F)
    {τ : WorldHistory F} (hτ : τ.IsTotal) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (.stab φ) ↔ StarTruthAt M τ t φ := by
  constructor
  · intro h; exact of_stab M τ hτ t φ h
  · intro h σ hσ hsame
    refine (truth_congr_ext M φ τ σ t (fun s => by simp [hτ s, hσ s]) ?_).mp h
    intro s _ _
    exact states_eq_of_deterministic hD hτ hσ hsame s

/-! ## A4: `Determined` and the biconditional, as frame validities -/

theorem determined_starValidOn_of_deterministic (hD : TaskFrame.IsDeterministic F)
    (φ : StarFormula) : F.StarValidOn (.imp φ (.stab φ)) := by
  intro M τ t h
  exact (stab_iff_of_deterministic hD M τ.prop t φ).mpr h

/-- The full collapse: `⊡φ ↔ φ` is valid on every deterministic frame. -/
theorem stab_biconditional_starValidOn_of_deterministic (hD : TaskFrame.IsDeterministic F)
    (φ : StarFormula) :
    F.StarValidOn (.imp (.stab φ) φ) ∧ F.StarValidOn (.imp φ (.stab φ)) :=
  ⟨fun M τ t h => (stab_iff_of_deterministic hD M τ.prop t φ).mp h,
   determined_starValidOn_of_deterministic hD φ⟩

end Probe536
