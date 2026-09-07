/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.Star.AxiomValidity
import FormalSystem.StarLanguage

/-!
# Soundness of TM⋆ at every frame class

`TM⋆ ⊢[fc] φ ⟹ StarValidIn fc φ`, for every `fc`, by the same companion recursion the L⁺
soundness theorem uses (`Metalogic/Soundness.lean`, `derivable_valid_and_swap_validIn`):
the recursion carries **both** `StarValidIn fc φ` and `StarValidIn fc φ.swapTemporal`, so that
the `temporal_duality` case simply exchanges the two components. The `axiom` case feeds in the
two dispatch lemmas of `Conservativity/Star/AxiomValidity.lean`; everything else is the clause
structure of `StarTruthAt`.

**TD is discharged semantically, never proof-theoretically.** Mapping derivations to mirrored
derivations would require the axiom set to be mirror-closed, which TM⁺'s is not (BX lists the
future halves and obtains the past halves by TD); the companion recursion needs only
per-schema swap-validity, which `starAxiom_swap_validIn_min` supplies for every constructor.

## Main Results

- `star_derivable_valid_and_swap_validIn` — the companion recursion
- `star_soundness_validIn` — `StarDerivable fc [] φ → StarValidIn fc φ`
- `star_soundness_in` — the context form, by induction on the derivation
- `star_soundness_base/dense/discrete/dedekind`, `star_soundness_valid` — the per-class rows

## References

* `FormalSystem/Metalogic/Soundness.lean` — `derivable_valid_and_swap_validIn`, `soundness_in`,
  the theorems mirrored arm for arm
-/

namespace FormalSystem.Metalogic.Conservativity

open FormalSystem.Syntax
open FormalSystem.ProofSystem
open FormalSystem.StarLanguage
open FormalSystem.StarLanguage.StarFormula
open FormalSystem.Semantics
open FormalSystem.Metalogic

/-- **The companion recursion.** A TM⋆ theorem at `fc` is `StarValidIn fc`, and so is its
temporal dual. Mirror of `derivable_valid_and_swap_validIn`, arm for arm; well-founded on the
derivation's height because the `weakening` case re-targets to the empty context without a
structural descent. -/
theorem star_derivable_valid_and_swap_validIn {fc : FrameClass} {φ : StarFormula}
    (d : StarDerivationTree fc [] φ) : StarValidIn fc φ ∧ StarValidIn fc φ.swapTemporal := by
  match d with
  | .axiom _ _ h_ax h_fc =>
    exact ⟨starAxiom_validIn h_ax h_fc, starAxiom_swap_validIn h_ax h_fc⟩
  | .assumption _ _ h_mem =>
    exact absurd h_mem List.not_mem_nil
  | .modus_ponens _ psi' _ d1 d2 =>
    have h1 := star_derivable_valid_and_swap_validIn d1
    have h2 := star_derivable_valid_and_swap_validIn d2
    constructor
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ hτ t
      exact (h1.1.apply_total F hF M τ hτ t) (h2.1.apply_total F hF M τ hτ t)
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ hτ t
      exact (h1.2.apply_total F hF M τ hτ t) (h2.2.apply_total F hF M τ hτ t)
  | .necessitation psi' d' =>
    have h := star_derivable_valid_and_swap_validIn d'
    constructor
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ _ t σ hσ
      exact h.1.apply_total F hF M σ hσ t
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ _ t σ hσ
      exact h.2.apply_total F hF M σ hσ t
  | .temporal_necessitation psi' d' =>
    have h := star_derivable_valid_and_swap_validIn d'
    constructor
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ hτ t
      rw [StarTruth.allFuture_iff]
      intro s _
      exact h.1.apply_total F hF M τ hτ s
    · refine StarValidIn.of_forall_total ?_
      intro F hF M τ hτ t
      rw [swap_temporal_all_future, StarTruth.allPast_iff]
      intro s _
      exact h.2.apply_total F hF M τ hτ s
  | .temporal_duality psi' d' =>
    have h := star_derivable_valid_and_swap_validIn d'
    refine ⟨h.2, ?_⟩
    rw [swap_temporal_involution]
    exact h.1
  | .weakening Gamma' _ _ d' h_sub =>
    have h_term := StarDerivationTree.height_ofWeakeningNil_lt d' h_sub
    exact star_derivable_valid_and_swap_validIn (d'.ofWeakeningNil h_sub)
termination_by d.height
decreasing_by
  all_goals first
    | exact StarDerivationTree.mp_height_gt_left _ _
    | exact StarDerivationTree.mp_height_gt_right _ _
    | omega
    | simp only [StarDerivationTree.height]; omega

/-- **Soundness of TM⋆ at `fc`**, empty-context validity form.

Paper: — (formalization-native; the stability extension L-star is not in the paper)
-/
theorem star_soundness_validIn {fc : FrameClass} {φ : StarFormula}
    (h : StarDerivable fc [] φ) : StarValidIn fc φ :=
  h.elim fun d => (star_derivable_valid_and_swap_validIn d).1

/-- **Soundness of TM⋆ at `fc`**, context form: a derivation of `φ` from `Γ` makes `φ` true at
every model over a frame satisfying `fc`, every total history and every time at which all of `Γ`
is true. Mirror of `soundness_in`; the `temporal_duality` case defers to the companion
recursion. -/
theorem star_soundness_in {fc : FrameClass} (Γ : StarContext) (φ : StarFormula)
    (d : StarDerivationTree fc Γ φ)
    (F : TaskFrame) (hF : fc.Sat F) (M : TaskModel F)
    (τ : WorldHistory F) (h_mem : τ.IsTotal) (t : F.Duration)
    (h_ctx : ∀ ψ ∈ Γ, StarTruthAt M τ t ψ) :
    StarTruthAt M τ t φ := by
  induction d generalizing τ t with
  | «axiom» Γ' φ' h_ax h_fc =>
    exact (starAxiom_validIn h_ax h_fc).apply_total F hF M τ h_mem t
  | assumption Γ' φ' h_in => exact h_ctx φ' h_in
  | modus_ponens Γ' φ' ψ' _ _ ih1 ih2 =>
    exact (ih1 τ h_mem t h_ctx) (ih2 τ h_mem t h_ctx)
  | necessitation φ' _ ih =>
    intro σ h_σ_mem
    exact ih σ h_σ_mem t (by simp)
  | temporal_necessitation φ' _ ih =>
    rw [StarTruth.allFuture_iff]
    intro s _
    exact ih τ h_mem s (by simp)
  | temporal_duality φ' d' _ih =>
    exact ((star_derivable_valid_and_swap_validIn d').2).apply_total F hF M τ h_mem t
  | weakening Γ' Δ' φ' _ h_sub ih =>
    exact ih τ h_mem t (fun ψ h_in => h_ctx ψ (h_sub h_in))

/-! ## The four rows -/

/-- Soundness of TM⋆ at `.Base`: a TM⋆ theorem is `StarValid`. -/
theorem star_soundness_valid {φ : StarFormula} (h : StarDerivable FrameClass.Base [] φ) :
    StarValid φ :=
  star_soundness_validIn h

/-- Soundness of TM⋆ at `.Base` (context form). -/
theorem star_soundness_base (Γ : StarContext) (φ : StarFormula)
    (d : StarDerivationTree FrameClass.Base Γ φ) (F : TaskFrame) (M : TaskModel F)
    (τ : WorldHistory F) (h_mem : τ.IsTotal) (t : F.Duration)
    (h_ctx : ∀ ψ ∈ Γ, StarTruthAt M τ t ψ) : StarTruthAt M τ t φ :=
  star_soundness_in Γ φ d F trivial M τ h_mem t h_ctx

/-- Soundness of TM⋆ at `.Dense`. -/
theorem star_soundness_dense {φ : StarFormula} (h : StarDerivable FrameClass.Dense [] φ) :
    StarValidDense φ :=
  star_soundness_validIn h

/-- Soundness of TM⋆ at `.ZTime`. -/
theorem star_soundness_ztime {φ : StarFormula}
    (h : StarDerivable FrameClass.ZTime [] φ) : StarValidZTime φ :=
  star_soundness_validIn h

/-- Soundness of TM⋆ at `.RTime`. -/
theorem star_soundness_rtime {φ : StarFormula}
    (h : StarDerivable FrameClass.RTime [] φ) : StarValidRTime φ :=
  star_soundness_validIn h

/-! ## Acceptance checks -/

/-- The derived `⊡`-necessitation rule is sound: its conclusion is valid whenever its premise
is derivable. -/
example {fc : FrameClass} {φ : StarFormula} (d : ⊢⋆[fc] φ) :
    StarValidIn fc (StarFormula.stab φ) :=
  star_soundness_validIn ⟨stabNecessitation d⟩

/-- **TM⋆ is consistent at `.Base`**: `⊥` is not a theorem. (Consistency at the wider classes is
not a corollary, since derivability lifts upward; each would need its own witness frame.) Witness: the trivial frame over `ℤ` with the all-false valuation, mirroring
`bl_not_derivable_nil_bot_ztime`. -/
theorem star_not_derivable_nil_bot :
    ¬ StarDerivable FrameClass.Base [] StarFormula.bot := by
  intro h
  obtain ⟨τ⟩ := TaskFrame.hF_nonempty_of_frameAxioms (FrameOver.trivialFrame (D := ℤ))
  exact (star_soundness_validIn h).apply_total (FrameOver.trivialFrame (D := ℤ)) trivial
    TaskModel.allFalse τ.val τ.property 0

end FormalSystem.Metalogic.Conservativity
