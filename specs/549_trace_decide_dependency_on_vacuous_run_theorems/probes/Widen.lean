import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound
namespace FormalSystem.Metalogic.Decidability
open FormalSystem.ProofSystem

-- the un-`At` figure is positive too, by the same route
theorem one_le_mintAwareFuel' (Ucard Tmax mintBudget D β : Nat) :
    1 ≤ mintAwareFuel Ucard Tmax mintBudget D β :=
  fuelFigure_pos (by simp only [mintPathBound]; omega)

-- hence PostBlockingSettlesRun is false at the un-`At` figure as well, at .Base
theorem postBlockingSettlesRun_mintAwareFuel_false
    (U : Finset SignedFormula) (Tmax mintBudget D β : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base
        (mintAwareFuel U.card Tmax mintBudget D β) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.one_le_iff_ne_zero.mp (one_le_mintAwareFuel' U.card Tmax mintBudget D β))
  rw [hn]
  exact postBlockingSettlesRun_false_succ n

end FormalSystem.Metalogic.Decidability
#print axioms FormalSystem.Metalogic.Decidability.postBlockingSettlesRun_mintAwareFuel_false
