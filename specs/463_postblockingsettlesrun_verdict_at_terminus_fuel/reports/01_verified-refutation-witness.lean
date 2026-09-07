import FormalSystem.Metalogic.Decidability.Verified.Termination.MintBound
namespace Probe463
open FormalSystem.Syntax FormalSystem.Metalogic.Decidability FormalSystem.ProofSystem

def p : Formula := .atom (Atom.mkBase "p")
def q : Formula := .atom (Atom.mkBase "q")
def tt : Formula := .imp .bot .bot
def su : Formula := .untl tt tt
def ss : Formula := .snce tt tt
def puq : Formula := .untl p q

-- engine exit for seed (p -> q), times chain 2<0<1<3, blocked [3,2]
def S : Branch :=
  [ SignedFormula.pos tt ⟨0,3⟩
  , SignedFormula.pos su ⟨0,1⟩
  , SignedFormula.pos ss ⟨0,1⟩
  , SignedFormula.pos tt ⟨0,2⟩
  , SignedFormula.neg .bot ⟨0,1⟩
  , SignedFormula.pos tt ⟨0,1⟩
  , SignedFormula.pos su ⟨0,0⟩
  , SignedFormula.pos ss ⟨0,0⟩
  , SignedFormula.pos p ⟨0,0⟩
  , SignedFormula.neg q ⟨0,0⟩
  , SignedFormula.neg (.imp p q) ⟨0,0⟩ ]
def ordS : TimeOrdering := { constraints := [(1,3),(2,0),(0,1)] }

-- augmentation: world 1 machinery at times 0,1,2,3 + the witness at world 9, time 4
def AUG : Branch :=
  [ SignedFormula.neg .bot ⟨0,2⟩, SignedFormula.neg .bot ⟨0,3⟩, SignedFormula.pos puq ⟨1,0⟩, SignedFormula.pos q ⟨1,0⟩
  , SignedFormula.pos su ⟨1,0⟩, SignedFormula.pos ss ⟨1,0⟩
  , SignedFormula.pos q ⟨1,1⟩, SignedFormula.pos tt ⟨1,1⟩
  , SignedFormula.pos su ⟨1,1⟩, SignedFormula.pos ss ⟨1,1⟩
  , SignedFormula.pos tt ⟨1,2⟩, SignedFormula.neg .bot ⟨1,2⟩, SignedFormula.pos tt ⟨1,3⟩, SignedFormula.neg .bot ⟨1,3⟩
  , SignedFormula.pos tt ⟨1,0⟩, SignedFormula.neg .bot ⟨1,0⟩, SignedFormula.neg .bot ⟨1,1⟩
  , SignedFormula.pos puq ⟨9,4⟩ ]

def W : Branch := AUG ++ S
def ordW : TimeOrdering := { constraints := [(3,4),(1,3),(2,0),(0,1)] }
def trBad : EventualityTracker := { pending := [ { formula := q, label := ⟨7,0⟩, isUntil := true } ] }
def trW := fulfillEventualities W (registerEventualities W trBad)


open FormalSystem.Metalogic.Decidability in
theorem findClosure_W (fc : FrameClass) : findClosure W fc = none := by cases fc <;> rfl

theorem expandOnceUnblocked_W_sat :
    (expandOnceUnblocked W ordW FrameClass.Base trW).1 = ExpansionResult.saturated := by rfl

theorem expandOnceNoFresh_W_sat :
    expandOnceNoFresh W ordW FrameClass.Base = (ExpansionResult.saturated, ordW) := by rfl

theorem ebwf_W (n : Nat) :
    expandBranchWithFuel W (n+1) ordW FrameClass.Base trBad {} 100 0
      = some (.inr (W, ordW, {})) := by
  rw [expandBranchWithFuel]
  norm_num
  rfl

theorem settle_W_fails :
    findUnexpandedUnblockedWith W ordW FrameClass.Base
        (blockedTimes W ordW FrameClass.Base (armTracker W))
      = some (SignedFormula.pos puq ⟨9,4⟩) := by rfl

theorem postBlockingSettlesRun_false_Base (n : Nat) :
    ¬ PostBlockingSettlesRun FrameClass.Base (n+1) := by
  intro h
  have hsb : saturateBlocked W (n+1) ordW FrameClass.Base = some (.inr (W, ordW)) :=
    saturateBlocked_eq_self_of_noFresh_saturated (findClosure_W _) expandOnceNoFresh_W_sat _
  have := h W W ordW ordW trBad {} {} 100 0 W ordW (ebwf_W n) hsb
  rw [settle_W_fails] at this
  exact absurd this (by simp)

end Probe463

namespace Probe463
#print axioms postBlockingSettlesRun_false_Base
end Probe463
