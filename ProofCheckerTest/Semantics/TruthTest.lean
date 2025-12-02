import ProofChecker.Semantics.Truth
import ProofChecker.Semantics.TaskFrame

/-!
# Truth Evaluation Tests

Tests for truth evaluation in task models.
-/

namespace ProofCheckerTest.Semantics

open ProofChecker.Syntax
open ProofChecker.Semantics

-- Helper: use trivial frame for testing
def testFrame : TaskFrame := TaskFrame.trivialFrame

-- Helper: simple model where "p" is true, "q" is false
def testModel : TaskModel testFrame where
  valuation := fun _ p => p = "p"

-- Helper: trivial world history
def testHistory : WorldHistory testFrame := WorldHistory.trivial

-- Test: Bot is false (using trivial history's domain proof)
example : ¬(truth_at testModel testHistory 0 trivial Formula.bot) := by
  exact Truth.bot_false

-- Test: Atom truth depends on valuation (p is true)
example : (truth_at testModel testHistory 0 trivial (Formula.atom "p")) := by
  unfold truth_at testModel testHistory WorldHistory.trivial
  simp

-- Test: Atom truth depends on valuation (q is false)
example : ¬(truth_at testModel testHistory 0 trivial (Formula.atom "q")) := by
  unfold truth_at testModel testHistory WorldHistory.trivial
  simp

-- Test: Implication basic behavior
-- p → p is true
example : (truth_at testModel testHistory 0 trivial ((Formula.atom "p").imp (Formula.atom "p"))) := by
  intro h
  exact h

-- Test: Truth of negation (¬⊥ = ⊤)
example : (truth_at testModel testHistory 0 trivial Formula.bot.neg) := by
  unfold Formula.neg truth_at
  intro h
  exact h

end ProofCheckerTest.Semantics
