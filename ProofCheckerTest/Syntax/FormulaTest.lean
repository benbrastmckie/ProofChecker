import ProofChecker.Syntax.Formula

/-!
# Formula Test Suite

Tests for the Formula inductive type and derived operators.

## Test Categories

- Formula construction (atom, bot, imp, box, past, future)
- Decidable equality
- Structural complexity measure
- Derived Boolean operators (neg, and, or)
- Derived modal operators (diamond)
- Derived temporal operators (always, sometimes, sometime_past, sometime_future)
- Temporal duality (swap_past_future)
-/

namespace ProofCheckerTest.Syntax

open ProofChecker.Syntax

-- Test: Formula atom construction
example : Formula.atom "p" = Formula.atom "p" := rfl

-- Test: Formula bot construction
example : Formula.bot = Formula.bot := rfl

-- Test: Formula implication construction
example (p q : Formula) : (Formula.imp p q) = (Formula.imp p q) := rfl

-- Test: Formula box construction
example (p : Formula) : (Formula.box p) = (Formula.box p) := rfl

-- Test: Formula past construction
example (p : Formula) : (Formula.past p) = (Formula.past p) := rfl

-- Test: Formula future construction
example (p : Formula) : (Formula.future p) = (Formula.future p) := rfl

-- Test: Decidable equality - same atoms
example : (Formula.atom "p") = (Formula.atom "p") := rfl

-- Test: Decidable equality - different atoms
example : (Formula.atom "p") ≠ (Formula.atom "q") := by
  intro h
  injection h with h'
  contradiction

-- Test: Decidable equality - bot
example : Formula.bot = Formula.bot := rfl

-- Test: Decidable equality - complex formulas
example :
  (Formula.imp (Formula.atom "p") (Formula.atom "q")) =
  (Formula.imp (Formula.atom "p") (Formula.atom "q")) := rfl

-- Test: Complexity of atom
example : (Formula.atom "p").complexity = 1 := rfl

-- Test: Complexity of bot
example : Formula.bot.complexity = 1 := rfl

-- Test: Complexity of implication
example : ((Formula.atom "p").imp (Formula.atom "q")).complexity = 3 := rfl

-- Test: Complexity of box
example : ((Formula.atom "p").box).complexity = 2 := rfl

-- Test: Complexity of nested formula
example : ((Formula.atom "p").box.imp (Formula.atom "q").box).complexity = 5 := rfl

-- Test: Derived negation operator
example (p : Formula) : p.neg = (p.imp Formula.bot) := rfl

-- Test: Derived conjunction operator
example (p q : Formula) : (p.and q) = ((p.imp q.neg).neg) := rfl

-- Test: Derived disjunction operator
example (p q : Formula) : (p.or q) = (p.neg.imp q) := rfl

-- Test: Derived diamond (possibility) operator
example (p : Formula) : p.diamond = p.neg.box.neg := rfl

-- Test: Derived 'always' temporal operator (future for all times)
example (p : Formula) : p.always = p.future := rfl

-- Test: Derived 'sometimes' temporal operator (∃ future time)
example (p : Formula) : p.sometimes = p.always.neg.neg := rfl

-- Test: Derived 'sometime_past' operator
example (p : Formula) : p.sometime_past = p.past.neg.neg := rfl

-- Test: Derived 'sometime_future' operator
example (p : Formula) : p.sometime_future = p.sometimes := rfl

-- Test: swap_past_future on atom (unchanged)
example : (Formula.atom "p").swap_past_future = Formula.atom "p" := rfl

-- Test: swap_past_future on bot (unchanged)
example : Formula.bot.swap_past_future = Formula.bot := rfl

-- Test: swap_past_future on implication (recursive)
example (p q : Formula) :
  (p.imp q).swap_past_future = (p.swap_past_future.imp q.swap_past_future) := rfl

-- Test: swap_past_future on box (unchanged)
example (p : Formula) : (p.box).swap_past_future = p.swap_past_future.box := rfl

-- Test: swap_past_future on past (becomes future)
example (p : Formula) : (p.past).swap_past_future = p.swap_past_future.future := rfl

-- Test: swap_past_future on future (becomes past)
example (p : Formula) : (p.future).swap_past_future = p.swap_past_future.past := rfl

-- Test: swap_past_future is involution (applying twice gives identity)
example (p : Formula) : p.swap_past_future.swap_past_future = p := by
  induction p with
  | atom _ => rfl
  | bot => rfl
  | imp p q ihp ihq => simp [Formula.swap_past_future, ihp, ihq]
  | box p ih => simp [Formula.swap_past_future, ih]
  | past p ih => simp [Formula.swap_past_future, ih]
  | future p ih => simp [Formula.swap_past_future, ih]

end ProofCheckerTest.Syntax
