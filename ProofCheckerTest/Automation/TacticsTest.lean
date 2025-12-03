import ProofChecker.Automation.Tactics
import ProofChecker.ProofSystem

/-!
# Tests for Automation Tactics

This module contains tests for the custom tactics defined in
`ProofChecker.Automation.Tactics`.

## Test Coverage

**Phase 7**: Tests for implemented tactics (apply_axiom, modal_t, assumption_search, tm_auto).

## Test Organization

- **Phase 4 Tests**: apply_axiom and modal_t
- **Phase 5 Tests**: tm_auto (native implementation)
- **Phase 6 Tests**: assumption_search
- **Integration Tests**: Tactic combinations

## References

* Tactics Module: ProofChecker/Automation/Tactics.lean
-/

namespace ProofCheckerTest.Automation

open ProofChecker.Syntax ProofChecker.ProofSystem ProofChecker.Automation

/-!
## Phase 4: apply_axiom and modal_t Tests

Tests for basic axiom application tactics.
-/

/-- Test 1: prop_s axiom via Derivable.axiom -/
example : Derivable [] (Formula.imp (Formula.atom "p") (Formula.imp (Formula.atom "q") (Formula.atom "p"))) :=
  Derivable.axiom [] _ (Axiom.prop_s _ _)

/-- Test 2: prop_k axiom for distribution -/
example : Derivable [] (Formula.imp
  (Formula.imp (Formula.atom "p") (Formula.imp (Formula.atom "q") (Formula.atom "r")))
  (Formula.imp (Formula.imp (Formula.atom "p") (Formula.atom "q")) (Formula.imp (Formula.atom "p") (Formula.atom "r")))) :=
  Derivable.axiom [] _ (Axiom.prop_k _ _ _)

/-- Test 3: modal_t axiom (□p → p) -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.atom "p")) :=
  Derivable.axiom [] _ (Axiom.modal_t _)

/-- Test 4: modal_4 axiom (□p → □□p) -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.box (Formula.box (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.modal_4 _)

/-- Test 5: modal_b axiom (p → □◇p) -/
example : Derivable [] (Formula.imp (Formula.atom "p") (Formula.box (Formula.diamond (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.modal_b _)

/-- Test 6: temp_4 axiom (Fp → FFp) -/
example : Derivable [] (Formula.imp (Formula.future (Formula.atom "p")) (Formula.future (Formula.future (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.temp_4 _)

/-- Test 7: temp_a axiom (p → FPp) -/
example : Derivable [] (Formula.imp (Formula.atom "p") (Formula.future (Formula.sometime_past (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.temp_a _)

/-- Test 8: temp_l axiom (always p → Fp) -/
example : Derivable [] (Formula.imp (Formula.sometime_past (Formula.atom "p")) (Formula.future (Formula.atom "p"))) :=
  Derivable.axiom [] _ (Axiom.temp_l _)

/-- Test 9: modal_future axiom (□p → F□p) -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.future (Formula.box (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.modal_future _)

/-- Test 10: temp_future axiom (Fp → □Fp) -/
example : Derivable [] (Formula.imp (Formula.future (Formula.atom "p")) (Formula.box (Formula.future (Formula.atom "p")))) :=
  Derivable.axiom [] _ (Axiom.temp_future _)

/-- Test 11: apply_axiom tactic unifies with modal_t -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "q")) (Formula.atom "q")) := by
  apply_axiom

/-- Test 12: modal_t tactic (convenience wrapper) -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "r")) (Formula.atom "r")) := by
  modal_t

/-!
## Phase 5: tm_auto Tests

Tests for native TM automation (no Aesop dependency).
-/

/-- Test 13: tm_auto finds modal_t axiom -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.atom "p")) := by
  tm_auto

/-- Test 14: tm_auto finds modal_4 axiom -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.box (Formula.box (Formula.atom "p")))) := by
  tm_auto

/-- Test 15: tm_auto finds temp_4 axiom -/
example : Derivable [] (Formula.imp (Formula.future (Formula.atom "p")) (Formula.future (Formula.future (Formula.atom "p")))) := by
  tm_auto

/-- Test 16: tm_auto finds temp_a axiom -/
example : Derivable [] (Formula.imp (Formula.atom "p") (Formula.future (Formula.sometime_past (Formula.atom "p")))) := by
  tm_auto

/-- Test 17: tm_auto finds modal_future axiom -/
example : Derivable [] (Formula.imp (Formula.box (Formula.atom "p")) (Formula.future (Formula.box (Formula.atom "p")))) := by
  tm_auto

/-- Test 18: tm_auto finds temp_future axiom -/
example : Derivable [] (Formula.imp (Formula.future (Formula.atom "p")) (Formula.box (Formula.future (Formula.atom "p")))) := by
  tm_auto

/-!
## Phase 6: assumption_search Tests

Tests for context-based assumption finding.
-/

/-- Test 19: assumption_search finds exact match (Nat) -/
example (h : Nat) : Nat := by
  assumption_search

/-- Test 20: assumption_search with propositional type -/
example (h1 : Formula.atom "p" = Formula.atom "p") : Formula.atom "p" = Formula.atom "p" := by
  assumption_search

/-- Test 21: assumption_search with implication -/
example (h : Formula.imp (Formula.atom "p") (Formula.atom "q") = Formula.imp (Formula.atom "p") (Formula.atom "q")) :
    Formula.imp (Formula.atom "p") (Formula.atom "q") = Formula.imp (Formula.atom "p") (Formula.atom "q") := by
  assumption_search

/-- Test 22: assumption_search with multiple assumptions -/
example (h1 : String) (h2 : Nat) (h3 : Bool) : Bool := by
  assumption_search

/-- Test 23: assumption_search with formulas -/
example (h : Formula) : Formula := by
  assumption_search

/-!
## Helper Function Tests

Tests for formula pattern matching utilities.
-/

/-- Test 24: is_box_formula recognizes box formulas -/
example : is_box_formula (Formula.box (Formula.atom "p")) = true := rfl

/-- Test 25: is_box_formula rejects non-box formulas -/
example : is_box_formula (Formula.atom "p") = false := rfl

/-- Test 26: is_future_formula recognizes future formulas -/
example : is_future_formula (Formula.future (Formula.atom "p")) = true := rfl

/-- Test 27: is_future_formula rejects non-future formulas -/
example : is_future_formula (Formula.atom "p") = false := rfl

/-- Test 28: extract_from_box extracts inner formula -/
example : extract_from_box (Formula.box (Formula.atom "p")) = some (Formula.atom "p") := rfl

/-- Test 29: extract_from_box returns none for non-box -/
example : extract_from_box (Formula.atom "p") = none := rfl

/-- Test 30: extract_from_future extracts inner formula -/
example : extract_from_future (Formula.future (Formula.atom "p")) = some (Formula.atom "p") := rfl

/-- Test 31: extract_from_future returns none for non-future -/
example : extract_from_future (Formula.atom "p") = none := rfl

end ProofCheckerTest.Automation
