/-
Probe 01 — what `TruthAt` MEANS at a bounded (non-total) convex index.

Research evidence of record for task 553, phase 2. Every declaration below is sorry-free and
compiles against the live tree with

  lake env lean specs/553_decide_convex_history_layer_collapse/probes/01_bounded-index-diagnosis.lean

This probe is NOT part of the library and is never imported by it.

WHAT IT ESTABLISHES

  (i)   `atom_false_outside_domain` — at a time outside the index's domain an atom is FALSE,
        not ill-formed. The `∃ (ht : τ.domain t)` conjunct of `TruthAt`'s atom clause makes the
        whole clause false rather than untypeable.
  (ii)  `tense_sees_outside_domain` — the `untl` clause quantifies over all of `D` irrespective
        of the domain: at a bounded index whose only domain point carries a true atom, `F ¬p`
        is nevertheless TRUE, witnessed at a time the index does not settle.
  (iii) `refute_modal_t_at_bounded_index` — the T-schema `□p → p` FAILS at a bounded index at an
        out-of-domain time, because `□p` reads its quantifier off the TOTAL histories (where the
        domain proof is free) while `p` is evaluated at the bounded index (where it is not).
        This is the degeneracy: a formula's modal part and its atomic part are evaluated against
        two different domains.
  (iv)  `modal_t_holds_in_domain` — the same schema HOLDS at the same bounded index at a time
        that IS in the domain. So the degeneracy is exactly co-extensive with evaluating at
        `x ∉ dom τ`, which is precisely what the paper's line-1102 alternative forbids.

The pair (iii)/(iv) is the finding: the current clause set at a bounded index is neither
`def:BL-semantics` (which evaluates only at possible worlds) nor the paper's footnoted
alternative (which requires `x ∈ dom τ` and restricts the tenses); it is a third, unintended
reading that is degenerate off the domain and coherent on it.
-/
import FormalSystem.Semantics.Truth
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.SuccPred

open FormalSystem.Syntax FormalSystem.Semantics

namespace Probe553A

/-- The permissive frame over `ℤ`: every function `ℤ → ℕ` is a total history. -/
abbrev NF : TaskFrame := FrameOver.natFrame (D := ℤ)

/-- The model in which every atom is true at every world state. -/
def MT : TaskModel NF := TaskModel.allTrue

/-- Every function `ℤ → ℕ` is a total history of `NF`. -/
def totalHist (f : ℤ → ℕ) : ConvexHistory NF :=
  ConvexHistory.ofTotal NF f (fun s t => by
    by_cases h : t - s = 0
    · right; have : t = s := sub_eq_zero.mp h; subst this; rfl
    · left; exact h)

theorem totalHist_isTotal (f : ℤ → ℕ) : (totalHist f).IsTotal :=
  ConvexHistory.ofTotal_isTotal _ _ _

/--
**The bounded index.** A convex history over `NF` whose domain is the single time `0`
(equivalently the closed interval `[0, 0]`), sending it to world state `0`.

`NF`'s task relation is permissive (`d ≠ 0 ∨ w = u`), so `respects_task` is discharged by the
same case split as `totalHist`; convexity is the antisymmetry of `≤` on `ℤ`.
-/
def bdd : ConvexHistory NF where
  domain := fun t => 0 ≤ t ∧ t ≤ 0
  nonempty_domain := ⟨0, le_refl 0, le_refl 0⟩
  states := fun _ _ => (0 : Nat)
  respects_task := fun s t _ _ => by
    by_cases h : t - s = 0
    · right; rfl
    · left; exact h
  convex := fun x z hx hz y hxy hyz => ⟨le_trans hx.1 hxy, le_trans hyz hz.2⟩

/-- `bdd` is genuinely bounded: the time `1` is not in its domain. -/
theorem bdd_one_not_mem : ¬ bdd.domain 1 := by
  rintro ⟨-, h⟩; exact absurd h (by decide)

/-- `bdd` is genuinely bounded: it is not total. -/
theorem bdd_not_isTotal : ¬ bdd.IsTotal := fun h => bdd_one_not_mem (h 1)

/-- `0` IS in `bdd`'s domain. -/
theorem bdd_zero_mem : bdd.domain 0 := ⟨le_refl 0, le_refl 0⟩

/-! ### (i) An atom outside the domain is false, not ill-formed -/

/--
**Finding (i).** At `t = 1`, outside `bdd`'s domain, the atom `p` is FALSE. The clause is
well-formed — it is a `Prop` like any other — and it is refuted, because its leading existential
asks for a domain proof that does not exist.
-/
theorem atom_false_outside_domain (p : Atom) :
    ¬ TruthAt MT bdd 1 (Formula.atom p) := by
  rintro ⟨ht, -⟩
  exact bdd_one_not_mem ht

/-- For contrast: the same atom is TRUE at `0`, which is in the domain. -/
theorem atom_true_inside_domain (p : Atom) :
    TruthAt MT bdd 0 (Formula.atom p) :=
  ⟨bdd_zero_mem, trivial⟩

/-! ### (ii) The tense clauses quantify over all of `D`, not over the domain -/

/--
**Finding (ii).** `F ¬p` — `Formula.someFuture (Formula.neg (Formula.atom p))`, i.e.
`untl ⊤ (¬p)` — is TRUE at `(bdd, 0)`, even though the model makes every atom true at every
world state and `0` is the only time `bdd` settles. The witness is `s = 1`, a time OUTSIDE the
domain, where `¬p` holds only because the atom clause failed for want of a domain proof.

So the tense operators do not respect the index's domain: they range over all of `D` and read
"outside the domain" as "the atom is false there". That is not a restriction of the semantics to
the domain, and it is not the paper's footnoted alternative either.
-/
theorem tense_sees_outside_domain (p : Atom) :
    TruthAt MT bdd 0 (Formula.someFuture (Formula.neg (Formula.atom p))) := by
  refine ⟨1, by decide, ?_, ?_⟩
  · intro hp; exact atom_false_outside_domain p hp
  · intro r _ _; exact fun h => h

/-! ### (iii) The T-schema fails at a bounded index off the domain -/

/--
`□p` is true at EVERY time, at every index, in `MT`: the box clause quantifies over the total
histories, where the domain proof is free, and `MT` makes every atom true at every state.
-/
theorem box_atom_true (p : Atom) (τ : ConvexHistory NF) (t : ℤ) :
    TruthAt MT τ t (Formula.box (Formula.atom p)) :=
  fun _σ hσ => ⟨hσ t, trivial⟩

/--
**Finding (iii) — the degeneracy.** The T-schema `□p → p` is REFUTED at the bounded index `bdd`
at the out-of-domain time `1`.

`□p` holds because the box clause re-indexes to the total histories, where `p`'s domain
obligation is discharged for free. `p` fails because the atom clause is evaluated at `bdd`, where
it is not. The antecedent and the consequent are therefore evaluated against two different
domains, and the schema separates them.

`modal_t` (`ProofSystem/Axioms.lean`) is an axiom of TM. So dropping the `IsTotal` binder from
the consequence relation while leaving `t` ranging over all of `D` — the relation this study
calls C2 — does not merely weaken the logic: it invalidates an axiom.
-/
theorem refute_modal_t_at_bounded_index (p : Atom) :
    ¬ TruthAt MT bdd 1 (Formula.imp (Formula.box (Formula.atom p)) (Formula.atom p)) := by
  intro h
  exact atom_false_outside_domain p (h (box_atom_true p bdd 1))

/-! ### (iv) …and holds at the same index inside the domain -/

/--
**Finding (iv).** At `0`, which IS in `bdd`'s domain, the same instance of the T-schema holds.

Together with (iii) this locates the degeneracy exactly: it is evaluation at `x ∉ dom τ` that
breaks the schema, not boundedness of the index as such. The paper's line-1102 alternative
requires `x ∈ dom τ`, so it does not inherit this failure — the failure belongs to C2 alone.
-/
theorem modal_t_holds_in_domain (p : Atom) :
    TruthAt MT bdd 0 (Formula.imp (Formula.box (Formula.atom p)) (Formula.atom p)) :=
  fun _ => atom_true_inside_domain p

/-! ### Bonus: `F⊤` is true at every index under the CURRENT clauses -/

/--
`F⊤` — the seriality axiom TS's semantic content — is true at the bounded index at every time,
because the `untl` clause quantifies over all of `D` and `ℤ` has no maximum.

This is what a domain-restricted tense clause would break, and it is why the paper's footnote
observes that its alternative makes `F⊥` satisfiable. Under the CURRENT clauses at a bounded
index, it does not: the boundedness is invisible to the tense operators.
-/
theorem someFuture_top_true_at_bounded (t : ℤ) :
    TruthAt MT bdd t (Formula.someFuture Formula.top) :=
  ⟨t + 1, lt_add_one t, fun h => h, fun _ _ _ h => h⟩

end Probe553A
