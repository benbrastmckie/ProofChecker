/-
Probe 02 — the candidate consequence relations C1–C4, defined and separated.

Research evidence of record for task 553, phase 3. Every declaration below is sorry-free and
compiles against the live tree with

  lake env lean specs/553_decide_convex_history_layer_collapse/probes/02_alternative-consequence.lean

This probe is NOT part of the library and is never imported by it. `TruthAtConvex` below is a
LOCAL recursion written beside the library's `TruthAt`, not a modification of it.

THE FOUR RELATIONS

  C1  the current/paper relation. `ConsequenceOnFrames` (`Semantics/Validity.lean:78`):
      index total (`τ.IsTotal`), `□` over `H_F`, tenses over all of `D`, `t` over all of `D`.
      Reproduced here as `ValidC1` for a single frame.

  C2  the current CLAUSES at a convex index: drop the `IsTotal` binder from C1 and change
      nothing else. This is not a design; it is what the tree's `TruthAt` already computes at a
      bounded index. Probe 01 shows it is degenerate.

  C3  the paper's line-1102 alternative: index any convex `τ` with `x ∈ dom τ`; `□` quantifies
      over the convex `σ` with `x ∈ dom σ`; the tense clauses are restricted to `dom τ`;
      consequence quantifies `x` over `dom τ` rather than over `D`.

  C4  C3 restricted to closed-bounded-interval domains `[a, b]` — the sections of the paper's
      behavior presheaf `Beh(F)`. This is the relation with a categorical reading.

WHAT IT ESTABLISHES

  * `valid_C1_someFuture_top` / `refute_C3_someFuture_top` — `F⊤` (the semantic content of TM's
    seriality axiom TS) is C1-valid and C3-INVALID, refuted at the right endpoint of a bounded
    interval. This is the separating pair the paper's own commented-out sentence predicts.
  * `truthC3_box_indep` — under C3, `□φ` at `(τ, x)` does not depend on `τ` at all. `□` remains
    a universal modality; C3 changes its RANGE, not its character.
  * `pointHist` + `pointHist_domain_self` — a point history `{⟨x, w⟩}` is a legal C3 index for
    every world state `w`, so C3's `□` ranges over strictly more indices than C1's does.
  * `c3_modal_t`, `c3_modal_4`, `c3_modal_b`, `c3_modal_5_collapse` — the whole S5 modal core
    survives C3, for an arbitrary task frame, precisely BECAUSE of `truthC3_box_indep`.
  * `validC3_imp_validC4` — every C3-validity is a C4-validity; C4 is the restriction of C3 to
    interval indices, so the F⊤ refutation lands for C4 too (`refute_C4_someFuture_top`).
-/
import FormalSystem.Semantics.Truth
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.SuccPred

open FormalSystem.Syntax FormalSystem.Semantics
open scoped Classical

namespace Probe553B

variable {F : TaskFrame}

/-! ## The C3 truth definition -/

/--
**C3 truth.** The paper's line-1102 alternative, clause for clause:

* `atom` — unchanged (already domain-relative);
* `box` — quantifies over the convex `σ` whose domain contains the evaluation time, in place of
  `def:BL-semantics`'s quantification over `H_F`;
* `untl` / `snce` — the witness `s` and the interval times `r` are both restricted to `dom τ`,
  in place of the library's unrestricted quantification over `D`.

The index is not required to be total. The side condition `x ∈ dom τ` is imposed by the
consequence and validity definitions below, not by this recursion, exactly as `IsTotal` is
imposed by `ConsequenceOnFrames` and not by `TruthAt`.
-/
def TruthAtConvex (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration) : Formula → Prop
  | Formula.atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => TruthAtConvex M τ t φ → TruthAtConvex M τ t ψ
  | Formula.box φ => ∀ (σ : ConvexHistory F), σ.domain t → TruthAtConvex M σ t φ
  | Formula.untl ψ φ => ∃ s : F.Duration, τ.domain s ∧ t < s ∧ TruthAtConvex M τ s φ ∧
      ∀ r : F.Duration, τ.domain r → t < r → r < s → TruthAtConvex M τ r ψ
  | Formula.snce ψ φ => ∃ s : F.Duration, τ.domain s ∧ s < t ∧ TruthAtConvex M τ s φ ∧
      ∀ r : F.Duration, τ.domain r → s < r → r < t → TruthAtConvex M τ r ψ

/-! ## The four validity notions, at a fixed frame -/

/-- **C1** at a fixed frame: the current relation. Index total, time over all of `D`. -/
def ValidC1 (F : TaskFrame) (φ : Formula) : Prop :=
  ∀ (M : TaskModel F) (τ : ConvexHistory F), τ.IsTotal → ∀ t : F.Duration, TruthAt M τ t φ

/-- **C2** at a fixed frame: C1 with the `IsTotal` binder deleted and nothing else changed. -/
def ValidC2 (F : TaskFrame) (φ : Formula) : Prop :=
  ∀ (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration), TruthAt M τ t φ

/-- **C3** at a fixed frame: any convex index, evaluated only at times in its own domain. -/
def ValidC3 (F : TaskFrame) (φ : Formula) : Prop :=
  ∀ (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration), τ.domain x → TruthAtConvex M τ x φ

/-- A convex history is an **interval history** when its domain is a closed bounded interval —
the domain shape of the paper's `Beh(F)(ℓ)` sections, up to translation. -/
def IsInterval (τ : ConvexHistory F) : Prop :=
  ∃ a b : F.Duration, ∀ t : F.Duration, τ.domain t ↔ (a ≤ t ∧ t ≤ b)

/-- **C4** at a fixed frame: C3 restricted to interval indices — the sections of `Beh(F)`. -/
def ValidC4 (F : TaskFrame) (φ : Formula) : Prop :=
  ∀ (M : TaskModel F) (τ : ConvexHistory F), IsInterval τ →
    ∀ x : F.Duration, τ.domain x → TruthAtConvex M τ x φ

/-- C4 is a restriction of C3: every C3-validity is a C4-validity. -/
theorem validC3_imp_validC4 {F : TaskFrame} {φ : Formula} (h : ValidC3 F φ) : ValidC4 F φ :=
  fun M τ _ x hx => h M τ x hx

/-! ## C3's box is index-independent, and its range is larger than `H_F` -/

/--
**C3's `□` does not depend on the index.** Its clause reads its quantifier range off the
evaluation time `x` alone — the convex `σ` with `x ∈ dom σ` — so `□φ` at `(τ, x)` and at
`(τ', x)` are the same proposition, by `rfl`.

This is the structural fact that makes the S5 core survive C3: `□` is still a universal modality
over a set determined by `x`, and that set still contains the index itself (because a C3 index
satisfies `x ∈ dom τ`). What C3 changes is the RANGE — from `H_F` to the convex histories
through `x` — not the character of the operator.
-/
theorem truthC3_box_indep (M : TaskModel F) (τ τ' : ConvexHistory F) (x : F.Duration)
    (φ : Formula) :
    TruthAtConvex M τ x (Formula.box φ) = TruthAtConvex M τ' x (Formula.box φ) := rfl

/--
**The point history** `{⟨x, w⟩}` as a convex history: the paper's one-point partial history
(`Semantics/Extension/Extension.lean:227`) with its convexity field, which is immediate since
the domain is a singleton.

`respects_task` is only ever the zero-duration instance, discharged by `nullity_identity`.
-/
def pointHist (F : TaskFrame) (w : F.WorldState) (x : F.Duration) : ConvexHistory F where
  domain := fun t => t = x
  nonempty_domain := ⟨x, rfl⟩
  states := fun _ _ => w
  respects_task := by
    intro s t hs ht
    subst hs; subst ht
    simpa [sub_self] using (F.nullity_identity w w).mpr rfl
  convex := by
    intro a c ha hc y hay hyc
    subst ha; subst hc
    exact le_antisymm hyc hay

/-- A point history is a legal C3 index at its own point. -/
theorem pointHist_domain_self (F : TaskFrame) (w : F.WorldState) (x : F.Duration) :
    (pointHist F w x).domain x := rfl

/-- A point history is an interval history — the degenerate interval `[x, x]`, i.e. a germ. -/
theorem pointHist_isInterval (F : TaskFrame) (w : F.WorldState) (x : F.Duration) :
    IsInterval (pointHist F w x) :=
  ⟨x, x, fun _t => ⟨fun h => ⟨le_of_eq h.symm, le_of_eq h⟩, fun h => le_antisymm h.2 h.1⟩⟩

/-- A point history is never total when `D` has more than one element. -/
theorem pointHist_not_isTotal (F : TaskFrame) (w : F.WorldState) (x y : F.Duration) (h : y ≠ x) :
    ¬ (pointHist F w x).IsTotal := fun ht => h (ht y)

/-! ## The S5 modal core survives C3 -/

/-- **T survives C3**: `□φ → φ`. The index is itself in the box's range, by the C3 side
condition `x ∈ dom τ`. -/
theorem c3_modal_t (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (hx : τ.domain x)
    (φ : Formula) : TruthAtConvex M τ x (Formula.imp (Formula.box φ) φ) :=
  fun h => h τ hx

/-- **4 survives C3**: `□φ → □□φ`. Immediate from `truthC3_box_indep`. -/
theorem c3_modal_4 (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (φ : Formula) :
    TruthAtConvex M τ x (Formula.imp (Formula.box φ) (Formula.box (Formula.box φ))) :=
  fun h _σ _ ρ hρ => h ρ hρ

/-- **B survives C3**: `φ → □◇φ`, with `◇φ = ¬□¬φ`. -/
theorem c3_modal_b (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (hx : τ.domain x)
    (φ : Formula) : TruthAtConvex M τ x (Formula.imp φ (Formula.box φ.diamond)) := by
  intro hφ σ _ hbox
  exact hbox τ hx hφ

/-- **5 (in the repository's collapse form) survives C3**: `◇□φ → □φ`. Classical. -/
theorem c3_modal_5_collapse (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (φ : Formula) : TruthAtConvex M τ x (Formula.imp φ.box.diamond φ.box) := by
  intro h σ hσ
  by_contra hcon
  refine h (fun ρ _ hbox => hcon ?_)
  exact hbox σ hσ

/--
**Under C3, `□F⊤` is UNSATISFIABLE** — at every model, every convex index, and every time.

The point history `{⟨x, w⟩}` is in the box's C3 range at `x` for every world state `w`
(`pointHist_domain_self`), and no point history has a later time in its own domain, so `F⊤`
fails there. Hence `□F⊤` is false everywhere.

This is the sharpest thing this study can say about "what C3 does to formulas mixing `□` with
tense", and it is stronger than the loss of TS. TM is closed under necessitation, so `⊢ F⊤`
yields `⊢ □F⊤`; a semantics on which `□F⊤` is unsatisfiable is not one from which TM's rule
structure can be salvaged by deleting an axiom. C3 is a genuinely different logic, not TM minus
seriality.

The same argument refutes `□ψ` for every `ψ` that fails at germs — every formula whose principal
content is tense.
-/
theorem c3_box_someFuture_top_unsat {F : TaskFrame} (M : TaskModel F) (τ : ConvexHistory F)
    (x : F.Duration) :
    ¬ TruthAtConvex M τ x (Formula.box (Formula.someFuture Formula.top)) := by
  intro h
  obtain ⟨w⟩ := (inferInstance : Nonempty F.WorldState)
  obtain ⟨s, hs, hxs, -, -⟩ := h (pointHist F w x) (pointHist_domain_self F w x)
  subst hs
  exact lt_irrefl _ hxs

/-! ## The separation: `F⊤` is C1-valid and C3-invalid -/

/-- The permissive frame over `ℤ`. Reused from probe 01. -/
abbrev NF : TaskFrame := FrameOver.natFrame (D := ℤ)

/-- Every function `ℤ → ℕ` is a total history of `NF`. -/
def totalHist (f : ℤ → ℕ) : ConvexHistory NF :=
  ConvexHistory.ofTotal NF f (fun s t => by
    by_cases h : t - s = 0
    · right; have : t = s := sub_eq_zero.mp h; subst this; rfl
    · left; exact h)

/-- The bounded index `[0, 0]` over `NF`, as in probe 01. -/
def bdd : ConvexHistory NF where
  domain := fun t => 0 ≤ t ∧ t ≤ 0
  nonempty_domain := ⟨0, le_refl 0, le_refl 0⟩
  states := fun _ _ => (0 : Nat)
  respects_task := fun s t _ _ => by
    by_cases h : t - s = 0
    · right; rfl
    · left; exact h
  convex := fun x z hx hz y hxy hyz => ⟨le_trans hx.1 hxy, le_trans hyz hz.2⟩

theorem bdd_zero_mem : bdd.domain 0 := ⟨le_refl 0, le_refl 0⟩

theorem bdd_isInterval : IsInterval bdd := ⟨0, 0, fun _ => Iff.rfl⟩

/--
**`F⊤` is C1-valid at `NF`.** The `untl` clause quantifies over all of `D = ℤ`, which has no
maximum, so the witness `t + 1` is always available. Nothing about totality is used — which is
the point: C1's tense clauses never consult the domain, so C1-validity of `F⊤` is a fact about
`D`, not about the index.

The general statement over every frame is `Soundness.serial_future_axiom_valid`
(`Metalogic/Soundness.lean:261`); this is its one-frame instance, proved here so that the
separating pair is self-contained.
-/
theorem valid_C1_someFuture_top : ValidC1 NF (Formula.someFuture Formula.top) :=
  fun _M _τ _hτ t => ⟨t + 1, lt_add_one t, fun h => h, fun _ _ _ h => h⟩

/--
**`F⊤` is NOT C3-valid at `NF`.** Refuted at `(bdd, 0)` — the right endpoint of the closed
bounded interval `[0, 0]`. C3's `untl` clause requires its witness `s` to lie in `dom τ`, and
`dom bdd = {0}` contains no time strictly after `0`.

This is exactly what the paper's own commented-out sentence at line 1102 predicts: "At the final
move of a finished game there is no later time in that history's domain, and so `F⊤` — the
seriality axiom TS of the logic TM presented below — and its past dual both fail, making `F⊥`
satisfiable and the unboundedness of time contingent." Here it is machine-checked rather than
cited.
-/
theorem refute_C3_someFuture_top : ¬ ValidC3 NF (Formula.someFuture Formula.top) := by
  intro h
  obtain ⟨s, ⟨-, hs0⟩, h0s, -, -⟩ := h TaskModel.allTrue bdd 0 bdd_zero_mem
  exact absurd (lt_of_lt_of_le h0s hs0) (lt_irrefl 0)

/-- **…and not C4-valid either**, since `bdd` is an interval index. -/
theorem refute_C4_someFuture_top : ¬ ValidC4 NF (Formula.someFuture Formula.top) := by
  intro h
  obtain ⟨s, ⟨-, hs0⟩, h0s, -, -⟩ := h TaskModel.allTrue bdd bdd_isInterval 0 bdd_zero_mem
  exact absurd (lt_of_lt_of_le h0s hs0) (lt_irrefl 0)

/-- Dually, `P⊤` fails at the LEFT endpoint of the same interval — the past seriality axiom. -/
theorem refute_C3_somePast_top : ¬ ValidC3 NF (Formula.somePast Formula.top) := by
  intro h
  obtain ⟨s, ⟨hs0, -⟩, hs, -, -⟩ := h TaskModel.allTrue bdd 0 bdd_zero_mem
  exact absurd (lt_of_le_of_lt hs0 hs) (lt_irrefl 0)

/-! ## C2 is not C1 either — the degeneracy, restated in this file's vocabulary -/

/-- `□p → p` is C1-valid at `NF` (the index is one of the total histories the box quantifies
over). -/
theorem valid_C1_modal_t (p : Atom) :
    ValidC1 NF (Formula.imp (Formula.box (Formula.atom p)) (Formula.atom p)) :=
  fun _M τ hτ _t h => h τ hτ

/-- `□p → p` is NOT C2-valid at `NF`: probe 01's refutation, restated. The witness is the
bounded index at an out-of-domain time, which C2 admits and C3 does not. -/
theorem refute_C2_modal_t (p : Atom) :
    ¬ ValidC2 NF (Formula.imp (Formula.box (Formula.atom p)) (Formula.atom p)) := by
  intro h
  obtain ⟨⟨-, h1⟩, -⟩ := h TaskModel.allTrue bdd 1 (fun σ hσ => ⟨hσ 1, trivial⟩)
  exact absurd h1 (by decide)

end Probe553B
