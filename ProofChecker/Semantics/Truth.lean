import ProofChecker.Semantics.TaskModel
import ProofChecker.Semantics.WorldHistory
import ProofChecker.Syntax.Formula

/-!
# Truth - Truth Evaluation in Task Semantics

This module defines truth evaluation for TM formulas in task models.

## Paper Specification Reference

**Bimodal Logic Semantics (app:TaskSemantics, def:BL-semantics, lines 1857-1866)**:
The JPL paper defines truth evaluation for TM formulas as follows:
- `M,τ,x ⊨ p` iff `τ(x) ∈ V(p)` (atom satisfaction)
- `M,τ,x ⊨ ⊥` is false (bottom)
- `M,τ,x ⊨ φ → ψ` iff `M,τ,x ⊨ φ` implies `M,τ,x ⊨ ψ` (implication)
- `M,τ,x ⊨ □φ` iff `M,σ,x ⊨ φ` for all σ ∈ Ω (box: necessity)
- `M,τ,x ⊨ Past φ` iff `M,τ,y ⊨ φ` for all y ∈ T where y < x (past)
- `M,τ,x ⊨ Future φ` iff `M,τ,y ⊨ φ` for all y ∈ T where x < y (future)

**ProofChecker Implementation Alignment**:
✓ Atom: `M.valuation (τ.states t ht) p` matches paper's `τ(x) ∈ V(p)`
✓ Bot: `False` matches paper's definition
✓ Imp: Standard material conditional matches paper
✓ Box: `∀ (σ : WorldHistory F) (hs : σ.domain t), truth_at M σ t hs φ` matches paper's quantification over all histories
✓ Past: `∀ (s : Int) (hs : τ.domain s), s < t → truth_at M τ s hs φ` matches paper's quantification with domain restriction
✓ Future: `∀ (s : Int) (hs : τ.domain s), t < s → truth_at M τ s hs φ` matches paper's quantification with domain restriction

**Semantic Verification (Task 3A.7)**:
Temporal operator implementations correctly restrict quantification to `s ∈ τ.domain`
(history's time domain), matching the paper's specification exactly. This is critical
for correct temporal semantics.

## Main Definitions

- `truth_at`: Truth of a formula at a model-history-time triple
- No notation defined (parsing conflicts with validity notation)

## Main Results

- Basic truth lemmas (e.g., `bot` is always false)
- Truth evaluation examples

## Implementation Notes

- Truth is defined recursively on formula structure
- Modal box quantifies over all world histories at current time
- Temporal past/future quantify over earlier/later times in current history
- Times are Int for MVP simplicity

## References

* [ARCHITECTURE.md](../../../Documentation/UserGuide/ARCHITECTURE.md) - Truth evaluation specification
* [Formula.lean](../Syntax/Formula.lean) - Formula syntax
* [TaskModel.lean](TaskModel.lean) - Task model structure
* JPL Paper app:TaskSemantics (def:BL-semantics, lines 1857-1866) - Formal truth definition
-/

namespace ProofChecker.Semantics

open ProofChecker.Syntax

variable {F : TaskFrame}

/--
Truth of a formula at a model-history-time triple.

Given:
- `M`: A task model (frame + valuation)
- `τ`: A world history (function from times to states)
- `t`: A time point
- `φ`: A formula

Returns whether `φ` is true at this semantic configuration.

The evaluation is defined recursively on formula structure:
- Atoms: true iff valuation says so at current state
- Bot (⊥): always false
- Implication: standard material conditional
- Box (□): true iff φ true at all world histories at time t
- Past (P): true iff φ true at all past times in current history
- Future (F): true iff φ true at all future times in current history
-/
def truth_at (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t) :
    Formula → Prop
  | Formula.atom p => M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => truth_at M τ t ht φ → truth_at M τ t ht ψ
  | Formula.box φ => ∀ (σ : WorldHistory F) (hs : σ.domain t), truth_at M σ t hs φ
  | Formula.past φ => ∀ (s : Int) (hs : τ.domain s), s < t → truth_at M τ s hs φ
  | Formula.future φ => ∀ (s : Int) (hs : τ.domain s), t < s → truth_at M τ s hs φ

-- Note: We avoid defining a notation for truth_at as it causes parsing conflicts
-- with the validity notation in Validity.lean. Use truth_at directly.

namespace Truth

/--
Bot (⊥) is false everywhere.
-/
theorem bot_false {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t} :
    ¬(truth_at M τ t ht Formula.bot) := by
  intro h
  exact h

/--
Truth of implication is material conditional.
-/
theorem imp_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ ψ : Formula) :
    (truth_at M τ t ht (φ.imp ψ)) ↔ ((truth_at M τ t ht φ) → (truth_at M τ t ht ψ)) := by
  rfl

/--
Truth of atom depends on valuation at current state.
-/
theorem atom_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (p : String) :
    (truth_at M τ t ht (Formula.atom p)) ↔ M.valuation (τ.states t ht) p := by
  rfl

/--
Truth of box: formula true at all histories at current time.
-/
theorem box_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.box) ↔
      ∀ (σ : WorldHistory F) (hs : σ.domain t), (truth_at M σ t hs φ) := by
  rfl

/--
Truth of past: formula true at all earlier times in history.
-/
theorem past_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.past) ↔
      ∀ (s : Int) (hs : τ.domain s), s < t → (truth_at M τ s hs φ) := by
  rfl

/--
Truth of future: formula true at all later times in history.
-/
theorem future_iff {F : TaskFrame} {M : TaskModel F} {τ : WorldHistory F} {t : Int} {ht : τ.domain t}
    (φ : Formula) :
    (truth_at M τ t ht φ.future) ↔
      ∀ (s : Int) (hs : τ.domain s), t < s → (truth_at M τ s hs φ) := by
  rfl

end Truth

/-! ## Time-Shift Preservation

These lemmas establish that truth is preserved under time-shift transformations.
This is fundamental to proving the MF and TF axioms valid.

The key insight is that for a formula φ:
  `truth_at M σ y hy φ ↔ truth_at M (time_shift σ (y - x)) x hx φ`

This relates truth at (σ, y) to truth at (shifted_σ, x).
-/

namespace TimeShift

/--
Time-shift preserves truth of formulas.

If σ is a history and Δ = y - x, then truth at (σ, y) equals truth at (time_shift σ Δ, x).

**Paper Reference**: lem:history-time-shift-preservation establishes this property.

The proof proceeds by structural induction on formulas:
- **Atom**: States match because (time_shift σ Δ).states x = σ.states (x + Δ) = σ.states y
- **Bot**: Both sides are False
- **Imp**: By induction hypothesis on subformulas
- **Box**: Both quantify over ALL histories at their respective times; using a bijection
  between histories at x and histories at y via time-shift
- **Past/Future**: Times shift together with the history

**Key Insight**: The box case is the crucial one. For any history ρ at time x,
`time_shift ρ (-Δ)` gives a history at time y (since x + Δ = y means x = y - Δ).
This establishes a bijection between histories at the two times.
-/
theorem time_shift_preserves_truth (M : TaskModel F) (σ : WorldHistory F) (x y : Int)
    (hx : (WorldHistory.time_shift σ (y - x)).domain x) (hy : σ.domain y) (φ : Formula) :
    truth_at M (WorldHistory.time_shift σ (y - x)) x hx φ ↔ truth_at M σ y hy φ := by
  -- Proof by structural induction on φ
  induction φ generalizing x y hx hy with
  | atom p =>
    -- For atoms, states must match
    -- (time_shift σ Δ).states x = σ.states (x + Δ) = σ.states y
    simp only [truth_at, WorldHistory.time_shift]
    -- Need to show: M.valuation (σ.states (x + (y - x)) hx) p ↔ M.valuation (σ.states y hy) p
    have h_eq : x + (y - x) = y := by omega
    congr 2
    · rw [h_eq]
    · rfl

  | bot =>
    -- Both sides are False
    simp only [truth_at]

  | imp ψ χ ih_ψ ih_χ =>
    -- By IH on both subformulas
    simp only [truth_at]
    constructor
    · intro h h_psi
      have h_psi' := (ih_ψ x y hx hy).mpr h_psi
      exact (ih_χ x y hx hy).mp (h h_psi')
    · intro h h_psi'
      have h_psi := (ih_ψ x y hx hy).mp h_psi'
      exact (ih_χ x y hx hy).mpr (h h_psi)

  | box ψ ih =>
    -- For box, both quantify over ALL histories at their times
    -- We use the fact that time-shift gives a bijection between histories at x and y
    simp only [truth_at]
    constructor
    · intro h_box_x ρ hρ_y
      -- ρ is a history at time y
      -- time_shift ρ (y - x) is a history at time x (domain at x iff ρ domain at x + (y-x) = y)
      have hρ_x : (WorldHistory.time_shift ρ (y - x)).domain x := by
        simp only [WorldHistory.time_shift]
        have h_eq : x + (y - x) = y := by omega
        rw [h_eq]
        exact hρ_y
      have h1 := h_box_x (WorldHistory.time_shift ρ (y - x)) hρ_x
      exact (ih x y hρ_x hρ_y).mp h1
    · intro h_box_y ρ hρ_x
      -- ρ is a history at time x
      -- time_shift ρ (-(y - x)) = time_shift ρ (x - y) is a history at time y
      have hρ_y : (WorldHistory.time_shift ρ (x - y)).domain y := by
        simp only [WorldHistory.time_shift]
        have h_eq : y + (x - y) = x := by omega
        rw [h_eq]
        exact hρ_x
      have h1 := h_box_y (WorldHistory.time_shift ρ (x - y)) hρ_y
      -- We need to relate back: time_shift (time_shift ρ (x-y)) (y-x) at x equals ρ at x
      -- Actually we can use IH directly on the shifted history
      -- ih gives: truth at (time_shift ρ' (y-x), x) ↔ truth at (ρ', y)
      -- We have h1 : truth at (time_shift ρ (x-y), y)
      -- We need: truth at (ρ, x)
      -- Using IH with ρ' = time_shift ρ (x-y):
      --   truth at (time_shift (time_shift ρ (x-y)) (y-x), x) ↔ truth at (time_shift ρ (x-y), y)
      -- The LHS needs to equal truth at (ρ, x)
      -- time_shift (time_shift ρ (x-y)) (y-x) domain at x iff (time_shift ρ (x-y)) domain at x + (y-x) = y
      -- iff ρ domain at y + (x - y) = x ✓

      -- This requires showing the double shift equals the original
      -- For now, we use a direct argument
      have hρ_x' : (WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (y - x)).domain x := by
        simp only [WorldHistory.time_shift]
        have h_eq : x + (y - x) + (x - y) = x := by omega
        rw [h_eq]
        exact hρ_x
      have h2 := (ih x y hρ_x' hρ_y).mpr h1
      -- h2 : truth_at M (time_shift (time_shift ρ (x-y)) (y-x)) x hρ_x' ψ
      -- Need: truth_at M ρ x hρ_x ψ
      -- The shifted histories have the same states (up to proof irrelevance)
      -- This requires a transport lemma
      sorry

  | past ψ ih =>
    -- Past quantifies over earlier times in the same history
    simp only [truth_at]
    constructor
    · intro h_past r hr hrt
      -- We have truth at (time_shift σ Δ, x) for all r < x
      -- Need truth at (σ, y) for all r < y
      -- Under time shift: r in shifted domain iff r + Δ in original domain
      have hr' : (WorldHistory.time_shift σ (y - x)).domain (r - (y - x)) := by
        simp only [WorldHistory.time_shift]
        have h_eq : r - (y - x) + (y - x) = r := by omega
        rw [h_eq]
        exact hr
      have hrt' : r - (y - x) < x := by omega
      have h1 := h_past (r - (y - x)) hr' hrt'
      -- h1 : truth_at M (time_shift σ (y-x)) (r - (y-x)) hr' ψ
      -- Need: truth_at M σ r hr ψ
      -- Using IH with shifted times
      sorry
    · intro h_past r hr hrt
      sorry

  | future ψ ih =>
    -- Similar to past case
    simp only [truth_at]
    sorry

/--
Corollary: For any history σ at time y, there exists a history at time x
(namely, time_shift σ (y - x)) where the same formulas are true.

This is the key lemma for proving MF and TF axioms.
-/
theorem exists_shifted_history (M : TaskModel F) (σ : WorldHistory F) (x y : Int)
    (hy : σ.domain y) (φ : Formula) :
    truth_at M σ y hy φ ↔
    truth_at M (WorldHistory.time_shift σ (y - x)) x
      (by simp only [WorldHistory.time_shift]; have h : x + (y - x) = y := by omega; rw [h]; exact hy) φ := by
  exact (time_shift_preserves_truth M σ x y _ hy φ).symm

end TimeShift

end ProofChecker.Semantics
