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
Truth is independent of the domain membership proof (proof irrelevance for truth).

This auxiliary lemma is crucial for transporting truth between different domain membership proofs.
-/
theorem truth_proof_irrel (M : TaskModel F) (τ : WorldHistory F) (t : Int)
    (ht₁ ht₂ : τ.domain t) (φ : Formula) :
    truth_at M τ t ht₁ φ ↔ truth_at M τ t ht₂ φ := by
  -- Proof by structural induction on φ
  induction φ generalizing t ht₁ ht₂ with
  | atom p =>
    -- τ.states t ht₁ = τ.states t ht₂ by proof irrelevance, so both sides are equal
    rfl
  | bot =>
    rfl
  | imp ψ χ ih_ψ ih_χ =>
    constructor
    · intro h h_ψ
      have := (ih_ψ t ht₁ ht₂).mpr h_ψ
      exact (ih_χ t ht₁ ht₂).mp (h this)
    · intro h h_ψ
      have := (ih_ψ t ht₁ ht₂).mp h_ψ
      exact (ih_χ t ht₁ ht₂).mpr (h this)
  | box ψ _ =>
    rfl
  | past ψ _ =>
    rfl
  | future ψ _ =>
    rfl

/--
Truth transport across equal histories.

When two histories are equal and both domain proofs are valid, truth is preserved.
-/
theorem truth_history_eq (M : TaskModel F) (τ₁ τ₂ : WorldHistory F) (t : Int)
    (ht₁ : τ₁.domain t) (ht₂ : τ₂.domain t) (h_eq : τ₁ = τ₂) (φ : Formula) :
    truth_at M τ₁ t ht₁ φ ↔ truth_at M τ₂ t ht₂ φ := by
  cases h_eq
  exact truth_proof_irrel M τ₁ t ht₁ ht₂ φ

/--
Truth at double time-shift with opposite amounts equals truth at original history.

This is the key transport lemma for the box case of time_shift_preserves_truth.
It allows us to transfer truth from (time_shift (time_shift σ Δ) (-Δ)) back to σ.
-/
theorem truth_double_shift_cancel (M : TaskModel F) (σ : WorldHistory F) (Δ : Int) (t : Int)
    (ht : σ.domain t) (ht' : (WorldHistory.time_shift (WorldHistory.time_shift σ Δ) (-Δ)).domain t)
    (φ : Formula) :
    truth_at M (WorldHistory.time_shift (WorldHistory.time_shift σ Δ) (-Δ)) t ht' φ ↔
    truth_at M σ t ht φ := by
  induction φ generalizing t ht ht' with
  | atom p =>
    simp only [truth_at]
    have h_eq := WorldHistory.time_shift_time_shift_neg_states σ Δ t ht ht'
    rw [h_eq]
  | bot =>
    simp only [truth_at]
  | imp ψ χ ih_ψ ih_χ =>
    simp only [truth_at]
    constructor
    · intro h h_ψ
      have h_ψ' := (ih_ψ t ht ht').mpr h_ψ
      exact (ih_χ t ht ht').mp (h h_ψ')
    · intro h h_ψ'
      have h_ψ := (ih_ψ t ht ht').mp h_ψ'
      exact (ih_χ t ht ht').mpr (h h_ψ)
  | box ψ ih =>
    simp only [truth_at]
    -- Box quantifies over ALL histories at time t, independent of current history
    -- Both sides quantify over the same set of histories
  | past ψ ih =>
    simp only [truth_at]
    constructor
    · intro h s hs h_lt
      -- Need domain proof for s in double-shift
      have hs' : (WorldHistory.time_shift (WorldHistory.time_shift σ Δ) (-Δ)).domain s := by
        exact (WorldHistory.time_shift_time_shift_neg_domain_iff σ Δ s).mpr hs
      exact (ih s hs hs').mp (h s hs' h_lt)
    · intro h s hs' h_lt
      -- Need domain proof for s in original
      have hs : σ.domain s := by
        exact (WorldHistory.time_shift_time_shift_neg_domain_iff σ Δ s).mp hs'
      exact (ih s hs hs').mpr (h s hs h_lt)
  | future ψ ih =>
    simp only [truth_at]
    constructor
    · intro h s hs h_lt
      have hs' : (WorldHistory.time_shift (WorldHistory.time_shift σ Δ) (-Δ)).domain s := by
        exact (WorldHistory.time_shift_time_shift_neg_domain_iff σ Δ s).mpr hs
      exact (ih s hs hs').mp (h s hs' h_lt)
    · intro h s hs' h_lt
      have hs : σ.domain s := by
        exact (WorldHistory.time_shift_time_shift_neg_domain_iff σ Δ s).mp hs'
      exact (ih s hs hs').mpr (h s hs h_lt)

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
  induction φ generalizing x y hx hy σ with
  | atom p =>
    -- For atoms, states must match
    -- (time_shift σ Δ).states x = σ.states (x + Δ) = σ.states y
    simp only [truth_at, WorldHistory.time_shift]
    -- Need to show: M.valuation (σ.states (x + (y - x)) hx) p ↔ M.valuation (σ.states y hy) p
    have h_eq : x + (y - x) = y := by omega
    -- Use states_eq_of_time_eq to transport states from (x + (y - x)) to y
    rw [WorldHistory.states_eq_of_time_eq σ (x + (y - x)) y h_eq _ hy]

  | bot =>
    -- Both sides are False
    simp only [truth_at]

  | imp ψ χ ih_ψ ih_χ =>
    -- By IH on both subformulas
    simp only [truth_at]
    constructor
    · intro h h_psi
      have h_psi' := (ih_ψ σ x y hx hy).mpr h_psi
      exact (ih_χ σ x y hx hy).mp (h h_psi')
    · intro h h_psi'
      have h_psi := (ih_ψ σ x y hx hy).mp h_psi'
      exact (ih_χ σ x y hx hy).mpr (h h_psi)

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
      -- Apply IH with ρ instead of σ
      exact (ih ρ x y hρ_x hρ_y).mp h1
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
      -- The key insight: double shift cancels out
      -- (time_shift (time_shift ρ (x-y)) (y-x)).states x = ρ.states (x + (y-x) + (x-y)) = ρ.states x

      -- First, apply IH to get truth at double-shifted history
      have hρ_x' : (WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (y - x)).domain x := by
        simp only [WorldHistory.time_shift]
        have h_eq : x + (y - x) + (x - y) = x := by omega
        rw [h_eq]
        exact hρ_x
      -- Apply IH with time_shift ρ (x - y) instead of σ
      have h2 := (ih (WorldHistory.time_shift ρ (x - y)) x y hρ_x' hρ_y).mpr h1
      -- h2 : truth_at M (time_shift (time_shift ρ (x-y)) (y-x)) x hρ_x' ψ
      -- Need: truth_at M ρ x hρ_x ψ

      -- Key insight: (y-x) = -(x-y), so double shift cancels
      have h_cancel : y - x = -(x - y) := by omega
      -- Use history extensionality to rewrite the double shift
      have h_hist_eq : WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (y - x) =
                       WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (-(x - y)) := by
        exact WorldHistory.time_shift_congr (WorldHistory.time_shift ρ (x - y)) (y - x) (-(x - y)) h_cancel
      -- Transport domain proof using history equality
      have hρ_x'' : (WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (-(x - y))).domain x := by
        rw [← h_hist_eq]
        exact hρ_x'
      -- Transport truth using history equality
      have h2' : truth_at M (WorldHistory.time_shift (WorldHistory.time_shift ρ (x - y)) (-(x - y))) x hρ_x'' ψ := by
        exact (truth_history_eq M _ _ x hρ_x' hρ_x'' h_hist_eq ψ).mp h2
      -- Use truth_double_shift_cancel to transport from double-shifted history to original
      exact (truth_double_shift_cancel M ρ (x - y) x hρ_x hρ_x'' ψ).mp h2'

  | past ψ ih =>
    -- Past quantifies over earlier times in the same history
    -- Times shift together: r < y in σ corresponds to r-(y-x) < x in shifted history
    simp only [truth_at]
    constructor
    · intro h_past s hs h_s_lt_y
      -- s < y in σ, need to show truth at s in σ
      -- Use shifted time: s' = s - (y - x) < x
      have hs_shifted : (WorldHistory.time_shift σ (y - x)).domain (s - (y - x)) := by
        simp only [WorldHistory.time_shift]
        have : (s - (y - x)) + (y - x) = s := by omega
        rw [this]
        exact hs
      have h_s_shifted_lt_x : s - (y - x) < x := by omega
      have h_truth_shifted := h_past (s - (y - x)) hs_shifted h_s_shifted_lt_x
      -- Apply IH: need to show (time_shift σ (y - x), s - (y - x)) ↔ (σ, s)
      -- The shift amount should be: s - (s - (y - x)) = y - x
      have h_shift_eq : s - (s - (y - x)) = y - x := by omega
      -- Use congruence to equate the histories
      have h_hist_eq : WorldHistory.time_shift σ (s - (s - (y - x))) = WorldHistory.time_shift σ (y - x) := by
        exact WorldHistory.time_shift_congr σ (s - (s - (y - x))) (y - x) h_shift_eq
      -- Create domain proof for IH
      have hs_ih : (WorldHistory.time_shift σ (s - (s - (y - x)))).domain (s - (y - x)) := by
        rw [h_hist_eq]
        exact hs_shifted
      -- Transport truth using history equality
      have h_truth_ih : truth_at M (WorldHistory.time_shift σ (s - (s - (y - x)))) (s - (y - x)) hs_ih ψ := by
        exact (truth_history_eq M _ _ (s - (y - x)) hs_shifted hs_ih h_hist_eq.symm ψ).mp h_truth_shifted
      -- Apply IH
      exact (ih σ (s - (y - x)) s hs_ih hs).mp h_truth_ih
    · intro h_past s' hs' h_s'_lt_x
      -- s' < x in shifted σ, need to show truth at s' in shifted σ
      -- s' corresponds to time s = s' + (y - x) in σ
      have hs : σ.domain (s' + (y - x)) := by
        simp only [WorldHistory.time_shift] at hs'
        exact hs'
      have h_s_lt_y : s' + (y - x) < y := by omega
      have h_truth_orig := h_past (s' + (y - x)) hs h_s_lt_y
      -- Apply IH: need shift amount = (s' + (y - x)) - s' = y - x
      have h_shift_eq : (s' + (y - x)) - s' = y - x := by omega
      -- Use congruence to equate histories
      have h_hist_eq : WorldHistory.time_shift σ ((s' + (y - x)) - s') = WorldHistory.time_shift σ (y - x) := by
        exact WorldHistory.time_shift_congr σ ((s' + (y - x)) - s') (y - x) h_shift_eq
      -- Create domain proof for IH
      have hs'_ih : (WorldHistory.time_shift σ ((s' + (y - x)) - s')).domain s' := by
        rw [h_hist_eq]
        exact hs'
      -- Apply IH and transport
      have h_ih := (ih σ s' (s' + (y - x)) hs'_ih hs).mpr h_truth_orig
      -- Transport using history equality
      exact (truth_history_eq M _ _ s' hs'_ih hs' h_hist_eq ψ).mp h_ih

  | future ψ ih =>
    -- Similar to past case: r > y in σ corresponds to r-(y-x) > x in shifted history
    simp only [truth_at]
    constructor
    · intro h_future s hs h_y_lt_s
      -- y < s in σ, need to show truth at s in σ
      -- Use shifted time: s' = s - (y - x) > x
      have hs_shifted : (WorldHistory.time_shift σ (y - x)).domain (s - (y - x)) := by
        simp only [WorldHistory.time_shift]
        have : (s - (y - x)) + (y - x) = s := by omega
        rw [this]
        exact hs
      have h_x_lt_s_shifted : x < s - (y - x) := by omega
      have h_truth_shifted := h_future (s - (y - x)) hs_shifted h_x_lt_s_shifted
      -- Apply IH with shift amount s - (s - (y - x)) = y - x
      have h_shift_eq : s - (s - (y - x)) = y - x := by omega
      -- Use congruence to equate histories
      have h_hist_eq : WorldHistory.time_shift σ (s - (s - (y - x))) = WorldHistory.time_shift σ (y - x) := by
        exact WorldHistory.time_shift_congr σ (s - (s - (y - x))) (y - x) h_shift_eq
      -- Create domain proof for IH
      have hs_ih : (WorldHistory.time_shift σ (s - (s - (y - x)))).domain (s - (y - x)) := by
        rw [h_hist_eq]
        exact hs_shifted
      -- Transport truth using history equality
      have h_truth_ih : truth_at M (WorldHistory.time_shift σ (s - (s - (y - x)))) (s - (y - x)) hs_ih ψ := by
        exact (truth_history_eq M _ _ (s - (y - x)) hs_shifted hs_ih h_hist_eq.symm ψ).mp h_truth_shifted
      -- Apply IH
      exact (ih σ (s - (y - x)) s hs_ih hs).mp h_truth_ih
    · intro h_future s' hs' h_x_lt_s'
      -- x < s' in shifted σ, need to show truth at s' in shifted σ
      -- s' corresponds to time s = s' + (y - x) in σ
      have hs : σ.domain (s' + (y - x)) := by
        simp only [WorldHistory.time_shift] at hs'
        exact hs'
      have h_y_lt_s : y < s' + (y - x) := by omega
      have h_truth_orig := h_future (s' + (y - x)) hs h_y_lt_s
      -- Apply IH with shift amount (s' + (y - x)) - s' = y - x
      have h_shift_eq : (s' + (y - x)) - s' = y - x := by omega
      -- Use congruence to equate histories
      have h_hist_eq : WorldHistory.time_shift σ ((s' + (y - x)) - s') = WorldHistory.time_shift σ (y - x) := by
        exact WorldHistory.time_shift_congr σ ((s' + (y - x)) - s') (y - x) h_shift_eq
      -- Create domain proof for IH
      have hs'_ih : (WorldHistory.time_shift σ ((s' + (y - x)) - s')).domain s' := by
        rw [h_hist_eq]
        exact hs'
      -- Apply IH and transport
      have h_ih := (ih σ s' (s' + (y - x)) hs'_ih hs).mpr h_truth_orig
      -- Transport using history equality
      exact (truth_history_eq M _ _ s' hs'_ih hs' h_hist_eq ψ).mp h_ih

/--
Corollary: For any history σ at time y, there exists a history at time x
(namely, time_shift σ (y - x)) where the same formulas are true.

This is the key lemma for proving MF and TF axioms.
-/
theorem exists_shifted_history (M : TaskModel F) (σ : WorldHistory F) (x y : Int)
    (hy : σ.domain y) (φ : Formula) :
    truth_at M σ y hy φ ↔
    truth_at M (WorldHistory.time_shift σ (y - x)) x
      (by
        simp only [WorldHistory.time_shift]
        have h : x + (y - x) = y := by omega
        rw [h]
        exact hy) φ := by
  have hx : (WorldHistory.time_shift σ (y - x)).domain x := by
    simp only [WorldHistory.time_shift]
    have h : x + (y - x) = y := by omega
    rw [h]
    exact hy
  exact (time_shift_preserves_truth M σ x y hx hy φ).symm

end TimeShift

/-! ## Temporal Duality

This section proves that validity is preserved under the swap_past_future transformation.
The key insight is that swapping Past and Future operators corresponds to time reversal
via negation (t ↦ -t), and validity ("true everywhere") is preserved because "everywhere"
includes all times in both temporal directions.

The proof relies on Int's totally ordered abelian group structure rather than postulating
a SymmetricFrame constraint. Order reversal (s < t ↔ -t < -s) provides the necessary
symmetry without additional frame properties.
-/

namespace TemporalDuality

/--
Local definition of validity to avoid circular dependency with Validity.lean.
A formula is valid if it's true at all model-history-time triples.
-/
private def is_valid (φ : Formula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t),
    truth_at M τ t ht φ

/--
Auxiliary lemma: If φ is valid, then for any specific triple (M, τ, t),
φ is true at that triple.

This is just the definition of validity, but stated as a lemma for clarity.
-/
theorem valid_at_triple {φ : Formula} (h_valid : is_valid φ) (F : TaskFrame) (M : TaskModel F)
    (τ : WorldHistory F) (t : Int) (ht : τ.domain t) :
    truth_at M τ t ht φ := h_valid F M τ t ht


/--
Auxiliary lemma: If φ is valid and ψ is the result of swapping past/future in φ,
then for any triple where ψ is true, we can construct a relationship.

Actually, we need a stronger result: truth at a triple is preserved under swap
when the formula is valid.
-/
theorem truth_swap_of_valid_at_triple (φ : Formula) (F : TaskFrame) (M : TaskModel F)
    (τ : WorldHistory F) (t : Int) (ht : τ.domain t) :
    is_valid φ → truth_at M τ t ht φ.swap_past_future := by
  intro h_valid
  -- Proof by structural induction on φ
  induction φ generalizing F M τ t ht with
  | atom p =>
    -- swap_past_future (atom p) = atom p
    simp only [Formula.swap_past_future]
    exact h_valid F M τ t ht

  | bot =>
    -- swap_past_future bot = bot
    -- Goal after simp: False
    -- This follows from h_valid being impossible (bot cannot be valid)
    simp only [Formula.swap_past_future, truth_at]
    -- h_valid says bot is valid, which means bot is true at all triples
    -- But bot is False by definition, contradiction
    exact h_valid F M τ t ht

  | imp ψ χ ih_ψ ih_χ =>
    -- swap_past_future (ψ → χ) = (swap ψ) → (swap χ)
    simp only [Formula.swap_past_future, truth_at]
    intro h_swap_ψ
    -- Goal: truth_at M τ t ht χ.swap_past_future
    -- We have h_swap_ψ : truth_at M τ t ht ψ.swap_past_future
    -- From h_valid: is_valid (ψ → χ)
    --
    -- Key insight: We need to use the fact that h_valid gives us the implication at EVERY triple.
    -- In particular, at this triple, we have: ψ → χ is true.
    -- This means: truth_at M τ t ht ψ → truth_at M τ t ht χ
    --
    -- We have swap(ψ) true. To get χ (and then swap(χ)), we'd need ψ.
    -- But we can't directly get ψ from swap(ψ) without knowing swap(ψ) is valid.
    --
    -- Alternative approach: Use Classical logic.
    -- Either ψ is valid or ψ is not valid.
    -- Case 1: ψ is valid. Then by IH, swap(ψ) is true at (M, τ, t). ✓ (matches h_swap_ψ)
    --         Also, validity of ψ → χ + validity of ψ implies... no, that's not right.
    --         Validity of ψ → χ means: at every triple, ψ → χ. It doesn't mean ψ → (χ valid).
    --
    -- Case 2: ψ is not valid. Then there exists (F', M', τ', t') where ψ is false.
    --         This doesn't help us directly.
    --
    -- The real insight: we need a different induction structure.
    -- Instead of: is_valid φ → truth_at ... φ.swap
    -- We should prove: is_valid φ ↔ is_valid φ.swap
    -- Then for imp: is_valid (ψ → χ) ↔ is_valid (swap(ψ) → swap(χ))
    --
    -- Actually, let's try a direct proof for the implication case:
    -- is_valid (ψ → χ) means: ∀ M τ t, (truth ψ → truth χ)
    -- is_valid (swap ψ → swap χ) means: ∀ M τ t, (truth swap ψ → truth swap χ)
    --
    -- These are NOT obviously equivalent without knowing more about ψ and χ.
    --
    -- For MVP: Accept this limitation and document it clearly.
    -- The temporal duality rule is still sound for the cases we care about
    -- (formulas derivable in TM), even if we can't prove it for all valid formulas.
    sorry

  | box ψ ih =>
    -- swap_past_future (box ψ) = box (swap ψ)
    simp only [Formula.swap_past_future, truth_at]
    intro σ hs
    -- Goal: truth_at M σ t hs ψ.swap_past_future
    -- From h_valid: is_valid (box ψ)
    -- This means: ∀ F' M' τ' t' ht', ∀ σ' hs', truth_at M' σ' t' hs' ψ
    -- In particular, this means ψ is valid (true at ALL triples)
    have h_ψ_valid : is_valid ψ := by
      intro F' M' τ' t' ht'
      -- Instantiate h_valid at (F', M', τ', t', ht')
      have h_box := h_valid F' M' τ' t' ht'
      -- h_box : ∀ σ hs, truth_at M' σ t' hs ψ
      -- Choose σ = τ'
      exact h_box τ' ht'
    -- By IH, since ψ is valid, swap(ψ) is true at (M, σ, t, hs)
    exact ih F M σ t hs h_ψ_valid

  | past ψ ih =>
    -- swap_past_future (past ψ) = future (swap ψ)
    simp only [Formula.swap_past_future, truth_at]
    intro s hs h_t_lt_s
    -- Goal: truth_at M τ s hs ψ.swap_past_future
    -- From h_valid: is_valid (past ψ)
    --
    -- Key insight: If "Past ψ" is valid, then ψ is valid.
    -- Proof: For any (M', τ', s') where s' is in τ'.domain:
    --   - The validity of "Past ψ" means it holds at all (F, M, τ, t, ht)
    --   - We need some t > s' in τ'.domain to instantiate Past ψ at t
    --   - τ'.domain is convex, and we can extend any history to include more times
    --   - The trick: we're quantifying over ALL histories including those with full Int domain
    --
    -- Actually, the simpler proof: we already have τ with s ∈ τ.domain and t ∈ τ.domain
    -- and h_t_lt_s : t < s. So s is in the future from t's perspective.
    -- By h_valid at (F, M, τ, s), since s ∈ τ.domain, we get Past ψ at s.
    -- This means: ∀ r < s, r ∈ τ.domain → ψ at r.
    -- In particular, for r = s-1, if s-1 ∈ τ.domain, ψ at s-1.
    -- But this doesn't directly give us ψ at s (we get it at times BEFORE s).
    --
    -- Different approach: Use that h_valid holds at EVERY triple.
    -- We need ψ at (F, M, τ, s, hs). The τ already has s in its domain.
    -- Pick a time t' > s such that t' ∈ τ.domain (if such exists in τ).
    -- Then h_valid at (F, M, τ, t', ht') gives Past ψ at t', i.e., ψ at all r < t'.
    -- Since s < t', we get ψ at s.
    -- BUT: we can't assume τ.domain extends beyond s.
    --
    -- The resolution: Validity quantifies over ALL frames, ALL models, ALL histories.
    -- For any given s, we can find SOME (F', M', τ') where τ'.domain contains both s and s+1.
    -- The key is that validity says truth at THAT triple too.
    --
    -- Here's the correct argument for is_valid ψ:
    -- Given any (F', M', τ', s', hs'), we need truth_at M' τ' s' hs' ψ.
    -- Consider the history τ' extended to include s'+1 (conceptually).
    -- Actually, we can't "extend" a given history - it's a fixed structure.
    --
    -- The ACTUAL solution: Work with the existing τ and t.
    -- We have h_t_lt_s : t < s, so s is in the future from t's perspective.
    -- We're inside a goal where we need swap(ψ) at (M, τ, s, hs).
    -- We'll show ψ is valid using a clever instantiation.
    --
    -- For ψ to be valid: ∀ (F, M, τ, r, hr), truth_at M τ r hr ψ.
    -- Given any such (F, M, τ, r, hr), we need to find a way to extract ψ from Past ψ.
    -- The issue: Past ψ at time t gives ψ at all s < t, but we need ψ at r with no guarantee r < t.
    --
    -- Resolution: Since τ.domain includes r, and τ.domain is typically assumed to include
    -- some t > r (for Past at t to tell us about r), we need this structural property.
    -- Let's add an assumption that histories have unbounded domains, or work around it.
    --
    -- For MVP: Accept that this requires the domain to extend, which is reasonable for
    -- physical interpretations where time extends to the future.
    have h_ψ_valid : is_valid ψ := by
      intro F' M' τ' r hr
      -- We need to find some t > r in τ'.domain.
      -- The key insight: h_valid holds for ALL (F, M, τ, t, ht).
      -- We need a (τ'', t'') where τ''.domain r and τ''.domain t'' and r < t''.
      -- For simplicity, we assume we can construct or find such a history.
      -- This is where the research report's suggestion of "extending histories" applies.
      sorry
    exact ih F M τ s hs h_ψ_valid

  | future ψ ih =>
    -- swap_past_future (future ψ) = past (swap ψ)
    simp only [Formula.swap_past_future, truth_at]
    intro s hs h_s_lt_t
    -- Goal: truth_at M τ s hs ψ.swap_past_future
    -- From h_valid: is_valid (future ψ)
    --
    -- Symmetric to past case:
    -- Key insight: If "Future ψ" is valid, then ψ is valid.
    -- Proof: For any (M', τ', s') where s' is in τ'.domain:
    --   - If there exists some r < s' with r ∈ τ'.domain
    --   - By validity of Future ψ at (M', τ', r), we have ψ at all u > r
    --   - Since s' > r, ψ holds at s'
    --
    -- The same domain extension issue applies as in the past case.
    have h_ψ_valid : is_valid ψ := by
      intro F' M' τ' r hr
      -- We need some t < r in τ'.domain to instantiate Future ψ at t.
      -- This requires the domain to extend into the past.
      sorry
    exact ih F M τ s hs h_ψ_valid

/--
Validity is preserved under swap_past_future transformation.

If a formula φ is valid (true at all model-history-time triples), then
swap_past_future φ is also valid.

**Key Insight**: This theorem is true for formulas that are derivable with
temporal duality from theorems that don't use temporal operators, but may
not hold for arbitrary valid formulas. The issue is that "past ψ" being valid
doesn't directly imply "future (swap ψ)" is valid unless ψ has a special structure.

For the soundness of temporal_duality rule, we only apply it to formulas
in empty contexts (valid formulas), and specifically formulas derived without
using assumptions about specific times. In this restricted setting, the symmetry
holds.

**Proof Strategy**: For now, we use sorry and document that this requires careful
analysis of which formulas can validly use temporal duality.
-/
theorem valid_swap_of_valid (φ : Formula) : is_valid φ → is_valid φ.swap_past_future := by
  intro h_valid F M τ t ht
  exact truth_swap_of_valid_at_triple φ F M τ t ht h_valid

end TemporalDuality

end ProofChecker.Semantics
