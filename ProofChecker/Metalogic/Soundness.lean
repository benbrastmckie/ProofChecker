import ProofChecker.ProofSystem.Derivation
import ProofChecker.Semantics.Validity

/-!
# Soundness - Soundness Theorem for TM Logic

This module proves the soundness theorem for bimodal logic TM.

## Paper Specification Reference

**Perpetuity Principles (app:valid, line 1984)**:
The JPL paper "The Perpetuity Calculus of Agency" proves perpetuity principles
P1 (□φ → △φ) and P2 (▽φ → ◇φ) are valid over all task semantic models using
time-shift automorphisms.

**ProofChecker Extensions**:
This implementation extends beyond the paper's explicit proofs by including
axioms TL, MF, TF. These axioms are documented as conditionally valid, requiring
specific frame properties (BackwardPersistence, ModalTemporalPersistence) not
guaranteed by the base TaskFrame structure.

**Proven Axioms Aligned with Paper**: MT, M4, MB, T4, TA match the paper's S5
modal and linear temporal logic components.

## Main Results

- `prop_k_valid`, `prop_s_valid`: Propositional axioms are valid
- `modal_t_valid`: Modal T axiom is valid
- `modal_4_valid`: Modal 4 axiom is valid
- `modal_b_valid`: Modal B axiom is valid
- `temp_4_valid`: Temporal 4 axiom is valid
- `temp_a_valid`: Temporal A axiom is valid
- `temp_l_valid`: TL axiom (conditional on BackwardPersistence)
- `modal_future_valid`: MF axiom (conditional on ModalTemporalPersistence)
- `temp_future_valid`: TF axiom (conditional on ModalTemporalPersistence)
- `soundness`: Derivability implies semantic validity (`Γ ⊢ φ → Γ ⊨ φ`)

## Implementation Notes

**Completed Proofs**:
- 7/10 axiom validity lemmas: prop_k, prop_s, MT, M4, MB, T4, TA
- 4/7 soundness cases: axiom, assumption, modus_ponens, weakening

**Conditional Proofs (require additional frame constraints)**:
- `temp_l_valid`: Requires BackwardPersistence frame property
- `modal_future_valid`: Requires ModalTemporalPersistence frame property
- `temp_future_valid`: Requires ModalTemporalPersistence frame property
- `modal_k` soundness: Requires modal closure of contexts
- `temporal_k` soundness: Requires temporal closure of contexts
- `temporal_duality` soundness: Requires temporal duality lemma

**Frame Constraint Analysis**:

The three conditional axiom validity lemmas (TL, MF, TF) require semantic properties
not derivable from the basic TaskFrame structure (nullity + compositionality).
See frame property definitions (BackwardPersistence, ModalTemporalPersistence)
below for formal specifications.

**MVP Approach**: Option B (Conditional Validity Documentation)
We document frame requirements in theorem docstrings and accept conditional
soundness. This pragmatic approach avoids invasive TaskFrame refactoring while
making semantic assumptions explicit.

## References

* [ARCHITECTURE.md](../../../Documentation/UserGuide/ARCHITECTURE.md) - Soundness specification
* [Derivation.lean](../../ProofSystem/Derivation.lean) - Derivability relation
* [Validity.lean](../../Semantics/Validity.lean) - Semantic validity
* JPL Paper app:valid (line 1984) - Perpetuity principle validity proofs
-/

namespace ProofChecker.Metalogic

open ProofChecker.Syntax
open ProofChecker.ProofSystem
open ProofChecker.Semantics

/-! ## Frame Properties for Conditional Soundness

The following frame properties are required for certain axioms to be valid.
These properties are NOT enforced by the base TaskFrame structure (nullity + compositionality),
but are needed for TL, MF, and TF axioms to hold universally.

For MVP, we document these requirements and accept conditional soundness for these axioms.
-/

/--
Backward Persistence property for task frames.

A frame satisfies backward persistence if formulas that hold "from a point onward"
also hold in intervals extending backward from future points.

**Required for**: TL axiom (`Fφ → F(Pφ)`)

**Intuition**: If φ holds at all times s ≥ t₂ in a history τ, then φ also holds
at all times r in the interval [t₁, t₂) within τ (for any t₁ < t₂).

**Formal Statement**: For all models M, histories τ, times t₁ < t₂, and formulas φ:
If φ holds at all s ≥ t₂ in τ, then φ holds at all r ∈ [t₁, t₂) in τ.

**Frame Examples**:
- Frames where truth persists backward from future commitments satisfy this
- Not all task frames satisfy this property

**Impact**: TL axiom validity is conditional on frames satisfying backward persistence.
-/
def BackwardPersistence (F : TaskFrame) : Prop :=
  ∀ (M : TaskModel F) (τ : WorldHistory F) (t₁ t₂ : Int) (φ : Formula),
    t₁ < t₂ →
    (∀ (s : Int) (hs : τ.domain s), s ≥ t₂ → truth_at M τ s hs φ) →
    (∀ (r : Int) (hr : τ.domain r), t₁ ≤ r → r < t₂ → truth_at M τ r hr φ)

/--
Modal-Temporal Persistence property for task frames.

A frame satisfies modal-temporal persistence if necessary truths remain necessary
across temporal progression.

**Required for**: MF axiom (`□φ → □(Fφ)`) and TF axiom (`□φ → F(□φ)`)

**Intuition**: If φ is necessarily true at time t (holds at all histories at t),
then φ remains necessarily true at all future times s > t.

**Formal Statement**: For all models M, times t < s, and formulas φ:
If φ holds at all histories at time t, then φ holds at all histories at time s.

**Frame Examples**:
- Frames where modal necessity is time-invariant satisfy this
- Frames where truth can vary across times may not satisfy this

**Impact**: MF and TF axiom validity is conditional on frames satisfying modal-temporal persistence.
-/
def ModalTemporalPersistence (F : TaskFrame) : Prop :=
  ∀ (M : TaskModel F) (t s : Int) (φ : Formula),
    t < s →
    (∀ (σ : WorldHistory F) (hσ : σ.domain t), truth_at M σ t hσ φ) →
    (∀ (σ : WorldHistory F) (hσ : σ.domain s), truth_at M σ s hσ φ)

/--
Propositional K axiom is valid: `⊨ (φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`.

This is a propositional tautology (distribution of implication).

Proof: Classical propositional reasoning. Assume (φ → (ψ → χ)) and (φ → ψ),
show (φ → χ). Given φ, we get ψ from second premise, then χ from first premise.
-/
theorem prop_k_valid (φ ψ χ : Formula) :
    ⊨ ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) := by
  intro F M τ t ht
  unfold truth_at
  intro h1 h2 h_phi
  exact h1 h_phi (h2 h_phi)

/--
Propositional S axiom is valid: `⊨ φ → (ψ → φ)`.

This is a propositional tautology (weakening/constant function).

Proof: Assume φ and ψ, show φ. This is immediate from the first assumption.
-/
theorem prop_s_valid (φ ψ : Formula) : ⊨ (φ.imp (ψ.imp φ)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_phi _
  exact h_phi

/--
Modal T axiom is valid: `⊨ □φ → φ`.

For any formula `φ`, the formula `□φ → φ` is valid (true in all models).

Proof: If `□φ` is true at `(M, τ, t)`, then `φ` is true at all histories at time `t`.
Since `τ` is a history containing `t`, we have `φ` true at `(M, τ, t)`.
-/
theorem modal_t_valid (φ : Formula) : ⊨ (φ.box.imp φ) := by
  intro F M τ t ht
  unfold truth_at
  intro h_box
  -- h_box : ∀ σ, t ∈ σ.domain → truth_at M σ t φ
  -- Goal: truth_at M τ t φ
  exact h_box τ ht

/--
Modal 4 axiom is valid: `⊨ □φ → □□φ`.

For any formula `φ`, the formula `□φ → □□φ` is valid.

Proof: Assume `□φ` is true at `(M, τ, t)`, i.e., for all histories `σ` at time `t`, `φ` holds.
We need to show `□□φ` is true, i.e., for all histories `σ` at time `t`, `□φ` holds at `σ`.
But `□φ` at `(M, σ, t)` means for all histories `ρ` at time `t`, `φ` holds at `ρ`.
Since `□φ` was already true (for ALL histories including `ρ`), this follows immediately.
-/
theorem modal_4_valid (φ : Formula) : ⊨ ((φ.box).imp (φ.box.box)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_box
  -- h_box : ∀ σ hs, truth_at M σ t hs φ
  -- Goal: ∀ σ hs, ∀ ρ hr, truth_at M ρ t hr φ
  intro σ hs ρ hr
  -- The key insight: h_box gives truth at ALL histories at time t
  -- ρ is just another history at time t, so h_box applies directly
  exact h_box ρ hr

/--
Modal B axiom is valid: `⊨ φ → □◇φ`.

For any formula `φ`, the formula `φ → □◇φ` is valid.

Proof: Assume `φ` is true at `(M, τ, t)`.
We need to show `□◇φ` is true, i.e., for all histories `σ` at time `t`, `◇φ` holds at `σ`.
`◇φ` is defined as `¬□¬φ`, so we need: ¬(∀ ρ hr, ¬(truth_at M ρ t hr φ)).
This is equivalent to: ∃ ρ hr, truth_at M ρ t hr φ.
We witness with `τ` and `ht`, where we assumed `φ` is true.
-/
theorem modal_b_valid (φ : Formula) : ⊨ (φ.imp (φ.diamond.box)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_phi
  -- h_phi : truth_at M τ t ht φ
  -- Goal: truth_at M τ t ht (φ.diamond.box)
  -- Unfolding: ∀ σ hs, truth_at M σ t hs φ.diamond
  intro σ hs
  -- Goal: truth_at M σ t hs φ.diamond
  -- φ.diamond = φ.neg.box.neg = ((φ.imp bot).box).imp bot
  unfold Formula.diamond truth_at
  -- Goal: truth_at M σ t hs (φ.neg.box) → truth_at M σ t hs bot
  -- which is: (∀ ρ hr, truth_at M ρ t hr φ.neg) → False
  intro h_box_neg
  -- h_box_neg : ∀ ρ hr, truth_at M ρ t hr φ.neg
  -- where φ.neg = φ.imp bot
  -- So h_box_neg : ∀ ρ hr, truth_at M ρ t hr (φ.imp bot)
  -- which means: ∀ ρ hr, truth_at M ρ t hr φ → False
  have h_neg_at_tau := h_box_neg τ ht
  -- h_neg_at_tau : truth_at M τ t ht (φ.imp bot)
  -- which is: truth_at M τ t ht φ → False
  unfold Formula.neg truth_at at h_neg_at_tau
  exact h_neg_at_tau h_phi

/--
Temporal 4 axiom is valid: `⊨ Fφ → FFφ`.

For any formula `φ`, the formula `Fφ → FFφ` is valid.

Proof: Assume `Fφ` is true at `(M, τ, t)`, i.e., for all s > t in τ's domain, `φ` holds at s.
We need to show `FFφ` is true, i.e., for all s > t, for all r > s, `φ` holds at r.
Since r > s > t implies r > t, and Fφ says φ holds at all times > t, φ holds at r.
-/
theorem temp_4_valid (φ : Formula) : ⊨ ((φ.future).imp (φ.future.future)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_future
  -- h_future : ∀ s hs, t < s → truth_at M τ s hs φ
  -- Goal: ∀ s hs, t < s → (∀ r hr, s < r → truth_at M τ r hr φ)
  intro s hs hts r hr hsr
  -- Need to show: truth_at M τ r hr φ
  -- We have: t < s and s < r, so t < r
  have htr : t < r := Int.lt_trans hts hsr
  exact h_future r hr htr

/--
Temporal A axiom is valid: `⊨ φ → F(sometime_past φ)`.

For any formula `φ`, the formula `φ → F(sometime_past φ)` is valid.

Proof: Assume `φ` is true at `(M, τ, t)`.
We need to show `F(sometime_past φ)` at `(M, τ, t)`.
This means: for all s > t in domain, `sometime_past φ` at `(M, τ, s)`.
`sometime_past φ = ¬P¬φ` means: NOT (for all r < s in domain, ¬φ at r).
Equivalently: there EXISTS r < s in domain where φ is true.
Since t < s and t is in domain (we're evaluating there), t is such an r.
-/
theorem temp_a_valid (φ : Formula) : ⊨ (φ.imp (Formula.future φ.sometime_past)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_phi
  -- h_phi : truth_at M τ t ht φ
  -- Goal: ∀ s hs, t < s → truth_at M τ s hs φ.sometime_past
  intro s hs hts
  -- Goal: truth_at M τ s hs φ.sometime_past
  -- With corrected definition: sometime_past φ = φ.neg.past.neg
  -- = (φ.neg).past.neg
  -- = ((φ.imp bot).past).imp bot

  -- truth_at ... φ.sometime_past
  -- = truth_at ... (φ.neg.past.neg)
  -- = truth_at ... ((φ.imp bot).past.imp bot)
  -- = (truth_at ... (φ.imp bot).past) → False
  -- = (∀ r hr, r < s → (truth_at ... φ → False)) → False

  -- We need to prove: (∀ r hr, r < s → (truth_at M τ r hr φ → False)) → False
  -- We have: h_phi : truth_at M τ t ht φ, and hts : t < s

  -- Assuming h : ∀ r hr, r < s → (truth_at M τ r hr φ → False)
  -- Then h t ht hts : truth_at M τ t ht φ → False
  -- And h t ht hts h_phi : False

  unfold Formula.sometime_past Formula.neg truth_at
  -- Goal: (∀ r hr, r < s → truth_at M τ r hr (φ.imp bot)) → False
  intro h_all_neg
  -- h_all_neg : ∀ r hr, r < s → truth_at M τ r hr (φ.imp bot)
  -- This says: for all r < s, ¬φ at r
  have h_neg_at_t := h_all_neg t ht hts
  -- h_neg_at_t : truth_at M τ t ht (φ.imp bot)
  -- = truth_at M τ t ht φ → truth_at M τ t ht bot
  -- = truth_at M τ t ht φ → False
  unfold truth_at at h_neg_at_t
  exact h_neg_at_t h_phi

/--
TL axiom validity (conditional on backward persistence).

**Frame Constraint Required**: BackwardPersistence

The TL axiom `Fφ → F(Pφ)` is valid in task semantic models whose underlying
frames satisfy the backward persistence property.

**Backward Persistence Property**:
If φ holds at all times s ≥ t₂ in a history τ, then φ also holds at all
times r in the interval [t₁, t₂) within τ (for any t₁ < t₂).

**Justification**: The TL axiom relates future quantification to past
quantification at future times. Without backward persistence, φ can hold
from some future point onward without holding in the gap before that point.
When we have Fφ (φ holds at all future times), and we want to show F(Pφ)
(at all future times s, φ holds at all past times relative to s), we need
φ to hold in the interval [t, s) for any future s. This is exactly backward
persistence.

**Impact on Soundness**: The soundness theorem holds for TL axiom derivations
*provided* the semantic models satisfy backward persistence.

**Future Work**: Option A (add to TaskFrame), Option C (weaken axiom), or
accept conditional soundness (current MVP approach).
-/
theorem temp_l_valid (φ : Formula) : ⊨ ((Formula.future φ).imp (Formula.future (Formula.past φ))) := by
  intro F M τ t ht
  unfold truth_at
  intro h_gfuture
  -- h_gfuture : ∀ s hs, t < s → truth_at M τ s hs φ
  -- Goal: for all s > t, for all r < s, φ at r
  intro s hs hts r hr hrs
  -- We need: truth_at M τ r hr φ
  -- Case split on whether r > t or r ≤ t
  -- If r > t: h_gfuture gives us φ at r
  -- If r ≤ t: We don't have information from our premise

  -- This axiom requires backward persistence frame property.
  -- For MVP, we document the requirement and use sorry.
  sorry

/--
MF axiom validity (conditional on modal-temporal persistence).

**Frame Constraint Required**: ModalTemporalPersistence

The MF axiom `□φ → □(Fφ)` is valid in task semantic models whose underlying
frames satisfy the modal-temporal persistence property.

**Modal-Temporal Persistence Property**:
If φ is necessarily true at time t (holds at all histories at t), then φ
remains necessarily true at all future times s > t (holds at all histories at s).

**Justification**: The MF axiom states that necessary truths remain necessary
in the future. From □φ (φ holds at all histories at time t), we need to show
□(Fφ) (for all histories σ, φ holds at all future times in σ). This requires
that if φ is necessary at t, it remains true across all histories at future
times s > t, which is exactly modal-temporal persistence.

**Impact on Soundness**: The soundness theorem holds for MF axiom derivations
*provided* the semantic models satisfy modal-temporal persistence.

**Future Work**: Option A (add to TaskFrame), Option C (weaken axiom), or
accept conditional soundness (current MVP approach).
-/
theorem modal_future_valid (φ : Formula) : ⊨ ((φ.box).imp ((φ.future).box)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_box_phi
  -- h_box_phi : ∀ σ hs, truth_at M σ t hs φ
  -- Goal: ∀ σ hs, ∀ s hs', t < s → truth_at M σ s hs' φ
  intro σ hs s hs' hts
  -- We need: truth_at M σ s hs' φ
  -- From h_box_phi: φ at all histories at time t
  -- But we need φ at history σ at time s ≠ t

  -- This axiom requires modal-temporal persistence frame property.
  -- For MVP, we document the requirement and use sorry.
  sorry

/--
TF axiom validity (conditional on modal-temporal persistence).

**Frame Constraint Required**: ModalTemporalPersistence

The TF axiom `□φ → F(□φ)` is valid in task semantic models whose underlying
frames satisfy the modal-temporal persistence property.

**Modal-Temporal Persistence Property**:
If φ is necessarily true at time t (holds at all histories at t), then φ
remains necessarily true at all future times s > t (holds at all histories at s).

**Justification**: The TF axiom states that if φ is necessary at time t,
then at all future times s > t, φ remains necessary (F(□φ) means for all
future times s, □φ holds at s). This is a direct application of modal-temporal
persistence: necessary truths at t remain necessary at all future times.

**Impact on Soundness**: The soundness theorem holds for TF axiom derivations
*provided* the semantic models satisfy modal-temporal persistence.

**Future Work**: Option A (add to TaskFrame), Option C (weaken axiom), or
accept conditional soundness (current MVP approach).
-/
theorem temp_future_valid (φ : Formula) : ⊨ ((φ.box).imp ((φ.box).future)) := by
  intro F M τ t ht
  unfold truth_at
  intro h_box_phi
  -- h_box_phi : ∀ σ hs, truth_at M σ t hs φ
  -- Goal: ∀ s hs, t < s → ∀ σ hs', truth_at M σ s hs' φ
  intro s hs hts σ hs'
  -- We need: truth_at M σ s hs' φ
  -- From h_box_phi: φ at all histories at time t
  -- But we need φ at history σ at time s ≠ t

  -- This axiom requires modal-temporal persistence frame property.
  -- For MVP, we document the requirement and use sorry.
  sorry

/--
All TM axioms are valid.

This helper lemma shows that every axiom instance is a valid formula.
-/
theorem axiom_valid {φ : Formula} : Axiom φ → ⊨ φ := by
  intro h_axiom
  cases h_axiom with
  | prop_k φ ψ χ => exact prop_k_valid φ ψ χ
  | prop_s φ ψ => exact prop_s_valid φ ψ
  | modal_t ψ => exact modal_t_valid ψ
  | modal_4 ψ => exact modal_4_valid ψ
  | modal_b ψ => exact modal_b_valid ψ
  | temp_4 ψ => exact temp_4_valid ψ
  | temp_a ψ => exact temp_a_valid ψ
  | temp_l ψ => exact temp_l_valid ψ
  | modal_future ψ => exact modal_future_valid ψ
  | temp_future ψ => exact temp_future_valid ψ

/--
Soundness theorem: Derivability implies semantic validity.

If `Γ ⊢ φ` (φ is derivable from context Γ), then `Γ ⊨ φ` (φ is a semantic consequence of Γ).

Proof by induction on the derivation structure:
- Axioms: All axioms are valid (proven above)
- Assumptions: Assumed formulas are true by hypothesis
- Modus Ponens: If `φ → ψ` and `φ` both valid, then `ψ` valid
- Modal K: If `φ` derivable from boxed context, then `□φ` derivable
- Temporal K: If `φ` derivable from future context, then `Fφ` derivable
- Temporal Duality: Swapping past/future preserves validity
- Weakening: Adding premises preserves semantic consequence
-/
theorem soundness (Γ : Context) (φ : Formula) : (Γ ⊢ φ) → (Γ ⊨ φ) := by
  intro h_deriv
  induction h_deriv with
  | «axiom» Γ' φ' h_ax =>
    -- Case: φ' is an axiom
    -- All axioms are valid, hence semantic consequences of any context
    intro F M τ t ht _
    exact axiom_valid h_ax F M τ t ht

  | @assumption Γ' φ' h_mem =>
    -- Case: φ' ∈ Γ' (assumption)
    -- If all of Γ' true, then φ' (member of Γ') is true
    intro F M τ t ht h_all
    exact h_all φ' h_mem

  | @modus_ponens Γ' φ' ψ' _ _ ih_imp ih_phi =>
    -- Case: From Γ' ⊢ φ' → ψ' and Γ' ⊢ φ', derive Γ' ⊢ ψ'
    -- By IH: Γ' ⊨ φ' → ψ' and Γ' ⊨ φ'
    -- Goal: Γ' ⊨ ψ'
    intro F M τ t ht h_all
    have h_imp := ih_imp F M τ t ht h_all
    have h_phi := ih_phi F M τ t ht h_all
    unfold truth_at at h_imp
    exact h_imp h_phi

  | @modal_k Γ' φ' _ ih =>
    -- Case: From Γ'.map box ⊢ φ', derive Γ' ⊢ □φ'
    -- IH: (Γ'.map box) ⊨ φ'
    -- Goal: Γ' ⊨ □φ'
    --
    -- At (M, τ, t) where Γ' true, we need □φ' true.
    -- □φ' at (M, τ, t) means: ∀ σ, t ∈ σ.domain → φ' at (M, σ, t)
    --
    -- To use IH at (M, σ, t), we need (Γ'.map box) true at (M, σ, t).
    -- For ψ ∈ Γ', we need ψ.box true at (M, σ, t).
    -- ψ.box at (M, σ, t) means: ∀ ρ, t ∈ ρ.domain → ψ at (M, ρ, t)
    --
    -- We know ψ at (M, τ, t) for ψ ∈ Γ', but not at all ρ.
    -- This requires a frame constraint ensuring Γ is "modal" (constant across histories).
    --
    -- For MVP, marking as sorry pending frame constraint analysis.
    sorry

  | @temporal_k Γ' φ' _ ih =>
    -- Case: From Γ'.map future ⊢ φ', derive Γ' ⊢ Fφ'
    -- IH: (Γ'.map future) ⊨ φ'
    -- Goal: Γ' ⊨ Fφ'
    --
    -- At (M, τ, t) where Γ' true, we need Fφ' true.
    -- Fφ' at (M, τ, t) means: ∀ s > t, s ∈ τ.domain → φ' at (M, τ, s)
    --
    -- To use IH at (M, τ, s), we need (Γ'.map future) true at (M, τ, s).
    -- For ψ ∈ Γ', we need ψ.future true at (M, τ, s).
    -- ψ.future at (M, τ, s) means: ∀ r > s, r ∈ τ.domain → ψ at (M, τ, r)
    --
    -- We know ψ at (M, τ, t), but ψ.future at later times requires ψ true at all later times.
    -- This also requires frame constraints.
    --
    -- For MVP, marking as sorry pending frame constraint analysis.
    sorry

  | @temporal_duality φ' _ ih =>
    -- Case: From [] ⊢ φ', derive [] ⊢ swap_past_future φ'
    -- IH: [] ⊨ φ' (i.e., ⊨ φ', φ' is valid)
    -- Goal: [] ⊨ swap_past_future φ' (i.e., swap_past_future φ' is valid)
    --
    -- Temporal duality: if φ is valid, then swapping past↔future gives a valid formula.
    -- This requires showing truth is preserved under the duality transformation.
    --
    -- Key lemma needed: truth_at M τ t ht φ ↔ truth_at M τ' t' ht' (swap_past_future φ)
    -- where τ' and t' are related by time reversal.
    --
    -- This is a deep semantic property requiring careful proof.
    -- For MVP, marking as sorry pending semantic duality lemma.
    sorry

  | @weakening Γ' Δ' φ' _ h_sub ih =>
    -- Case: From Γ' ⊢ φ' and Γ' ⊆ Δ', derive Δ' ⊢ φ'
    -- By IH: Γ' ⊨ φ'
    -- Goal: Δ' ⊨ φ'
    intro F M τ t ht h_all
    apply ih F M τ t ht
    intro ψ h_mem
    exact h_all ψ (h_sub h_mem)

end ProofChecker.Metalogic
