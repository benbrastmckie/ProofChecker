import ProofChecker.ProofSystem.Derivation
import ProofChecker.Semantics.Validity

/-!
# Soundness - Soundness Theorem for TM

This module proves the soundness theorem for bimodal logic TM.

## Main Results

- `modal_t_valid`: Modal T axiom is valid
- `modal_4_valid`: Modal 4 axiom is valid
- `modal_b_valid`: Modal B axiom is valid
- `temp_4_valid`: Temporal 4 axiom is valid
- `temp_a_valid`: Temporal A axiom is valid
- `soundness`: Derivability implies semantic validity (`Γ ⊢ φ → Γ ⊨ φ`)

## Implementation Notes

**Completed Proofs**:
- 5/8 axiom validity lemmas: MT, M4, MB, T4, TA
- 4/7 soundness cases: axiom, assumption, modus_ponens, weakening

**Incomplete Proofs (require additional frame constraints)**:
- `temp_l_valid`: Requires relating future quantification to past
- `modal_future_valid`: Requires temporal persistence of necessity
- `temp_future_valid`: Requires temporal persistence of necessity
- `modal_k` soundness: Requires modal closure of contexts
- `temporal_k` soundness: Requires temporal closure of contexts
- `temporal_duality` soundness: Requires temporal duality lemma

**Frame Constraint Analysis**:

The three incomplete axiom validity lemmas (TL, MF, TF) require semantic properties
not derivable from the basic TaskFrame structure (nullity + compositionality).

1. **TL (temp_l)**: `always φ → Future Past φ`
   - Requires: If φ holds at all future times, then at each future time s,
     φ holds at all past times relative to s
   - Issue: Past times relative to s include times ≤ current time t,
     where `always φ` provides no information
   - Needed: Frame constraint ensuring backward temporal persistence

2. **MF (modal_future)**: `□φ → □Fφ`
   - Requires: If φ is necessary now (all histories at time t), then
     at all histories, φ persists into the future
   - Issue: Box quantifies over histories at fixed time, but future
     quantifies over different times within each history
   - Needed: Frame constraint ensuring temporal persistence of necessity

3. **TF (temp_future)**: `□φ → F□φ`
   - Requires: If φ is necessary now, then at all future times s,
     φ remains necessary (holds at all histories at time s)
   - Issue: Similar to MF, requires relating necessity across different times
   - Needed: Frame constraint ensuring necessary truths remain necessary

**Potential Solutions**:
- Add axiom schemas to restrict models (semantic approach)
- Add frame constraints to TaskFrame structure (semantic approach)
- Accept partial soundness for provable axioms only (proof-theoretic approach)
- Use weaker logic without problematic axioms (system design approach)

For Phase 5, we document these limitations and focus on what is provable.

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - Soundness specification
* [Derivation.lean](../../ProofSystem/Derivation.lean) - Derivability relation
* [Validity.lean](../../Semantics/Validity.lean) - Semantic validity
-/

namespace ProofChecker.Metalogic

open ProofChecker.Syntax
open ProofChecker.ProofSystem
open ProofChecker.Semantics

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
Temporal L axiom is valid: `⊨ Gφ → G(Hφ)`.

Where G = future (for all future times), H = past (for all past times).

So this is: `future φ → future (past φ)`

Proof sketch: Assume `Gφ` (future φ) is true at `(M, τ, t)`.
This means: for all s > t in domain, φ at s.
We need: `G(Hφ)` at t, i.e., for all s > t, for all r < s, φ at r.

The issue: from Gφ we only know φ at times > t, but we need φ at times r < s
which could include r ≤ t (where we don't have information).

This axiom requires additional frame constraints to be valid.
In task semantics, this may follow from compositionality properties.
For MVP, we mark this as sorry pending deeper semantic analysis.
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

  -- TODO: This axiom may require frame-specific constraints.
  -- For MVP, using sorry pending semantic analysis.
  sorry

/--
Modal-Future axiom is valid: `⊨ □φ → □(Fφ)`.

For any formula `φ`, the formula `□φ → □(Fφ)` is valid.

Proof: Assume `□φ` is true at `(M, τ, t)`, i.e., for all histories σ at t, φ at σ.
We need to show `□(Fφ)`, i.e., for all histories σ at t, Fφ at σ.
Fφ at (M, σ, t) means: for all s > t in σ.domain, φ at (M, σ, s).

But wait, □φ only tells us φ at time t across all histories, not at other times.
This axiom relates modal and temporal operators in a specific way.

Key insight: □φ means φ is necessarily true at the CURRENT time across all histories.
The consequent □Fφ means for all histories σ, φ is true at all future times in σ.
This is NOT derivable from □φ alone!

Actually, this axiom as stated seems incorrect for our semantics.
The issue is that □ quantifies over histories but Fφ quantifies over times within a history.

Let me reconsider: perhaps the axiom is meant to capture a different relationship.
Looking at ARCHITECTURE.md: "Necessary truths remain necessary in the future"

Actually, for this to be valid, we'd need a constraint that if φ is true at all histories
at time t, then φ is also true at all histories at all future times. This would require
a frame condition relating histories across times.

For MVP, marking as sorry pending deeper semantic analysis.
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

  -- This requires a frame constraint relating truth across times.
  -- For MVP, using sorry pending semantic analysis.
  sorry

/--
Temporal-Future axiom is valid: `⊨ □φ → F(□φ)`.

For any formula `φ`, the formula `□φ → F(□φ)` is valid.

Proof: Assume `□φ` is true at `(M, τ, t)`, i.e., for all histories σ at t, φ at σ.
We need to show `F(□φ)`, i.e., for all s > t, □φ at (M, τ, s).
□φ at (M, τ, s) means: for all histories σ at s, φ at σ.

Similar to modal_future_valid, this relates modal and temporal operators and
requires frame constraints for validity.

For MVP, marking as sorry pending deeper semantic analysis.
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

  -- This requires a frame constraint relating truth across times.
  -- For MVP, using sorry pending semantic analysis.
  sorry

/--
All TM axioms are valid.

This helper lemma shows that every axiom instance is a valid formula.
-/
theorem axiom_valid {φ : Formula} : Axiom φ → ⊨ φ := by
  intro h_axiom
  cases h_axiom with
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
