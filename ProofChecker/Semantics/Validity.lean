import ProofChecker.Semantics.Truth
import ProofChecker.Syntax.Context

/-!
# Validity - Semantic Validity and Consequence

This module defines semantic validity and consequence for TM formulas.

## Main Definitions

- `valid`: A formula is valid if true in all models
- `semantic_consequence`: Semantic consequence relation
- `satisfiable`: A context is satisfiable if consistent
- Notation: `⊨ φ` for validity, `Γ ⊨ φ` for semantic consequence

## Main Results

- Basic validity lemmas
- Relationship between validity and semantic consequence

## Implementation Notes

- Validity quantifies over all frames, models, histories, and times
- Semantic consequence: truth in all models where premises true
- Used in soundness theorem: `Γ ⊢ φ → Γ ⊨ φ`
- Times are Int for MVP

## References

* [ARCHITECTURE.md](../../../docs/ARCHITECTURE.md) - Validity specification
* [Truth.lean](Truth.lean) - Truth evaluation
* [Context.lean](../Syntax/Context.lean) - Proof contexts
-/

namespace ProofChecker.Semantics

open ProofChecker.Syntax

/--
A formula is valid if it is true in all models at all times in all histories.

Formally: for every task frame `F`, every model `M` over `F`, every world history `τ`,
every time `t` where `τ.domain t`, the formula is true at `(M, τ, t)`.
-/
def valid (φ : Formula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t),
    truth_at M τ t ht φ

/--
Notation for validity: `⊨ φ` means `valid φ`.
-/
notation:50 "⊨ " φ:50 => valid φ

/--
Semantic consequence: `Γ ⊨ φ` means φ is true in all models where all of `Γ` are true.

Formally: for every model-history-time where all formulas in `Γ` are true,
formula `φ` is also true.
-/
def semantic_consequence (Γ : Context) (φ : Formula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t),
    (∀ ψ ∈ Γ, truth_at M τ t ht ψ) →
    truth_at M τ t ht φ

/--
Notation for semantic consequence: `Γ ⊨ φ`.
-/
notation:50 Γ:50 " ⊨ " φ:50 => semantic_consequence Γ φ

/--
A context is satisfiable if there exists a model where all formulas in the context are true.

This is the semantic notion of consistency.
-/
def satisfiable (Γ : Context) : Prop :=
  ∃ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F) (t : Int) (ht : τ.domain t),
    ∀ φ ∈ Γ, truth_at M τ t ht φ

namespace Validity

/--
Valid formulas are semantic consequences of empty context.
-/
theorem valid_iff_empty_consequence (φ : Formula) :
    (⊨ φ) ↔ ([] ⊨ φ) := by
  constructor
  · intro h F M τ t ht _
    exact h F M τ t ht
  · intro h F M τ t ht
    exact h F M τ t ht (by intro ψ hψ; exact absurd hψ (List.not_mem_nil ψ))

/--
Semantic consequence is monotonic: adding premises preserves consequences.
-/
theorem consequence_monotone {Γ Δ : Context} {φ : Formula} :
    Γ ⊆ Δ → (Γ ⊨ φ) → (Δ ⊨ φ) := by
  intro h_sub h_cons F M τ t ht h_delta
  apply h_cons F M τ t ht
  intro ψ hψ
  exact h_delta ψ (h_sub hψ)

/--
If a formula is valid, it is a semantic consequence of any context.
-/
theorem valid_consequence (φ : Formula) (Γ : Context) :
    (⊨ φ) → (Γ ⊨ φ) := by
  intro h F M τ t ht _
  exact h F M τ t ht

/--
Context with all formulas true implies each formula individually true.
-/
theorem consequence_of_member {Γ : Context} {φ : Formula} :
    φ ∈ Γ → (Γ ⊨ φ) := by
  intro h F M τ t ht h_all
  exact h_all φ h

/--
Unsatisfiable context semantically implies anything.
-/
theorem unsatisfiable_implies_all {Γ : Context} {φ : Formula} :
    ¬satisfiable Γ → (Γ ⊨ φ) := by
  intro h_unsat F M τ t ht h_all
  exfalso
  apply h_unsat
  exact ⟨F, M, τ, t, ht, h_all⟩

end Validity

end ProofChecker.Semantics
