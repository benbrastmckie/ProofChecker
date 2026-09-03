/-
Probes for the stability modal `⊡` over task frames (research evidence of record).

Every declaration below is sorry-free and compiles against the live tree with
`lake env lean specs/535_axiomatize_stability_modal_tm_star/probes/01_stab-axiom-probes.lean`.
Each probe's docstring states what it establishes. Parts A and the T/4/5/`□→⊡`/atom-stability
validities reuse the prototype compiled for the L⋆ metatheory research; the new content is
Parts B (state-invariance and `□⊡ ↔ □`), C (history pasting and the three pasting validities
that the naive axiom set cannot derive), D (refutations on the permissive frame over ℤ) and E
(`⊡φ` depends on the world state alone, not on the time — the "atomization" fact).
-/
import FormalSystem.Semantics.Truth
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.SuccPred

open FormalSystem.Syntax FormalSystem.Semantics
open scoped Classical

namespace Scratch535

/-! ## Part A: L⋆ syntax and semantics (reused prototype) -/

inductive StarFormula : Type where
  | atom : Atom → StarFormula
  | bot : StarFormula
  | imp : StarFormula → StarFormula → StarFormula
  | box : StarFormula → StarFormula
  | untl : StarFormula → StarFormula → StarFormula
  | snce : StarFormula → StarFormula → StarFormula
  | stab : StarFormula → StarFormula
  deriving Repr, DecidableEq

variable {F : TaskFrame}

/-- `σ ∈ ⟨τ⟩_x` (paper line 1108): same world state at `t`. -/
def SameStateAt (τ σ : WorldHistory F) (t : F.Duration) : Prop :=
  ∀ (hτ : τ.domain t) (hσ : σ.domain t), τ.states t hτ = σ.states t hσ

/-- Paper line 1114: the `stab` clause quantifies over total histories in `⟨τ⟩_t`. -/
def StarTruthAt (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) : StarFormula → Prop
  | .atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | .bot => False
  | .imp φ ψ => StarTruthAt M τ t φ → StarTruthAt M τ t ψ
  | .box φ => ∀ (σ : WorldHistory F), σ.IsTotal → StarTruthAt M σ t φ
  | .untl ψ φ => ∃ s : F.Duration, t < s ∧ StarTruthAt M τ s φ ∧
      ∀ r : F.Duration, t < r → r < s → StarTruthAt M τ r ψ
  | .snce ψ φ => ∃ s : F.Duration, s < t ∧ StarTruthAt M τ s φ ∧
      ∀ r : F.Duration, s < r → r < t → StarTruthAt M τ r ψ
  | .stab φ => ∀ (σ : WorldHistory F), σ.IsTotal → SameStateAt τ σ t → StarTruthAt M σ t φ

def StarValid (φ : StarFormula) : Prop :=
  ∀ (F : TaskFrame) (M : TaskModel F) (τ : WorldHistory F), τ.IsTotal →
    ∀ t : F.Duration, StarTruthAt M τ t φ

namespace StarFormula
def neg (φ : StarFormula) : StarFormula := .imp φ .bot
def top : StarFormula := .imp .bot .bot
def conj (φ ψ : StarFormula) : StarFormula := neg (.imp φ (neg ψ))
/-- `⟐φ := ¬⊡¬φ` (paper line 1121). -/
def dstab (φ : StarFormula) : StarFormula := neg (.stab (neg φ))
def someFuture (φ : StarFormula) : StarFormula := .untl top φ
def allFuture (φ : StarFormula) : StarFormula := neg (someFuture (neg φ))
def somePast (φ : StarFormula) : StarFormula := .snce top φ
def allPast (φ : StarFormula) : StarFormula := neg (somePast (neg φ))
end StarFormula

open StarFormula

theorem atom_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (p : Atom) :
    StarTruthAt M τ t (.atom p) ↔ ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p := Iff.rfl

theorem conj_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ ψ : StarFormula) :
    StarTruthAt M τ t (conj φ ψ) ↔ StarTruthAt M τ t φ ∧ StarTruthAt M τ t ψ := by
  simp [conj, neg, StarTruthAt]

theorem dstab_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (dstab φ) ↔
      ∃ σ : WorldHistory F, σ.IsTotal ∧ SameStateAt τ σ t ∧ StarTruthAt M σ t φ := by
  simp [dstab, neg, StarTruthAt]

theorem someFuture_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (someFuture φ) ↔ ∃ s, t < s ∧ StarTruthAt M τ s φ := by
  simp [someFuture, top, StarTruthAt]

theorem allFuture_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (allFuture φ) ↔ ∀ s, t < s → StarTruthAt M τ s φ := by
  simp [allFuture, someFuture, neg, top, StarTruthAt]

theorem somePast_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (somePast φ) ↔ ∃ s, s < t ∧ StarTruthAt M τ s φ := by
  simp [somePast, top, StarTruthAt]

/-! ### A1-A5: the definitional validities (T, 4, 5, `□→⊡`, atom stability), reused. -/

/-- **A1 (□→⊡)**: `⟨τ⟩_x ⊆ H_F`. -/
theorem stab_of_box (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula)
    (h : StarTruthAt M τ t (.box φ)) : StarTruthAt M τ t (.stab φ) :=
  fun σ hσ _ => h σ hσ

/-- **A2 (T)**: at a total history. -/
theorem of_stab (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (φ : StarFormula) (h : StarTruthAt M τ t (.stab φ)) : StarTruthAt M τ t φ :=
  h τ hτ (fun _ _ => rfl)

/-- **A3 (4)**. -/
theorem stab_four (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration)
    (φ : StarFormula) (h : StarTruthAt M τ t (.stab φ)) :
    StarTruthAt M τ t (.stab (.stab φ)) := by
  intro σ hσ hσsame ρ hρ hρsame
  exact h ρ hρ (fun hτ' hρ' => by rw [hσsame hτ' (hσ t), hρsame (hσ t) hρ'])

/-- **A4 (5)**: at a total history. -/
theorem stab_five (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    (φ : StarFormula) (h : ¬ StarTruthAt M τ t (.stab φ)) :
    StarTruthAt M τ t (.stab (.imp (.stab φ) .bot)) := by
  intro σ hσ hσsame hstab
  apply h
  intro ρ hρ hρsame
  exact hstab ρ hρ (fun hσ' hρ' => by rw [← hσsame (hτ t) hσ', ← hρsame (hτ t) hρ'])

/-- **A5 (atom stability)**: `p → ⊡p` for atoms (paper footnote, line 1119). -/
theorem stab_atom_of_atom (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (p : Atom)
    (h : StarTruthAt M τ t (.atom p)) : StarTruthAt M τ t (.stab (.atom p)) := by
  intro σ hσ hsame
  obtain ⟨hτ, hv⟩ := h
  exact ⟨hσ t, by rw [← hsame hτ (hσ t)]; exact hv⟩

/-- **A6 (shift commutation)**: `∼_t` commutes with time shift; `Iff.rfl`. -/
theorem sameStateAt_timeShift (τ σ : WorldHistory F) (t Δ : F.Duration) :
    SameStateAt (τ.timeShift Δ) (σ.timeShift Δ) t ↔ SameStateAt τ σ (t + Δ) := Iff.rfl

/-! ## Part B: `⊡φ` is a state formula at each time; `□⊡ ↔ □`; `□ → ⊡□`. -/

/-- **B1**: the truth of `⊡φ` at `(τ,t)` depends only on the `∼_t`-class of `τ`. -/
theorem stab_congr_sameState (M : TaskModel F) (τ σ : WorldHistory F) (t : F.Duration)
    (hτ : τ.domain t) (hσ : σ.domain t) (h : SameStateAt τ σ t) (φ : StarFormula) :
    StarTruthAt M τ t (.stab φ) ↔ StarTruthAt M σ t (.stab φ) := by
  constructor
  · intro hτs ρ hρ hρs
    exact hτs ρ hρ (fun hτ' hρ' => by rw [h hτ' hσ, hρs hσ hρ'])
  · intro hσs ρ hρ hρs
    exact hσs ρ hρ (fun hσ' hρ' => by rw [← h hτ hσ', hρs hτ hρ'])

/-- **B2**: `□⊡φ ↔ □φ` (semantically; derivable from K, T(⊡), 4(□), `□→⊡`). -/
theorem box_stab_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula) :
    StarTruthAt M τ t (.box (.stab φ)) ↔ StarTruthAt M τ t (.box φ) := by
  constructor
  · intro h σ hσ; exact h σ hσ σ hσ (fun _ _ => rfl)
  · intro h σ hσ ρ hρ _; exact h ρ hρ

/-- **B3**: `□φ → ⊡□φ` (derivable from 4(□) and `□→⊡`). -/
theorem stab_box_of_box (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (φ : StarFormula)
    (h : StarTruthAt M τ t (.box φ)) : StarTruthAt M τ t (.stab (.box φ)) :=
  fun _ _ _ => h

/-! ## Part C: history pasting (the Markov structure of `⟨τ⟩_t`) and its validities -/

/-- `ρ`'s states up to and including `t`, `σ`'s states after `t`. -/
def pasteFun (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration) :
    F.Duration → F.WorldState :=
  fun s => if s ≤ t then ρ.states s (hρ s) else σ.states s (hσ s)

theorem paste_rel_le_lt (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) {s s' : F.Duration} (hs : s ≤ t) (hs' : ¬ s' ≤ t) :
    F.TaskRel (ρ.states s (hρ s)) (s' - s) (σ.states s' (hσ s')) := by
  have h1 : F.TaskRel (ρ.states s (hρ s)) (t - s) (ρ.states t (hρ t)) := ρ.respects_task s t _ _
  have h2 : F.TaskRel (σ.states t (hσ t)) (s' - t) (σ.states s' (hσ s')) := σ.respects_task t s' _ _
  rw [hsame (hρ t) (hσ t)] at h1
  have heq : s' - s = (t - s) + (s' - t) := by
    rw [add_comm]; exact (sub_add_sub_cancel s' t s).symm
  rw [heq]
  exact (F.comp _ _ _ _ (sub_nonneg.mpr hs) (sub_nonneg.mpr (le_of_lt (not_le.mp hs')))).mpr
    ⟨_, h1, h2⟩

/-- The pasted state function respects the task relation: composition across `t`
(`TaskFrame.comp`), the converse convention for the reverse orientation. -/
theorem paste_rel (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) :
    ∀ s s' : F.Duration, F.TaskRel (pasteFun ρ σ hρ hσ t s) (s' - s) (pasteFun ρ σ hρ hσ t s') := by
  intro s s'
  unfold pasteFun
  by_cases hs : s ≤ t <;> by_cases hs' : s' ≤ t
  · rw [if_pos hs, if_pos hs']; exact ρ.respects_task s s' _ _
  · rw [if_pos hs, if_neg hs']; exact paste_rel_le_lt ρ σ hρ hσ t hsame hs hs'
  · rw [if_neg hs, if_pos hs', F.converse, neg_sub]; exact paste_rel_le_lt ρ σ hρ hσ t hsame hs' hs
  · rw [if_neg hs, if_neg hs']; exact σ.respects_task s s' _ _

/-- **C0 (pasting)**: if `ρ(t) = σ(t)` then `ρ|(-∞,t] ⌢ σ|(t,∞)` is a total history. Uses only
`TaskFrame.comp` and `TaskFrame.converse` — no Saturation, no extension theorem. -/
def paste (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) : WorldHistory F :=
  WorldHistory.ofTotal F (pasteFun ρ σ hρ hσ t) (paste_rel ρ σ hρ hσ t hsame)

theorem paste_isTotal (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) : (paste ρ σ hρ hσ t hsame).IsTotal :=
  WorldHistory.ofTotal_isTotal _ _ _

def AgreeFrom (τ σ : WorldHistory F) (t : F.Duration) : Prop :=
  ∀ s, t ≤ s → ∀ (hτ : τ.domain s) (hσ : σ.domain s), τ.states s hτ = σ.states s hσ

def AgreeUpTo (τ σ : WorldHistory F) (t : F.Duration) : Prop :=
  ∀ s, s ≤ t → ∀ (hτ : τ.domain s) (hσ : σ.domain s), τ.states s hτ = σ.states s hσ

theorem agreeFrom_mono {τ σ : WorldHistory F} {t s : F.Duration} (hts : t ≤ s)
    (h : AgreeFrom τ σ t) : AgreeFrom τ σ s :=
  fun r hsr => h r (le_trans hts hsr)

theorem agreeUpTo_mono {τ σ : WorldHistory F} {t s : F.Duration} (hst : s ≤ t)
    (h : AgreeUpTo τ σ t) : AgreeUpTo τ σ s :=
  fun r hrs => h r (le_trans hrs hst)

theorem paste_agreeFrom (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) : AgreeFrom (paste ρ σ hρ hσ t hsame) σ t := by
  intro s hts h1 h2
  show pasteFun ρ σ hρ hσ t s = σ.states s h2
  unfold pasteFun
  by_cases h : s ≤ t
  · have : s = t := le_antisymm h hts
    subst this
    rw [if_pos le_rfl]; exact hsame _ _
  · rw [if_neg h]

theorem paste_agreeUpTo (ρ σ : WorldHistory F) (hρ : ρ.IsTotal) (hσ : σ.IsTotal) (t : F.Duration)
    (hsame : SameStateAt ρ σ t) : AgreeUpTo (paste ρ σ hρ hσ t hsame) ρ t := by
  intro s hst h1 h2
  show pasteFun ρ σ hρ hσ t s = ρ.states s h2
  unfold pasteFun
  rw [if_pos hst]

/-- Pure-future formulas: no `snce` outside a `box`/`stab` scope. -/
inductive IsPureFuture : StarFormula → Prop
  | atom (p : Atom) : IsPureFuture (.atom p)
  | bot : IsPureFuture .bot
  | imp {φ ψ : StarFormula} : IsPureFuture φ → IsPureFuture ψ → IsPureFuture (.imp φ ψ)
  | box (φ : StarFormula) : IsPureFuture (.box φ)
  | stab (φ : StarFormula) : IsPureFuture (.stab φ)
  | untl {ψ φ : StarFormula} : IsPureFuture ψ → IsPureFuture φ → IsPureFuture (.untl ψ φ)

/-- Pure-past formulas: no `untl` outside a `box`/`stab` scope. -/
inductive IsPurePast : StarFormula → Prop
  | atom (p : Atom) : IsPurePast (.atom p)
  | bot : IsPurePast .bot
  | imp {φ ψ : StarFormula} : IsPurePast φ → IsPurePast ψ → IsPurePast (.imp φ ψ)
  | box (φ : StarFormula) : IsPurePast (.box φ)
  | stab (φ : StarFormula) : IsPurePast (.stab φ)
  | snce {ψ φ : StarFormula} : IsPurePast ψ → IsPurePast φ → IsPurePast (.snce ψ φ)

theorem sameStateAt_congr_left {τ σ ρ : WorldHistory F} {t : F.Duration}
    (hτ : τ.domain t) (hσ : σ.domain t) (h : τ.states t hτ = σ.states t hσ) :
    SameStateAt τ ρ t ↔ SameStateAt σ ρ t := by
  constructor
  · intro hh hσ' hρ'; rw [← h]; exact hh _ _
  · intro hh hτ' hρ'; rw [h]; exact hh _ _

/-- **C1a**: a pure-future formula sees only the history from `t` onward. -/
theorem truth_congr_agreeFrom (M : TaskModel F) {φ : StarFormula} (hφ : IsPureFuture φ) :
    ∀ (τ σ : WorldHistory F), τ.IsTotal → σ.IsTotal → ∀ t, AgreeFrom τ σ t →
      (StarTruthAt M τ t φ ↔ StarTruthAt M σ t φ) := by
  induction hφ with
  | atom p =>
    intro τ σ hτ hσ t hag
    constructor
    · rintro ⟨h1, hv⟩; exact ⟨hσ t, by rw [← hag t le_rfl h1 (hσ t)]; exact hv⟩
    · rintro ⟨h2, hv⟩; exact ⟨hτ t, by rw [hag t le_rfl (hτ t) h2]; exact hv⟩
  | bot => intros; exact Iff.rfl
  | imp _ _ ihφ ihψ =>
    intro τ σ hτ hσ t hag
    exact Iff.imp (ihφ τ σ hτ hσ t hag) (ihψ τ σ hτ hσ t hag)
  | box φ => intros; exact Iff.rfl
  | stab φ =>
    intro τ σ hτ hσ t hag
    exact forall_congr' fun ρ => imp_congr_right fun _ =>
      imp_congr_left (sameStateAt_congr_left (hτ t) (hσ t) (hag t le_rfl _ _))
  | untl _ _ ihψ ihφ =>
    intro τ σ hτ hσ t hag
    exact exists_congr fun s => and_congr_right fun hts =>
      and_congr (ihφ τ σ hτ hσ s (agreeFrom_mono hts.le hag))
        (forall_congr' fun r => imp_congr_right fun htr => imp_congr_right fun _ =>
          ihψ τ σ hτ hσ r (agreeFrom_mono htr.le hag))

/-- **C1b**: a pure-past formula sees only the history up to `t`. -/
theorem truth_congr_agreeUpTo (M : TaskModel F) {φ : StarFormula} (hφ : IsPurePast φ) :
    ∀ (τ σ : WorldHistory F), τ.IsTotal → σ.IsTotal → ∀ t, AgreeUpTo τ σ t →
      (StarTruthAt M τ t φ ↔ StarTruthAt M σ t φ) := by
  induction hφ with
  | atom p =>
    intro τ σ hτ hσ t hag
    constructor
    · rintro ⟨h1, hv⟩; exact ⟨hσ t, by rw [← hag t le_rfl h1 (hσ t)]; exact hv⟩
    · rintro ⟨h2, hv⟩; exact ⟨hτ t, by rw [hag t le_rfl (hτ t) h2]; exact hv⟩
  | bot => intros; exact Iff.rfl
  | imp _ _ ihφ ihψ =>
    intro τ σ hτ hσ t hag
    exact Iff.imp (ihφ τ σ hτ hσ t hag) (ihψ τ σ hτ hσ t hag)
  | box φ => intros; exact Iff.rfl
  | stab φ =>
    intro τ σ hτ hσ t hag
    exact forall_congr' fun ρ => imp_congr_right fun _ =>
      imp_congr_left (sameStateAt_congr_left (hτ t) (hσ t) (hag t le_rfl _ _))
  | snce _ _ ihψ ihφ =>
    intro τ σ hτ hσ t hag
    exact exists_congr fun s => and_congr_right fun hst =>
      and_congr (ihφ τ σ hτ hσ s (agreeUpTo_mono hst.le hag))
        (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun hrt =>
          ihψ τ σ hτ hσ r (agreeUpTo_mono hrt.le hag))

/-- **C2 (Paste)**: `⟐φ⁺ ∧ ⟐ψ⁻ → ⟐(φ⁺ ∧ ψ⁻)` is valid for pure-future `φ⁺` and pure-past
`ψ⁻`. Not derivable from S5(⊡) + `□→⊡` + `p→⊡p` + TM⁺ (see the report's independence
argument). -/
theorem paste_valid (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal) (t : F.Duration)
    {φ ψ : StarFormula} (hφ : IsPureFuture φ) (hψ : IsPurePast ψ) :
    StarTruthAt M τ t (.imp (dstab φ) (.imp (dstab ψ) (dstab (conj φ ψ)))) := by
  intro h1 h2
  rw [dstab_iff] at h1 h2 ⊢
  obtain ⟨σ, hσ, hτσ, hφσ⟩ := h1
  obtain ⟨ρ, hρ, hτρ, hψρ⟩ := h2
  have hsame : SameStateAt ρ σ t := fun a b => (hτρ (hτ t) a).symm.trans (hτσ (hτ t) b)
  refine ⟨paste ρ σ hρ hσ t hsame, paste_isTotal ρ σ hρ hσ t hsame, ?_, ?_⟩
  · intro a b
    rw [hτρ a (hρ t)]
    exact (paste_agreeUpTo ρ σ hρ hσ t hsame t le_rfl b (hρ t)).symm
  · rw [conj_iff]
    exact ⟨(truth_congr_agreeFrom M hφ _ _ (paste_isTotal ρ σ hρ hσ t hsame) hσ t
              (paste_agreeFrom ρ σ hρ hσ t hsame)).mpr hφσ,
           (truth_congr_agreeUpTo M hψ _ _ (paste_isTotal ρ σ hρ hσ t hsame) hρ t
              (paste_agreeUpTo ρ σ hρ hσ t hsame)).mpr hψρ⟩

/-- **C3 (FS)**: `F⟐φ⁺ → ⟐Fφ⁺` is valid for pure-future `φ⁺` (pasting at the future time). -/
theorem future_dstab_valid (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal)
    (t : F.Duration) {φ : StarFormula} (hφ : IsPureFuture φ) :
    StarTruthAt M τ t (.imp (someFuture (dstab φ)) (dstab (someFuture φ))) := by
  intro h
  rw [someFuture_iff] at h
  obtain ⟨y, hty, hy⟩ := h
  rw [dstab_iff] at hy
  obtain ⟨ρ, hρ, hτρ, hφρ⟩ := hy
  rw [dstab_iff]
  refine ⟨paste τ ρ hτ hρ y hτρ, paste_isTotal τ ρ hτ hρ y hτρ, ?_, ?_⟩
  · intro a b
    exact (paste_agreeUpTo τ ρ hτ hρ y hτρ t hty.le b a).symm
  · rw [someFuture_iff]
    exact ⟨y, hty, (truth_congr_agreeFrom M hφ _ _ (paste_isTotal τ ρ hτ hρ y hτρ) hρ y
      (paste_agreeFrom τ ρ hτ hρ y hτρ)).mpr hφρ⟩

/-- **C4 (GS)**: `⊡Gφ⁺ → G⊡φ⁺` is valid for pure-future `φ⁺` (the dual reading of C3;
`Will φ⁺ → G Will φ⁺`-shaped consequences follow). -/
theorem stab_allFuture_valid (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal)
    (t : F.Duration) {φ : StarFormula} (hφ : IsPureFuture φ) :
    StarTruthAt M τ t (.imp (.stab (allFuture φ)) (allFuture (.stab φ))) := by
  intro h
  rw [allFuture_iff]
  intro y hty ρ hρ hτρ
  have hπ := h (paste τ ρ hτ hρ y hτρ) (paste_isTotal τ ρ hτ hρ y hτρ)
    (fun a b => (paste_agreeUpTo τ ρ hτ hρ y hτρ t hty.le b a).symm)
  rw [allFuture_iff] at hπ
  exact (truth_congr_agreeFrom M hφ _ _ (paste_isTotal τ ρ hτ hρ y hτρ) hρ y
    (paste_agreeFrom τ ρ hτ hρ y hτρ)).mp (hπ y hty)

/-! ## Part D: refutations on the permissive frame `natFrame` over ℤ (every `ℤ → ℕ` is a
total history there, so `⟨τ⟩_t` is as large as possible). -/

abbrev NF : TaskFrame := FrameOver.natFrame (D := ℤ)

def natHist (f : ℤ → ℕ) : WorldHistory NF :=
  WorldHistory.ofTotal NF f (fun s t => by
    by_cases h : t - s = 0
    · right
      have : t = s := sub_eq_zero.mp h
      subst this; rfl
    · left; exact h)

theorem natHist_isTotal (f : ℤ → ℕ) : (natHist f).IsTotal := WorldHistory.ofTotal_isTotal _ _ _

/-- Every atom is true exactly at world state `0`. -/
def natModel : TaskModel NF where
  valuation := fun (n : ℕ) _ => n = 0

/-- **D1**: `⊡p → □⊡p` is refuted (`⊡` does not collapse into `□`). -/
theorem refute_stab_box (p : Atom) :
    ¬ StarValid (.imp (.stab (.atom p)) (.box (.stab (.atom p)))) := by
  intro h
  have hv := h NF natModel (natHist fun _ => 0) (natHist_isTotal _) 0
  have h1 : StarTruthAt natModel (natHist fun _ => 0) 0 (.stab (.atom p)) := by
    intro σ hσ hs
    exact ⟨hσ 0, (hs trivial (hσ 0)).symm⟩
  have h2 := hv h1 (natHist fun _ => 1) (natHist_isTotal _) (natHist fun _ => 1)
    (natHist_isTotal _) (fun _ _ => rfl)
  rw [atom_iff] at h2
  obtain ⟨_, h4⟩ := h2
  have h5 : (1 : ℕ) = 0 := h4
  exact one_ne_zero h5

/-- **D2**: `G⊡p → ⊡Gp` is refuted (the converse of C4 fails even for atoms). -/
theorem refute_allFuture_stab (p : Atom) :
    ¬ StarValid (.imp (allFuture (.stab (.atom p))) (.stab (allFuture (.atom p)))) := by
  intro h
  have hv := h NF natModel (natHist fun _ => 0) (natHist_isTotal _) 0
  have hA : StarTruthAt natModel (natHist fun _ => 0) 0 (allFuture (.stab (.atom p))) := by
    rw [allFuture_iff]
    intro y _ ρ hρ hs
    exact ⟨hρ y, (hs trivial (hρ y)).symm⟩
  have hB := hv hA (natHist fun s => if s = 1 then 1 else 0) (natHist_isTotal _)
    (fun _ _ => by show (0 : ℕ) = (if (0 : ℤ) = 1 then 1 else 0); simp)
  rw [allFuture_iff] at hB
  have hat := hB (1 : ℤ) (one_pos : (0 : ℤ) < 1)
  rw [atom_iff] at hat
  obtain ⟨_, v⟩ := hat
  have v' : (if (1 : ℤ) = 1 then (1 : ℕ) else 0) = 0 := v
  simp at v'

/-- **D3**: `⊡GPp → G⊡Pp` is refuted — C4 genuinely needs the pure-future restriction. -/
theorem refute_stab_allFuture_past (p : Atom) :
    ¬ StarValid (.imp (.stab (allFuture (somePast (.atom p))))
        (allFuture (.stab (somePast (.atom p))))) := by
  intro h
  have hv := h NF natModel (natHist fun _ => 0) (natHist_isTotal _) 0
  have hA : StarTruthAt natModel (natHist fun _ => 0) 0 (.stab (allFuture (somePast (.atom p)))) := by
    intro σ hσ hs
    rw [allFuture_iff]
    intro y hy
    rw [somePast_iff]
    exact ⟨0, hy, hσ 0, (hs trivial (hσ 0)).symm⟩
  have hB := hv hA
  rw [allFuture_iff] at hB
  have hC := hB (1 : ℤ) (one_pos : (0 : ℤ) < 1) (natHist fun s => if s = 1 then 0 else 1)
    (natHist_isTotal _)
    (fun _ _ => by show (0 : ℕ) = (if (1 : ℤ) = 1 then 0 else 1); simp)
  rw [somePast_iff] at hC
  obtain ⟨s, hs1, hat⟩ := hC
  rw [atom_iff] at hat
  obtain ⟨_, v⟩ := hat
  have hs1' : (s : ℤ) < 1 := hs1
  have v' : (if (s : ℤ) = 1 then (0 : ℕ) else 1) = 0 := v
  rw [if_neg (fun h => by rw [h] at hs1'; exact lt_irrefl _ hs1')] at v'
  exact one_ne_zero v'

/-- **D4**: *Determined* `Fp → ⊡Fp` is refuted over a non-deterministic frame
(paper `app:deterministic`, second half, in the `natFrame` shape). -/
theorem refute_determined (p : Atom) :
    ¬ StarValid (.imp (someFuture (.atom p)) (.stab (someFuture (.atom p)))) := by
  intro h
  have hv := h NF natModel (natHist fun _ => 0) (natHist_isTotal _) 0
  have hA : StarTruthAt natModel (natHist fun _ => 0) 0 (someFuture (.atom p)) := by
    rw [someFuture_iff]; exact ⟨(1 : ℤ), (one_pos : (0 : ℤ) < 1), trivial, (rfl : (0 : ℕ) = 0)⟩
  have hB := hv hA (natHist fun s => if s ≤ 0 then 0 else 1) (natHist_isTotal _)
    (fun _ _ => by show (0 : ℕ) = (if (0 : ℤ) ≤ 0 then 0 else 1); simp)
  rw [someFuture_iff] at hB
  obtain ⟨s, hs, hat⟩ := hB
  rw [atom_iff] at hat
  obtain ⟨_, v⟩ := hat
  have hs' : (0 : ℤ) < s := hs
  have v' : (if (s : ℤ) ≤ 0 then (0 : ℕ) else 1) = 0 := v
  rw [if_neg (not_le.mpr hs')] at v'
  exact one_ne_zero v'

/-- **D5**: `P⊡p → ⊡Pp` is refuted. This is the `⊡`-analogue of the single tense/modal
interaction axiom of T×W / Ockhamist logic (Kamp's AK12 in Thomason 1984 §4, Reynolds 2003's
HN), and it fails because `⟨τ⟩_t` is not closed towards the past. -/
theorem refute_somePast_stab (p : Atom) :
    ¬ StarValid (.imp (somePast (.stab (.atom p))) (.stab (somePast (.atom p)))) := by
  intro h
  have hv := h NF natModel (natHist fun _ => 0) (natHist_isTotal _) 0
  have hA : StarTruthAt natModel (natHist fun _ => 0) 0 (somePast (.stab (.atom p))) := by
    rw [somePast_iff]
    refine ⟨(-1 : ℤ), (by decide : (-1 : ℤ) < 0), ?_⟩
    intro ρ hρ hs
    exact ⟨hρ (-1), (hs trivial (hρ (-1))).symm⟩
  have hB := hv hA (natHist fun s => if s < 0 then 1 else 0) (natHist_isTotal _)
    (fun _ _ => by show (0 : ℕ) = (if (0 : ℤ) < 0 then 1 else 0); simp)
  rw [somePast_iff] at hB
  obtain ⟨s, hs, hat⟩ := hB
  rw [atom_iff] at hat
  obtain ⟨_, v⟩ := hat
  have hs' : (s : ℤ) < 0 := hs
  have v' : (if (s : ℤ) < 0 then (1 : ℕ) else 0) = 0 := v
  rw [if_pos hs'] at v'
  exact one_ne_zero v'

/-! ## Part E: time-shift invariance — `⊡φ` depends on the world state alone -/

theorem states_congr (ρ : WorldHistory F) {s s' : F.Duration} (h : s = s') (hs : ρ.domain s) :
    ρ.states s hs = ρ.states s' (h ▸ hs) := by subst h; rfl

/-- **E0**: pointwise-equal histories satisfy the same formulas. -/
theorem truth_congr_ext (M : TaskModel F) (φ : StarFormula) :
    ∀ (τ σ : WorldHistory F) (t : F.Duration),
      (∀ s, τ.domain s ↔ σ.domain s) →
      (∀ s (hτ : τ.domain s) (hσ : σ.domain s), τ.states s hτ = σ.states s hσ) →
      (StarTruthAt M τ t φ ↔ StarTruthAt M σ t φ) := by
  induction φ with
  | atom p =>
    intro τ σ t hd hs
    constructor
    · rintro ⟨h1, hv⟩; exact ⟨(hd t).mp h1, by rw [← hs t h1 ((hd t).mp h1)]; exact hv⟩
    · rintro ⟨h2, hv⟩; exact ⟨(hd t).mpr h2, by rw [hs t ((hd t).mpr h2) h2]; exact hv⟩
  | bot => intros; exact Iff.rfl
  | imp φ ψ ihφ ihψ => intro τ σ t hd hs; exact Iff.imp (ihφ τ σ t hd hs) (ihψ τ σ t hd hs)
  | box φ _ => intros; exact Iff.rfl
  | untl ψ φ ihψ ihφ =>
    intro τ σ t hd hs
    exact exists_congr fun s => and_congr_right fun _ => and_congr (ihφ τ σ s hd hs)
      (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ σ r hd hs)
  | snce ψ φ ihψ ihφ =>
    intro τ σ t hd hs
    exact exists_congr fun s => and_congr_right fun _ => and_congr (ihφ τ σ s hd hs)
      (forall_congr' fun r => imp_congr_right fun _ => imp_congr_right fun _ => ihψ τ σ r hd hs)
  | stab φ _ =>
    intro τ σ t hd hs
    refine forall_congr' fun ρ => imp_congr_right fun _ => imp_congr_left ⟨?_, ?_⟩
    · intro h hσ' hρ'; rw [← hs t ((hd t).mpr hσ') hσ']; exact h _ _
    · intro h hτ' hρ'; rw [hs t hτ' ((hd t).mp hτ')]; exact h _ _

theorem timeShift_isTotal' (σ : WorldHistory F) (hσ : σ.IsTotal) (Δ : F.Duration) :
    (σ.timeShift Δ).IsTotal := fun z => hσ (z + Δ)

theorem shift_neg_shift_domain (ρ : WorldHistory F) (Δ s : F.Duration) :
    ((ρ.timeShift (-Δ)).timeShift Δ).domain s ↔ ρ.domain s := by
  show ρ.domain (s + Δ + -Δ) ↔ ρ.domain s
  rw [add_neg_cancel_right]

theorem shift_neg_shift_states (ρ : WorldHistory F) (Δ s : F.Duration)
    (h1 : ((ρ.timeShift (-Δ)).timeShift Δ).domain s) (h2 : ρ.domain s) :
    ((ρ.timeShift (-Δ)).timeShift Δ).states s h1 = ρ.states s h2 := by
  show ρ.states (s + Δ + -Δ) h1 = ρ.states s h2
  exact (states_congr ρ (add_neg_cancel_right s Δ) h1)

/-- **E1**: L⋆ truth commutes with time shift (the `StarFormula` twin of
`timeShift_preserves_truth`, proved directly because `TruthCorr` is `Formula`-only). -/
theorem starTruthAt_timeShift (M : TaskModel F) (φ : StarFormula) :
    ∀ (σ : WorldHistory F) (t Δ : F.Duration),
      StarTruthAt M (σ.timeShift Δ) t φ ↔ StarTruthAt M σ (t + Δ) φ := by
  induction φ with
  | atom p => intros; exact Iff.rfl
  | bot => intros; exact Iff.rfl
  | imp φ ψ ihφ ihψ => intro σ t Δ; exact Iff.imp (ihφ σ t Δ) (ihψ σ t Δ)
  | box φ ih =>
    intro σ t Δ
    constructor
    · intro h ρ hρ
      exact (ih ρ t Δ).mp (h (ρ.timeShift Δ) (timeShift_isTotal' ρ hρ Δ))
    · intro h ρ hρ
      have h1 := (ih (ρ.timeShift (-Δ)) t Δ).mpr (h (ρ.timeShift (-Δ)) (timeShift_isTotal' ρ hρ (-Δ)))
      exact (truth_congr_ext M φ _ ρ t (shift_neg_shift_domain ρ Δ)
        (shift_neg_shift_states ρ Δ)).mp h1
  | untl ψ φ ihψ ihφ =>
    intro σ t Δ
    constructor
    · rintro ⟨s, hts, hφ, hψ⟩
      refine ⟨s + Δ, (add_lt_add_iff_right Δ).mpr hts, (ihφ σ s Δ).mp hφ, ?_⟩
      intro r' h1 h2
      have := ihψ σ (r' - Δ) Δ
      rw [sub_add_cancel] at this
      exact this.mp (hψ (r' - Δ) (lt_sub_iff_add_lt.mpr h1) (sub_lt_iff_lt_add.mpr h2))
    · rintro ⟨s', h, hφ, hψ⟩
      refine ⟨s' - Δ, lt_sub_iff_add_lt.mpr h, ?_, ?_⟩
      · have := ihφ σ (s' - Δ) Δ
        rw [sub_add_cancel] at this
        exact this.mpr hφ
      · intro r htr hrs
        exact (ihψ σ r Δ).mpr (hψ (r + Δ) ((add_lt_add_iff_right Δ).mpr htr) (lt_sub_iff_add_lt.mp hrs))
  | snce ψ φ ihψ ihφ =>
    intro σ t Δ
    constructor
    · rintro ⟨s, hst, hφ, hψ⟩
      refine ⟨s + Δ, (add_lt_add_iff_right Δ).mpr hst, (ihφ σ s Δ).mp hφ, ?_⟩
      intro r' h1 h2
      have := ihψ σ (r' - Δ) Δ
      rw [sub_add_cancel] at this
      exact this.mp (hψ (r' - Δ) (lt_sub_iff_add_lt.mpr h1) (sub_lt_iff_lt_add.mpr h2))
    · rintro ⟨s', h, hφ, hψ⟩
      refine ⟨s' - Δ, sub_lt_iff_lt_add.mpr h, ?_, ?_⟩
      · have := ihφ σ (s' - Δ) Δ
        rw [sub_add_cancel] at this
        exact this.mpr hφ
      · intro r hsr hrt
        exact (ihψ σ r Δ).mpr (hψ (r + Δ) (sub_lt_iff_lt_add.mp hsr) ((add_lt_add_iff_right Δ).mpr hrt))
  | stab φ ih =>
    intro σ t Δ
    constructor
    · intro h ρ hρ hs
      exact (ih ρ t Δ).mp (h (ρ.timeShift Δ) (timeShift_isTotal' ρ hρ Δ) hs)
    · intro h ρ hρ hs
      have hs' : SameStateAt σ (ρ.timeShift (-Δ)) (t + Δ) := by
        intro hσ' hρ'
        exact (hs hσ' (hρ t)).trans (states_congr ρ (add_neg_cancel_right t Δ).symm (hρ t))
      have h1 := (ih (ρ.timeShift (-Δ)) t Δ).mpr
        (h (ρ.timeShift (-Δ)) (timeShift_isTotal' ρ hρ (-Δ)) hs')
      exact (truth_congr_ext M φ _ ρ t (shift_neg_shift_domain ρ Δ)
        (shift_neg_shift_states ρ Δ)).mp h1

/-- **E2**: `⊡φ` depends on the world state alone — if `τ(t) = σ(s)` (at possibly different
times) then `⊡φ` has the same truth value at `(τ,t)` and `(σ,s)`. This licenses treating each
`⊡φ` as a fresh state-valued atom (the atomization route to TM⁺-schema soundness over L⋆). -/
theorem stab_state_only (M : TaskModel F) (τ σ : WorldHistory F) (hτ : τ.IsTotal)
    (hσ : σ.IsTotal) (t s : F.Duration) (h : τ.states t (hτ t) = σ.states s (hσ s))
    (φ : StarFormula) :
    StarTruthAt M τ t (.stab φ) ↔ StarTruthAt M σ s (.stab φ) := by
  have hsame : SameStateAt τ (σ.timeShift (s - t)) t := by
    intro h1 h2
    rw [h]
    exact states_congr σ (add_sub_cancel t s).symm (hσ s)
  rw [stab_congr_sameState M τ (σ.timeShift (s - t)) t (hτ t) (hσ (t + (s - t))) hsame φ,
    starTruthAt_timeShift, add_sub_cancel]


/-! ## Part C (continued): the `U`-generalisation of C3 -/

theorem untl_iff (M : TaskModel F) (τ : WorldHistory F) (t : F.Duration) (ψ φ : StarFormula) :
    StarTruthAt M τ t (.untl ψ φ) ↔ ∃ s, t < s ∧ StarTruthAt M τ s φ ∧
      ∀ r, t < r → r < s → StarTruthAt M τ r ψ := Iff.rfl

/-- **C5 (US)**: `(α⁻ U ⟐φ⁺) → ⟐(α⁻ U φ⁺)` for pure-past `α⁻` and pure-future `φ⁺`. C3 is
the instance `α⁻ := ⊤`; C4 is C3's contrapositive. -/
theorem untl_dstab_valid (M : TaskModel F) (τ : WorldHistory F) (hτ : τ.IsTotal)
    (t : F.Duration) {α φ : StarFormula} (hα : IsPurePast α) (hφ : IsPureFuture φ) :
    StarTruthAt M τ t (.imp (.untl α (dstab φ)) (dstab (.untl α φ))) := by
  intro h
  rw [untl_iff] at h
  obtain ⟨y, hty, hy, hguard⟩ := h
  rw [dstab_iff] at hy
  obtain ⟨ρ, hρ, hτρ, hφρ⟩ := hy
  rw [dstab_iff]
  refine ⟨paste τ ρ hτ hρ y hτρ, paste_isTotal τ ρ hτ hρ y hτρ,
    fun a b => (paste_agreeUpTo τ ρ hτ hρ y hτρ t hty.le b a).symm, ?_⟩
  rw [untl_iff]
  refine ⟨y, hty, (truth_congr_agreeFrom M hφ _ _ (paste_isTotal τ ρ hτ hρ y hτρ) hρ y
    (paste_agreeFrom τ ρ hτ hρ y hτρ)).mpr hφρ, ?_⟩
  intro r htr hry
  exact (truth_congr_agreeUpTo M hα _ τ (paste_isTotal τ ρ hτ hρ y hτρ) hτ r
    (agreeUpTo_mono hry.le (paste_agreeUpTo τ ρ hτ hρ y hτρ))).mpr (hguard r htr hry)

end Scratch535
