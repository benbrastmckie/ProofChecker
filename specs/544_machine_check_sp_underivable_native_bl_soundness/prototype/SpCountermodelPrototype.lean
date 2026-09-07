import FormalSystem.Metalogic.Conservativity.TMCompletenessReduction
import FormalSystem.Metalogic.Conservativity.SpWitness

namespace Scratch544

open FormalSystem
open FormalSystem.Syntax
open FormalSystem.BaseLanguage
open FormalSystem.ProofSystem

/-! ## A native BL frame, not bound to `TaskFrame` -/

structure BLFrame where
  Point : Type
  [pointNonempty : Nonempty Point]
  lt : Point → Point → Prop
  lt_trans : ∀ {a b c}, lt a b → lt b c → lt a c
  lt_irrefl : ∀ a, ¬ lt a a
  no_max : ∀ a, ∃ b, lt a b
  no_min : ∀ a, ∃ b, lt b a
  fut_lin : ∀ {a b c}, lt a b → lt a c → lt b c ∨ b = c ∨ lt c b
  past_lin : ∀ {a b c}, lt b a → lt c a → lt b c ∨ b = c ∨ lt c b

attribute [instance] BLFrame.pointNonempty

private theorem triRotate {α : Type} {r : α → α → Prop} {b c : α}
    (h : r b c ∨ b = c ∨ r c b) : r c b ∨ b = c ∨ r b c := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- Order reversal: the class is closed under it, which is what makes TD sound. -/
def BLFrame.swap (F : BLFrame) : BLFrame where
  Point := F.Point
  lt := fun a b => F.lt b a
  lt_trans := fun h1 h2 => F.lt_trans h2 h1
  lt_irrefl := F.lt_irrefl
  no_max := F.no_min
  no_min := F.no_max
  fut_lin := fun h1 h2 => triRotate (F.past_lin h1 h2)
  past_lin := fun h1 h2 => triRotate (F.fut_lin h1 h2)

/-! ## Native truth -/

def BLFrameTruth (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) : BLFormula → Prop
  | .atom p => V w p
  | .bot => False
  | .imp φ ψ => BLFrameTruth F V w φ → BLFrameTruth F V w ψ
  | .box φ => ∀ v : F.Point, BLFrameTruth F V v φ
  | .allPast φ => ∀ v : F.Point, F.lt v w → BLFrameTruth F V v φ
  | .allFuture φ => ∀ v : F.Point, F.lt w v → BLFrameTruth F V v φ

def BLFrameValid (φ : BLFormula) : Prop :=
  ∀ (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point), BLFrameTruth F V w φ

/-! ### Characterisation lemmas -/

namespace BLFrameTruth

variable {F : BLFrame} {V : F.Point → Atom → Prop} {w : F.Point}

theorem imp_iff (φ ψ : BLFormula) :
    BLFrameTruth F V w (φ.imp ψ) ↔ (BLFrameTruth F V w φ → BLFrameTruth F V w ψ) := Iff.rfl

theorem box_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.box ↔ ∀ v : F.Point, BLFrameTruth F V v φ := Iff.rfl

theorem past_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.allPast ↔ ∀ v, F.lt v w → BLFrameTruth F V v φ := Iff.rfl

theorem future_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.allFuture ↔ ∀ v, F.lt w v → BLFrameTruth F V v φ := Iff.rfl

@[simp] theorem neg_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.neg ↔ ¬ BLFrameTruth F V w φ := Iff.rfl

@[simp] theorem top_true : BLFrameTruth F V w BLFormula.top := id

@[simp] theorem and_iff (φ ψ : BLFormula) :
    BLFrameTruth F V w (φ.and ψ) ↔ (BLFrameTruth F V w φ ∧ BLFrameTruth F V w ψ) := by
  simp only [BLFormula.and, BLFormula.neg, BLFrameTruth]; tauto

@[simp] theorem or_iff (φ ψ : BLFormula) :
    BLFrameTruth F V w (φ.or ψ) ↔ (BLFrameTruth F V w φ ∨ BLFrameTruth F V w ψ) := by
  simp only [BLFormula.or, BLFormula.neg, BLFrameTruth]; tauto

@[simp] theorem diamond_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.diamond ↔ ∃ v : F.Point, BLFrameTruth F V v φ := by
  simp only [BLFormula.diamond, BLFormula.neg, BLFrameTruth]
  constructor
  · intro h; by_contra hc; push Not at hc; exact h (fun v hv => hc v hv)
  · rintro ⟨v, hv⟩ h; exact h v hv

@[simp] theorem someFuture_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.someFuture ↔ ∃ v, F.lt w v ∧ BLFrameTruth F V v φ := by
  simp only [BLFormula.someFuture, BLFormula.neg, BLFrameTruth]
  constructor
  · intro h; by_contra hc; push Not at hc; exact h (fun v hv hφ => hc v hv hφ)
  · rintro ⟨v, hv, hφ⟩ h; exact h v hv hφ

@[simp] theorem somePast_iff (φ : BLFormula) :
    BLFrameTruth F V w φ.somePast ↔ ∃ v, F.lt v w ∧ BLFrameTruth F V v φ := by
  simp only [BLFormula.somePast, BLFormula.neg, BLFrameTruth]
  constructor
  · intro h; by_contra hc; push Not at hc; exact h (fun v hv hφ => hc v hv hφ)
  · rintro ⟨v, hv, hφ⟩ h; exact h v hv hφ

end BLFrameTruth

/-! ## The swap-transfer lemma -/

theorem truth_swap (F : BLFrame) (V : F.Point → Atom → Prop) (w : F.Point) (φ : BLFormula) :
    BLFrameTruth F.swap V w φ ↔ BLFrameTruth F V w φ.swapBL := by
  induction φ generalizing w with
  | atom p => exact Iff.rfl
  | bot => exact Iff.rfl
  | imp φ ψ ih1 ih2 => exact imp_congr (ih1 w) (ih2 w)
  | box φ ih => exact forall_congr' fun v => ih v
  | allPast φ ih => exact forall_congr' fun v => imp_congr_right fun _ => ih v
  | allFuture φ ih => exact forall_congr' fun v => imp_congr_right fun _ => ih v

end Scratch544

namespace Scratch544

open FormalSystem FormalSystem.Syntax FormalSystem.BaseLanguage FormalSystem.ProofSystem

/-! ## Axiom validity -/

theorem axiom_valid {φ : BLFormula} (ax : BaseLanguage.Axiom φ)
    (h_fc : ax.minFrameClass ≤ FrameClass.Base) : BLFrameValid φ := by
  cases ax with
  | prop_k φ ψ χ => intro F V w h1 h2 h3; exact h1 h3 (h2 h3)
  | prop_s φ ψ => intro F V w h1 _; exact h1
  | ex_falso φ => intro F V w h; exact h.elim
  | peirce φ ψ =>
      intro F V w h
      by_contra hc
      exact hc (h (fun hφ => absurd hφ hc))
  | modal_k φ ψ => intro F V w h1 h2 v; exact h1 v (h2 v)
  | modal_t φ => intro F V w h; exact h w
  | modal_5 φ =>
      intro F V w h v
      rw [BLFrameTruth.diamond_iff] at h
      obtain ⟨u, hu⟩ := h
      exact hu v
  | modal_future φ => intro F V w h v u _; exact h u
  | temp_k φ ψ => intro F V w h1 h2 v hv; exact h1 v hv (h2 v hv)
  | temp_4 φ => intro F V w h v hv u hu; exact h u (F.lt_trans hv hu)
  | temp_serial =>
      intro F V w
      rw [BLFrameTruth.someFuture_iff]
      obtain ⟨v, hv⟩ := F.no_max w
      exact ⟨v, hv, BLFrameTruth.top_true⟩
  | temp_connect φ =>
      intro F V w h v hv
      rw [BLFrameTruth.somePast_iff]
      exact ⟨w, hv, h⟩
  | temp_linearity φ ψ =>
      intro F V w h
      rw [BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff, BLFrameTruth.someFuture_iff] at h
      obtain ⟨⟨s, hws, hφ⟩, ⟨u, hwu, hψ⟩⟩ := h
      rcases F.fut_lin hws hwu with hlt | heq | hgt
      · -- s < u : third disjunct, `F(φ ∧ Fψ)` at `s`
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inr ((BLFrameTruth.or_iff _ _).mpr (Or.inr ?_)))
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨s, hws, ?_⟩
        rw [BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff]
        exact ⟨hφ, u, hlt, hψ⟩
      · -- s = u : second disjunct
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inr ((BLFrameTruth.or_iff _ _).mpr (Or.inl ?_)))
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨s, hws, ?_⟩
        rw [BLFrameTruth.and_iff]
        exact ⟨hφ, heq ▸ hψ⟩
      · -- u < s : first disjunct
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inl ?_)
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨u, hwu, ?_⟩
        rw [BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff]
        exact ⟨⟨s, hgt, hφ⟩, hψ⟩
  | df _ => exact absurd h_fc (show ¬ (FrameClass.ZTime ≤ FrameClass.Base) by decide)
  | dn _ => exact absurd h_fc (show ¬ (FrameClass.Dense ≤ FrameClass.Base) by decide)
  | co _ => exact absurd h_fc (show ¬ (FrameClass.RTime ≤ FrameClass.Base) by decide)

/-! ## Native soundness -/

theorem blFrameValid_of_derivation {φ : BLFormula}
    (d : BaseLanguage.DerivationTree FrameClass.Base [] φ) : BLFrameValid φ := by
  match d with
  | .axiom _ _ h_ax h_fc => exact axiom_valid h_ax h_fc
  | .assumption _ _ h_mem => exact absurd h_mem (by simp)
  | .modus_ponens _ ψ' _ d1 d2 =>
      exact fun F V w =>
        (blFrameValid_of_derivation d1 F V w) (blFrameValid_of_derivation d2 F V w)
  | .necessitation _ d' => exact fun F V _ v => blFrameValid_of_derivation d' F V v
  | .temporal_necessitation _ d' =>
      exact fun F V _ v _ => blFrameValid_of_derivation d' F V v
  | .temporal_duality φ' d' =>
      intro F V w
      exact (truth_swap F V w φ').mp (blFrameValid_of_derivation d' F.swap V w)
  | .weakening Γ' _ _ d' h_sub =>
      have h_term := BaseLanguage.DerivationTree.height_ofWeakeningNil_lt d' h_sub
      exact blFrameValid_of_derivation (d'.ofWeakeningNil h_sub)
termination_by d.height
decreasing_by
  all_goals first
    | omega
    | (simp only [BaseLanguage.DerivationTree.height]; omega)

end Scratch544

namespace Scratch544

open FormalSystem FormalSystem.Syntax FormalSystem.BaseLanguage FormalSystem.ProofSystem
open FormalSystem.Metalogic

/-! ## The two-fibre countermodel: `ℤ ⊕ ℝ` -/

private theorem sum_tri : ∀ (a b c : ℤ ⊕ ℝ), a < b → a < c → b < c ∨ b = c ∨ c < b := by
  rintro (m | x) (n | y) (k | z) h1 h2 <;> simp_all <;> exact lt_trichotomy _ _

private theorem sum_tri' : ∀ (a b c : ℤ ⊕ ℝ), b < a → c < a → b < c ∨ b = c ∨ c < b := by
  rintro (m | x) (n | y) (k | z) h1 h2 <;> simp_all <;> exact lt_trichotomy _ _

@[reducible] def twoFibre : BLFrame where
  Point := ℤ ⊕ ℝ
  lt := (· < ·)
  lt_trans := fun h1 h2 => lt_trans h1 h2
  lt_irrefl := fun a => lt_irrefl a
  no_max := by
    rintro (n | x)
    · exact ⟨Sum.inl (n + 1), by simp⟩
    · exact ⟨Sum.inr (x + 1), by simp⟩
  no_min := by
    rintro (n | x)
    · exact ⟨Sum.inl (n - 1), by simp⟩
    · exact ⟨Sum.inr (x - 1), by simp⟩
  fut_lin := fun {a b c} h1 h2 => sum_tri a b c h1 h2
  past_lin := fun {a b c} h1 h2 => sum_tri' a b c h1 h2

/-- The valuation: false exactly at `inl 1` on the `ℤ` fibre, and at the strictly positive
reals on the `ℝ` fibre. -/
def twoV : (ℤ ⊕ ℝ) → Atom → Prop
  | Sum.inl n, _ => n ≠ 1
  | Sum.inr r, _ => r ≤ 0

end Scratch544

namespace Scratch544

open FormalSystem FormalSystem.Syntax FormalSystem.BaseLanguage FormalSystem.ProofSystem
open FormalSystem.Metalogic

@[simp] theorem twoFibre_lt (a b : ℤ ⊕ ℝ) : twoFibre.lt a b ↔ a < b := Iff.rfl

@[simp] theorem twoFibre_atom (w : ℤ ⊕ ℝ) (a : Atom) :
    BLFrameTruth twoFibre twoV w (BLFormula.atom a) ↔ twoV w a := Iff.rfl

/-- **DF fails on the `ℝ` fibre.** -/
theorem df_fails (a : Atom) :
    ¬ BLFrameTruth twoFibre twoV (Sum.inr 0)
      (((((BLFormula.atom a).allPast).and (BLFormula.atom a)).and
          BLFormula.top.someFuture).imp ((BLFormula.atom a).allPast).someFuture) := by
  intro h
  have hante : BLFrameTruth twoFibre twoV (Sum.inr 0)
      ((((BLFormula.atom a).allPast).and (BLFormula.atom a)).and BLFormula.top.someFuture) := by
    rw [BLFrameTruth.and_iff, BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff]
    refine ⟨⟨?_, ?_⟩, ⟨Sum.inr 1, by simp, BLFrameTruth.top_true⟩⟩
    · rw [BLFrameTruth.past_iff]
      rintro (n | r) hlt
      · simp at hlt
      · simp only [Sum.inr_lt_inr_iff] at hlt
        exact le_of_lt hlt
    · show twoV (Sum.inr 0) a
      exact le_refl 0
  have hcons := h hante
  rw [BLFrameTruth.someFuture_iff] at hcons
  obtain ⟨v, hv, hHp⟩ := hcons
  match v, hv with
  | Sum.inl n, hv => simp at hv
  | Sum.inr r, hv =>
      simp only [Sum.inr_lt_inr_iff] at hv
      rw [BLFrameTruth.past_iff] at hHp
      have h2 : twoV (Sum.inr (r / 2)) a := by
        refine hHp (Sum.inr (r / 2)) ?_
        simp only [Sum.inr_lt_inr_iff]
        linarith
      have : r / 2 ≤ 0 := h2
      linarith

/-- **DN fails on the `ℤ` fibre.** -/
theorem dn_fails (a : Atom) :
    ¬ BLFrameTruth twoFibre twoV (Sum.inl 0)
      (((BLFormula.atom a).allFuture.allFuture).imp (BLFormula.atom a).allFuture) := by
  intro h
  have hante : BLFrameTruth twoFibre twoV (Sum.inl 0)
      ((BLFormula.atom a).allFuture.allFuture) := by
    rw [BLFrameTruth.future_iff]
    rintro (n | x) hn
    · rw [BLFrameTruth.future_iff]
      rintro (m | y) hm
      · simp only [Sum.inl_lt_inl_iff] at hn hm
        show m ≠ 1
        omega
      · simp at hm
    · simp at hn
  have hcons := h hante
  rw [BLFrameTruth.future_iff] at hcons
  have := hcons (Sum.inl 1) (by simp)
  have h1 : (1 : ℤ) ≠ 1 := this
  exact h1 rfl

/-- **`(Sp)` is false at every point of the two-fibre frame.** -/
theorem sp_false (a : Atom) (w : ℤ ⊕ ℝ) :
    ¬ BLFrameTruth twoFibre twoV w (Sp (BLFormula.atom a) (BLFormula.atom a)) := by
  intro h
  rw [Sp, BLFrameTruth.or_iff, BLFrameTruth.box_iff, BLFrameTruth.box_iff] at h
  rcases h with hl | hr
  · exact df_fails a (hl (Sum.inr 0))
  · exact dn_fails a (hr (Sum.inl 0))

/-- **`(Sp)` is not a theorem of TM.** -/
theorem not_derivable_sp (a : Atom) :
    ¬ BaseLanguage.Derivable FrameClass.Base [] (Sp (BLFormula.atom a) (BLFormula.atom a)) := by
  rintro ⟨d⟩
  exact sp_false a (Sum.inl 0) (blFrameValid_of_derivation d twoFibre twoV (Sum.inl 0))

/-- **TM is not weakly complete over task frames.** -/
theorem tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase := by
  intro h
  unfold TMCompleteBase TMComplete at h
  exact not_derivable_sp a (h _ (blValid_sp (BLFormula.atom a) (BLFormula.atom a)))

end Scratch544

#print axioms Scratch544.not_derivable_sp
#print axioms Scratch544.tmCompleteBase_refuted
#print axioms Scratch544.blFrameValid_of_derivation
