/-
Probe 03 — axiom survival under C3 (the paper's line-1102 alternative semantics).

Research evidence of record for task 553, phase 4. Every declaration below is sorry-free and
compiles against the live tree with

  lake env lean specs/553_decide_convex_history_layer_collapse/probes/03_axiom-survival.lean

This probe is NOT part of the library and is never imported by it. It re-declares the C3
semantics of probe 02 rather than importing it (probes are not modules).

WHAT IT ESTABLISHES

  Germ structure
    `germ_untl_false`, `germ_snce_false`  — at a germ (point history) BOTH binary tense
        operators are outright false, so `G`/`H` are vacuously true and `F`/`P` outright false.
    `c3_box_untl_unsat`, `c3_box_snce_unsat` — consequently `□(φ U ψ)` and `□(φ S ψ)` are
        C3-UNSATISFIABLE for every `φ, ψ`: germs are always in C3's box range.
    `c3_nec` — C3 IS closed under necessitation (semantically).
    `c3_valid_imp_germ_valid` — every C3-validity is germ-valid. With `c3_nec` this is the
        governing constraint on the C3 logic: a theorem must survive at a one-point domain.

  Failures
    `refute_C3_serial_future`, `refute_C3_serial_past` — TM's two seriality axioms, verbatim.

  Survivals (each stated at the axiom's verbatim formula, for an arbitrary task frame)
    `c3_modal_t`, `c3_modal_4`, `c3_modal_b`, `c3_modal_5_collapse`, `c3_modal_k_dist`
    `c3_connect_future`, `c3_connect_past`, `c3_until_F`, `c3_since_P`
    `c3_F_until_equiv`, `c3_P_since_equiv`

  Shift invariance
    `truthC3_timeShift` — C3 truth is invariant under time translation of the index. This is
        the C3 analogue of `app:auto_existence`, and it is what settles `modal_future`.
    `c3_modal_future` — TM's one modal/temporal interaction axiom, `□φ → □Gφ`, SURVIVES C3.
-/
import FormalSystem.Semantics.ShiftSet
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.SuccPred

open FormalSystem.Syntax FormalSystem.Semantics
open scoped Classical

namespace Probe553C

variable {F : TaskFrame}

/-- C3 truth — the paper's line-1102 alternative. Identical to probe 02's `TruthAtConvex`. -/
def TruthAtConvex (M : TaskModel F) (τ : ConvexHistory F) (t : F.Duration) : Formula → Prop
  | Formula.atom p => ∃ (ht : τ.domain t), M.valuation (τ.states t ht) p
  | Formula.bot => False
  | Formula.imp φ ψ => TruthAtConvex M τ t φ → TruthAtConvex M τ t ψ
  | Formula.box φ => ∀ (σ : ConvexHistory F), σ.domain t → TruthAtConvex M σ t φ
  | Formula.untl ψ φ => ∃ s : F.Duration, τ.domain s ∧ t < s ∧ TruthAtConvex M τ s φ ∧
      ∀ r : F.Duration, τ.domain r → t < r → r < s → TruthAtConvex M τ r ψ
  | Formula.snce ψ φ => ∃ s : F.Duration, τ.domain s ∧ s < t ∧ TruthAtConvex M τ s φ ∧
      ∀ r : F.Duration, τ.domain r → s < r → r < t → TruthAtConvex M τ r ψ

/-- C3 validity at a fixed frame. -/
def ValidC3 (F : TaskFrame) (φ : Formula) : Prop :=
  ∀ (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration), τ.domain x → TruthAtConvex M τ x φ

/-- The germ `{⟨x, w⟩}` as a convex history. Identical to probe 02's `pointHist`. -/
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

theorem pointHist_domain_self (F : TaskFrame) (w : F.WorldState) (x : F.Duration) :
    (pointHist F w x).domain x := rfl

/-! ## Germ structure: both binary tense operators are false at a germ -/

/-- At a germ, `φ U ψ` is false: its witness would have to lie in a one-point domain and be
strictly later than that point. -/
theorem germ_untl_false (M : TaskModel F) (w : F.WorldState) (x : F.Duration) (ψ φ : Formula) :
    ¬ TruthAtConvex M (pointHist F w x) x (Formula.untl ψ φ) := by
  rintro ⟨s, hs, hxs, -, -⟩
  subst hs
  exact lt_irrefl _ hxs

/-- At a germ, `φ S ψ` is false, symmetrically. -/
theorem germ_snce_false (M : TaskModel F) (w : F.WorldState) (x : F.Duration) (ψ φ : Formula) :
    ¬ TruthAtConvex M (pointHist F w x) x (Formula.snce ψ φ) := by
  rintro ⟨s, hs, hsx, -, -⟩
  subst hs
  exact lt_irrefl _ hsx

/--
**`□(φ U ψ)` is C3-UNSATISFIABLE**, at every model, every convex index and every time, over an
arbitrary task frame. The germ at `x` is always in C3's box range at `x`, and no binary tense
formula is true at a germ.

This is the single most consequential structural fact about C3. TM's `serial_future` gives
`⊢ F⊤ = ⊢ ⊤ U ⊤`, and TM is closed under necessitation, so `⊢ □F⊤`. A semantics on which every
boxed `U`-formula is unsatisfiable is therefore not TM-minus-an-axiom: the interaction between
necessitation and the germ indices is what breaks, and it breaks for every formula whose
principal connective is a binary tense operator, not just for `F⊤`.
-/
theorem c3_box_untl_unsat (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (ψ φ : Formula) : ¬ TruthAtConvex M τ x (Formula.box (Formula.untl ψ φ)) := by
  intro h
  obtain ⟨w⟩ := (inferInstance : Nonempty F.WorldState)
  exact germ_untl_false M w x ψ φ (h (pointHist F w x) (pointHist_domain_self F w x))

/-- The past dual. -/
theorem c3_box_snce_unsat (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration)
    (ψ φ : Formula) : ¬ TruthAtConvex M τ x (Formula.box (Formula.snce ψ φ)) := by
  intro h
  obtain ⟨w⟩ := (inferInstance : Nonempty F.WorldState)
  exact germ_snce_false M w x ψ φ (h (pointHist F w x) (pointHist_domain_self F w x))

/-- **C3 is closed under necessitation**, semantically: a C3-validity is true at every convex
index through the evaluation time, which is exactly what `□` asks for. -/
theorem c3_nec {φ : Formula} (h : ValidC3 F φ) : ValidC3 F (Formula.box φ) :=
  fun M _τ x _hx σ hσ => h M σ x hσ

/--
**Every C3-validity is germ-valid.** Taking the index to be the germ at `x`.

Combined with `c3_nec` and `c3_box_untl_unsat`, this is the governing constraint on the C3
logic: a theorem must survive evaluation at a one-point domain, where every binary tense
operator is false. `F⊤` does not, which is why TS goes.
-/
theorem c3_valid_imp_germ_valid {φ : Formula} (h : ValidC3 F φ) (M : TaskModel F)
    (w : F.WorldState) (x : F.Duration) : TruthAtConvex M (pointHist F w x) x φ :=
  h M (pointHist F w x) x (pointHist_domain_self F w x)

/-! ## The two failures: TM's seriality axioms, verbatim -/

/-- The permissive frame over `ℤ`. -/
abbrev NF : TaskFrame := FrameOver.natFrame (D := ℤ)

/-- The bounded index `[0, 0]` over `NF`. -/
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

/-- **`serial_future` FAILS under C3**, at its verbatim `Axiom` statement
`⊤ → F⊤` (`ProofSystem/Axioms.lean:140`). -/
theorem refute_C3_serial_future :
    ¬ ValidC3 NF ((Formula.bot.imp Formula.bot).imp
      (Formula.someFuture (Formula.bot.imp Formula.bot))) := by
  intro h
  obtain ⟨s, ⟨-, hs0⟩, h0s, -, -⟩ := h TaskModel.allTrue bdd 0 bdd_zero_mem (fun c => c)
  exact absurd (lt_of_lt_of_le h0s hs0) (lt_irrefl 0)

/-- **`serial_past` FAILS under C3**, at its verbatim `Axiom` statement `⊤ → P⊤`
(`ProofSystem/Axioms.lean:144`). -/
theorem refute_C3_serial_past :
    ¬ ValidC3 NF ((Formula.bot.imp Formula.bot).imp
      (Formula.somePast (Formula.bot.imp Formula.bot))) := by
  intro h
  obtain ⟨s, ⟨hs0, -⟩, hs, -, -⟩ := h TaskModel.allTrue bdd 0 bdd_zero_mem (fun c => c)
  exact absurd (lt_of_le_of_lt hs0 hs) (lt_irrefl 0)

/-! ## The survivals -/

/-- `modal_t`: `□φ → φ`. Uses the C3 side condition `x ∈ dom τ`. -/
theorem c3_modal_t (φ : Formula) : ValidC3 F (Formula.imp (Formula.box φ) φ) :=
  fun _M τ _x hx h => h τ hx

/-- `modal_4`: `□φ → □□φ`. C3's box is index-independent. -/
theorem c3_modal_4 (φ : Formula) :
    ValidC3 F (Formula.imp (Formula.box φ) (Formula.box (Formula.box φ))) :=
  fun _M _τ _x _hx h _σ _ ρ hρ => h ρ hρ

/-- `modal_b`: `φ → □◇φ`. -/
theorem c3_modal_b (φ : Formula) : ValidC3 F (Formula.imp φ (Formula.box φ.diamond)) :=
  fun _M τ _x hx hφ _σ _ hbox => hbox τ hx hφ

/-- `modal_5_collapse`: `◇□φ → □φ`. Classical. -/
theorem c3_modal_5_collapse (φ : Formula) : ValidC3 F (Formula.imp φ.box.diamond φ.box) := by
  intro _M _τ _x _hx h σ hσ
  by_contra hcon
  exact h (fun ρ _ hbox => hcon (hbox σ hσ))

/-- `modal_k_dist`: `□(φ→ψ) → (□φ → □ψ)`. -/
theorem c3_modal_k_dist (φ ψ : Formula) :
    ValidC3 F (Formula.imp (φ.imp ψ).box (φ.box.imp ψ.box)) :=
  fun _M _τ _x _hx himp hφ σ hσ => himp σ hσ (hφ σ hσ)

/-! ### The tense survivals need the `someFuture` / `allFuture` characterizations -/

theorem c3_someFuture_iff (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (φ : Formula) :
    TruthAtConvex M τ x (Formula.someFuture φ) ↔
      ∃ s, τ.domain s ∧ x < s ∧ TruthAtConvex M τ s φ :=
  ⟨fun ⟨s, hs, hxs, hφ, _⟩ => ⟨s, hs, hxs, hφ⟩,
   fun ⟨s, hs, hxs, hφ⟩ => ⟨s, hs, hxs, hφ, fun _ _ _ _ h => h⟩⟩

theorem c3_somePast_iff (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (φ : Formula) :
    TruthAtConvex M τ x (Formula.somePast φ) ↔
      ∃ s, τ.domain s ∧ s < x ∧ TruthAtConvex M τ s φ :=
  ⟨fun ⟨s, hs, hsx, hφ, _⟩ => ⟨s, hs, hsx, hφ⟩,
   fun ⟨s, hs, hsx, hφ⟩ => ⟨s, hs, hsx, hφ, fun _ _ _ _ h => h⟩⟩

theorem c3_allFuture_iff (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (φ : Formula) :
    TruthAtConvex M τ x (Formula.allFuture φ) ↔
      ∀ s, τ.domain s → x < s → TruthAtConvex M τ s φ := by
  constructor
  · intro h s hs hxs
    by_contra hcon
    exact h ((c3_someFuture_iff M τ x φ.neg).mpr ⟨s, hs, hxs, hcon⟩)
  · intro h hcon
    obtain ⟨s, hs, hxs, hneg⟩ := (c3_someFuture_iff M τ x φ.neg).mp hcon
    exact hneg (h s hs hxs)

theorem c3_allPast_iff (M : TaskModel F) (τ : ConvexHistory F) (x : F.Duration) (φ : Formula) :
    TruthAtConvex M τ x (Formula.allPast φ) ↔
      ∀ s, τ.domain s → s < x → TruthAtConvex M τ s φ := by
  constructor
  · intro h s hs hsx
    by_contra hcon
    exact h ((c3_somePast_iff M τ x φ.neg).mpr ⟨s, hs, hsx, hcon⟩)
  · intro h hcon
    obtain ⟨s, hs, hsx, hneg⟩ := (c3_somePast_iff M τ x φ.neg).mp hcon
    exact hneg (h s hs hsx)

/-- `connect_future` (BX4): `φ → G(Pφ)`. The present is in the past of every later domain time,
because the C3 side condition puts `x` itself in `dom τ`. -/
theorem c3_connect_future (φ : Formula) : ValidC3 F (φ.imp φ.somePast.allFuture) := by
  intro M τ x hx hφ
  refine (c3_allFuture_iff M τ x φ.somePast).mpr fun s hs hxs => ?_
  exact (c3_somePast_iff M τ s φ).mpr ⟨x, hx, hxs, hφ⟩

/-- `connect_past` (BX4'): `φ → H(Fφ)`. -/
theorem c3_connect_past (φ : Formula) : ValidC3 F (φ.imp φ.someFuture.allPast) := by
  intro M τ x hx hφ
  refine (c3_allPast_iff M τ x φ.someFuture).mpr fun s hs hsx => ?_
  exact (c3_someFuture_iff M τ s φ).mpr ⟨x, hx, hsx, hφ⟩

/-- `until_F` (BX11): `(φ U ψ) → Fψ`. -/
theorem c3_until_F (φ ψ : Formula) :
    ValidC3 F ((Formula.untl φ ψ).imp (Formula.someFuture ψ)) := by
  intro M τ x _hx h
  obtain ⟨s, hs, hxs, hψ, -⟩ := h
  exact (c3_someFuture_iff M τ x ψ).mpr ⟨s, hs, hxs, hψ⟩

/-- `since_P` (BX11'): `(φ S ψ) → Pψ`. -/
theorem c3_since_P (φ ψ : Formula) :
    ValidC3 F ((Formula.snce φ ψ).imp (Formula.somePast ψ)) := by
  intro M τ x _hx h
  obtain ⟨s, hs, hsx, hψ, -⟩ := h
  exact (c3_somePast_iff M τ x ψ).mpr ⟨s, hs, hsx, hψ⟩

/-- `F_until_equiv` (BX12): `Fφ → U(⊤, φ)`. Definitional under C3, as under C1. -/
theorem c3_F_until_equiv (φ : Formula) :
    ValidC3 F ((Formula.someFuture φ).imp (Formula.untl (Formula.bot.imp Formula.bot) φ)) :=
  fun _M _τ _x _hx h => h

/-- `P_since_equiv` (BX12'): `Pφ → S(⊤, φ)`. -/
theorem c3_P_since_equiv (φ : Formula) :
    ValidC3 F ((Formula.somePast φ).imp (Formula.snce (Formula.bot.imp Formula.bot) φ)) :=
  fun _M _τ _x _hx h => h

/-! ## Shift invariance, and `modal_future` -/

/--
**C3 truth is invariant under time translation of the index.**

`TruthAtConvex M (σ.timeShift Δ) z φ ↔ TruthAtConvex M σ (z + Δ) φ`, for every formula, index,
time and offset. The box case is the substantive one: the convex histories through `z` and the
convex histories through `z + Δ` are exchanged by `timeShift`, so C3's box range translates
along with everything else.

This is the C3 analogue of the paper's `app:auto_existence` (the possible worlds are closed
under translation). It is what makes C3 a time-uniform semantics despite its indices being
bounded, and it is the lemma that settles `modal_future`.
-/
theorem truthC3_timeShift (M : TaskModel F) (φ : Formula) :
    ∀ (σ : ConvexHistory F) (z Δ : F.Duration),
      TruthAtConvex M (σ.timeShift Δ) z φ ↔ TruthAtConvex M σ (z + Δ) φ := by
  induction φ with
  | atom p => intro _ _ _; exact Iff.rfl
  | bot => intro _ _ _; exact Iff.rfl
  | imp φ ψ ihφ ihψ => intro σ z Δ; exact imp_congr (ihφ σ z Δ) (ihψ σ z Δ)
  | box φ ih =>
      intro σ z Δ
      constructor
      · intro h ρ hρ
        exact (ih ρ z Δ).mp (h (ρ.timeShift Δ) hρ)
      · intro h ρ hρ
        have hdom : (ρ.timeShift (-Δ)).domain (z + Δ) := by
          show ρ.domain (z + Δ + -Δ)
          simpa using hρ
        have hz : TruthAtConvex M ρ (z + Δ + -Δ) φ := (ih ρ (z + Δ) (-Δ)).mp (h _ hdom)
        simpa using hz
  | untl ψ φ ihψ ihφ =>
      intro σ z Δ
      constructor
      · rintro ⟨s, hs, hzs, hφ, hψ⟩
        refine ⟨s + Δ, hs, add_lt_add_of_lt_of_le hzs (le_refl Δ), (ihφ σ s Δ).mp hφ, ?_⟩
        intro r hr hzr hrs
        have hback : r - Δ + Δ = r := sub_add_cancel r Δ
        have hdom : (σ.timeShift Δ).domain (r - Δ) := by
          show σ.domain (r - Δ + Δ); rw [hback]; exact hr
        have h1 : z < r - Δ := by
          have := hzr; rw [← hback] at this; exact lt_of_add_lt_add_right this
        have h2 : r - Δ < s := by
          have := hrs; rw [← hback] at this; exact lt_of_add_lt_add_right this
        have := (ihψ σ (r - Δ) Δ).mp (hψ (r - Δ) hdom h1 h2)
        rwa [hback] at this
      · rintro ⟨s, hs, hzs, hφ, hψ⟩
        have hback : s - Δ + Δ = s := sub_add_cancel s Δ
        have hdom : (σ.timeShift Δ).domain (s - Δ) := by
          show σ.domain (s - Δ + Δ); rw [hback]; exact hs
        have h1 : z < s - Δ := by
          have := hzs; rw [← hback] at this; exact lt_of_add_lt_add_right this
        refine ⟨s - Δ, hdom, h1, (ihφ σ (s - Δ) Δ).mpr (by rw [hback]; exact hφ), ?_⟩
        intro r hr hzr hrs
        refine (ihψ σ r Δ).mpr (hψ (r + Δ) hr (add_lt_add_of_lt_of_le hzr (le_refl Δ)) ?_)
        have := add_lt_add_of_lt_of_le hrs (le_refl Δ)
        rwa [hback] at this
  | snce ψ φ ihψ ihφ =>
      intro σ z Δ
      constructor
      · rintro ⟨s, hs, hsz, hφ, hψ⟩
        refine ⟨s + Δ, hs, add_lt_add_of_lt_of_le hsz (le_refl Δ), (ihφ σ s Δ).mp hφ, ?_⟩
        intro r hr hsr hrz
        have hback : r - Δ + Δ = r := sub_add_cancel r Δ
        have hdom : (σ.timeShift Δ).domain (r - Δ) := by
          show σ.domain (r - Δ + Δ); rw [hback]; exact hr
        have h1 : s < r - Δ := by
          have := hsr; rw [← hback] at this; exact lt_of_add_lt_add_right this
        have h2 : r - Δ < z := by
          have := hrz; rw [← hback] at this; exact lt_of_add_lt_add_right this
        have := (ihψ σ (r - Δ) Δ).mp (hψ (r - Δ) hdom h1 h2)
        rwa [hback] at this
      · rintro ⟨s, hs, hsz, hφ, hψ⟩
        have hback : s - Δ + Δ = s := sub_add_cancel s Δ
        have hdom : (σ.timeShift Δ).domain (s - Δ) := by
          show σ.domain (s - Δ + Δ); rw [hback]; exact hs
        have h1 : s - Δ < z := by
          have := hsz; rw [← hback] at this; exact lt_of_add_lt_add_right this
        refine ⟨s - Δ, hdom, h1, (ihφ σ (s - Δ) Δ).mpr (by rw [hback]; exact hφ), ?_⟩
        intro r hr hsr hrz
        refine (ihψ σ r Δ).mpr (hψ (r + Δ) hr ?_ (add_lt_add_of_lt_of_le hrz (le_refl Δ)))
        have := add_lt_add_of_lt_of_le hsr (le_refl Δ)
        rwa [hback] at this

/--
**C3's box is time-uniform.** If `□φ` holds at `x` then it holds at every time `y`, because the
convex histories through `x` and through `y` are exchanged by `timeShift` and `truthC3_timeShift`
carries truth across.
-/
theorem c3_box_time_uniform (M : TaskModel F) (τ τ' : ConvexHistory F) (x y : F.Duration)
    (φ : Formula) (h : TruthAtConvex M τ x (Formula.box φ)) :
    TruthAtConvex M τ' y (Formula.box φ) := by
  intro ρ hρ
  have hdom : (ρ.timeShift (y - x)).domain x := by
    show ρ.domain (x + (y - x))
    have : x + (y - x) = y := by rw [add_sub_cancel]
    rw [this]; exact hρ
  have := h (ρ.timeShift (y - x)) hdom
  have h2 := (truthC3_timeShift M φ ρ x (y - x)).mp this
  have hxy : x + (y - x) = y := by rw [add_sub_cancel]
  rwa [hxy] at h2

/--
**`modal_future` SURVIVES C3**: `□φ → □(Gφ)`, TM's one modal/temporal interaction axiom
(`ProofSystem/Axioms.lean:185`), for an arbitrary task frame.

The proof is `c3_box_time_uniform`: `□φ` at `x` gives `□φ` at every later domain time `s`, and
`□φ` at `s` gives `φ` at `(σ, s)` for the very `σ` under consideration, since the C3 side
condition puts `σ` in the box's range at `s`.

Note what this does NOT rescue. `□Gφ` is a boxed formula whose body is `¬(⊤ U ¬φ)`, not a boxed
`U`-formula, so `c3_box_untl_unsat` does not apply to it — `G` is vacuously TRUE at germs, where
`F` is false. The axiom survives precisely because the germ-degeneracy of the tense operators
falls on the existential side.
-/
theorem c3_modal_future (φ : Formula) :
    ValidC3 F ((Formula.box φ).imp (Formula.box (Formula.allFuture φ))) := by
  intro M τ x _hx h σ hσ
  refine (c3_allFuture_iff M σ x φ).mpr fun s hs _hxs => ?_
  exact (c3_box_time_uniform M τ σ x s φ h) σ hs

/-! ## The uniformity layer collapses, asymmetrically -/

/-- The bounded index `[0, 1]` over `NF`. Over `ℤ` this domain has an immediate-successor pair
and two endpoints, which is exactly what the uniformity axioms talk about. -/
def bdd01 : ConvexHistory NF where
  domain := fun t => 0 ≤ t ∧ t ≤ 1
  nonempty_domain := ⟨0, by decide, by decide⟩
  states := fun _ _ => (0 : Nat)
  respects_task := fun s t _ _ => by
    by_cases h : t - s = 0
    · right; rfl
    · left; exact h
  convex := fun x z hx hz y hxy hyz => ⟨le_trans hx.1 hxy, le_trans hyz hz.2⟩

theorem bdd01_zero : bdd01.domain 0 := ⟨by decide, by decide⟩
theorem bdd01_one : bdd01.domain 1 := ⟨by decide, by decide⟩

/-- `next ⊤` — the discreteness witness `U(⊥, ⊤)` — holds at `(bdd01, 0)`: `1` is the immediate
successor of `0` in the domain. -/
theorem next_top_at_zero (M : TaskModel NF) :
    TruthAtConvex M bdd01 0 (Formula.untl Formula.bot (Formula.bot.imp Formula.bot)) :=
  ⟨1, bdd01_one, by decide, fun c => c, by
    intro r _ h0r hr1
    exfalso
    have a : (0 : ℤ) + 1 ≤ (r : ℤ) := Int.lt_iff_add_one_le.mp h0r
    have a' : (1 : ℤ) ≤ (r : ℤ) := by simpa using a
    exact absurd (show (r : ℤ) < 1 from hr1) (not_lt.mpr a')⟩

/-- `next ⊤` FAILS at `(bdd01, 1)`: the right endpoint has no later domain time at all. -/
theorem not_next_top_at_one (M : TaskModel NF) :
    ¬ TruthAtConvex M bdd01 1 (Formula.untl Formula.bot (Formula.bot.imp Formula.bot)) := by
  rintro ⟨s, ⟨-, hs1⟩, h1s, -, -⟩
  exact absurd (lt_of_lt_of_le h1s hs1) (lt_irrefl 1)

/-- `prev ⊤` — `S(⊥, ⊤)` — FAILS at `(bdd01, 0)`: the left endpoint has no earlier domain time. -/
theorem not_prev_top_at_zero (M : TaskModel NF) :
    ¬ TruthAtConvex M bdd01 0 (Formula.snce Formula.bot (Formula.bot.imp Formula.bot)) := by
  rintro ⟨s, ⟨hs0, -⟩, hs, -, -⟩
  exact absurd (lt_of_le_of_lt hs0 hs) (lt_irrefl 0)

/-- `prev ⊤` holds at `(bdd01, 1)`. -/
theorem prev_top_at_one (M : TaskModel NF) :
    TruthAtConvex M bdd01 1 (Formula.snce Formula.bot (Formula.bot.imp Formula.bot)) :=
  ⟨0, bdd01_zero, by decide, fun c => c, by
    intro r _ h0r hr1
    exfalso
    have a : (0 : ℤ) + 1 ≤ (r : ℤ) := Int.lt_iff_add_one_le.mp h0r
    have a' : (1 : ℤ) ≤ (r : ℤ) := by simpa using a
    exact absurd (show (r : ℤ) < 1 from hr1) (not_lt.mpr a')⟩

/-- **`discrete_symm_fwd` FAILS under C3**: `U(⊤,⊥) → S(⊤,⊥)` is refuted at the LEFT endpoint,
where a forward gap exists and no backward one can. -/
theorem refute_C3_discrete_symm_fwd :
    ¬ ValidC3 NF ((Formula.untl Formula.bot (Formula.bot.imp Formula.bot)).imp
      (Formula.snce Formula.bot (Formula.bot.imp Formula.bot))) := fun h =>
  not_prev_top_at_zero TaskModel.allTrue
    (h TaskModel.allTrue bdd01 0 bdd01_zero (next_top_at_zero TaskModel.allTrue))

/-- **`discrete_symm_bwd` FAILS under C3**, dually, at the RIGHT endpoint. -/
theorem refute_C3_discrete_symm_bwd :
    ¬ ValidC3 NF ((Formula.snce Formula.bot (Formula.bot.imp Formula.bot)).imp
      (Formula.untl Formula.bot (Formula.bot.imp Formula.bot))) := fun h =>
  not_next_top_at_one TaskModel.allTrue
    (h TaskModel.allTrue bdd01 1 bdd01_one (prev_top_at_one TaskModel.allTrue))

/-- **`discrete_propagate_fwd` FAILS under C3**: `U(⊤,⊥) → G(U(⊤,⊥))`. The gap at `0` does not
propagate to `1`, because `G` now reaches the right endpoint, where no gap exists. -/
theorem refute_C3_discrete_propagate_fwd :
    ¬ ValidC3 NF ((Formula.untl Formula.bot (Formula.bot.imp Formula.bot)).imp
      (Formula.allFuture (Formula.untl Formula.bot (Formula.bot.imp Formula.bot)))) := by
  intro h
  have hG := h TaskModel.allTrue bdd01 0 bdd01_zero (next_top_at_zero TaskModel.allTrue)
  have := (c3_allFuture_iff TaskModel.allTrue bdd01 0
    (Formula.untl Formula.bot (Formula.bot.imp Formula.bot))).mp hG 1 bdd01_one (by decide)
  exact not_next_top_at_one TaskModel.allTrue this

/--
**`discrete_box_necessity` FAILS under C3**: `U(⊤,⊥) → □(U(⊤,⊥))`. Its consequent is a boxed
`U`-formula, hence C3-unsatisfiable by `c3_box_untl_unsat`, while its antecedent is satisfiable.

This is the germ theorem cashed out on a named TM axiom, and it shows that the failure is not
confined to the seriality axioms: any axiom whose consequent boxes a binary tense formula goes
the same way.
-/
theorem refute_C3_discrete_box_necessity :
    ¬ ValidC3 NF ((Formula.untl Formula.bot (Formula.bot.imp Formula.bot)).imp
      (Formula.box (Formula.untl Formula.bot (Formula.bot.imp Formula.bot)))) := fun h =>
  c3_box_untl_unsat TaskModel.allTrue bdd01 0 Formula.bot (Formula.bot.imp Formula.bot)
    (h TaskModel.allTrue bdd01 0 bdd01_zero (next_top_at_zero TaskModel.allTrue))

end Probe553C
