/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

import FormalSystem.Metalogic.Conservativity.SpWitness
import FormalSystem.Metalogic.Conservativity.TMCompletenessReduction
import FormalSystem.Semantics.BLFrame

set_option autoImplicit false

/-!
# The two-fibre countermodel and CEB's failing half

Machine-checks the claim `Metalogic/Conservativity/SpWitness.lean` explicitly disclaims: the
boxed dichotomy

  `(Sp) := □(DF φ) ∨ □(DN ψ)`

is **not** a theorem of TM, the tense-primitive base proof system
`BaseLanguage.DerivationTree FrameClass.Base`. Together with `SpWitness.blValid_sp` (`(Sp)` is
BL-valid on every task frame) this refutes TM's weak completeness over the task-frame class:
`tmCompleteBase_refuted : ¬ TMCompleteBase`, the `.Base` mirror of
`Z1Countermodel.tmCompleteZTime_refuted`.

## Why no task-frame refutation can exist

`(Sp)` is valid on *every* task frame, so the refuting structure must lie outside the class. The
route taken here is a native semantics: `Semantics/BLFrame.lean` supplies a frame notion with no
group structure on time, native BL soundness for TM is proved directly against it
(`blFrameValid_of_derivation`), and the countermodel is an instance of that class. Note the
contrast with the `TaskFrame`-bound stack: **TM⁺ is unsound** on the two-fibre structure below,
so no composition through `tr` and BL⁺ soundness is available. The soundness theorem in this
module is about TM (`BaseLanguage.DerivationTree`), never about TM⁺, and the two must not be
blurred.

## Why the countermodel needs *two* order shapes

Sharpened order-theoretic impossibility argument. Fix a strict linear order and a time `t`.

* The `DF` instance `(Hφ ∧ φ ∧ F⊤) → F(Hφ)` can fail at `t` only if `t` has **no immediate
  successor**: if `t < s` were least above `t`, then `Hφ` at `t` together with `φ` at `t` gives
  `Hφ` at `s`, so `F(Hφ)` holds.
* The `DN` instance `GGφ → Gφ` can fail at `t` only if `t` **has** an immediate successor: a
  failure needs a point `s > t` where `φ` fails while `φ` holds throughout the future of every
  future of `t`, which forces `s` to have no point of the future of `t` strictly below it.

The two failure conditions are mutually exclusive at a fixed time, regardless of the valuation,
the number of histories, or any group structure. So on a *single* linear order no time refutes
both disjuncts, and — since `□` is the universal modality — no point refutes `(Sp)`. A
countermodel therefore needs two differently-shaped orders simultaneously `□`-accessible. That is
exactly a **disjoint** sum of orders, `ℤ ⊕ ℝ` here, and *not* the lexicographic sum `ℤ + ℚ`: a
lexicographic sum is again a single linear order and is refuted by the argument above.

## The claim is schema-level, not universally quantified

"No instance of `(Sp)` is a theorem of TM" is **false as literally stated**, and must not be
re-attempted. `DF ⊤` is true at every point of every `BLFrame` (its consequent `F(H⊤)` follows
from `no_max`), so `□(DF ⊤)` holds everywhere and `Sp ⊤ ψ` is not refuted here — indeed it is
TM-derivable. The deliverable is the schema-level claim, witnessed by the atomic instance
`Sp (.atom a) (.atom a)`. Refuting `TMCompleteBase` needs exactly one BL-valid non-theorem, so
nothing is lost.

## Main Definitions

- `twoFibre` — the countermodel frame `ℤ ⊕ ℝ` (Mathlib's disjoint-sum order)
- `twoV` — its valuation

## Main Results

- `blFrameValid_of_axiom` — every TM axiom schema admissible at `FrameClass.Base` is `BLFrameValid`
- `blFrameValid_of_derivation` — **native BL soundness**: every TM theorem is `BLFrameValid`
- `df_fails`, `dn_fails` — the two disjuncts fail, on the `ℝ` and `ℤ` fibres respectively
- `sp_false` — `(Sp)` is false at every point of `twoFibre`
- `not_derivable_sp` — **CEB's failing half**: `(Sp)` is not a TM-theorem
- `tmCompleteBase_refuted` — `¬ TMCompleteBase`

## References

* `FormalSystem/Semantics/BLFrame.lean` — the native frame notion and `truth_swap`
* `FormalSystem/Metalogic/Conservativity/SpWitness.lean` — `Sp`, `blValid_sp`, `sp_translate`
* `FormalSystem/Metalogic/Conservativity/TMCompletenessReduction.lean` — `TMCompleteBase`
* `FormalSystem/Metalogic/Conservativity/Z1Countermodel.lean` — the `.ZTime` mirror
* `FormalSystem/Metalogic/Conservativity/BaseLanguageSoundness.lean` — the `TaskFrame`-bound
  soundness theorems this one deliberately does not route through

## Tags

conservativity · CEB · countermodel · underivability · native-soundness
-/

namespace FormalSystem.Metalogic

open FormalSystem.Syntax
open FormalSystem.BaseLanguage
open FormalSystem.ProofSystem
open FormalSystem.Semantics

/-! ## Native BL soundness for TM

Naming note: the axiom-validity lemma is `blFrameValid_of_axiom`, not the bare `axiom_valid` a
reader might expect by analogy with `Metalogic/Soundness.lean`. That base name is already taken
there by the BL⁺ lemma (about `Formula`, not `BLFormula`), and the repository's C23 invariant
additionally forbids resolving the clash by nesting a namespace — a shadowed base name defeats
the dead-declaration census. The `blFrameValid_of_*` pair also reads better together.
-/

/--
**Every TM axiom admissible at `FrameClass.Base` is valid on the native BL frame class.**

Sixteen `BaseLanguage.Axiom` constructors, thirteen of which have `minFrameClass = .Base`:

* propositional — `prop_k`, `prop_s`, `ex_falso`, `peirce` (`peirce` is the one classical step);
* modal — `modal_k`, `modal_t`, `modal_5`, `modal_future`, all immediate because `□` is the
  universal modality over `F.Point`;
* temporal — `temp_k`, `temp_4` (from `lt_trans`), `temp_serial` (from `no_max`), `temp_connect`,
  `temp_linearity` (from `fut_lin`, the longest branch).

The remaining three (`df`, `dn`, `co`) carry `minFrameClass` `.ZTime`, `.Dense`, `.RTime`, none of
which is `≤ .Base`, so the side condition `h_fc` is absurd for them. Exhaustiveness of `cases ax`
is what confirms the census — a missed constructor is a compile error, not an oversight.
-/
theorem blFrameValid_of_axiom {φ : BLFormula} (ax : BaseLanguage.Axiom φ)
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
      · -- `s < u` : third disjunct, `F(φ ∧ Fψ)` at `s`
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inr ((BLFrameTruth.or_iff _ _).mpr (Or.inr ?_)))
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨s, hws, ?_⟩
        rw [BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff]
        exact ⟨hφ, u, hlt, hψ⟩
      · -- `s = u` : second disjunct
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inr ((BLFrameTruth.or_iff _ _).mpr (Or.inl ?_)))
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨s, hws, ?_⟩
        rw [BLFrameTruth.and_iff]
        exact ⟨hφ, heq ▸ hψ⟩
      · -- `u < s` : first disjunct
        refine (BLFrameTruth.or_iff _ _).mpr (Or.inl ?_)
        rw [BLFrameTruth.someFuture_iff]
        refine ⟨u, hwu, ?_⟩
        rw [BLFrameTruth.and_iff, BLFrameTruth.someFuture_iff]
        exact ⟨⟨s, hgt, hφ⟩, hψ⟩
  | df _ => exact absurd h_fc (show ¬ (FrameClass.ZTime ≤ FrameClass.Base) by decide)
  | dn _ => exact absurd h_fc (show ¬ (FrameClass.Dense ≤ FrameClass.Base) by decide)
  | co _ => exact absurd h_fc (show ¬ (FrameClass.RTime ≤ FrameClass.Base) by decide)

/--
**Native BL soundness for TM.** Every closed `FrameClass.Base` derivation yields a formula valid
on the whole native BL frame class.

Recursion over all seven `BaseLanguage.DerivationTree` constructors. `assumption` is vacuous at
the empty context; `modus_ponens`, `necessitation` and `temporal_necessitation` are immediate
from the corresponding truth clauses (the last two because `BLFrameValid` already quantifies over
every point). `temporal_duality` is one line via `Semantics.truth_swap` at `F.swap`, which is
available precisely because the frame class is converse-closed. `weakening` routes through
`DerivationTree.ofWeakeningNil`, with `height_ofWeakeningNil_lt` supplying termination.
-/
theorem blFrameValid_of_derivation {φ : BLFormula}
    (d : BaseLanguage.DerivationTree FrameClass.Base [] φ) : BLFrameValid φ := by
  match d with
  | .axiom _ _ h_ax h_fc => exact blFrameValid_of_axiom h_ax h_fc
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

/-! ## The two-fibre countermodel: `ℤ ⊕ ℝ` -/

/-- Forward trichotomy on the disjoint-sum order `ℤ ⊕ ℝ`: two futures of a point are comparable.
The cross-fibre cases are impossible (nothing on one fibre is below anything on the other in
Mathlib's `Sum` order) and die by `simp_all`; the same-fibre cases are `lt_trichotomy`. -/
private theorem sum_tri : ∀ (a b c : ℤ ⊕ ℝ), a < b → a < c → b < c ∨ b = c ∨ c < b := by
  rintro (m | x) (n | y) (k | z) h1 h2 <;> simp_all <;> exact lt_trichotomy _ _

/-- Backward trichotomy on `ℤ ⊕ ℝ`: two pasts of a point are comparable. The past mirror of
`sum_tri`, proved the same way. -/
private theorem sum_tri' : ∀ (a b c : ℤ ⊕ ℝ), b < a → c < a → b < c ∨ b = c ∨ c < b := by
  rintro (m | x) (n | y) (k | z) h1 h2 <;> simp_all <;> exact lt_trichotomy _ _

/--
**The two-fibre frame.** `ℤ ⊕ ℝ` under Mathlib's disjoint-sum order: two incomparable copies of
time, one discrete and one dense-and-complete, both `□`-accessible because `□` is the universal
modality.

The **disjoint** sum is what the impossibility argument in the module docstring demands; a
*lexicographic* sum such as `ℤ + ℚ` is again a single linear order and cannot work. `ℝ` rather
than `ℚ` only because `linarith` is frictionless there — any dense order without endpoints would
do.

`@[reducible]` is load-bearing, not decoration: without it the valuation's type
`ℤ ⊕ ℝ → Atom → Prop` and the expected `twoFibre.Point → Atom → Prop` sit at different
transparency levels, and `rw [BLFrameTruth.and_iff]` fails on the mismatch.
-/
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

/-- The valuation on `twoFibre`, uniform in the atom: false exactly at `inl 1` on the `ℤ` fibre,
and at the strictly positive reals on the `ℝ` fibre. Atom-independence is why a *single* atom
witnesses both disjunct failures below. -/
def twoV : (ℤ ⊕ ℝ) → Atom → Prop
  | Sum.inl n, _ => n ≠ 1
  | Sum.inr r, _ => r ≤ 0

/-- The frame's order is the ambient `Sum` order; a `rfl` bridge so `simp` can see through
`twoFibre.lt`. -/
@[simp] theorem twoFibre_lt (a b : ℤ ⊕ ℝ) : twoFibre.lt a b ↔ a < b := Iff.rfl

/-- The atom clause on `twoFibre` is the valuation; a `rfl` bridge for `simp`. -/
@[simp] theorem twoFibre_atom (w : ℤ ⊕ ℝ) (a : Atom) :
    BLFrameTruth twoFibre twoV w (BLFormula.atom a) ↔ twoV w a := Iff.rfl

/--
**`DF` fails on the `ℝ` fibre.** At `inr 0` the antecedent `Hp ∧ p ∧ F⊤` holds — `p` is true
exactly on the non-positive reals, which is downward closed, and `inr 1` witnesses `F⊤` — while
the consequent `F(Hp)` fails: any later real `r > 0` has `r / 2` strictly between `0` and `r`
with `p` false there, so `Hp` fails at every witness.

This is the disjunct that needs a time with no immediate successor.
-/
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

/--
**`DN` fails on the `ℤ` fibre.** At `inl 0` the antecedent `GGp` holds — every point two steps
into the future is `inl m` with `m ≥ 2`, where `p` is true — while `Gp` fails at `inl 1`, the
one point where `p` is false.

This is the disjunct that needs a time with an immediate successor, which is why it cannot share
a fibre with `df_fails`.
-/
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

/--
**`(Sp)` is false at every point of the two-fibre frame.**

`□` is the universal modality, so each disjunct of `Sp` is refuted by exhibiting one point where
its body fails — `inr 0` for `DF` and `inl 0` for `DN`. The point `w` is therefore irrelevant.

A *single* atom witnesses both disjuncts, because `twoV` is uniform in the atom; no second atom
is introduced.
-/
theorem sp_false (a : Atom) (w : twoFibre.Point) :
    ¬ BLFrameTruth twoFibre twoV w (Sp (BLFormula.atom a) (BLFormula.atom a)) := by
  intro h
  rw [Sp, BLFrameTruth.or_iff, BLFrameTruth.box_iff, BLFrameTruth.box_iff] at h
  rcases h with hl | hr
  · exact df_fails a (hl (Sum.inr 0))
  · exact dn_fails a (hr (Sum.inl 0))

/--
**CEB's failing half: `(Sp)` is not a theorem of TM.**

The atomic instance `Sp p p` is `BLFrameValid`-refuted by `twoFibre`, and native BL soundness
(`blFrameValid_of_derivation`) says every TM theorem is `BLFrameValid`. This is
the claim `SpWitness.lean` disclaims as out of scope; it is now discharged.

The statement is deliberately **schema-level**, witnessed by an atomic instance. The universally
quantified reading — "no instance of `(Sp)` is a TM-theorem" — is *false*: `□(DF ⊤)` holds on
every `BLFrame` (its consequent follows from `no_max`), so `Sp ⊤ ψ` is not refuted here. See the
module docstring.
-/
theorem not_derivable_sp (a : Atom) :
    ¬ BaseLanguage.Derivable FrameClass.Base [] (Sp (BLFormula.atom a) (BLFormula.atom a)) := by
  rintro ⟨d⟩
  exact sp_false a (Sum.inl 0) (blFrameValid_of_derivation d twoFibre twoV (Sum.inl 0))

/--
**TM is not weakly complete over the task-frame class.** The negation of
`TMCompletenessReduction`'s `TMCompleteBase`, witnessed by `Sp p p`: `BLValid (Sp p p)` holds
(`SpWitness.blValid_sp`) yet `Sp p p` is not TM-derivable (`not_derivable_sp`).

Mirrors `Z1Countermodel.tmCompleteZTime_refuted` in shape. Only the **negation** is stated: per
`Metalogic/Conservativity.lean`'s standing prohibition, forward conservativity is refuted, not
open, and no theorem here concludes `TMCompleteBase`, `ForwardBase` or `forward` positively.

`TMCompleteBase` does not apply directly as a function, hence the `unfold` first.
-/
theorem tmCompleteBase_refuted (a : Atom) : ¬ TMCompleteBase := by
  intro h
  unfold TMCompleteBase TMComplete at h
  exact not_derivable_sp a (h _ (blValid_sp (BLFormula.atom a) (BLFormula.atom a)))

end FormalSystem.Metalogic
