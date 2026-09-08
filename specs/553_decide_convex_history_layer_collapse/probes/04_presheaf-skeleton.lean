/-
Probe 04 — the behavior presheaf `Beh(F)`, as far as one agent run reaches.

Research evidence of record for task 553, phase 5. Every declaration below is sorry-free and
compiles against the live tree with

  lake env lean specs/553_decide_convex_history_layer_collapse/probes/04_presheaf-skeleton.lean

This probe is NOT part of the library and is never imported by it.

WHAT IT ESTABLISHES, against the paper's `def:behavior-presheaf` and `app:presheaf-dictionary`

  * `Beh F l` — the sections over the duration `l`: the convex histories whose domain is exactly
    the closed interval `[0, l]`. This is `def:behavior-presheaf`'s `Beh(F)(ℓ)` on the nose, and
    it is a PROPER SUBFAMILY of `ConvexHistory F`, whose domain is an arbitrary convex predicate.
  * `restrict` — restriction along the translation `Tr p : l' → l` of `def:interval-site`,
    sending `τ` to `z ↦ τ(p + z)`.
  * `restrict_id`, `restrict_comp` — PRESHEAF FUNCTORIALITY: `Tr 0` acts as the identity and
    `Tr p ∘ Tr p' = Tr (p + p')`. Together these are the opening paragraph of
    `app:presheaf-dictionary`'s proof ("so `Beh(F)` is a presheaf").
  * `germ`, `ofGerm`, `germ_ofGerm`, `ofGerm_germ` — the GERMS clause of
    `app:presheaf-dictionary`: `Beh(F)(0) ≅ W`, with `lem:nullity` (`F.nullity_identity`)
    supplying the one obligation, exactly as the paper's proof says.

  * `glue_seam` — the composition step of `app:gluing` at the interval site: the task relation
    holds ACROSS the seam between two sections whose germs agree there. This is the only place
    `app:gluing`'s proof does real work, and the library already carries the same argument for
    TOTAL histories in `StarPasting.paste_rel_le_lt`.

WHAT IT DELIBERATELY DOES NOT ESTABLISH (see the report's section 5 and its follow-on tasks):
  the *Sheaf* clause proper (assembling the glued section and proving the two restriction
  identities and uniqueness — bookkeeping over `glue_seam`), Directed Gluing, Totality,
  Possible Worlds, Determinism, Reflection. Those are stated in the report and left unproved.
-/
import FormalSystem.Semantics.ShiftSet
import Mathlib.Algebra.Order.Group.Int

open FormalSystem.Semantics

namespace Probe553D

variable {F : TaskFrame}

/-! ## Sections of the behavior presheaf -/

/--
`Beh(F)(l)` — the sections over the duration `l`.

`def:behavior-presheaf`, verbatim: "The *behavior presheaf* `Beh(F)` assigns to each `ℓ ∈ D⁺`
the set `Beh(F)(ℓ)` of convex histories with domain `[0, ℓ]`."

Note what this is NOT: it is not `ConvexHistory F`, whose `domain` is an arbitrary convex
predicate. The presheaf selects the closed-bounded-interval sub-family. Every statement of
`app:presheaf-dictionary` is about this sub-family, which is why the presheaf apparatus needs a
convex layer but does not need the whole of one.
-/
def Beh (F : TaskFrame) (l : F.Duration) : Type :=
  { τ : ConvexHistory F // ∀ t, τ.domain t ↔ (0 ≤ t ∧ t ≤ l) }

namespace Beh

/-- A section's underlying history has the interval domain, in the direction usually needed. -/
theorem mem_dom {l : F.Duration} (τ : Beh F l) {t : F.Duration} (h0 : 0 ≤ t) (hl : t ≤ l) :
    τ.val.domain t := (τ.property t).mpr ⟨h0, hl⟩

/-! ## Restriction along the translations of the interval site -/

/--
Restriction along `Tr p : l' → l`, the translation of `def:interval-site` that "places `[0, l']`
as the subinterval `[p, p + l']` of `[0, l]`". Its action is `def:behavior-presheaf`'s: the
section `τ ∈ Beh(F)(l)` goes to `z ↦ τ(p + z)` on `[0, l']`.
-/
def restrict {l : F.Duration} (p l' : F.Duration) (hp : 0 ≤ p) (hl' : 0 ≤ l')
    (hple : p + l' ≤ l) (τ : Beh F l) : Beh F l' :=
  ⟨{ domain := fun z => 0 ≤ z ∧ z ≤ l'
     nonempty_domain := ⟨0, le_refl 0, hl'⟩
     states := fun z hz =>
       τ.val.states (p + z) (mem_dom τ (add_nonneg hp hz.1)
         (le_trans (add_le_add (le_refl p) hz.2) hple))
     respects_task := by
       intro s t hs ht
       have h := τ.val.respects_task (p + s) (p + t)
         (mem_dom τ (add_nonneg hp hs.1) (le_trans (add_le_add (le_refl p) hs.2) hple))
         (mem_dom τ (add_nonneg hp ht.1) (le_trans (add_le_add (le_refl p) ht.2) hple))
       rwa [add_sub_add_left_eq_sub] at h
     convex := by
       intro a c ha hc y hay hyc
       exact ⟨le_trans ha.1 hay, le_trans hyc hc.2⟩ },
   fun _ => Iff.rfl⟩

/-- The restricted section's domain is the interval `[0, l']`, definitionally. -/
theorem restrict_domain {l : F.Duration} (p l' : F.Duration) (hp : 0 ≤ p) (hl' : 0 ≤ l')
    (hple : p + l' ≤ l) (τ : Beh F l) (z : F.Duration) :
    (restrict p l' hp hl' hple τ).val.domain z = (0 ≤ z ∧ z ≤ l') := rfl

/-- The restricted section's value at `z` is the original's at `p + z`. Definitional, using
Lean's proof irrelevance to discharge the domain-proof argument. -/
theorem restrict_states {l : F.Duration} (p l' : F.Duration) (hp : 0 ≤ p) (hl' : 0 ≤ l')
    (hple : p + l' ≤ l) (τ : Beh F l) (z : F.Duration)
    (hz : (restrict p l' hp hl' hple τ).val.domain z) (hpz : τ.val.domain (p + z)) :
    (restrict p l' hp hl' hple τ).val.states z hz = τ.val.states (p + z) hpz := rfl

/-- Equality of sections is equality of the underlying histories. -/
theorem ext {l : F.Duration} {σ τ : Beh F l} (h : σ.val = τ.val) : σ = τ := Subtype.ext h

/--
**Functoriality, identity half**: `Tr 0` acts trivially. `app:presheaf-dictionary`'s
"while `Tr 0` acts trivially".
-/
theorem restrict_id {l : F.Duration} (hl : 0 ≤ l) (τ : Beh F l) :
    restrict 0 l (le_refl 0) hl (by rw [zero_add]) τ = τ := by
  refine ext (ShiftSet.wh_ext ?_ ?_)
  · funext z
    show (0 ≤ z ∧ z ≤ l) = τ.val.domain z
    exact propext ((τ.property z).symm)
  · intro r hr h'
    have h0r : τ.val.domain (0 + r) := by rw [zero_add]; exact h'
    rw [restrict_states 0 l (le_refl 0) hl (by rw [zero_add]) τ r hr h0r]
    exact ConvexHistory.states_eq_of_time_eq τ.val (0 + r) r (zero_add r) h0r h'

/--
**Functoriality, composition half**: restricting along `Tr p` and then along `Tr p'` is
restricting along `Tr (p + p')`. `app:presheaf-dictionary`'s "restricting along `Tr p'` thereafter
yields `z ↦ τ(p + p' + z)`, the restriction along `Tr p ∘ Tr p' = Tr (p + p')`".
-/
theorem restrict_comp {l : F.Duration} (p l' p' l'' : F.Duration)
    (hp : 0 ≤ p) (hl' : 0 ≤ l') (hple : p + l' ≤ l)
    (hp' : 0 ≤ p') (hl'' : 0 ≤ l'') (hple' : p' + l'' ≤ l')
    (τ : Beh F l) :
    restrict p' l'' hp' hl'' hple' (restrict p l' hp hl' hple τ)
      = restrict (p + p') l'' (add_nonneg hp hp') hl''
          (by
            rw [add_assoc]
            exact le_trans (add_le_add (le_refl p) hple') hple) τ := by
  refine ext (ShiftSet.wh_ext rfl ?_)
  intro r hr hr'
  have hin : τ.val.domain (p + (p' + r)) :=
    mem_dom τ (add_nonneg hp (add_nonneg hp' hr.1))
      (le_trans (add_le_add (le_refl p) (le_trans (add_le_add (le_refl p') hr.2) hple')) hple)
  have hin' : τ.val.domain (p + p' + r) := by rw [← add_assoc] at hin; exact hin
  rw [restrict_states p' l'' hp' hl'' hple' _ r hr (by
        rw [restrict_domain]
        exact ⟨add_nonneg hp' hr.1, le_trans (add_le_add (le_refl p') hr.2) hple'⟩),
      restrict_states p l' hp hl' hple τ (p' + r) _ hin,
      restrict_states (p + p') l'' (add_nonneg hp hp') hl'' _ τ r hr' hin']
  exact ConvexHistory.states_eq_of_time_eq τ.val (p + (p' + r)) (p + p' + r)
    (add_assoc p p' r).symm hin hin'

/-! ## The Germs clause: `Beh(F)(0) ≅ W` -/

/-- The germ of a section over `0`: its unique value. -/
def germ (τ : Beh F 0) : F.WorldState :=
  τ.val.states 0 (mem_dom τ (le_refl 0) (le_refl 0))

/--
Every world state is a germ.

`app:presheaf-dictionary`'s *Germs* proof, verbatim: "a function `{⟨0, w⟩}` is a convex history
on `[0, 0] = {0}` exactly when `w ⇒₀ w`, which `lem:nullity` provides for every `w ∈ W`." Here
`lem:nullity` is `F.nullity_identity`, and the `respects_task` obligation below is its only use.
-/
def ofGerm (F : TaskFrame) (w : F.WorldState) : Beh F 0 :=
  ⟨{ domain := fun t => 0 ≤ t ∧ t ≤ 0
     nonempty_domain := ⟨0, le_refl 0, le_refl 0⟩
     states := fun _ _ => w
     respects_task := by
       intro s t hs ht
       have hs0 : s = 0 := le_antisymm hs.2 hs.1
       have ht0 : t = 0 := le_antisymm ht.2 ht.1
       subst hs0; subst ht0
       simpa [sub_self] using (F.nullity_identity w w).mpr rfl
     convex := by
       intro a c ha hc y hay hyc
       exact ⟨le_trans ha.1 hay, le_trans hyc hc.2⟩ },
   fun _ => Iff.rfl⟩

/-- `W → Beh(F)(0) → W` is the identity. -/
theorem germ_ofGerm (F : TaskFrame) (w : F.WorldState) : germ (ofGerm F w) = w := rfl

/-- `Beh(F)(0) → W → Beh(F)(0)` is the identity. With `germ_ofGerm` this is `Beh(F)(0) ≅ W`,
the *Germs* clause of `app:presheaf-dictionary`. -/
theorem ofGerm_germ (τ : Beh F 0) : ofGerm F (germ τ) = τ := by
  refine ext (ShiftSet.wh_ext ?_ ?_)
  · funext z
    show (0 ≤ z ∧ z ≤ 0) = τ.val.domain z
    exact propext ((τ.property z).symm)
  · intro r _ h'
    have hr0 : r = 0 := le_antisymm ((τ.property r).mp h').2 ((τ.property r).mp h').1
    subst hr0
    rfl

/-! ## The Sheaf clause: its composition step, at the interval site -/

/--
**The seam step of `app:gluing`, at the interval site.**

Given sections `τ₁ ∈ Beh(F)(l₁)` and `τ₂ ∈ Beh(F)(l₂)` whose germs agree at the seam —
`τ₁(l₁) = τ₂(0)`, which is the paper's `Rres{l₁}{0}(τ₁) = Lres{l₂}{0}(τ₂)` — the task relation
holds ACROSS the seam: from a `τ₁`-state at `s ∈ [0, l₁]` to a `τ₂`-state at `t - l₁ ∈ [0, l₂]`,
over the duration `t - s`.

This is the one place where `app:gluing`'s proof does real work ("the constraints
`τ₁(x) ⇒_{z-x} τ(z)` and `τ(z) ⇒_{y-z} τ₂(y)` compose by *Compositionality*"), and it is the
same argument the library already carries in `Semantics/StarPasting.lean`'s `paste_rel_le_lt` —
there stated for TOTAL histories only. That this probe has to re-derive it rather than cite it is
the concrete measure of the gap between the library's gluing and the presheaf's: the mathematics
is identical and only the totality hypothesis differs.

What remains for the *Sheaf* clause proper — assembling the glued section by cases and proving
the two restriction identities and uniqueness — is bookkeeping over this step, and is left to
the follow-on task proposed in the report's section 7.3.
-/
theorem glue_seam {l₁ l₂ : F.Duration} (h₁ : 0 ≤ l₁) (h₂ : 0 ≤ l₂)
    (τ₁ : Beh F l₁) (τ₂ : Beh F l₂)
    (hmatch : τ₁.val.states l₁ (mem_dom τ₁ h₁ (le_refl l₁))
      = τ₂.val.states 0 (mem_dom τ₂ (le_refl 0) h₂))
    (s t : F.Duration) (hs : 0 ≤ s) (hsl : s ≤ l₁)
    (ht : 0 ≤ t - l₁) (htl : t - l₁ ≤ l₂) :
    F.TaskRel (τ₁.val.states s (mem_dom τ₁ hs hsl)) (t - s)
      (τ₂.val.states (t - l₁) (mem_dom τ₂ ht htl)) := by
  have hA : F.TaskRel (τ₁.val.states s (mem_dom τ₁ hs hsl)) (l₁ - s)
      (τ₁.val.states l₁ (mem_dom τ₁ h₁ (le_refl l₁))) :=
    τ₁.val.respects_task s l₁ _ _
  have hB : F.TaskRel (τ₂.val.states 0 (mem_dom τ₂ (le_refl 0) h₂)) ((t - l₁) - 0)
      (τ₂.val.states (t - l₁) (mem_dom τ₂ ht htl)) :=
    τ₂.val.respects_task 0 (t - l₁) _ _
  rw [hmatch] at hA
  rw [sub_zero] at hB
  have hsum : t - s = (l₁ - s) + (t - l₁) := by
    rw [add_comm]; exact (sub_add_sub_cancel t l₁ s).symm
  rw [hsum]
  exact (F.comp _ _ _ _ (sub_nonneg.mpr hsl) ht).mpr ⟨_, hA, hB⟩

end Beh

end Probe553D
