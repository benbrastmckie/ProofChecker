/-
Probe: is the paper's F° (`W = D = ℝ`, `w ⇒_x u` iff `x ≤ u − w ≤ 2x` for `x ≥ 0`,
extended to negative durations by the converse convention) a legal task frame?
Research-only file; not part of the FormalSystem library.
-/
import FormalSystem.Semantics.TaskFrame
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Probe536

open FormalSystem.Semantics
open Set

/-- `ℝ` as a temporal order. `@[reducible]` is load-bearing. -/
@[reducible] noncomputable def rOrder : TemporalOrder := ⟨ℝ⟩

/-- The two-sided extension of `x ≤ u − w ≤ 2x` (`x ≥ 0`) by the converse convention. -/
def fzeroRel (w : ℝ) (d : ℝ) (u : ℝ) : Prop := u - w ∈ Set.uIcc d (2 * d)

theorem fzeroRel_iff (w d u : ℝ) :
    fzeroRel w d u ↔ (d ≤ u - w ∧ u - w ≤ 2 * d) ∨ (2 * d ≤ u - w ∧ u - w ≤ d) := by
  simp [fzeroRel, Set.mem_uIcc]

/-! ### Fibres are closed bounded intervals -/

theorem mem_fib_iff (w d u : ℝ) :
    u ∈ TaskFrame.Fib (D := rOrder) fzeroRel w d ↔ fzeroRel w d u := Iff.rfl

theorem fib_eq_Icc (w d : ℝ) (h : 0 ≤ d) :
    TaskFrame.Fib (D := rOrder) fzeroRel w d = Set.Icc (w + d) (w + 2 * d) := by
  ext u
  rw [mem_fib_iff, fzeroRel_iff, Set.mem_Icc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; left; exact ⟨by linarith, by linarith⟩

theorem fib_eq_Icc' (w d : ℝ) (h : d ≤ 0) :
    TaskFrame.Fib (D := rOrder) fzeroRel w d = Set.Icc (w + 2 * d) (w + d) := by
  ext u
  rw [mem_fib_iff, fzeroRel_iff, Set.mem_Icc]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; right; exact ⟨by linarith, by linarith⟩

theorem isCompact_fib (w d : ℝ) : IsCompact (TaskFrame.Fib (D := rOrder) fzeroRel w d) := by
  rcases le_total 0 d with h | h
  · rw [fib_eq_Icc w d h]; exact isCompact_Icc
  · rw [fib_eq_Icc' w d h]; exact isCompact_Icc

theorem isClosed_fib (w d : ℝ) : IsClosed (TaskFrame.Fib (D := rOrder) fzeroRel w d) := by
  rcases le_total 0 d with h | h
  · rw [fib_eq_Icc w d h]; exact isClosed_Icc
  · rw [fib_eq_Icc' w d h]; exact isClosed_Icc

/-! ### The six axioms -/

theorem fzero_nullity (w u : ℝ) : fzeroRel w 0 u ↔ w = u := by
  rw [fzeroRel_iff]; constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith
  · rintro rfl; left; constructor <;> linarith

theorem fzero_converse (w d u : ℝ) : fzeroRel w d u ↔ fzeroRel u (-d) w := by
  rw [fzeroRel_iff, fzeroRel_iff]; constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right; constructor <;> linarith
    · left; constructor <;> linarith

theorem fzero_serial : TaskFrame.Serial (D := rOrder) fzeroRel := by
  intro w x _
  refine ⟨⟨w + x, ?_⟩, ⟨w - x, ?_⟩⟩ <;> rw [fzeroRel_iff]
  · rcases le_total 0 x with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rcases le_total 0 x with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith

theorem fzero_comp : TaskFrame.Compositional (D := rOrder) fzeroRel := by
  intro w v x y hx hy
  constructor
  · intro h
    rw [fzeroRel_iff] at h
    rcases le_total (w + x) (v - 2 * y) with hm | hm
    · refine ⟨v - 2 * y, ?_, ?_⟩ <;> rw [fzeroRel_iff] <;> left <;>
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    · refine ⟨w + x, ?_, ?_⟩ <;> rw [fzeroRel_iff] <;> left <;>
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨u, h1, h2⟩
    rw [fzeroRel_iff] at h1 h2 ⊢
    left
    rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
      exact ⟨by linarith, by linarith⟩

theorem fzero_limit (w u : ℝ)
    (h : ∀ x : ℝ, 0 < x → ∃ y : ℝ, |y| < x ∧ fzeroRel w y u) : u = w := by
  by_contra hne
  have hpos : 0 < |u - w| := by
    simpa [sub_eq_zero] using abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨y, hy, hr⟩ := h (|u - w| / 2) (by linarith)
  rw [fzeroRel_iff] at hr
  have hya : |y| < |u - w| / 2 := hy
  rcases abs_lt.mp hya with ⟨hy1, hy2⟩
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases abs_cases (u - w) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hy1 hy2 <;> linarith
  · rcases abs_cases (u - w) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hy1 hy2 <;> linarith

theorem fzero_saturation : TaskFrame.Saturation (D := rOrder) fzeroRel := by
  intro S hdir hmem
  have hne : Nonempty S := ⟨⟨hdir.1.choose, hdir.1.choose_spec⟩⟩
  refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    (fun S₁ h₁ S₂ h₂ => ?_) (fun U hU => (hmem U hU).2) (fun U hU => ?_) (fun U hU => ?_)
  · obtain ⟨S', hS', hsub⟩ := hdir.2 S₁ h₁ S₂ h₂
    exact ⟨S', hS', hsub.trans inter_subset_left, hsub.trans inter_subset_right⟩
  · rcases (hmem U hU).1 with ⟨w, x, rfl⟩ | ⟨w, v, x, y, _, _, rfl⟩
    · exact isCompact_fib w x
    · exact (isCompact_fib w x).inter_right (isClosed_fib v (-y))
  · rcases (hmem U hU).1 with ⟨w, x, rfl⟩ | ⟨w, v, x, y, _, _, rfl⟩
    · exact isClosed_fib w x
    · exact (isClosed_fib w x).inter (isClosed_fib v (-y))

/-- **F° is a task frame.** -/
noncomputable def fzeroFrame : FrameOver rOrder where
  WorldState := ℝ
  TaskRel := fzeroRel
  nullity_identity := fzero_nullity
  comp := fzero_comp
  converse := fzero_converse
  serial := fzero_serial
  limit := fzero_limit
  saturation := fzero_saturation

end Probe536

namespace Probe536

open FormalSystem.Semantics Set

/-! ### F° is NOT Deterministic -/

theorem fzero_not_deterministic :
    ¬ (∀ (w u v : ℝ) (x : ℝ), fzeroRel w x u → fzeroRel w x v → u = v) := by
  intro h
  have h1 : fzeroRel 0 1 1 := by rw [fzeroRel_iff]; left; norm_num
  have h2 : fzeroRel 0 1 2 := by rw [fzeroRel_iff]; left; norm_num
  have := h 0 1 2 1 h1 h2
  norm_num at this

/-! ### Every total history of F° is a bi-Lipschitz increasing bijection of `ℝ`.

Stated on the bare state function `f`, which is what a total history's `states` field
collapses to; `hf` is exactly `respects_task`. -/

variable (f : ℝ → ℝ) (hf : ∀ s t : ℝ, fzeroRel (f s) (t - s) (f t))

include hf

theorem fzero_bounds {s t : ℝ} (hst : s ≤ t) : t - s ≤ f t - f s ∧ f t - f s ≤ 2 * (t - s) := by
  have := (fzeroRel_iff (f s) (t - s) (f t)).mp (hf s t)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

theorem fzero_lipschitz : LipschitzWith 2 f := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rcases le_total s t with h | h
  · obtain ⟨h1, h2⟩ := fzero_bounds f hf h
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (f s), abs_sub_comm s]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    push_cast; linarith
  · obtain ⟨h1, h2⟩ := fzero_bounds f hf h
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    push_cast; linarith

theorem fzero_continuous : Continuous f := (fzero_lipschitz f hf).continuous

/-- **Forward surjectivity.** Every state strictly above `f x` is `f c` for some `c > x`. -/
theorem fzero_hits_future {x v : ℝ} (hv : f x < v) : ∃ c, x < c ∧ f c = v := by
  set a := x + (v - f x) / 2 with ha
  set b := x + (v - f x) with hb
  have hab : a ≤ b := by simp only [ha, hb]; linarith
  have hfa : f a ≤ v := by
    obtain ⟨_, h2⟩ := fzero_bounds f hf (show x ≤ a by simp only [ha]; linarith)
    simp only [ha] at h2; linarith
  have hfb : v ≤ f b := by
    obtain ⟨h1, _⟩ := fzero_bounds f hf (show x ≤ b by simp only [hb]; linarith)
    simp only [hb] at h1; linarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hab (fzero_continuous f hf).continuousOn
    (Set.mem_Icc.mpr ⟨hfa, hfb⟩)
  exact ⟨c, by have := hc.1; simp only [ha] at this; linarith, hcv⟩

/-- **Backward surjectivity.** Every state strictly below `f x` is `f c` for some `c < x`. -/
theorem fzero_hits_past {x v : ℝ} (hv : v < f x) : ∃ c, c < x ∧ f c = v := by
  set a := x - (f x - v) with ha
  set b := x - (f x - v) / 2 with hb
  have hab : a ≤ b := by simp only [ha, hb]; linarith
  have hfa : f a ≤ v := by
    obtain ⟨h1, _⟩ := fzero_bounds f hf (show a ≤ x by simp only [ha]; linarith)
    simp only [ha] at h1; linarith
  have hfb : v ≤ f b := by
    obtain ⟨_, h2⟩ := fzero_bounds f hf (show b ≤ x by simp only [hb]; linarith)
    simp only [hb] at h2; linarith
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hab (fzero_continuous f hf).continuousOn
    (Set.mem_Icc.mpr ⟨hfa, hfb⟩)
  exact ⟨c, by have := hc.2; simp only [hb] at this; linarith, hcv⟩

/-- **Strict monotonicity**, the other half of the order-isomorphism claim. -/
theorem fzero_strictMono : StrictMono f := by
  intro s t hst
  obtain ⟨h1, _⟩ := fzero_bounds f hf hst.le
  linarith

end Probe536

namespace Probe536

open FormalSystem.Semantics Set

/-! ## F¹: the deterministic translation flow over `ℝ` -/

def foneRel (w : ℝ) (d : ℝ) (u : ℝ) : Prop := u = w + d

theorem fone_saturation : TaskFrame.Saturation (D := rOrder) foneRel := by
  intro S hdir hmem
  obtain ⟨S₀, hS₀⟩ := hdir.1
  obtain ⟨c, hc⟩ := (hmem S₀ hS₀).2
  refine ⟨c, ?_⟩
  intro U hU
  obtain ⟨S', hS', hsub⟩ := hdir.2 U hU S₀ hS₀
  obtain ⟨e, he⟩ := (hmem S' hS').2
  have h1 : e ∈ U := (hsub he).1
  have h2 : e ∈ S₀ := (hsub he).2
  -- every fibre / segment of a functional relation is a subsingleton
  have hsub' : ∀ V, (TaskFrame.IsFiber (D := rOrder) foneRel V
      ∨ TaskFrame.IsSegment (D := rOrder) foneRel V) → ∀ a ∈ V, ∀ b ∈ V, a = b := by
    rintro V (⟨w, x, rfl⟩ | ⟨w, v, x, y, _, _, rfl⟩) a ha b hb
    · exact ha.trans hb.symm
    · exact ha.1.trans hb.1.symm
  have := hsub' S₀ (hmem S₀ hS₀).1 e h2 c hc
  exact this ▸ h1

noncomputable def foneFrame : FrameOver rOrder where
  WorldState := ℝ
  TaskRel := foneRel
  nullity_identity := by intro w u; simp [foneRel, eq_comm]
  comp := by
    intro w v x y _ _
    constructor
    · rintro rfl; exact ⟨w + x, rfl, by simp [foneRel]; ring⟩
    · rintro ⟨u, rfl, rfl⟩; simp [foneRel]; ring
  converse := by intro w d u; simp [foneRel]; constructor <;> (intro h; linarith)
  serial := by intro w x _; exact ⟨⟨w + x, rfl⟩, ⟨w - x, by simp [foneRel]⟩⟩
  limit := by
    intro w u h
    by_contra hne
    have hpos : 0 < |u - w| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨y, hy, hr⟩ := h (|u - w|) hpos
    have hr' : u = w + y := hr
    have heq : u - w = y := by rw [hr']; ring
    rw [heq] at hy
    exact lt_irrefl _ hy
  saturation := fone_saturation

/-- **F¹ is Deterministic.** -/
theorem fone_deterministic :
    ∀ (w u v : ℝ) (x : ℝ), foneRel w x u → foneRel w x v → u = v := by
  rintro w u v x rfl rfl; rfl

end Probe536
